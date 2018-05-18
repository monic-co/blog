---
title: Introducing the Pact analysis tools
date: 2018-05-17 13:16:01
tags:
---

Together with [Kadena](http://kadena.io/), Monic just released a static analysis tool for the [Pact](https://github.com/kadena-io/pact) smart contract language. In this post we'll talk about the purpose of our tool, what it can do today, and what we have planned for the future.

## Example: balance transfer

We begin with an example to help motivate building this tool.

This is a

```lisp
(module accounts 'accounts-admin-keyset
  "Account balances module"

  (defschema account
    "account"
    balance:integer
    ks:keyset)
  (deftable accounts:{account})

(defun transfer (from:string to:string amount:integer)
  "Transfer money between accounts"

  (let ((from-bal (at 'balance (read accounts from)))
        (from-ks  (at 'ks      (read accounts from)))
        (to-bal   (at 'balance (read accounts to))))
    (enforce-keyset from-ks)
    (enforce (>= from-bal amount) "Insufficient Funds")
    (update accounts from { "balance": (- from-bal amount) })
    (update accounts to   { "balance": (+ to-bal amount) }))))
```

## How does it work?

The most important tool we used was the [SBV](http://leventerkok.github.io/sbv/) (SMT Based Verification) library by Levent Erkök, which provides a Haskell interface to SMT solvers. SBV supports a handful of solvers, though the only one we've used so far is Microsoft's [Z3](https://github.com/Z3Prover/z3).

### SQL injection search.

The pact analysis tool is a large codebase, but we can understand its basic approach via a smaller example. We're going to detect possible SQL injections given a simple expression language. The complete example is available [in the sbv repo](https://github.com/LeventErkok/sbv/blob/bfc6c80fe4e4546ba26a1bd045e87b88e973f7f4/Documentation/SBV/Examples/Strings/SQLInjection.hs)

We start with the terms of the language. This is a stringly-typed language, somewhat like bash, with the following types of expressions:

* `Query`: query from the database using SQL syntax.
* `Const`: a string literal
* `Concat`: concatenate two strings
* `ReadVar`: read a variable in scope. Since our language is stringly typed we can use dynamic variables names:
  - `ReadVar (Concat "user_" "name")`
  - `ReadVar (Concat "user_" (ReadVar "category"))`
  - `ReadVar (Query "SELECT var FROM vars WHERE id=5)`

```haskell
-- | Simple expression language
data SQLExpr = Query   SQLExpr
             | Const   String
             | Concat  SQLExpr SQLExpr
             | ReadVar SQLExpr

-- | A simple program to query all messages with a given topic id. In SQL like notation:
--
-- @
--   query ("SELECT msg FROM msgs where topicid='" ++ my_topicid ++ "'")
-- @
exampleProgram :: SQLExpr
exampleProgram = Query $ foldr1 Concat [ "SELECT msg FROM msgs WHERE topicid='"
                                       , ReadVar "my_topicid"
                                       , "'"
                                       ]
```

Now we need some way to translate these expressions into constraints that z3 can solve. This translation looks like evaluation. One way to think about this is that we're going to ask z3 to run evaluation backwards (to give us inputs producing some output). So we need to describe how evaluation runs forwards.

```haskell
-- | Evaluation monad. The state argument is the environment to store
-- variables as we evaluate.
type M = StateT (SFunArray String String) (WriterT [SString] Symbolic)

-- | Given an expression, symbolically evaluate it
eval :: SQLExpr -> M SString
eval (Query q)         = do q' <- eval q
                            tell [q']
                            lift $ lift exists_
eval (Const str)       = return $ literal str
eval (Concat e1 e2)    = (.++) <$> eval e1 <*> eval e2
eval (ReadVar nm)      = do n   <- eval nm
                            arr <- get
                            return $ readArray arr n
```

`SFunArray` represents a mapping (think of a block of memory or a database table). Our `SFunArray String String` represents the variables in scope in our language. We also write our program's queries as `[SString]` (`SString` is an SBV *symbolic* string).

We need to recognize exploits. To do so we use regular expressions (z3 has a theory of strings and regular expressions).

From what I've seen, strings and regular expressions are quite difficult to solve for. It's easy to accidentally generate a very large space for z3 to search. To make the problem tractable, we use a simplified model of what exploits look like.

```haskell
-- | We'll greatly simplify here and say a statement is either a select or a drop:
statementRe :: RegExp
statementRe = selectRe + dropRe

-- | The exploit: We're looking for a DROP TABLE after at least one legitimate command.
exploitRe :: RegExp
exploitRe = KPlus (statementRe * "; ")
          * "DROP TABLE 'users'"
```

Finally we analyze the example program (`query ("SELECT msg FROM msgs where topicid='" ++ my_topicid ++ "'")`):

```haskell
badTopic <- sString "badTopic"

-- Create an initial environment that returns the symbolic
-- value my_topicid only, and undefined for all other variables
undef      <- sString "uninitialized"
let env :: SFunArray String String
    env = mkSFunArray $ \varName -> ite (varName .== "my_topicid") badTopic undef

(_, queries) <- runWriterT (evalStateT (eval expr) env)

-- For all the queries thus generated, ask that one of them be "explotiable"
constrain $ bAny (`R.match` exploitRe) queries
```

```
>>> findInjection exampleProgram
"h'; DROP TABLE 'users"
```

Indeed, if we substitute the suggested string, we get the program `query ("SELECT msg FROM msgs where topicid='h'; DROP TABLE 'users'")` which would query for topic "h" and then delete the users table!

This was a simplified example, but follows the same fundamental approach as the Pact analysis tool.

### The smt-lib 2 output

It's almost hard to believe that the above code was all to build a set of constraints. This is because SBV exposes a very high level interface which does most of the heavy lifting.

Let's log the low-level interaction with z3 to understand what's happening.

```
[GOOD] ; --- literal constants ---
[GOOD] (define-fun s_2 () Bool false)
[GOOD] (define-fun s_1 () Bool true)
[GOOD] (define-fun s3 () String "SELECT msg FROM msgs WHERE topicid='")
[GOOD] (define-fun s4 () String "'")
[GOOD] ; --- skolem constants ---
[GOOD] (declare-fun s0 () String) ; tracks user variable "badTopic"
[GOOD] (declare-fun s1 () String) ; tracks user variable "uninitialized"
[GOOD] (declare-fun s2 () String)
[GOOD] ; --- constant tables ---
[GOOD] ; --- skolemized tables ---
[GOOD] ; --- arrays ---
[GOOD] ; --- uninterpreted constants ---
[GOOD] ; --- user given axioms ---
[GOOD] ; --- formula ---
[GOOD] (define-fun s5 () String (str.++ s0 s4))
[GOOD] (define-fun s6 () String (str.++ s3 s5))
[GOOD] (define-fun s7 () Bool (str.in.re s6 (re.++ (re.+ (re.++ (re.union (re.++ (str.to.re "SELECT ") (re.union ((_ re.loop 1 7) (re.range "a" "z")) (str.to.re "*")) (str.to.re " FROM ") ((_ re.loop 1 7) (re.range "a" "z")) (re.opt (re.++ (str.to.re " WHERE ") ((_ re.loop 1 7) (re.range "a" "z")) (str.to.re "=") (re.union ((_ re.loop 1 7) (re.range "a" "z")) (re.++ (str.to.re "'") ((_ re.loop 1 5) (re.union (re.range "a" "z") (str.to.re " "))) (str.to.re "'")))))) (re.++ (str.to.re "DROP TABLE ") (re.union ((_ re.loop 1 7) (re.range "a" "z")) (re.++ (str.to.re "'") ((_ re.loop 1 5) (re.union (re.range "a" "z") (str.to.re " "))) (str.to.re "'"))))) (str.to.re "; "))) (str.to.re "DROP TABLE 'users'"))))
[GOOD] (assert s7)
[SEND] (check-sat)
[RECV] sat
[SEND] (get-value (s0))
[RECV] ((s0 "h'; DROP TABLE 'users"))
```

SBV produces fantastically legible output. I've debugged at this level a few times and usually been able to find I need. I'm not sure there's much I can say to make this clearer than it already is.

## Future directions

TODO which things to mention
