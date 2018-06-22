---
title: Introducing the Pact property checker
date: 2018-05-17 13:16:01
tags:
---

Together with [Kadena](http://kadena.io/), [Monic](https://www.monic.co/) has developed new a static analysis tool for the [Pact](https://github.com/kadena-io/pact) smart contract language that we're calling the "property checker". In this post we'll talk about the purpose of our tool, what it can do today, and what we have planned for the future.

## Pact: some background

As a smart contract language, Pact is designed to be run within the confines of a blockchain. Users submit transactions to the network, and if a transaction is accepted into the system, the user's code will either create a new contract, or interact with a contract already deployed to the system. Each contract maintains state across interactions via a SQL-like table model for data.

Like most smart contract languages, Pact is deterministic (so that the same code produces the same result when executing on each node), but additionally it's much more computationally constrained than languages like Ethereum's Solidity (or the EVM generally). In Pact, there are no loops, recursion, null values, or exceptions; and authorization patterns are encoded as builtins which either successfully execute or abort (and roll back) the transaction:

```lisp
(defun read-user:user (name:string)
  "Read the user indexed by `name` if the current tx was signed by an admin. Aborts otherwise."
  (enforce-keyset 'admins)
  (read users name))
```

Here you can think of the `admins` keyset as a pre-published list of the public keys for all administrators of the smart contract.

## The state of smart contract security

As we've seen from the string of successful attacks on contracts in the Ethereum world, it's clear that the current approaches to smart contract security aren't working. Almost every one of these exploited Ethereum contracts was written by a foremost Solidity expert (or one of the creators of Ethereum!). How is a newcomer to the platform expected to author a secure contract?

Though Pact was designed to make programmer errors more unlikely, between the combination of conditionals, DB access, and authorization concerns, programs can become non-trivial very quickly. Pact's (optional) type system goes some way toward building confidence in programs, but in the adversarial world of smart contracts, type systems and unit tests aren't sufficient for building secure systems.

## The Pact property checker

To address the current state of affairs, we've built our property checking system that allows programmers to decorate:

- table schemas with "invariants", and
- functions with "properties" (think: theorems)

that must hold for _all_ possible inputs and database states.

If you're familiar with the notion of contracts (note: not smart contracts!) from [Dafny](https://github.com/Microsoft/dafny), or the style of refinement types afforded by [Liquid Haskell](https://ucsd-progsys.github.io/liquidhaskell-blog/), the Pact property checker shares some similarities with those systems.

## Some trivial examples

As an example, we can decorate an absolute value function with the property that the function's return value must always be greater than or equal to zero:

```lisp
(defun abs:integer (x:integer)
  ("Returns the absolute value of an integer"
    (property (>= result 0)))

  (if (< x 0)
    (negate x)
    x))
```

and the property checker will immediately inform the user that this property holds for all possible values of `x`.

Similarly we can place a schema invariant on a database table to ensure that an account balance must always be positive:

```lisp
(defschema account
  ("A user account"
    (invariant (>= balance 0)))

  balance:integer
  ks:keyset)
```

For this invariant, the system ensures that every function in the contract maintains the invariant on any write to a table with that schema.

We've also built editor integration into [Atom](https://atom.io/) that verifies these invariants and properties whenever a smart contract is modified during development:

<img src="shot.png" />

To see how the property checking system would be used in the real world, let's go through a longer example.

## A real-world example: transferring funds

This is a simple contract for tracking user balances of a fictional currency. If you're familiar with Ethereum, you can think of this as simplified version of an [ERC20](https://en.wikipedia.org/wiki/ERC20) contract. For this example we're going to ignore concerns like issuance of the currency, and demonstrate only a `transfer` function to send funds between accounts.

<annotated-code></annotated-code>

## How does it work?

We translate Pact code into a set of constraints for an [SMT solver](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories) (we used Microsoft's [Z3](https://github.com/Z3Prover/z3)). We then ask for a set of inputs that results in a violated invariant or property. There are three possible results:

* The solver returns, having satisfied the constraints. This means that there is a set of inputs violating the property or invariant. We display it for the user like in the example.
* The solver returns and says that the constraints are impossible to satisfy. This means that the property or invariant is valid.
* The solver times out. This means that we can't tell whether the property or invariant is valid without waiting for longer. The search we're asking Z3 to do is decidable, but it's pretty easy to make it take a very long time. This hasn't been a real problem for any contracts we've analyzed so far.

The two most important tools we use are Z3 itself, and the [SBV](http://leventerkok.github.io/sbv/) (SMT Based Verification) library by [Levent Erkök](http://leventerkok.github.io/), which provides a high-level Haskell interface to SMT solvers.

The pact analysis tool is a large codebase, but we can understand its basic approach via a smaller example.

### SQL injection search.

We're going to analyze a simple language intended as an example of a server-side web scripting language, where we can query a database and munge strings. Our analysis will detect possible SQL injections.

We start with the terms of the language. This is a stringly-typed language, somewhat like bash, with the following types of expressions:

* `Query`: query from the database using SQL syntax.
* `Const`: a string literal
* `Concat`: concatenate two strings
* `ReadVar`: read a variable in scope. Since our language is stringly-typed we can use dynamic variables:
  - `ReadVar (Concat "user_" "name")`
  - `ReadVar (Concat "user_" (ReadVar "category"))`
  - `ReadVar (Query "SELECT var FROM vars WHERE id=5")`

```haskell
-- | Simple expression language
data SQLExpr = Query   SQLExpr
             | Const   String
             | Concat  SQLExpr SQLExpr
             | ReadVar SQLExpr

-- | A simple program to query all messages with a given topic id. In SQL-like notation:
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

Now we need some way to translate these expressions into constraints that Z3 can solve. Surprisingly, this translation looks like evaluation. One way to think about this is that we're going to ask Z3 to run evaluation backwards (to give us inputs producing some output). So we need to describe to Z3 how evaluation runs forwards.

```haskell
-- | Evaluation monad. The state argument is the environment to store
-- variables as we evaluate.
type M = StateT (SFunArray String String) (WriterT [SString] Symbolic)

-- | Given an expression, symbolically evaluate it
eval :: SQLExpr -> M SString
eval (Query q)      = do q' <- eval q
                         tell [q']
                         lift $ lift exists_
eval (Const str)    = return $ literal str
eval (Concat e1 e2) = (.++) <$> eval e1 <*> eval e2
eval (ReadVar nm)   = do n   <- eval nm
                         arr <- get
                         return $ readArray arr n
```

`SFunArray` represents a mapping (think of a block of memory or a database table). Our `SFunArray String String` represents the variables in scope in our language. We also write our program's queries as `[SString]` (`SString` is an SBV *symbolic* string).

We need to recognize exploits. To do so we use regular expressions (Z3 has a theory of strings and regular expressions).

From what I've seen, strings and regular expressions are quite difficult to solve for. It's easy to accidentally generate a very large space for Z3 to search. To make the problem tractable, we use a simplified model of what exploits look like.

Note that we've overloaded Haskell's `+` and `*` operators to mean "or" and "then", respectively. This idea comes from [Gabriel Gonzalez](https://github.com/Gabriel439/slides/blob/master/regex/regex.md).

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
findInjection = do
  badTopic <- sString "badTopic"

  -- Create an initial environment that returns the symbolic
  -- value my_topicid only, and undefined for all other variables
  undef <- sString "uninitialized"
  let env :: SFunArray String String
      env = mkSFunArray $ \varName -> ite (varName .== "my_topicid") badTopic undef

  (_, queries) <- runWriterT (evalStateT (eval expr) env)

  -- For all the queries thus generated, ask that one of them be "explotiable"
  constrain $ bAny (`R.match` exploitRe) queries

  query ... -- get result from SBV
```

```
>>> findInjection exampleProgram
"h'; DROP TABLE 'users"
```

Indeed, if we substitute the suggested string, we get the program `query ("SELECT msg FROM msgs where topicid='h'; DROP TABLE 'users'")`, a [classic SQL injection](https://xkcd.com/327/).

This was a simplified example, but follows the same fundamental approach as the Pact analysis tool. The complete example is available [in the sbv repo](https://github.com/LeventErkok/sbv/blob/bfc6c80fe4e4546ba26a1bd045e87b88e973f7f4/Documentation/SBV/Examples/Strings/SQLInjection.hs).

### The smt-lib 2 output

It's almost hard to believe that the above code was all to build a set of constraints. This is because SBV exposes a very high level interface which does most of the heavy lifting.

To get a better understanding of what Z3 is actually doing, let's log the low-level interaction between SBV and Z3.

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

That's it! The `GOOD` lines are a translation of our program. `(assert s7)` is saying "I assert that there is no input producing a query matching our exploit pattern". Then the two sets of `SEND` / `RECV` are Z3 saying, "actually, I know a bad input" (`sat`) and "here it is" (`((s0 "h'; DROP TABLE 'users"))`).

## Future directions

We're actively developing this tool and very excited for the projects we have planned.

### Abstracting properties

Currently there's no way to define a new property. Where we mean "conserves mass" we have to write `(= (column-delta table 'column) 0)`. Soon you'll be able to define new properties with `(defproperty conserves-mass (= (column-delta table 'column) 0)`.

### Improved UX

Right now we show the inputs to a function, but as we've seen, there's still some work left to the user. You need to step through line-by-line to understand what those inputs mean for your code. Worse, we don't show values read from the database.

We plan to improve this experience by showing a line-by-line trace of values, similar to what a debugger like the Chrome devtools debugger might show. We'll write more about this in an upcoming post.

### Covering all of the language

Right now we punt on some parts of the language that are hard to model in z3. In particular, we're actively working on adding support for properties of lists.

### Stronger defaults

We've shown that it's possible to write a `pure` property, meaning that some function doesn't read, write, or abort. Our plan is to make something like this the default, so that all non-pure code must be explicitly marked.
