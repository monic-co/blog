---
title: How the Pact property checker works
date: 2018-07-17 00:00:00
tags:
published: false
authors: [joel, brian]
---

[Last time](/introducing-the-pact-property-checker/), we saw an example of the Pact property checking system detecting bugs in a smart contract, but we didn't get into the details of how the system works. At a high-level, what happens is this:

## Overview

We translate Pact code into a set of [SMT solver](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories) constraints (we used Microsoft's [Z3](https://github.com/Z3Prover/z3)). We then ask for a set of inputs that results in a violated invariant or property. There are three possible results:

* The solver returns, having satisfied the constraints. This means that there is a set of inputs violating the property or invariant. We display it for the user like in the example.
* The solver returns and says that the constraints are impossible to satisfy. This means that the property or invariant is *valid*.
* The solver times out. This means that we can't tell whether the property or invariant is valid without waiting for longer. The search we're asking Z3 to do is decidable, but it possible to design a combination of program and property that would take a very long time to check. This hasn't been a real problem for any contracts we've analyzed so far.

The two most important tools we use are Z3 itself, and the [SBV](http://leventerkok.github.io/sbv/) (SMT-Based Verification) library by [Levent Erkök](http://leventerkok.github.io/), which provides a high-level Haskell interface to SMT solvers.

The details of the implementation are somewhat involved, but in the remainder of this post we'll look at it from two different angles:

* We'll walk through the implementation of a property checking system for a much simpler language.
* We'll examine the low-level interaction our real system has with its backing SMT solver.

Together these will give us a good idea of how our system actually works.

## SQL injection search.

We're going to analyze a simple language intended as an example of a server-side web scripting language, where we can query a database and munge strings. We'll use sbv to implement symbolic analysis to detect possible SQL injections.

We start with the terms of the language. This is a stringly-typed language, somewhat like bash, with the following types of expressions:

* `Query`: query from the database using SQL syntax.
* `Const`: a string literal
* `Concat`: concatenate two strings
* `ReadVar`: read a variable in scope
  - `ReadVar (Concat "user_" "name")`
  - `ReadVar (Concat "user_" (ReadVar "category"))`

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

Now we need some way to translate these expressions into constraints that Z3 can solve. Perhaps surprisingly, this translation looks a lot like evaluation -- and that's because it is! This is *symbolic*, rather than the standard form of *concrete*, evaluation. In symbolic evaluation, instead of successively computing (concrete) intermediate values until we produce our output, we instead pass over the program, accumulating a set of symbolic values (think: variables) that are related to one another and are subject to certain constraints. You can think of a system of equations from early algebra classes to help conceptualize this. In a symbolic program, similar to relational or logical programming, the line between inputs and outputs is blurred; instead of computation "moving" in a single "forward" direction, inputs are merely *related* to outputs according to our "system of equations" and constraints. So as we perform symbolic evaluation, we produce a symbolic value that represents our return value, that is constructed from, and is related to, our inputs.

For this particular task, we'll fix our output SQL statement, and ask Z3 to produce a certain, satisfying user input -- effectively evaluating backwards.

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

`SFunArray a b` represents a mapping (think of a block of memory or a database table) from *symbolic* values of type `a` to *symbolic* values of type `b`. Our `SFunArray String String` represents the variables in scope in our language. We also write our program's queries as `[SString]` (where `SString` is an SBV symbolic string).

Our goal is to recognize exploits. To do so we use Z3's support for regular expressions. (Where SMT stands for "satisfiability modulo theories", here we use the *theories* for strings and regular expressions).

From our experience, strings and regular expressions are quite difficult to solve for -- it's easy to accidentally generate a very large space for Z3 to search. To make the problem tractable, we use a simplified model of what exploits look like.

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

Finally we analyze the example program (`query ("SELECT msg FROM msgs where topicid='" ++ my_topicid ++ "'")`) to try to find an exploit:

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

This was a simplified example, but follows the same fundamental approach as the Pact property checker. The complete example is available [in the sbv repo](https://github.com/LeventErkok/sbv/blob/bfc6c80fe4e4546ba26a1bd045e87b88e973f7f4/Documentation/SBV/Examples/Strings/SQLInjection.hs).

## The smt-lib 2 output

It's almost hard to believe that the above code was all we needed to build the necessary set of constraints. This is because SBV exposes a very high level interface which does most of the heavy lifting.

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

