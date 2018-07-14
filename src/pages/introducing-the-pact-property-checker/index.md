---
title: Introducing the Pact property checker
date: 2018-05-17 13:16:01
tags:
authors: [joel, brian]
---

Together with [Kadena](http://kadena.io/), [Monic](https://www.monic.co/) has developed new a static analysis tool for the [Pact](https://github.com/kadena-io/pact) smart contract language that we're calling the *property checker*. In this post we'll talk about the purpose of the tool, what it can do today, and what we have planned for the future.

## Pact: some background

As a smart contract language, Pact is designed to be run within the confines of a blockchain. If you're not completely familiar with how smart contracts work, it's helpful to understand them as autonomous agents with which users interact. A user submits a transaction to the network, and if accepted into the system, this will either create a new contract, or interact with an existing one already deployed to the system. In Pact, each contract maintains state across interactions via a SQL-like table model for data.

Like most smart contract languages, Pact is deterministic (so that the same code produces the same result when executing on each node), but additionally it's much more computationally constrained than languages like Ethereum's Solidity (or the EVM generally). In Pact, there are no loops, recursion, null values, or exceptions; and authorization patterns are encoded as builtins which either successfully execute or abort (and roll back) the transaction:

```lisp
(defun read-user:user (name:string)
  "Read the user indexed by `name` if the current tx was signed by an admin. Aborts otherwise."
  (enforce-keyset 'admins)
  (read users name))
```

Here you can think of the `admins` *keyset* as a pre-published list of the public keys for all administrators of the smart contract.

## The state of smart contract security

As we've seen from the string of successful attacks on contracts in the Ethereum world, it's clear that the current approaches to smart contract security aren't working. Most exploited high-profile Ethereum contracts were written by Solidity experts or Ethereum Foundation developers. How is a newcomer to the platform expected to author a secure contract?

Though Pact was designed to make programmer errors less likely, between the combination of conditionals, DB access, and authorization concerns, programs can become non-trivial very quickly. Pact's (optional) type system goes some way toward building confidence in programs, but in the adversarial world of smart contracts, type systems and unit tests aren't sufficient for building secure systems.

## The Pact property checker

To address the current state of affairs, we've built our property checking system that allows programmers to decorate both

- table schemas with *invariants*, and
- functions with *properties* (think: theorems)

that must hold for _all_ possible inputs and database states.

The Pact property checker shares some similarities with contracts (note: not smart contracts!) from e.g. [Dafny](https://github.com/Microsoft/dafny) and [Liquid Haskell](https://ucsd-progsys.github.io/liquidhaskell-blog/)-style refinement types.

## Some simple examples

As an example, we can decorate an absolute value function with the property that the function's return value must always be non-negative:

```lisp
(defun abs:integer (x:integer)
  (meta "Returns the absolute value of an integer"
    (property (>= result 0)))

  (if (< x 0)
    (negate x)
    x))
```

and the property checker verifies that this property holds for all possible values of `x`.

Similarly we can place a schema invariant on a database table to ensure that an account balance must always be positive:

```lisp
(defschema account
  (meta "A user account"
    (invariant (>= balance 0)))

  balance:integer
  ks:keyset)
```

For this invariant, the system ensures that every function in the contract maintains the invariant on any write to a table with that schema.

We've also built editor integration for [Atom](https://atom.io/) that verifies these invariants and properties whenever a smart contract is modified during development:

![screenshot of atom plugin](shot.png)

To see how the property checking system would be used in the real world, let's go through a longer example.

## A real-world example: transferring funds

We'll write a simple contract for tracking user balances of a fictional currency. If you're familiar with Ethereum, you can think of this as simplified version of an [ERC20](https://en.wikipedia.org/wiki/ERC20) contract. For this example we're going to ignore concerns like issuance of the currency, and demonstrate only a `transfer` function to send funds between accounts.

<annotated-code></annotated-code>

## Future directions

We're actively developing this tool and very excited for the projects we have planned.

### Abstracting properties

Currently there's no way to define a new property by name. We have to write `(= (column-delta table 'column) 0)` where we'd rather write `conserves-mass`. [Soon](https://github.com/kadena-io/pact/pull/135) you'll be able to define new properties with `(defproperty conserves-mass (= (column-delta table 'column) 0)`.

### Improved UX

Currently, for falsifying models, we show concrete arguments, DB accesses, and whether keysets were authorized; but due to the fact that symbolic programs don't execute linearly from inputs to output, these models can be slightly confusing. Consider the following code:

```lisp
(if (x < 10)
  (read accounts "a")
  (read accounts "b"))
```

A falsifying model for this expression will actually contain values for *both* reads, even though a concrete execution would only perform one.

We plan to improve this experience by synthesizing a linear execution trace from the model, similar to what something like the Chrome DevTools debugger might show. This would contain a full walk through a single concrete execution path, without any superfluous DB accesses or variable bindings from paths not taken. This work is [currently in-progress](https://github.com/kadena-io/pact/issues/132), and we'll share more about this in an upcoming post.

### Covering all of the language

For the initial release, we punted on some parts of the language that are less-frequently used and harder to model in Z3. In particular, we're actively working on adding [support for sequences to sbv](https://github.com/LeventErkok/sbv/pull/394) to model lists in Pact.

### Stronger defaults

Once we have `defproperty`, we'll have all of the necessary building blocks to write a `pure` property, asserting that a function doesn't read or write the database, or abort the current transaction. Our plan is to make something like this the default, so that all non-pure code must be explicitly marked.

## More to come

Those were just a few of the projects we have on our roadmap, as we work towards a great environment for writing correct contracts. Of course, there's a lot to do, and we're hiring, so if you made it this far and you're interested in our work, definitely [get in touch](mailto:joel@monic.co)!
