# Noq

Not [Coq](https://coq.inria.fr/). Simple expression transformer that is not Coq.

## Quick Start

```console
$ cargo run ./examples/add.noq
```

## Main Idea

The Main Idea is being able to define transformation rules of symbolic algebraic expressions and sequentially applying them.

## Expression

Current expression syntax can be defined roughly like this:

```
<expression> ::= <operator-0>
<operator-0> ::= <operator-1> ((`+` | `-`) <operator-0>)*
<operator-1> ::= <operator-2> ((`*` | `/`) <operator-1>)*
<operator-2> ::= <primary> (`^` <operator-2>)*
<primary> ::= (`(` <expression> `)`) | <application-chain> | <symbol> | <variable>
<application-chain> ::= (<symbol> | <variable>) (<fun-args>)+
<symbol> ::= [a-z0-9][_a-zA-Z0-9]*
<variable> ::= [_A-Z][_a-zA-Z0-9]*
<fun-args> ::= `(` (<expression>),* `)`
```

## Rules and Shapes

The two main entities of the languare are Rules and Shapes. A rule defines pattern (head) and it's corresponding substitution (body). The rule definition has the following syntax:

```
<name:symbol> :: <head:expression> = <body:expression>
```

Here is an example of a rule that swaps elements of a pair:

```
swap :: swap(pair(A, B)) = pair(B, A)
```

Shaping is a process of sequential applying of rules to an expression transforming it into a different expression. Shaping has the following syntax:

```
<expression> {
  ... sequence of rule applications ...
}
```

For example here is how you shape expression `swap(pair(f(a), g(b)))` with the `swap` rule defined above:

```
swap(pair(f(a), g(b))) {
  all | swap
}
```

The result of this shaping is `pair(g(b), f(a))`.

### Anonymous rules

You don't have to define a rule to use it in shaping. You can directly describe it after the `|`:

```
swap(pair(f(a), g(b))) {
  all | :: swap(pair(A, B)) = pair(B, A)
}
```
