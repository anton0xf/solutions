# 2. Lists internal representation
Date: 2025-09-04

## Status
Accepted

## Context
`(list ...)` values should be represented in interpreter memory somehow.

It's usually represented as a consed list in lisps.
But it also could be represented as an array (slice), which is more memory efficient.
And I initially used slice.

But then I realized that I cannot support `set-car!` and `set-cdr!` in that way.
Suppose you have two references: to the head of some list (`a-list`)
and to its `cdr` (`a-tail`).
And when you call `(set-cdr! a-list another-list)` it sould change `a-list`
but preserve `a-tail`.

## Decision
Use consed lists to represent lists.
