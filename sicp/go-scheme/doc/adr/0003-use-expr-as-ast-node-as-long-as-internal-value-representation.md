# 3. Use Expr as AST node as long as internal value representation
Date: 2025-11-19

## Status
Accepted

## Context
It's often a good idea to separate AST node types from internal value representation types.
But it requires a lot of boilerplate to convert between the two forms in both directions.

## Decision
for such a simple app, I decides, that it's acceptable to use Expr for both.
And it simplifies the code.

## Consequences
It could be confusing, that there are no such AST nodes as Function, but there is such Expr, for example.
