# AGENTS.md
Learning project: formalizing category theory in Rocq.

## Build
- Must build with both Rocq 9.1 and Coq 8.20: don't use names or features available in only one of them (e.g. `From Stdlib`).
- `make` builds everything, `make clean` cleans.
- New `.v` files must be added to `_CoqProject` (logical name `ACat`).
- Work is done only when `make` passes with no new `Admitted`.

## Structure
- It's part of a bigger mono-repository: the git root is above this folder, so run git commands for this folder only and stage only files under it.
- `Intro*.v`: early exercises, independent of the rest.
- `Cat.v`: the `cat` record and basic notions (iso, epi/mono, initial/terminal).
- `Functor.v`, `ContrFunctor.v`, `CatC.v`: functors and the category of categories.
- `Structures/`: concrete structures (types, magma ... group, orders) as categories.
- `Util.v`: global helpers.

## Working with Anton
- It's an educational project, so don't write the code for me. Your role is to help when I'm stuck, suggest ways to implement things, explain Rocq and category theory, and discuss options.
- Show each step before taking it, and keep steps small.
- Never commit or push without asking.
- Start every commit message with `coq/cat:` and don't add a `Co-Authored-By` trailer.
