# wiz-cats

Category theory in [Wiz](https://github.com/wiz-pl/wiz), a dependently typed language
with observational equality, built with grail (Wiz's build tool).

It exists to try Wiz on abstract mathematics (universe polymorphism, structures,
equality) the way a stranger would, and to write down what that was like: see
[FINDINGS.md](FINDINGS.md). How categories are represented, and why, is in
[DESIGN.md](DESIGN.md).

## What is here

| file | contents |
|---|---|
| `src/Cats/Eq.wiz` | equality lemmas at every universe; J as a function; equality of pairs |
| `src/Cats/Category.wiz` | `Category.{u, v}`, functors `C ⥤ D`, composition and its laws (`Fun.comp_assoc`, `Fun.id_comp`, `Fun.comp_id`), `Fun.ext`, natural transformations, the category of types `Types.{u}`, fully faithful functors |
| `src/Cats/Constructions.wiz` | the opposite category (`op (op C) = C` definitionally), products of categories, functor categories |
| `src/Cats/Limits.wiz` | isomorphisms; terminal objects, binary products, equalisers, pullbacks as universal properties; terminal objects and products are unique up to isomorphism; the limits of `Types` |
| `src/Cats/Adjunction.wiz` | adjunctions as natural hom-bijections and as unit and counit with the triangle identities; each gives the other; the round trips |
| `src/Cats/Yoneda.wiz` | representable presheaves, the Yoneda lemma, the Yoneda embedding, which is fully faithful |
| `src/Cats/Examples.wiz` | the instances of lib/Functor.wiz (`Option`, `List`) as functors `Types ⥤ Types`, with their laws; a monoid as a one-object category, monoid homomorphisms as functors |
| `tests/` | what the definitions are (`#check`), what they compute (`#eval`), which use an axiom, and `inference.wiz`, the regression test for the findings that are fixed |
| `repro/` | the reproducers of FINDINGS.md, checked against the pinned toolchain (the fixed ones now check) |

Nothing is postulated except Wiz's own `castRefl` (propositional regularity), and only
`UnitCounit.round` uses it (`tests/axioms.wiz`). Function extensionality and proof
irrelevance are not axioms in Wiz: they are how its equality computes.

## Building

You need Nix with flakes. `nix develop` gives a shell with `wiz` and `grail` from the
Wiz flake, pinned in `flake.lock`.

```sh
nix develop
grail build      # check the library: a few seconds
grail test       # tests/ and repro/
```

A `repro/` test that fails means Wiz's behaviour changed: the test pins what the
pinned toolchain does, including the errors that are still open (and a fixed reproducer
that starts failing again is exactly what it is there for).

The library is written the way this toolchain can write it: composition is `f ≫ g`
where the category comes from the type of `f`, universe levels and implicit arguments
are inferred, and `#check` prints the stated type. B1, B5, B6 and B7 (FINDINGS.md) are
fixed at master `aeaa34ef` (2026-11-14), which is what `flake.nix`/`flake.lock` pin;
`tests/inference.wiz` keeps them fixed.

With tower, Wiz's toolchain manager, instead of the flake's `wiz`: `wiz-toolchain`
names the same commit (master `aeaa34ef`), and tower's `wiz` and `grail` shims pick it
up in this directory.

## Licence

GPL-3.0-or-later (LICENSE).
