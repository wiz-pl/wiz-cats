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
| `src/Cats/Category.wiz` | `Category.{u, v}`, functors `C ⥤ D`, composition, `Fun.ext`, natural transformations, the category of types `Types.{u}`, fully faithful functors |
| `src/Cats/Constructions.wiz` | the opposite category (`op (op C) = C` definitionally), products of categories, functor categories |
| `src/Cats/Limits.wiz` | isomorphisms; terminal objects, binary products, equalisers, pullbacks as universal properties; terminal objects and products are unique up to isomorphism; the limits of `Types` |
| `src/Cats/Adjunction.wiz` | adjunctions as natural hom-bijections and as unit and counit with the triangle identities; each gives the other; the round trips |
| `src/Cats/Yoneda.wiz` | representable presheaves, the Yoneda lemma, the Yoneda embedding, which is fully faithful |
| `src/Cats/Examples.wiz` | the instances of lib/Functor.wiz (`Option`, `List`) as functors `Types ⥤ Types`, with their laws; a monoid as a one-object category, monoid homomorphisms as functors |
| `tests/` | what the definitions are (`#check`), what they compute (`#eval`), and which use an axiom |
| `repro/` | the reproducers of FINDINGS.md, tested against today's error messages |

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

A `repro/` test that fails means Wiz's behaviour changed, probably because the finding
was fixed: the test pins today's error message.

With tower, Wiz's toolchain manager, instead of the flake's `wiz`: `wiz-toolchain`
names the commit this repository is developed against (master 9596a24, the commit
`flake.lock` pins too), and tower's `wiz` and `grail` shims pick it up in this
directory.

## Licence

GPL-3.0-or-later (LICENSE).
