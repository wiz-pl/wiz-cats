# Findings

What formalising category theory showed about Wiz, as of wiz master `9596a24`
(2026-11-12). Each entry: what happened, a minimal reproducer (the files under
`repro/` are the reproducers, each checked with `wiz check -I src repro/NAME.wiz`), and
what this library does instead. Severity:

* **bug**: wrong behaviour (a correct program rejected, or a wrong one accepted);
* **gap**: something abstract mathematics needs that Wiz lacks;
* **papercut**: works, but costs time.

Timings are rough (single runs through `light` on a shared machine), not measurements.

## Status (2026-11-12)

Fixed in wiz PRs that are not merged yet; branch `cleanup` of this repository uses them
(a local toolchain: master + #230 + #239 + #221 + #227) and drops the workarounds:

* **B1** (levels fixed by an implicit argument's type): fixed in #239. The explicit
  levels on the lemmas (`eqTrans.{v₃} (eqCongr.{v₂, v₃} …)`) and the ascriptions on
  constructor applications are gone; the error, where a level really is unknown, now
  names the constant ("could not infer the universe level u of k").
* **B5** (a structure-valued hole under a projection): fixed in #239 (a first-order
  approximation, as Lean's for `Category.comp ?C`). `(C := C)` is gone, and `f ≫ g`
  works; the proofs use it where a law isn't rewritten with.
* **B6** (`rw` "expected: C ⥤ D, inferred: C ⥤ D"): fixed in #239. P11 (`rw` doesn't
  try `rfl`) is not.
* **B7** (a hole in a binder's type): fixed in #239; the `(D := Types)` in the Yoneda
  binders is gone.
* Not fixed: B2, G2 (proofs count usage; wiz agent prf-conv-2), B3, B4 (`max` levels:
  `eqCongr2.{u, v, max u v}` stays), G1 (Logic's lemmas at `Type`; `congrArg` is
  universe-polymorphic in lib/Nat.wiz since #221), G3–G8, the papercuts except as
  noted. P9 is partly fixed (the parameters of `Equaliser.mk`/`Pullback.mk` are still
  passed by name).

The repro tests record the new state: `repro/b1-levels`, `b5-proj-hole` and
`b7-binder-holes` check without errors; `b6-rw-functor` shows the rewritten goal.

## Bugs

### B1. Universe levels fixed only by an implicit argument's type are never solved (fixed in wiz #239)

"could not infer a universe level; add a universe parameter or annotation", pointing at
the start of the declaration, for programs that are well typed and whose levels are
determined. Two shapes (`repro/b1-levels.wiz`):

```
structure Box.{u, v} where
  T : Type u
  R : T → T → Type v
  r : (x : T) → R x x
structure S2.{u, v} (B : Box.{u, v}) where
  law : (x : B.T) → B.r x = B.r x
def ok.{u, v} (B : Box.{u, v}) (s : S2 B) : (x : B.T) → B.r x = B.r x := fun x => eqSymm (s.law x)
-- rejected: the same term as a constructor argument
def bad.{u, v} (B : Box.{u, v}) (s : S2 B) : S2 B := S2.mk (fun x => eqSymm (s.law x))
```

(`eqSymm.{u}` is `Eq.symm` at `Type u`, `src/Cats/Eq.wiz`.) And, with no expected type:

```
-- rejected
def e₁ … : Fun.mk o m₁ i₁ c₁ = Fun.mk o m₂ i₂ c₂ := …
-- accepted
def e₂ … : (Fun.mk o m₁ i₁ c₁ : C ⥤ D) = Fun.mk o m₂ i₂ c₂ := …
```

Likely cause (from reading `Wiz/Elab/Command.lean`, `solveSortConstraints`):
metavariables are untyped, so solving `?C := C` for `{C : Category.{?a, ?b}}` never
unifies `Category.{?a, ?b}` with the type of `C`, and `?a`, `?b` stay unsolved unless
the result type pins them. Only holes of type `Sort ?l` get a recorded constraint, which
is re-checked after elaboration by inferring the solution's type; that loop runs twice,
skips solutions that still contain holes, and ignores solutions whose type it can't
infer. The error gives no position inside the declaration and doesn't say which
constant's level is missing, so finding the culprit took a bisection with an
`axiom sorry`, whose own level then hit the same bug unless written `sorry.{0}`.

Here: explicit levels on the lemmas inside constructor arguments
(`eqTrans.{v₃} (eqCongr.{v₂, v₃} …)`) and type ascriptions on constructor applications.
Both are all over `src/Cats/Category.wiz`. This is the most frequent failure so far.

### B2. `refl x` checks `x` as if it were used at ω

```
structure P where
  a : Nat
  b : Nat
def lem0 (0 n : Nat) : n = n := refl n
def ok {0 p : P} : p.b = p.b := lem0 p.b    -- accepted
def bad {0 p : P} : p.a = p.a := refl p.a   -- rejected: cannot project p.1 … p has quantity 0
```

`refl` is a proof and has no usage (CoreSpec §8.1), but its argument is checked in the
unerased context, so a projection of an erased structure in it is refused. The same
happens for `rfl`: `F ⋙ Fun.id D = F := rfl` with `D` implicit is rejected ("cannot
project (Fun.id D).1 … uses D, which has quantity 0"). (`repro/b2-refl-usage.wiz`)
Here: the categories are bound at ω where `rfl` mentions them.

### B3. `rfl` at an equation of two categories takes over 2 GB

```
def Category.op.{u, v} (C : Category.{u, v}) : Category.{u, v} := …   -- src/Cats/Constructions.wiz
def slow.{u, v} (C : Category.{u, v}) : Category.op (Category.op C) = C := rfl     -- killed: 2 GB, 17 s
def fast.{u, v} (C : Category.{u, v}) : Category.op (Category.op C) = C := refl C  -- 0.5 s, 100 MB
```

The two sides are convertible (structure η), and `refl C` is accepted at once. What
blows up is the *computed equation*: `#check Category.op_op` (of the `refl C` version)
is killed the same way, so it is the quotation of `C.op.op = C` computed to a Σ over the
seven fields, each with a cast along a `transp` whose motive is the rest of the Σ type,
which contains the equations of the later fields, and so on: the size grows
exponentially with the number of dependent fields. The elaborator's `rfl` (13n) reads
the sides back out of that computed equation, hence the difference. (The equation of
two functors, four fields, already prints as 12 000 characters, G5.) Not in `repro/` (it would take the test runner's memory); the lines above
reproduce it.
Here: `refl C`.

### B4. The level unifier doesn't normalise: `?u+1 = max (u+1) (u+1)` fails

`eqCongr (fun y => y) (refl x)` for `x : A × B`, `A B : Type u`, is "universe level
mismatch: ?u0+1 vs max (u+1) (u+1)" (`repro/b4-level-max.wiz`); the same with
`Sort (max (imax (u₁+1) (imax (u₁+1) (imax (v₁+1) (v₂+1)))) 0)` for a Σ type of
functions. Both sides are `l+1` after normalisation (`Level.normalize` exists, the
kernel uses it). Here: explicit levels, or a `let AB : Type u := A × B` that fixes the
level of the type.

### B5. A structure-valued hole under a projection is never solved (fixed in wiz #239)

```
def lem {ω C : Category} {X Y Z : C.Obj} (0 f : C.Hom X Y) (0 g : C.Hom Y Z) (0 h : C.Hom X Z)
    (0 e : C.comp f g = h) : h = C.comp f g := …
def bad … (0 e : C.comp f g = h) : h = C.comp f g := lem _ _ _ e
-- type mismatch: expected (?m6 C X Y Z f g h e).2.2.2.1 (?m7 …) … = ?m12 …, inferred
-- C.2.2.2.1 X Y Z f g = h (unification problem is outside the pattern fragment)
```

(`repro/b5-proj-hole.wiz`.) A structure is an anonymous Σ, so `C.comp` is the
projection `C.2.2.2.1`, and `(?C).2.2.2.1 ?f ?g =?= C.2.2.2.1 f g` is not decomposed into
`?C =?= C`. (In Lean, `Category.comp ?C ?f ?g` is an application of a constant and the
first-order approximation solves it.) So no lemma about morphisms of an implicit
category can find the category from a morphism equation: every such use needs
`(C := C)`. The holes for the objects and morphisms are then found. It also makes
the notation `f ≫ g` (`Category.cmp`, with `{ω C : Category}` implicit) unusable: the
category is never found from `f : C.Hom X Y`.
Here: `(C := C)` (`Product.unique`, the Yoneda embedding), and `C.comp f g` instead of
`f ≫ g` everywhere.

### B6. `rw` with a functor law: "expected: C ⥤ D, inferred: C ⥤ D" (fixed in wiz #239)

In a goal about the unit of an adjunction, `rw (F.map_comp (U.unit.app X) (G.map f))`
fails with "rewrite: type mismatch / expected: C ⥤ D / inferred: C ⥤ D"
(`repro/b6-rw-functor.wiz`). The same `rw` with a functor law at plain objects works.
The two printed types are the same; the difference is invisible (levels are not printed,
P5, or a hole). `U.unit.app X : C.Hom ((Fun.id C).obj X) ((F ⋙ G).obj X)`, so the
objects are only convertible with `X` and `G.obj (F.obj X)`. Here: every proof about
adjunctions is a term, a chain of `eqTrans` and `eqCongr` (`src/Cats/Adjunction.wiz`).

### B7. A hole in a binder's type is not solved before the body needs it (fixed in wiz #239)

```
def bad {ω C : Category} {X : C.Obj} {P : Category.op C ⥤ Types}
    (α : NatTrans (Category.yo C X) P) {Y : C.Obj} (f : C.Hom Y X) :
    α.app Y (C.comp f (C.id X)) = P.map f (α.app X (C.id X)) :=
  α.naturality f (C.id X)
-- function expected: α.2.1 ?Y ?Y' f : (?m1 C X P).2.2.2.1 … = …
```

`NatTrans {C D : Category} (F G : C ⥤ D)`: the hole for `D` in the type of `α` should be
`Types` (from `P : Category.op C ⥤ Types`), but while the body is elaborated the type
of `α` still has `?m1 C X P` for it, so the naturality equation is about `(?m1 C X
P).comp …`, which can't compute to a function of `g`. Writing `(D := Types.{v})` in the
binder fixes it (`repro/b7-binder-holes.wiz`). Here: the Yoneda lemma's binders name
both categories.

## Gaps

### G1. The equality lemmas of lib/Logic.wiz are at `Type` only

`Eq.symm`, `Eq.trans`, `Eq.congrArg`, `funext`, `congrFun` take `{A : Type}`, so every
equation between morphisms of a category whose hom-types live in `Type v` needs its own
copy. Here: `src/Cats/Eq.wiz` (`eqSymm.{u}`, `eqTrans`, `eqCongr`, `eqCongr2`, `eqJ`).

### G2. A proof uses the variables it passes to unerased arguments

Proofs are irrelevant and erased, but usage checking still counts them: a variable at
quantity 0 can't be passed to a lemma's ω argument, even inside a proof
(`repro/g2-proof-usage.wiz`).

```
def lem (n : Nat) : n = n := refl n
def r {0 n : Nat} : n = n := lem n    -- rejected: n declared with quantity 0 but used ω
```

In category theory almost everything implicit is erased (`{F G H : C ⥤ D}` in the
vertical composite of natural transformations), and every law is applied to morphisms
built from them (`D.assoc (F.map f) (α.app X) (β.app Y)`), so with the obvious
signatures every proof about natural transformations is rejected. Here: every law
takes its morphisms at 0 (`id_comp : {X Y : Obj} → (0 f : Hom X Y) → …`), every
equality lemma takes its proofs at 0 (`eqTrans (0 e₁ : a = b) (0 e₂ : b = c)`), and
categories whose data is used are bound `{ω C : Category}`. Checking the arguments of
an application whose type is a proposition in the erased context would remove the need
for all of it (Lean erases proofs wholesale).

### G3. Implicit binders default to quantity 0, so `{C : Category}` can't be projected

`def Category.cmp {C : Category} {X Y Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z) := C.comp f g`
is rejected ("cannot project C.2 … C, which has quantity 0 … a structure can't be held
at a quantity other than ω yet"): a bundled category is data, and its implicit binders
must be written `{ω C : Category}`. The message is accurate but long and talks about
linear structures, which aren't involved.

### G4. `transp` can't take an equation that has computed

`transp P p e` needs the type of `e` to be an equation as written. At a function type
or a structure an equation always computes (`m₁ = m₂` is `(0 X) → (0 Y) → (0 f) → …`),
so `transp` reports "expected a proof of an equation, got (0 X : …) → …". Here: `eqJ`,
J as a function, whose argument has the type `a = b` at a variable type.

### G5. Equality of functors: the cast in the computed equation is stuck

`F = G` for `F G : C ⥤ D` computes to a Σ whose second component is
`cast (…) (F.map (cast X) (cast Y) (cast f)) = G.map X Y f`: the arguments of `map` are
cast backwards along `C.Obj = C.Obj`, and the result forwards along a `transp` over the
whole remaining Σ type (the printed equation is about 12 000 characters). Even when
`F.obj ≡ G.obj` none of the casts compute (the types are variables, and regularity holds
only at inert types), and `castRefl` removes only the outer one, not the dependent
casts of the arguments. Here: `Fun.ext` proves two functors with the same object map
equal from an equation of their maps, by J and proof irrelevance, without `castRefl`
(DESIGN.md). Functors whose object maps are only propositionally equal are not handled
yet.

### G6. Equality of pairs, componentwise, needs an axiom

`(a, b) = (a', b')` at `A × B` computes to `(0 e : a = a') × (cast B B ê b = b')`, and
the cast at a type variable `B` is stuck, so the obvious proof `⟨e₁, e₂⟩` is rejected
and the componentwise proof needs `castRefl`. Congruence by J,
`eqCongr2 (fun x y => (x, y)) e₁ e₂`, needs no axiom, and that is what `pairEq` does
(`src/Cats/Eq.wiz`; the product category is axiom-free, `#print axioms`). The same
holds for every structure: a later field is compared after a cast along the equations
of the earlier ones, even when its type doesn't depend on them. `UnitCounit.round` (two
natural-transformation fields) is proved componentwise with one `castRefl`; the
J route would need the `Fun.mkOf` trick of `Fun.ext` (laws transported along the
equation). A cheap improvement: regularity for the non-dependent case (the cast
`cast B B ê b` between syntactically equal types).

### G7. Proof components of an erased subtype element can't be reached

`ι ≫ f = ι ≫ g` in `Types`, with `ι = fun p => p.1` on `E = (a : A) × (f a = g a)`,
computes to `(0 p : E) → f p.1 = g p.1` (funext binds `p` at 0). The obvious proof
`fun p => p.2` is rejected ("cannot project p.2 … p, which has quantity 0", B2 again);
`let 0 (x, e) := p; e` gives `e : P x`, not `P p.1` (the tuple `let` is not dependent);
an identity `(0 h : P) → P := h` is rejected ("h declared with quantity 0 but used 1").
What works: a function with an *unerased* binder, `sigmaProp : (p : (a : A) × P a) → P p.1
:= fun p => p.2`, passed where the erased one is expected, which the kernel accepts by
subtyping (a Π that is a proposition ignores quantities, CoreSpec §11.5), but only with
all its implicit arguments given: the elaborator's unifier doesn't do that subtyping
("quantity mismatch") when holes are left. Here: `sigmaProp (A := A) (P := …)`.

The same mismatch, the other way round, for proofs by induction: a law takes its
argument erased (`map_id : (0 A : Type) → (0 x : f A) → map id x = x`, G2), and an
erased value can't be matched on, so the proof by cases or induction is a separate
function with unerased binders (`Option.map_id' : (x : Option A) → …`), passed by
subtyping. That works only if the field's own type variables are explicit
(`fun A => Option.map_id' (A := A)`): an implicit lambda is inserted for `{A}` and
can't be named ("unexpected implicit binder"), and without the name the hole for `A`
makes the elaborator's unifier refuse the quantities. Here: `LawfulFunctor`'s types
are explicit binders (`src/Cats/Examples.wiz`).

Related: a Σ binder can't carry a quantity in a term (`(a : A) × (0 _ : f a = g a)` is
"function expected 0 : Nat"), so a subtype's proof component is ω, and building one
from an erased proof is rejected (G2). The equaliser's and pullback's `lift` take
their proof at ω for that reason.

### G8. lib/Functor.wiz's `Functor` is at `Type → Type` and has no laws

So the functors that the instances give are functors on `Types.{0}` only, and the laws
are a separate structure (`LawfulFunctor`, with proofs for `Option` and `List`). A
universe-polymorphic `Functor.{u, v} (f : Type u → Type v)` and a `LawfulFunctor` class
in the library would make `Types.{u} ⥤ Types.{v}` available for every instance.

## Papercuts

* **P1.** `max` takes exactly two levels: `Type (max u₁ v₁ u₂ v₂)` is "function expected
  Type : Type 1"; write `max (max u₁ v₁) (max u₂ v₂)`.
* **P2.** A structure's universe is inferred too large: `NatTrans F G` (data
  `app : (X : C.Obj) → D.Hom (F X) (G X)` and a proof field quantifying over `C.Hom X Y`)
  is put in `Type (max (max u₁ v₂) (max u₁ v₁))`: the proof field's binders count.
  Here: an explicit `: Type (max u₁ v₂)`.
* **P3.** An equation of structures ends in the marker component: `α = β` for natural
  transformations is `(0 e : (0 X) → α.app X = β.app X) × True × ((0 fields✝ : Enum
  [fields✝]) → True)`, so `NatTrans.ext` is `(h, (), fun _ => ())`, not `h`.
* **P4.** Errors print fields as projections: `G.2.1 (F.1 X) (F.1 X) (F.2.1 X X (C.2.2.1 X))`
  for `G.map (F.map (C.id X))`. With five-field structures this is hard to read.
* **P5.** `#check Types` prints `Types : Category`, without the levels; `#check @NatTrans.ext`
  prints its result type as the computed equation (`(0 e : (0 X : C.1) → α.1 X = β.1 X) × …`),
  not as `α = β`.
* **P6.** `@f.{u}` does not parse (`@castRefl.{v₂} A e a`); named arguments
  (`castRefl.{v₂} (A := …) e a`) work.
* **P7.** A local whose type has implicit binders (`m₁ : {X Y : C.Obj} → C.Hom X Y → …`),
  elaborated against a hole (`⟨m₁, refl m₁⟩` with no expected type), is eta-expanded
  with fresh holes for the implicits that aren't tied to the new binders:
  `fun X Y => m₁ ?m108 ?m109`; `fun X Y f => hmap f` gives `hmap ?a ?b f`. Here:
  `@hmap X Y f`. The same makes `castRefl (A := T) (refl T) m` unusable for a local `m`
  of such a type `T` (`{X : C.Obj} → {ω Y : D.Obj} → …`, the type of an adjunction's
  `from`): `m` is applied to fresh holes, its type becomes `D.Hom (F.obj ?X) ?Y`, and
  the equation `T = …` computes to `False` (different type formers). Here: the
  equation of two adjunctions (round trip) is stated pointwise only.
* **P8.** The anonymous constructor `⟨…⟩` does not see that its expected type, an
  equation at a Σ, computes to a Σ ("needs a structure, a pair … not (m₁, …) = (m₂, …)");
  a tuple `(a, b)` is elaborated without the expected type and then fails on the
  quantities ("quantity mismatch": `(X : C.1) → …` against `(0 X : C.1) → …`).

* **P9.** Holes in an application's arguments are not solved from the expected type
  first: `NatTrans.ext _ _ h` against `vcomp (id F) α = α` fails with "outside the
  pattern fragment" (`h`'s type `?α.1 X = ?β.1 X` is unified before the result type).
  And in a field of `Category.mk` the expected type of a law still has holes for the
  earlier fields (`?m3 C D X X Y (?m2 C D X) α = α`), so the equation has not computed
  and `⟨…⟩` rejects it. Even the parameters of the structure are still holes while its
  fields are elaborated: in `Equaliser.mk E (fun p => p.1) …` against
  `Equaliser Types f g`, the field `cond` is checked against `(?m2 …).comp …`, with the
  category itself a hole, and `fun p => p.1` against a hole ("cannot project from a
  value of type ?m13 A B f g"). Lean elaborates against the expected type first
  (`elab_as_elim` aside, it postpones the arguments). Here: the laws of the functor
  category are separate lemmas, and the limits in `Types` pass the parameters by name
  (`Equaliser.mk (C := Types.{u}) (f := f) (g := g) …`) and annotate binder types.
* **P10.** No generalised field notation: `S.hom_ext` for `S : Terminal C` (meaning
  `Terminal.hom_ext S`) and `C.op.op` are "no field 'hom_ext' in a value of type
  (0 fields✝ : Enum [fields✝]) → Unit…": only real fields are found, and the error
  names the Σ's last component instead of the structure. Also, `Option.functor.map`
  (the field `map` of the constant `Option.functor`) is read as a field `functor` of
  `Option`. Here: `Terminal.hom_ext S`, `Category.op (Category.op C)`,
  `(Option.functor).map`.

* **P11.** `rw` doesn't try `rfl` afterwards: after `rw (C.id_comp f)` the goal `f = f` is
  left open (`repro/b6-rw-functor.wiz`).
* **P12.** A `let` in a proof binds at ω, so `let η := U.unit.app X; …` in a proof is
  rejected when `X` is erased (G2): write `let 0 η := …`.

* **P13.** Names that shadow are printed the same: in the expected type of a field of
  `Fun.mk`, the field's own implicit `{X Y Z}` and the definition's `X` are all printed
  `X`, so `(0 x : C.2.1 X X)` means "from the field's `X` to the definition's `X`".
  Binders get primes (`n'`), context variables don't.
* **P14.** A law that is a function of an erased variable can't be written as a plain
  lambda inside a constructor: `(fun Y => fun g => C.id_comp g)` against the computed
  `(0 x : C.Hom Y X) → …` is "quantity mismatch", because the lambda was elaborated
  before the equation computed (P9). `fun (0 g : C.Hom Y X) => …` works.

* **P15.** A hole of type `Unit` is not solved: `(Monoid.toCategory M).comp 2 3`, whose
  objects are of type `Unit`, is "could not infer implicit argument X" (η for `Unit`
  makes `()` the only solution). Here: `(X := ()) (Y := ()) (Z := ())`.

## What works well

* `structure Category.{u, v}` with dependent fields, implicit-binder fields and proof
  fields; `Types.{u} : Category.{u+1, u}` with all three laws by `rfl`.
* `NatTrans.ext` is (almost) the identity: funext and proof irrelevance are definitional.
* Associativity of functor composition, `(F ⋙ G) ⋙ H = F ⋙ (G ⋙ H)`, is `rfl`
  (structure η in conversion).
* Checking is fast. `wiz check --no-cache` (rough single runs, each including its
  imports): Eq 1.4 s, Category 1.6 s, Constructions 1.9 s, Limits 2.4 s, Adjunction
  4.3 s, Yoneda 2.5 s, Examples 2.6 s, all under 105 MB. The one blow-up is B3.
* `#print axioms`: everything is axiom-free except `UnitCounit.round` (`castRefl`).
* `rw` works on goals about morphisms of a bundled category (`rw (C.comp_id f)`).
