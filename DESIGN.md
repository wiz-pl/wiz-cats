# Design

How categories are represented here, and why. The short version: **bundled structures,
hom-*types* with Wiz's own (observational) equality, two universe levels, and laws as
proof fields**. The rest of this file explains the choices and what Wiz's observational
type theory (OTT) buys.

## Hom-types with propositional equality, not E-categories

In intensional MLTT a category is usually one of:

* an **E-category** (setoid-enriched): each `Hom X Y` carries its own equivalence
  relation `≈`, and composition must respect it. Every construction then has to prove
  that its operations respect every `≈` involved, and equality of functors and of
  natural transformations is a further layer of setoids. This is what you do when your
  equality has no funext and no quotients.
* a category whose hom-types are **sets with the identity type**, plus funext as an
  axiom (Lean's Mathlib, Coq's UniMath with univalence, …).

Wiz's equality is observational (Pujet and Tabareau's TTobs, CoreSpec §8). The equation
`a = b` is a proposition that *computes* by the type of `a` and `b`:

* at a function type it is pointwise equality: `f = g` *is* `(0 x : A) → f x = g x`,
  so `funext` is the identity function (`lib/Logic.wiz`);
* at a proposition it is `True`: proofs are irrelevant definitionally, so two proofs of
  a law are convertible, and an equation between structures ignores their proof fields;
* at a Σ type (every structure is one) it is the Σ of the equations of the components;
* at `Prop` it is logical equivalence (propext).

So the setoid structure of an E-category is *already* the equality of the hom-types,
for every hom-type, and the extensional reasoning MLTT needs setoids for comes for free.
We use plain hom-types and `=`. The one thing OTT does not give us is a definitional
`cast A A e x ≡ x` (regularity); Wiz has it only at inert types and offers the axiom
`castRefl` otherwise (CoreSpec §8.4a). It matters for equations of structures (below),
and J gets around it everywhere but one place (`UnitCounit.round`).

## Universe levels

`Category.{u, v}` has objects in `Type u` and morphisms in `Type v`:

```
structure Category.{u, v} where
  Obj : Type u
  Hom : Obj → Obj → Type v
  …
```

so the structure lives in `Type (max (u+1) (v+1))`. The category of types `Types.{u}` is
a `Category.{u+1, u}`; a small category is `Category.{u, u}`; the functor category
`[C, D]` for `C : Category.{u₁, v₁}`, `D : Category.{u₂, v₂}` is a
`Category.{max u₁ v₁ u₂ v₂, max u₁ v₂}`, as in Mathlib. Hom-types are `Type v`, never
`Sort v`: the equality `=` is only formed at types whose universe is never `Prop`
(CoreSpec §8.1), so a hom-*proposition* (a preorder as a thin category) would need a
`ULift` or a separate structure. Wiz is not cumulative, so where a construction needs a
category one level up (Yoneda: presheaves on `C` land in `Types.{v}`), the levels are
written out and `ULift` is used where a type must move up.

## Bundled, and laws as fields

Categories, functors and natural transformations are bundled structures. Wiz's classes
have no `extends` and no coercions yet (stage 7b), so a `class Category (Obj : Type u)`
in Mathlib's style would buy us instance search for the hom-type and composition
notation, at the cost of carrying the instance through every construction, which
Wiz's resolver must find from an object type that is often a variable (`C.Obj` for a
bundled `C`). We use bundled structures with projections (`C.Hom X Y`, `C.comp f g`)
and local notation where it helps.

Composition is in diagrammatic order, `comp f g : Hom X Z` for `f : Hom X Y`,
`g : Hom Y Z` (`f ≫ g` in Mathlib's notation), so the implicit objects come in the
order the morphisms are written. The notation itself is defined but not used: with a
bundled category the elaborator can't find `C` from `f : C.Hom X Y` (FINDINGS.md, B5),
so the library writes `C.comp f g`.

The laws (`id_comp`, `comp_id`, `assoc`) are fields whose types are equations, so they
are propositions, so:

* two categories with the same data are equal, whatever their proofs;
* equality of two **functors** `F G : C ⥤ D` (a Σ of `obj`, `map` and the laws) computes
  to `(e : F.obj = G.obj) × (cast … F.map = G.map)`; the laws drop out;
* equality of two **natural transformations** `α β : F ⟶ G` (a Σ of `app` and the
  naturality proof) computes to `(0 X : C.Obj) → α.app X = β.app X`: `NatTrans.ext` is
  the identity function, and the functor category's laws are proved pointwise from
  `D`'s.

That last point is the main win over MLTT: there, `NatTrans.ext` needs funext (an
axiom) and proof irrelevance for the naturality square (a theorem about the hom-sets
being sets, or another axiom).

**Equality of structures with data fields** is where the cast bites. `F = G` for functors
computes to `(e : F.obj = G.obj) × (cast … F.map = G.map)`, and the cast is at a type
variable (`D.Hom`), so it is stuck even when `F.obj` and `G.obj` are convertible; worse,
the cast of a function casts its arguments backwards too, so `castRefl` (which removes
one outer cast) is not enough. The same happens to a plain pair `(a, b) = (a', b')`.
Two ways round it:

* **Congruence by J.** `pairEq e₁ e₂ := eqCongr2 (fun x y => (x, y)) e₁ e₂`: no cast is
  ever written, and no axiom is used. For functors, `Fun.ext` does the same along an
  equation of the maps, with the laws carried by a helper (`Fun.mkOf`) that transports
  them along the equation; proof irrelevance makes the helper at the two ends
  convertible with the two functors. This covers functors with the same object map.
* **`castRefl`**, componentwise, where the later field's type doesn't mention the
  earlier ones (`UnitCounit.round`).

Functors whose object maps are only propositionally equal are not handled; Mathlib's
`eqToHom` approach would be the next step.

## Quantities

Wiz checks usage (QTT) everywhere, proofs included (FINDINGS.md, G2): a proof that passes
a variable to an unerased argument uses it. So the library follows three rules:

* every law takes its morphisms and objects at quantity 0
  (`id_comp : {X Y : Obj} → (0 f : Hom X Y) → …`), and every equality lemma its proofs;
* categories, functors and natural transformations whose data is used are bound
  `{ω C : Category}`: implicit binders default to 0;
* a proof by cases or induction (which needs its argument) is a separate function with
  unerased binders, passed where an erased one is expected: the kernel accepts it by
  subtyping, since a Π that is a proposition ignores quantities.

## Limits, adjunctions, Yoneda

* A limit is a structure: the object, the cone's morphisms, the lifting function and its
  equations, and uniqueness (`uniq : (0 h : Hom Z obj) → h = pair (h ≫ fst) (h ≫ snd)`).
  Uniqueness up to isomorphism is proved for terminal objects and products.
* An adjunction is primarily the natural hom-bijection (`to`, `from`, the two inverse
  laws, naturality of `to` on both sides; naturality of `from` is derived). The
  unit-counit form is a second structure; each converts into the other.
* The Yoneda lemma is stated for presheaves `P : Cᵒᵖ ⥤ Types.{v}` on a
  `C : Category.{u, v}`, so the hom-types of `C` are objects of `Types.{v}` and no
  `ULift` is needed. The Yoneda embedding lands in the functor category
  `[Cᵒᵖ, Types.{v}]`, a `Category.{max u (v+1), max u v}`.

The files are listed in README.md.
