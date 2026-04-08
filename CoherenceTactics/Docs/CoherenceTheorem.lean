import CoherenceTactics.Docs.Support

open Verso Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option verso.exampleProject "."
set_option verso.exampleModule "CoherenceTactics.Examples"
set_option pp.rawOnError true


#doc (Manual) "The Coherence Theorem" =>
%%%
file := "The-Coherence-Theorem"
tag := "coherence-theorem"
%%%

In a monoidal category, the tensor product is associative and unital only up to
specified isomorphism. Thus
$`X \otimes (Y \otimes Z)` and $`(X \otimes Y) \otimes Z` are different objects, and so are
$`I \otimes X` and $`X`, or $`X \otimes I` and $`X`. To pass between such expressions one uses the
associator $`\alpha` and the left and right unitors $`\lambda` and $`\rho`.

In mathlib these are:

 * {name CategoryTheory.MonoidalCategoryStruct.associator}`associator`
   with notation `α_ X Y Z`
 * {name CategoryTheory.MonoidalCategoryStruct.leftUnitor}`leftUnitor`
   with notation `λ_ X`
 * {name CategoryTheory.MonoidalCategoryStruct.rightUnitor}`rightUnitor`
   with notation `ρ_ X`

For general tensor expressions, one can write several different composites of associators and
unitors with the same source and target. For example,

$$`
(((a \otimes (b \otimes (I \otimes c))) \otimes d) \otimes e)
  \cong
((I \otimes (a \otimes b)) \otimes (c \otimes (d \otimes e))).
`

One would like all composites of this kind to agree. If stated directly, this would be
an infinite axiom scheme, because there are infinitely many source and target expressions and
infinitely many formally different composites between them.

Mac Lane's coherence theorem says that one does not need to impose all of those equalities. It is enough to assume only the pentagon and triangle identities. In mathlib these are
{name CategoryTheory.MonoidalCategory.pentagon}`pentagon` and
{name CategoryTheory.MonoidalCategory.triangle}`triangle`.

The {name Mathlib.Tactic.Monoidal.pureCoherence}`monoidal_coherence` tactic is a direct implementation of this theorem. It proves that any two composites built only from associators and unitors with the same source and target are equal.

```CoherenceTactics.leanAnchor monoidalCoherencePure -showProofStates
```

{docstring Mathlib.Tactic.Monoidal.pureCoherence}

A proof of this theorem, and the one that underlies mathlib's implementation, follows the
accumulator-style normalization argument of Beylin and Dybjer.
For the original source, see {citehere beylinDybjer1996}[].

It begins by specifying a class of normal forms. The normal forms are the
left-associated expressions with the unit object on the far left:

$$`
((\cdots ((I \otimes X_1) \otimes X_2) \otimes \cdots) \otimes X_n).
`

For example, the normalization of the source object in the example above is
$$`
[((a \otimes (b \otimes (I \otimes c))) \otimes d) \otimes e]
= ((((I \otimes a) \otimes b) \otimes c) \otimes d) \otimes e.
`

The recursion is set up on $`[N \otimes X]`, where $`N` is already normalized, rather than on
$`[X]` directly. The definition proceeds by structural recursion on $`X`:

$$`
[N \otimes I] := N
`

$$`
[N \otimes (X \otimes Y)] := [[N \otimes X] \otimes Y]
`

$$`
[N \otimes A] := N \otimes A
`

for atomic $`A`.

At the same time we define a normalization isomorphism

$$`
\nu_{N,X} : N \otimes X \xrightarrow{\cong} [N \otimes X].
`

Again the definition is recursive:

$$`
N \otimes I \xrightarrow{\rho_N} N = [N \otimes I].
`

$$`
\begin{aligned}
N \otimes (X \otimes Y)
  &\xrightarrow{\alpha_{N,X,Y}} (N \otimes X) \otimes Y \\
  &\xrightarrow{\nu_{N,X} \otimes \mathrm{id}_Y} [N \otimes X] \otimes Y \\
  &\xrightarrow{\nu_{[N \otimes X],Y}} [[N \otimes X] \otimes Y]
   = [N \otimes (X \otimes Y)].
\end{aligned}
`

$$`
N \otimes A \xrightarrow{\mathrm{id}} N \otimes A = [N \otimes A]
`

where $`A` is atomic.

The key lemma is that a canonical composite built from associators and unitors does not affect the
result of normalization. If $`f : X \cong Y` is built only from associators and unitors, then the
composite

$$`
\begin{aligned}
N \otimes X
  &\xrightarrow{\mathrm{id}_N \otimes f} N \otimes Y \\
  &\xrightarrow{\nu_{N,Y}} [N \otimes Y]
\end{aligned}
`

is equal to the normalization isomorphism

$$`
\nu_{N,X} : N \otimes X \xrightarrow{\cong} [N \otimes X].
`

This is the point where the axioms of a monoidal category are actually used.
When $`f` is an associator, the proof uses the pentagon identity, and when $`f` is a unitor, the proof uses the triangle identity.

Once the key lemma is available, one proves the coherence theorem by taking $`N = I`. If
$`f, g : X \cong Y` are both built only from associators and unitors, then the key lemma gives

$$`
\nu_{I,Y} \circ (\mathrm{id}_I \otimes f) = \nu_{I,X}
\qquad\text{and}\qquad
\nu_{I,Y} \circ (\mathrm{id}_I \otimes g) = \nu_{I,X}.
`

Since $`\nu_{I,Y}` is an isomorphism, it follows that

$$`
\mathrm{id}_I \otimes f = \mathrm{id}_I \otimes g.
`

The original maps are recovered from these tensorings by the left unitor:

$$`
f = (\lambda_X)^{-1} \circ (\mathrm{id}_I \otimes f) \circ \lambda_Y
\qquad\text{and}\qquad
g = (\lambda_X)^{-1} \circ (\mathrm{id}_I \otimes g) \circ \lambda_Y.
`

Therefore $`f = g`.

The same proof works for bicategories, and the corresponding tactic is
{name Mathlib.Tactic.Bicategory.pureCoherence}`bicategory_coherence`.

{docstring Mathlib.Tactic.Bicategory.pureCoherence}

# Implementation
%%%
tag := "coherence-implementation"
%%%

The implementation has a shared core and two front ends. The shared core carries out the proof of
the coherence theorem. The monoidal front end and the bicategorical front end read their
respective goals into the syntax expected by that shared core.

## Shared Core
%%%
tag := "coherence-implementation-shared"
%%%

A monoidal category enters this implementation through the usual one-object bicategory dictionary:
an object $`X` is treated as a 1-morphism $`X : \ast \to \ast`, a morphism
$`f : X \to Y` is treated as a 2-morphism between those 1-morphisms, and tensor product is treated
as horizontal composition. Mathlib does not define monoidal categories literally as special cases of
bicategories, so the implementation has to carry out the proof in a form that both front ends can
use.

The tactics first convert Lean expressions into internal syntax (there are several such syntactic
categories; for example, {name Mathlib.Tactic.BicategoryLike.Mor₂}`Mor₂`). This syntax is shared by
the monoidal and bicategorical cases. In practice, one gives abstractly a monad expressing the
requirement that Lean expressions can be converted into internal syntax (in the case of
{name Mathlib.Tactic.BicategoryLike.Mor₂}`Mor₂`, the corresponding one is
{name Mathlib.Tactic.BicategoryLike.MkMor₂}`MkMor₂`). The concrete conversion method is given later,
in the sections on the front ends.
Then, in the shared part, one runs on this syntax the proof-generating algorithm for the coherence
theorem.

All of this runs in
{name Mathlib.Tactic.BicategoryLike.CoherenceM}`CoherenceM`,
which extends {name Lean.Meta.MetaM}`MetaM` with the context and caches needed by this proof.

```CoherenceTactics.leanDecl (module := Mathlib.Tactic.CategoryTheory.Coherence.Datatypes)
Mathlib.Tactic.BicategoryLike.Context
Mathlib.Tactic.BicategoryLike.State
Mathlib.Tactic.BicategoryLike.CoherenceM
```

The declarations below give the syntax corresponding to 2-morphisms and the monad expressing that
Lean expressions can be converted into this syntax.

```CoherenceTactics.leanDecl (module := Mathlib.Tactic.CategoryTheory.Coherence.Datatypes)
Mathlib.Tactic.BicategoryLike.Mor₂
Mathlib.Tactic.BicategoryLike.MkMor₂
```

With this setup in place, the declarations below give the algorithm that generates proof terms from
the proof of the coherence theorem.

The normalized 1-morphisms from the proof appear in Lean as
{name Mathlib.Tactic.BicategoryLike.NormalizedHom}`NormalizedHom`:

```CoherenceTactics.leanDecl (module := Mathlib.Tactic.CategoryTheory.Coherence.Datatypes)
Mathlib.Tactic.BicategoryLike.NormalizedHom
```

The recursive normalization procedure returns
{name Mathlib.Tactic.BicategoryLike.Normalize.Result}`Normalize.Result`,
which packages together the chosen normal form and the coherence isomorphism into it:

```CoherenceTactics.leanDecl (module := Mathlib.Tactic.CategoryTheory.Coherence.PureCoherence)
Mathlib.Tactic.BicategoryLike.Normalize.Result
```

The function that constructs this data is
{name Mathlib.Tactic.BicategoryLike.normalize}`normalize`:

```CoherenceTactics.leanDecl (module := Mathlib.Tactic.CategoryTheory.Coherence.PureCoherence)
Mathlib.Tactic.BicategoryLike.normalize
```

The key lemma from the mathematical proof appears as
{name Mathlib.Tactic.BicategoryLike.naturality}`naturality`,
and the final theorem proved from it appears as
{name Mathlib.Tactic.BicategoryLike.pureCoherence}`pureCoherence`:

```CoherenceTactics.leanDecl (module := Mathlib.Tactic.CategoryTheory.Coherence.PureCoherence)
Mathlib.Tactic.BicategoryLike.naturality
```

```CoherenceTactics.leanDecl (module := Mathlib.Tactic.CategoryTheory.Coherence.PureCoherence)
Mathlib.Tactic.BicategoryLike.pureCoherence
```

The next two subsections explain how the monoidal and bicategorical front ends feed their goals
into this shared core.

## Monoidal Front End
%%%
tag := "coherence-implementation-monoidal"
%%%

The monoidal front end first extracts the monoidal data from the goal. It then reads the relevant
{name Lean.Expr}`Lean.Expr` terms into the syntax expected by the shared core. The declarations
that do this are
{name Mathlib.Tactic.Monoidal.mkContext?}`mkContext?`,
{name Mathlib.Tactic.Monoidal.mor₁OfExpr}`mor₁OfExpr`,
{name Mathlib.Tactic.Monoidal.Mor₂IsoOfExpr}`Mor₂IsoOfExpr`, and
{name Mathlib.Tactic.Monoidal.Mor₂OfExpr}`Mor₂OfExpr`.

```CoherenceTactics.leanDecl (module := Mathlib.Tactic.CategoryTheory.Monoidal.Datatypes)
Mathlib.Tactic.Monoidal.mkContext?
Mathlib.Tactic.Monoidal.mor₁OfExpr
Mathlib.Tactic.Monoidal.Mor₂IsoOfExpr
Mathlib.Tactic.Monoidal.Mor₂OfExpr
```

In particular, {name Mathlib.Tactic.Monoidal.mor₁OfExpr}`mor₁OfExpr`
turns tensor expressions for objects into the 1-morphism language used by the shared core, while
{name Mathlib.Tactic.Monoidal.Mor₂IsoOfExpr}`Mor₂IsoOfExpr`
and
{name Mathlib.Tactic.Monoidal.Mor₂OfExpr}`Mor₂OfExpr`
recognize the corresponding coherence isomorphisms and morphisms over those object expressions. Once
this front end has done its work,
{name Mathlib.Tactic.Monoidal.pureCoherence}`monoidal_coherence`
just calls the shared core with the monoidal context.

## Bicategorical Front End
%%%
tag := "coherence-implementation-bicategory"
%%%

The bicategorical front end plays the same role for bicategories. It extracts the bicategory from the goal and reads the relevant
{name Lean.Expr}`Lean.Expr` terms directly into the syntax expected by the shared core. The relevant
declarations are
{name Mathlib.Tactic.Bicategory.mkContext?}`mkContext?`,
{name Mathlib.Tactic.Bicategory.mor₁OfExpr}`mor₁OfExpr`,
{name Mathlib.Tactic.Bicategory.Mor₂IsoOfExpr}`Mor₂IsoOfExpr`, and
{name Mathlib.Tactic.Bicategory.Mor₂OfExpr}`Mor₂OfExpr`.

```CoherenceTactics.leanDecl (module := Mathlib.Tactic.CategoryTheory.Bicategory.Datatypes)
Mathlib.Tactic.Bicategory.mkContext?
Mathlib.Tactic.Bicategory.mor₁OfExpr
Mathlib.Tactic.Bicategory.Mor₂IsoOfExpr
Mathlib.Tactic.Bicategory.Mor₂OfExpr
```

Once this front end has done its work,
{name Mathlib.Tactic.Bicategory.pureCoherence}`bicategory_coherence`
just calls the shared core with the bicategorical context.
