import CoherenceTactics.Docs.Support

open Verso Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option verso.exampleProject "."
set_option verso.exampleModule "CoherenceTactics.Examples"
set_option pp.rawOnError true

#doc (Manual) "Monoidal and Bicategory Tactics" =>
%%%
file := "Monoidal-and-Bicategory-Tactics"
tag := "tactics"
%%%

# `monoidal` and `bicategory`
%%%
tag := "the-tactics"
%%%

This chapter is about the user-facing tactics
{name Mathlib.Tactic.Monoidal.monoidal}`monoidal`
and
{name Mathlib.Tactic.Bicategory.bicategory}`bicategory`.
The previous chapter treated the coherence theorem and the tactics
{name Mathlib.Tactic.Monoidal.pureCoherence}`monoidal_coherence`
and
{name Mathlib.Tactic.Bicategory.pureCoherence}`bicategory_coherence`.
Here the focus is on the more common situation where a goal contains actual maps,
and coherence is only part of the proof.

## The `monoidal` Tactic
%%%
tag := "monoidal"
%%%

The tactic {name Mathlib.Tactic.Monoidal.monoidal}`monoidal` solves equalities of morphisms in a
monoidal category when the same actual morphisms (such as `f` and `g`) appear in the same order
on both sides, and only the surrounding coherence data differ.

{docstring Mathlib.Tactic.Monoidal.monoidal}

In typical use, the rewriting lemmas that change the actual morphisms are applied first.
Once those morphisms already match on both sides, {name Mathlib.Tactic.Monoidal.monoidal}`monoidal`
is used to prove that the remaining structural part
(that is, the part built only from associators and unitors)
is equal on the two sides.
The {name Lean.calcTactic}`calc` pattern below is the usual way to reach that point in a proof.

## The `bicategory` Tactic
%%%
tag := "bicategory"
%%%

The tactic {name Mathlib.Tactic.Bicategory.bicategory}`bicategory` is the bicategorical analogue
of {name Mathlib.Tactic.Monoidal.monoidal}`monoidal`.
It applies when the same actual 2-morphisms, such as `η`, `ε`, or a naturality map, appear in the
same order on both sides, and only the surrounding coherence data differ.

{docstring Mathlib.Tactic.Bicategory.bicategory}

In typical use, the rewriting lemmas that change the actual 2-morphisms are applied first.
Once those 2-morphisms already match on both sides,
{name Mathlib.Tactic.Bicategory.bicategory}`bicategory`
is used to remove the remaining coherence layer.
The bicategorical proof in the overview is the main example of this pattern.

## Working in {name Lean.calcTactic}`calc`
%%%
tag := "monoidal-workflow"
%%%

In practice, these tactics are most useful inside a {name Lean.calcTactic}`calc` block.
As in the overview, one writes the mathematically meaningful rewrites as the lines of the
{name Lean.calcTactic}`calc`, and uses the tactic only for the intermediate steps where the two
sides differ by associators and unitors. To use {name Lean.Parser.Tactic.rwSeq}`rw`, one often has to place
parentheses appropriately so that the lemma at hand applies. This creates
intermediate goals in which only the coherence data differ.

The monoidal example below shows this pattern explicitly:

```CoherenceTactics.leanDecl (module := CoherenceTactics.Examples)
CoherenceTactics.Examples.monoidal_calc
```

The visible rewrites come from the braiding lemmas and the exchange law, while
{name Mathlib.Tactic.Monoidal.monoidal}`monoidal` closes the remaining coherence step after each rewrite.

This proof can also be visualized with the string diagram widget
{name Mathlib.Tactic.Widget.StringDiagram}`Mathlib.Tactic.Widget.StringDiagram`.
As in the overview, Verso does not display the widget directly yet, so the diagrams are shown below
without mouseover Lean information:

Step 1.

```CoherenceTactics.stringDiagram
CoherenceTactics.Examples.monoidal_calc_step₁
```

Step 2.

```CoherenceTactics.stringDiagram
CoherenceTactics.Examples.monoidal_calc_step₂
```

Step 3.

```CoherenceTactics.stringDiagram
CoherenceTactics.Examples.monoidal_calc_step₃
```

## Tracing
%%%
tag := "tracing"
%%%

To inspect the normalization performed by the tactics, enable tracing with
`set_option trace.monoidal true` or `set_option trace.bicategory true`.
The trace output prints the normalization steps.

# Implementation
%%%
tag := "implementation"
%%%

The previous chapter explained
{name Mathlib.Tactic.Monoidal.pureCoherence}`monoidal_coherence`
and
{name Mathlib.Tactic.Bicategory.pureCoherence}`bicategory_coherence`,
which solve goals built only from associators and unitors.
This chapter explains what is added by
{name Mathlib.Tactic.Monoidal.monoidal}`monoidal`
and
{name Mathlib.Tactic.Bicategory.bicategory}`bicategory`
when a goal contains actual maps, not merely those constructed from associators and unitors.
The extra work is to rearrange each side until those maps can be compared directly, leaving only
coherence equalities for the previous chapter.

## Shared Core
%%%
tag := "implementation-shared"
%%%

The previous chapter explained the design of the shared core. What is added here is the
normalization of 2-morphisms.

The core recursive function is
{name Mathlib.Tactic.BicategoryLike.eval}`eval`,
which rearranges the parsed expression into a form where the actual maps can be compared one by one.
The classes
{name Mathlib.Tactic.BicategoryLike.MkEvalComp}`MkEvalComp`,
{name Mathlib.Tactic.BicategoryLike.MkEvalWhiskerLeft}`MkEvalWhiskerLeft`,
{name Mathlib.Tactic.BicategoryLike.MkEvalWhiskerRight}`MkEvalWhiskerRight`,
{name Mathlib.Tactic.BicategoryLike.MkEvalHorizontalComp}`MkEvalHorizontalComp`,
and
{name Mathlib.Tactic.BicategoryLike.MkEval}`MkEval`
support this function by supplying the equality proofs needed at each recursive step.

Normalization means
separating two kinds of data in the composite. The actual maps
stay in the same order. Associators and unitors are pushed into the coherence pieces around them.
The target shape is an alternating composite

$$`
\alpha_0 \,\mathbin{\gg}\, \eta_1 \,\mathbin{\gg}\, \alpha_1 \,\mathbin{\gg}\, \cdots
  \,\mathbin{\gg}\, \eta_n \,\mathbin{\gg}\, \alpha_n,
`

where each $`\alpha_i` is one coherence piece built only from associators and unitors.
More precisely, the source code defines each $`\eta_i` to have the form

$$`
f_1 \triangleleft \cdots \triangleleft f_n \triangleleft \theta.
`

Here $`\theta` has the form

$$`
\iota_1 \otimes \cdots \otimes \iota_\ell,
`

and each $`\iota_j` has the form

$$`
\kappa \triangleright g_1 \triangleright \cdots \triangleright g_k,
`

where $`\kappa` is one atomic 2-morphism from the original expression. In the implementation,
these three layers are represented by
{name Mathlib.Tactic.BicategoryLike.WhiskerLeft}`WhiskerLeft`,
{name Mathlib.Tactic.BicategoryLike.HorizontalComp}`HorizontalComp`,
and {name Mathlib.Tactic.BicategoryLike.WhiskerRight}`WhiskerRight`.
The datatype {name Mathlib.Tactic.BicategoryLike.NormalExpr}`NormalExpr`
then stores the full alternating expression.

```CoherenceTactics.leanDecl (module := Mathlib.Tactic.CategoryTheory.Coherence.Normalize)
Mathlib.Tactic.BicategoryLike.WhiskerRight
Mathlib.Tactic.BicategoryLike.HorizontalComp
Mathlib.Tactic.BicategoryLike.WhiskerLeft
Mathlib.Tactic.BicategoryLike.NormalExpr
```

The result type
{name Mathlib.Tactic.BicategoryLike.Eval.Result}`Eval.Result`
packages such a normalized expression together with a proof that it is equal to the original term.

```CoherenceTactics.leanDecl (module := Mathlib.Tactic.CategoryTheory.Coherence.Normalize)
Mathlib.Tactic.BicategoryLike.Eval.Result
```

The function that actually carries out this normalization is
{name Mathlib.Tactic.BicategoryLike.eval}`eval`.

```CoherenceTactics.leanDecl (module := Mathlib.Tactic.CategoryTheory.Coherence.Normalize)
Mathlib.Tactic.BicategoryLike.eval
```

The helper {name Mathlib.Tactic.BicategoryLike.evalComp}`evalComp`
combines two already-normalized expressions.

```CoherenceTactics.leanDecl (module := Mathlib.Tactic.CategoryTheory.Coherence.Normalize)
Mathlib.Tactic.BicategoryLike.evalComp
```

The helper {name Mathlib.Tactic.BicategoryLike.evalWhiskerLeft}`evalWhiskerLeft`
handles left whiskering.

```CoherenceTactics.leanDecl (module := Mathlib.Tactic.CategoryTheory.Coherence.Normalize)
Mathlib.Tactic.BicategoryLike.evalWhiskerLeft
```

The helper {name Mathlib.Tactic.BicategoryLike.evalWhiskerRight}`evalWhiskerRight`
for right whiskering and
{name Mathlib.Tactic.BicategoryLike.evalHorizontalComp}`evalHorizontalComp`
for horizontal composition are more involved.
One reason is that the normal form stores actual maps as
{name Mathlib.Tactic.BicategoryLike.WhiskerLeft}`WhiskerLeft`
terms, and the expression in the form `(f ◁ η) ▷ h` cannot be in the normal form.
These two helper functions are implemented by mutual recursion with auxiliary functions.

```CoherenceTactics.leanDecl (module := Mathlib.Tactic.CategoryTheory.Coherence.Normalize)
Mathlib.Tactic.BicategoryLike.evalWhiskerRight
```

Using {name Mathlib.Tactic.BicategoryLike.eval}`eval`, the function
{name Mathlib.Tactic.BicategoryLike.normalForm}`normalForm`
replace the original goal by the equality of the
two normalized expressions.

```CoherenceTactics.leanDecl (module := Mathlib.Tactic.CategoryTheory.Coherence.Basic)
Mathlib.Tactic.BicategoryLike.normalForm
```

Then
{name Mathlib.Tactic.BicategoryLike.ofNormalizedEq}`ofNormalizedEq`
examines an equality of normalized composites and decomposes the leading `cons` layer.
Its theorem `mk_eq_of_cons` turns
`α ≫ η ≫ ηs = α' ≫ η' ≫ ηs'`
into three new goals:
the first coherence piece, the next actual map, and the remaining tail.

```CoherenceTactics.leanDecl (module := Mathlib.Tactic.CategoryTheory.Coherence.Basic)
Mathlib.Tactic.BicategoryLike.ofNormalizedEq
```

Finally,
{name Mathlib.Tactic.BicategoryLike.main}`main`
first calls
{name Mathlib.Tactic.BicategoryLike.normalForm}`normalForm`
to replace the original goal by an equality of normalized expressions. It then repeats
{name Mathlib.Tactic.BicategoryLike.ofNormalizedEq}`ofNormalizedEq`
until no further `cons` layer remains.

At that point the remaining goals alternate between coherence pieces and actual maps. The actual-map
goals are closed by reflexivity. The remaining coherence goals are then sent to
{name Mathlib.Tactic.BicategoryLike.pureCoherence}`the pure coherence tactic` from the
previous chapter.

```CoherenceTactics.leanDecl (module := Mathlib.Tactic.CategoryTheory.Coherence.Basic)
Mathlib.Tactic.BicategoryLike.main
```

## Monoidal Front End
%%%
tag := "implementation-monoidal"
%%%

The monoidal front end is the code around the user-facing tactic

```CoherenceTactics.leanDecl (module := Mathlib.Tactic.CategoryTheory.Monoidal.Basic)
Mathlib.Tactic.Monoidal.monoidal
```

## Bicategorical Front End
%%%
tag := "implementation-bicategory"
%%%

The bicategorical front end is the code around the user-facing tactic

```CoherenceTactics.leanDecl (module := Mathlib.Tactic.CategoryTheory.Bicategory.Basic)
Mathlib.Tactic.Bicategory.bicategory
```
