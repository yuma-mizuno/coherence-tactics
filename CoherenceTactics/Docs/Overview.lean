import CoherenceTactics.Docs.Support

open Verso Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option verso.exampleProject "."
set_option verso.exampleModule "CoherenceTactics.Examples"
set_option pp.rawOnError true


#doc (Manual) "Overview" =>
%%%
file := "Overview"
tag := "overview"
%%%

The tactic
{name Mathlib.Tactic.Monoidal.monoidal}`monoidal`
solves equalities of morphisms in monoidal categories,
and
the tactic
{name Mathlib.Tactic.Bicategory.bicategory}`bicategory`
solves equalities of 2-morphisms in bicategories.
These tactics solve goals when the two sides differ only by associators and unitors. The
mathematical background is the coherence theorem: internally, the general coherence equalities
needed to solve such goals are generated from the pentagon and triangle identities.

In practice, these tactics are often used to close individual steps inside a {name Lean.calcTactic}`calc` proof. Write the sequence of
mathematically meaningful rewrites as the lines of the {name Lean.calcTactic}`calc`. To use {name Lean.Parser.Tactic.rwSeq}`rw`, one often has to
place parentheses appropriately so that the rewriting lemma at hand applies, such as
{name CategoryTheory.Bicategory.whisker_exchange}`whisker_exchange`, a naturality lemma, or an
application-specific identity. This creates
intermediate goals where the two sides
differ only by associators and unitors. At those points, apply
{name Mathlib.Tactic.Monoidal.monoidal}`monoidal`
or
{name Mathlib.Tactic.Bicategory.bicategory}`bicategory`
to close the step.

A typical example is the construction showing that an equivalence datum, not yet known to satisfy
the triangle identities, can be upgraded to an adjoint equivalence by replacing the counit.
The proof below is the left triangle identity for the upgraded counit:

```CoherenceTactics.leanDecl (module := CoherenceTactics.Examples)
CategoryTheory.Bicategory.Demo.adjointifyCounit_hom
CategoryTheory.Bicategory.Demo.adjointifyCounit_left_triangle
```

The visible rewrites are the two uses of
{name CategoryTheory.Bicategory.whisker_exchange}`whisker_exchange`
and the cancellations of `η.inv ≫ η.hom` and `ε.inv ≫ ε.hom`. After each such step,
{name Mathlib.Tactic.Bicategory.bicategory}`bicategory`
solves the remaining equality, where the only difference is in associators and unitors.

The proof above can be visualized with the string diagram widget
{name Mathlib.Tactic.Widget.StringDiagram}`Mathlib.Tactic.Widget.StringDiagram`
as a sequence of string diagrams. Verso does not display the widget directly yet, so instead the
diagrams are shown below without mouseover Lean information:

Step 1.

```CoherenceTactics.stringDiagram
CategoryTheory.Bicategory.Demo.adjointifyCounit_left_triangle_step₁
```

Step 2.

```CoherenceTactics.stringDiagram
CategoryTheory.Bicategory.Demo.adjointifyCounit_left_triangle_step₂
```

Step 3.

```CoherenceTactics.stringDiagram
CategoryTheory.Bicategory.Demo.adjointifyCounit_left_triangle_step₃
```

Step 4.

```CoherenceTactics.stringDiagram
CategoryTheory.Bicategory.Demo.adjointifyCounit_left_triangle_step₄
```

Step 5.

```CoherenceTactics.stringDiagram
CategoryTheory.Bicategory.Demo.adjointifyCounit_left_triangle_step₅
```
