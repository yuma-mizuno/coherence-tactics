import CoherenceTactics.Docs.Overview
import CoherenceTactics.Docs.CoherenceTheorem
import CoherenceTactics.Docs.Tactics
import VersoManual

open Verso Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option verso.exampleProject "."
set_option verso.exampleModule "CoherenceTactics.Examples"
set_option pp.rawOnError true

#doc (Manual) "Coherence Tactics for Monoidal Categories and Bicategories in Lean" =>
%%%
shortTitle := "Coherence Tactics"
tag := "index"
%%%

Author: Yuma Mizuno

Source repository: [yuma-mizuno/coherence-tactics](https://github.com/yuma-mizuno/coherence-tactics)

This note explains two tactics in Lean:
{name Mathlib.Tactic.Monoidal.monoidal}`monoidal`
for equalities of morphisms in monoidal categories, and
{name Mathlib.Tactic.Bicategory.bicategory}`bicategory`
for equalities of 2-morphisms in bicategories.
These tactics are available in [Mathlib](https://leanprover-community.github.io/mathlib4_docs/).


{include 0 CoherenceTactics.Docs.Overview}

{include 0 CoherenceTactics.Docs.CoherenceTheorem}

{include 0 CoherenceTactics.Docs.Tactics}
