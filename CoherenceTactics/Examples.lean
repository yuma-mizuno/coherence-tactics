import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
import Mathlib.Tactic.Widget.StringDiagram

open CategoryTheory Mathlib.Tactic

section

open MonoidalCategory

open scoped MonoidalCategory

namespace CoherenceTactics.Examples

-- ANCHOR: monoidalCoherencePure
example {C : Type*} [Category C] [MonoidalCategory C] :
    (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom := by
  monoidal_coherence
-- ANCHOR_END: monoidalCoherencePure

abbrev tensorμ {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    (X₁ X₂ Y₁ Y₂ : C) :
    (X₁ ⊗ X₂) ⊗ Y₁ ⊗ Y₂ ⟶ (X₁ ⊗ Y₁) ⊗ X₂ ⊗ Y₂ :=
  (α_ X₁ X₂ (Y₁ ⊗ Y₂)).hom ≫
    (X₁ ◁ (α_ X₂ Y₁ Y₂).inv) ≫
      (X₁ ◁ (β_ X₂ Y₁).hom ▷ Y₂) ≫
        (X₁ ◁ (α_ Y₁ X₂ Y₂).hom) ≫
          (α_ X₁ Y₁ (X₂ ⊗ Y₂)).inv

-- ANCHOR: monoidalCalc
theorem monoidal_calc {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    (X₁ X₂ X₃ Y₁ Y₂ Y₃ : C) :
    tensorμ (X₁ ⊗ X₂) X₃ (Y₁ ⊗ Y₂) Y₃ ≫
        (tensorμ X₁ X₂ Y₁ Y₂ ▷ (X₃ ⊗ Y₃)) ≫ (α_ (X₁ ⊗ Y₁) (X₂ ⊗ Y₂) (X₃ ⊗ Y₃)).hom =
      ((α_ X₁ X₂ X₃).hom ⊗ₘ (α_ Y₁ Y₂ Y₃).hom) ≫
        tensorμ X₁ (X₂ ⊗ X₃) Y₁ (Y₂ ⊗ Y₃) ≫ ((X₁ ⊗ Y₁) ◁ tensorμ X₂ X₃ Y₂ Y₃) := by
  dsimp only [tensorμ]
  with_panel_widgets [Mathlib.Tactic.Widget.StringDiagram]
  calc
    _ = 𝟙 _ ⊗≫ X₁ ◁ X₂ ◁ (β_ X₃ Y₁).hom ▷ Y₂ ▷ Y₃ ⊗≫
      X₁ ◁ ((X₂ ⊗ Y₁) ◁ (β_ X₃ Y₂).hom ≫
        (β_ X₂ Y₁).hom ▷ (Y₂ ⊗ X₃)) ▷ Y₃ ⊗≫ 𝟙 _ := by
          rw [BraidedCategory.braiding_tensor_right_hom]
          monoidal
    _ = 𝟙 _ ⊗≫ X₁ ◁ (((α_ X₂ X₃ Y₁).hom ≫ X₂ ◁ (β_ X₃ Y₁).hom ≫ (α_ X₂ Y₁ X₃).inv ≫
        (β_ X₂ Y₁).hom ▷ X₃ ≫ (α_ Y₁ X₂ X₃).hom)) ▷ Y₂ ▷ Y₃ ⊗≫
          X₁ ◁ Y₁ ◁ X₂ ◁ (β_ X₃ Y₂).hom ▷ Y₃ ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]
      monoidal
    _ = _ := by
      rw [← BraidedCategory.braiding_tensor_left_hom]
      monoidal
-- ANCHOR_END: monoidalCalc

theorem monoidal_calc_step₁ {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    (X₁ X₂ X₃ Y₁ Y₂ Y₃ : C) :
    tensorμ (X₁ ⊗ X₂) X₃ (Y₁ ⊗ Y₂) Y₃ ≫
        (tensorμ X₁ X₂ Y₁ Y₂ ▷ (X₃ ⊗ Y₃)) ≫ (α_ (X₁ ⊗ Y₁) (X₂ ⊗ Y₂) (X₃ ⊗ Y₃)).hom =
      𝟙 _ ⊗≫ X₁ ◁ X₂ ◁ (β_ X₃ Y₁).hom ▷ Y₂ ▷ Y₃ ⊗≫
        X₁ ◁ ((X₂ ⊗ Y₁) ◁ (β_ X₃ Y₂).hom ≫
          (β_ X₂ Y₁).hom ▷ (Y₂ ⊗ X₃)) ▷ Y₃ ⊗≫ 𝟙 _ := by
  dsimp only [tensorμ]
  rw [BraidedCategory.braiding_tensor_right_hom]
  monoidal

theorem monoidal_calc_step₂ {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    (X₁ X₂ X₃ Y₁ Y₂ Y₃ : C) :
    𝟙 (((X₁ ⊗ X₂) ⊗ X₃) ⊗ (Y₁ ⊗ Y₂) ⊗ Y₃) ⊗≫ X₁ ◁ X₂ ◁ (β_ X₃ Y₁).hom ▷ Y₂ ▷ Y₃ ⊗≫
        X₁ ◁ ((X₂ ⊗ Y₁) ◁ (β_ X₃ Y₂).hom ≫
          (β_ X₂ Y₁).hom ▷ (Y₂ ⊗ X₃)) ▷ Y₃ ⊗≫ 𝟙 _ =
      𝟙 _ ⊗≫ X₁ ◁ X₂ ◁ (β_ X₃ Y₁).hom ▷ Y₂ ▷ Y₃ ⊗≫
      X₁ ◁ (β_ X₂ Y₁).hom ▷ X₃ ▷ Y₂ ▷ Y₃ ⊗≫ X₁ ◁ Y₁ ◁ X₂ ◁ (β_ X₃ Y₂).hom ▷ Y₃ ⊗≫
        𝟙 ((X₁ ⊗ Y₁) ⊗ (X₂ ⊗ Y₂) ⊗ X₃ ⊗ Y₃) := by
  rw [whisker_exchange]
  monoidal

theorem monoidal_calc_step₃ {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    (X₁ X₂ X₃ Y₁ Y₂ Y₃ : C) :
    𝟙 _ ⊗≫ X₁ ◁ (((α_ X₂ X₃ Y₁).hom ≫ X₂ ◁ (β_ X₃ Y₁).hom ≫ (α_ X₂ Y₁ X₃).inv ≫
        (β_ X₂ Y₁).hom ▷ X₃ ≫ (α_ Y₁ X₂ X₃).hom)) ▷ Y₂ ▷ Y₃ ⊗≫
          X₁ ◁ Y₁ ◁ X₂ ◁ (β_ X₃ Y₂).hom ▷ Y₃ ⊗≫ 𝟙 _ =
      ((α_ X₁ X₂ X₃).hom ⊗ₘ (α_ Y₁ Y₂ Y₃).hom) ≫
        tensorμ X₁ (X₂ ⊗ X₃) Y₁ (Y₂ ⊗ Y₃) ≫ ((X₁ ⊗ Y₁) ◁ tensorμ X₂ X₃ Y₂ Y₃) := by
  rw [← BraidedCategory.braiding_tensor_left_hom]
  monoidal

end CoherenceTactics.Examples

end

namespace CategoryTheory.Bicategory

namespace Demo

open Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]

open scoped Bicategory

variable {a b : B} {f : a ⟶ b} {g : b ⟶ a}

abbrev adjointifyCounit_hom (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :
    g ≫ f ⟶ 𝟙 b :=
  g ◁ ((ρ_ f).inv ≫ rightZigzag ε.inv η.inv ≫ (λ_ f).hom) ≫ ε.hom

theorem adjointifyCounit_left_triangle (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :
    leftZigzag η.hom (adjointifyCounit_hom η ε) = (λ_ f).hom ≫ (ρ_ f).inv := by
  with_panel_widgets [Mathlib.Tactic.Widget.StringDiagram]
  calc
    _ = 𝟙 (𝟙 a ≫ f) ⊗≫ (η.hom ▷ (f ≫ 𝟙 b) ≫ (f ≫ g) ◁ f ◁ ε.inv) ⊗≫
          f ◁ g ◁ η.inv ▷ f ⊗≫ f ◁ ε.hom := by
      bicategory
    _ = 𝟙 (𝟙 a ≫ f) ⊗≫ f ◁ ε.inv ⊗≫
          (η.hom ▷ (f ≫ g) ≫ (f ≫ g) ◁ η.inv) ▷ f ⊗≫ f ◁ ε.hom := by
      rw [← whisker_exchange η.hom (f ◁ ε.inv)]
      bicategory
    _ = 𝟙 (𝟙 a ≫ f) ⊗≫ f ◁ ε.inv ⊗≫ (η.inv ≫ η.hom) ▷ f ⊗≫ f ◁ ε.hom := by
      rw [← whisker_exchange η.hom η.inv]
      bicategory
    _ = 𝟙 (𝟙 a ≫ f) ⊗≫ f ◁ (ε.inv ≫ ε.hom) := by
      rw [Iso.inv_hom_id]
      bicategory
    _ = _ := by
      rw [Iso.inv_hom_id]
      bicategory

theorem adjointifyCounit_left_triangle_step₁ (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :
    η.hom ▷ f ⊗≫ f ◁ adjointifyCounit_hom η ε =
      𝟙 (𝟙 a ≫ f) ⊗≫ (η.hom ▷ (f ≫ 𝟙 b) ≫ (f ≫ g) ◁ f ◁ ε.inv) ⊗≫
        f ◁ g ◁ η.inv ▷ f ⊗≫ f ◁ ε.hom := by
  bicategory


theorem adjointifyCounit_left_triangle_step₂ (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :
    𝟙 (𝟙 a ≫ f) ⊗≫ (η.hom ▷ (f ≫ 𝟙 b) ≫ (f ≫ g) ◁ f ◁ ε.inv) ⊗≫
        f ◁ g ◁ η.inv ▷ f ⊗≫ f ◁ ε.hom =
      𝟙 (𝟙 a ≫ f) ⊗≫ f ◁ ε.inv ⊗≫
        (η.hom ▷ (f ≫ g) ≫ (f ≫ g) ◁ η.inv) ▷ f ⊗≫ f ◁ ε.hom := by
  rw [← whisker_exchange η.hom (f ◁ ε.inv)]
  bicategory

theorem adjointifyCounit_left_triangle_step₃ (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :
    𝟙 (𝟙 a ≫ f) ⊗≫ f ◁ ε.inv ⊗≫
        (η.hom ▷ (f ≫ g) ≫ (f ≫ g) ◁ η.inv) ▷ f ⊗≫ f ◁ ε.hom =
      𝟙 (𝟙 a ≫ f) ⊗≫ f ◁ ε.inv ⊗≫ (η.inv ≫ η.hom) ▷ f ⊗≫ f ◁ ε.hom := by
  rw [← whisker_exchange η.hom η.inv]
  bicategory

theorem adjointifyCounit_left_triangle_step₄ (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :
    𝟙 (𝟙 a ≫ f) ⊗≫ f ◁ ε.inv ⊗≫ (η.inv ≫ η.hom) ▷ f ⊗≫ f ◁ ε.hom =
      𝟙 (𝟙 a ≫ f) ⊗≫ f ◁ (ε.inv ≫ ε.hom) := by
  rw [Iso.inv_hom_id]
  bicategory

theorem adjointifyCounit_left_triangle_step₅ (_η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :
    𝟙 (𝟙 a ≫ f) ⊗≫ f ◁ (ε.inv ≫ ε.hom) = (λ_ f).hom ≫ (ρ_ f).inv := by
  rw [Iso.inv_hom_id]
  bicategory

end Demo

end CategoryTheory.Bicategory
