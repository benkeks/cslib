/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, GitHub Copilot
-/

module

public import Cslib.Init

public section

namespace Cslib

universe u v w

variable {Model : Type u} {World : Type v} {Formula : Type w}

/-- Typeclass for semantic satisfaction relations. -/
class HasSatisfaction (Model : Type u) (World : Type v) (Formula : Type w) where
  /-- `satisfies model world formula` means that `world` satisfies `formula` in `model`. -/
  satisfies : Model → World → Formula → Prop

/-- The theory of a world is the set of formulas it satisfies in a given model. -/
abbrev theory [HasSatisfaction Model World Formula] (model : Model) (world : World) : Set Formula :=
  { formula | HasSatisfaction.satisfies model world formula }

/-- Two worlds are theory-equivalent in a model if they satisfy the same formulas. -/
abbrev TheoryEq [HasSatisfaction Model World Formula] (model : Model) (w1 w2 : World) : Prop :=
  theory (Formula := Formula) model w1 = theory (Formula := Formula) model w2

/-- Theory equivalence is symmetric. -/
theorem TheoryEq.is_symm [HasSatisfaction Model World Formula] {model : Model} {w1 w2 : World}
    (h : TheoryEq (Formula := Formula) model w1 w2) :
    TheoryEq (Formula := Formula) model w2 w1 := by
  simpa [TheoryEq] using h.symm

/-- A satisfied formula belongs to the theory of the corresponding world. -/
theorem satisfies_theory [HasSatisfaction Model World Formula] {model : Model} {world : World}
    {formula : Formula} (h : HasSatisfaction.satisfies model world formula) :
    formula ∈ theory (Formula := Formula) model world := h

/-- Theory-equivalent worlds satisfy the same formulas. -/
theorem theoryEq_satisfies [HasSatisfaction Model World Formula] {model : Model}
    {w1 w2 : World} {formula : Formula} (h : TheoryEq (Formula := Formula) model w1 w2)
    (hs : HasSatisfaction.satisfies model w1 formula) :
    HasSatisfaction.satisfies model w2 formula := by
  change formula ∈ theory (Formula := Formula) model w2
  rw [← h]
  exact hs

end Cslib
