/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Marco Peressotti, Alexandre Rademaker
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic

@[expose] public section

/-! # Hennessy-Milner Logic (HML)

Hennessy-Milner Logic (HML) is a logic for reasoning about the behaviour of nondeterministic and
concurrent systems.

## Implementation notes
There are two main versions of HML. The original [Hennessy1985], which includes a negation
connective, and a variation without negation, for example as in [Aceto1999].
We follow the latter, which is used in many recent papers. Negation is recovered as usual, by having
a `false` atomic proposition and a function that, given any proposition, returns its negated form
(see `Proposition.neg`).

## Main definitions

- `Proposition`: the language of propositions.
- `Satisfies lts s a`: in the LTS `lts`, the state `s` satisfies the proposition `a`.
- `denotation a`: the denotation of a proposition `a`, defined as the set of states that
satisfy `a`.
- `theory lts s`: the set of all propositions satisfied by state `s` in the LTS `lts`.

## Main statements

- `satisfies_mem_denotation`: the denotational semantics of HML is correct, in the sense that it
coincides with the notion of satisfiability.
- `not_theoryEq_satisfies`: if two states have different theories, then there exists a
distinguishing proposition that one state satisfies and the other does not.
- `theoryEq_eq_bisimilarity`: two states have the same theory iff they are bisimilar
(see `Bisimilarity`).

## References

* [M. Hennessy, R. Milner, *Algebraic Laws for Nondeterminism and Concurrency*][Hennessy1985]
* [L. Aceto, A. Ingólfsdóttir, *Testing Hennessy-Milner Logic with Recursion*][Aceto1999]

-/

namespace Cslib.Logic.HML

/-- Propositions. -/
inductive Proposition (Label : Type u) : Type u where
  | false
  | imp (φ₁ φ₂ : Proposition Label)
  | diamond (μ : Label) (φ : Proposition Label)

@[simp, scoped grind =]
abbrev Proposition.neg (φ : Proposition Label) : Proposition Label :=
  imp φ .false
@[simp, scoped grind =]
abbrev Proposition.true : Proposition Label :=
  neg .false
@[simp, scoped grind =]
abbrev Proposition.or (φ₁ φ₂ : Proposition Label) : Proposition Label :=
  (imp (neg φ₁) φ₂)
@[simp, scoped grind =]
abbrev Proposition.and (φ₁ φ₂ : Proposition Label) : Proposition Label :=
  neg (or (neg φ₁) (neg φ₂))
@[simp, scoped grind =]
abbrev Proposition.box (μ : Label) (φ : Proposition Label) : Proposition Label :=
  neg (diamond μ (neg φ))

/-- Finite conjunction of propositions. -/
@[simp, scoped grind =]
def Proposition.finiteAnd (as : List (Proposition Label)) : Proposition Label :=
  List.foldr .and .true as

/-- Finite disjunction of propositions. -/
@[simp, scoped grind =]
def Proposition.finiteOr (as : List (Proposition Label)) : Proposition Label :=
  List.foldr .or .false as

mutual
  /-- Satisfaction relation. `Satisfies lts s a` means that, in the LTS `lts`,
    the state `s` satisfies the proposition `a`. -/
  @[scoped grind]
  inductive Satisfies (lts : LTS State Label) : State → Proposition Label → Prop where
    | imp_triv {s : State} {a b : Proposition Label} :
      Unsatisfies lts s a →
      Satisfies lts s (.imp a b)
    | imp_true {s : State} {a b : Proposition Label} :
      Satisfies lts s b →
      Satisfies lts s (.imp a b)
    | diamond {s s' : State} {μ : Label} {a : Proposition Label}
      (htr : lts.Tr s μ s') (hs : Satisfies lts s' a) : Satisfies lts s (.diamond μ a)

  inductive Unsatisfies (lts : LTS State Label) : State → Proposition Label → Prop where
    | false {s : State} : Unsatisfies lts s .false
    | imp_false {s : State} {a b : Proposition Label} :
      Satisfies lts s a → Unsatisfies lts s b →
      Unsatisfies lts s (.imp a b)
    | diamond {s : State} {μ : Label} {a : Proposition Label}
      (htr : ∀ s', lts.Tr s μ s' → Unsatisfies lts s' a) :
      Unsatisfies lts s (.diamond μ a)
end

@[simp, scoped grind =]
theorem unsatisfies_diamond_iff {lts : LTS State Label} {s : State} {μ : Label}
    {a : Proposition Label} :
    Unsatisfies lts s (.diamond μ a) ↔
      ∀ s', ¬ lts.Tr s μ s' ∨ Unsatisfies lts s' a := by
  constructor
  · intro h s'
    cases h with
    | diamond htr =>
      by_cases htr' : lts.Tr s μ s'
      · exact Or.inr (htr s' htr')
      · exact Or.inl htr'
  · intro h
    apply Unsatisfies.diamond
    intro s' htr
    cases h s' with
    | inl hntr => exact False.elim (hntr htr)
    | inr hsat => exact hsat

example : Satisfies lts s (.box a .true) := by
  repeat constructor
  intros
  repeat constructor

mutual
  theorem satisfies_not_unsatisfies {lts : LTS State Label} {s : State} {a : Proposition Label} :
      Satisfies lts s a → ¬ Unsatisfies lts s a := by
    intro hs hu
    cases hs with
    | imp_triv hua =>
      cases hu with
      | imp_false hsa _ =>
        exact unsatisfies_not_satisfies hua hsa
    | imp_true hsb =>
      cases hu with
      | imp_false _ hub =>
        exact satisfies_not_unsatisfies hsb hub
    | diamond htr hs' =>
      cases hu with
      | diamond hall =>
        exact satisfies_not_unsatisfies hs' (hall _ htr)

  theorem unsatisfies_not_satisfies {lts : LTS State Label} {s : State} {a : Proposition Label} :
      Unsatisfies lts s a → ¬ Satisfies lts s a := by
    intro hu hs
    cases hu with
    | false =>
      cases hs
    | imp_false hsa hub =>
      cases hs with
      | imp_triv hua =>
        exact satisfies_not_unsatisfies hsa hua
      | imp_true hsb =>
        exact unsatisfies_not_satisfies hub hsb
    | diamond hall =>
      cases hs with
      | diamond htr hs' =>
        exact unsatisfies_not_satisfies (hall _ htr) hs'
end

theorem satisfies_or_unsatisfies {lts : LTS State Label} (s : State) (a : Proposition Label) :
    Satisfies lts s a ∨ Unsatisfies lts s a := by
  classical
  induction a generalizing s with
  | false =>
    exact Or.inr Unsatisfies.false
  | imp a b iha ihb =>
    cases iha s with
    | inl hsa =>
      cases ihb s with
      | inl hsb => exact Or.inl (Satisfies.imp_true hsb)
      | inr hub => exact Or.inr (Unsatisfies.imp_false hsa hub)
    | inr hua =>
      exact Or.inl (Satisfies.imp_triv hua)
  | diamond μ a iha =>
    by_cases hex : ∃ s', lts.Tr s μ s' ∧ Satisfies lts s' a
    · rcases hex with ⟨s', htr, hs'⟩
      exact Or.inl (Satisfies.diamond htr hs')
    · refine Or.inr ?_
      apply Unsatisfies.diamond
      intro s' htr
      cases iha s' with
      | inl hs' =>
        exact False.elim (hex ⟨s', htr, hs'⟩)
      | inr hu' =>
        exact hu'

@[simp, scoped grind =]
theorem not_satisfies_iff_unsatisfies {lts : LTS State Label} {s : State} {a : Proposition Label} :
    ¬ Satisfies lts s a ↔ Unsatisfies lts s a := by
  constructor
  · intro h
    cases satisfies_or_unsatisfies (lts := lts) s a with
    | inl hs => exact False.elim (h hs)
    | inr hu => exact hu
  · intro hu
    exact unsatisfies_not_satisfies hu

/-- A state satisfies a proposition iff it does not satisfy the negation of the proposition. -/
@[simp, scoped grind =]
theorem neg_satisfies {lts : LTS State Label} :
    ¬Satisfies lts s a.neg ↔ Satisfies lts s a := by
  rw [Proposition.neg, not_satisfies_iff_unsatisfies]
  constructor
  · intro h
    cases h with
    | imp_false hs _ => exact hs
  · intro hs
    exact Unsatisfies.imp_false hs Unsatisfies.false

/-- Denotation of a proposition. -/
@[simp, scoped grind =]
def Proposition.denotation (a : Proposition Label) (lts : LTS State Label)
    : Set State :=
  match a with
  | .false => ∅
  | .imp a b => {s | s ∉ a.denotation lts ∨ s ∈ b.denotation lts}
  | .diamond μ a => {s | ∃ s', lts.Tr s μ s' ∧ s' ∈ a.denotation lts}

/-- The theory of a state is the set of all propositions that it satifies. -/
abbrev theory (lts : LTS State Label) (s : State) : Set (Proposition Label) :=
  {a | Satisfies lts s a}

/-- Two states are theory-equivalent (for a specific LTS) if they have the same theory. -/
abbrev TheoryEq (lts : LTS State Label) (s1 s2 : State) :=
  theory lts s1 = theory lts s2

theorem TheoryEq.is_symm {s1 s2 : State}
  (h : TheoryEq lts s1 s2) : TheoryEq lts s2 s1 :=
  by grind

open Proposition LTS

/-- Characterisation theorem for the denotational semantics. -/
@[scoped grind =]
theorem satisfies_mem_denotation {lts : LTS State Label} :
    Satisfies lts s a ↔ s ∈ a.denotation lts := by
  induction a generalizing s with
  | false =>
    constructor
    · intro hs
      cases hs
    · intro hs
      simp at hs
  | imp a b iha ihb =>
    constructor
    · intro hs
      cases hs with
      | imp_triv hua =>
        left
        intro hmem
        exact unsatisfies_not_satisfies hua ((iha).2 hmem)
      | imp_true hsb =>
        right
        exact (ihb).1 hsb
    · intro hmem
      cases hmem with
      | inl hna =>
        apply Satisfies.imp_triv
        apply (not_satisfies_iff_unsatisfies (lts := lts) (s := s) (a := a)).1
        intro hs
        exact hna ((iha).1 hs)
      | inr hmb =>
        exact Satisfies.imp_true ((ihb).2 hmb)
  | diamond μ a iha =>
    constructor
    · intro hs
      cases hs with
      | diamond htr hs' =>
        exact ⟨_, htr, (iha).1 hs'⟩
    · intro h
      rcases h with ⟨s', htr, hs'⟩
      exact Satisfies.diamond htr ((iha).2 hs')

@[simp]
theorem not_satisfies_false {lts : LTS State Label} :
    ¬ Satisfies lts s (.false : Proposition Label) := by
  intro hs
  cases hs

@[simp]
theorem satisfies_true {lts : LTS State Label} :
    Satisfies lts s (.true : Proposition Label) := by
  exact Satisfies.imp_triv Unsatisfies.false

/-- A state is in the denotation of a proposition iff it is not in the denotation of the negation
of the proposition. -/
@[scoped grind =]
theorem neg_denotation {lts : LTS State Label} (a : Proposition Label) :
    s ∉ a.neg.denotation lts ↔ s ∈ a.denotation lts := by
  grind [_=_ satisfies_mem_denotation]

@[simp, scoped grind =]
theorem satisfies_or_iff {lts : LTS State Label} :
    Satisfies lts s (a.or b) ↔ Satisfies lts s a ∨ Satisfies lts s b := by
  rw [satisfies_mem_denotation, satisfies_mem_denotation, satisfies_mem_denotation]
  simp [Proposition.denotation]

@[simp, scoped grind =]
theorem satisfies_and_iff {lts : LTS State Label} :
    Satisfies lts s (a.and b) ↔ Satisfies lts s a ∧ Satisfies lts s b := by
  rw [satisfies_mem_denotation, satisfies_mem_denotation, satisfies_mem_denotation]
  simp [Proposition.denotation]

/-- A state satisfies a finite conjunction iff it satisfies all conjuncts. -/
@[scoped grind =]
theorem satisfies_finiteAnd {lts : LTS State Label} {s : State}
    {as : List (Proposition Label)} :
    Satisfies lts s (Proposition.finiteAnd as) ↔ ∀ a ∈ as, Satisfies lts s a := by
  induction as with
  | nil =>
    simp [Proposition.finiteAnd]
  | cons head tail ih =>
    change Satisfies lts s (head.and (Proposition.finiteAnd tail)) ↔
      ∀ a ∈ head :: tail, Satisfies lts s a
    constructor
    · intro hs a ha
      have hand := (satisfies_and_iff (lts := lts) (s := s)
        (a := head) (b := Proposition.finiteAnd tail)).1 hs
      rcases List.mem_cons.mp ha with rfl | htail
      · exact hand.1
      · exact (ih.1 hand.2) a htail
    · intro h
      apply (satisfies_and_iff (lts := lts) (s := s)
        (a := head) (b := Proposition.finiteAnd tail)).2
      refine ⟨h head (by simp), ?_⟩
      apply ih.2
      intro a ha
      exact h a (List.mem_cons_of_mem _ ha)

/-- A state satisfies a finite disjunction iff it satisfies some disjunct. -/
@[scoped grind =]
theorem satisfies_finiteOr {lts : LTS State Label} {s : State}
    {as : List (Proposition Label)} :
    Satisfies lts s (Proposition.finiteOr as) ↔ ∃ a ∈ as, Satisfies lts s a := by
  induction as with
  | nil =>
    simp [Proposition.finiteOr]
  | cons head tail ih =>
    change Satisfies lts s (head.or (Proposition.finiteOr tail)) ↔
      ∃ a ∈ head :: tail, Satisfies lts s a
    constructor
    · intro hs
      have hor := (satisfies_or_iff (lts := lts) (s := s)
        (a := head) (b := Proposition.finiteOr tail)).1 hs
      cases hor with
      | inl hhead =>
        exact ⟨head, by simp, hhead⟩
      | inr htail =>
        rcases ih.1 htail with ⟨a, ha, hsa⟩
        exact ⟨a, List.mem_cons_of_mem _ ha, hsa⟩
    · intro h
      rcases h with ⟨a, ha, hsa⟩
      rcases List.mem_cons.mp ha with rfl | htail
      · exact (satisfies_or_iff (lts := lts) (s := s)
          (a := a) (b := Proposition.finiteOr tail)).2 (Or.inl hsa)
      · exact (satisfies_or_iff (lts := lts) (s := s)
          (a := head) (b := Proposition.finiteOr tail)).2
          (Or.inr (ih.2 ⟨a, htail, hsa⟩))

@[scoped grind →]
theorem satisfies_theory (h : Satisfies lts s a) : a ∈ theory lts s := by
  grind

/-- Two states are theory-equivalent iff they are denotationally equivalent. -/
theorem theoryEq_denotation_eq {lts : LTS State Label} :
    TheoryEq lts s1 s2 ↔
    (∀ a : Proposition Label, s1 ∈ a.denotation lts ↔ s2 ∈ a.denotation lts) := by
  grind [_=_ satisfies_mem_denotation]

/-- If two states are not theory equivalent, there exists a distinguishing proposition. -/
lemma not_theoryEq_satisfies (h : ¬ TheoryEq lts s1 s2) :
    ∃ a, (Satisfies lts s1 a ∧ ¬Satisfies lts s2 a) := by
  grind [=_ neg_satisfies]

/-- If two states are theory equivalent and the former satisfies a proposition, the latter does as
well. -/
theorem theoryEq_satisfies {lts : LTS State Label} (h : TheoryEq lts s1 s2)
    (hs : Satisfies lts s1 a) : Satisfies lts s2 a := by
  unfold TheoryEq theory at h
  rw [Set.ext_iff] at h
  exact (h a).mp hs

section ImageToPropositions

variable {lts : LTS State Label} (stateMap : lts.image s μ → Proposition Label)
variable [finImage : Fintype (lts.image s μ)]

/-- The list of propositions over finite μ-derivatives. -/
noncomputable def propositions : List (Proposition Label) :=
  finImage.elems.toList.map stateMap

theorem propositions_complete (s' : lts.image s μ) : stateMap s' ∈ propositions stateMap := by
  apply List.mem_map.mpr
  use s', Finset.mem_toList.mpr (Fintype.complete s')

theorem propositions_satisfies_conjunction (htr : lts.Tr s1 μ s1')
  (hdist_spec : ∀ s2', Satisfies lts s1' (stateMap s2')) :
    Satisfies lts s1 (.diamond μ <| Proposition.finiteAnd (propositions stateMap)) := by
  apply Satisfies.diamond htr
  rw [satisfies_finiteAnd]
  intro a ha_mem
  grind [List.mem_map.mp ha_mem]

end ImageToPropositions

end Cslib.Logic.HML
