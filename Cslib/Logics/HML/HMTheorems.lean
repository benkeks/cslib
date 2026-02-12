
module

public import Cslib.Logics.HML.Basic
public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Cslib.Foundations.Semantics.LTS.TraceEq
public import Cslib.Foundations.Semantics.LTS.Simulation

@[expose] public section

namespace Cslib.Logic.HML

open Proposition LTS TraceEq Simulation Bisimulation

inductive Proposition.linear {Label} : Proposition Label → Prop where
  | true : linear .true
  | diamond {μ φ} : linear φ → linear (.diamond μ φ)

lemma linear_closed (μ : Label) (φ : Proposition Label) (h : linear (.diamond μ φ))
  : (linear φ) := by grind [linear]

def trace_to_hml {Label} (tr : List Label) : Proposition Label :=
  tr.foldr (fun μ acc => .diamond μ acc) .true

lemma trace_to_hml_satisfies {State Label} (lts : LTS State Label) (tr : List Label) (s : State)
  (htr : tr ∈ lts.traces s) :
    Satisfies lts s (trace_to_hml tr) := by
  induction tr generalizing s with grind [traces, trace_to_hml]

lemma trace_to_hml_linear {Label} (tr : List Label) :
    linear (trace_to_hml tr) := by
  induction tr with grind [trace_to_hml, linear]

def hml_to_trace {Label} (φ : Proposition Label) (lin : linear φ) : List Label :=
  match φ with
  | .true => []
  | .diamond μ φ' => μ :: hml_to_trace φ' (linear_closed μ φ' lin)

lemma hml_sat_to_trace {State Label} (lts : LTS State Label) (φ : Proposition Label) (s : State)
  (hsat : Satisfies lts s φ) (hlin : linear φ) :
  hml_to_trace φ hlin ∈ lts.traces s := by
  induction φ generalizing s with
  | true =>
    grind [LTS.empty_trace_trivial, hml_to_trace]
  | diamond μ φ ih =>
    have step : ∃ s' , lts.Tr s μ s' ∧
      hml_to_trace φ (linear_closed μ φ hlin) ∈ lts.traces s' := by grind
    obtain ⟨s', htr, htraces⟩ := step
    have : μ :: hml_to_trace φ (linear_closed μ φ hlin) ∈ lts.traces s := by
      obtain ⟨s'', htr'⟩ := htraces
      exists s''
      exact (MTr.stepL htr htr')
    grind [traces, hml_to_trace, linear_closed]
  | _ => grind [linear]

lemma trace_to_hml_inv (φ : Proposition Label) (lin : linear φ) :
    trace_to_hml (hml_to_trace φ lin) = φ := by
  induction φ with
  | true => rfl
  | diamond μ φ ih => grind [hml_to_trace, trace_to_hml]
  | _ => cases lin

lemma hml_to_trace_inv (tr : List Label) :
    (hml_to_trace (trace_to_hml tr) (trace_to_hml_linear tr)) = tr := by
  induction tr with
  | nil => rfl
  | cons μ tr ih => grind [hml_to_trace, trace_to_hml]

theorem linear_hml_eq_traceEq {State Label} (lts : LTS State Label) :
  TraceEq lts = (fun s1 s2 => ∀ φ, linear φ → (Satisfies lts s1 φ ↔ Satisfies lts s2 φ)) := by
  ext s1 s2
  constructor
  · intros traceEq φ lin
    have teq : lts.traces s1 = lts.traces s2 := traceEq
    constructor <;> intro hsat
    · have htrace1 : hml_to_trace φ lin ∈ lts.traces s1 :=
        hml_sat_to_trace lts φ s1 hsat lin
      grind [trace_to_hml_satisfies, trace_to_hml_inv]
    · have htrace2 : hml_to_trace φ lin ∈ lts.traces s2 :=
        hml_sat_to_trace lts φ s2 hsat lin
      grind [trace_to_hml_satisfies, trace_to_hml_inv]
  · intros logEq
    apply Set.ext
    intro tr
    constructor
    · intro htr
      have traceSat1 := trace_to_hml_satisfies lts tr s1 htr
      grind [hml_sat_to_trace, hml_to_trace_inv]
    · intro htr
      have traceSat2 := trace_to_hml_satisfies lts tr s2 htr
      grind [hml_sat_to_trace, hml_to_trace_inv]

inductive Proposition.positive {Label} : Proposition Label → Prop where
  | true : positive .true
  | and {φ₁ φ₂} : positive φ₁ → positive φ₂ → positive (.and φ₁ φ₂)
  | diamond {μ φ} : positive φ → positive (.diamond μ φ)

/-- Theory equivalence is a simulation. -/
@[scoped grind ⇒]
theorem theoryEq_isSimulation (lts : LTS State Label)
    [image_finite : ∀ s μ, Finite (lts.image s μ)] :
    Simulation lts (TheoryEq lts) := by
  intro s1 s2 h μ
  let (s : State) := @Fintype.ofFinite (lts.image s μ) (image_finite s μ)
  intros s1' htr
  by_contra
  have hdist : ∀ s2' : lts.image s2 μ, ∃ a, Satisfies lts s1' a ∧ ¬Satisfies lts s2'.val a := by
    intro ⟨s2', hs2'⟩
    apply not_theoryEq_satisfies
    grind
  choose dist_formula hdist_spec using hdist
  let conjunction := Proposition.finiteAnd (propositions dist_formula)
  have hs1_diamond : Satisfies lts s1 (.diamond μ conjunction) := by
    grind [propositions_satisfies_conjunction]
  cases (theoryEq_satisfies h hs1_diamond) with | @diamond _ s2'' _ _ htr2 hsat =>
  grind [propositions_complete dist_formula ⟨s2'', htr2⟩]

/-- If two states are bisimilar and the former satisfies a proposition, the latter does as
well. -/
@[scoped grind ⇒]
lemma bisimilarity_satisfies {lts : LTS State Label}
    (hr : s1 ~[lts] s2) (a : Proposition Label) (hs : Satisfies lts s1 a) :
    Satisfies lts s2 a := by
  induction a generalizing s1 s2 with
  | diamond μ a ih =>
    cases hs with
    | diamond htr _ => grind [Bisimilarity.is_bisimulation]
  | _ => grind [Bisimilarity.symm]

lemma bisimilarity_TheoryEq {lts : LTS State Label}
    (hr : s1 ~[lts] s2) :
    TheoryEq lts s1 s2 := by
  have : s2 ~[lts] s1 := by grind [Bisimilarity.symm]
  grind

/-- Theory equivalence and bisimilarity coincide for image-finite LTSs. -/
theorem theoryEq_eq_bisimilarity (lts : LTS State Label)
    [image_finite : ∀ s μ, Finite (lts.image s μ)] :
    TheoryEq lts = Bisimilarity lts := by
  ext s1 s2
  apply Iff.intro <;> intro h
  · rw [Bisimilarity.symm_simulation]
    exact ⟨TheoryEq lts, h, Std.Symm.mk (fun _ _ => TheoryEq.is_symm), theoryEq_isSimulation lts⟩
  · exact bisimilarity_TheoryEq h

end Cslib.Logic.HML
