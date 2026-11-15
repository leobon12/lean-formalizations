/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkUnionLaw

/-!
# GW2's union locality, part 1: increasing families of marked-local sets

Packet PROVE-GW2-RELDET (locality clause of `GW2Rd.HasGW2UnionLocality`). The explored flow line of GW2 is local only
at stopping times strictly before its lifetime `ζα`, while K2's lines ask a marked-local set at every deterministic
time `t`. The set used is `A ∪ relClosureH (⋃ₙ Kₙ)` with `A` the retained set and `Kₙ` the flow hull at `t ∧ σₙ`
(`σₙ ↑ ζα` announcing), with the marks `ℋ₀ ⊔ ⨆ₙ 𝓜ₙ` (`𝓜ₙ` the stopped σ-algebras).

For field-determined marks, the history-marked avoidance criterion is equivalent to: every marked avoidance event is
almost surely an event of `σ(h − G h)` (`WalkLaw.mem_aeSigma_of_isHistoryAvoidanceLocal`,
`WalkLaw.isHistoryAvoidanceLocal_of_mem_aeSigma`). That class of events is a σ-algebra, so countable intersections of
avoidance events and the passage to `⨆ₙ 𝓜ₙ` are free:

* `disjoint_relClosureH_iff`: for an open `U ⊆ ℍ`, `relClosureH S` avoids `U` iff `S` does;
* **`isHistoryAvoidanceLocal_union_relClosure_iUnion`**: if `A` is marked local for field-determined marks `ℋ₀`, the
  `Kₙ` are marked local for increasing field-determined marks `𝓜ₙ`, and the `Kₙ` increase almost surely, then
  `A ∪ relClosureH (⋃ₙ Kₙ)` is marked local for `ℋ₀ ⊔ ⨆ₙ 𝓜ₙ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE.Theorem14.GW2Rd

open LocalSets

/-- For an open `U ⊆ ℍ`, the relative closure of `S` in `ℍ` avoids `U` iff `S` does. -/
theorem disjoint_relClosureH_iff {S U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H) :
    Disjoint (relClosureH S) U ↔ Disjoint S U := by
  constructor
  · intro hd
    refine Set.disjoint_left.2 fun z hzS hzU => Set.disjoint_left.1 hd ⟨hUH hzU, subset_closure ⟨hzS, hUH hzU⟩⟩ hzU
  · intro hd
    refine Set.disjoint_left.2 fun z hz hzU => ?_
    have h1 : Disjoint (S ∩ H) U := hd.mono_left inter_subset_left
    have h2 : Disjoint (closure (S ∩ H)) U := (Disjoint.closure_left h1 hU)
    exact Set.disjoint_left.1 h2 hz.2 hzU

section Core

variable {Ω : Type*} {ℋ₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- **An a.s. increasing family of marked-local sets, closed up and joined to a marked-local set, is marked local for
the joined marks.** -/
theorem isHistoryAvoidanceLocal_union_relClosure_iUnion {Y : Ω → DistOn upperHalfPlaneOpens} (hYm : Measurable Y)
    {A : Ω → Set ℂ} (hAℋ : Measurable[ℋ₀, hittingSigma] A)
    (hℋ₀d : ℋ₀ ≤ aeSigma (MeasurableSpace.comap Y inferInstance) P)
    (hlocA : WholeField.IsHistoryAvoidanceLocal ℋ₀ A Y P)
    {𝓜 : ℕ → MeasurableSpace Ω} (h𝓜 : Monotone 𝓜) {K : ℕ → Ω → Set ℂ}
    (hK : ∀ n, Measurable[𝓜 n, hittingSigma] (K n))
    (h𝓜d : ∀ n, 𝓜 n ≤ aeSigma (MeasurableSpace.comap Y inferInstance) P)
    (hlocK : ∀ n, WholeField.IsHistoryAvoidanceLocal (𝓜 n) (K n) Y P)
    (hKmono : ∀ᵐ ω ∂P, Monotone fun n => K n ω) :
    WholeField.IsHistoryAvoidanceLocal (ℋ₀ ⊔ ⨆ n, 𝓜 n)
      (fun ω => A ω ∪ relClosureH (⋃ n, K n ω)) Y P := by
  refine WalkLaw.isHistoryAvoidanceLocal_of_mem_aeSigma hYm fun U G hUH hG hd => ?_
  set Av : Set Ω := {ω | Disjoint (A ω ∪ relClosureH (⋃ n, K n ω)) U} with hAvdef
  set An : ℕ → Set Ω := fun n => {ω | Disjoint (A ω ∪ K n ω) U} with hAndef
  -- the avoidance event is the intersection of the approximating avoidance events
  have hAv : Av = ⋂ n, An n := by
    ext ω
    simp only [hAvdef, hAndef, mem_ofPred_eq, mem_iInter, disjoint_union_left,
      disjoint_relClosureH_iff U.isOpen hUH, disjoint_iUnion_left]
    exact ⟨fun h n => ⟨h.1, h.2 n⟩, fun h => ⟨(h 0).1, fun n => (h n).2⟩⟩
  -- the approximating events decrease almost surely
  have hAnmono : ∀ᵐ ω ∂P, ∀ n m, n ≤ m → ω ∈ An m → ω ∈ An n := by
    filter_upwards [hKmono] with ω hω n m hnm hm
    simp only [hAndef, mem_ofPred_eq, disjoint_union_left] at hm ⊢
    exact ⟨hm.1, hm.2.mono_left (hω hnm)⟩
  -- the marked approximating events are events of the complementary projection
  have hstep : ∀ m F, MeasurableSet[ℋ₀ ⊔ 𝓜 m] F → ∀ n, m ≤ n → MeasurableSet[WalkLaw.complSigma P G Y] (An n ∩ F) := by
    intro m F hF n hmn
    have hloc := WalkLaw.isHistoryAvoidanceLocal_union_of_det hYm
      (fun U' hU'H => hAℋ (measurableSet_avoid U'.isOpen hU'H))
      (fun U' hU'H => hK n (measurableSet_avoid U'.isOpen hU'H)) hℋ₀d (h𝓜d n) hlocA (hlocK n)
    have hF' : MeasurableSet[ℋ₀ ⊔ 𝓜 n] F := (sup_le_sup_left (h𝓜 hmn) ℋ₀) F hF
    have hAn : MeasurableSet[ℋ₀ ⊔ 𝓜 n] (An n) := by
      have e : An n = {ω | Disjoint (A ω) U} ∩ {ω | Disjoint (K n ω) U} := by
        ext ω
        simp only [hAndef, mem_ofPred_eq, disjoint_union_left, mem_inter_iff]
      rw [e]
      exact (le_sup_left (a := ℋ₀) (b := 𝓜 n) _ (hAℋ (measurableSet_avoid U.isOpen hUH))).inter
        (le_sup_right (a := ℋ₀) (b := 𝓜 n) _ (hK n (measurableSet_avoid U.isOpen hUH)))
    exact WalkLaw.mem_aeSigma_of_isHistoryAvoidanceLocal hYm hloc hUH hG hd hF'
      ((sup_le hℋ₀d (h𝓜d n)) _ (hAn.inter hF'))
  -- hence the avoidance event, traced on a mark of `ℋ₀ ⊔ 𝓜 m`, is one
  have hkey : ∀ m F, MeasurableSet[ℋ₀ ⊔ 𝓜 m] F → MeasurableSet[WalkLaw.complSigma P G Y] (Av ∩ F) := by
    intro m F hF
    have hI : MeasurableSet[WalkLaw.complSigma P G Y] (⋂ n, (An (n + m) ∩ F)) :=
      MeasurableSet.iInter fun n => hstep m F hF (n + m) (Nat.le_add_left m n)
    obtain ⟨T, hT, hTe⟩ := hI
    refine ⟨T, hT, EventuallyEq.trans ?_ hTe⟩
    filter_upwards [hAnmono] with ω hω
    apply propext
    rw [hAv]
    simp only [mem_inter_iff, mem_iInter]
    constructor
    · rintro ⟨h1, h2⟩ n
      exact ⟨h1 (n + m), h2⟩
    · intro h
      refine ⟨fun n => hω n (n + m) (Nat.le_add_right n m) (h n).1, (h 0).2⟩
  have hAvC : MeasurableSet[WalkLaw.complSigma P G Y] Av := by
    have h := hkey 0 univ MeasurableSet.univ
    rwa [inter_univ] at h
  -- the marks whose traced avoidance event is an event of the complementary projection form a σ-algebra
  have hle : ℋ₀ ⊔ ⨆ n, 𝓜 n ≤
      ({ MeasurableSet' := fun F => MeasurableSet[WalkLaw.complSigma P G Y] (Av ∩ F)
         measurableSet_empty := by
           simp only [inter_empty]
           exact @MeasurableSet.empty Ω (WalkLaw.complSigma P G Y)
         measurableSet_compl := fun F hF => by
           have e : Av ∩ Fᶜ = Av ∩ (Av ∩ F)ᶜ := by
             ext ω
             simp only [mem_inter_iff, mem_compl_iff]
             tauto
           rw [e]
           exact hAvC.inter hF.compl
         measurableSet_iUnion := fun f hf => by
           rw [inter_iUnion]
           exact MeasurableSet.iUnion hf } : MeasurableSpace Ω) := by
    refine sup_le (fun F hF => hkey 0 F ((le_sup_left : ℋ₀ ≤ ℋ₀ ⊔ 𝓜 0) F hF)) (iSup_le fun m F hF => ?_)
    exact hkey m F ((le_sup_right : 𝓜 m ≤ ℋ₀ ⊔ 𝓜 m) F hF)
  intro F hF
  exact hle F hF

end Core

end InteractingSLE.Theorem14.GW2Rd
