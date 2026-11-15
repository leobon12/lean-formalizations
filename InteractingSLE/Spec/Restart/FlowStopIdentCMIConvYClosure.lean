/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvYEvents

/-! # Increasing local sets: relative closure of the union -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI
open QuantumZipper LQGMetric LocalSets

/-- Countable unions are measurable for the hitting sigma algebra. -/
theorem measurable_iUnion_hitting {S : Type*} [mS : MeasurableSpace S]
    {A : ℕ → S → Set ℂ} (hA : ∀ n, Measurable[mS, hittingSigma] (A n)) :
    Measurable[mS, hittingSigma] (fun ω => ⋃ n, A n ω) := by
  refine measurable_generateFrom ?_
  rintro _ ⟨U, hU, hUH, rfl⟩
  have he : (fun ω => ⋃ n, A n ω) ⁻¹' {T | (T ∩ U).Nonempty} =
      ⋃ n, {ω | (A n ω ∩ U).Nonempty} := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, mem_iUnion, iUnion_inter, nonempty_iUnion]
  rw [he]
  exact MeasurableSet.iUnion fun n => hA n (measurableSet_hitting hU hUH)

/-- Avoiding an open set is unchanged by relative closure. -/
theorem disjoint_relClosureH_open_iff {A U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H) :
    Disjoint (relClosureH A) U ↔ Disjoint A U := by
  simp only [disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty,
    relClosureH_inter_nonempty_iff hU hUH]

/-- The relative closure of an increasing sequence of local sets is local.
Only almost sure monotonicity is needed. This is the Gaussian closure step;
it does not identify this closure with a filled terminal Loewner hull. -/
theorem isLocalSet_relClosure_iUnion {S : Type u} [mS : MeasurableSpace S]
    {P : Measure S} [IsProbabilityMeasure P] {h : S → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {A : ℕ → S → Set ℂ}
    (hA : ∀ n, Measurable[mS, hittingSigma] (A n))
    (hmono : ∀ᵐ ω ∂P, Monotone fun n => A n ω) (hloc : ∀ n, IsLocalSet (A n) h P) :
    IsLocalSet (fun ω => relClosureH (⋃ n, A n ω)) h P := by
  have hAm := measurable_relClosureH.comp (measurable_iUnion_hitting hA)
  have hAc : ∀ᵐ ω ∂P, relClosureH (⋃ n, A n ω) ⊆ H ∧
      IsOpen (H \ relClosureH (⋃ n, A n ω)) :=
    Eventually.of_forall fun _ => ⟨relClosureH_subset _, isOpen_H_diff_relClosureH _⟩
  apply ((isLocalSet_tfae hh hAm hAc).out 1 4).1
  intro U G hUH hG hMD
  let E : ℕ → Set S := fun n => {ω | Disjoint (A n ω) U}
  let Eall : Set S := {ω | Disjoint (relClosureH (⋃ n, A n ω)) U}
  have hEn : ∀ n, MeasurableSet (E n) := fun n => hA n (measurableSet_avoid U.isOpen hUH)
  have hE : Eall = ⋂ n, E n := by
    ext ω
    simp only [Eall, E, mem_ofPred_eq, mem_iInter, disjoint_relClosureH_open_iff U.isOpen hUH,
      disjoint_iUnion_left]
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => (E n).indicator (fun _ => (1 : ℝ)) ω) atTop
      (𝓝 (Eall.indicator (fun _ => (1 : ℝ)) ω)) := by
    filter_upwards [hmono] with ω hm
    by_cases he : ω ∈ Eall
    · have hn : ∀ n, ω ∈ E n := by simpa only [hE, mem_iInter] using he
      simpa only [indicator_of_mem he, indicator_of_mem (hn _)] using
        (tendsto_const_nhds (x := (1 : ℝ)))
    · have hn : ¬ ∀ n, ω ∈ E n := by simpa only [hE, mem_iInter] using he
      obtain ⟨n, hn⟩ := not_forall.mp hn
      rw [indicator_of_notMem he]
      apply (tendsto_const_nhds (x := (0 : ℝ))).congr'
      filter_upwards [eventually_ge_atTop n] with m hnm
      have hnm' : ω ∉ E m := fun hω => hn (hω.mono_left (hm hnm))
      simp only [indicator_of_notMem hnm']
  have hk : ∀ n, AEStronglyMeasurable[MeasurableSpace.comap
      (fun ω => markovCompl G (h ω)) inferInstance]
      (P[(E n).indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap h inferInstance]) P := by
    intro n
    obtain ⟨g, hg, he⟩ := (IsLocalSet.isMarkedAvoidanceLocal hh.measurable (hA n) (hloc n)
      |>.isAvoidanceLocal (hA n) hh.measurable) U G hUH hG hMD
    exact ((hg.comp (measurable_iff_comap_le.2 le_rfl)).stronglyMeasurable.aestronglyMeasurable).congr
      he.symm
  have hkg := aestronglyMeasurable_condExp_of_dominated_limit hh.measurable.comap_le
    (fun n => (measurable_const.indicator (hEn n)).aestronglyMeasurable)
    (fun _ => (1 : ℝ)) (integrable_const _) (fun n => Eventually.of_forall fun ω => by
      by_cases he : ω ∈ E n <;> simp [he]) hlim hk
  obtain ⟨g, hg, he⟩ := hkg.stronglyMeasurable_mk.exists_eq_measurable_comp
  refine ⟨g, hg.measurable, hkg.ae_eq_mk.trans ?_⟩
  rw [he]
  rfl

end InteractingSLE.Restart.FlowStopIdentCMI
