/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TaMix
import QuantumZipper.Proofs.Loewner.CaraRZ

/-!
# The filling of a marked local set on a mark, almost surely

Packet PROVE-GW2-RELDET, ruling R113 (`GW2SzLoc.SchedHullLocalStatement`, corrected in round 17). The explored hull of
the schedule fills its trace only almost surely (the trace exists a.s.), and only on the mark `oldSuccess`. Off the
mark the explored set is the whole half-plane.

* `aeSigma_of_ae_eq`: completed σ-algebras are closed under almost-sure equality;
* `exists_halfIm_subset_compl_fwdHull`: a Loewner hull of a continuous driver at a finite time misses a far
  half-plane (`QuantumZipper.CaraR.fwdHull_subset_closedBall`);
* **`isHistoryAvoidanceLocal_fill_on_ae`**: let `S` be marked local for field-determined marks `ℋ` containing the null
  sets, with marks as avoidance events. Let `E` be a mark, and let `K` fill `S` almost surely on `E` (with `ℍ \ S` open
  and a far half-plane outside `K`). If the avoidance events of `K` are measurable, then `K` on `E`, `ℍ` off `E`, is
  marked local for `ℋ`, with marks as avoidance events.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology TopologicalSpace
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW2Rd

open LocalSets WholeField Coupling

theorem aeSigma_of_ae_eq {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Set Ω} (hY : MeasurableSet[aeSigma m P] Y) (hXY : X =ᵐ[P] Y) : MeasurableSet[aeSigma m P] X := by
  obtain ⟨Y', hY', hYY'⟩ := hY
  exact ⟨Y', hY', hXY.trans hYY'⟩

/-- **A Loewner hull at a finite time misses a far half-plane.** -/
theorem exists_halfIm_subset_compl_fwdHull {A : ℝ → ℝ} (hA : Continuous A) (s : ℝ) :
    ∃ R : ℝ, {w : ℂ | R < w.im} ⊆ H \ fwdHull A s := by
  set s' : ℝ := max s 1 with hs'
  have hs'0 : 0 < s' := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := s')).exists_bound_of_continuousOn hA.continuousOn
  have hsub : fwdHull A s ⊆ fwdHull A s' := fun z hz =>
    ⟨hz.1, hz.2.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
  have hball := QuantumZipper.CaraR.fwdHull_subset_closedBall hA hs'0
    (M := M) fun r hr => by simpa only [Real.norm_eq_abs] using hM r hr
  refine ⟨max (M + 3 * Real.sqrt s') 0, fun w hw => ⟨?_, fun hwK => ?_⟩⟩
  · exact show (0 : ℝ) < w.im from lt_of_le_of_lt (le_max_right _ _) hw
  · have h1 := hball (hsub hwK)
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 : w.im ≤ ‖w‖ := (le_abs_self _).trans (Complex.abs_im_le_norm w)
    have h3 : M + 3 * Real.sqrt s' < w.im := lt_of_le_of_lt (le_max_left _ _) hw
    linarith

section FillOn

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

open scoped Classical in
/-- **The filling of a marked local set on a mark, almost surely, with the half-plane off the mark.** -/
theorem isHistoryAvoidanceLocal_fill_on_ae (hhm : Measurable h)
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P) (hℋle : ℋ ≤ mΩ) (hnull : Ito.nullSets P ≤ ℋ)
    {S K : Ω → Set ℂ} (hloc : IsHistoryAvoidanceLocal ℋ S h P)
    (hSm : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[ℋ] {ω | Disjoint (S ω) U})
    (hKm : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet {ω | Disjoint (K ω) U})
    (hℋd : ℋ ≤ aeSigma (MeasurableSpace.comap h inferInstance) P) {E : Set Ω} (hE : MeasurableSet[ℋ] E)
    (hgood : ∀ᵐ ω ∂P, ω ∈ E → IsFilling (K ω) (S ω) ∧ IsOpen (H \ S ω) ∧
      ∃ R : ℝ, {w : ℂ | R < w.im} ⊆ H \ K ω) :
    (∀ U : Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[ℋ] {ω | Disjoint (if ω ∈ E then K ω else H) U}) ∧
      IsHistoryAvoidanceLocal ℋ (fun ω => if ω ∈ E then K ω else H) h P := by
  set A : Ω → Set ℂ := fun ω => if ω ∈ E then K ω else H with hAdef
  -- the countable combination of avoidance events of `S`
  set C : Opens ℂ → Set Ω → Set Ω := fun U M => ({ω | Disjoint (S ω) U} ∩ M) ∩
      ⋂ i, ⋂ (_ : denseSeq ℂ i ∈ (U : Set ℂ)), ⋃ F' : Finset (ℚ × ℚ × ℚ), ⋃ n : ℕ,
        ⋃ (_ : IsFillTube F' n (denseSeq ℂ i)),
          ({ω | Disjoint (S ω) (unionOpens U F' n (denseSeq ℂ i))} ∩ M) with hCdef
  have hVH : ∀ (U : Opens ℂ), (U : Set ℂ) ⊆ H → ∀ {F : Finset (ℚ × ℚ × ℚ)} {n : ℕ} {z : ℂ}, IsFillTube F n z →
      ((unionOpens U F n z : Opens ℂ) : Set ℂ) ⊆ H := fun U hUH _ n z hT =>
    union_subset hUH (fillTube_subset_H hT.1 n z)
  -- for a nonempty `U`, the marked avoidance event of `A` is almost surely the combination, marked by `E ∩ M`
  have hev : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → (U : Set ℂ) ≠ ∅ → ∀ M : Set Ω,
      {ω | Disjoint (A ω) U} ∩ M =ᵐ[P] C U (E ∩ M) := by
    intro U hUH hU M
    obtain ⟨z, hz⟩ := nonempty_iff_ne_empty.2 hU
    filter_upwards [hgood] with ω hω
    by_cases hωE : ω ∈ E
    · obtain ⟨hfill, hSo, R, hR⟩ := hω hωE
      have hiff := disjoint_fill_iff hfill hSo hR U.isOpen hUH
      have hAω : A ω = K ω := by simp only [hAdef, hωE, ↓reduceIte]
      change (ω ∈ {ω | Disjoint (A ω) U} ∩ M) = (ω ∈ C U (E ∩ M))
      simp only [hCdef, mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_iUnion, exists_prop, hAω, hωE, true_and]
      apply propext
      constructor
      · rintro ⟨hK, hωM⟩
        obtain ⟨h1, h2⟩ := hiff.1 hK
        refine ⟨⟨h1, hωM⟩, fun i hi => ?_⟩
        obtain ⟨F', n, hT, hω'⟩ := h2 i hi
        exact ⟨F', n, hT, hω', hωM⟩
      · rintro ⟨⟨h1, hωM⟩, h2⟩
        refine ⟨hiff.2 ⟨h1, fun i hi => ?_⟩, hωM⟩
        obtain ⟨F', n, hT, hω', -⟩ := h2 i hi
        exact ⟨F', n, hT, hω'⟩
    · have hAω : A ω = H := by simp only [hAdef, hωE, ↓reduceIte]
      change (ω ∈ {ω | Disjoint (A ω) U} ∩ M) = (ω ∈ C U (E ∩ M))
      apply propext
      constructor
      · rintro ⟨hd, -⟩
        rw [mem_ofPred_eq, hAω] at hd
        exact absurd hz (disjoint_left.1 hd (hUH hz))
      · rintro ⟨⟨-, hωEM⟩, -⟩
        exact absurd hωEM.1 hωE
  have hev0 : ∀ U : Opens ℂ, (U : Set ℂ) = ∅ → ∀ X : Ω → Set ℂ, {ω | Disjoint (X ω) U} = univ := by
    intro U hU X
    ext ω
    simp only [hU, mem_ofPred_eq, disjoint_empty, mem_univ]
  have hCm : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → ∀ {M : Set Ω}, MeasurableSet[ℋ] M → MeasurableSet[ℋ] (C U M) :=
    fun U hUH M hM => ((hSm U hUH).inter hM).inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
      MeasurableSet.iUnion fun F' => MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun hT =>
        (hSm _ (hVH U hUH hT)).inter hM)
  -- the ambient avoidance events of `A`
  have hAamb : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet {ω | Disjoint (A ω) U} := by
    intro U hUH
    have e : {ω | Disjoint (A ω) U} = (E ∩ {ω | Disjoint (K ω) U}) ∪ (Eᶜ ∩ {ω | Disjoint H (U : Set ℂ)}) := by
      ext ω
      by_cases hωE : ω ∈ E <;> simp [hAdef, hωE]
    rw [e]
    exact ((hℋle _ hE).inter (hKm U hUH)).union ((hℋle _ hE).compl.inter
      (by by_cases hd : Disjoint H (U : Set ℂ) <;> simp [hd]))
  refine ⟨fun U hUH => ?_, WalkLaw.isHistoryAvoidanceLocal_of_mem_aeSigma hhm fun U G hUH hG hd F hF => ?_⟩
  · by_cases hU : (U : Set ℂ) = ∅
    · rw [hev0 U hU]
      exact MeasurableSet.univ
    · have h1 := hev U hUH hU univ
      simp only [inter_univ] at h1
      exact Supp8.RelSafe.measurableSet_of_ae_eq hℋle hnull (hAamb U hUH) (hCm U hUH hE) h1
  · by_cases hU : (U : Set ℂ) = ∅
    · have e : {ω | Disjoint (A ω) U} ∩ F = {ω | Disjoint (S ω) U} ∩ F := by rw [hev0 U hU, hev0 U hU]
      rw [e]
      exact WalkLaw.mem_aeSigma_of_isHistoryAvoidanceLocal hhm hloc hUH hG hd hF (hℋd _ ((hSm U hUH).inter hF))
    · have hEF : MeasurableSet[ℋ] (E ∩ F) := hE.inter hF
      refine aeSigma_of_ae_eq ?_ (hev U hUH hU F)
      refine MeasurableSet.inter (mem_complSigma_of_le hhm hh hloc hSm hℋd le_rfl hUH hd hEF)
        (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun F' =>
          MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun hT => ?_)
      exact mem_complSigma_of_le hhm hh hloc hSm hℋd (fun x hx => Or.inl hx) (hVH U hUH hT) hd hEF

end FillOn

end InteractingSLE.Theorem14.GW2Rd
