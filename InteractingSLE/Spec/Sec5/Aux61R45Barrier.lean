/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61R45Compare
import InteractingSLE.Spec.Sec5.Aux61R45Visit
import InteractingSLE.Spec.Sec2.AddMarksGirsanov

/-! # GB7a for announced local evolutions, including the terminal stop -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal
namespace InteractingSLE.Sec5.Aux61R45
open GB7a Girsanov Sec2
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {κ : ℝ} {nL nR : ℕ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W B : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}

/-- The stopped local equations give the threshold-free comparison equations. -/
theorem cmpEquations_of_isSLEPathUpTo {ω : Ω} {ζ₀ : ℝ≥0∞}
    (hq : IsSLEPathUpTo κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (B · ω) ζ₀) :
    CmpEquations κ (Fin.append ρL ρR) (W · ω) (B · ω) (fun j t => allMarks VL VR j t ω) ζ₀ := by
  refine ⟨fun ht j => ?_, fun ht => ?_, fun ht j => ?_⟩
  · cases j using Fin.addCases with
    | left i => simpa [allMarks_castAdd] using hq.integrable_gapL ht i
    | right i => simpa [allMarks_natAdd] using hq.integrable_gapR ht i
  · rw [hq.w_eq ht, Fin.sum_univ_add, add_assoc]
    simp [allMarks_castAdd, allMarks_natAdd]
  · cases j using Fin.addCases with
    | left i =>
      simp only [allMarks_castAdd]
      rw [hq.vL_eq ht i, hq.vL_zero i]
    | right i =>
      simp only [allMarks_natAdd]
      rw [hq.vR_eq ht i, hq.vR_zero i]

/-- Aux. 62's right comparison for a local evolution with an announced stop. -/
theorem measure_rightCmp_eq_zero_upTo {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞}
    (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (hE : IsSLEEvolutionUpTo κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hLc : ∀ i ω, ContinuousOn (VL i · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hRc : ∀ j ω, ContinuousOn (VR j · ω) {t | (t : ℝ≥0∞) < ζ ω})
    {R : ℕ → Ω → ℝ≥0} (hR : Coupling.IsAnnouncingSeq 𝓕 P ζ R)
    {k : Fin nR} {k2 : Option (Fin nR)} (hk2 : ∀ j, k2 = some j → k < j)
    {S : ℝ} (hS : κ / 2 - 2 ≤ S) (q : ℝ≥0) :
    P {ω | RightCmp ρL ρR W VL VR ζ k k2 S q ω} = 0 := by
  set ρa : Fin (nL + nR) → ℝ := Fin.append ρL ρR with hρa
  set ρb : Fin (nL + nR) → ℝ := Fin.append (fun _ => 0) (refWeightR k k2 S) with hρb
  set k' : Fin (nL + nR) := Fin.natAdd nL k with hk'
  have hUc : ∀ j ω, ContinuousOn (allMarks VL VR j · ω) {t | (t : ℝ≥0∞) < ζ ω} := by
    intro j ω
    cases j using Fin.addCases with
    | left i => rw [allMarks_castAdd]; exact hLc i ω
    | right i => rw [allMarks_natAdd]; exact hRc i ω
  have hpath : ∀ᵐ ω ∂P, CmpEquations κ ρa (W · ω) (B · ω)
      (fun j t => allMarks VL VR j t ω) (ζ ω) :=
    hE.ae_path.mono fun _ hp => cmpEquations_of_isSLEPathUpTo hp
  have hsumb : ∀ (w : ℝ) (u : Fin (nL + nR) → ℝ), ∑ j, ρb j / (w - u j) =
      ∑ j, refWeightR k k2 S j / (w - u (Fin.natAdd nL j)) := fun w u => by
    rw [Fin.sum_univ_add]
    simp [hρb]
  have hdrift' : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω →
      (∀ j, IsMon ρa ρb k' j → W t ω ≠ allMarks VL VR j t ω) →
      0 < allMarks VL VR k' t ω - W t ω ∧ κ / (2 * (allMarks VL VR k' t ω - W t ω)) ≤
        cmpBeta ρb k' (W · ω) (fun j t => allMarks VL VR j t ω) t := by
    filter_upwards [hE.ae_path] with ω hp t ht hne
    have hk := hne k' (Or.inr (Or.inr rfl))
    rw [hk', allMarks_natAdd] at hk
    simp only [cmpBeta, hk', allMarks_natAdd]
    rw [hsumb]
    simp only [allMarks_natAdd]
    exact refWeight_drift_ge hκ4 hS hk2 (hp.monotone_vR ht) (hp.w_le_vR ht) hk
  have hA' : ∀ ω ∈ {ω | RightCmp ρL ρR W VL VR ζ k k2 S q ω}, ∃ T : ℝ≥0, q < T ∧ (T : ℝ≥0∞) ≤ ζ ω ∧
      (∀ t : ℝ≥0, q ≤ t → t < T → ∀ j, IsMon ρa ρb k' j → W t ω ≠ allMarks VL VR j t ω) ∧
      (∃ C : ℝ, ∀ t : ℝ≥0, q ≤ t → t < T →
        (∫ s in (q : ℝ)..t, (∑ j, (ρb j - ρa j) / (W s.toNNReal ω - allMarks VL VR j s.toNNReal ω)) ^ 2) ≤ C) ∧
      Tendsto (fun t => allMarks VL VR k' t ω - W t ω) (𝓝[<] T) (𝓝 0) := by
    intro ω hωA
    obtain ⟨T, hqT, hTζ, hgap, ⟨C, hC⟩, hlim⟩ := hωA
    refine ⟨T, hqT, hTζ, fun t hqt htT j hj => ?_, ⟨C, fun t hqt htT => ?_⟩, ?_⟩
    · cases j using Fin.addCases with
      | left i =>
        rw [allMarks_castAdd]
        refine (hgap t hqt htT).1 i ?_
        rcases hj with h | h | h
        · simpa [hρa] using h
        · simp [hρb] at h
        · exfalso
          have := congrArg Fin.val h
          simp only [hk', Fin.val_castAdd, Fin.val_natAdd] at this
          omega
      | right i =>
        rw [allMarks_natAdd]
        refine (hgap t hqt htT).2 i ?_
        rcases hj with h | h | h
        · exact Or.inl (by simpa [hρa] using h)
        · exact Or.inr (Or.inl (by simpa [hρb] using h))
        · exact Or.inr (Or.inr ((Fin.natAdd_inj nL).1 h))
    · convert hC t hqt htT using 4
      rw [Fin.sum_univ_add]
      simp [hρa, hρb, allMarks_castAdd, allMarks_natAdd, neg_div]
    · simpa [hk', allMarks_natAdd] using hlim
  exact measure_eq_zero_of_cmp hκ hE.brownian hE.adapted_W
    (Sec2.allMarks_adaptedBefore hE.adapted_VL hE.adapted_VR) hWc hUc hpath hdrift' hR q hA'

section Visits
variable {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {ζ : Ω → ℝ≥0∞} {η : Ω → ℝ≥0 → ℂ} {R : ℕ → Ω → ℝ≥0}

omit [IsProbabilityMeasure P] in
/-- A finite stop with a continuous state has the state limit used in GB7a. -/
theorem ae_state_limit_of_continuousOn
    (hc : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, (T : ℝ≥0∞) = ζ ω →
      ContinuousOn (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)) (Iic T)) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω →
      ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
        Tendsto (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω))
          (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) := by
  filter_upwards [hc] with ω hω T _ hT
  exact ⟨W T ω, (fun i => VL i T ω), (fun j => VR j T ω),
    ((hω T hT) T (Set.mem_Iic.2 le_rfl)).tendsto.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)⟩

/-- GB7a on the right through an announced local stop; equality with the stop
is included. Injectivity is supplied by the actual excursion, not by a full
reference evolution. -/
theorem gb7aEvol_right_upTo (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hord : IsOrderedForceWord xL xR)
    (hE : IsSLEEvolutionUpTo κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hLc : ∀ i ω, ContinuousOn (VL i · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hRc : ∀ j ω, ContinuousOn (VR j · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hR : Coupling.IsAnnouncingSeq 𝓕 P ζ R)
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (W · ω) (ζ ω) (η ω))
    (hinj : ∀ᵐ ω ∂P, InjOn (η ω) {t | (t : ℝ≥0∞) ≤ ζ ω})
    (hc : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, (T : ℝ≥0∞) = ζ ω →
      ContinuousOn (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)) (Iic T))
    {k : Fin nR} {a' : ℝ} (hnext : ∀ j, xR k < xR j → a' ≤ xR j)
    (hS : κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i => xR i ≤ xR k), ρR i) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → ∀ y ∈ Ioo (xR k) a', η ω t ≠ y := by
  have hnull : P (⋃ q : ℚ, {ω | RightCmp ρL ρR W VL VR ζ k none
      (∑ i ∈ univ.filter (fun i => xR i ≤ xR k), ρR i) (q : ℝ).toNNReal ω}) = 0 :=
    measure_iUnion_null fun q => measure_rightCmp_eq_zero_upTo hκ hκ4 hE hWc hLc hRc hR
      (by simp only [reduceCtorEq, false_implies, implies_true]) hS _
  filter_upwards [hE.ae_path, hη, hinj, ae_state_limit_of_continuousOn hc,
    measure_eq_zero_iff_ae_notMem.1 hnull] with ω hp hg hi hl hn t ht y hy he
  obtain ⟨q, hq⟩ := rightCmpPath_of_visit_upTo hp hord hg hi hl hnext ⟨t, ht, y, hy, he⟩
  exact hn (mem_iUnion.2 ⟨q, rightCmp_iff.2 hq⟩)

/-- The left-hand stopped barrier, by reflection of the local equations. -/
theorem gb7aEvol_left_upTo (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hord : IsOrderedForceWord xL xR)
    (hE : IsSLEEvolutionUpTo κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hLc : ∀ i ω, ContinuousOn (VL i · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hRc : ∀ j ω, ContinuousOn (VR j · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hR : Coupling.IsAnnouncingSeq 𝓕 P ζ R)
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (W · ω) (ζ ω) (η ω))
    (hinj : ∀ᵐ ω ∂P, InjOn (η ω) {t | (t : ℝ≥0∞) ≤ ζ ω})
    (hc : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, (T : ℝ≥0∞) = ζ ω →
      ContinuousOn (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)) (Iic T))
    {k : Fin nL} {a : ℝ} (hnext : ∀ j, xL j < xL k → xL j ≤ a)
    (hS : κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i => xL k ≤ xL i), ρL i) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → ∀ y ∈ Ioo a (xL k), η ω t ≠ y := by
  have hER : IsSLEEvolutionUpTo κ (-xR) (-xL) ρR ρL P 𝓕 (-W)
      (fun i => -VR i) (fun i => -VL i) (-B) ζ :=
    ⟨hE.brownian.neg, hE.adapted_W.neg, fun i => (hE.adapted_VR i).neg,
      fun j => (hE.adapted_VL j).neg, hE.ae_path.mono fun _ h => h.reflect⟩
  have hnull : P (⋃ q : ℚ, {ω | RightCmp ρR ρL (-W) (fun i => -VR i) (fun j => -VL j) ζ k none
      (∑ i ∈ univ.filter (fun i => xL k ≤ xL i), ρL i) (q : ℝ).toNNReal ω}) = 0 :=
    measure_iUnion_null fun q => measure_rightCmp_eq_zero_upTo hκ hκ4 hER
      (fun ω => (hWc ω).neg) (fun i ω => (hRc i ω).neg) (fun j ω => (hLc j ω).neg) hR
      (by simp only [reduceCtorEq, false_implies, implies_true]) hS _
  filter_upwards [hE.ae_path, hη, hinj, ae_state_limit_of_continuousOn hc,
    measure_eq_zero_iff_ae_notMem.1 hnull] with ω hp hg hi hl hn t ht y hy he
  obtain ⟨q, hq⟩ := leftCmpPath_of_visit_upTo hp hord hg hi hl hnext ⟨t, ht, y, hy, he⟩
  exact hn (mem_iUnion.2 ⟨q, rightCmp_iff.2 hq⟩)

end Visits

end InteractingSLE.Sec5.Aux61R45
