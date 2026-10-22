import HigherDimLQGContinuity.SiteEvents.Trials
import HigherDimLQGMetric.Field.SphereBump
import HigherDimLQGMetric.ShellDec.Sigma

/-! Locality of pinned sphere averages through mean-zero test pairings. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false
noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory Set Filter Topology Metric
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

private theorem q10_measurable_pairing0 (V : Set (Rd d))
    (φ : {ψ : TestRd0 d // tsupport (ψ.1 : Rd d → ℝ) ⊆ V}) :
    Measurable[fieldSigma0 (id : DistRd d → DistRd d) V]
      (fun g : DistRd d => g φ.1.1) := by
  have hsrc : Measurable[fieldSigma0 id V]
      (fun g : DistRd d =>
        fun ψ : {ψ : TestRd0 d // tsupport (ψ.1 : Rd d → ℝ) ⊆ V} => g ψ.1.1) :=
    Measurable.of_comap_le le_rfl
  exact (measurable_pi_apply φ).comp hsrc

/-- Under the unit pin, a sphere average whose sphere lies in `V` has a `fieldSigma0 id V`
measurable representative when the pin sphere also lies in `V`. -/
theorem q10_exists_local_pinAvg (hd : 2 ≤ d) {V : Set (Rd d)} (hV : IsOpen V)
    {r : ℝ} (hr : 0 < r) (z : Rd d)
    (hS : sphere z r ⊆ V) (hpin : sphere (0 : Rd d) 1 ⊆ V) :
    ∃ Y : DistRd d → ℝ, Measurable[fieldSigma0 id V] Y ∧
      (fun g : DistRd d => sphereAvg g r z) =ᵐ[pinLaw d 1] Y := by
  let U : TopologicalSpace.Opens (Rd d) := ⟨V, hV⟩
  obtain ⟨N₁, hN₁⟩ := exists_tsupport_sphBump_subset
    (U := U) (r := r) (z := z) (by simpa [U, abs_of_pos hr] using hS)
  obtain ⟨N₂, hN₂⟩ := exists_tsupport_sphBump_subset
    (U := U) (r := (1 : ℝ)) (z := (0 : Rd d)) (by simpa [U] using hpin)
  let N := max N₁ N₂
  have hN₁' (n : ℕ) : tsupport (⇑(sphBump (n + N) z r)) ⊆ V :=
    hN₁ _ (by dsimp [N]; omega)
  have hN₂' (n : ℕ) : tsupport (⇑(sphBump (n + N) (0 : Rd d) 1)) ⊆ V :=
    hN₂ _ (by dsimp [N]; omega)
  let φ (n : ℕ) : {ψ : TestRd0 d // tsupport (ψ.1 : Rd d → ℝ) ⊆ V} :=
    ⟨sphDiff0 (by omega : 1 ≤ d) (n + N) z r (n + N) 0 1, by
      change tsupport (⇑(sphBump (n + N) z r - sphBump (n + N) 0 1 : TestRd d)) ⊆ V
      exact (tsupport_sub _ _).trans (union_subset (hN₁' n) (hN₂' n))⟩
  let Y : DistRd d → ℝ := fun g => limUnder atTop (fun n => g (φ n).1.1)
  have hYm : Measurable[fieldSigma0 id V] Y := by
    have hm (n : ℕ) : StronglyMeasurable[fieldSigma0 id V]
        (fun g : DistRd d => g (φ n).1.1) :=
      (q10_measurable_pairing0 V (φ n)).stronglyMeasurable
    exact (@StronglyMeasurable.limUnder ℕ (DistRd d) ℝ (fieldSigma0 id V)
      _ _ atTop _ (fun n g => g (φ n).1.1) _ _ hm).measurable
  refine ⟨Y, hYm, ?_⟩
  have hLGF := (isWholeSpaceLGF_pinLaw hd one_pos).1
  have hPin := (isWholeSpaceLGF_pinLaw hd one_pos).2
  filter_upwards [hLGF.ae_exists_tendsto_sphereAvgSeq hd hr z,
    hLGF.ae_exists_tendsto_sphereAvgSeq hd one_pos 0, hPin]
    with g hzr h01 h0
  have ht₁ : Tendsto (fun n => sphereAvgSeq g r z (n + N)) atTop
      (𝓝 (sphereAvg g r z)) :=
    (tendsto_sphereAvgSeq_sphereAvg hzr).comp (tendsto_add_atTop_nat N)
  have ht₂ : Tendsto (fun n => sphereAvgSeq g 1 0 (n + N)) atTop
      (𝓝 (sphereAvg g 1 0)) :=
    (tendsto_sphereAvgSeq_sphereAvg h01).comp (tendsto_add_atTop_nat N)
  have hlim : Tendsto (fun n => g (φ n).1.1) atTop
      (𝓝 (sphereAvg g r z - sphereAvg g 1 0)) := by
    simpa only [φ, sphDiff0, sphereAvgSeq_sub_eq_apply_sphDiff] using ht₁.sub ht₂
  change sphereAvg g r z = Y g
  change sphereAvg g r z = limUnder atTop (fun n => g (φ n).1.1)
  rw [hlim.limUnder_eq, h0, sub_zero]

/-- The pinned sphere-average cap is a local event. -/
theorem q10_pinCap_aeEventIn (hd : 2 ≤ d) {V : Set (Rd d)} (hV : IsOpen V)
    {r : ℝ} (hr : 0 < r) (z : Rd d)
    (hS : sphere z r ⊆ V) (hpin : sphere (0 : Rd d) 1 ⊆ V) (K : ℝ) :
    AEEventIn (pinLaw d 1) (fieldSigma0 id V)
      {g | |sphereAvg g r z| ≤ K} := by
  obtain ⟨Y, hYm, hYeq⟩ := q10_exists_local_pinAvg hd hV hr z hS hpin
  letI : MeasurableSpace (DistRd d) := fieldSigma0 id V
  have hset : MeasurableSet[fieldSigma0 (id : DistRd d → DistRd d) V]
      {g : DistRd d | |Y g| ≤ K} := hYm.abs measurableSet_Iic
  refine ⟨{g | |Y g| ≤ K}, hset, ?_⟩
  filter_upwards [hYeq] with g hg
  simp only [hg]

end HigherDimLQGContinuity
