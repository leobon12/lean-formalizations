import SupercriticalLQGUniqueness.B2.PfeAxioms.A4RealAxiomV
import SupercriticalLQGUniqueness.B2.PfeAxioms.R68VLaw

 






set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.CircleAvg
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem r68v_real_across_twoSidedTight_of_coupling
    (hS : DG20Section4) (hPerc : DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    (c : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hc : ∀ r : ℚ, ∀ hr : 0 < r,
      Tendsto (fun n => (r : ℝ) *
        (m ⟨(ε n : ℝ) / (r : ℝ),
          Set.mem_Ioi.mpr (div_pos (ε n).property (Rat.cast_pos.mpr hr))⟩ : ℝ) /
        (m (ε n) : ℝ)) atTop
        (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ)))
    (Λ : ℝ) (hΛ : 1 < Λ)
    (hV : ∀ δ : Ioo (0 : ℝ) 1, ∀ r : ℚ, ∀ hr : 0 < r,
      Λ⁻¹ * (δ : ℝ) ^ Λ ≤
        (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
          (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
      (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
          (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
        Λ * (δ : ℝ) ^ (-Λ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    {V : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (h' : Ω' → DistC) (hN : ℕ → Ω' → DistC) (L : Ω' → LSCMetric)
    (hB : Final.DG20CouplingData ξ Q m ε c V P' h' hN L)
    (hSA : Final.CoupledSmallAnnuli ξ m ε V P' hN L)
    (hDm : Measurable D) (hII : ∀ᵐ ω ∂P', L ω = D (h' ω))
    (a : Ioi (0 : ℝ) → Ω → ℝ)
    (ha : ∀ r, ∀ᵐ ω ∂P, IsCircleAverage (h ω) r 0 (a r ω))
    (A : EuclideanAnnulus) :
    IsTwoSidedTight P (fun (r : Ioi (0 : ℝ)) ω =>
      ENNReal.ofReal ((c r : ℝ)⁻¹ * Real.exp (-((ξ : ℝ) * a r ω))) *
        acrossDist (D (h ω)) (A.dilate r r.2)) := by
  obtain ⟨K, hK, hKcmp⟩ := exists_uniform_cluster_normalizer_compare
    hS ξ Q hQ m hm ε hε c hc Λ hΛ hV
  choose ψ hψ c' hc' using fun r : Ioi (0 : ℝ) =>
    exists_real_ratio_cluster_of_section4 hS ξ Q hQ m hm ε hε r
  let Z' : Ioi (0 : ℝ) → Ω → ℝ≥0∞ := fun r ω =>
    acrossDist (B2.LscTop.smulMetric
      ⟨(c' r : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h ω) r 0),
        Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr (c' r).property) (Real.exp_pos _))⟩
      (B2.LscTop.dilate r (D (h ω)))) A
  apply twoSidedTight_of_factor_compare P _ Z' _ K hK
  · intro r
    filter_upwards [ha r] with ω hω
    have heq : circleAvg (h ω) r 0 = a r ω := circleAvg_eq_of_tendsto hω
    obtain ⟨hK1, hK2⟩ := hKcmp r (c' r) (ψ r) (hψ r) (hc' r)
    refine ⟨(c' r : ℝ) / (c r : ℝ), hK1, hK2, ?_⟩
    have hc0 : (c r : ℝ) ≠ 0 := ne_of_gt (c r).property
    have hc'0 : (c' r : ℝ) ≠ 0 := ne_of_gt (c' r).property
    simp only [Z']
    rw [acrossDist_smul_dilate, heq, ← mul_assoc,
      ← ENNReal.ofReal_mul (div_pos (c' r).property (c r).property).le]
    congr 2
    simp only [neg_mul]
    field_simp
  · intro η hη
    obtain ⟨M, hM, hT⟩ := scaled_across_upper_tail_cluster_of_section4
      hS ξ Q hQ m hm ε hε D hD P h hh X hX A η hη
    exact ⟨2 * M, by positivity, fun r => hT r (c' r) (ψ r) (hψ r) (hc' r)⟩
  · intro η hη
    obtain ⟨M, hM, hT⟩ := r68v_scaled_across_lower_tail_cluster_of_coupling
      hPerc hB hSA A η hη
    refine ⟨M, hM, fun r => ?_⟩
    have hLaw := r68v_measure_scaled_cost_lt_eq_of_coupling hB D hDm hII
      P h hh r (c' r) (fun G => acrossDist G A) (measurable_acrossDist A)
      (ENNReal.ofReal M⁻¹)
    change P {ω | acrossDist (r68vScaledLimitMetric ξ r (c' r) (h ω) (D (h ω))) A <
      ENNReal.ofReal M⁻¹} ≤ ENNReal.ofReal η
    rw [hLaw]
    exact hT r (c' r) (ψ r) (hψ r) (hc' r)
  · intro r
    simpa only [neg_mul] using
      (aemeasurable_annularV_costs_of_subseqLimit ξ m ε D hD P h hh X hX
        c a ha A r).1

theorem r68v_real_around_twoSidedTight_of_coupling
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (_hSkC : B2.DG20Lim.DG20LimitSkC)
    (hS : DG20Section4) (hPerc : DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    (c : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hc : ∀ r : ℚ, ∀ hr : 0 < r,
      Tendsto (fun n => (r : ℝ) *
        (m ⟨(ε n : ℝ) / (r : ℝ),
          Set.mem_Ioi.mpr (div_pos (ε n).property (Rat.cast_pos.mpr hr))⟩ : ℝ) /
        (m (ε n) : ℝ)) atTop
        (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ)))
    (Λ : ℝ) (hΛ : 1 < Λ)
    (hV : ∀ δ : Ioo (0 : ℝ) 1, ∀ r : ℚ, ∀ hr : 0 < r,
      Λ⁻¹ * (δ : ℝ) ^ Λ ≤
        (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
          (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
      (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
          (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
        Λ * (δ : ℝ) ^ (-Λ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    {V : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (h' : Ω' → DistC) (hN : ℕ → Ω' → DistC) (L : Ω' → LSCMetric)
    (hB : Final.DG20CouplingData ξ Q m ε c V P' h' hN L)
    (hSA : Final.CoupledSmallAnnuli ξ m ε V P' hN L)
    (hDm : Measurable D) (hII : ∀ᵐ ω ∂P', L ω = D (h' ω))
    (a : Ioi (0 : ℝ) → Ω → ℝ)
    (ha : ∀ r, ∀ᵐ ω ∂P, IsCircleAverage (h ω) r 0 (a r ω))
    (A : EuclideanAnnulus) :
    IsTwoSidedTight P (fun (r : Ioi (0 : ℝ)) ω =>
      ENNReal.ofReal ((c r : ℝ)⁻¹ * Real.exp (-((ξ : ℝ) * a r ω))) *
        aroundDist (D (h ω)) (A.dilate r r.2)) := by
  obtain ⟨K, hK, hKcmp⟩ := exists_uniform_cluster_normalizer_compare
    hS ξ Q hQ m hm ε hε c hc Λ hΛ hV
  choose ψ hψ c' hc' using fun r : Ioi (0 : ℝ) =>
    exists_real_ratio_cluster_of_section4 hS ξ Q hQ m hm ε hε r
  let Z' : Ioi (0 : ℝ) → Ω → ℝ≥0∞ := fun r ω =>
    aroundDist (B2.LscTop.smulMetric
      ⟨(c' r : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h ω) r 0),
        Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr (c' r).property) (Real.exp_pos _))⟩
      (B2.LscTop.dilate r (D (h ω)))) A
  apply twoSidedTight_of_factor_compare P _ Z' _ K hK
  · intro r
    filter_upwards [ha r] with ω hω
    have heq : circleAvg (h ω) r 0 = a r ω := circleAvg_eq_of_tendsto hω
    obtain ⟨hK1, hK2⟩ := hKcmp r (c' r) (ψ r) (hψ r) (hc' r)
    refine ⟨(c' r : ℝ) / (c r : ℝ), hK1, hK2, ?_⟩
    have hc0 : (c r : ℝ) ≠ 0 := ne_of_gt (c r).property
    have hc'0 : (c' r : ℝ) ≠ 0 := ne_of_gt (c' r).property
    simp only [Z']
    rw [aroundDist_smul_dilate, heq, ← mul_assoc,
      ← ENNReal.ofReal_mul (div_pos (c' r).property (c r).property).le]
    congr 2
    simp only [neg_mul]
    field_simp
  · intro η hη
    obtain ⟨M, hM, hT⟩ := scaled_around_upper_tail_cluster_of_section4
      hS ξ Q hQ m hm ε hε D hD P h hh X hX A (η / 4) (by positivity)
    refine ⟨8 * M, by positivity, fun r => ?_⟩
    have hSum : ENNReal.ofReal (2 * M) + ENNReal.ofReal (2 * M) +
        ENNReal.ofReal (2 * M) + ENNReal.ofReal (2 * M) =
        ENNReal.ofReal (8 * M) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    have hδsum : ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4) +
        ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4) = ENNReal.ofReal η := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    have hTr := hT r (c' r) (ψ r) (hψ r) (hc' r)
    rw [hSum, hδsum] at hTr
    exact hTr
  · intro η hη
    obtain ⟨M, hM, hT⟩ := r68v_scaled_around_lower_tail_cluster_of_coupling
      hPerc hB hSA A η hη
    refine ⟨M, hM, fun r => ?_⟩
    have hLaw := r68v_measure_scaled_cost_lt_eq_of_coupling hB D hDm hII
      P h hh r (c' r) (fun G => aroundDist G A)
      (Uniqueness.TwoScale.S36.measurable_aroundDist_fixed A)
      (ENNReal.ofReal M⁻¹)
    change P {ω | aroundDist (r68vScaledLimitMetric ξ r (c' r) (h ω) (D (h ω))) A <
      ENNReal.ofReal M⁻¹} ≤ ENNReal.ofReal η
    rw [hLaw]
    exact hT r (c' r) (ψ r) (hψ r) (hc' r)
  · intro r
    simpa only [neg_mul] using
      (aemeasurable_annularV_costs_of_subseqLimit ξ m ε D hD P h hh X hX
        c a ha A r).2

theorem r68v_pfeAxiomV_of_coupling
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (hSkC : B2.DG20Lim.DG20LimitSkC)
    (hS : DG20Section4) (hPerc : DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    (c : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hc : ∀ r : ℚ, ∀ hr : 0 < r,
      Tendsto (fun n => (r : ℝ) *
        (m ⟨(ε n : ℝ) / (r : ℝ),
          Set.mem_Ioi.mpr (div_pos (ε n).property (Rat.cast_pos.mpr hr))⟩ : ℝ) /
        (m (ε n) : ℝ)) atTop
        (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ)))
    (Λ : ℝ) (hΛ : 1 < Λ)
    (hV : ∀ δ : Ioo (0 : ℝ) 1, ∀ r : ℚ, ∀ hr : 0 < r,
      Λ⁻¹ * (δ : ℝ) ^ Λ ≤
        (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
          (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
      (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
          (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
        Λ * (δ : ℝ) ^ (-Λ))
    {V : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (h' : Ω' → DistC) (hN : ℕ → Ω' → DistC) (L : Ω' → LSCMetric)
    (hB : Final.DG20CouplingData ξ Q m ε c V P' h' hN L)
    (hSA : Final.CoupledSmallAnnuli ξ m ε V P' hN L)
    (hDm : Measurable D) (hII : ∀ᵐ ω ∂P', L ω = D (h' ω)) :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWholePlaneGFF h P → ∀ a : Set.Ioi (0 : ℝ) → Ω → ℝ,
        (∀ r : Set.Ioi (0 : ℝ), ∀ᵐ ω ∂P, IsCircleAverage (h ω) r 0 (a r ω)) →
        ∀ A : EuclideanAnnulus,
          IsTwoSidedTight P (fun (r : Set.Ioi (0 : ℝ)) ω =>
            ENNReal.ofReal ((c r : ℝ)⁻¹ * Real.exp (-((ξ : ℝ) * a r ω))) *
              acrossDist (D (h ω)) (A.dilate r r.2)) ∧
          IsTwoSidedTight P (fun (r : Set.Ioi (0 : ℝ)) ω =>
            ENNReal.ofReal ((c r : ℝ)⁻¹ * Real.exp (-((ξ : ℝ) * a r ω))) *
              aroundDist (D (h ω)) (A.dilate r r.2)) := by
  intro Ω _ P _ h hh a ha A
  have hb := LQGMetric.DFGPS.isGFFPlusBddCont_of_wp hh.1
  choose X _ hX using fun t : Ioi (0 : ℝ) => exists_heatVersion_bdd hb t
  exact ⟨r68v_real_across_twoSidedTight_of_coupling hS hPerc ξ Q hQ m hm ε hε
      D hD c hc Λ hΛ hV P h hh X hX P' h' hN L hB hSA hDm hII a ha A,
    r68v_real_around_twoSidedTight_of_coupling hSkC hS hPerc ξ Q hQ m hm ε hε
      D hD c hc Λ hΛ hV P h hh X hX P' h' hN L hB hSA hDm hII a ha A⟩


end SupercriticalLQGUniqueness.B2.PfeAxioms
