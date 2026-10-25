import SupercriticalLQGUniqueness.B2.PfeAxioms.A4UniformCompare
import SupercriticalLQGUniqueness.B2.PfeAxioms.A4ScaledUpperCluster
import SupercriticalLQGUniqueness.B2.PfeAxioms.A4ScaledLowerCluster
import SupercriticalLQGUniqueness.B2.PfeAxioms.AnnularVMeasurable
import SupercriticalLQGUniqueness.B2.PfeAxioms.RealAxiomVSkC
import SupercriticalLQGUniqueness.B2.PfeWeyl.InputsS1

 










set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.CircleAvg
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

theorem twoSidedTight_of_factor_compare
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z Z' : ι → Ω → ℝ≥0∞) (hZm : ∀ i, AEMeasurable (Z i) P)
    (K : ℝ) (hK : 0 < K)
    (hfac : ∀ i, ∀ᵐ ω ∂P, ∃ t : ℝ, K⁻¹ ≤ t ∧ t ≤ K ∧
      Z i ω = ENNReal.ofReal t * Z' i ω)
    (hup : ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧ ∀ i,
      P {ω | ENNReal.ofReal M < Z' i ω} ≤ ENNReal.ofReal η)
    (hlow : ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧ ∀ i,
      P {ω | Z' i ω < ENNReal.ofReal M⁻¹} ≤ ENNReal.ofReal η) :
    IsTwoSidedTight P Z := by
  refine ⟨hZm, ?_⟩
  intro η hη
  obtain ⟨Mu, hMu, hU⟩ := hup η hη
  obtain ⟨Ml, hMl, hL⟩ := hlow η hη
  let M : ℝ := K * (Mu + Ml)
  have hM : 0 < M := by positivity
  refine ⟨M, hM, fun i => ⟨?_, ?_⟩⟩
  · have hsub : ∀ᵐ ω ∂P, ENNReal.ofReal M < Z i ω →
        ENNReal.ofReal Mu < Z' i ω := by
      filter_upwards [hfac i] with ω ⟨t, ht1, ht2, hZ⟩
      intro hlt
      by_contra hle'
      have hle := not_lt.mp hle'
      have hbound : Z i ω ≤ ENNReal.ofReal M := by
        rw [hZ]
        calc ENNReal.ofReal t * Z' i ω
            ≤ ENNReal.ofReal K * ENNReal.ofReal Mu :=
              mul_le_mul' (ENNReal.ofReal_le_ofReal ht2) hle
          _ = ENNReal.ofReal (K * Mu) := (ENNReal.ofReal_mul hK.le).symm
          _ ≤ ENNReal.ofReal M := by
              apply ENNReal.ofReal_le_ofReal
              dsimp [M]
              nlinarith
      exact (not_lt.mpr hbound) hlt
    exact (measure_mono_ae hsub).trans (hU i)
  · have hsub : ∀ᵐ ω ∂P, Z i ω < ENNReal.ofReal M⁻¹ →
        Z' i ω < ENNReal.ofReal Ml⁻¹ := by
      filter_upwards [hfac i] with ω ⟨t, ht1, ht2, hZ⟩
      intro hlt
      by_contra hle'
      have hle := not_lt.mp hle'
      have hbound : ENNReal.ofReal M⁻¹ ≤ Z i ω := by
        rw [hZ]
        calc ENNReal.ofReal M⁻¹ ≤ ENNReal.ofReal (K⁻¹ * Ml⁻¹) := by
              apply ENNReal.ofReal_le_ofReal
              rw [← mul_inv]
              apply inv_anti₀ (by positivity)
              dsimp [M]
              nlinarith
          _ = ENNReal.ofReal K⁻¹ * ENNReal.ofReal Ml⁻¹ :=
              ENNReal.ofReal_mul (inv_pos.mpr hK).le
          _ ≤ ENNReal.ofReal t * Z' i ω :=
              mul_le_mul' (ENNReal.ofReal_le_ofReal ht1) hle
      exact (not_lt.mpr hbound) hlt
    exact (measure_mono_ae hsub).trans (hL i)

 




theorem real_across_twoSidedTight_of_section4_perc
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
    (hsmall : ∀ k : ℕ, ∀ᵐ ω ∂P,
      PfeWeyl.SmallAnnulusCosts
        (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω))
        (D (h ω)) (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1)))
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
    obtain ⟨M, hM, hT⟩ := scaled_across_lower_tail_cluster_of_perc
      hPerc ξ m hm ε hε D hD P h hh X hX hsmall A η hη
    exact ⟨M, hM, fun r => hT r (c' r) (ψ r) (hψ r) (hc' r)⟩
  · intro r
    simpa only [neg_mul] using
      (aemeasurable_annularV_costs_of_subseqLimit ξ m ε D hD P h hh X hX
        c a ha A r).1

 


theorem real_around_twoSidedTight_of_section4_perc_skC
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
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (hsmall : ∀ k : ℕ, ∀ᵐ ω ∂P,
      PfeWeyl.SmallAnnulusCosts
        (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω))
        (D (h ω)) (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1)))
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
    obtain ⟨M, hM, hT⟩ := scaled_around_lower_tail_cluster_of_perc_skC
      hSkC hPerc ξ Q hQ m hm ε hε D hD P h hh X hX hsmall A η hη
    exact ⟨M, hM, fun r => hT r (c' r) (ψ r) (hψ r) (hc' r)⟩
  · intro r
    simpa only [neg_mul] using
      (aemeasurable_annularV_costs_of_subseqLimit ξ m ε D hD P h hh X hX
        c a ha A r).2

 




theorem pfeAxiomV_of_section4_perc_skC
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (hSkC : B2.DG20Lim.DG20LimitSkC)
    (hS : DG20Section4) (hPerc : DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    (hsmall : PfeWeyl.NormalizedSmallAnnuli ξ m ε D)
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
        Λ * (δ : ℝ) ^ (-Λ)) :
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
  have hsm := hsmall P h hh X hX
  exact ⟨real_across_twoSidedTight_of_section4_perc hS hPerc ξ Q hQ m hm ε hε
      D hD c hc Λ hΛ hV P h hh X hX hsm a ha A,
    real_around_twoSidedTight_of_section4_perc_skC hSkC hS hPerc ξ Q hQ m hm ε hε
      D hD c hc Λ hΛ hV P h hh X hX hsm a ha A⟩

 




theorem exists_pfe_normalizer_axiomV_of_skC
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (hSkC : B2.DG20Lim.DG20LimitSkC)
    (hS : DG20Section4) (hPerc : DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
        (∀ r : ℚ, ∀ hr : 0 < r,
          Tendsto (fun n => (r : ℝ) *
            (m ⟨(ε (φ n) : ℝ) / (r : ℝ),
              Set.mem_Ioi.mpr (div_pos (ε (φ n)).property
                (Rat.cast_pos.mpr hr))⟩ : ℝ) /
            (m (ε (φ n)) : ℝ)) atTop
            (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ))) ∧
        (∃ Λ : ℝ, 1 < Λ ∧
          ∀ δ : Set.Ioo (0 : ℝ) 1, ∀ r : ℚ, ∀ hr : 0 < r,
            Λ⁻¹ * (δ : ℝ) ^ Λ ≤
              (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
                (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
                (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
            (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
                (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
                (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
              Λ * (δ : ℝ) ^ (-Λ)) ∧
        ∀ (ψ : ℕ → ℕ), StrictMono ψ → ∀ D : DistC → LSCMetric,
          SubseqLimit ξ m (fun n => ε (φ (ψ n))) D →
          PfeWeyl.NormalizedSmallAnnuli ξ m (fun n => ε (φ (ψ n))) D →
          ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
            ∀ a : Set.Ioi (0 : ℝ) → Ω → ℝ,
            (∀ r : Set.Ioi (0 : ℝ), ∀ᵐ ω ∂P, IsCircleAverage (h ω) r 0 (a r ω)) →
            ∀ A : EuclideanAnnulus,
              IsTwoSidedTight P (fun (r : Set.Ioi (0 : ℝ)) ω =>
                ENNReal.ofReal ((c r : ℝ)⁻¹ * Real.exp (-((ξ : ℝ) * a r ω))) *
                  acrossDist (D (h ω)) (A.dilate r r.2)) ∧
              IsTwoSidedTight P (fun (r : Set.Ioi (0 : ℝ)) ω =>
                ENNReal.ofReal ((c r : ℝ)⁻¹ * Real.exp (-((ξ : ℝ) * a r ω))) *
                  aroundDist (D (h ω)) (A.dilate r r.2)) := by
  obtain ⟨φ, hφ, c, hc, Λ, hΛ, hV⟩ :=
    exists_real_axiomV_of_DG20LimitSkC hS hSkC ξ Q hQ m hm ε hε
  refine ⟨φ, hφ, c, hc, ⟨Λ, hΛ, hV⟩, ?_⟩
  intro ψ hψ D hD hsmall
  have hεφψ : Tendsto (fun n => (ε (φ (ψ n)) : ℝ)) atTop (𝓝 0) :=
    hε.comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop)
  have hcψ : ∀ r : ℚ, ∀ hr : 0 < r,
      Tendsto (fun n => (r : ℝ) *
        (m ⟨(ε (φ (ψ n)) : ℝ) / (r : ℝ),
          Set.mem_Ioi.mpr (div_pos (ε (φ (ψ n))).property
            (Rat.cast_pos.mpr hr))⟩ : ℝ) /
        (m (ε (φ (ψ n))) : ℝ)) atTop
        (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ)) :=
    fun r hr => (hc r hr).comp hψ.tendsto_atTop
  intro Ω _ P _ h hh
  exact pfeAxiomV_of_section4_perc_skC hSkC hS hPerc ξ Q hQ m hm
    (fun n => ε (φ (ψ n))) hεφψ D hD hsmall c hcψ Λ hΛ hV P h hh

end SupercriticalLQGUniqueness.B2.PfeAxioms
