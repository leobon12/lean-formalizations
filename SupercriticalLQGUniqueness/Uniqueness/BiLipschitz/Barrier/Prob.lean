import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Barrier
import SupercriticalLQGUniqueness.Frozen.IsLFPPExponent
import LQGMetric.Field.CircleAvgProc
import LQGMetric.Field.CircleAvgRate




 













set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace Uniqueness.BiLipschitz.Barrier

open LQGMetric (DistC IsWholePlaneGFF)

 
def baseAnnulus : EuclideanAnnulus := ⟨(0, (1, 2)), one_pos, one_lt_two⟩

theorem baseAnnulus_dilate (n : ℕ) (hr : (0 : ℝ) < (2 : ℝ) ^ n) :
    baseAnnulus.dilate ((2 : ℝ) ^ n) hr = dyadicAnnulus n := by
  apply Subtype.ext
  simp only [EuclideanAnnulus.dilate, baseAnnulus, dyadicAnnulus, EuclideanAnnulus.center,
    EuclideanAnnulus.innerRadius, EuclideanAnnulus.outerRadius, smul_zero, mul_one, pow_succ]

 
theorem normalizer_le {ξ Q a : ℝ} (hξ : 0 < ξ) (n : ℕ)
    (ha : -(Q * n * Real.log 2 / 2) < a) :
    ((2 : ℝ) ^ n) ^ (-(ξ * Q)) * Real.exp (-(ξ * a)) ≤
      Real.exp (-(ξ * Q * Real.log 2 / 2) * n) := by
  rw [Real.rpow_def_of_pos (by positivity), Real.log_pow, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 : ξ * (-(Q * n * Real.log 2 / 2)) ≤ ξ * a := mul_le_mul_of_nonneg_left ha.le hξ.le
  have key : n * Real.log 2 * -(ξ * Q) + -(ξ * a) - -(ξ * Q * Real.log 2 / 2) * n =
      ξ * (-(Q * n * Real.log 2 / 2)) - ξ * a := by ring
  exact sub_nonpos.1 (key ▸ sub_nonpos.2 h1)

 
theorem ae_barrier {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Q D) (hQ : 0 < Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, Barrier (D (h ω)) := by
  have hξ : (0 : ℝ) < ξ := ξ.2
  
  let a : Set.Ioi (0 : ℝ) → Ω → ℝ := fun r ω => LQGMetric.circleAvg (h ω) r 0
  have ha : ∀ r : Set.Ioi (0 : ℝ), ∀ᵐ ω ∂P, IsCircleAverage (h ω) r 0 (a r ω) := by
    intro r
    filter_upwards [LQGMetric.CircleAvg.ae_tendsto_mollAvg hh.1 0 r.2] with ω hω
    obtain ⟨b, hb⟩ := hω
    have hab : a r ω = b := LQGMetric.CircleAvg.circleAvg_eq_of_tendsto hb
    show Tendsto _ atTop (𝓝 (a r ω))
    rw [hab]
    exact hb
  
  have hV := (hD.2.2.2.2.2 P h hh a ha baseAnnulus).1
  have hnorm : ∀ᵐ ω ∂P, LQGMetric.circleAvg (h ω) 1 0 = 0 := by
    filter_upwards [hh.2] with ω hω
    exact LQGMetric.CircleAvg.circleAvg_eq_of_tendsto hω
  
  have key : ∀ (M : ℕ) (δ : ℝ), 0 < δ → ∃ N : ℕ, ∀ n ≥ N,
      P {ω | acrossDist (D (h ω)) (dyadicAnnulus n) ≤ M} ≤ ENNReal.ofReal δ := by
    intro M δ hδ
    obtain ⟨Mε, hMε, hMεP⟩ := hV.2 (δ / 2) (half_pos hδ)
    have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
    
    have hc : 0 < ξ * Q * Real.log 2 / 2 := by positivity
    have hev1 : ∀ᶠ n : ℕ in atTop,
        Real.exp (-(ξ * Q * Real.log 2 / 2) * n) * M < Mε⁻¹ := by
      have h0 : Tendsto (fun n : ℕ => Real.exp (-(ξ * Q * Real.log 2 / 2) * n) * M) atTop
          (𝓝 (0 * M)) := by
        refine Tendsto.mul_const _ ?_
        have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
          ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hc)
        refine this.congr fun n => ?_
        simp only [Function.comp_apply, neg_mul]
      rw [zero_mul] at h0
      exact h0.eventually (gt_mem_nhds (inv_pos.2 hMε))
    
    have hev2 : ∀ᶠ n : ℕ in atTop, 4 / (Q ^ 2 * Real.log 2) / n ≤ δ / 2 := by
      have h0 := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (4 / (Q ^ 2 * Real.log 2))
      exact h0.eventually (ge_mem_nhds (half_pos hδ))
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hev1.and (hev2.and (eventually_ge_atTop 1)))
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨hn1, hn2, hn3⟩ := hN n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn3
    set t : ℝ := Q * n * Real.log 2 / 2 with ht
    have htpos : 0 < t := by positivity
    have hr : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    set r : Set.Ioi (0 : ℝ) := ⟨(2 : ℝ) ^ n, hr⟩ with hrdef
    
    set Z := LQGMetric.CircleAvg.cInc h ((2 : ℝ) ^ n) 0 1 0 with hZ
    have hlaw := LQGMetric.CircleAvg.map_cInc hh.1 hr one_pos 0 0
    have hfacts := LQGMetric.CircleAvg.gaussianReal_facts
      ((LQGMetric.CircleAvg.measurable_cInc hh.1 ((2 : ℝ) ^ n) 0 1 0).aemeasurable (μ := P)) hlaw.1
    have hmean : P[Z] = 0 := by
      have hm := (LQGMetric.CircleAvg.measurable_cInc hh.1 ((2 : ℝ) ^ n) 0 1 0).aemeasurable (μ := P)
      rw [show P[Z] = ∫ x, x ∂(P.map Z) from (integral_map hm aestronglyMeasurable_id).symm,
        hlaw.1, integral_id_gaussianReal]
    have hvar : Var[Z; P] = n * Real.log 2 := by
      rw [LQGMetric.CircleAvg.variance_cInc_one hh.1 hr 0, Real.log_pow,
        abs_of_nonneg (by positivity)]
    have hcheb : P {ω | t ≤ |Z ω - P[Z]|} ≤ ENNReal.ofReal (δ / 2) := by
      refine (meas_ge_le_variance_div_sq hfacts.2 htpos).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [hvar, ht]
      have : n * Real.log 2 / (Q * n * Real.log 2 / 2) ^ 2 = 4 / (Q ^ 2 * Real.log 2) / n := by
        field_simp
        norm_num
      rw [this]
      exact hn2
    
    have htight : P {ω | ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
        Real.exp (-((ξ : ℝ) * a r ω))) * acrossDist (D (h ω)) (baseAnnulus.dilate r r.2) <
          ENNReal.ofReal Mε⁻¹} ≤ ENNReal.ofReal (δ / 2) := (hMεP r).2
    
    have hincl : {ω | acrossDist (D (h ω)) (dyadicAnnulus n) ≤ M} ≤ᵐ[P]
        ({ω | t ≤ |Z ω - P[Z]|} ∪ {ω | ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
          Real.exp (-((ξ : ℝ) * a r ω))) * acrossDist (D (h ω)) (baseAnnulus.dilate r r.2) <
            ENNReal.ofReal Mε⁻¹} : Set Ω) := by
      filter_upwards [hnorm] with ω hω1 hωM
      replace hωM : acrossDist (D (h ω)) (dyadicAnnulus n) ≤ M := hωM
      by_cases hZt : t ≤ |Z ω - P[Z]|
      · exact Or.inl hZt
      · right
        push Not at hZt
        rw [hmean, sub_zero] at hZt
        have hZω : Z ω = a r ω := by
          simp only [hZ, LQGMetric.CircleAvg.cInc, hω1, sub_zero]
          rfl
        have haω : -t < a r ω := by
          rw [← hZω]; exact (abs_lt.1 hZt).1
        have hnb := normalizer_le hξ n (a := a r ω) (by rw [ht] at haω; exact haω)
        show ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) * Real.exp (-((ξ : ℝ) * a r ω))) *
          acrossDist (D (h ω)) (baseAnnulus.dilate r r.2) < ENNReal.ofReal Mε⁻¹
        rw [show baseAnnulus.dilate r r.2 = dyadicAnnulus n from baseAnnulus_dilate n hr]
        calc ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) * Real.exp (-((ξ : ℝ) * a r ω))) *
              acrossDist (D (h ω)) (dyadicAnnulus n)
            ≤ ENNReal.ofReal (Real.exp (-((ξ : ℝ) * Q * Real.log 2 / 2) * n)) * M :=
              mul_le_mul' (ENNReal.ofReal_le_ofReal hnb) hωM
          _ = ENNReal.ofReal (Real.exp (-((ξ : ℝ) * Q * Real.log 2 / 2) * n) * M) := by
              rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_natCast]
          _ < ENNReal.ofReal Mε⁻¹ :=
              (ENNReal.ofReal_lt_ofReal_iff (inv_pos.2 hMε)).2 hn1
    calc P {ω | acrossDist (D (h ω)) (dyadicAnnulus n) ≤ M}
        ≤ P ({ω | t ≤ |Z ω - P[Z]|} ∪ {ω | ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
          Real.exp (-((ξ : ℝ) * a r ω))) * acrossDist (D (h ω)) (baseAnnulus.dilate r r.2) <
            ENNReal.ofReal Mε⁻¹}) := measure_mono_ae hincl
      _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) :=
          (measure_union_le _ _).trans (add_le_add hcheb htight)
      _ = ENNReal.ofReal δ := by
          rw [← ENNReal.ofReal_add (half_pos hδ).le (half_pos hδ).le]
          congr 1
          ring
  
  choose N hN using fun k : ℕ => key k ((1 / 2 : ℝ) ^ k) (by positivity)
  let nseq : ℕ → ℕ := fun k => max k (N k)
  let E : ℕ → Set Ω := fun k => {ω | acrossDist (D (h ω)) (dyadicAnnulus (nseq k)) ≤ k}
  have hE : ∀ k, P (E k) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := fun k =>
    hN k (nseq k) (le_max_right _ _)
  have hsum : (∑' k, P (E k)) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hE)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) summable_geometric_two]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  intro n₀ M
  obtain ⟨K, hK⟩ := eventually_atTop.1 hω
  set k := max K (max n₀ M) with hk
  refine ⟨nseq k, ?_, ?_⟩
  · exact (le_max_left n₀ M).trans ((le_max_right K _).trans (le_max_left k (N k)))
  · have hnot : ω ∉ E k := hK k (le_max_left _ _)
    have hlt : (k : ℝ≥0∞) < acrossDist (D (h ω)) (dyadicAnnulus (nseq k)) := by
      simpa [E] using hnot
    refine lt_of_le_of_lt ?_ hlt
    exact_mod_cast (le_max_right n₀ M).trans (le_max_right K _)

end Uniqueness.BiLipschitz.Barrier
end SupercriticalLQGUniqueness
