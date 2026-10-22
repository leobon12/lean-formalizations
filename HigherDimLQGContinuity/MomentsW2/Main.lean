import HigherDimLQGContinuity.MomentsW2.FinalTail

/-!
# W2: uniform inverse moments for white-noise shell crossings
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLFPP

variable {d : ℕ} {κ : Rd d → ℝ}

/-- Translation invariance for strict inequalities of normalized crossings. -/
theorem w2_ratio_prob_translate (hκ : IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : DGZ.IsDyadicRealization κ P W H) (hd : 2 ≤ d)
    (ξ : ℝ) (n : ℕ) (c : Rd d) (r₁ r₂ t : ℝ) :
    P {ω | DGZ.acrossDist ξ (fun z => H n z ω) c r₁ r₂ /
      DGZ.aQ P H ξ n 2⁻¹ < t} =
      P {ω | DGZ.acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ /
        DGZ.aQ P H ξ n 2⁻¹ < t} := by
  have hmed : 0 < DGZ.aQ P H ξ n 2⁻¹ :=
    DGZ.tight_aQ_pos (by omega : 0 < d) hH ξ n (by norm_num) (by norm_num)
  have ha : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  have hmap := DGZ.map_acrossDist_translate_eq (hH.band n) (hH.band n)
    hH.whiteNoise hH.whiteNoise hκ ha ξ c 0 r₁ r₂
  simp only [add_zero] at hmap
  have hc : Measurable (fun ω => DGZ.acrossDist ξ (fun z => H n z ω) c r₁ r₂) :=
    DGZ.measurable_acrossDist (hH.band n).continuous (hH.band n).measurable ξ c r₁ r₂
  have hz : Measurable (fun ω => DGZ.acrossDist ξ (fun z => H n z ω) 0 r₁ r₂) :=
    DGZ.measurable_acrossDist (hH.band n).continuous (hH.band n).measurable ξ 0 r₁ r₂
  have hlt (u : ℝ) :
      P {ω | DGZ.acrossDist ξ (fun z => H n z ω) c r₁ r₂ < u} =
        P {ω | DGZ.acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ < u} := by
    have he := congrArg (fun Q : Measure ℝ => Q (Iio u)) hmap
    simpa [Measure.map_apply hc measurableSet_Iio,
      Measure.map_apply hz measurableSet_Iio, Set.preimage] using he
  calc
    P {ω | DGZ.acrossDist ξ (fun z => H n z ω) c r₁ r₂ /
        DGZ.aQ P H ξ n 2⁻¹ < t} =
      P {ω | DGZ.acrossDist ξ (fun z => H n z ω) c r₁ r₂ <
        t * DGZ.aQ P H ξ n 2⁻¹} := by
          congr 1; ext ω; exact div_lt_iff₀ hmed
    _ = P {ω | DGZ.acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ <
        t * DGZ.aQ P H ξ n 2⁻¹} := hlt _
    _ = P {ω | DGZ.acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ /
        DGZ.aQ P H ξ n 2⁻¹ < t} := by
          congr 1; ext ω; exact (div_lt_iff₀ hmed).symm

/-- Appendix A W2(a): inverse moments of normalized white-noise cubical shell crossings. -/
theorem wnInvCross {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) (hCr : CrudeLowerShape d κ)
    (hN : UNondegShape d κ) (hQ : UQuantCompShape d κ) :
    WNInvCrossShape d κ := by
  intro b μ hb hμ z r₁ r₂ hr₂ hr q hq
  obtain ⟨c, B, E, C, hc, hB, hqE, hC, htail⟩ :=
    w2_uniform_geom_tail hd hκ hCr hN hQ hb hμ hr₂ hr hq
  let r : ℝ := (2 : ℝ) ^ B
  let a : ℝ := E / B
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) hB
  have hqa : q < a := (lt_div_iff₀ hB).2 (by simpa only [mul_comm] using hqE)
  let M : ℝ := LQGMetric.DFGPS.momBd q a (C * r ^ a * c ^ (-a)) (max 1 c⁻¹)
  refine ⟨M, ?_⟩
  intro ξ hξ Ω _ P W H hH n
  haveI : IsProbabilityMeasure P := hH.whiteNoise.isProbabilityMeasure
  let Y : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal
    (DGZ.acrossDist ξ (fun w => H n w ω) z r₁ r₂ / DGZ.aQ P H ξ n 2⁻¹)
  have htailY : ∀ m : ℕ,
      P {ω | Y ω < ENNReal.ofReal (c * r ^ (-(m : ℝ)))} ≤
        ENNReal.ofReal (C * r ^ (-(a * m))) := by
    intro m
    have hpow₁ : r ^ (-(m : ℝ)) = (2 : ℝ) ^ (-(B * m)) := by
      dsimp [r]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    have hpow₂ : r ^ (-(a * m)) = (2 : ℝ) ^ (-(E * m)) := by
      dsimp [r, a]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      field_simp
    rw [hpow₁, hpow₂]
    have hthresh : 0 < c * (2 : ℝ) ^ (-(B * m)) := by positivity
    have hevent : {ω | Y ω < ENNReal.ofReal (c * (2 : ℝ) ^ (-(B * m)))} =
        {ω | DGZ.acrossDist ξ (fun w => H n w ω) z r₁ r₂ /
          DGZ.aQ P H ξ n 2⁻¹ < c * (2 : ℝ) ^ (-(B * m))} := by
      ext ω
      exact ENNReal.ofReal_lt_ofReal_iff hthresh
    rw [hevent, w2_ratio_prob_translate hκ hH hd ξ n z r₁ r₂]
    exact htail ξ hξ Ω P W H hH n m
  exact w2_inv_moment_of_geom_tail P Y hc hr hC hq hqa htailY

end HigherDimLQGContinuity
