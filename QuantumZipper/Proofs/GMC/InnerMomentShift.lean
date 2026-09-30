import QuantumZipper.Proofs.GMC.InnerMomentReduce

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# GMC-INNERMOM (3): pathwise effect of the Cameron–Martin shift on the inner mass

For the Palm inequality (`PalmRootedStmt`, file `InnerMomentPalm`): after the Cameron–Martin
tilt by `e^{(γ/2) Y_k(x)}`, the inner process `y` is shifted by
`s(q) = (γ/2) Cov(Y_q, Y_k(x))`. Here we show, pathwise on the event where the dyadic roundings
of the field converge, that the regularized averages of the rebuilt shifted sample are those of
`y` plus `(γ/2) g(u)`, `g(u) = Cov(Y_k(u), Y_k(x))` (continuity of `g` in the centre:
`kernelCov_fc_eq_integral` and continuity of circle averages of continuous functions), and that
`g(u) ≤ 2 log δ − 2 log max(|u − x|, 2·2^{-k}) + 2 log 2` (kernel identities K1, K3 and the
bound `fcPot ≤ −2 log r`). Consequently (`massFun_shift_le`)
`W^{shift} ≤ 2^{γ²/2} ∫ (δ/max(|x−u|, 2·2^{-k}))^{γ²/2} W(du)`.
Own write-up of the standard covariance estimate for circle averages.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Real Set Topology
open scoped NNReal ENNReal

namespace QuantumZipper
namespace GMCMoments

open FracMom BdryExist GaussTK KernelId

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

theorem continuous_integral_circleUnif {f : ℂ → ℝ} (hf : Continuous f) (r : ℝ) :
    Continuous fun z : ℂ => ∫ y, f y ∂(circleUnif z r) := by
  have e : (fun z : ℂ => ∫ y, f y ∂(circleUnif z r)) = fun z =>
      (ENNReal.ofReal (2 * π))⁻¹.toReal * ∫ θ in Icc 0 (2 * π), f (circleMap z r θ) := by
    funext z
    rw [circleUnif, integral_smul_measure, integral_map (measurable_circleMap z r).aemeasurable
      hf.aestronglyMeasurable, Measure.restrict_congr_set Ico_ae_eq_Icc, smul_eq_mul]
  rw [e]
  refine continuous_const.mul ?_
  have hc : Continuous (fun p : ℂ × ℝ => circleMap p.1 r p.2) := by
    simp only [circleMap]; fun_prop
  exact continuous_parametric_integral_of_continuous (f := fun z θ => f (circleMap z r θ))
    (hf.comp hc) isCompact_Icc

/-- `g(μ) = Cov(Y_μ, Y_k(x))` as a function of the inner circle `μ`. -/
def covG (t δ x r : ℝ) (μ : Measure ℂ) : ℝ :=
  kernelCov2 neumannH (μ, foldedCircle (t : ℂ) δ) (foldedCircle (x : ℂ) r, foldedCircle (t : ℂ) δ)

theorem continuous_covG_fc {t δ x r ρ : ℝ} (hδ : 0 < δ) (hr : 0 < r) :
    Continuous fun z : ℂ => covG t δ x r (foldedCircle z ρ) := by
  have e : (fun z : ℂ => covG t δ x r (foldedCircle z ρ)) = fun z =>
      (∫ y, fcPot r x y ∂(circleUnif z ρ)) - (∫ y, fcPot δ t y ∂(circleUnif z ρ)) -
        kernelCov neumannH (foldedCircle (t : ℂ) δ) (foldedCircle (x : ℂ) r) +
        kernelCov neumannH (foldedCircle (t : ℂ) δ) (foldedCircle (t : ℂ) δ) := by
    funext z
    simp only [covG, kernelCov2]
    rw [kernelCov_fc_eq_integral _ _ _ hr, kernelCov_fc_eq_integral _ _ _ hδ]
  rw [e]
  exact (((continuous_integral_circleUnif (continuous_fcPot hr _) ρ).sub
    (continuous_integral_circleUnif (continuous_fcPot hδ _) ρ)).sub continuous_const).add
      continuous_const

theorem kernelCov_fc_le_neg_two_log {z : ℂ} {x r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (ρ : ℝ) :
    kernelCov neumannH (foldedCircle z ρ) (foldedCircle (x : ℂ) r) ≤ -2 * log r := by
  rw [kernelCov_fc_eq_integral _ _ _ hr]
  have hb : ∀ y, fcPot r x y ≤ -2 * log r := by
    intro y
    unfold fcPot
    have h1 := log_le_log hr (le_max_left r ‖(x : ℂ) - y‖)
    have h2 := log_le_log hr (le_max_left r ‖(x : ℂ) - (starRingEnd ℂ) y‖)
    linarith
  by_cases hi : Integrable (fcPot r x) (circleUnif z ρ)
  · calc ∫ y, fcPot r x y ∂(circleUnif z ρ) ≤ ∫ _y, -2 * log r ∂(circleUnif z ρ) :=
          integral_mono hi (integrable_const _) hb
      _ = -2 * log r := by simp
  · rw [integral_undef hi]
    have := log_nonpos hr.le hr1
    linarith

/-- **Covariance bound.** For `u, x` with `|u − t| + r ≤ δ`, `|x − t| + r ≤ δ`:
`Cov(Y_r(u), Y_r(x)) ≤ 2 log δ − 2 log max(|u − x|, 2r) + 2 log 2`. -/
theorem covG_fc_le {t δ x u r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hu : |u - t| + r ≤ δ)
    (hx : |x - t| + r ≤ δ) :
    covG t δ x r (foldedCircle (u : ℂ) r) ≤
      2 * log δ - 2 * log (max |u - x| (2 * r)) + 2 * log 2 := by
  have hδ : 0 < δ := by linarith [abs_nonneg (u - t)]
  simp only [covG, kernelCov2]
  rw [kernelCov_fc_real_nested' hr hu, kernelCov_fc_real_nested hr hx,
    kernelCov_fc_real_sameCenter hδ hδ, max_self]
  have hK : kernelCov neumannH (foldedCircle (u : ℂ) r) (foldedCircle (x : ℂ) r) ≤
      -2 * log (max |u - x| (2 * r)) + 2 * log 2 := by
    rcases le_or_gt (2 * r) |u - x| with h | h
    · rw [max_eq_left h, kernelCov_fc_real_separated hr hr (by linarith)]
      have := log_nonneg one_le_two
      linarith
    · rw [max_eq_right h.le, log_mul two_ne_zero hr.ne']
      have := kernelCov_fc_le_neg_two_log (z := (u : ℂ)) (x := x) hr hr1 r
      linarith
  linarith

theorem tendsto_dyadicRoundC_ofReal (u : ℝ) :
    Tendsto (fun n => dyadicRoundC n (u : ℂ)) atTop (𝓝 (u : ℂ)) := by
  have h0 : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hR : Tendsto (fun n => dyadicRound n u) atTop (𝓝 u) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h0
    rw [Real.norm_eq_abs, one_div_pow]
    exact CircleCont.abs_dyadicRound_sub_le n u
  simp_rw [dyadicRoundC_ofReal]
  exact (Complex.continuous_ofReal.tendsto u).comp hR

/-- Eventually the dyadic circles at `u` are inner circles. -/
theorem eventually_exists_innerMeas {t δ u : ℝ} {k : ℕ} (hδ : 0 < δ)
    (hu : |u - t| + radius k < δ) :
    ∀ᶠ j : ℕ in atTop, ∃ q : InnerQ,
      innerMeas t δ q = foldedCircle (dyadicRoundC j (u : ℂ)) (radius k) := by
  have hr := radius_pos k
  have hε : 0 < δ - |u - t| - radius k := by linarith
  have hev : ∀ᶠ j : ℕ in atTop, (1 / 2 : ℝ) ^ j < δ - |u - t| - radius k :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)).eventually
      (gt_mem_nhds hε)
  filter_upwards [hev] with j hj
  set d := dyadicRound j u with hd
  have hds : |d - u| ≤ 1 / 2 ^ j := CircleCont.abs_dyadicRound_sub_le j u
  rw [one_div_pow] at hj
  have hdt : |d - t| ≤ |d - u| + |u - t| := by
    have := abs_add_le (d - u) (u - t); rwa [sub_add_sub_cancel] at this
  have hq : 0 < radius k / δ ∧ |(d - t) / δ| + radius k / δ ≤ 1 := by
    refine ⟨div_pos hr hδ, ?_⟩
    rw [abs_div, abs_of_pos hδ, ← add_div, div_le_one hδ]
    linarith
  refine ⟨⟨((d - t) / δ, radius k / δ), hq⟩, ?_⟩
  simp only [innerMeas, dyadicRoundC_ofReal, ← hd]
  congr 1
  · congr 1; field_simp; ring
  · field_simp

theorem innerRebuild_add (t δ : ℝ) (y s : InnerQ → ℝ) (μ : Measure ℂ) :
    innerRebuild t δ (y + s) μ = innerRebuild t δ y μ + innerRebuild t δ s μ := by
  unfold innerRebuild
  split_ifs <;> simp

/-- **Pathwise shift of the regularized averages.** -/
theorem avgReg_innerRebuild_shift {t δ x u : ℝ} {k : ℕ} (hδ : 0 < δ)
    (hu : |u - t| + radius k < δ) {γ : ℝ} {s : InnerQ → ℝ}
    (hs : ∀ j : InnerQ, s j = γ / 2 * covG t δ x (radius k) (innerMeas t δ j)) {ω : Ω}
    (hlim : Tendsto (fun j => X ω (foldedCircle (dyadicRoundC j (u : ℂ)) (radius k)))
      atTop (𝓝 (avgReg (X ω) k (u : ℂ)))) :
    avgReg (innerRebuild t δ (innerProc X t δ ω + s)) k (u : ℂ) =
      avgReg (innerSample X t δ ω) k (u : ℂ) +
        γ / 2 * covG t δ x (radius k) (foldedCircle (u : ℂ) (radius k)) := by
  have hr := radius_pos k
  have hev := eventually_exists_innerMeas (u := u) hδ hu
  -- the `y` part
  have hY : Tendsto (fun j => innerSample X t δ ω (foldedCircle (dyadicRoundC j (u : ℂ))
      (radius k))) atTop (𝓝 (avgReg (innerSample X t δ ω) k (u : ℂ))) := by
    rw [avgReg_innerSample_eq hδ hu hlim]
    refine (hlim.sub_const _).congr' ?_
    filter_upwards [hev] with j ⟨q, hq⟩
    rw [← hq, innerSample_apply]
  -- the shift part
  have hS : Tendsto (fun j => innerRebuild t δ s (foldedCircle (dyadicRoundC j (u : ℂ))
      (radius k))) atTop (𝓝 (γ / 2 * covG t δ x (radius k) (foldedCircle (u : ℂ) (radius k)))) := by
    have hc : Tendsto (fun j => γ / 2 * covG t δ x (radius k)
        (foldedCircle (dyadicRoundC j (u : ℂ)) (radius k))) atTop
        (𝓝 (γ / 2 * covG t δ x (radius k) (foldedCircle (u : ℂ) (radius k)))) :=
      (((continuous_covG_fc (ρ := radius k) (x := x) (t := t) hδ hr).tendsto _).comp
        (tendsto_dyadicRoundC_ofReal u)).const_mul _
    refine hc.congr' ?_
    filter_upwards [hev] with j hj
    have hj' := hj
    obtain ⟨q, hq⟩ := hj'
    simp only [innerRebuild, dif_pos hj, hs]
    rw [hj.choose_spec]
  have hsum := hY.add hS
  refine Eq.trans ?_ hsum.limUnder_eq
  unfold avgReg
  congr 1
  funext j
  rw [innerRebuild_add]
  rfl

end GMCMoments
end QuantumZipper
