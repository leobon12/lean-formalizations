import Mathlib
import MatedCRTHarmonic.Growth.ChainRates
import MatedCRTHarmonic.CellScaling.Model

/-!
# the area-growth bound: `μ_h(B_{R_{2^k}}(0)) ≤ 2^{(1+δ)k}` eventually, almost surely

By the area scaling law, `P(μ_h(B_{R_{2^k}}(0)) > 2^{(1+δ)k}) = P(μ_h(B_1(0)) > 2^{δk})`, which by
Markov's inequality and [16, Lemma A.3] is at most `E[μ_h(B_1(0))^p] 2^{-pδk}`, summable; Borel–Cantelli concludes.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellScaling

open MatedCRTHarmonic

/-- `b t < x` gives `t < b⁻¹ x` in `ℝ≥0∞` (with `b > 0`). -/
theorem ofReal_lt_ofReal_inv_mul {b t : ℝ} (hb : 0 < b) {x : ℝ≥0∞} (h : ENNReal.ofReal (b * t) < x) :
    ENNReal.ofReal t < ENNReal.ofReal b⁻¹ * x := by
  rcases le_or_gt t 0 with ht | ht
  · rw [ENNReal.ofReal_of_nonpos ht]
    exact ENNReal.mul_pos (by simpa using hb) (ne_of_gt (lt_of_le_of_lt zero_le h))
  rcases eq_or_ne x ⊤ with rfl | hx
  · rw [ENNReal.mul_top (by simpa using hb)]
    exact ENNReal.ofReal_lt_top
  · rw [← ENNReal.ofReal_toReal hx] at h ⊢
    have hlt : b * t < x.toReal := by
      by_contra hle
      push Not at hle
      exact absurd h (not_lt.2 (ENNReal.ofReal_le_ofReal hle))
    rw [← ENNReal.ofReal_mul (le_of_lt (inv_pos.2 hb))]
    refine (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt ht)).2 ?_
    rw [lt_inv_mul_iff₀ hb]
    exact hlt

/-- Markov's inequality in the `p`-th moment form for an `ℝ≥0∞`-valued variable. -/
theorem measure_lt_le_lintegral_rpow_div {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : Ω → ℝ≥0∞}
    (hf : AEMeasurable f P) {p : ℝ} (hp : 0 < p) {t : ℝ≥0∞} (ht : t ≠ 0) (ht' : t ≠ ⊤) :
    P {ω | t < f ω} ≤ (∫⁻ ω, f ω ^ p ∂P) / t ^ p := by
  have hfp : AEMeasurable (fun ω => f ω ^ p) P := hf.pow_const p
  have hmarkov := mul_meas_ge_le_lintegral₀ hfp (t ^ p)
  have hsub : {ω | t < f ω} ⊆ {ω | t ^ p ≤ f ω ^ p} := fun ω hω =>
    ENNReal.rpow_le_rpow (le_of_lt hω) (le_of_lt hp)
  have htp0 : t ^ p ≠ 0 := by
    intro h0
    rcases ENNReal.rpow_eq_zero_iff.1 h0 with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact ht h1
    · linarith
  have htpT : t ^ p ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (le_of_lt hp) ht'
  rw [ENNReal.le_div_iff_mul_le (Or.inl htp0) (Or.inl htpT)]
  calc P {ω | t < f ω} * t ^ p ≤ t ^ p * P {ω | t ^ p ≤ f ω ^ p} := by
        rw [mul_comm]; gcongr
    _ ≤ _ := hmarkov

/-- **the area-growth bound** (the cell-counting argument): for every `δ > 0`, almost surely
`μ_h(B_{R_{2^k}}(0)) ≤ 2^{(1+δ)k}` for all sufficiently large `k`. From `AreaScalingLaw` ([14, Prop 4.13(i)] +
[SW]) and `AreaBallMoment` ([16, Lemma A.3]) by Markov's inequality and Borel–Cantelli. -/
theorem ae_eventually_area_ball_le {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {M : MesoModel.MatedCRTUnitMesoModel γ}
    (D : ConeRealization M) (hscale : AreaScalingLaw D) (hmom : AreaBallMoment D) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂M.coupled.family.P, ∀ᶠ k : ℕ in atTop,
      D.area ω (ball 0 (D.scale ((2 : ℝ) ^ k) ω)) ≤ ENNReal.ofReal ((2 : ℝ) ^ ((1 + δ) * k)) := by
  set P := M.coupled.family.P
  -- the moment exponent
  have hγsq : 0 < 4 / γ ^ 2 - 1 := by
    have : γ ^ 2 < 4 := by nlinarith
    have h4 : 1 < 4 / γ ^ 2 := by rw [lt_div_iff₀ (by positivity)]; linarith
    linarith
  set p : ℝ := (4 / γ ^ 2 - 1) / 2 with hp
  have hp0 : 0 < p := by rw [hp]; linarith
  have hp1 : p < 4 / γ ^ 2 - 1 := by rw [hp]; linarith
  set C : ℝ≥0∞ := ∫⁻ ω, D.area ω (ball 0 1) ^ p ∂P with hC
  have hCfin : C ≠ ⊤ := ne_of_lt (hmom.2 p hp0 hp1)
  set Bad : ℕ → Set M.coupled.family.Ω := fun k =>
    {ω | ENNReal.ofReal ((2 : ℝ) ^ ((1 + δ) * k)) < D.area ω (ball 0 (D.scale ((2 : ℝ) ^ k) ω))}
  set r : ℝ := (2 : ℝ) ^ (-(p * δ)) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    rw [hr]
    calc (2 : ℝ) ^ (-(p * δ)) < (2 : ℝ) ^ (0 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by nlinarith)
      _ = 1 := by simp
  have hbound : ∀ k : ℕ, P (Bad k) ≤ ENNReal.ofReal (C.toReal * r ^ k) := by
    intro k
    set b : ℝ := (2 : ℝ) ^ k with hb
    have hbpos : 0 < b := by positivity
    set t : ℝ := (2 : ℝ) ^ (δ * k) with ht
    have htpos : 0 < t := by positivity
    have hsplit : (2 : ℝ) ^ ((1 + δ) * k) = b * t := by
      rw [hb, ht, ← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
      congr 1
      ring
    have hsub : Bad k ⊆ {ω | ENNReal.ofReal b⁻¹ * D.area ω (ball 0 (D.scale b ω)) ∈ Ioi (ENNReal.ofReal t)} := by
      intro ω hω
      change ENNReal.ofReal t < ENNReal.ofReal b⁻¹ * D.area ω (ball 0 (D.scale b ω))
      have hω' : ENNReal.ofReal (b * t) < D.area ω (ball 0 (D.scale b ω)) := by
        rw [← hsplit]; exact hω
      exact ofReal_lt_ofReal_inv_mul hbpos hω'
    have hlaw := hscale b hbpos (Ioi (ENNReal.ofReal t)) measurableSet_Ioi
    have hmark := measure_lt_le_lintegral_rpow_div hmom.1 hp0
      (t := ENNReal.ofReal t) (by simpa using htpos) ENNReal.ofReal_ne_top
    have htp : ENNReal.ofReal t ^ p = ENNReal.ofReal (t ^ p) :=
      ENNReal.ofReal_rpow_of_nonneg (le_of_lt htpos) (le_of_lt hp0)
    have hrk : r ^ k = (t ^ p)⁻¹ := by
      rw [hr, ht, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num),
        ← Real.rpow_neg (by norm_num)]
      congr 1
      ring
    calc P (Bad k) ≤ P {ω | ENNReal.ofReal b⁻¹ * D.area ω (ball 0 (D.scale b ω)) ∈ Ioi (ENNReal.ofReal t)} :=
          measure_mono hsub
      _ = P {ω | D.area ω (ball 0 1) ∈ Ioi (ENNReal.ofReal t)} := hlaw
      _ ≤ C / ENNReal.ofReal t ^ p := hmark
      _ = ENNReal.ofReal (C.toReal * r ^ k) := by
          rw [htp, hrk, ← ENNReal.ofReal_toReal hCfin, ENNReal.ofReal_toReal hCfin,
            ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hCfin,
            ENNReal.ofReal_inv_of_pos (by positivity), div_eq_mul_inv]
  have hsum : Summable (fun k : ℕ => C.toReal * r ^ k) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hae := Growth.ae_eventually_notMem_of_real_summable_bound P Bad (fun k => C.toReal * r ^ k)
    (fun k => mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hr0 k)) hsum hbound
  filter_upwards [hae] with ω hω
  filter_upwards [hω] with k hk
  simp only [Bad, mem_ofPred_eq, not_lt] at hk
  exact hk

end MatedCRTHarmonic.CellScaling
