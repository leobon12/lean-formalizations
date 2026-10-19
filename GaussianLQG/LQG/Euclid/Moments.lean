import GaussianLQG.LQG.Localization.Tail
import GaussianLQG.LQG.Geodesics
import GaussianLQG.LQG.Euclid.Basic

/-!
# Moments of the majorant of Lemma `lem:energy-approx`

For `[0, ∞]`-valued `B, Θ, 𝖤` and constants `c₁, Λ, ε₀` let
`Y = c₁ (1 + B)^{1/2} 𝖤^{1/12}` on the good event `{𝖤 ≤ ε₀}` and `Y = 2(Θ + Λ)` off it
(`energyY`). `exists_lintegral_energyY_le`: if `E[B^p] ≤ C_B`, `E[Θ^{2p}] ≤ C_Θ` and
`E[𝖤^p] ≤ C_E ξ^{p/2}` (`0 < ξ ≤ 1`), then `E[Y^p] ≤ C ξ^{p/24}` with `C` depending only on the
constants (blueprint Lemma `lem:energy-approx`, last display):
* on the good event, Cauchy–Schwarz gives
  `E[(1+B)^{p/2} 𝖤^{p/12}] ≤ E[(1+B)^p]^{1/2} E[𝖤^{p/6}]^{1/2}` and Jensen gives
  `E[𝖤^{p/6}] ≤ E[𝖤^p]^{1/6} ≤ C ξ^{p/12}`;
* off it, Cauchy–Schwarz and Markov's inequality give
  `E[(2(Θ+Λ))^p 1_{𝖤 > ε₀}] ≤ E[(2(Θ+Λ))^{2p}]^{1/2} (ε₀^{-p} E[𝖤^p])^{1/2} ≤ C ξ^{p/4}`,
  and `ξ^{p/4} ≤ ξ^{p/24}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GaussianLQG

/-- The majorant `Y` of Lemma `lem:energy-approx`: `c₁ (1 + B)^{1/2} 𝖤^{1/12}` if `𝖤 ≤ ε₀`,
`2(Θ + Λ)` otherwise. -/
def energyY (c1 Λ ε0 : ℝ) (B Θ E : ℝ≥0∞) : ℝ≥0∞ :=
  if E ≤ ENNReal.ofReal ε0 then ENNReal.ofReal c1 * (1 + B) ^ (1 / 2 : ℝ) * E ^ (1 / 12 : ℝ)
  else 2 * (Θ + ENNReal.ofReal Λ)

theorem measurable_energyY {Ω : Type*} [MeasurableSpace Ω] (c1 Λ ε0 : ℝ)
    {B Θ E : Ω → ℝ≥0∞} (hB : Measurable B) (hΘ : Measurable Θ) (hE : Measurable E) :
    Measurable fun ω => energyY c1 Λ ε0 (B ω) (Θ ω) (E ω) := by
  unfold energyY
  refine Measurable.ite (measurableSet_le hE measurable_const) ?_ ?_
  · exact (measurable_const.mul ((measurable_const.add hB).pow_const _)).mul (hE.pow_const _)
  · exact measurable_const.mul (hΘ.add measurable_const)

/-- **Jensen** on a probability space: `E[f^a] ≤ E[f^q]^{a/q}` for `0 < a ≤ q`. -/
theorem lintegral_rpow_le_rpow_lintegral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ≥0∞} (hf : AEMeasurable f μ) {a q : ℝ} (ha : 0 < a)
    (haq : a ≤ q) : ∫⁻ ω, f ω ^ a ∂μ ≤ (∫⁻ ω, f ω ^ q ∂μ) ^ (a / q) := by
  have hq : 0 < q := lt_of_lt_of_le ha haq
  have h := eLpNorm_le_eLpNorm_of_exponent_le (μ := μ) (ENNReal.ofReal_le_ofReal haq)
    hf.aestronglyMeasurable
  rw [eLpNorm_ofReal_eq ha, eLpNorm_ofReal_eq hq] at h
  simp_rw [enorm_eq_self] at h
  calc ∫⁻ ω, f ω ^ a ∂μ = ((∫⁻ ω, f ω ^ a ∂μ) ^ (1 / a)) ^ a := by
        rw [← ENNReal.rpow_mul, one_div_mul_cancel ha.ne', ENNReal.rpow_one]
    _ ≤ ((∫⁻ ω, f ω ^ q ∂μ) ^ (1 / q)) ^ a := ENNReal.rpow_le_rpow h ha.le
    _ = (∫⁻ ω, f ω ^ q ∂μ) ^ (a / q) := by
        rw [← ENNReal.rpow_mul]
        congr 1
        ring

/-- `ofReal (C x^e)^s ≤ ofReal C ^ s · ofReal (x^{e s})` for `x ≥ 0`, `s ≥ 0`. -/
theorem ofReal_mul_rpow_rpow_le (C : ℝ) {x e s : ℝ} (hx : 0 ≤ x) (hs : 0 ≤ s) :
    ENNReal.ofReal (C * x ^ e) ^ s ≤ ENNReal.ofReal C ^ s * ENNReal.ofReal (x ^ (e * s)) := by
  rw [ENNReal.ofReal_mul' (Real.rpow_nonneg hx _), ENNReal.mul_rpow_of_nonneg _ _ hs,
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hx _) hs, ← Real.rpow_mul hx]

/-- **Moments of the majorant `Y`** (blueprint Lemma `lem:energy-approx`): if `E[B^p] ≤ C_B`,
`E[Θ^{2p}] ≤ C_Θ` and `E[𝖤^p] ≤ C_E ξ^{p/2}` with `0 < ξ ≤ 1`, then `E[Y^p] ≤ C ξ^{p/24}`, where `C`
depends only on `p, c₁, Λ, ε₀, C_E, C_B, C_Θ`. -/
theorem exists_lintegral_energyY_le {p : ℝ} (hp : 1 ≤ p) (c1 Λ ε0 CE : ℝ) (hε0 : 0 < ε0)
    {CB CΘ : ℝ≥0∞} (hCB : CB ≠ ⊤) (hCΘ : CΘ ≠ ⊤) :
    ∃ C : ℝ, ∀ {B Θ E : Coord → ℝ≥0∞} {ξ : ℝ}, Measurable B → Measurable Θ → Measurable E →
      0 < ξ → ξ ≤ 1 → ∫⁻ ω, B ω ^ p ∂stdP ≤ CB → ∫⁻ ω, Θ ω ^ (2 * p) ∂stdP ≤ CΘ →
      ∫⁻ ω, E ω ^ p ∂stdP ≤ ENNReal.ofReal (CE * ξ ^ (p / 2)) →
      ∫⁻ ω, energyY c1 Λ ε0 (B ω) (Θ ω) (E ω) ^ p ∂stdP ≤ ENNReal.ofReal (C * ξ ^ (p / 24)) := by
  have hp0 : 0 < p := by linarith
  set cE : ℝ≥0∞ := ENNReal.ofReal CE with hcE_def
  set K1 : ℝ≥0∞ := ENNReal.ofReal c1 ^ p * (2 ^ (p - 1) * (1 + CB)) ^ (1 / 2 : ℝ) *
    cE ^ (1 / 12 : ℝ) with hK1_def
  set K2 : ℝ≥0∞ := (2 ^ (2 * p) * (2 ^ (2 * p - 1) * (CΘ + ENNReal.ofReal Λ ^ (2 * p)))) ^
      (1 / 2 : ℝ) * ((ENNReal.ofReal ε0 ^ p)⁻¹ * cE) ^ (1 / 2 : ℝ) with hK2_def
  have hε0p : ENNReal.ofReal ε0 ^ p ≠ 0 := by
    rw [ne_eq, ENNReal.rpow_eq_zero_iff]
    push Not
    exact ⟨fun h => absurd h (ENNReal.ofReal_pos.2 hε0).ne',
      fun h => absurd h ENNReal.ofReal_ne_top⟩
  have hK1 : K1 ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp0.le
      ENNReal.ofReal_ne_top) (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
        (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top)
          (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hCB⟩))))
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
  have hK2 : K2 ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top)
        (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top)
          (ENNReal.add_ne_top.2 ⟨hCΘ, ENNReal.rpow_ne_top_of_nonneg (by linarith)
            ENNReal.ofReal_ne_top⟩))))
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
        (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hε0p) ENNReal.ofReal_ne_top))
  refine ⟨(K1 + K2).toReal, fun {B Θ E ξ} hB hΘ hE hξ hξ1 hBm hΘm hEm => ?_⟩
  set G : Set Coord := {ω | E ω ≤ ENNReal.ofReal ε0} with hG_def
  have hGm : MeasurableSet G := measurableSet_le hE measurable_const
  set YG : Coord → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal c1 * (1 + B ω) ^ (1 / 2 : ℝ) * E ω ^ (1 / 12 : ℝ) with hYG_def
  set Yoff : Coord → ℝ≥0∞ := fun ω => 2 * (Θ ω + ENNReal.ofReal Λ) with hYoff_def
  have hYGm : Measurable YG :=
    (measurable_const.mul ((measurable_const.add hB).pow_const _)).mul (hE.pow_const _)
  have hYoffm : Measurable Yoff := measurable_const.mul (hΘ.add measurable_const)
  -- (i) the pointwise split
  have hsplit : ∀ ω, energyY c1 Λ ε0 (B ω) (Θ ω) (E ω) ^ p ≤
      YG ω ^ p + Yoff ω ^ p * Gᶜ.indicator 1 ω := by
    intro ω
    unfold energyY
    split_ifs with h
    · exact le_self_add
    · rw [indicator_of_mem (show ω ∈ Gᶜ from h), Pi.one_apply, mul_one]
      exact le_add_self
  -- (ii) the good event: Cauchy–Schwarz and Jensen
  have hYGp : ∀ ω, YG ω ^ p = ENNReal.ofReal c1 ^ p *
      ((1 + B ω) ^ (p / 2) * (E ω ^ (1 / 6 : ℝ)) ^ (p / 2)) := by
    intro ω
    simp only [hYG_def]
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_assoc]
    congr 3 <;> ring
  have h1B : ∫⁻ ω, (1 + B ω) ^ p ∂stdP ≤ 2 ^ (p - 1) * (1 + CB) := by
    calc ∫⁻ ω, (1 + B ω) ^ p ∂stdP ≤ ∫⁻ ω, 2 ^ (p - 1) * (1 + B ω ^ p) ∂stdP := by
          refine lintegral_mono fun ω => ?_
          have := ENNReal.rpow_add_le_mul_rpow_add_rpow 1 (B ω) hp
          rwa [ENNReal.one_rpow] at this
      _ = 2 ^ (p - 1) * (1 + ∫⁻ ω, B ω ^ p ∂stdP) := by
          have hm : Measurable fun ω => (1 : ℝ≥0∞) + B ω ^ p :=
            measurable_const.add (hB.pow_const p)
          have hm1 : Measurable fun _ : Coord => (1 : ℝ≥0∞) := measurable_const
          rw [lintegral_const_mul _ hm, lintegral_add_left hm1, lintegral_const, measure_univ,
            mul_one]
      _ ≤ 2 ^ (p - 1) * (1 + CB) := by gcongr
  have hE6 : ∫⁻ ω, (E ω ^ (1 / 6 : ℝ)) ^ p ∂stdP ≤
      cE ^ (1 / 6 : ℝ) * ENNReal.ofReal (ξ ^ (p / 2 * (1 / 6))) := by
    have e : ∀ ω, (E ω ^ (1 / 6 : ℝ)) ^ p = E ω ^ (p / 6) := fun ω => by
      rw [← ENNReal.rpow_mul]
      congr 1
      ring
    simp_rw [e]
    calc ∫⁻ ω, E ω ^ (p / 6) ∂stdP ≤ (∫⁻ ω, E ω ^ p ∂stdP) ^ (p / 6 / p) :=
          lintegral_rpow_le_rpow_lintegral hE.aemeasurable (by positivity) (by linarith)
      _ = (∫⁻ ω, E ω ^ p ∂stdP) ^ (1 / 6 : ℝ) := by
          congr 1
          field_simp
      _ ≤ ENNReal.ofReal (CE * ξ ^ (p / 2)) ^ (1 / 6 : ℝ) :=
          ENNReal.rpow_le_rpow hEm (by norm_num)
      _ ≤ cE ^ (1 / 6 : ℝ) * ENNReal.ofReal (ξ ^ (p / 2 * (1 / 6))) :=
          ofReal_mul_rpow_rpow_le CE hξ.le (by norm_num)
  have hfirst : ∫⁻ ω, YG ω ^ p ∂stdP ≤ K1 * ENNReal.ofReal (ξ ^ (p / 24)) := by
    simp_rw [hYGp]
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)]
    have hm1 : Measurable fun ω => (1 : ℝ≥0∞) + B ω := measurable_const.add hB
    have hm2 : Measurable fun ω => E ω ^ (1 / 6 : ℝ) := hE.pow_const _
    have hCS := lintegral_rpow_mul_rpow_le (μ := stdP) hm1.aemeasurable hm2.aemeasurable
      (q := p / 2)
    rw [show 2 * (p / 2) = p by ring] at hCS
    calc ENNReal.ofReal c1 ^ p *
          ∫⁻ ω, (1 + B ω) ^ (p / 2) * (E ω ^ (1 / 6 : ℝ)) ^ (p / 2) ∂stdP
        ≤ ENNReal.ofReal c1 ^ p * ((∫⁻ ω, (1 + B ω) ^ p ∂stdP) ^ (1 / 2 : ℝ) *
            (∫⁻ ω, (E ω ^ (1 / 6 : ℝ)) ^ p ∂stdP) ^ (1 / 2 : ℝ)) := by gcongr
      _ ≤ ENNReal.ofReal c1 ^ p * ((2 ^ (p - 1) * (1 + CB)) ^ (1 / 2 : ℝ) *
            (cE ^ (1 / 6 : ℝ) * ENNReal.ofReal (ξ ^ (p / 2 * (1 / 6)))) ^ (1 / 2 : ℝ)) := by
          gcongr
      _ = K1 * ENNReal.ofReal (ξ ^ (p / 24)) := by
          rw [ENNReal.mul_rpow_of_nonneg (cE ^ (1 / 6 : ℝ))
              (ENNReal.ofReal (ξ ^ (p / 2 * (1 / 6)))) (by norm_num : (0 : ℝ) ≤ 1 / 2),
            ← ENNReal.rpow_mul,
            ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hξ.le _) (by norm_num),
            ← Real.rpow_mul hξ.le, hK1_def]
          rw [show p / 2 * (1 / 6) * (1 / 2) = p / 24 by ring,
            show (1 / 6 : ℝ) * (1 / 2) = 1 / 12 by norm_num]
          ring
  -- (iii) off the good event: Cauchy–Schwarz and Markov
  have hoff2 : ∫⁻ ω, (Yoff ω ^ p) ^ (2 : ℝ) ∂stdP ≤
      2 ^ (2 * p) * (2 ^ (2 * p - 1) * (CΘ + ENNReal.ofReal Λ ^ (2 * p))) := by
    have e : ∀ ω, (Yoff ω ^ p) ^ (2 : ℝ) = 2 ^ (2 * p) * (Θ ω + ENNReal.ofReal Λ) ^ (2 * p) :=
      fun ω => by
        simp only [hYoff_def]
        rw [← ENNReal.rpow_mul, mul_comm p 2, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
    simp_rw [e]
    have hm : Measurable fun ω => (Θ ω + ENNReal.ofReal Λ) ^ (2 * p) :=
      (hΘ.add measurable_const).pow_const _
    rw [lintegral_const_mul _ hm]
    gcongr
    calc ∫⁻ ω, (Θ ω + ENNReal.ofReal Λ) ^ (2 * p) ∂stdP
        ≤ ∫⁻ ω, 2 ^ (2 * p - 1) * (Θ ω ^ (2 * p) + ENNReal.ofReal Λ ^ (2 * p)) ∂stdP :=
          lintegral_mono fun ω => ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ (by linarith)
      _ = 2 ^ (2 * p - 1) * (∫⁻ ω, Θ ω ^ (2 * p) ∂stdP + ENNReal.ofReal Λ ^ (2 * p)) := by
          have hm : Measurable fun ω => Θ ω ^ (2 * p) + ENNReal.ofReal Λ ^ (2 * p) :=
            (hΘ.pow_const _).add measurable_const
          have hm1 : Measurable fun ω => Θ ω ^ (2 * p) := hΘ.pow_const _
          rw [lintegral_const_mul _ hm, lintegral_add_left hm1, lintegral_const, measure_univ,
            mul_one]
      _ ≤ 2 ^ (2 * p - 1) * (CΘ + ENNReal.ofReal Λ ^ (2 * p)) := by gcongr
  have hGc : stdP Gᶜ ≤ (ENNReal.ofReal ε0 ^ p)⁻¹ * cE * ENNReal.ofReal (ξ ^ (p / 2)) := by
    have hsub : Gᶜ ⊆ {ω | ENNReal.ofReal ε0 ≤ E ω} := fun ω hω =>
      (not_le.1 (show ¬ E ω ≤ ENNReal.ofReal ε0 from hω)).le
    calc stdP Gᶜ ≤ stdP {ω | ENNReal.ofReal ε0 ≤ E ω} := measure_mono hsub
      _ ≤ (ENNReal.ofReal ε0 ^ p)⁻¹ * ∫⁻ ω, E ω ^ p ∂stdP :=
          measure_ge_le_inv_rpow_mul_lintegral_rpow hE.aemeasurable hp0
            (ENNReal.ofReal_pos.2 hε0).ne' ENNReal.ofReal_ne_top
      _ ≤ (ENNReal.ofReal ε0 ^ p)⁻¹ * ENNReal.ofReal (CE * ξ ^ (p / 2)) := by gcongr
      _ ≤ (ENNReal.ofReal ε0 ^ p)⁻¹ * cE * ENNReal.ofReal (ξ ^ (p / 2)) := by
          rw [mul_assoc]
          gcongr
          rw [hcE_def, ← ENNReal.ofReal_mul' (Real.rpow_nonneg hξ.le _)]
  have hsecond : ∫⁻ ω, Yoff ω ^ p * Gᶜ.indicator 1 ω ∂stdP ≤
      K2 * ENNReal.ofReal (ξ ^ (p / 24)) := by
    have hCS := lintegral_mul_indicator_one_le (μ := stdP) (hYoffm.pow_const p).aemeasurable
      hGm.compl
    have hξp : (ξ ^ (p / 2)) ^ (1 / 2 : ℝ) ≤ ξ ^ (p / 24) := by
      rw [← Real.rpow_mul hξ.le]
      exact Real.rpow_le_rpow_of_exponent_ge hξ hξ1 (by linarith)
    calc ∫⁻ ω, Yoff ω ^ p * Gᶜ.indicator 1 ω ∂stdP
        ≤ (∫⁻ ω, (Yoff ω ^ p) ^ (2 : ℝ) ∂stdP) ^ (1 / 2 : ℝ) * stdP Gᶜ ^ (1 / 2 : ℝ) := hCS
      _ ≤ (2 ^ (2 * p) * (2 ^ (2 * p - 1) * (CΘ + ENNReal.ofReal Λ ^ (2 * p)))) ^ (1 / 2 : ℝ) *
            ((ENNReal.ofReal ε0 ^ p)⁻¹ * cE * ENNReal.ofReal (ξ ^ (p / 2))) ^ (1 / 2 : ℝ) := by
          gcongr
      _ = K2 * ENNReal.ofReal ((ξ ^ (p / 2)) ^ (1 / 2 : ℝ)) := by
          rw [ENNReal.mul_rpow_of_nonneg ((ENNReal.ofReal ε0 ^ p)⁻¹ * cE)
              (ENNReal.ofReal (ξ ^ (p / 2))) (by norm_num : (0 : ℝ) ≤ 1 / 2),
            ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hξ.le _) (by norm_num), hK2_def]
          ring
      _ ≤ K2 * ENNReal.ofReal (ξ ^ (p / 24)) := by
          gcongr
  -- (iv) conclusion
  calc ∫⁻ ω, energyY c1 Λ ε0 (B ω) (Θ ω) (E ω) ^ p ∂stdP
      ≤ ∫⁻ ω, (YG ω ^ p + Yoff ω ^ p * Gᶜ.indicator 1 ω) ∂stdP := lintegral_mono hsplit
    _ = ∫⁻ ω, YG ω ^ p ∂stdP + ∫⁻ ω, Yoff ω ^ p * Gᶜ.indicator 1 ω ∂stdP :=
        lintegral_add_left (hYGm.pow_const p) _
    _ ≤ K1 * ENNReal.ofReal (ξ ^ (p / 24)) + K2 * ENNReal.ofReal (ξ ^ (p / 24)) :=
        add_le_add hfirst hsecond
    _ = ENNReal.ofReal ((K1 + K2).toReal * ξ ^ (p / 24)) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal (ENNReal.add_ne_top.2 ⟨hK1, hK2⟩), add_mul]

end GaussianLQG
