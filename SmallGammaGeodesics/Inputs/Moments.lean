import GaussianLQG.LQG.Localization
import GaussianLQG.LQG.Scaling
import SmallGammaGeodesics.Core.PathFunctionals

/-!
# Lemma 2.1′: fixed moments, localization and the exponential energy moment (source §2.2)

Source: `source/small-parameter-lqg-geodesics.pdf`, Lemma 2.1 and (2.2)–(2.7). Kavvadias [5] is removed
from the dependency closure (ruling G6): Lemma 2.1 is replaced by Lemma 2.1′ (planning audit GA5,
"Details for later use" (a1); GA1 (c3) and §3; blueprint Lemma `lem:moments`), proved on an arbitrary
GaussianLQG coordinate `Setup` from its certified uniform moments (S6), the scaling lemmas and the
localization lemma `lem:T-B`. The metric is normalized by `e^{-b_γ}` with `b_γ = E log D(0,1)`
(`Setup.b`, ruling G8).

Write `K₁ = B̄₁(0)`, `T = S.locT γ K₁`, `B = S.locB γ K₁ 1`, `Θ = S.locTheta γ K₁ 1` and
`D̃ = e^{-b_γ} D`. The results are:

* (i) `exists_D01_moments`: for every `p ≥ 1`, `E[D̃(0,1)^p]` and `E[D̃(0,1)^{-p}]` are bounded for small
  `γ` (from `I_γ(K₁,1) ≤ D(0,1) ≤ A_γ(K₁)`, (S6) and `|b_γ| ≤ C`);
* (ii) `exists_locMoments_closedBall_one`: for every `p ≥ 1`, `E[T^p]`, `E[B^p]`, `E[Θ^p]` are bounded for
  small `γ`; `ae_localization_zero_one`: for small `γ`, a.s. `T, B, Θ < ∞`, `T ≥ 4`, `B ≥ 1`, and every
  constant-speed geodesic `η` from `0` to `1` satisfies `η([0,1]) ⊆ B_T(0)`, `M(η) ≤ T`,
  `ν_η(B_r(u)) ≤ B r^{1/2}` (`r ∈ (0,1]`), and `ν_η` is regular with `ℰ(ν_η, ν_η) ≤ Θ²`;
* (iii) source (2.3): `exp_locTheta_sq_le` and `expEnergyMoment` (ported verbatim from GA1's compiled
  probe `GA1Probe2.lean`): `E exp(Θ²/4) ≤ C` for small `γ`, and a.s. every geodesic from `0` to `1` has
  `ℰ(ν_η, ν_η) ≤ Θ²`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics

open GaussianLQG LQGMetric LQGMetric.Blueprint

/-! ## A Lebesgue-integral helper -/

/-- If `f ≤ c A` pointwise with `c < ∞` and `∫⁻ A^p ≤ C`, then `∫⁻ f^p ≤ c^p C` (`p ≥ 0`). -/
theorem lintegral_rpow_le_of_le_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f A : α → ℝ≥0∞} {c C : ℝ≥0∞} {p : ℝ} (hp : 0 ≤ p) (hc : c ≠ ⊤) (hf : ∀ x, f x ≤ c * A x)
    (hA : ∫⁻ x, A x ^ p ∂μ ≤ C) : ∫⁻ x, f x ^ p ∂μ ≤ c ^ p * C := by
  have hcp : c ^ p ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp hc
  calc ∫⁻ x, f x ^ p ∂μ ≤ ∫⁻ x, (c * A x) ^ p ∂μ :=
        lintegral_mono fun x => ENNReal.rpow_le_rpow (hf x) hp
    _ = c ^ p * ∫⁻ x, A x ^ p ∂μ := by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp]
        exact lintegral_const_mul' _ _ hcp
    _ ≤ c ^ p * C := by gcongr

/-! ## (i) Moments of `D̃(0,1)` -/

private theorem zero_mem_closedBall_one : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 :=
  Metric.mem_closedBall_self zero_le_one

private theorem one_mem_closedBall_one : (1 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
  rw [mem_closedBall_zero_iff, norm_one]

private theorem norm_zero_sub_one : ‖(0 : ℂ) - 1‖ = 1 := by
  rw [zero_sub, norm_neg, norm_one]

/-- `D(0,1) ≤ A(B̄₁(0))` for every continuous metric. -/
theorem ofReal_D01_le_holderConst (D : ContMetric) :
    ENNReal.ofReal (D.1 (0, 1)) ≤ holderConst D.1 (Metric.closedBall 0 1) := by
  have h := ofReal_div_le_holderConst D.1 zero_mem_closedBall_one one_mem_closedBall_one
    zero_ne_one
  rwa [norm_zero_sub_one, Real.one_rpow, div_one] at h

/-- `I(B̄₁(0), 1) ≤ D(0,1)` for every continuous metric. -/
theorem sepInf_le_ofReal_D01 (D : ContMetric) :
    sepInf D.1 (Metric.closedBall 0 1) 1 ≤ ENNReal.ofReal (D.1 (0, 1)) :=
  GaussianLQG.sepInf_le_ofReal D.1 zero_mem_closedBall_one one_mem_closedBall_one
    norm_zero_sub_one.ge

/-- Pointwise: `D̃(0,1) ≤ e^{C} A(B̄₁(0))` when `|b| ≤ C`. -/
theorem ofReal_exp_neg_mul_D01_le (D : ContMetric) {b C : ℝ} (hb : |b| ≤ C) :
    ENNReal.ofReal (Real.exp (-b) * D.1 (0, 1)) ≤
      ENNReal.ofReal (Real.exp C) * holderConst D.1 (Metric.closedBall 0 1) := by
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  gcongr
  · exact (neg_le_abs b).trans hb
  · exact ofReal_D01_le_holderConst D

/-- Pointwise: `D̃(0,1)^{-1} ≤ e^{C} I(B̄₁(0), 1)^{-1}` when `|b| ≤ C`. -/
theorem inv_ofReal_exp_neg_mul_D01_le (D : ContMetric) {b C : ℝ} (hb : |b| ≤ C) :
    (ENNReal.ofReal (Real.exp (-b) * D.1 (0, 1)))⁻¹ ≤
      ENNReal.ofReal (Real.exp C) * (sepInf D.1 (Metric.closedBall 0 1) 1)⁻¹ := by
  have hD : 0 < D.1 (0, 1) := contMetric_pos D zero_ne_one
  have hx : 0 < Real.exp (-b) * D.1 (0, 1) := mul_pos (Real.exp_pos _) hD
  rw [ENNReal.ofReal_inv_of_pos hx |>.symm, mul_inv, ← Real.exp_neg, neg_neg,
    ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_inv_of_pos hD]
  gcongr
  · exact (le_abs_self b).trans hb
  · exact sepInf_le_ofReal_D01 D

/-- **Lemma 2.1′ (i)** (GA5 (a1), step 1): for every `p ≥ 1` there are `γs > 0` and `C` such that for
`γ ∈ (0, γs]`, `E[D̃(0,1)^p] ≤ C` and `E[D̃(0,1)^{-p}] ≤ C`, where `D̃ = e^{-b_γ} D^γ`. -/
theorem exists_D01_moments (S : Setup) : ∀ p : ℝ, 1 ≤ p → ∃ γs C : ℝ, 0 < γs ∧
    ∀ γ ∈ Ioc (0 : ℝ) γs,
      (∫⁻ ω, ENNReal.ofReal (Real.exp (-S.b γ) * (S.D γ ω).1 (0, 1)) ^ p ∂stdP) ≤
        ENNReal.ofReal C ∧
      (∫⁻ ω, (ENNReal.ofReal (Real.exp (-S.b γ) * (S.D γ ω).1 (0, 1)))⁻¹ ^ p ∂stdP) ≤
        ENNReal.ofReal C := by
  intro p hp
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨γ6, hγ6, h6⟩ := S.S6 p hp
  obtain ⟨C6, hC6, hC6b⟩ := h6 (Metric.closedBall 0 1) (isCompact_closedBall 0 1) 1 one_pos
  obtain ⟨γb, Cb, hγb, hb⟩ := S.abs_b_le
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.exp Cb) with hc_def
  have hc : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcC : c ^ p * C6 ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp0 hc) hC6
  refine ⟨min γ6 γb, (c ^ p * C6).toReal, lt_min hγ6 hγb, fun γ hγ => ?_⟩
  obtain ⟨hγ0, hγle⟩ := hγ
  obtain ⟨hA, hI⟩ := hC6b γ ⟨hγ0, hγle.trans (min_le_left _ _)⟩
  have hbγ := hb γ ⟨hγ0, hγle.trans (min_le_right _ _)⟩
  rw [ENNReal.ofReal_toReal hcC]
  exact ⟨lintegral_rpow_le_of_le_mul hp0 hc (fun ω => ofReal_exp_neg_mul_D01_le _ hbγ) hA,
    lintegral_rpow_le_of_le_mul hp0 hc (fun ω => inv_ofReal_exp_neg_mul_D01_le _ hbγ) hI⟩

/-! ## (ii) Moments of `T`, `B`, `Θ`, and localization for geodesics from `0` to `1` -/

/-- **Lemma 2.1′ (ii), moments** (GA5 (a1), step 2): for every `p ≥ 1` there are `γs > 0` and `C` such
that for `γ ∈ (0, γs]`, `E[T^p]`, `E[B^p]` and `E[Θ^p]` are at most `C`, where `T`, `B`, `Θ` are the
localization variables of `K₁ = B̄₁(0)`, `δ = 1` (`Setup.exists_locMoments`). -/
theorem exists_locMoments_closedBall_one (S : Setup) : ∀ p : ℝ, 1 ≤ p → ∃ γs C : ℝ, 0 < γs ∧
    ∀ γ ∈ Ioc (0 : ℝ) γs,
      (∫⁻ ω, S.locT γ (Metric.closedBall 0 1) ω ^ p ∂stdP) ≤ ENNReal.ofReal C ∧
      (∫⁻ ω, S.locB γ (Metric.closedBall 0 1) 1 ω ^ p ∂stdP) ≤ ENNReal.ofReal C ∧
      (∫⁻ ω, S.locTheta γ (Metric.closedBall 0 1) 1 ω ^ p ∂stdP) ≤ ENNReal.ofReal C := by
  intro p hp
  obtain ⟨γs, hγs, hmom⟩ := S.exists_locMoments S.holderScaling S.annulusScaling p hp
  obtain ⟨C, hC, hCb⟩ := hmom (Metric.closedBall 0 1) (isCompact_closedBall 0 1) 1 one_pos
  refine ⟨γs, C.toReal, hγs, fun γ hγ => ?_⟩
  obtain ⟨-, hint⟩ := hCb γ hγ
  rw [ENNReal.ofReal_toReal hC]
  refine ⟨(lintegral_mono fun ω => ?_).trans hint, (lintegral_mono fun ω => ?_).trans hint,
    (lintegral_mono fun ω => ?_).trans hint⟩
  · exact le_self_add.trans le_self_add
  · exact le_add_self.trans le_self_add
  · exact le_add_self

/-- `T ≥ 4` for `K₁ = B̄₁(0)` whenever `T < ∞` (`T ≥ 2 R₀` and `R₀ ≥ 2`). -/
theorem four_le_toReal_locT (S : Setup) {γ : ℝ} {ω : Coord}
    (hT : S.locT γ (Metric.closedBall 0 1) ω ≠ ⊤) :
    4 ≤ (S.locT γ (Metric.closedBall 0 1) ω).toReal := by
  have hR0 := (locR0_spec (isCompact_closedBall (0 : ℂ) 1).isBounded).1
  have h := (ENNReal.ofReal_le_iff_le_toReal hT).1
    (Setup.ofReal_two_mul_locR0_le_locT (S := S) (γ := γ) (K := Metric.closedBall 0 1) (ω := ω))
  linarith

/-- If a path stays in the open ball `B_T(0)`, its maximal distance from `[0,1]` is at most `T`. -/
theorem maxDev_le_of_range_subset_ball {η : C(unitInterval, ℂ)} {T : ℝ}
    (h : range η ⊆ Metric.ball 0 T) : maxDev η ≤ T := by
  unfold maxDev
  refine ciSup_le fun t => ?_
  have h0 : (0 : ℂ) ∈ segment ℝ (0 : ℂ) 1 := left_mem_segment ℝ 0 1
  have ht : η t ∈ Metric.ball (0 : ℂ) T := h (mem_range_self t)
  rw [mem_ball_zero_iff] at ht
  calc Metric.infDist (η t) (segment ℝ (0 : ℂ) 1) ≤ dist (η t) 0 := Metric.infDist_le_dist_of_mem h0
    _ = ‖η t‖ := dist_zero_right _
    _ ≤ T := ht.le

/-- **Lemma 2.1′ (ii), almost-sure statements** (GA5 (a1), step 2; `Setup.ae_localization` at
`K₁ = B̄₁(0)`, `δ = 1`, `z = 0`, `w = 1`): there is `γT > 0` such that for `γ ∈ (0, γT]`, almost
surely `T, B, Θ < ∞`, `T ≥ 4`, `B ≥ 1`, and every constant-speed geodesic `η` from `0` to `1`
satisfies `η([0,1]) ⊆ B_T(0)`, `M(η) ≤ T`, `ν_η(B_r(u)) ≤ B r^{1/2}` for `u ∈ ℂ`, `r ∈ (0,1]`, and
`ν_η` is regular with `ℰ(ν_η, ν_η) ≤ Θ²`. -/
theorem ae_localization_zero_one (S : Setup) : ∃ γT : ℝ, 0 < γT ∧ ∀ γ ∈ Ioc (0 : ℝ) γT,
    ∀ᵐ ω ∂stdP, S.locT γ (Metric.closedBall 0 1) ω ≠ ⊤ ∧
      S.locB γ (Metric.closedBall 0 1) 1 ω ≠ ⊤ ∧
      S.locTheta γ (Metric.closedBall 0 1) 1 ω ≠ ⊤ ∧
      4 ≤ (S.locT γ (Metric.closedBall 0 1) ω).toReal ∧
      1 ≤ (S.locB γ (Metric.closedBall 0 1) 1 ω).toReal ∧
      ∀ η : C(unitInterval, ℂ), IsGeod01 (S.D γ ω) 0 1 η →
        range η ⊆ Metric.ball 0 (S.locT γ (Metric.closedBall 0 1) ω).toReal ∧
        maxDev η ≤ (S.locT γ (Metric.closedBall 0 1) ω).toReal ∧
        (∀ u : ℂ, ∀ r : ℝ, 0 < r → r ≤ 1 →
          (lengthMeasure η (Metric.ball u r)).toReal ≤
            (S.locB γ (Metric.closedBall 0 1) 1 ω).toReal * r ^ (1 / 2 : ℝ)) ∧
        IsRegular (lengthMeasure η) ∧
        energy (lengthMeasure η) (lengthMeasure η) ≤
          (S.locTheta γ (Metric.closedBall 0 1) 1 ω).toReal ^ 2 := by
  obtain ⟨γT, hγT, hloc⟩ := S.ae_localization S.holderScaling S.annulusScaling
  refine ⟨γT, hγT, fun γ hγ => ?_⟩
  filter_upwards [hloc γ hγ (Metric.closedBall 0 1) (isCompact_closedBall 0 1) 1 one_pos]
    with ω hω
  obtain ⟨hT, hB, hΘ, hgeo⟩ := hω
  have hB1 : 1 ≤ (S.locB γ (Metric.closedBall 0 1) 1 ω).toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hB (Setup.one_le_locB (S := S))
  refine ⟨hT, hB, hΘ, four_le_toReal_locT S hT, hB1, fun η hη => ?_⟩
  obtain ⟨hr, hball, hreg, hen⟩ := hgeo 0 zero_mem_closedBall_one 1 one_mem_closedBall_one
    norm_zero_sub_one.ge η hη
  exact ⟨hr, maxDev_le_of_range_subset_ball hr, hball, hreg, hen⟩

/-! ## (iii) Source (2.3): the exponential energy moment (ported from GA1's `GA1Probe2.lean`) -/

/-- Pointwise: `exp(Θ²/4) ≤ e^{1/2} (T + B)` when `T, B < ∞`. -/
theorem exp_locTheta_sq_le (S : Setup) {γ : ℝ} {K : Set ℂ} {δ : ℝ} {ω : Coord}
    (hT : S.locT γ K ω ≠ ⊤) (hB : S.locB γ K δ ω ≠ ⊤) :
    ENNReal.ofReal (Real.exp ((S.locTheta γ K δ ω).toReal ^ 2 / 4)) ≤
      ENNReal.ofReal (Real.exp (1 / 2)) * (S.locT γ K ω + S.locB γ K δ ω) := by
  have hT1 : 1 ≤ (S.locT γ K ω).toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hT (Setup.one_le_locT (S := S))
  have hB1 : 1 ≤ (S.locB γ K δ ω).toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hB (Setup.one_le_locB (S := S))
  set t := (S.locT γ K ω).toReal with ht
  set b := (S.locB γ K δ ω).toReal with hb
  have hsum : 0 < t + b := by linarith
  have hlt : Real.log t ≤ Real.log (t + b) := Real.log_le_log (by linarith) (by linarith)
  have hlb : Real.log b ≤ Real.log (t + b) := Real.log_le_log (by linarith) (by linarith)
  have hreal : Real.exp ((S.locTheta γ K δ ω).toReal ^ 2 / 4) ≤
      Real.exp (1 / 2) * (t + b) := by
    rw [Setup.toReal_locTheta_sq hT hB, ← Real.exp_log hsum, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    rw [← ht, ← hb]
    linarith
  calc ENNReal.ofReal (Real.exp ((S.locTheta γ K δ ω).toReal ^ 2 / 4))
      ≤ ENNReal.ofReal (Real.exp (1 / 2) * (t + b)) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (Real.exp (1 / 2)) * (S.locT γ K ω + S.locB γ K δ ω) := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
          ENNReal.ofReal_add (by linarith) (by linarith), ht, hb,
          ENNReal.ofReal_toReal hT, ENNReal.ofReal_toReal hB]

/-- **Source (2.3)**, with `Θ` of GaussianLQG Lemma `lem:T-B` at `K = B̄_1(0)`, `δ = 1` as the
energy majorant: one threshold `γs` and one constant `C` such that for `γ ∈ (0, γs]`,
`E exp(Θ²/4) ≤ C`, and a.s. every constant-speed geodesic `η` from `0` to `1` has a regular length
measure `ν_η` with `ℰ(ν_η, ν_η) ≤ Θ²`. Hence `E exp(ℰ(ν_η,ν_η)/4) ≤ C`. -/
theorem expEnergyMoment (S : Setup) :
    ∃ γs C : ℝ, 0 < γs ∧ ∀ γ ∈ Ioc (0 : ℝ) γs,
      (∫⁻ ω, ENNReal.ofReal
          (Real.exp ((S.locTheta γ (Metric.closedBall 0 1) 1 ω).toReal ^ 2 / 4)) ∂stdP) ≤
        ENNReal.ofReal C ∧
      ∀ᵐ ω ∂stdP, S.locTheta γ (Metric.closedBall 0 1) 1 ω ≠ ⊤ ∧
        ∀ η : C(unitInterval, ℂ), IsGeod01 (S.D γ ω) 0 1 η →
          IsRegular (lengthMeasure η) ∧
          energy (lengthMeasure η) (lengthMeasure η) ≤
            (S.locTheta γ (Metric.closedBall 0 1) 1 ω).toReal ^ 2 := by
  have hA := S.holderScaling
  have hL := S.annulusScaling
  set K : Set ℂ := Metric.closedBall (0 : ℂ) 1 with hK
  have hKc : IsCompact K := isCompact_closedBall 0 1
  obtain ⟨γ1, hγ1, hmom⟩ := S.exists_locMoments hA hL 1 le_rfl
  obtain ⟨C1, hC1, hC1b⟩ := hmom K hKc 1 one_pos
  obtain ⟨γT, hγT, hloc⟩ := S.ae_localization hA hL
  refine ⟨min γ1 γT, Real.exp (1 / 2) * C1.toReal, lt_min hγ1 hγT, fun γ hγ => ?_⟩
  obtain ⟨hγ0, hγle⟩ := hγ
  have hγ1' : γ ≤ γ1 := hγle.trans (min_le_left _ _)
  have hγT' : γ ≤ γT := hγle.trans (min_le_right _ _)
  obtain ⟨-, hint⟩ := hC1b γ ⟨hγ0, hγ1'⟩
  have h0K : (0 : ℂ) ∈ K := Metric.mem_closedBall_self zero_le_one
  have h1K : (1 : ℂ) ∈ K := by rw [hK, mem_closedBall_zero_iff, norm_one]
  have h01 : (1 : ℝ) ≤ ‖(0 : ℂ) - 1‖ := by rw [zero_sub, norm_neg, norm_one]
  have hae := hloc γ ⟨hγ0, hγT'⟩ K hKc 1 one_pos
  refine ⟨?_, ?_⟩
  · calc ∫⁻ ω, ENNReal.ofReal (Real.exp ((S.locTheta γ K 1 ω).toReal ^ 2 / 4)) ∂stdP
        ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (1 / 2)) *
            (S.locT γ K ω ^ (1 : ℝ) + S.locB γ K 1 ω ^ (1 : ℝ) +
              S.locTheta γ K 1 ω ^ (1 : ℝ)) ∂stdP := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae] with ω hω
          obtain ⟨hT, hB, -, -⟩ := hω
          refine (exp_locTheta_sq_le S hT hB).trans ?_
          simp only [ENNReal.rpow_one]
          exact mul_le_mul_right le_self_add _
      _ = ENNReal.ofReal (Real.exp (1 / 2)) *
            ∫⁻ ω, (S.locT γ K ω ^ (1 : ℝ) + S.locB γ K 1 ω ^ (1 : ℝ) +
              S.locTheta γ K 1 ω ^ (1 : ℝ)) ∂stdP :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Real.exp (1 / 2)) * C1 := by gcongr
      _ = ENNReal.ofReal (Real.exp (1 / 2) * C1.toReal) := by
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_toReal hC1]
  · filter_upwards [hae] with ω hω
    exact ⟨hω.2.2.1, fun η hη => (hω.2.2.2 0 h0K 1 h1K h01 η hη).2.2⟩

end SmallGammaGeodesics
