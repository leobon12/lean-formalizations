import QuantumZipper.Statements.Prop16Literal
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: the chart is a dilation to first order at `0`

Deterministic part of the transfer `theorem1_6 → theorem1_6_literal` (decision D95). For a chart
`ψ` with a strict complex derivative `κ > 0` at `0`, `ψ 0 = 0` and `ψ` real on a real segment
around `0`:

* `LitChart.im_close`: near `0`, `|Im ψ z − κ Im z| ≤ (κ/2) |Im z|`, so `ψ` preserves the sign
  of the imaginary part (the reflected chart maps `ℍ` to `ℍ` and the lower half-plane to the
  lower half-plane near `0`);
* `LitChart.image_subset`, `LitChart.subset_image`: for every `ε ∈ (0,1)` and all small `s`,
  `B((1−ε)κs) ∩ ℍ ⊆ ψ(B(s) ∩ ℍ) ⊆ B((1+ε)κs) ∩ ℍ` (the upper inclusion through the local
  inverse of the inverse function theorem);
* `LitChart.scale_bounds`: the (1.8)-scales of two measures with
  `μ(B_{c₁s} ∩ ℍ) ≤ ν(B_s ∩ ℍ) ≤ μ(B_{c₂s} ∩ ℍ)` for small `s` (`c₁,₂ = (1∓ε)κ`) satisfy `a/((1+ε)κ) ≤ b ≤ a/((1−ε)κ)` once `a` is small: the
  dilation `ψ'(0)` is absorbed by the normalization (1.8), Sheffield arXiv:1012.4797, p. 21,
  lines 797–807.

Own elementary arguments (AGENT_GUIDE cost rule): first-order Taylor expansion, the inverse
function theorem (mathlib `HasStrictDerivAt.localInverse`) and monotonicity of `sInf`.
-/

noncomputable section

open Filter Set Metric MeasureTheory
open scoped Topology ENNReal

namespace QuantumZipper

namespace LitChart

variable {ψ : ℂ → ℂ} {κ : ℝ}

/-- Strict differentiability at `0`, quantitatively. -/
theorem strict_bound (hψ : HasStrictDerivAt ψ (κ : ℂ) 0) {c : ℝ} (hc : 0 < c) :
    ∃ δ > 0, ∀ p q : ℂ, ‖p‖ < δ → ‖q‖ < δ →
      ‖ψ p - ψ q - κ * (p - q)‖ ≤ c * ‖p - q‖ := by
  have h := hψ.hasStrictFDerivAt.isLittleO.def hc
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨δ, hδ, hδh⟩ := h
  refine ⟨δ, hδ, fun p q hp hq => ?_⟩
  have hpq : dist (p, q) ((0 : ℂ), (0 : ℂ)) < δ := by
    rw [Prod.dist_eq, max_lt_iff, dist_zero_right, dist_zero_right]; exact ⟨hp, hq⟩
  have := hδh hpq
  simpa [mul_comm] using this

/-- Near `0` the chart preserves the sign of the imaginary part. -/
theorem im_close (hκ : 0 < κ) (hψ : HasStrictDerivAt ψ (κ : ℂ) 0)
    {r : ℝ} (hr : 0 < r) (hreal : ∀ t : ℝ, |t| < r → (ψ t).im = 0) :
    ∃ δ > 0, ∀ z : ℂ, ‖z‖ < δ → |(ψ z).im - κ * z.im| ≤ κ / 2 * |z.im| := by
  obtain ⟨δ, hδ, hb⟩ := strict_bound hψ (half_pos hκ)
  refine ⟨min δ r, lt_min hδ hr, fun z hz => ?_⟩
  have hz1 : ‖z‖ < δ := hz.trans_le (min_le_left _ _)
  have hz2 : ‖z‖ < r := hz.trans_le (min_le_right _ _)
  have hre : ‖((z.re : ℝ) : ℂ)‖ ≤ ‖z‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact Complex.abs_re_le_norm z
  have h1 := hb z (z.re : ℂ) hz1 (hre.trans_lt hz1)
  have hre' : |z.re| < r := (Complex.abs_re_le_norm z).trans_lt hz2
  have h0 : (ψ (z.re : ℂ)).im = 0 := hreal z.re hre'
  have hsub : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hn : ‖z - (z.re : ℂ)‖ = |z.im| := by
    rw [hsub, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have him : (ψ z - ψ (z.re : ℂ) - κ * (z - (z.re : ℂ))).im = (ψ z).im - κ * z.im := by
    rw [hsub]; simp [h0]
  calc |(ψ z).im - κ * z.im| = |(ψ z - ψ (z.re : ℂ) - κ * (z - (z.re : ℂ))).im| := by rw [him]
    _ ≤ ‖ψ z - ψ (z.re : ℂ) - κ * (z - (z.re : ℂ))‖ := Complex.abs_im_le_norm _
    _ ≤ κ / 2 * ‖z - (z.re : ℂ)‖ := h1
    _ = κ / 2 * |z.im| := by rw [hn]

/-- The lower inclusion `ψ(B(s) ∩ ℍ) ⊆ B((1+ε)κs) ∩ ℍ` for small `s`. -/
theorem image_subset (hκ : 0 < κ) (hψ : HasStrictDerivAt ψ (κ : ℂ) 0) (hψ0 : ψ 0 = 0)
    {r : ℝ} (hr : 0 < r) (hreal : ∀ t : ℝ, |t| < r → (ψ t).im = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s, 0 < s → s ≤ δ →
      ψ '' (ball 0 s ∩ H) ⊆ ball 0 ((1 + ε) * κ * s) ∩ H := by
  obtain ⟨δ₁, hδ₁, hb⟩ := strict_bound hψ (show 0 < ε * κ / 2 by positivity)
  obtain ⟨δ₂, hδ₂, him⟩ := im_close hκ hψ hr hreal
  refine ⟨min δ₁ δ₂ / 2, by positivity, fun s hs hsδ => ?_⟩
  rintro _ ⟨z, ⟨hzb, hzH⟩, rfl⟩
  rw [mem_ball, dist_zero_right] at hzb
  have hz1 : ‖z‖ < δ₁ := by
    have := min_le_left δ₁ δ₂; linarith
  have hz2 : ‖z‖ < δ₂ := by
    have := min_le_right δ₁ δ₂; linarith
  refine ⟨?_, ?_⟩
  · rw [mem_ball, dist_zero_right]
    have h1 := hb z 0 hz1 (by simpa using hδ₁)
    simp only [hψ0, sub_zero] at h1
    have h2 : ‖ψ z‖ ≤ κ * ‖z‖ + ε * κ / 2 * ‖z‖ := by
      have := norm_sub_norm_le (ψ z) (κ * z)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hκ.le] at this
      linarith
    have hzpos : 0 ≤ ‖z‖ := norm_nonneg z
    have h3 : κ * ‖z‖ + ε * κ / 2 * ‖z‖ < (1 + ε) * κ * s := by
      have hp : 0 ≤ ε * κ * ‖z‖ := by positivity
      have : κ * ‖z‖ + ε * κ / 2 * ‖z‖ ≤ (1 + ε) * κ * ‖z‖ := by
        have e : (1 + ε) * κ * ‖z‖ = κ * ‖z‖ + ε * κ * ‖z‖ := by ring
        have e2 : ε * κ / 2 * ‖z‖ = ε * κ * ‖z‖ / 2 := by ring
        rw [e, e2]; linarith
      have h4 : (1 + ε) * κ * ‖z‖ < (1 + ε) * κ * s :=
        mul_lt_mul_of_pos_left hzb (by positivity)
      linarith
    linarith
  · have hi := him z hz2
    have hzim : 0 < z.im := hzH
    rw [abs_of_pos hzim] at hi
    show 0 < (ψ z).im
    have := (abs_le.1 hi).1
    nlinarith

/-- The upper inclusion `B((1−ε)κs) ∩ ℍ ⊆ ψ(B(s) ∩ ℍ)` for small `s` (local inverse). -/
theorem subset_image (hκ : 0 < κ) (hψ : HasStrictDerivAt ψ (κ : ℂ) 0) (hψ0 : ψ 0 = 0)
    {r : ℝ} (hr : 0 < r) (hreal : ∀ t : ℝ, |t| < r → (ψ t).im = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s, 0 < s → s ≤ δ →
      ball 0 ((1 - ε) * κ * s) ∩ H ⊆ ψ '' (ball 0 s ∩ H) := by
  have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  set g := hψ.localInverse ψ (κ : ℂ) 0 hκ' with hgdef
  have hg : HasStrictDerivAt g ((κ⁻¹ : ℝ) : ℂ) 0 := by
    have := hψ.to_localInverse hκ'
    rw [hψ0] at this
    simpa using this
  have hright := hψ.eventually_right_inverse hκ'
  rw [hψ0, Metric.eventually_nhds_iff] at hright
  obtain ⟨ρ, hρ, hρr⟩ := hright
  have hleft := (hψ.eventually_left_inverse hκ').self_of_nhds
  rw [hψ0] at hleft
  obtain ⟨δg, hδg, hbg⟩ := strict_bound hg (show 0 < ε / κ by positivity)
  obtain ⟨δ₂, hδ₂, him⟩ := im_close hκ hψ hr hreal
  refine ⟨min δ₂ (min ρ δg / κ), lt_min hδ₂ (by positivity), fun s hs hsδ => ?_⟩
  rintro w ⟨hwb, hwH⟩
  rw [mem_ball, dist_zero_right] at hwb
  have hs1 : s ≤ δ₂ := hsδ.trans (min_le_left _ _)
  have hs2 : κ * s ≤ min ρ δg := by
    have := hsδ.trans (min_le_right _ _)
    rw [le_div_iff₀ hκ] at this; linarith
  have hw1 : ‖w‖ < κ * s := by
    have : (1 - ε) * κ * s ≤ κ * s := by
      have : 0 ≤ ε * κ * s := by positivity
      nlinarith
    linarith
  have hwρ : ‖w‖ < ρ := hw1.trans_le (hs2.trans (min_le_left _ _))
  have hwg : ‖w‖ < δg := hw1.trans_le (hs2.trans (min_le_right _ _))
  -- the bound on `g w`
  have hb := hbg w 0 hwg (by simpa using hδg)
  have hg0 : g 0 = 0 := hleft
  rw [hg0, sub_zero, sub_zero] at hb
  have hgw : ‖g w‖ ≤ κ⁻¹ * ‖w‖ + ε / κ * ‖w‖ := by
    have := norm_sub_norm_le (g w) (((κ⁻¹ : ℝ) : ℂ) * w)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hκ.le)] at this
    linarith
  have hgw' : ‖g w‖ < s := by
    have e : κ⁻¹ * ‖w‖ + ε / κ * ‖w‖ = (1 + ε) * ‖w‖ / κ := by field_simp
    rw [e] at hgw
    have h1 : (1 + ε) * ‖w‖ < (1 + ε) * ((1 - ε) * κ * s) :=
      mul_lt_mul_of_pos_left hwb (by positivity)
    have h2 : (1 + ε) * ((1 - ε) * κ * s) ≤ κ * s := by
      have : 0 ≤ ε * ε * κ * s := by positivity
      nlinarith
    have h3 : (1 + ε) * ‖w‖ / κ < s := by
      rw [div_lt_iff₀ hκ]; linarith
    linarith
  have hψg : ψ (g w) = w := hρr (by rwa [dist_zero_right])
  refine ⟨g w, ⟨by rwa [mem_ball, dist_zero_right], ?_⟩, hψg⟩
  -- `g w ∈ ℍ`: otherwise `Im ψ(g w) ≤ 0`
  show 0 < (g w).im
  by_contra hneg
  push Not at hneg
  have hi := him (g w) (hgw'.trans_le hs1)
  rw [hψg, abs_of_nonpos hneg] at hi
  have hwim : 0 < w.im := hwH
  have := (abs_le.1 hi).2
  nlinarith

/-- The (1.8)-scale of a measure: the least radius `a` with `μ(B_a(0) ∩ ℍ) ≥ 1`
(`scaleParamOn γ x U = scaleOf (qAreaMeasureOn γ x U)` by definition). -/
def scaleOf (μ : Measure ℂ) : ℝ := sInf {a : ℝ | 0 < a ∧ 1 ≤ μ (ball 0 a ∩ H)}

theorem scaleOf_bdd (μ : Measure ℂ) : BddBelow {a : ℝ | 0 < a ∧ 1 ≤ μ (ball 0 a ∩ H)} :=
  ⟨0, fun _ h => h.1.le⟩

/-- **Scale comparison.** If `μ(B(c₁ s) ∩ ℍ) ≤ ν(B_s ∩ ℍ) ≤ μ(B(c₂ s) ∩ ℍ)` for `s ≤ ρ`, then the (1.8)-scales satisfy
`a / c₂ ≤ b ≤ a / c₁` as soon as `0 < a < c₁ ρ`. -/
theorem scale_bounds {μ ν : Measure ℂ} {ρ c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁₂ : c₁ ≤ c₂)
    (hlow : ∀ s, 0 < s → s ≤ ρ → μ (ball 0 (c₁ * s) ∩ H) ≤ ν (ball 0 s ∩ H))
    (hup : ∀ s, 0 < s → s ≤ ρ → ν (ball 0 s ∩ H) ≤ μ (ball 0 (c₂ * s) ∩ H))
    (ha0 : 0 < scaleOf μ) (ha : scaleOf μ < c₁ * ρ) :
    scaleOf μ / c₂ ≤ scaleOf ν ∧ scaleOf ν ≤ scaleOf μ / c₁ := by
  have hc₂ : 0 < c₂ := hc₁.trans_le hc₁₂
  set A := {a : ℝ | 0 < a ∧ 1 ≤ μ (ball 0 a ∩ H)} with hA
  set B := {a : ℝ | 0 < a ∧ 1 ≤ ν (ball 0 a ∩ H)} with hB
  have hAne : A.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have : scaleOf μ = 0 := by simp only [scaleOf, ← hA, h, Real.sInf_empty]
    linarith
  have haρ : scaleOf μ / c₁ < ρ := by rw [div_lt_iff₀ hc₁]; linarith
  -- every `s ∈ (a / c₁, ρ]` lies in `B`
  have hmemB : ∀ s, scaleOf μ / c₁ < s → s ≤ ρ → s ∈ B := by
    intro s hs hsρ
    have hs0 : 0 < s := lt_trans (div_pos ha0 hc₁) hs
    have hlt : sInf A < c₁ * s := by
      show scaleOf μ < c₁ * s
      rw [div_lt_iff₀ hc₁] at hs; linarith
    obtain ⟨t, ⟨ht0, ht1⟩, hts⟩ := exists_lt_of_csInf_lt hAne hlt
    refine ⟨hs0, ?_⟩
    calc (1 : ℝ≥0∞) ≤ μ (ball 0 t ∩ H) := ht1
      _ ≤ μ (ball 0 (c₁ * s) ∩ H) :=
          measure_mono (inter_subset_inter_left _ (ball_subset_ball hts.le))
      _ ≤ ν (ball 0 s ∩ H) := hlow s hs0 hsρ
  have hBne : B.Nonempty := ⟨ρ, hmemB ρ haρ le_rfl⟩
  constructor
  · refine le_csInf hBne fun s ⟨hs0, hs1⟩ => ?_
    rw [div_le_iff₀ hc₂]
    rcases le_or_gt s ρ with hsρ | hsρ
    · have hmem : c₂ * s ∈ A := by
        refine ⟨by positivity, ?_⟩
        calc (1 : ℝ≥0∞) ≤ ν (ball 0 s ∩ H) := hs1
          _ ≤ μ (ball 0 (c₂ * s) ∩ H) := hup s hs0 hsρ
      have := csInf_le (scaleOf_bdd μ) hmem
      show sInf A ≤ s * c₂
      linarith
    · have h1 : c₁ * ρ ≤ c₂ * s :=
        mul_le_mul hc₁₂ hsρ.le (by linarith [div_pos ha0 hc₁]) hc₂.le
      linarith
  · refine le_of_forall_gt_imp_ge_of_dense fun s hs => ?_
    have h1 := csInf_le (scaleOf_bdd ν) (hmemB (min s ρ) (lt_min hs haρ) (min_le_right _ _))
    exact h1.trans (min_le_left _ _)

end LitChart

end QuantumZipper
