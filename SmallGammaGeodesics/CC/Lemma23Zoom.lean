import SmallGammaGeodesics.CC.Lemma23
import SmallGammaGeodesics.NIC.Main

/-!
# [3] Lemma 2.3* on the zoom couplings (track CC, packet CC6a, T2 for D10)

Source: `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D9** (Lemma 2.3*) and the
way **D10** ([3] Prop 2.1) uses it, on the NIC spaces of the zoomed inverse maps of CC4 (D6).

`zoom_nic` (CC4) gives, for `IsConfNbhd ϕ W V`, a compact `Kc ⊆ V` and `R > 0`, constants `r₁, C`
and, for every `z ∈ Kc` and `r ∈ (0, r₁]`, the global extension `Ξ = zoomExt ϕ ψ z r R` of the
zoomed inverse map with inverse `Ξinv` (`IsZoomExt`, constant `C`), and a NIC coupling `(h, h̄, K)`
of `Ξinv` on `B_R` with `E sup_{B̄_{R/2}} |K − K(0)| ≤ C r`. Then:
* `lemma23_zoom`: along any sequence of such data with `r n → 0`, the bad event of Lemma 2.3* has
  probability tending to `0` (the sequence form of D9);
* `lemma23_zoom_uniform`: for every `C > 0`, `δ, η > 0` there is `r₀ > 0` such that **every** such
  datum with `r ≤ r₀` (any centre, any map, any probability space) has bad-event probability `≤ η`
  (the uniformity over `z` that D10 obtains by contradiction along sequences);
* `lemma23_zoom_exists`: the unconditional package for D10 (`zoom_nic NIC.nicInput_holds` and D9's
  measurable continuous extension `K̃` of `K` from `B̄_{3R/4}`, `exists_measurable_contExt`):
  constants `r₁, C`, the NIC spaces for all `z ∈ Kc`, `r ∈ (0, r₁]`, and for all `δ, η > 0` a radius
  `r₀ ≤ r₁` below which the bound holds on every such space.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric

section Zoom

variable {γ : ℝ} {D : DistC → ContMetric}

/-- **[3] Lemma 2.3* for the zoom couplings of CC4** (`zoom_nic`): along any sequence of zoom data
`(z n, r n)` with `r n → 0`, extension maps `Ξ_n = zoomExt ϕ ψ (z n) (r n) R` with inverses `Ξinv n`
(`IsZoomExt` with constant `C`, `C r n ≤ 1/32`), NIC couplings of `Ξinv n` on `B_R` and
`E sup_{B̄_{R/2}} |K n − K n(0)| ≤ C r n`, and continuous `K̃ n ω = K n ω` on `B_{R/2}` (e.g. from
`exists_measurable_contExt`), the conclusion of `lemma23_seq` holds. -/
theorem lemma23_zoom (hD : IsStrongLQGMetric γ D) {ϕ ψ : ℂ → ℂ} {W : Set ℂ} {R C : ℝ}
    (hR : 0 < R) {ρ : TestC} (hρs : tsupport (ρ : ℂ → ℝ) ⊆ closedBall 0 (R / 2))
    (hρ1 : ∫ x, ρ x = 1) {K₁ : Set ℂ} (hK₁ : IsCompact K₁) (hK₁B : K₁ ⊆ ball 0 (R / 2))
    {z : ℕ → ℂ} {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) {Ξinv : ℕ → ℂ → ℂ}
    (hZ : ∀ n, IsZoomExt ϕ ψ W (z n) (r n) R C (zoomExt ϕ ψ (z n) (r n) R) (Ξinv n))
    {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (P n)] {h hbar : ∀ n, Ω n → DistC} {K : ∀ n, Ω n → ℂ → ℝ}
    (hc : ∀ n, IsNICCoupling (P n) (Ξinv n) (ball 0 R) (C * r n ^ 2) (h n) (hbar n) (K n))
    (hsup : ∀ n, ∫⁻ ω, supDev (K n ω) (R / 2) ∂(P n) ≤ ENNReal.ofReal (C * r n))
    {Kt : ∀ n, Ω n → C(ℂ, ℝ)} (hKt : ∀ n ω, ∀ x ∈ ball (0 : ℂ) (R / 2), Kt n ω x = K n ω x)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => P n {ω | ¬ ∀ u ∈ K₁, ∀ v ∈ K₁,
      (D (addFun (hbar n ω) (Kt n ω))).internal (ball 0 (R / 2)) u v ≤
          (D (h n ω)).internal (ball 0 (R / 2)) u v +
            ENNReal.ofReal (δ * Real.exp (xiGamma γ * h n ω ρ)) ∧
      (D (h n ω)).internal (ball 0 (R / 2)) u v ≤
          (D (addFun (hbar n ω) (Kt n ω))).internal (ball 0 (R / 2)) u v +
            ENNReal.ofReal (δ * Real.exp (xiGamma γ * h n ω ρ))}) atTop (𝓝 0) := by
  have hε : Tendsto (fun n => C * r n) atTop (𝓝 0) := by
    have := hr.const_mul C
    rwa [mul_zero] at this
  refine lemma23_seq hD hR hρs hρ1 hK₁ hK₁B hc (fun n => (hZ n).nearId)
    (fun n x => (hZ n).inv_norm_sub_le x) hε hsup (fun n ω x hx => ?_) hδ
  rw [hKt n ω x hx, sub_self, abs_zero]
  have := (hZ n).inv_norm_sub_le 0
  exact (norm_nonneg _).trans this

/-- **[3] Lemma 2.3* for zoom couplings, uniform form** (D10's uniformity over the centre). For
every `C > 0`, `δ > 0` and `η > 0` there is `r₀ > 0` such that for every map `ϕ`, left inverse `ψ`,
set `W`, centre `z` and scale `r ≤ r₀`, every inverse `Ξinv` of the extension `zoomExt ϕ ψ z r R`
with `IsZoomExt` (constant `C`), and every NIC coupling `(h, h̄, K)` of `Ξinv` on `B_R` (any
probability space) with `E sup_{B̄_{R/2}} |K − K(0)| ≤ C r` and any continuous `K̃ = K` on
`B_{R/2}`, the bad event of
Lemma 2.3* has probability at most `η`. -/
theorem lemma23_zoom_uniform (hD : IsStrongLQGMetric γ D) {R : ℝ} (hR : 0 < R) {ρ : TestC}
    (hρs : tsupport (ρ : ℂ → ℝ) ⊆ closedBall 0 (R / 2)) (hρ1 : ∫ x, ρ x = 1)
    {K₁ : Set ℂ} (hK₁ : IsCompact K₁) (hK₁B : K₁ ⊆ ball 0 (R / 2)) {δ : ℝ} (hδ : 0 < δ)
    {η : ℝ≥0∞} (hη : 0 < η) {C : ℝ} (hC : 0 < C) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ (ϕ ψ : ℂ → ℂ) (W : Set ℂ) (z : ℂ) (r : ℝ), r ≤ r₀ →
      ∀ Ξinv : ℂ → ℂ, IsZoomExt ϕ ψ W z r R C (zoomExt ϕ ψ z r R) Ξinv →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ)
        (h hbar : Ω → DistC) (K : Ω → ℂ → ℝ) (Kt : Ω → C(ℂ, ℝ)),
        IsNICCoupling P Ξinv (ball 0 R) B h hbar K →
        ∫⁻ ω, supDev (K ω) (R / 2) ∂P ≤ ENNReal.ofReal (C * r) →
        (∀ ω, ∀ x ∈ ball (0 : ℂ) (R / 2), Kt ω x = K ω x) →
        P {ω | ¬ ∀ u ∈ K₁, ∀ v ∈ K₁,
        (D (addFun (hbar ω) (Kt ω))).internal (ball 0 (R / 2)) u v ≤
            (D (h ω)).internal (ball 0 (R / 2)) u v +
              ENNReal.ofReal (δ * Real.exp (xiGamma γ * h ω ρ)) ∧
        (D (h ω)).internal (ball 0 (R / 2)) u v ≤
            (D (addFun (hbar ω) (Kt ω))).internal (ball 0 (R / 2)) u v +
              ENNReal.ofReal (δ * Real.exp (xiGamma γ * h ω ρ))} ≤ η := by
  obtain ⟨ε₁, hε₁, hU⟩ := lemma23_uniform (γ := γ) (D := D) hD hR hρs hρ1 hK₁ hK₁B hδ hη
  refine ⟨ε₁ / C, div_pos hε₁ hC, fun ϕ ψ W z r hr Ξinv hZ Ω _ P _ B h hbar K Kt hc hsup hKt => ?_⟩
  have hCr0 : 0 ≤ C * r := (norm_nonneg _).trans (hZ.inv_norm_sub_le 0)
  have hCr : C * r ≤ ε₁ := by
    have := mul_le_mul_of_nonneg_left hr hC.le
    rwa [mul_div_cancel₀ _ hC.ne'] at this
  refine hU P Ξinv (zoomExt ϕ ψ z r R) B (C * r) h hbar K Kt hc hZ.nearId hZ.inv_norm_sub_le hCr
    hsup fun ω x hx => ?_
  rw [hKt ω x hx, sub_self, abs_zero]
  exact hCr0

/-- **[3] Lemma 2.3* on the zoom NIC spaces, unconditional package for D10.** For
`IsConfNbhd ϕ W V`, a left inverse `ψ` of `ϕ` on `W`, a compact `Kc ⊆ V` and `R > 0` (and `ρ`, `K₁`
as in Lemma 2.3*), there are `r₁, C > 0` with `C r₁ ≤ 1/32` such that
1. for every `z ∈ Kc` and `r ∈ (0, r₁]` there are an inverse `Ξinv` of the extension of the zoomed
   inverse map (`IsZoomExt`) and a NIC coupling `(h, h̄, K)` of `Ξinv` on `B_R` (increment constant
   `C r²`, `E sup_{B̄_{R/2}} |K − K(0)| ≤ C r`), with a measurable continuous `K̃` equal to `K` on
   `B̄_{3R/4}` and `0` off `B_R` (D9's `K̃`);
2. for all `δ, η > 0` there is `r₀ ∈ (0, r₁]` such that for every `r ≤ r₀`, every such `Ξinv` and
   every such coupling with any continuous `K̃ = K` on `B_{R/2}`, the bad event of Lemma 2.3* has
   probability at most `η`.

No hypothesis beyond the data: `NICInput` is discharged by `NIC.nicInput_holds`. -/
theorem lemma23_zoom_exists (hD : IsStrongLQGMetric γ D) {ϕ ψ : ℂ → ℂ} {W V : Set ℂ}
    (hϕ : IsConfNbhd ϕ W V) (hψ : ∀ x ∈ W, ψ (ϕ x) = x) {Kc : Set ℂ} (hKc : IsCompact Kc)
    (hKcV : Kc ⊆ V) {R : ℝ} (hR : 0 < R) {ρ : TestC}
    (hρs : tsupport (ρ : ℂ → ℝ) ⊆ closedBall 0 (R / 2)) (hρ1 : ∫ x, ρ x = 1)
    {K₁ : Set ℂ} (hK₁ : IsCompact K₁) (hK₁B : K₁ ⊆ ball 0 (R / 2)) :
    ∃ r₁ C : ℝ, 0 < r₁ ∧ 0 < C ∧ C * r₁ ≤ 1 / 32 ∧
    (∀ z ∈ Kc, ∀ r ∈ Ioc (0 : ℝ) r₁,
      ∃ Ξinv : ℂ → ℂ, IsZoomExt ϕ ψ W z r R C (zoomExt ϕ ψ z r R) Ξinv ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (h hbar : Ω → DistC) (K : Ω → ℂ → ℝ) (Kt : Ω → C(ℂ, ℝ)),
        IsNICCoupling P Ξinv (ball 0 R) (C * r ^ 2) h hbar K ∧
        Measurable (fun ω => supDev (K ω) (R / 2)) ∧
        ∫⁻ ω, supDev (K ω) (R / 2) ∂P ≤ ENNReal.ofReal (C * r) ∧
        Measurable Kt ∧ (∀ ω, ∀ x ∈ closedBall (0 : ℂ) (3 * R / 4), Kt ω x = K ω x) ∧
        ∀ ω x, R ≤ ‖x‖ → Kt ω x = 0) ∧
    ∀ δ : ℝ, 0 < δ → ∀ η : ℝ≥0∞, 0 < η → ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ r₁ ∧
      ∀ (z : ℂ) (r : ℝ), r ≤ r₀ →
      ∀ Ξinv : ℂ → ℂ, IsZoomExt ϕ ψ W z r R C (zoomExt ϕ ψ z r R) Ξinv →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ)
        (h hbar : Ω → DistC) (K : Ω → ℂ → ℝ) (Kt : Ω → C(ℂ, ℝ)),
        IsNICCoupling P Ξinv (ball 0 R) B h hbar K →
        ∫⁻ ω, supDev (K ω) (R / 2) ∂P ≤ ENNReal.ofReal (C * r) →
        (∀ ω, ∀ x ∈ ball (0 : ℂ) (R / 2), Kt ω x = K ω x) →
        P {ω | ¬ ∀ u ∈ K₁, ∀ v ∈ K₁,
        (D (addFun (hbar ω) (Kt ω))).internal (ball 0 (R / 2)) u v ≤
            (D (h ω)).internal (ball 0 (R / 2)) u v +
              ENNReal.ofReal (δ * Real.exp (xiGamma γ * h ω ρ)) ∧
        (D (h ω)).internal (ball 0 (R / 2)) u v ≤
            (D (addFun (hbar ω) (Kt ω))).internal (ball 0 (R / 2)) u v +
              ENNReal.ofReal (δ * Real.exp (xiGamma γ * h ω ρ))} ≤ η := by
  obtain ⟨r₁, C, hr₁, hC, hCr₁, hzoom⟩ := zoom_nic NIC.nicInput_holds hϕ hψ hKc hKcV hR
  refine ⟨r₁, C, hr₁, hC, hCr₁, fun z hz r hr => ?_, fun δ hδ η hη => ?_⟩
  · obtain ⟨Ξinv, hZ, Ω, mΩ, P, hP, h, hbar, K, hc, hmeas, hint⟩ := hzoom z hz r hr
    obtain ⟨Kt, hKtm, hKtK, hKt0⟩ := exists_measurable_contExt (ρ := 3 * R / 4) (R := R)
      (by positivity) (by linarith) hc.measurable fun ω => (hc.harmonic ω).continuousOn
    exact ⟨Ξinv, hZ, Ω, mΩ, P, hP, h, hbar, K, Kt, hc, hmeas, hint, hKtm, hKtK, hKt0⟩
  · obtain ⟨r₀, hr₀, hU⟩ := lemma23_zoom_uniform (γ := γ) (D := D) hD hR hρs hρ1 hK₁ hK₁B hδ hη hC
    refine ⟨min r₀ r₁, lt_min hr₀ hr₁, min_le_right _ _, fun z r hr Ξinv hZ Ω _ P _ B h hbar K Kt hc
      hsup hKt => ?_⟩
    exact hU ϕ ψ W z r (hr.trans (min_le_left _ _)) Ξinv hZ P B h hbar K Kt hc hsup hKt

end Zoom

end SmallGammaGeodesics.CC
