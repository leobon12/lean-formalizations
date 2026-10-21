import SmallGammaGeodesics.CC.Prop21NIC
import SmallGammaGeodesics.CC.Prop21Geom
import SmallGammaGeodesics.CC.Prop21Good

/-!
# [3] Prop 2.1: the localized bad event on the NIC spaces is uniformly small
(packet CC6b; CC0 Details D10)

Source: `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D10**, with CC6a's recipe
(`planning/handoffs/CC6a.md`, Details §2). For `IsConfNbhd ϕ W V`, a compact `K ⊆ V` and
`δ, η > 0` we choose, **before** the centre `z ∈ K` and the scale `r`:

* `m ≤ |ϕ'| ≤ M` on `K`, `ρ_K` with `B(z, ρ_K) ⊆ V`, and `s₀ = m/2`;
* `L₂` (`exists_circBump_tail`): `⟨h, ρ⟩ − h_{s₀}(0) < L₂` w.h.p., `ρ = σ_{0,s₀} * ψ_0`;
* `L₃`: `h_{|ϕ'(z)|}(0) − h_{s₀}(0) > −L₃` w.h.p. (`GM.Tight.prob_circleAvg_inc_le`);
* `S` (`GM.Tight.gm_S2_4b'`), `a` (`GM.Tight.gm_S2_4a`), `b` (`GM.Tight.gm_S2_4b`): diameter,
  crossing and modulus bounds, uniform over whole-plane GFFs, scales and centres;
* `R = 8 s₀ e^ℓ` with `ℓ` large: the crossing of `A_{R/8, R/4}` beats the diameter of `B̄_{2M}`
  (`h_{R/8}(0) − h_{s₀}(0) > −Qℓ/2` w.h.p.);
* CC6a's `lemma23_zoom_exists` (the NIC spaces) and `lemma23_uniform` (Lemma 2.3*).

`exists_nic_side`: there are `R, r₀ > 0` such that for every `z ∈ K` and `r ∈ (0, r₀]` the zoom
geometry holds (`ZoomGeom`) and there is a probability space carrying a normalized whole-plane
GFF `x` and a conformal coupling `(x, h̄, f)` of `(ϕ̃, W̃, ψ̃(B_{R/2}))` whose localized bad event
(`LocBad`) has probability at most `η`. On the intersection of the seven good events the bad event
fails (`not_locBad_of_good`), and each bad event has probability at most `η/8`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric

/-! ## Scalar helpers -/

/-- Reading the GM tightness events at scale `s` and centre `0`. -/
theorem lt_of_scaled {X : ContMetric} {s T : ℝ} (hs : 0 < s) {A B : Set ℂ}
    (h : ∀ u ∈ A, ∀ v ∈ B, X.1 ((s : ℂ) * u + 0, (s : ℂ) * v + 0) < T) {y y' : ℂ}
    (hy : y / (s : ℂ) ∈ A) (hy' : y' / (s : ℂ) ∈ B) : X.1 (y, y') < T := by
  have hs' : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  have := h _ hy _ hy'
  rwa [add_zero, add_zero, mul_div_cancel₀ _ hs', mul_div_cancel₀ _ hs'] at this

theorem norm_div_real_of_pos {s : ℝ} (hs : 0 < s) (y : ℂ) : ‖y / (s : ℂ)‖ = ‖y‖ / s := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]

/-- The crossing bound beats the diameter and the normalization (`hSA` of
`not_locBad_of_good`). -/
theorem bound_SA {ξ Q a S L₂ L₁ ℓ s₀ h₀ h₁ hρ δ₁ : ℝ} (hξ : 0 < ξ) (ha : 0 < a) (hs₀ : 0 < s₀)
    (hL₁ : L₁ = (S + 2 * s₀ ^ (-(ξ * Q)) * Real.exp (ξ * L₂)) / a)
    (hℓ : L₁ ≤ Real.exp (ξ * Q * ℓ / 2)) (h10 : -(Q / 2 * ℓ) < h₁ - h₀) (hρ0 : hρ - h₀ < L₂)
    (hδ₁1 : δ₁ ≤ 1) :
    S * (s₀ ^ (ξ * Q) * Real.exp (ξ * h₀)) + 2 * (δ₁ * Real.exp (ξ * hρ)) ≤
      a * (s₀ * Real.exp ℓ) ^ (ξ * Q) * Real.exp (ξ * h₁) := by
  set 𝔰 : ℝ := s₀ ^ (ξ * Q) * Real.exp (ξ * h₀) with h𝔰
  have hs₀p : 0 < s₀ ^ (ξ * Q) := Real.rpow_pos_of_pos hs₀ _
  have h𝔰0 : 0 < 𝔰 := mul_pos hs₀p (Real.exp_pos _)
  have hinv : s₀ ^ (-(ξ * Q)) * s₀ ^ (ξ * Q) = 1 := by
    rw [Real.rpow_neg hs₀.le, inv_mul_cancel₀ hs₀p.ne']
  -- the normalization: `e^{ξ⟨h,ρ⟩} ≤ s₀^{-ξQ} e^{ξ L₂} 𝔰`
  have hE : Real.exp (ξ * hρ) ≤ s₀ ^ (-(ξ * Q)) * Real.exp (ξ * L₂) * 𝔰 := by
    have h1 : Real.exp (ξ * hρ) ≤ Real.exp (ξ * h₀) * Real.exp (ξ * L₂) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith)
    calc Real.exp (ξ * hρ) ≤ Real.exp (ξ * h₀) * Real.exp (ξ * L₂) := h1
      _ = s₀ ^ (-(ξ * Q)) * Real.exp (ξ * L₂) * 𝔰 := by
          rw [h𝔰]
          calc Real.exp (ξ * h₀) * Real.exp (ξ * L₂)
              = (s₀ ^ (-(ξ * Q)) * s₀ ^ (ξ * Q)) * (Real.exp (ξ * h₀) * Real.exp (ξ * L₂)) := by
                rw [hinv, one_mul]
            _ = _ := by ring
  -- the crossing: `a e^{ξQℓ/2} 𝔰 ≤ a (s₀ e^ℓ)^{ξQ} e^{ξ h₁}`
  have hA : a * Real.exp (ξ * Q * ℓ / 2) * 𝔰 ≤
      a * (s₀ * Real.exp ℓ) ^ (ξ * Q) * Real.exp (ξ * h₁) := by
    rw [Real.mul_rpow hs₀.le (Real.exp_pos _).le, ← Real.exp_mul]
    have h2 : Real.exp (ξ * Q * ℓ / 2) * Real.exp (ξ * h₀) ≤
        Real.exp (ℓ * (ξ * Q)) * Real.exp (ξ * h₁) := by
      rw [← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith)
    calc a * Real.exp (ξ * Q * ℓ / 2) * 𝔰 =
        a * s₀ ^ (ξ * Q) * (Real.exp (ξ * Q * ℓ / 2) * Real.exp (ξ * h₀)) := by
          rw [h𝔰]; ring
      _ ≤ a * s₀ ^ (ξ * Q) * (Real.exp (ℓ * (ξ * Q)) * Real.exp (ξ * h₁)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  have hL₁a : a * L₁ = S + 2 * s₀ ^ (-(ξ * Q)) * Real.exp (ξ * L₂) := by
    rw [hL₁]; field_simp
  calc S * 𝔰 + 2 * (δ₁ * Real.exp (ξ * hρ))
      ≤ S * 𝔰 + 2 * (1 * (s₀ ^ (-(ξ * Q)) * Real.exp (ξ * L₂) * 𝔰)) := by
        gcongr
    _ = (a * L₁) * 𝔰 := by rw [hL₁a]; ring
    _ ≤ (a * Real.exp (ξ * Q * ℓ / 2)) * 𝔰 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hℓ ha.le) h𝔰0.le
    _ ≤ _ := hA

/-- The normalization of the target event (`hκδ` of `not_locBad_of_good`). -/
theorem bound_κδ {ξ Q m s₀ L₂ L₃ h₀ c₀ hρ nc δ δ₁ s₁ Λ₁ Λ₂ : ℝ} (hξ : 0 < ξ) (hQ : 0 < Q)
    (hm : 0 < m) (hs₀ : 0 < s₀) (hmc : m ≤ nc) (hδ : 0 < δ)
    (hΛ₁ : Λ₁ = Real.exp (ξ * L₃) * s₀ ^ (ξ * Q) * m ^ (-(ξ * Q)))
    (hΛ₂ : Λ₂ = Λ₁ * s₀ ^ (-(ξ * Q)) * Real.exp (ξ * L₂))
    (hc₀ : -L₃ < c₀ - h₀) (hρ0 : hρ - h₀ < L₂) (hs₁ : s₁ = δ / (4 * Λ₁))
    (hδ₁ : δ₁ ≤ δ / (2 * Λ₂)) :
    Real.exp (-(ξ * (c₀ + Q * Real.log nc))) *
      (2 * (s₁ * (s₀ ^ (ξ * Q) * Real.exp (ξ * h₀))) + δ₁ * Real.exp (ξ * hρ)) ≤ δ := by
  have hnc : 0 < nc := hm.trans_le hmc
  have hξQ : 0 < ξ * Q := mul_pos hξ hQ
  have hs₀p : 0 < s₀ ^ (ξ * Q) := Real.rpow_pos_of_pos hs₀ _
  have hΛ₁0 : 0 < Λ₁ := by rw [hΛ₁]; positivity
  have hΛ₂0 : 0 < Λ₂ := by rw [hΛ₂]; positivity
  set κ : ℝ := Real.exp (-(ξ * (c₀ + Q * Real.log nc))) with hκ
  -- `κ 𝔰 ≤ Λ₁`
  have hκ𝔰 : κ * (s₀ ^ (ξ * Q) * Real.exp (ξ * h₀)) ≤ Λ₁ := by
    have h1 : κ * Real.exp (ξ * h₀) ≤ Real.exp (ξ * L₃) * nc ^ (-(ξ * Q)) := by
      rw [hκ, ← Real.exp_add, Real.rpow_def_of_pos hnc, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith)
    have h2 : nc ^ (-(ξ * Q)) ≤ m ^ (-(ξ * Q)) :=
      Real.rpow_le_rpow_of_nonpos hm hmc (by linarith)
    calc κ * (s₀ ^ (ξ * Q) * Real.exp (ξ * h₀)) = s₀ ^ (ξ * Q) * (κ * Real.exp (ξ * h₀)) := by
          ring
      _ ≤ s₀ ^ (ξ * Q) * (Real.exp (ξ * L₃) * m ^ (-(ξ * Q))) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity)))
            hs₀p.le
      _ = Λ₁ := by rw [hΛ₁]; ring
  -- `κ E ≤ Λ₂`
  have hκE : κ * Real.exp (ξ * hρ) ≤ Λ₂ := by
    have h1 : Real.exp (ξ * hρ) ≤ Real.exp (ξ * h₀) * Real.exp (ξ * L₂) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith)
    have hinv : s₀ ^ (-(ξ * Q)) * s₀ ^ (ξ * Q) = 1 := by
      rw [Real.rpow_neg hs₀.le, inv_mul_cancel₀ hs₀p.ne']
    calc κ * Real.exp (ξ * hρ) ≤ κ * (Real.exp (ξ * h₀) * Real.exp (ξ * L₂)) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = (κ * (s₀ ^ (ξ * Q) * Real.exp (ξ * h₀))) * (s₀ ^ (-(ξ * Q)) * Real.exp (ξ * L₂)) := by
          calc κ * (Real.exp (ξ * h₀) * Real.exp (ξ * L₂))
              = κ * ((s₀ ^ (-(ξ * Q)) * s₀ ^ (ξ * Q)) *
                  (Real.exp (ξ * h₀) * Real.exp (ξ * L₂))) := by rw [hinv, one_mul]
            _ = _ := by ring
      _ ≤ Λ₁ * (s₀ ^ (-(ξ * Q)) * Real.exp (ξ * L₂)) :=
          mul_le_mul_of_nonneg_right hκ𝔰 (by positivity)
      _ = Λ₂ := by rw [hΛ₂]; ring
  calc κ * (2 * (s₁ * (s₀ ^ (ξ * Q) * Real.exp (ξ * h₀))) + δ₁ * Real.exp (ξ * hρ))
      = 2 * s₁ * (κ * (s₀ ^ (ξ * Q) * Real.exp (ξ * h₀))) + δ₁ * (κ * Real.exp (ξ * hρ)) := by
        ring
    _ ≤ 2 * s₁ * Λ₁ + δ / (2 * Λ₂) * Λ₂ := by
        have hs₁0 : 0 ≤ s₁ := by rw [hs₁]; positivity
        gcongr
    _ = δ := by
        rw [hs₁]
        field_simp
        ring

/-! ## The NIC side of [3] Prop 2.1 -/

variable {γ : ℝ} {D : DistC → ContMetric}

/-- **The localized bad event on the NIC spaces is uniformly small** (D10). -/
theorem exists_nic_side (hγ : 0 < γ) (hD : GaussianLQG.IsCanonicalLQGMetric γ D)
    {ϕ ψ : ℂ → ℂ} {W V : Set ℂ} (hϕ : IsConfNbhd ϕ W V) (hψ : ∀ x ∈ W, ψ (ϕ x) = x)
    {K : Set ℂ} (hK : IsCompact K) (hKV : K ⊆ V) {δ : ℝ} (hδ : 0 < δ) {η : ℝ} (hη : 0 < η) :
    ∃ R r₀ : ℝ, 0 < R ∧ 0 < r₀ ∧ ∀ z ∈ K, ∀ r ∈ Ioc (0 : ℝ) r₀, ZoomGeom ϕ ψ W V z r R ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (x hb : Ω → DistC) (f : Ω → C(ℂ, ℝ)),
        IsNormalizedWPGFF x P ∧ IsWholePlaneGFF hb P ∧ Measurable f ∧
        (∀ᵐ ω ∂P, IsConfCoupling γ (zoomMap ϕ z r) (zoomSet z r W)
          (zoomPsi ϕ ψ z r '' ball 0 (R / 2)) (x ω) (hb ω) (f ω)) ∧
        P {ω | LocBad δ (zoomPsi ϕ ψ z r '' sphere 0 (R / 4))
          (fun u v => ENNReal.ofReal ((D (x ω)).1 (u, v)))
          ((D (x ω)).internal ((fun w => deriv ϕ z * w) ⁻¹' ball 0 (R / 2)))
          (confMetric D (zoomMap ϕ z r) (zoomPsi ϕ ψ z r '' ball 0 (R / 2)) (hb ω) (f ω))} ≤
          ENNReal.ofReal η := by
  /- 1. Constants, chosen before the centre and the scale. -/
  have hDs := hD.1
  have hDw := GM.gm_eq1_15 hγ hDs
  have hξ : 0 < xiGamma γ := GM.xiGamma_pos hγ
  have hQ : 0 < Q γ := Q_pos hγ
  obtain ⟨m, M₀, hm, hmM₀⟩ := hϕ.exists_deriv_bounds hK hKV
  set M : ℝ := max (max M₀ 1) m with hMdef
  have hM1 : 1 ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  have hmM : m ≤ M := le_max_right _ _
  have hcK : ∀ z ∈ K, m ≤ ‖deriv ϕ z‖ ∧ ‖deriv ϕ z‖ ≤ M := fun z hz =>
    ⟨(hmM₀ z hz).1, (hmM₀ z hz).2.trans ((le_max_left _ _).trans (le_max_left _ _))⟩
  obtain ⟨ρK, hρK, hρKV⟩ := hK.exists_thickening_subset_open hϕ.isOpen_V hKV
  have hballK : ∀ z ∈ K, ball z ρK ⊆ V := fun z hz =>
    (ball_subset_thickening hz ρK).trans hρKV
  set s₀ : ℝ := m / 2 with hs₀def
  have hs₀ : 0 < s₀ := by positivity
  have hs₀m : s₀ < m := by rw [hs₀def]; linarith
  set η' : ℝ := η / 8 with hη'def
  have hη' : 0 < η' := by positivity
  have hη'E : (0 : ℝ≥0∞) < ENNReal.ofReal η' := ENNReal.ofReal_pos.2 hη'
  -- the normalization constants
  obtain ⟨L₂, hL₂, hL₂P⟩ := exists_circBump_tail hs₀ hη'
  set ℓc : ℝ := Real.log (M / s₀) with hℓcdef
  have hℓc : 0 < ℓc := Real.log_pos (by rw [lt_div_iff₀ hs₀]; linarith)
  set L₃ : ℝ := Real.sqrt (2 * ℓc * (|Real.log η'| + 1)) with hL₃def
  have hL₃0 : 0 ≤ L₃ := Real.sqrt_nonneg _
  have hL₃sq : L₃ ^ 2 = 2 * ℓc * (|Real.log η'| + 1) :=
    Real.sq_sqrt (by positivity)
  -- the GM tightness constants (uniform over fields, scales and centres)
  obtain ⟨S, hS, hSP⟩ := GM.Tight.gm_S2_4b' hDw (isCompact_closedBall (0 : ℂ) (2 * M / s₀)) hη'E
  have hdisj : Disjoint (closedBall (0 : ℂ) 1) (sphere 0 2 ∪ sphere 0 4) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    have h1 := mem_closedBall_zero_iff.1 hx
    rcases hx' with h | h <;> rw [mem_sphere_zero_iff_norm] at h <;> linarith
  obtain ⟨a, ha, haP⟩ := GM.Tight.gm_S2_4a hDw (isCompact_closedBall (0 : ℂ) 1)
    ((isCompact_sphere 0 2).union (isCompact_sphere 0 4)) hdisj hη'E
  set L₁ : ℝ := (S + 2 * s₀ ^ (-(xiGamma γ * Q γ)) * Real.exp (xiGamma γ * L₂)) / a with hL₁def
  -- the radius `R = 8 s₀ e^ℓ`
  obtain ⟨ℓ, hℓ0, hℓ1, hℓ2, hℓ3⟩ : ∃ ℓ : ℝ, 0 < ℓ ∧ L₁ ≤ Real.exp (xiGamma γ * Q γ * ℓ / 2) ∧
      Real.exp (-(Q γ ^ 2 * ℓ / 8)) ≤ η' ∧ 32 * (M + 1) ≤ 8 * s₀ * Real.exp ℓ := by
    have e1 : ∀ᶠ ℓ in atTop, L₁ ≤ Real.exp (xiGamma γ * Q γ * ℓ / 2) := by
      have : Tendsto (fun ℓ : ℝ => xiGamma γ * Q γ * ℓ / 2) atTop atTop := by
        have h := tendsto_id.const_mul_atTop (show 0 < xiGamma γ * Q γ / 2 by positivity)
        refine h.congr fun ℓ => ?_
        simp only [id]
        ring
      exact (Real.tendsto_exp_atTop.comp this).eventually_ge_atTop L₁
    have e2 : ∀ᶠ ℓ in atTop, Real.exp (-(Q γ ^ 2 * ℓ / 8)) ≤ η' := by
      have : Tendsto (fun ℓ : ℝ => Q γ ^ 2 * ℓ / 8) atTop atTop := by
        have h := tendsto_id.const_mul_atTop (show 0 < Q γ ^ 2 / 8 by positivity)
        refine h.congr fun ℓ => ?_
        simp only [id]
        ring
      exact (Real.tendsto_exp_neg_atTop_nhds_zero.comp this).eventually (ge_mem_nhds hη')
    have e3 : ∀ᶠ ℓ in atTop, 32 * (M + 1) ≤ 8 * s₀ * Real.exp ℓ :=
      (Real.tendsto_exp_atTop.const_mul_atTop (by positivity)).eventually_ge_atTop _
    obtain ⟨ℓ, h0, h1, h2, h3⟩ := ((eventually_gt_atTop 0).and (e1.and (e2.and e3))).exists
    exact ⟨ℓ, h0, h1, h2, h3⟩
  set R : ℝ := 8 * s₀ * Real.exp ℓ with hRdef
  have hR : 0 < R := by positivity
  have hR8 : R / 8 = s₀ * Real.exp ℓ := by rw [hRdef]; ring
  have hR8pos : 0 < R / 8 := by positivity
  have hMR : M + 1 < R / 4 := by linarith
  have h2MR8 : 2 * M ≤ R / 8 := by linarith
  -- CC6a's test function and compact set
  set ρ : TestC := CircleAvg.circBump 0 0 s₀ with hρdef
  have hρs : tsupport (ρ : ℂ → ℝ) ⊆ closedBall 0 (R / 2) :=
    tsupport_circBump_zero_subset hs₀.le (by rw [hs₀def]; linarith)
  have hρ1 : ∫ x, ρ x = 1 := CircleAvg.integral_circBump 0 0 s₀
  have hK₁ : IsCompact (closedBall (0 : ℂ) (R / 4)) := isCompact_closedBall _ _
  have hK₁B : closedBall (0 : ℂ) (R / 4) ⊆ ball 0 (R / 2) := closedBall_subset_ball (by linarith)
  -- the target-dependent constants
  set Λ₁ : ℝ := Real.exp (xiGamma γ * L₃) * s₀ ^ (xiGamma γ * Q γ) * m ^ (-(xiGamma γ * Q γ))
    with hΛ₁def
  set Λ₂ : ℝ := Λ₁ * s₀ ^ (-(xiGamma γ * Q γ)) * Real.exp (xiGamma γ * L₂) with hΛ₂def
  have hΛ₁ : 0 < Λ₁ := by positivity
  have hΛ₂ : 0 < Λ₂ := by positivity
  set s₁ : ℝ := δ / (4 * Λ₁) with hs₁def
  have hs₁ : 0 < s₁ := by positivity
  set δ₁ : ℝ := min 1 (δ / (2 * Λ₂)) with hδ₁def
  have hδ₁ : 0 < δ₁ := lt_min one_pos (by positivity)
  have hδ₁1 : δ₁ ≤ 1 := by rw [hδ₁def]; exact min_le_left _ _
  have hδ₁2 : δ₁ ≤ δ / (2 * Λ₂) := by rw [hδ₁def]; exact min_le_right _ _
  obtain ⟨b, hb, hbP⟩ := GM.Tight.gm_S2_4b hDw (isCompact_closedBall (0 : ℂ) (2 * M / s₀)) hs₁
    hη'E
  -- CC6a: the NIC spaces and Lemma 2.3*
  obtain ⟨r₁, C, hr₁, hC, hCr₁, hzoom, -⟩ :=
    lemma23_zoom_exists hDs hϕ hψ hK hKV hR hρs hρ1 hK₁ hK₁B
  obtain ⟨ε₁, hε₁, hU⟩ := lemma23_uniform (γ := γ) (D := D) hDs hR hρs hρ1 hK₁ hK₁B hδ₁ hη'E
  set C' : ℝ := C * (1 + 2 * Q γ) with hC'def
  have hC' : 0 < C' := by positivity
  set r₀ : ℝ := min r₁ (min (ε₁ / C') (min (b * s₀ / C) (min (1 / (C * R ^ 2))
    (m * ρK / (R / 2 + 1) / 2)))) with hr₀def
  have hr₀ : 0 < r₀ := by
    refine lt_min hr₁ (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) ?_)))
    positivity
  refine ⟨R, r₀, hR, hr₀, fun z hz r hr => ?_⟩
  /- 2. The zoom at `(z, r)`. -/
  obtain ⟨hr0, hrr₀⟩ := hr
  have hr₀₁ : r₀ ≤ r₁ := min_le_left _ _
  have hr₀ε : r₀ ≤ ε₁ / C' := (min_le_right _ _).trans (min_le_left _ _)
  have hr₀b : r₀ ≤ b * s₀ / C :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr₀R : r₀ ≤ 1 / (C * R ^ 2) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hr₀ρ : r₀ ≤ m * ρK / (R / 2 + 1) / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _)))
  have hrr₁ : r ≤ r₁ := hrr₀.trans hr₀₁
  obtain ⟨Ξinv, hZ, Ω, mΩ, P, hP, h, hbar, Kn, Kt, hc, -, hsup, hKtm, hKtK, -⟩ :=
    hzoom z hz r ⟨hr0, hrr₁⟩
  have hCr0 : 0 ≤ C * r := by positivity
  have hCr32 : C * r ≤ 1 / 32 := (mul_le_mul_of_nonneg_left hrr₁ hC.le).trans hCr₁
  have hCrb : C * r ≤ b * s₀ := by
    have := mul_le_mul_of_nonneg_left (hrr₀.trans hr₀b) hC.le
    rwa [mul_div_cancel₀ _ hC.ne'] at this
  have hCrR : C * r * R ^ 2 ≤ 1 := by
    have := mul_le_mul_of_nonneg_left (hrr₀.trans hr₀R) (show 0 ≤ C * R ^ 2 by positivity)
    rw [mul_one_div_cancel (by positivity)] at this
    calc C * r * R ^ 2 = C * R ^ 2 * r := by ring
      _ ≤ 1 := this
  have hC'r : C' * r ≤ ε₁ := by
    have := mul_le_mul_of_nonneg_left (hrr₀.trans hr₀ε) hC'.le
    rwa [mul_div_cancel₀ _ hC'.ne'] at this
  have hCC' : C * r ≤ C' * r := by
    rw [hC'def]
    have : C ≤ C * (1 + 2 * Q γ) := le_mul_of_one_le_right hC.le (by linarith)
    exact mul_le_mul_of_nonneg_right this hr0.le
  have hrρ : r * (R / 2 + 1) < m * ρK := by
    have h1 : r ≤ m * ρK / (R / 2 + 1) / 2 := hrr₀.trans hr₀ρ
    have h2 : r * (R / 2 + 1) ≤ m * ρK / 2 := by
      have hR1 : 0 < R / 2 + 1 := by positivity
      calc r * (R / 2 + 1) ≤ m * ρK / (R / 2 + 1) / 2 * (R / 2 + 1) :=
            mul_le_mul_of_nonneg_right h1 hR1.le
        _ = m * ρK / 2 := by field_simp
    have : 0 < m * ρK := by positivity
    linarith
  set c : ℂ := deriv ϕ z with hcdef
  have hmc : m ≤ ‖c‖ := (hcK z hz).1
  have hcM : ‖c‖ ≤ M := (hcK z hz).2
  have hgeom : ZoomGeom ϕ ψ W V z r R :=
    zoomGeom_of hϕ hr0 hR hZ hm hmc hcM hMR hCr0 (by linarith) hCrR (hballK z hz) hrρ
  have hcR : ‖c‖ + C * r ≤ R := by linarith
  -- the NIC fields
  obtain ⟨jl, hjl, hjlb⟩ := exists_zoomJac γ hZ hCr0 (by linarith)
  have hKtB : ∀ ω, ∀ x ∈ ball (0 : ℂ) (R / 2), Kt ω x = Kn ω x := fun ω x hx =>
    hKtK ω x (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)) hx)
  obtain ⟨hx, hhb', hfm, hcoup, hdist, hint, hconf, hlen⟩ :=
    nic_zoom_fields (D := D) hγ hD hϕ hψ hr0 hR hZ (by linarith) hgeom.sub hc hKtm hKtB hjl
  refine ⟨hgeom, Ω, mΩ, P, hP, _, _, _, hx, hhb', hfm, hcoup, ?_⟩
  /- 3. The seven bad events. -/
  have hh := hc.isWholePlaneGFF
  set B1 : Set Ω := {ω | ¬ ∀ u ∈ closedBall (0 : ℂ) (R / 4), ∀ v ∈ closedBall (0 : ℂ) (R / 4),
      (D (addFun (hbar ω) (Kt ω + jl))).internal (ball 0 (R / 2)) u v ≤
          (D (h ω)).internal (ball 0 (R / 2)) u v +
            ENNReal.ofReal (δ₁ * Real.exp (xiGamma γ * h ω ρ)) ∧
      (D (h ω)).internal (ball 0 (R / 2)) u v ≤
          (D (addFun (hbar ω) (Kt ω + jl))).internal (ball 0 (R / 2)) u v +
            ENNReal.ofReal (δ₁ * Real.exp (xiGamma γ * h ω ρ))} with hB1def
  have hB1 : P B1 ≤ ENNReal.ofReal η' := by
    refine hU P Ξinv (zoomExt ϕ ψ z r R) (C * r ^ 2) (C' * r) h hbar Kn (fun ω => Kt ω + jl) hc
      (hZ.nearId.mono hCC') (fun x => (hZ.inv_norm_sub_le x).trans hCC') hC'r
      (hsup.trans (ENNReal.ofReal_le_ofReal hCC')) fun ω x hx => ?_
    rw [ContinuousMap.add_apply, hKtB ω x hx, add_sub_cancel_left]
    refine (hjlb x).trans ?_
    rw [abs_of_pos hQ, hC'def]
    linarith
  set B2 : Set Ω := {ω | ¬ ∀ u ∈ closedBall (0 : ℂ) 1, ∀ v ∈ sphere (0 : ℂ) 2 ∪ sphere 0 4,
      a * (R / 8) ^ (xiGamma γ * Q γ) * Real.exp (xiGamma γ * circleAvg (h ω) (R / 8) 0) <
        (D (h ω)).1 (((R / 8 : ℝ) : ℂ) * u + 0, ((R / 8 : ℝ) : ℂ) * v + 0)} with hB2def
  have hB2 : P B2 ≤ ENNReal.ofReal η' := (haP P h hh (R / 8) hR8pos 0).le
  set B3 : Set Ω := {ω | ¬ ∀ u ∈ closedBall (0 : ℂ) (2 * M / s₀),
      ∀ v ∈ closedBall (0 : ℂ) (2 * M / s₀),
      (D (h ω)).1 ((s₀ : ℂ) * u + 0, (s₀ : ℂ) * v + 0) <
        S * s₀ ^ (xiGamma γ * Q γ) * Real.exp (xiGamma γ * circleAvg (h ω) s₀ 0)} with hB3def
  have hB3 : P B3 ≤ ENNReal.ofReal η' := (hSP P h hh s₀ hs₀ 0).le
  set B4 : Set Ω := {ω | ¬ ∀ u ∈ closedBall (0 : ℂ) (2 * M / s₀),
      ∀ v ∈ closedBall (0 : ℂ) (2 * M / s₀), ‖u - v‖ ≤ b →
      (D (h ω)).1 ((s₀ : ℂ) * u + 0, (s₀ : ℂ) * v + 0) <
        s₁ * s₀ ^ (xiGamma γ * Q γ) * Real.exp (xiGamma γ * circleAvg (h ω) s₀ 0)} with hB4def
  have hB4 : P B4 ≤ ENNReal.ofReal η' := (hbP P h hh s₀ hs₀ 0).le
  set B5 : Set Ω := {ω | circleAvg (h ω) (R / 8) 0 - circleAvg (h ω) s₀ 0 ≤ -(Q γ / 2 * ℓ)}
    with hB5def
  have hB5 : P B5 ≤ ENNReal.ofReal η' := by
    have hlt : s₀ < R / 8 := by
      rw [hR8]
      exact lt_mul_of_one_lt_right hs₀ (Real.one_lt_exp_iff.2 hℓ0)
    refine (GM.Tight.prob_circleAvg_inc_le hh hs₀ hlt 0 (by positivity)).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq_of_le ?_ hℓ2))
    rw [hR8, mul_div_cancel_left₀ _ hs₀.ne', Real.log_exp]
    congr 1
    field_simp
    ring
  set B6 : Set Ω := {ω | L₂ ≤ h ω ρ - circleAvg (h ω) s₀ 0} with hB6def
  have hB6 : P B6 ≤ ENNReal.ofReal η' := hL₂P P h hh
  set B7 : Set Ω := {ω | circleAvg (h ω) ‖c‖ 0 - circleAvg (h ω) s₀ 0 ≤ -L₃} with hB7def
  have hB7 : P B7 ≤ ENNReal.ofReal η' := by
    have hlt : s₀ < ‖c‖ := hs₀m.trans_le hmc
    refine (GM.Tight.prob_circleAvg_inc_le hh hs₀ hlt 0 hL₃0).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hlc : 0 < Real.log (‖c‖ / s₀) := Real.log_pos (by rw [lt_div_iff₀ hs₀]; linarith)
    have hlcM : Real.log (‖c‖ / s₀) ≤ ℓc :=
      Real.log_le_log (div_pos (hm.trans_le hmc) hs₀) (div_le_div_of_nonneg_right hcM hs₀.le)
    have h1 : -L₃ ^ 2 / (2 * Real.log (‖c‖ / s₀)) ≤ Real.log η' := by
      rw [neg_div, neg_le, le_div_iff₀ (by positivity), hL₃sq]
      have h2 : -Real.log η' ≤ |Real.log η'| + 1 := by
        linarith [neg_le_abs (Real.log η')]
      have h3 : 0 ≤ |Real.log η'| + 1 := by positivity
      calc -Real.log η' * (2 * Real.log (‖c‖ / s₀))
          ≤ (|Real.log η'| + 1) * (2 * Real.log (‖c‖ / s₀)) :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ ≤ (|Real.log η'| + 1) * (2 * ℓc) := mul_le_mul_of_nonneg_left (by linarith) h3
        _ = 2 * ℓc * (|Real.log η'| + 1) := by ring
    calc Real.exp (-L₃ ^ 2 / (2 * Real.log (‖c‖ / s₀))) ≤ Real.exp (Real.log η') :=
          Real.exp_le_exp.2 h1
      _ = η' := Real.exp_log hη'
  /- 4. Off the bad events, the localized event fails. -/
  have hincl : {ω | LocBad δ (zoomPsi ϕ ψ z r '' sphere 0 (R / 4))
      (fun u v => ENNReal.ofReal ((D (zoomNorm c (h ω))).1 (u, v)))
      ((D (zoomNorm c (h ω))).internal ((fun w => c * w) ⁻¹' ball 0 (R / 2)))
      (confMetric D (zoomMap ϕ z r) (zoomPsi ϕ ψ z r '' ball 0 (R / 2))
        (addConst (hbar ω) (-circleAvg (h ω) ‖c‖ 0))
        ((Kt ω + jl) + ContinuousMap.const ℂ (Q γ * Real.log ‖c⁻¹‖)))} ≤ᵐ[P]
      (((((B1 ∪ B2) ∪ B3) ∪ B4) ∪ B5) ∪ B6) ∪ B7 := by
    filter_upwards [hdist, hint, hconf, hlen] with ω h1 h2 h3 h4 hbad
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    obtain ⟨⟨⟨⟨⟨⟨n1, n2⟩, n3⟩, n4⟩, n5⟩, n6⟩, n7⟩ := hnot
    rw [hB1def, mem_ofPred_eq, not_not] at n1
    rw [hB2def, mem_ofPred_eq, not_not] at n2
    rw [hB3def, mem_ofPred_eq, not_not] at n3
    rw [hB4def, mem_ofPred_eq, not_not] at n4
    rw [hB5def, mem_ofPred_eq, not_le] at n5
    rw [hB6def, mem_ofPred_eq, not_le] at n6
    rw [hB7def, mem_ofPred_eq, not_le] at n7
    set h₀ : ℝ := circleAvg (h ω) s₀ 0 with hh₀
    set 𝔰 : ℝ := s₀ ^ (xiGamma γ * Q γ) * Real.exp (xiGamma γ * h₀) with h𝔰def
    set A : ℝ := a * (R / 8) ^ (xiGamma γ * Q γ) * Real.exp (xiGamma γ * circleAvg (h ω) (R / 8) 0)
      with hAdef
    set κ : ℝ := Real.exp (-(xiGamma γ * (circleAvg (h ω) ‖c‖ 0 + Q γ * Real.log ‖c‖)))
      with hκdef
    have hmem2M : ∀ y ∈ closedBall (0 : ℂ) (2 * M),
        y / (s₀ : ℂ) ∈ closedBall (0 : ℂ) (2 * M / s₀) :=
      fun y hy => by
        rw [mem_closedBall_zero_iff, norm_div_real_of_pos hs₀]
        exact div_le_div_of_nonneg_right (mem_closedBall_zero_iff.1 hy) hs₀.le
    have hsc : ∀ {t : ℝ}, 0 < t → ∀ y : ℂ, ((t : ℝ) : ℂ) * (y / (t : ℂ)) + 0 = y := fun ht y => by
      rw [add_zero, mul_div_cancel₀ _ (Complex.ofReal_ne_zero.2 ht.ne')]
    refine not_locBad_of_good (Mc := (D (addFun (hbar ω) (Kt ω + jl))).internal (ball 0 (R / 2)))
      (R := R) (M := M) (Cr := C * r) (κ := κ) (δ₁ := δ₁) (E := Real.exp (xiGamma γ * h ω ρ))
      (S := S) (A := A) (s₁ := s₁) (𝔰 := 𝔰) h4 hR (by linarith) hcM (by linarith)
      (Real.exp_pos _) (mul_nonneg hδ₁.le (Real.exp_pos _).le) (fun u v => by rw [h1 u v])
      (fun u v => h2 u v) (fun u _ v _ => h3 u v) (fun u hu => zoomMap_eq_inv hR hZ hcR hu)
      hZ.inv_norm_sub_le hgeom.map_T n1 (fun y hy y' hy' => ?_) (fun y hy w hw => ?_)
      (fun y hy y' hy' hyy' => ?_) ?_ ?_ hbad
    · -- diameter
      have := lt_of_scaled hs₀ n3 (hmem2M y hy) (hmem2M y' hy')
      rw [h𝔰def]
      linarith
    · -- crossing
      have hy1 : y / ((R / 8 : ℝ) : ℂ) ∈ closedBall (0 : ℂ) 1 := by
        rw [mem_closedBall_zero_iff, norm_div_real_of_pos hR8pos, div_le_one hR8pos]
        exact (mem_closedBall_zero_iff.1 hy).trans h2MR8
      have hw1 : w / ((R / 8 : ℝ) : ℂ) ∈ sphere (0 : ℂ) 2 ∪ sphere 0 4 := by
        rcases hw with hw | hw <;> rw [mem_sphere_zero_iff_norm] at hw
        · left
          rw [mem_sphere_zero_iff_norm, norm_div_real_of_pos hR8pos, hw]
          field_simp
          ring
        · right
          rw [mem_sphere_zero_iff_norm, norm_div_real_of_pos hR8pos, hw]
          field_simp
          ring
      have := n2 _ hy1 _ hw1
      rwa [hsc hR8pos, hsc hR8pos] at this
    · -- modulus
      have hb' : ‖y / (s₀ : ℂ) - y' / (s₀ : ℂ)‖ ≤ b := by
        rw [← sub_div, norm_div_real_of_pos hs₀, div_le_iff₀ hs₀]
        linarith
      have := n4 _ (hmem2M y hy) _ (hmem2M y' hy') hb'
      rw [hsc hs₀, hsc hs₀] at this
      rw [h𝔰def]
      linarith
    · -- the crossing beats the diameter
      have := bound_SA (Q := Q γ) (h₁ := circleAvg (h ω) (R / 8) 0) hξ ha hs₀ hL₁def hℓ1 n5 n6
        hδ₁1
      rw [← hR8, ← h𝔰def] at this
      rw [hAdef]
      exact this
    · -- the target normalization
      exact bound_κδ hξ hQ hm hs₀ hmc hδ hΛ₁def hΛ₂def n7 n6 hs₁def hδ₁2
  /- 5. The union bound. -/
  have hsum : P ((((((B1 ∪ B2) ∪ B3) ∪ B4) ∪ B5) ∪ B6) ∪ B7) ≤ 7 * ENNReal.ofReal η' := by
    calc P ((((((B1 ∪ B2) ∪ B3) ∪ B4) ∪ B5) ∪ B6) ∪ B7)
        ≤ P B1 + P B2 + P B3 + P B4 + P B5 + P B6 + P B7 := by
          refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
          refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
          refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
          refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
          refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
          exact measure_union_le _ _
      _ ≤ ENNReal.ofReal η' + ENNReal.ofReal η' + ENNReal.ofReal η' + ENNReal.ofReal η' +
          ENNReal.ofReal η' + ENNReal.ofReal η' + ENNReal.ofReal η' := by
          gcongr
      _ = 7 * ENNReal.ofReal η' := by ring
  calc _ ≤ P ((((((B1 ∪ B2) ∪ B3) ∪ B4) ∪ B5) ∪ B6) ∪ B7) := measure_mono_ae hincl
    _ ≤ 7 * ENNReal.ofReal η' := hsum
    _ = ENNReal.ofReal (7 * η') := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal (by rw [hη'def]; linarith)

end SmallGammaGeodesics.CC
