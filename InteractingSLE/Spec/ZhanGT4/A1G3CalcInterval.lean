/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3CalcClear
import InteractingSLE.Spec.ZhanGT4.DualSeedUniformBound

/-!
# Zhan's A.1, G3: uniform derivative scales on the extended own interval

Packet PROVE-A1-G3CALC (R48). Source: Astra, *Follow-up proofs*, §A.1.3 and §A.1.6 (`ig1_followup_proofs.txt`
L314–L340, L495–L497). A22's `exists_seed_interval_deriv_lower_right` and `exists_seed_interval_own_bounds_right`
(the reflected own map is analytic with derivative in `[e^{−L}, e^{L}]` on the seed interval) with the seed interval
`[V_lo, V_hi]` replaced by the extended interval `[V_lo, g_t(q) + W_t]` (`A1G3CalcClear`). The protected point `q`
itself is the right end; the real-flow order argument of A22 is used with `≤` and the case `x = g_t(q) + W_t` is the
protected estimate itself.

* **`exists_ext_interval_deriv_lower_right`**: clearance and the derivative lower bound of every local reflection;
* **`exists_ext_interval_own_bounds_right`**: clearance and `deriv F_t ∈ [e^{−L}, e^{L}]` on the extended interval,
  with constants chosen before the paths and times.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4.A1G3Calc

open QuantumZipper (H IsForwardSol fwdMap fwdHull)

open InteractingSLE.ZhanGT4

/-- **Uniform lower derivative bounds on the extended interval** `[V_lo(s), g_s(q) + W_s]` (A22's
`exists_seed_interval_deriv_lower_right` for the extended interval; the real segment `(0, q]` is `2δ`-far from `H₂`).
Both constants are chosen before the drivers, coordinates, times and image chains. -/
theorem exists_ext_interval_deriv_lower_right {H₁ H₂ : Set ℂ}
    (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂) {δ : ℝ} (hδ : 0 < δ)
    (hsepδ : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖)
    {q d : ℝ} (hq : 0 < q) (hd : 0 < d)
    (hqH : Disjoint (ball (q : ℂ) (2 * d)) (H₁ ∪ H₂))
    (hseg : ∀ a ∈ H₂, ∀ y : ℝ, 0 < y → y ≤ q → 2 * δ ≤ ‖a - y‖) :
    ∃ r γ : ℝ, 0 < r ∧ 0 < γ ∧
      ∀ (W₁ W₂ Vlo Vhi : ℝ → ℝ) (s t₂ : ℝ) (a₂ W₂' : ℝ → ℝ),
        Continuous W₁ → 0 ≤ s → W₁ 0 = 0 → ((W₁ 0 : ℝ) : ℂ) ∈ closure H₁ →
        ((W₂ 0 : ℝ) : ℂ) ∈ closure H₂ → q < W₂ 0 →
        fwdHull W₁ s ⊆ H₁ → fwdHull W₂ t₂ ⊆ H₂ →
        IsSeedCoordinate W₁ Vlo s → IsSeedCoordinate W₁ Vhi s →
        ImgData W₂ (fwdHull W₁ s) (fun z => fwdMap W₁ s z + W₁ s) t₂ a₂ W₂' →
        ∀ x ∈ uIcc (Vlo s) ((fwdMap W₁ s q).re + W₁ s),
          Disjoint (ball (x : ℂ) r)
            ((fun z => fwdMap W₁ s z + W₁ s) '' fwdHull W₂ t₂) ∧
          ∀ (R G : ℂ → ℂ) (ρ : ℝ),
            IsMapOut ((fun z => fwdMap W₁ s z + W₁ s) '' fwdHull W₂ t₂) R →
            0 < ρ → DifferentiableOn ℂ G (ball (x : ℂ) ρ) →
            EqOn G R (ball (x : ℂ) ρ ∩ H) →
            Real.exp (-(2 / γ ^ 2 * t₂)) ≤ ‖deriv G x‖ := by
  have hsepδ' : ∀ a ∈ H₁, ∀ z ∈ H₂, 2 * δ ≤ ‖a - z‖ := by
    intro a ha z hz
    rw [norm_sub_rev]
    exact hsepδ z hz a ha
  have hsep := disjoint_closure_of_le_norm_sub hδ hsepδ
  have hqH' : Disjoint (ball (q : ℂ) (2 * d)) (H₂ ∪ H₁) := by
    rwa [union_comm]
  obtain ⟨r, hr, hclear⟩ := exists_le_norm_fwdMap_sub_ext_interval_uniform
    hH₁ hH₂.2.1 hH₂.1 hδ hsepδ hq hseg
  obtain ⟨r₂, hr₂, hclear₂⟩ := exists_le_norm_fwdMap_uniform
    hH₂ hH₁.2.1 hH₁.1 hδ hsepδ'
  obtain ⟨γ, hγ, hprot⟩ := exists_le_norm_fwdMap_protected hH₂ hH₁ hsep.symm hd hqH'
  refine ⟨r, γ, hr, hγ, ?_⟩
  intro W₁ W₂ Vlo Vhi s t₂ a₂ W₂' hW₁ hs hW00 hW₁H hW₂H hqW hK₁ hK₂ hlo hhi h x hx
  have hWq : W₁ 0 < q := by rwa [hW00]
  have ht₂ : 0 ≤ t₂ := h.pos.le
  have hsI : s ∈ Icc (0 : ℝ) s := ⟨hs, le_rfl⟩
  have ht₂I : t₂ ∈ Icc (0 : ℝ) t₂ := ⟨ht₂, le_rfl⟩
  have h2d : 0 < 2 * d := by positivity
  obtain ⟨uq, huq⟩ := exists_isForwardSol_of_disjoint_ball_gen hW₁ hWq.ne' hs h2d
    (hqH.mono_right (hK₁.trans subset_union_left))
  have hxu : x ∈ uIcc (Vlo s) ((uq s).re + W₁ s) := by
    rwa [fwdMap_eq_of_isForwardSol hW₁ huq hsI] at hx
  have hclx : Disjoint (ball (x : ℂ) r)
      ((fun z => fwdMap W₁ s z + W₁ s) '' fwdHull W₂ t₂) := by
    rw [Set.disjoint_left]
    rintro z hz ⟨w, hw, rfl⟩
    have hb := hclear W₁ Vlo Vhi s hW₁ hW00 hW₁H hK₁ hlo hhi uq huq s hsI w (hK₂ hw) x hxu
    rw [mem_ball, dist_eq_norm] at hz
    exact not_lt_of_ge hb hz
  refine ⟨hclx, ?_⟩
  let p : ℝ := (uq s).re + W₁ s
  have hxp : x ≤ p := hxu.2.trans (max_le (hlo.lt_gmap hW₁ hWq huq hsI).le le_rfl)
  obtain ⟨u0, hu0, hW₂'0⟩ := h.exists_start_alive hW₁ hs (by linarith)
  have hqp := QuantumZipper.F1.isForwardSol_lt_of_lt hs hqW huq hu0 s hsI
  have hpW : p < W₂' 0 := by
    rw [hW₂'0]
    dsimp only [p]
    linarith only [hqp]
  have hτ0 : 0 ≤ a₂ t₂ := (h.mapsTo_clock_Icc ht₂I).1
  have hclx' : Disjoint (ball (x : ℂ) r) (fwdHull W₂' (a₂ t₂)) := by
    rwa [h.img t₂ ht₂I]
  obtain ⟨vx, hvx⟩ := exists_isForwardSol_of_disjoint_ball_gen h.contW'
    (hxp.trans_lt hpW).ne hτ0 hr hclx'
  have hgap : ∀ u ∈ Icc (0 : ℝ) t₂, γ ≤ ‖fwdMap W₂' (a₂ u) x‖ := by
    intro u hu
    obtain ⟨⟨vp, hvp⟩, hpγ⟩ := hprot W₂ W₁ s t₂ a₂ W₂' h hW₁ hs hW₁H hK₂ hK₁ u hu
    rw [fwdMap_eq_of_isForwardSol hW₁ huq hsI] at hvp hpγ
    rcases hxp.eq_or_lt with hxe | hxlt
    · rw [hxe]
      exact hpγ
    have hat := h.mapsTo_clock_Icc hu
    have hau : a₂ u ∈ Icc (0 : ℝ) (a₂ u) := ⟨hat.1, le_rfl⟩
    have hvx' := isForwardSol_restrict hvx hat.2
    have hord := QuantumZipper.F1.isForwardSol_lt_of_lt hat.1 hxlt hvx' hvp (a₂ u) hau
    have hneg := QuantumZipper.re_neg_isForwardSol_real h.contW' hat.1 hvp hpW (a₂ u) hau
    have him := im_eq_zero_of_isForwardSol_real h.contW' hvp hau
    have hvpnorm : ‖vp (a₂ u)‖ = -(vp (a₂ u)).re := by
      have he : vp (a₂ u) = (((vp (a₂ u)).re : ℝ) : ℂ) :=
        Complex.ext rfl (by simpa only [Complex.ofReal_im] using him)
      rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hneg]
      rfl
    rw [fwdMap_eq_of_isForwardSol h.contW' hvp hau, hvpnorm] at hpγ
    rw [fwdMap_eq_of_isForwardSol h.contW' hvx hat]
    exact hpγ.trans ((neg_le_neg hord.le).trans
      ((neg_le_abs _).trans (Complex.abs_re_le_norm _)))
  have hclr : ∀ u ∈ Icc (0 : ℝ) t₂,
      Disjoint (ball (W₂ u : ℂ) r₂)
        ((fun z => fwdMap W₂ u z + W₂ u) '' fwdHull W₁ s) := by
    intro u hu
    exact OwnData.disjoint_ball_of_le_norm fun z hz =>
      hclear₂ W₂ h.cont hW₂H t₂ hK₂ u hu z (hK₁ hz)
  intro R G ρ hR hρ hGd hGR
  have hmin : 0 < min ρ r := lt_min hρ hr
  exact h.exp_le_norm_deriv_reflection_at hr₂ hclr hvx hγ hgap ht₂I hR hmin
    (hclx.mono_left (ball_subset_ball (min_le_right _ _)))
    (hGd.mono (ball_subset_ball (min_le_left _ _)))
    (fun z hz => hGR ⟨ball_subset_ball (min_le_left _ _) hz.1, hz.2⟩)

/-- **Uniform real derivative scales of the reflected own map on the extended interval** (A22's
`exists_seed_interval_own_bounds_right` for `[V_lo(t), g_t(q) + W_t]`). -/
theorem exists_ext_interval_own_bounds_right {H₁ H₂ : Set ℂ}
    (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂) {δ : ℝ} (hδ : 0 < δ)
    (hsepδ : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖)
    {q d : ℝ} (hq : 0 < q) (hd : 0 < d)
    (hqH : Disjoint (ball (q : ℂ) (2 * d)) (H₁ ∪ H₂))
    (hseg : ∀ a ∈ H₂, ∀ y : ℝ, 0 < y → y ≤ q → 2 * δ ≤ ‖a - y‖) (Tm : ℝ) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧
      ∀ (W₁ W₂ Vlo Vhi : ℝ → ℝ) (T t₂ : ℝ) (a W' : ℝ → ℝ),
        OwnData W₁ (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) T a W' →
        Continuous W₂ → 0 < t₂ →
        ((W₁ 0 : ℝ) : ℂ) ∈ closure H₁ → ((W₂ 0 : ℝ) : ℂ) ∈ closure H₂ →
        q < W₂ 0 → t₂ ≤ Tm →
        fwdHull W₁ T ⊆ H₁ → fwdHull W₂ t₂ ⊆ H₂ →
        IsSeedCoordinate W₁ Vlo T → IsSeedCoordinate W₁ Vhi T →
        ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ uIcc (Vlo t) ((fwdMap W₁ t q).re + W₁ t),
          Disjoint (ball (x : ℂ) r)
            ((fun z => fwdMap W₁ t z + W₁ t) '' fwdHull W₂ t₂) ∧
          deriv (fun y : ℝ => (ownExt W₁ W' a
            (fun z => fwdMap W₂ t₂ z + W₂ t₂) t y).re) x ∈
              Icc (Real.exp (-L)) (Real.exp L) := by
  obtain ⟨r, γ, hr, hγ, hgeo⟩ :=
    exists_ext_interval_deriv_lower_right hH₁ hH₂ hδ hsepδ hq hd hqH hseg
  let L : ℝ := 2 / γ ^ 2 * |Tm|
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  refine ⟨r, L, hr, hL, ?_⟩
  intro W₁ W₂ Vlo Vhi T t₂ a W' h hW₂ ht₂ hW₁H hW₂H hqW ht₂m hK₁ hK₂ hlo hhi t ht x hx
  obtain ⟨a₂, W₂', h₂⟩ := exists_imgData hW₂ ht₂
    (isHPHull_fwdHull h.cont ht.1) (isMapOut_fwdMap_gen h.cont ht.1)
    (h.disj.symm.mono (closure_mono ((QuantumZipper.fwdHull_mono).1 ht.2)) Subset.rfl)
  have hKt : fwdHull W₁ t ⊆ H₁ :=
    ((QuantumZipper.fwdHull_mono).1 ht.2).trans hK₁
  obtain ⟨hclear, hlower⟩ := hgeo W₁ W₂ Vlo Vhi t t₂ a₂ W₂'
    h.cont ht.1 h.zero hW₁H hW₂H hqW hKt hK₂
    (hlo.restrict ht.2) (hhi.restrict ht.2) h₂ x hx
  obtain ⟨R, hR⟩ := (h.isHPHull_E ht).exists_isMapOut
  obtain ⟨hGd, -, -, -, -, hGR⟩ := h.ownExt_props ht hclear
  have hrl : 0 < r / 2 := by positivity
  have hb := hlower R _ (r / 2) hR hrl hGd (hGR R hR)
  have hd' := h.deriv_ownExt_real ht hr hclear
  have hnorm : ‖deriv (ownExt W₁ W' a
      (fun z => fwdMap W₂ t₂ z + W₂ t₂) t) x‖ =
      (deriv (ownExt W₁ W' a (fun z => fwdMap W₂ t₂ z + W₂ t₂) t) x).re := by
    have he : deriv (ownExt W₁ W' a (fun z => fwdMap W₂ t₂ z + W₂ t₂) t) x =
        (((deriv (ownExt W₁ W' a (fun z => fwdMap W₂ t₂ z + W₂ t₂) t) x).re : ℝ) : ℂ) :=
      Complex.ext rfl (by simpa only [Complex.ofReal_im] using hd'.1)
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd'.2.1]
    rfl
  have hdx := hGd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hrl))
  have hder := hdx.hasDerivAt.real_of_complex.deriv
  refine ⟨hclear, ?_⟩
  rw [hder]
  constructor
  · apply (Real.exp_le_exp.2 ?_).trans (hnorm ▸ hb)
    dsimp only [L]
    have hh : t₂ ≤ |Tm| := ht₂m.trans (le_abs_self Tm)
    exact neg_le_neg (mul_le_mul_of_nonneg_left hh (by positivity))
  · exact hd'.2.2.trans (Real.one_le_exp hL)

end InteractingSLE.ZhanGT4.A1G3Calc
