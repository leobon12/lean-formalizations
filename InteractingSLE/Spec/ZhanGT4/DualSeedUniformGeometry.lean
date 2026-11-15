/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedUniformOrder

/-!
# Uniform derivative lower bounds on the seed-coordinate interval

Packet PROVE-ZHAN-GT4-A22. A protected point between the enclosures stays
between every seed coordinate and the other source. Real-flow order carries
its uniform image gap to the entire seed interval. The transposed-time
derivative estimate then has one enclosure-dependent constant throughout.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull)

/-- Uniform lower derivative bounds throughout the seed interval, with the
other curve's source to the right of a protected point. Both constants are
chosen before the drivers, coordinates, times, and image chains. -/
theorem exists_seed_interval_deriv_lower_right {H₁ H₂ : Set ℂ}
    (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂) {δ : ℝ} (hδ : 0 < δ)
    (hsepδ : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖)
    {q d : ℝ} (hd : 0 < d)
    (hqH : Disjoint (ball (q : ℂ) (2 * d)) (H₁ ∪ H₂)) :
    ∃ r γ : ℝ, 0 < r ∧ 0 < γ ∧
      ∀ (W₁ W₂ Vlo Vhi : ℝ → ℝ) (s t₂ : ℝ) (a₂ W₂' : ℝ → ℝ),
        Continuous W₁ → 0 ≤ s → ((W₁ 0 : ℝ) : ℂ) ∈ closure H₁ →
        ((W₂ 0 : ℝ) : ℂ) ∈ closure H₂ → W₁ 0 < q → q < W₂ 0 →
        fwdHull W₁ s ⊆ H₁ → fwdHull W₂ t₂ ⊆ H₂ →
        IsSeedCoordinate W₁ Vlo s → IsSeedCoordinate W₁ Vhi s →
        ImgData W₂ (fwdHull W₁ s) (fun z => fwdMap W₁ s z + W₁ s) t₂ a₂ W₂' →
        ∀ x ∈ uIcc (Vlo s) (Vhi s),
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
  obtain ⟨r, hr, hclear⟩ := exists_le_norm_fwdMap_sub_seed_interval_uniform
    hH₁ hH₂.2.1 hH₂.1 hδ hsepδ
  obtain ⟨r₂, hr₂, hclear₂⟩ := exists_le_norm_fwdMap_uniform
    hH₂ hH₁.2.1 hH₁.1 hδ hsepδ'
  obtain ⟨γ, hγ, hprot⟩ := exists_le_norm_fwdMap_protected hH₂ hH₁ hsep.symm hd hqH'
  refine ⟨r, γ, hr, hγ, ?_⟩
  intro W₁ W₂ Vlo Vhi s t₂ a₂ W₂' hW₁ hs hW₁H hW₂H hWq hqW hK₁ hK₂ hlo hhi h x hx
  have ht₂ : 0 ≤ t₂ := h.pos.le
  have hsI : s ∈ Icc (0 : ℝ) s := ⟨hs, le_rfl⟩
  have ht₂I : t₂ ∈ Icc (0 : ℝ) t₂ := ⟨ht₂, le_rfl⟩
  have hclx : Disjoint (ball (x : ℂ) r)
      ((fun z => fwdMap W₁ s z + W₁ s) '' fwdHull W₂ t₂) := by
    rw [Set.disjoint_left]
    rintro z hz ⟨w, hw, rfl⟩
    have hb := hclear W₁ Vlo Vhi s hW₁ hW₁H hK₁ hlo hhi s hsI w (hK₂ hw) x hx
    rw [mem_ball, dist_eq_norm] at hz
    exact not_lt_of_ge hb hz
  refine ⟨hclx, ?_⟩
  have h2d : 0 < 2 * d := by positivity
  obtain ⟨uq, huq⟩ := exists_isForwardSol_of_disjoint_ball_gen hW₁ hWq.ne' hs h2d
    (hqH.mono_right (hK₁.trans subset_union_left))
  let p : ℝ := (uq s).re + W₁ s
  have hxp : x < p := hx.2.trans_lt (max_lt
    (hlo.lt_gmap hW₁ hWq huq hsI) (hhi.lt_gmap hW₁ hWq huq hsI))
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
    (hxp.trans hpW).ne hτ0 hr hclx'
  have hgap : ∀ u ∈ Icc (0 : ℝ) t₂, γ ≤ ‖fwdMap W₂' (a₂ u) x‖ := by
    intro u hu
    obtain ⟨⟨vp, hvp⟩, hpγ⟩ := hprot W₂ W₁ s t₂ a₂ W₂' h hW₁ hs hW₁H hK₂ hK₁ u hu
    rw [fwdMap_eq_of_isForwardSol hW₁ huq hsI] at hvp hpγ
    have hat := h.mapsTo_clock_Icc hu
    have hau : a₂ u ∈ Icc (0 : ℝ) (a₂ u) := ⟨hat.1, le_rfl⟩
    have hvx' := isForwardSol_restrict hvx hat.2
    have hord := QuantumZipper.F1.isForwardSol_lt_of_lt hat.1 hxp hvx' hvp (a₂ u) hau
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

end InteractingSLE.ZhanGT4
