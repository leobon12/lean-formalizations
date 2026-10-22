import HigherDimLQGMetric.Trap.Confine
import HigherDimLQGMetric.Metric.Reparam

/-!
# Parametrization by weighted arc length

Packet S3 (MA1 A17; the curves of A13(b) and of the stability argument are parametrized at
constant weighted speed). For a continuous curve `Q : [a, b] → Z` in a metric space, a continuous
weight that is positive along `Q`, and finite weighted length `W`, the curve
`P := P₁ ∘ g ∘ (λ ·)` (with `P₁` the parametrization by length and `g` the inverse of the
weighted length function of `P₁`) is defined on `[0, W/λ]` and satisfies
`∫_{P|[s,t]} w ds = λ (t - s)`. Every pair of its times corresponds to a pair of times of `Q`
with the same points and the same weighted length (`trap_exists_weighted_param`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

/-- **Weighted arc-length parametrization.** -/
theorem trap_exists_weighted_param {Z : Type*} [MetricSpace Z] {w : Z → ℝ} {Q : ℝ → Z}
    {a b lam : ℝ} (hab : a ≤ b) (hQ : ContinuousOn Q (Icc a b))
    (hw : ContinuousOn w (Q '' Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 < w (Q t)) (hlam : 0 < lam)
    (hfin : weightedLength w Q a b ≠ ⊤) :
    ∃ P : ℝ → Z, ContinuousOn P (Icc 0 ((weightedLength w Q a b).toReal / lam)) ∧
      P 0 = Q a ∧ P ((weightedLength w Q a b).toReal / lam) = Q b ∧
      MapsTo P (Icc 0 ((weightedLength w Q a b).toReal / lam)) (Q '' Icc a b) ∧
      (∀ s t, 0 ≤ s → s ≤ t → t ≤ (weightedLength w Q a b).toReal / lam →
        weightedLength w P s t = ENNReal.ofReal (lam * (t - s))) ∧
      (∀ s t, 0 ≤ s → s ≤ t → t ≤ (weightedLength w Q a b).toReal / lam →
        ∃ u v, a ≤ u ∧ u ≤ v ∧ v ≤ b ∧ P s = Q u ∧ P t = Q v ∧
          weightedLength w Q u v = weightedLength w P s t) := by
  -- bounds of the weight on the compact image
  have himc : IsCompact (Q '' Icc a b) := isCompact_Icc.image_of_continuousOn hQ
  have hne : (Q '' Icc a b).Nonempty := ⟨Q a, a, ⟨le_rfl, hab⟩, rfl⟩
  obtain ⟨zm, hzm, hmin⟩ := himc.exists_isMinOn hne hw
  obtain ⟨zM, -, hmax⟩ := himc.exists_isMaxOn hne hw
  set m := w zm with hm_def
  set Mw := w zM with hMw_def
  have hm : 0 < m := by
    obtain ⟨t, ht, rfl⟩ := hzm
    exact hpos t ht
  have hwm : ∀ z ∈ Q '' Icc a b, m ≤ w z := fun z hz => hmin hz
  have hwM : ∀ z ∈ Q '' Icc a b, w z ≤ Mw := fun z hz => hmax hz
  have hmM : m ≤ Mw := hwM _ hzm
  have hMw : 0 < Mw := hm.trans_le hmM
  -- finite length
  have hlen : curveLength Q a b ≠ ⊤ := by
    intro htop
    have h := ofReal_mul_curveLength_le_weightedLength (w := w) (P := Q) (m := m) hab
      (fun t ht => hwm _ ⟨t, ht, rfl⟩)
    rw [htop, ENNReal.mul_top (by simpa using hm)] at h
    exact hfin (top_unique h)
  set ℓ := (curveLength Q a b).toReal with hℓ_def
  set P₁ := lengthParam Q a b with hP₁_def
  obtain ⟨hu, hP₁c, hP₁0, hP₁ℓ, hP₁S⟩ :=
    lengthParam_props hab hQ hlen (S := Q '' Icc a b) (fun t ht => ⟨t, ht, rfl⟩)
  have hunit : ∀ s t, 0 ≤ s → s ≤ t → t ≤ ℓ → curveLength P₁ s t = ENNReal.ofReal (t - s) :=
    hasUnitSpeedOn_Icc_iff'.1 hu
  -- weighted pieces of the unit-speed curve
  have hpieceLo : ∀ s t, 0 ≤ s → s ≤ t → t ≤ ℓ →
      ENNReal.ofReal (m * (t - s)) ≤ weightedLength w P₁ s t := by
    intro s t hs hst htℓ
    have h := ofReal_mul_curveLength_le_weightedLength (w := w) (P := P₁) (m := m) hst
      (fun r hr => hwm _ (hP₁S ⟨hs.trans hr.1, hr.2.trans htℓ⟩))
    rwa [hunit s t hs hst htℓ, ← ENNReal.ofReal_mul hm.le] at h
  have hpieceHi : ∀ s t, 0 ≤ s → s ≤ t → t ≤ ℓ →
      weightedLength w P₁ s t ≤ ENNReal.ofReal (Mw * (t - s)) := by
    intro s t hs hst htℓ
    have h := weightedLength_le_ofReal_mul_curveLength (w := w) (P := P₁) (M := Mw)
      (a := s) (b := t) (fun r hr => hwM _ (hP₁S ⟨hs.trans hr.1, hr.2.trans htℓ⟩))
    rwa [hunit s t hs hst htℓ, ← ENNReal.ofReal_mul hMw.le] at h
  have hpiece_ne : ∀ s t, 0 ≤ s → s ≤ t → t ≤ ℓ → weightedLength w P₁ s t ≠ ⊤ :=
    fun s t hs hst htℓ => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hpieceHi s t hs hst htℓ)
  -- the weighted length function `G`
  set G : ℝ → ℝ := fun s => (weightedLength w P₁ 0 s).toReal with hG_def
  have hℓ0 : 0 ≤ ℓ := ENNReal.toReal_nonneg
  have hGdiff : ∀ s t, 0 ≤ s → s ≤ t → t ≤ ℓ →
      G t - G s = (weightedLength w P₁ s t).toReal := by
    intro s t hs hst htℓ
    have hadd := weightedLength_add (w := w) (P := P₁) hs hst
    have h1 := hpiece_ne 0 s le_rfl hs (hst.trans htℓ)
    have h2 := hpiece_ne s t hs hst htℓ
    simp only [hG_def]
    rw [← hadd, ENNReal.toReal_add h1 h2]
    ring
  have hGlo : ∀ s t, 0 ≤ s → s ≤ t → t ≤ ℓ → m * (t - s) ≤ G t - G s := by
    intro s t hs hst htℓ
    rw [hGdiff s t hs hst htℓ]
    have := (ENNReal.ofReal_le_iff_le_toReal (hpiece_ne s t hs hst htℓ)).1
      (hpieceLo s t hs hst htℓ)
    exact this
  have hGhi : ∀ s t, 0 ≤ s → s ≤ t → t ≤ ℓ → G t - G s ≤ Mw * (t - s) := by
    intro s t hs hst htℓ
    rw [hGdiff s t hs hst htℓ]
    exact ENNReal.toReal_le_of_le_ofReal (by nlinarith [sub_nonneg.2 hst])
      (hpieceHi s t hs hst htℓ)
  have hG0 : G 0 = 0 := by simp [hG_def, weightedLength_self]
  have hGℓ : G ℓ = (weightedLength w Q a b).toReal := by
    simp only [hG_def, hP₁_def, hℓ_def]
    rw [weightedLength_eq_lengthParam hab hQ hlen]
  set W := (weightedLength w Q a b).toReal with hW_def
  have hW0 : 0 ≤ W := ENNReal.toReal_nonneg
  -- continuity of `G`
  have hGc : ContinuousOn G (Icc 0 ℓ) := by
    refine (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal Mw) fun x hx y hy => ?_).continuousOn
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hMw.le]
    rcases le_total x y with hxy | hxy
    · rw [abs_of_nonpos (by linarith [hGlo x y hx.1 hxy hy.2, mul_nonneg hm.le (sub_nonneg.2 hxy)]),
        abs_of_nonpos (by linarith)]
      linarith [hGhi x y hx.1 hxy hy.2]
    · rw [abs_of_nonneg (by linarith [hGlo y x hy.1 hxy hx.2, mul_nonneg hm.le (sub_nonneg.2 hxy)]),
        abs_of_nonneg (by linarith)]
      linarith [hGhi y x hy.1 hxy hx.2]
  -- the inverse `g`
  have hsurj : ∀ y ∈ Icc 0 W, ∃ s ∈ Icc 0 ℓ, G s = y := by
    intro y hy
    have h := intermediate_value_Icc hℓ0 hGc
    rw [hG0, hGℓ] at h
    exact h hy
  set g : ℝ → ℝ := Function.invFunOn G (Icc 0 ℓ) with hg_def
  have hgG : ∀ y ∈ Icc 0 W, G (g y) = y := fun y hy => Function.invFunOn_eq (hsurj y hy)
  have hgmem : ∀ y ∈ Icc 0 W, g y ∈ Icc 0 ℓ := fun y hy => Function.invFunOn_mem (hsurj y hy)
  have hgmono : ∀ y ∈ Icc 0 W, ∀ y' ∈ Icc 0 W, y ≤ y' → g y ≤ g y' := by
    intro y hy y' hy' hyy'
    by_contra hlt
    push Not at hlt
    have := hGlo (g y') (g y) (hgmem y' hy').1 hlt.le (hgmem y hy).2
    rw [hgG y hy, hgG y' hy'] at this
    nlinarith [mul_pos hm (sub_pos.2 hlt)]
  have hglip : ∀ y ∈ Icc 0 W, ∀ y' ∈ Icc 0 W, y ≤ y' → m * (g y' - g y) ≤ y' - y := by
    intro y hy y' hy' hyy'
    have := hGlo (g y) (g y') (hgmem y hy).1 (hgmono y hy y' hy' hyy') (hgmem y' hy').2
    rwa [hgG y hy, hgG y' hy'] at this
  have hgc : ContinuousOn g (Icc 0 W) := by
    refine (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal m⁻¹) fun x hx y hy => ?_).continuousOn
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (inv_nonneg.2 hm.le)]
    rcases le_total x y with hxy | hxy
    · have h1 := hglip x hx y hy hxy
      have h2 := hgmono x hx y hy hxy
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      rw [← div_eq_inv_mul, le_div_iff₀ hm]
      linarith
    · have h1 := hglip y hy x hx hxy
      have h2 := hgmono y hy x hx hxy
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      rw [← div_eq_inv_mul, le_div_iff₀ hm]
      linarith
  have hg0 : g 0 = 0 := by
    have h0 : (0 : ℝ) ∈ Icc 0 W := ⟨le_rfl, hW0⟩
    have hmem := hgmem 0 h0
    have hlo := hGlo 0 (g 0) le_rfl hmem.1 hmem.2
    rw [hgG 0 h0, hG0] at hlo
    have : m * g 0 ≤ 0 := by linarith
    have hle : g 0 ≤ 0 := by
      by_contra hpos'
      push Not at hpos'
      nlinarith [mul_pos hm hpos']
    exact le_antisymm hle hmem.1
  have hgW : g W = ℓ := by
    have hWm : W ∈ Icc 0 W := ⟨hW0, le_rfl⟩
    have hmem := hgmem W hWm
    have hlo := hGlo (g W) ℓ hmem.1 hmem.2 le_rfl
    rw [hgG W hWm, hGℓ] at hlo
    have hge : ℓ ≤ g W := by
      by_contra hlt
      push Not at hlt
      nlinarith [mul_pos hm (sub_pos.2 hlt)]
    exact le_antisymm hmem.2 hge
  -- the time change `φ` and the curve `P`
  set L := W / lam with hL_def
  have hL0 : 0 ≤ L := div_nonneg hW0 hlam.le
  set φ : ℝ → ℝ := fun τ => g (lam * τ) with hφ_def
  have hlamτ : ∀ τ ∈ Icc 0 L, lam * τ ∈ Icc 0 W := by
    intro τ hτ
    refine ⟨mul_nonneg hlam.le hτ.1, ?_⟩
    have := mul_le_mul_of_nonneg_left hτ.2 hlam.le
    rwa [hL_def, mul_div_cancel₀ _ hlam.ne'] at this
  have hφmem : MapsTo φ (Icc 0 L) (Icc 0 ℓ) := fun τ hτ => hgmem _ (hlamτ τ hτ)
  have hφc : ContinuousOn φ (Icc 0 L) :=
    hgc.comp (continuous_const.mul continuous_id).continuousOn hlamτ
  have hφm : MonotoneOn φ (Icc 0 L) := fun s hs t ht hst =>
    hgmono _ (hlamτ s hs) _ (hlamτ t ht) (mul_le_mul_of_nonneg_left hst hlam.le)
  have hφG : ∀ τ ∈ Icc 0 L, G (φ τ) = lam * τ := fun τ hτ => hgG _ (hlamτ τ hτ)
  -- weighted lengths of `P₁` between two times
  have hP₁wl : ∀ r₁ r₂, 0 ≤ r₁ → r₁ ≤ r₂ → r₂ ≤ ℓ →
      weightedLength w P₁ r₁ r₂ = ENNReal.ofReal (G r₂ - G r₁) := by
    intro r₁ r₂ h1 h12 h2
    rw [hGdiff r₁ r₂ h1 h12 h2, ENNReal.ofReal_toReal (hpiece_ne r₁ r₂ h1 h12 h2)]
  have hPwl : ∀ s t, 0 ≤ s → s ≤ t → t ≤ L →
      weightedLength w (P₁ ∘ φ) s t = weightedLength w P₁ (φ s) (φ t) := by
    intro s t hs hst htL
    have hsub : Icc s t ⊆ Icc 0 L := Icc_subset_Icc hs htL
    exact weightedLength_comp_monotoneOn hst (hφc.mono hsub) (hφm.mono hsub)
  refine ⟨P₁ ∘ φ, hP₁c.comp hφc hφmem, ?_, ?_, ?_, ?_, ?_⟩
  · show P₁ (g (lam * 0)) = Q a
    rw [mul_zero, hg0]
    exact hP₁0
  · show P₁ (g (lam * (W / lam))) = Q b
    rw [mul_div_cancel₀ _ hlam.ne', hgW]
    exact hP₁ℓ
  · exact hP₁S.comp hφmem
  · intro s t hs hst htL
    have hsL : s ∈ Icc 0 L := ⟨hs, hst.trans htL⟩
    have htL' : t ∈ Icc 0 L := ⟨hs.trans hst, htL⟩
    rw [hPwl s t hs hst htL, hP₁wl _ _ (hφmem hsL).1 (hφm hsL htL' hst) (hφmem htL').2,
      hφG t htL', hφG s hsL]
    congr 1
    ring
  · intro s t hs hst htL
    have hsL : s ∈ Icc 0 L := ⟨hs, hst.trans htL⟩
    have htL' : t ∈ Icc 0 L := ⟨hs.trans hst, htL⟩
    -- the length function of `Q`
    set σ := variationOnFromTo Q (Icc a b) a with hσ_def
    have hbv : BoundedVariationOn Q (Icc a b) := hlen
    have hσm : MonotoneOn σ (Icc a b) :=
      variationOnFromTo.monotoneOn hbv.locallyBoundedVariationOn ⟨le_rfl, hab⟩
    have hσc : ContinuousOn σ (Icc a b) := continuousOn_variationOnFromTo hab hQ hlen
    have hσa : σ a = 0 := variationOnFromTo.self _ _ _
    have hσb : σ b = ℓ := by
      rw [hσ_def, variationOnFromTo.eq_of_le _ _ hab, inter_self]
      rfl
    have hσP : ∀ τ ∈ Icc a b, P₁ (σ τ) = Q τ := fun τ hτ => lengthParam_variationOnFromTo hlen hτ
    have hpre : ∀ r ∈ Icc 0 ℓ, ∃ τ ∈ Icc a b, σ τ = r := by
      intro r hr
      have h := intermediate_value_Icc hab hσc
      rw [hσa, hσb] at h
      exact h hr
    obtain ⟨u, hu, hσu⟩ := hpre _ (hφmem hsL)
    obtain ⟨v', hv', hσv'⟩ := hpre _ (hφmem htL')
    have hφst : φ s ≤ φ t := hφm hsL htL' hst
    -- choose `v` with `u ≤ v`
    obtain ⟨v, hv, huv, hσv⟩ : ∃ v ∈ Icc a b, u ≤ v ∧ σ v = φ t := by
      rcases hφst.lt_or_eq with hlt | heq
      · refine ⟨v', hv', ?_, hσv'⟩
        by_contra hvu
        push Not at hvu
        have := hσm hv' hu hvu.le
        rw [hσu, hσv'] at this
        exact absurd this (not_le.2 hlt)
      · exact ⟨u, hu, le_rfl, hσu.trans heq⟩
    refine ⟨u, v, hu.1, huv, hv.2, ?_, ?_, ?_⟩
    · show P₁ (φ s) = Q u
      rw [← hσu, hσP u hu]
    · show P₁ (φ t) = Q v
      rw [← hσv, hσP v hv]
    · have hsub : Icc u v ⊆ Icc a b := Icc_subset_Icc hu.1 hv.2
      have hcongr : EqOn Q (P₁ ∘ σ) (Icc u v) := fun τ hτ => (hσP τ (hsub hτ)).symm
      rw [weightedLength_congr hcongr,
        weightedLength_comp_monotoneOn huv (hσc.mono hsub) (hσm.mono hsub), hσu, hσv,
        hPwl s t hs hst htL]

end HigherDimLQGMetric
