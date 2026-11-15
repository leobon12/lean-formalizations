/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S9BOrder

/-!
# A thin left-side sector along an arc of a proper curve, avoiding a closed set

Packet PROVE-GB7A (the collar's joint activity, proof of Theorem 7.12D, supplement p. 543: "both incident collars
are therefore in the own unbounded component"). The proof of the side principle (`eventually_mem_leftSide_of_eqOn`,
`S9BSide.lean`) straightens a proper curve `γ` with the Schoenflies theorem and joins points of its left side inside
a thin annular sector along a compact arc. The same construction, with the tail of the second curve replaced by an
arbitrary closed set `F` that misses the arc, gives:

* `exists_leftSide_sector`: for a proper curve `γ` from a real seed, a compact parameter interval `[a, b]` of its
  seed line `ℓ`, and a closed set `F` missing `ℓ([a, b])`, there is a preconnected set `S` contained in the left side
  of `γ` and disjoint from `F`, which contains every point of the left side sufficiently close to `ℓ(t)` for each
  interior parameter `t ∈ (a, b)`.

This is the planar fact behind "follow the left side of the arc from the contact point to the tip".
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex Bornology
open scoped NNReal

namespace InteractingSLE

namespace Supp9B

variable {γ : ℝ≥0 → ℂ}

/-- **A left-side sector along an arc, avoiding a closed set.** For a proper curve `γ` from a real seed, parameters
`a`, `b` of its seed line `ℓ = seedLine γ`, and a closed set `F` that misses `ℓ([a, b])`, there is a preconnected
subset `S` of the left side of `γ`, disjoint from `F`, such that near every point `ℓ(t)`, `t ∈ (a, b)`, every point of
the left side lies in `S`. -/
theorem exists_leftSide_sector (hγ : IsProperCurve γ) (h0 : (γ 0).im = 0) {a b : ℝ} {F : Set ℂ}
    (hF : IsClosed F) (hdisj : ∀ t ∈ Icc a b, seedLine γ t ∉ F) :
    ∃ S : Set ℂ, IsPreconnected S ∧ S ⊆ leftSide γ ∧ Disjoint S F ∧
      ∀ t ∈ Ioo a b, ∀ᶠ w in 𝓝 (seedLine γ t), w ∈ leftSide γ → w ∈ S := by
  obtain ⟨h, hs, hL, -, hbL, -⟩ := exists_straightening_sides hγ h0
  set p := rightRef γ with hp
  set ℓ := seedLine γ with hℓ
  set Ψ : ℂ → ℂ := fun z => h.symm (inv p z) with hΨ
  have hpS : p ∉ seedRayClosure γ := rightRef_notMem hγ.2.2.1 h0
  have hℓp : ∀ t, ℓ t ≠ p := fun t h' => hpS (h' ▸ seedLine_mem h0 t)
  have hΨs : ∀ z ∈ seedRayClosure γ, Ψ z ∈ sphere (0 : ℂ) 1 := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ : inv p z ∈ h '' sphere 0 1 := hs ▸ inv_mem_invCurve hz hp
    simpa [hΨ, ← hyz] using hy
  have hΨc : ∀ z, z ≠ p → ContinuousAt Ψ z := fun z hz =>
    h.symm.continuous.continuousAt.comp (continuousAt_inv hz)
  have hΨinj : ∀ z w, Ψ z = Ψ w → z = w := fun z w hzw =>
    inv_injective p (h.symm.injective hzw)
  have hrec : ∀ z, uninv p (h (Ψ z)) = z := fun z => by simp [hΨ]
  have hΨℓ : Continuous fun t => Ψ (ℓ t) := continuous_iff_continuousAt.2 fun t =>
    (hΨc _ (hℓp t)).comp (continuous_seedLine hγ.1).continuousAt
  -- the arc in straightened coordinates
  set C := (fun t => Ψ (ℓ t)) '' Icc a b with hC
  have hCcpt : IsCompact C := isCompact_Icc.image hΨℓ
  have hCconn : IsPreconnected C := isPreconnected_Icc.image _ hΨℓ.continuousOn
  -- the rest of the closed curve
  set Fb := h.symm '' (inv p '' (ℓ '' (Iic a ∪ Ici b)) ∪ {0}) with hFb
  have hFbc : IsClosed Fb := by
    rw [hFb, h.image_symm]
    exact (isClosed_inv_image_union (isClosed_seedLine_image hγ (isClosed_Iic.union isClosed_Ici))).preimage
      h.continuous
  have hsph : sphere (0 : ℂ) 1 ⊆ C ∪ Fb := by
    intro y hy
    have hhy : h y ∈ invCurve γ := hs ▸ mem_image_of_mem h hy
    rcases hhy with ⟨z, hz, hzy⟩ | hz0
    · obtain ⟨t, rfl⟩ := seedLine_surj h0 hz
      have hy' : y = Ψ (ℓ t) := by
        show y = h.symm (inv p (ℓ t))
        rw [show inv p (ℓ t) = h y from hzy, Homeomorph.symm_apply_apply]
      by_cases ht : t ∈ Icc a b
      · exact Or.inl ⟨t, ht, hy'.symm⟩
      · refine Or.inr ⟨inv p (ℓ t), Or.inl ⟨ℓ t, ⟨t, ?_, rfl⟩, rfl⟩, hy'.symm⟩
        rw [mem_Icc, not_and_or, not_le, not_le] at ht
        rcases ht with ht | ht
        · exact Or.inl ht.le
        · exact Or.inr ht.le
    · exact Or.inr ⟨0, Or.inr rfl, by rw [← mem_singleton_iff.1 hz0, Homeomorph.symm_apply_apply]⟩
  have hnotFb : ∀ t ∈ Ioo a b, Ψ (ℓ t) ∉ Fb := by
    rintro t ht ⟨w, hw | hw, hwt⟩
    · obtain ⟨_, ⟨t', ht', rfl⟩, rfl⟩ := hw
      have := seedLine_injective hγ h0 (hΨinj _ _ hwt)
      rw [this] at ht'
      rcases ht' with h' | h'
      · exact absurd (mem_Iic.1 h') (not_le.2 ht.1)
      · exact absurd (mem_Ici.1 h') (not_le.2 ht.2)
    · rw [mem_singleton_iff.1 hw] at hwt
      exact inv_apply_ne_zero (hℓp t) (h.symm.injective (hwt.symm.trans (by simp)))
  -- the closed set to avoid, in straightened coordinates
  set Fa := h.symm '' (inv p '' F ∪ {0}) with hFa
  have hFac : IsClosed Fa := by
    rw [hFa, h.image_symm]
    exact (isClosed_inv_image_union hF).preimage h.continuous
  have hCFa : C ⊆ Faᶜ := by
    rintro _ ⟨t, ht, rfl⟩ ⟨w, hw | hw, hwt⟩
    · obtain ⟨z, hz, rfl⟩ := hw
      have hzt : z = ℓ t := hΨinj _ _ hwt
      exact hdisj t ht (hzt ▸ hz)
    · rw [mem_singleton_iff.1 hw] at hwt
      exact inv_apply_ne_zero (hℓp t) (h.symm.injective (hwt.symm.trans (by simp)))
  have hCs : C ⊆ sphere (0 : ℂ) 1 := by
    rintro _ ⟨t, -, rfl⟩; exact hΨs _ (seedLine_mem h0 t)
  -- a thin annular sector inside the disc along the arc
  obtain ⟨δ, hδ, hthick⟩ := hCcpt.exists_thickening_subset_open hFac.isOpen_compl hCFa
  set η : ℝ := min (δ / 2) (1 / 2) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by norm_num)
  have hηδ : η < δ := (min_le_left _ _).trans_lt (by linarith)
  have hη1 : η ≤ 1 / 2 := min_le_right _ _
  set Aη := (fun q : ℝ × ℂ => (q.1 : ℂ) * q.2) '' (Ioo (1 - η) 1 ×ˢ C) with hAη
  have hAconn : IsPreconnected Aη :=
    (isPreconnected_Ioo.prod hCconn).image _
      (by fun_prop : Continuous fun q : ℝ × ℂ => (q.1 : ℂ) * q.2).continuousOn
  have hAball : Aη ⊆ ball 0 1 := by
    rintro _ ⟨⟨r, c⟩, ⟨hr, hc⟩, rfl⟩
    have hc1 : ‖c‖ = 1 := by simpa using hCs hc
    rw [mem_ball, dist_zero_right, norm_mul, hc1, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith [hr.1])]
    exact hr.2
  have hAthick : Aη ⊆ thickening δ C := by
    rintro _ ⟨⟨r, c⟩, ⟨hr, hc⟩, rfl⟩
    rw [mem_thickening_iff]
    refine ⟨c, hc, ?_⟩
    have hc1 : ‖c‖ = 1 := by simpa using hCs hc
    have hr1 : r - 1 < 0 := by linarith [hr.2]
    rw [dist_eq_norm, show (r : ℂ) * c - c = ((r - 1 : ℝ) : ℂ) * c by push_cast; ring, norm_mul, hc1,
      mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hr1]
    linarith [hr.1]
  set Sη := uninv p '' (h '' Aη) with hSη
  have hhA : h '' Aη ⊆ (invCurve γ)ᶜ := by
    rintro _ ⟨x, hx, rfl⟩ hxJ
    rw [← hs] at hxJ
    obtain ⟨y, hy, hyx⟩ := hxJ
    rw [h.injective hyx] at hy
    have h1 : ‖x‖ = 1 := by simpa using hy
    have h2 : ‖x‖ < 1 := by simpa using hAball hx
    linarith
  have hSconn : IsPreconnected Sη :=
    (hAconn.image _ h.continuous.continuousOn).image _ ((continuousOn_uninv p).mono fun w hw =>
      ne_zero_of_notMem_invCurve (hhA hw))
  have hSL : Sη ⊆ leftSide γ := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact hbL x (by simpa using hAball hx)
  have hSF : Disjoint Sη F := by
    rw [Set.disjoint_left]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ hz
    have hxF : x ∈ Fa :=
      ⟨h x, Or.inl ⟨uninv p (h x), hz, inv_uninv p (h x)⟩, h.symm_apply_apply x⟩
    exact hthick (hAthick hx) hxF
  -- near every interior point of the arc, the left side lies in the sector
  have hK7 : ∀ t ∈ Ioo a b, ∀ᶠ w in 𝓝 (ℓ t), w ∈ leftSide γ → w ∈ Sη := by
    intro t ht
    have hy₀ : Ψ (ℓ t) ∈ sphere (0 : ℂ) 1 := hΨs _ (seedLine_mem h0 t)
    have hn1 : ‖Ψ (ℓ t)‖ = 1 := by simpa using hy₀
    have hy0 : Ψ (ℓ t) ≠ 0 := by intro h'; rw [h', norm_zero] at hn1; norm_num at hn1
    have hc := hΨc _ (hℓp t)
    set N : ℂ → ℂ := fun y => y / (‖y‖ : ℂ) with hN
    have hNc : ContinuousAt N (Ψ (ℓ t)) :=
      continuousAt_id.div (continuous_ofReal.comp continuous_norm).continuousAt
        (by simpa using hy0)
    have hNy : N (Ψ (ℓ t)) = Ψ (ℓ t) := by simp [hN, hn1]
    have hO : Fbᶜ ∈ 𝓝 (N (Ψ (ℓ t))) := by
      rw [hNy]; exact hFbc.isOpen_compl.mem_nhds (hnotFb t ht)
    have e1 : ∀ᶠ w in 𝓝 (ℓ t), N (Ψ w) ∈ Fbᶜ := (hNc.comp hc).preimage_mem_nhds hO
    have e2 : ∀ᶠ w in 𝓝 (ℓ t), 1 - η < ‖Ψ w‖ :=
      (continuous_norm.continuousAt.comp hc).eventually
        (lt_mem_nhds (show 1 - η < ‖Ψ (ℓ t)‖ by rw [hn1]; linarith))
    filter_upwards [e1, e2] with w hw1 hw2 hwL
    have hnw : ‖Ψ w‖ < 1 := hL w hwL
    have hw0 : Ψ w ≠ 0 := by intro h'; rw [h', norm_zero] at hw2; linarith
    have hu : N (Ψ w) ∈ sphere (0 : ℂ) 1 := by
      simp only [hN, mem_sphere_iff_norm, sub_zero, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_norm]
      exact div_self (norm_ne_zero_iff.2 hw0)
    have huC : N (Ψ w) ∈ C := by
      rcases hsph hu with h' | h'
      · exact h'
      · exact absurd h' hw1
    have hdecomp : ((‖Ψ w‖ : ℝ) : ℂ) * N (Ψ w) = Ψ w := by
      have hnw0 : (‖Ψ w‖ : ℂ) ≠ 0 := by simpa using hw0
      simp only [hN]; field_simp
    exact ⟨h (Ψ w), ⟨Ψ w, ⟨(‖Ψ w‖, N (Ψ w)), ⟨⟨hw2, hnw⟩, huC⟩, hdecomp⟩, rfl⟩, hrec w⟩
  exact ⟨Sη, hSconn, hSL, hSF, hK7⟩

end Supp9B

end InteractingSLE
