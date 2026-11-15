/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76GOrder

/-!
# No straddling in a hydrodynamic chart (Aux. lemma 85, the planar separation step)

Packet PROVE-T15-AUX85 (Aux. lemma 85, supplement pp. 299–300). Let `ψ` be a chart inverse of `D = ℍ \ fill K`
(continuous on `ℍ̄`, a bijection `ℍ → D`, real points off `D`, bounded displacement). Let `X` be a compact connected
subset of `ℍ̄` off `D` containing a real point, and `Y` a bounded connected subset of `ℍ̄` off `D` disjoint from `X`.
Then the real chart points of `Y` do not straddle a real chart point of `X`: there are no `w_Y < w_X < w_Y'` with
`ψ(w_Y), ψ(w_Y') ∈ Y` and `ψ(w_X) ∈ X` (`false_of_straddle`).

This is PROVE-LEMMA76G's crosscut argument (`Sec7.Lemma76G.lt_of_inv_mem`, Aux. lemma 60 generalized) with the
freeness of `Y` for the crosscut `F = ψ(S) ∪ X` (`S` the closed upper semicircle over `[−R, w_X]`) witnessed by the
chart point `w_Y' > w_X` instead of a real point of `Y`: the points of `ℍ` outside the half-disc are carried into the
unbounded domain of `F` along rays (`Lemma76E.mem_H_diff_fillH_of_ray`), so `ψ(w_Y')` is not trapped by `F`; `Y`
misses `F`, hence `ψ(w_Y)` is free for `F` as well, and `Lemma76G.false_of_lt_aux` gives the contradiction (a far-left
real point is trapped by `F` but adherent to the half-disc image).

In the source this is the statement that a crosscut excursion cuts off a bounded side ("A point separated from the
boundary is therefore decided by finitely many paired loops", p. 300), used here for the boundary walk of the joint
domain.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace RLC

namespace Aux85

open HalfPlaneSep Restart Sec7.Lemma76E Sec7.Lemma76G

/-- **No straddling.** In a chart inverse `ψ` of `ℍ \ fill K`, the chart points of a bounded connected set `Y` off the
domain do not straddle a chart point of a disjoint compact connected set `X` off the domain that contains a real
point. -/
theorem false_of_straddle {ψ : ℂ → ℂ} {K X Y : Set ℂ} (hK : IsCompact K) (hψc : ContinuousOn ψ Hbar)
    (hbij : BijOn ψ H (H \ fillH K)) (hreal : ∀ w ∉ H, ψ w ∉ H \ fillH K) {M : ℝ}
    (hM : ∀ w ∈ Hbar, ‖ψ w - w‖ ≤ M)
    (hXc : IsCompact X) (hXpc : IsPreconnected X) (hXim : ∀ z ∈ X, 0 ≤ z.im) (hXD : ∀ z ∈ X, z ∉ H \ fillH K)
    (hYb : IsBounded Y) (hYpc : IsPreconnected Y) (hYim : ∀ z ∈ Y, 0 ≤ z.im) (hYD : ∀ z ∈ Y, z ∉ H \ fillH K)
    (hXY : Disjoint X Y) {x₀ : ℝ} (hx₀X : ((x₀ : ℝ) : ℂ) ∈ X)
    {wX wY wY' : ℝ} (hwX : ψ wX ∈ X) (hwY : ψ wY ∈ Y) (hwY' : ψ wY' ∈ Y) (h1 : wY < wX) (h2 : wX < wY') :
    False := by
  have hrealHbar : ∀ v : ℝ, ((v : ℝ) : ℂ) ∈ Hbar := fun v => show (0 : ℝ) ≤ ((v : ℝ) : ℂ).im by simp
  -- the shifted chart
  set ψ' : ℂ → ℂ := fun z => ψ (z + wX) with hψ'
  have hshH : ∀ z : ℂ, z + (wX : ℂ) ∈ H ↔ z ∈ H := fun z => by
    show 0 < (z + (wX : ℂ)).im ↔ 0 < z.im
    simp
  have hshHbar : ∀ z ∈ Hbar, z + (wX : ℂ) ∈ Hbar := fun z hz => by
    show 0 ≤ (z + (wX : ℂ)).im
    simpa using (show 0 ≤ z.im from hz)
  have hψ'c : ContinuousOn ψ' Hbar :=
    hψc.comp (continuous_id.add continuous_const).continuousOn fun z hz => hshHbar z hz
  have hψ'bij : BijOn ψ' H (H \ fillH K) := by
    refine ⟨fun z hz => hbij.mapsTo ((hshH z).2 hz), fun z hz z' hz' he => ?_, fun y hy => ?_⟩
    · have := hbij.injOn ((hshH z).2 hz) ((hshH z').2 hz') he
      simpa using this
    · obtain ⟨v, hv, rfl⟩ := hbij.surjOn hy
      refine ⟨v - wX, (hshH _).1 (by simpa using hv), ?_⟩
      simp [hψ']
  have hψ'real : ∀ w ∉ H, ψ' w ∉ H \ fillH K := fun w hw => hreal _ fun h => hw ((hshH w).1 h)
  set M' : ℝ := M + |wX| with hM'
  have hM'b : ∀ w ∈ Hbar, ‖ψ' w - w‖ ≤ M' := fun w hw => by
    have h1 := hM _ (hshHbar w hw)
    have h2 : ψ' w - w = (ψ (w + wX) - (w + wX)) + (wX : ℂ) := by simp only [hψ']; ring
    rw [h2]
    calc ‖(ψ (w + wX) - (w + wX)) + (wX : ℂ)‖ ≤ ‖ψ (w + wX) - (w + wX)‖ + ‖(wX : ℂ)‖ := norm_add_le _ _
      _ ≤ M + |wX| := by rw [Complex.norm_real, Real.norm_eq_abs]; linarith
  have hM'0 : 0 ≤ M' := (norm_nonneg _).trans (hM'b 0 (by simpa using hrealHbar 0))
  -- a common radius
  obtain ⟨R₀', hR₀'⟩ := ((hK.isBounded.union hYb).union hXc.isBounded).subset_ball 0
  set R₀ := max R₀' 1 with hR₀def
  have hR₀ : 0 < R₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hnorm : ∀ z ∈ K ∪ Y ∪ X, ‖z‖ < R₀ := fun z hz => by
    have := (hR₀'.trans (ball_subset_ball (le_max_left R₀' 1))) hz
    rwa [mem_ball_zero_iff] at this
  have hKR : K ⊆ ball 0 R₀ := fun z hz => mem_ball_zero_iff.2 (hnorm z (Or.inl (Or.inl hz)))
  have hnA : ∀ z ∈ Y, ‖z‖ < R₀ := fun z hz => hnorm z (Or.inl (Or.inr hz))
  have hnC : ∀ z ∈ X, ‖z‖ < R₀ := fun z hz => hnorm z (Or.inr hz)
  have hψ'Hbar : ∀ v ∈ Hbar, 0 ≤ (ψ' v).im := fun v hv =>
    im_nonneg_of_mapsTo hψ'c (fun v' hv' => (hψ'bij.mapsTo hv').1) hv
  have hdisp : ∀ v : ℝ, |v| - M' ≤ ‖ψ' v‖ := fun v => by
    have h1 := hM'b v (hrealHbar v)
    have h2 : ‖((v : ℝ) : ℂ)‖ ≤ ‖ψ' v‖ + ‖ψ' v - v‖ := by
      calc ‖((v : ℝ) : ℂ)‖ = ‖ψ' v - (ψ' v - v)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖ψ' v‖ + ‖ψ' v - v‖ := norm_sub_le _ _
    rw [norm_real, Real.norm_eq_abs] at h2
    linarith
  set w : ℝ := wY - wX with hwdef
  have hw0 : w < 0 := by rw [hwdef]; linarith
  have hψ'w : ψ' w = ψ wY := by simp [hψ', hwdef]
  set v' : ℝ := wY' - wX with hv'def
  have hv'0 : 0 < v' := by rw [hv'def]; linarith
  have hψ'v' : ψ' v' = ψ wY' := by simp [hψ', hv'def]
  have hψ'0 : ψ' 0 = ψ wX := by simp [hψ']
  set R : ℝ := 2 * R₀ + M' + 2 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hwR : -R < w := by
    have h1 := hdisp w
    have h2 := hnA _ hwY
    rw [hψ'w] at h1
    have h3 : |w| < R := by linarith
    linarith [neg_abs_le w]
  set c : ℝ := -R / 2 with hc
  set r : ℝ := R / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hcr0 : c + r = 0 := by rw [hc, hr]; ring
  have hcrR : c - r = -R := by rw [hc, hr]; ring
  set Sc := semicircle c r with hScdef
  have hScHbar : Sc ⊆ Hbar := fun v hv => ((mem_semicircle_iff hr0.le).1 hv).1
  have h0Sc : (0 : ℂ) ∈ Sc := by
    have := right_mem_semicircle (c := c) hr0.le
    rw [hcr0, ofReal_zero] at this
    exact this
  have hRSc : ((-R : ℝ) : ℂ) ∈ Sc := by
    have := left_mem_semicircle (c := c) hr0.le
    rw [hcrR] at this
    exact this
  set yL := ψ' ((-R : ℝ) : ℂ) with hyLdef
  have hyLn : R₀ < ‖yL‖ := by
    have := hdisp (-R)
    rw [← hyLdef, abs_neg, abs_of_pos hRpos] at this
    linarith
  have hyL0 : yL.im = 0 := by
    have hnH : ((-R : ℝ) : ℂ) ∉ H := fun h => by
      have : (0 : ℝ) < ((-R : ℝ) : ℂ).im := h
      simp at this
    refine le_antisymm (not_lt.1 fun hpos => hψ'real _ hnH ?_) (hψ'Hbar _ (hrealHbar _))
    exact mem_H_diff_fillH_of_le_norm hK.isClosed hR₀ hKR hpos hyLn.le
  have hyLre : yL.re ≤ -2 * R₀ - 2 := by
    have h1 := hM'b _ (hrealHbar (-R))
    rw [← hyLdef] at h1
    have h2 := Complex.abs_re_le_norm (yL - ((-R : ℝ) : ℂ))
    have h3 : (yL - ((-R : ℝ) : ℂ)).re = yL.re + R := by simp
    rw [h3] at h2
    have := le_abs_self (yL.re + R)
    linarith
  -- the crosscut `F = ψ'(S) ∪ X`
  set F := ψ' '' Sc ∪ X with hFdef
  have hScIm : IsCompact (ψ' '' Sc) := (isCompact_semicircle c r).image_of_continuousOn (hψ'c.mono hScHbar)
  have hFc : IsCompact F := hScIm.union hXc
  have hFpc : IsPreconnected F :=
    IsPreconnected.union (ψ wX) ⟨0, h0Sc, hψ'0⟩ hwX
      ((isPreconnected_semicircle c r).image ψ' (hψ'c.mono hScHbar)) hXpc
  have hFim : ∀ z ∈ F, 0 ≤ z.im := by
    rintro z (⟨v, hv, rfl⟩ | hzC)
    · exact hψ'Hbar v (hScHbar hv)
    · exact hXim z hzC
  have hSc : ∀ v ∈ Sc, (v ∈ H ∧ ψ' v ∈ H \ fillH K) ∨ ψ' v = ψ wX ∨ ψ' v = yL := by
    intro v hv
    by_cases hvH : v ∈ H
    · exact Or.inl ⟨hvH, hψ'bij.mapsTo hvH⟩
    · rcases eq_or_eq_of_mem_semicircle hr0 hv hvH with h | h
      · rw [h, hcr0, ofReal_zero, hψ'0]; exact Or.inr (Or.inl rfl)
      · rw [h, hcrR]; exact Or.inr (Or.inr rfl)
  have hgood : ∀ v ∈ H, ‖v - c‖ ≠ r → ψ' v ∈ H \ F := by
    intro v hv hvr
    have hvD := hψ'bij.mapsTo hv
    refine ⟨hvD.1, ?_⟩
    rintro (⟨v', hv', he⟩ | hC')
    · by_cases hv'H : v' ∈ H
      · exact hvr (by rw [← hψ'bij.injOn hv'H hv he]; exact norm_sub_of_mem_semicircle hr0.le hv')
      · exact hψ'real v' hv'H (by rw [he]; exact hvD)
    · exact hXD _ hC' hvD
  have hAF : Disjoint Y F := by
    rw [Set.disjoint_left]
    rintro z hzA (⟨v, hv, rfl⟩ | hzC)
    · rcases hSc v hv with ⟨-, hD⟩ | he | he
      · exact hYD _ hzA hD
      · rw [he] at hzA; exact Set.disjoint_left.1 hXY hwX hzA
      · rw [he] at hzA; exact absurd (hnA _ hzA) (not_lt.2 hyLn.le)
    · exact Set.disjoint_left.1 hXY hzC hzA
  -- `F` is free at the far chart point `ψ'(v')`, hence along `Y`
  have hv'F : ψ' v' ∉ F := fun h => Set.disjoint_left.1 hAF (by rw [hψ'v']; exact hwY') h
  have hfreev : IsFreeAt F (ψ' v') := by
    rcases isFreeAt_or_isTrappedAt hFc.isClosed hv'F with h | h
    · exact h
    · exfalso
      obtain ⟨ε, hε, hdis⟩ := h
      obtain ⟨δ₀, hδ₀, hcont⟩ := Metric.continuousWithinAt_iff.1 (hψ'c _ (hrealHbar v')) ε hε
      set δ : ℝ := δ₀ / 2 with hδdef
      have hδ : 0 < δ := half_pos hδ₀
      set q : ℂ := (v' : ℂ) + (δ : ℂ) * I with hqdef
      have hqH : q ∈ H := show 0 < q.im by simp [hqdef, hδ]
      have hqd : dist q (v' : ℂ) < δ₀ := by
        rw [dist_eq_norm, hqdef, add_sub_cancel_left, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs,
          abs_of_pos hδ]
        linarith
      have hqr : r < ‖q - c‖ := by
        have h1 := Complex.abs_re_le_norm (q - c)
        have h2 : (q - c).re = v' - c := by simp [hqdef]
        rw [h2, abs_of_pos (by linarith)] at h1
        linarith
      have hqF := mem_H_diff_fillH_of_ray hψ'c hM'b hFc.isClosed
        (fun v hv hvr => hgood v hv (ne_of_gt hvr)) hqH hqr
      exact Set.disjoint_left.1 hdis (mem_ball.2 (hcont (Sec7.Lemma76Exit.H_subset_Hbar hqH) hqd)) hqF
  have hAX : Y ⊆ {z | 0 ≤ z.im} \ F := fun z hz => ⟨hYim z hz, fun h => Set.disjoint_left.1 hAF hz h⟩
  have hfreew : IsFreeAt F (ψ' w) := by
    rcases isFreeAt_or_isTrappedAt_of_isPreconnected hFc.isClosed hYpc hAX with hall | hall
    · rw [hψ'w]; exact hall _ hwY
    · exact absurd (hall _ hwY') (by rw [← hψ'v']; exact hfreev.not_isTrappedAt (by rw [hψ'v']; exact hYim _ hwY'))
  obtain ⟨ε, hε, hfree⟩ := hfreew
  have hFsub : ∀ z ∈ F, z ∈ ψ' '' Sc ∨ ‖z‖ < R₀ := by
    rintro z (hz | hz)
    · exact Or.inl hz
    · exact Or.inr (hnC z hz)
  have hx₀R : -R₀ < x₀ := by
    have := hnC _ hx₀X
    rw [norm_real, Real.norm_eq_abs] at this
    linarith [neg_abs_le x₀]
  exact false_of_lt_aux hψ'c hψ'bij hK.isClosed hR₀ hKR hcr0 hcrR hgood
    (fun v hv hvr => (mem_semicircle_iff hr0.le).2 ⟨hv, hvr⟩) subset_union_left hSc (hnC _ hwX) hFsub rfl hRSc
    hyL0 hyLre hx₀R (Or.inr hx₀X) hM'b hFc hFpc hFim hwR hw0 hε hfree

end Aux85

end RLC

end InteractingSLE
