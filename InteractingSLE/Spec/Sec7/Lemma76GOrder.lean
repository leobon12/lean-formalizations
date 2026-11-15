/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76ESide
import InteractingSLE.Spec.Sec7.ReverseArcSign
import InteractingSLE.Foundations.Loewner.Reflect

/-!
# The order of the retained chart along the real line (Aux. lemma 60 generalized)

Packet PROVE-LEMMA76G (proof of Lemma 7.6, p. 269, with Aux. lemma 60). Let `ψ` be a chart inverse of
`D = ℍ \ fill K` (continuous on `ℍ̄`, a bijection `ℍ → D`, real points off `D`, bounded displacement). Let `A`, `C` be
disjoint compact connected subsets of `ℍ̄` off `D`, where `A` contains a real point `x` right of every real point of
`C`, and `C` contains a real point. Then every chart point of `C` is left of every chart point of `A`
(`lt_of_inv_mem`); mirror image: if `x ∈ A` is left of every real point of `C`, every chart point of `A` is left of
every chart point of `C` (`lt_of_inv_mem'`, by the reflection `z ↦ −z̄`).

This is PROVE-LEMMA76E's proof of Aux. lemma 60 (`Lemma76E.pos_of_inv_mem_fst`, the case `C = β([0, b])`,
`ψ(0) = β(b)`) with the second chart point arbitrary: the crosscut is `F = ψ(S) ∪ C`, `S` the closed upper semicircle
over `[−R, w_C]`; `A` misses `F` and contains `x`, which is free for `F`, so the half-disc image is free, while a
far-left real point `t` is trapped by `F` and adherent to `D \ F`. The aux lemma `false_of_lt_aux` is
`Lemma76E.false_of_neg_aux` with the second tip allowed on the real line (`‖β_b‖ < R₀` in place of `β_b ∈ ℍ`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Sec7

namespace Lemma76G

open HalfPlaneSep Restart Lemma76E

/-! ### The contradiction -/

/-- `Lemma76E.false_of_neg_aux` with the right end of the crosscut anywhere in `B(0, R₀)`. -/
theorem false_of_lt_aux {ψ : ℂ → ℂ} {K F Sc : Set ℂ} {M R₀ R c r x₂ w ε : ℝ} {yL βb : ℂ}
    (hψc : ContinuousOn ψ Hbar) (hbij : BijOn ψ H (H \ fillH K)) (hKcl : IsClosed K) (hR₀ : 0 < R₀)
    (hKR : K ⊆ ball 0 R₀) (hcr0 : c + r = 0) (hcrR : c - r = -R)
    (hgood : ∀ v ∈ H, ‖v - c‖ ≠ r → ψ v ∈ H \ F)
    (hScmem : ∀ v : ℂ, 0 ≤ v.im → ‖v - c‖ = r → v ∈ Sc) (hScF : ψ '' Sc ⊆ F)
    (hSc : ∀ v ∈ Sc, (v ∈ H ∧ ψ v ∈ H \ fillH K) ∨ ψ v = βb ∨ ψ v = yL) (hβbn : ‖βb‖ < R₀)
    (hFsub : ∀ z ∈ F, z ∈ ψ '' Sc ∨ ‖z‖ < R₀)
    (hyLψ : ψ ((-R : ℝ) : ℂ) = yL) (hRSc : ((-R : ℝ) : ℂ) ∈ Sc) (hyL0 : yL.im = 0) (hyLre : yL.re ≤ -2 * R₀ - 2)
    (hx₂R : -R₀ < x₂) (hx₂F : ((x₂ : ℝ) : ℂ) ∈ F) (hM : ∀ w ∈ Hbar, ‖ψ w - w‖ ≤ M)
    (hFc : IsCompact F) (hFpc : IsPreconnected F) (hFim : ∀ z ∈ F, 0 ≤ z.im)
    (hwR : -R < w) (hw0 : w < 0) (hε : 0 < ε) (hfree : ball (ψ w) ε ∩ H ⊆ H \ fillH F) : False := by
  have hrealHbar : ∀ v : ℝ, ((v : ℝ) : ℂ) ∈ Hbar := fun v => show (0 : ℝ) ≤ ((v : ℝ) : ℂ).im by simp
  -- a point of the half-disc image near `ψ(w)`
  have hwc : ‖((w : ℝ) : ℂ) - c‖ < r := by
    rw [← ofReal_sub, norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  obtain ⟨δ₀, hδ₀, hcont⟩ := Metric.continuousWithinAt_iff.1 (hψc _ (hrealHbar w)) ε hε
  set δ : ℝ := min (δ₀ / 2) ((r - ‖((w : ℝ) : ℂ) - c‖) / 2) with hδdef
  have hδ : 0 < δ := lt_min (half_pos hδ₀) (half_pos (sub_pos.2 hwc))
  have hδ1 : δ ≤ δ₀ / 2 := min_le_left _ _
  have hδ2 : δ ≤ (r - ‖((w : ℝ) : ℂ) - c‖) / 2 := min_le_right _ _
  set q : ℂ := (w : ℂ) + (δ : ℂ) * I with hqdef
  have hnδ : ‖(δ : ℂ) * I‖ = δ := by rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  have hqH : q ∈ H := show 0 < q.im by simp [hqdef, hδ]
  have hqdist : dist q w < δ₀ := by
    rw [dist_eq_norm, hqdef, add_sub_cancel_left, hnδ]
    linarith
  have hqc : ‖q - c‖ < r := by
    have : ‖q - c‖ ≤ ‖((w : ℝ) : ℂ) - c‖ + δ := by
      calc ‖q - c‖ = ‖(((w : ℝ) : ℂ) - c) + (δ : ℂ) * I‖ := by rw [hqdef]; ring_nf
        _ ≤ ‖((w : ℝ) : ℂ) - c‖ + ‖(δ : ℂ) * I‖ := norm_add_le _ _
        _ = ‖((w : ℝ) : ℂ) - c‖ + δ := by rw [hnδ]
    linarith
  have hpF : ψ q ∈ H \ fillH F :=
    hfree ⟨mem_ball.2 (hcont (Lemma76Exit.H_subset_Hbar hqH) hqdist), (hbij.mapsTo hqH).1⟩
  -- the half-disc image and the outer rays lie in the unbounded domain of `F`
  set Bh : Set ℂ := ball (c : ℂ) r ∩ H with hBhdef
  have hBhcv : Convex ℝ Bh :=
    (convex_ball _ _).inter (convex_halfSpace_gt (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0)
  have hBhpc : IsPreconnected (ψ '' Bh) :=
    hBhcv.isPreconnected.image ψ (hψc.mono fun z hz => Lemma76Exit.H_subset_Hbar hz.2)
  have hBhsub : ψ '' Bh ⊆ H \ F := by
    rintro _ ⟨v, hv, rfl⟩
    exact hgood v hv.2 (ne_of_lt (by simpa [dist_eq_norm] using hv.1))
  have hqBh : q ∈ Bh := ⟨by simpa [dist_eq_norm] using hqc, hqH⟩
  have hin : ∀ v ∈ H, ‖v - c‖ < r → ψ v ∈ H \ fillH F := fun v hv hvr =>
    connectedComponentIn_subset_H_diff_fillH hFc.isClosed hpF
      (hBhpc.subset_connectedComponentIn ⟨q, hqBh, rfl⟩ hBhsub
        ⟨v, ⟨by simpa [dist_eq_norm] using hvr, hv⟩, rfl⟩)
  have hout : ∀ v ∈ H, r < ‖v - c‖ → ψ v ∈ H \ fillH F := fun v hv hvr =>
    Lemma76E.mem_H_diff_fillH_of_ray hψc hM hFc.isClosed (fun v' hv' hv'r => hgood v' hv' (ne_of_gt hv'r)) hv hvr
  -- a trapped real point adherent to the domain
  set t : ℝ := yL.re + 1 with htdef
  have htn : R₀ < ‖((t : ℝ) : ℂ)‖ := by
    rw [norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  have hyLF : (((yL.re : ℝ)) : ℂ) ∈ F := hScF ⟨_, hRSc, by rw [Restart.ofReal_re_eq hyL0, hyLψ]⟩
  have htF : ((t : ℝ) : ℂ) ∉ F := by
    intro htF
    rcases hFsub _ htF with ⟨v, hv, he⟩ | hn
    · rcases hSc v hv with ⟨-, hD⟩ | he' | he'
      · have h1 := hD.1
        rw [he] at h1
        exact absurd h1 (by simp [H])
      · have h1 := hβbn
        rw [← he', he] at h1
        exact absurd h1 (not_lt.2 htn.le)
      · rw [he'] at he
        have h1 := congrArg Complex.re he
        simp only [ofReal_re] at h1
        rw [htdef] at h1
        linarith
    · exact absurd hn (not_lt.2 htn.le)
  have htrap := isTrappedAt_of_isPreconnected hFc hFpc hFim hyLF hx₂F (by linarith) (by linarith) htF
  obtain ⟨ε₂, hε₂, hdis₂⟩ := htrap
  obtain ⟨ε₃, hε₃, hball₃⟩ := Metric.isOpen_iff.1 hFc.isClosed.isOpen_compl _ htF
  set δ' : ℝ := min ε₂ ε₃ / 2 with hδ'def
  have hδ' : 0 < δ' := half_pos (lt_min hε₂ hε₃)
  have hδ'2 : δ' < ε₂ := by have := min_le_left ε₂ ε₃; rw [hδ'def]; linarith
  have hδ'3 : δ' < ε₃ := by have := min_le_right ε₂ ε₃; rw [hδ'def]; linarith
  set z : ℂ := (t : ℂ) + (δ' : ℂ) * I with hzdef
  have hzH : z ∈ H := show 0 < z.im by simp [hzdef, hδ']
  have hzdist : dist z t = δ' := by
    rw [dist_eq_norm, hzdef, add_sub_cancel_left, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs,
      abs_of_pos hδ']
  have hzn : R₀ ≤ ‖z‖ := by
    have h1 := abs_re_le_norm z
    have hre : z.re = t := by simp [hzdef]
    rw [hre, abs_of_neg (by linarith)] at h1
    linarith
  have hzD : z ∈ H \ fillH K := mem_H_diff_fillH_of_le_norm hKcl hR₀ hKR hzH hzn
  obtain ⟨v, hvH, hvz⟩ := hbij.surjOn hzD
  have hzF : z ∉ F := hball₃ (mem_ball.2 (by rw [hzdist]; exact hδ'3))
  have hvr : ‖v - c‖ ≠ r := fun h =>
    hzF (hScF ⟨v, hScmem v (show (0 : ℝ) < v.im from hvH).le h, hvz⟩)
  have hzFF : z ∈ H \ fillH F := by
    rw [← hvz]
    rcases lt_or_gt_of_ne hvr with h | h
    · exact hin v hvH h
    · exact hout v hvH h
  exact Set.disjoint_left.1 hdis₂ (mem_ball.2 (by rw [hzdist]; exact hδ'2)) hzFF


/-! ### The order of chart points -/

/-- **Chart points of `C` precede chart points of `A`** (Aux. lemma 60 generalized). `ψ` is a chart inverse of
`ℍ \ fill K`; `A`, `C` are disjoint compact connected subsets of `ℍ̄` off the domain; `A` contains a real point `x`
right of every real point of `C`, and `C` contains a real point. -/
theorem lt_of_inv_mem {ψ : ℂ → ℂ} {K A C : Set ℂ} (hK : IsCompact K) (hψc : ContinuousOn ψ Hbar)
    (hbij : BijOn ψ H (H \ fillH K)) (hreal : ∀ w ∉ H, ψ w ∉ H \ fillH K) {M : ℝ}
    (hM : ∀ w ∈ Hbar, ‖ψ w - w‖ ≤ M)
    (hAc : IsCompact A) (hApc : IsPreconnected A) (hAim : ∀ z ∈ A, 0 ≤ z.im) (hAD : ∀ z ∈ A, z ∉ H \ fillH K)
    (hCc : IsCompact C) (hCpc : IsPreconnected C) (hCim : ∀ z ∈ C, 0 ≤ z.im) (hCD : ∀ z ∈ C, z ∉ H \ fillH K)
    (hAC : Disjoint A C) {x : ℝ} (hxA : ((x : ℝ) : ℂ) ∈ A) (hCx : ∀ z ∈ C, z.im = 0 → z.re < x)
    {x₀ : ℝ} (hx₀C : ((x₀ : ℝ) : ℂ) ∈ C) {wA wC : ℝ} (hwA : ψ wA ∈ A) (hwC : ψ wC ∈ C) : wC < wA := by
  by_contra hle
  have hle' : wA ≤ wC := not_lt.1 hle
  have hne : wA ≠ wC := fun h => Set.disjoint_left.1 hAC hwA (h ▸ hwC)
  have hlt : wA < wC := lt_of_le_of_ne hle' hne
  have hrealHbar : ∀ v : ℝ, ((v : ℝ) : ℂ) ∈ Hbar := fun v => show (0 : ℝ) ≤ ((v : ℝ) : ℂ).im by simp
  -- the shifted chart
  set ψ' : ℂ → ℂ := fun z => ψ (z + wC) with hψ'
  have hshH : ∀ z : ℂ, z + (wC : ℂ) ∈ H ↔ z ∈ H := fun z => by
    show 0 < (z + (wC : ℂ)).im ↔ 0 < z.im
    simp
  have hshHbar : ∀ z ∈ Hbar, z + (wC : ℂ) ∈ Hbar := fun z hz => by
    show 0 ≤ (z + (wC : ℂ)).im
    simpa using (show 0 ≤ z.im from hz)
  have hψ'c : ContinuousOn ψ' Hbar :=
    hψc.comp (continuous_id.add continuous_const).continuousOn fun z hz => hshHbar z hz
  have hψ'bij : BijOn ψ' H (H \ fillH K) := by
    refine ⟨fun z hz => hbij.mapsTo ((hshH z).2 hz), fun z hz z' hz' he => ?_, fun y hy => ?_⟩
    · have := hbij.injOn ((hshH z).2 hz) ((hshH z').2 hz') he
      simpa using this
    · obtain ⟨v, hv, rfl⟩ := hbij.surjOn hy
      refine ⟨v - wC, (hshH _).1 (by simpa using hv), ?_⟩
      simp [hψ']
  have hψ'real : ∀ w ∉ H, ψ' w ∉ H \ fillH K := fun w hw => hreal _ fun h => hw ((hshH w).1 h)
  set M' : ℝ := M + |wC| with hM'
  have hM'b : ∀ w ∈ Hbar, ‖ψ' w - w‖ ≤ M' := fun w hw => by
    have h1 := hM _ (hshHbar w hw)
    have h2 : ψ' w - w = (ψ (w + wC) - (w + wC)) + (wC : ℂ) := by simp only [hψ']; ring
    rw [h2]
    calc ‖(ψ (w + wC) - (w + wC)) + (wC : ℂ)‖ ≤ ‖ψ (w + wC) - (w + wC)‖ + ‖(wC : ℂ)‖ := norm_add_le _ _
      _ ≤ M + |wC| := by rw [Complex.norm_real, Real.norm_eq_abs]; linarith
  have hM'0 : 0 ≤ M' := (norm_nonneg _).trans (hM'b 0 (by simpa using hrealHbar 0))
  -- a common radius
  obtain ⟨R₀', hR₀'⟩ := ((hK.union hAc).union hCc).isBounded.subset_ball 0
  set R₀ := max R₀' 1 with hR₀def
  have hR₀ : 0 < R₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hnorm : ∀ z ∈ K ∪ A ∪ C, ‖z‖ < R₀ := fun z hz => by
    have := (hR₀'.trans (ball_subset_ball (le_max_left R₀' 1))) hz
    rwa [mem_ball_zero_iff] at this
  have hKR : K ⊆ ball 0 R₀ := fun z hz => mem_ball_zero_iff.2 (hnorm z (Or.inl (Or.inl hz)))
  have hnA : ∀ z ∈ A, ‖z‖ < R₀ := fun z hz => hnorm z (Or.inl (Or.inr hz))
  have hnC : ∀ z ∈ C, ‖z‖ < R₀ := fun z hz => hnorm z (Or.inr hz)
  have hψ'Hbar : ∀ v ∈ Hbar, 0 ≤ (ψ' v).im := fun v hv =>
    im_nonneg_of_mapsTo hψ'c (fun v' hv' => (hψ'bij.mapsTo hv').1) hv
  have hdisp : ∀ v : ℝ, |v| - M' ≤ ‖ψ' v‖ := fun v => by
    have h1 := hM'b v (hrealHbar v)
    have h2 : ‖((v : ℝ) : ℂ)‖ ≤ ‖ψ' v‖ + ‖ψ' v - v‖ := by
      calc ‖((v : ℝ) : ℂ)‖ = ‖ψ' v - (ψ' v - v)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖ψ' v‖ + ‖ψ' v - v‖ := norm_sub_le _ _
    rw [norm_real, Real.norm_eq_abs] at h2
    linarith
  set w : ℝ := wA - wC with hwdef
  have hw0 : w < 0 := by rw [hwdef]; linarith
  have hψ'w : ψ' w = ψ wA := by simp [hψ', hwdef]
  have hψ'0 : ψ' 0 = ψ wC := by simp [hψ']
  set R : ℝ := 2 * R₀ + M' + 2 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hwR : -R < w := by
    have h1 := hdisp w
    have h2 := hnA _ hwA
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
  -- the crosscut `F = ψ'(S) ∪ C`
  set F := ψ' '' Sc ∪ C with hFdef
  have hScIm : IsCompact (ψ' '' Sc) := (isCompact_semicircle c r).image_of_continuousOn (hψ'c.mono hScHbar)
  have hFc : IsCompact F := hScIm.union hCc
  have hFpc : IsPreconnected F :=
    IsPreconnected.union (ψ wC) ⟨0, h0Sc, hψ'0⟩ hwC
      ((isPreconnected_semicircle c r).image ψ' (hψ'c.mono hScHbar)) hCpc
  have hFim : ∀ z ∈ F, 0 ≤ z.im := by
    rintro z (⟨v, hv, rfl⟩ | hzC)
    · exact hψ'Hbar v (hScHbar hv)
    · exact hCim z hzC
  have hSc : ∀ v ∈ Sc, (v ∈ H ∧ ψ' v ∈ H \ fillH K) ∨ ψ' v = ψ wC ∨ ψ' v = yL := by
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
    · exact hCD _ hC' hvD
  have hAF : Disjoint A F := by
    rw [Set.disjoint_left]
    rintro z hzA (⟨v, hv, rfl⟩ | hzC)
    · rcases hSc v hv with ⟨-, hD⟩ | he | he
      · exact hAD _ hzA hD
      · rw [he] at hzA; exact Set.disjoint_left.1 hAC hzA hwC
      · rw [he] at hzA; exact absurd (hnA _ hzA) (not_lt.2 hyLn.le)
    · exact Set.disjoint_left.1 hAC hzA hzC
  have hxR : -R₀ < x := by
    have := hnA _ hxA
    rw [norm_real, Real.norm_eq_abs] at this
    linarith [neg_abs_le x]
  -- `F` is free at `x`, hence along `A`
  have hfreex : IsFreeAt F x := by
    refine isFreeAt_of_forall_re_lt hFc fun z hz hz0 => ?_
    rcases hz with ⟨v, hv, rfl⟩ | hzC
    · rcases hSc v hv with ⟨-, hD⟩ | he | he
      · exact absurd hz0 (ne_of_gt hD.1)
      · rw [he] at hz0 ⊢; exact hCx _ hwC hz0
      · rw [he]; linarith
    · exact hCx z hzC hz0
  have hAX : A ⊆ {z | 0 ≤ z.im} \ F := fun z hz => ⟨hAim z hz, fun h => Set.disjoint_left.1 hAF hz h⟩
  have hfreew : IsFreeAt F (ψ' w) := by
    rcases isFreeAt_or_isTrappedAt_of_isPreconnected hFc.isClosed hApc hAX with hall | hall
    · rw [hψ'w]; exact hall _ hwA
    · exact absurd (hall _ hxA) (hfreex.not_isTrappedAt (by simp))
  obtain ⟨ε, hε, hfree⟩ := hfreew
  have hFsub : ∀ z ∈ F, z ∈ ψ' '' Sc ∨ ‖z‖ < R₀ := by
    rintro z (hz | hz)
    · exact Or.inl hz
    · exact Or.inr (hnC z hz)
  have hx₀R : -R₀ < x₀ := by
    have := hnC _ hx₀C
    rw [norm_real, Real.norm_eq_abs] at this
    linarith [neg_abs_le x₀]
  exact false_of_lt_aux hψ'c hψ'bij hK.isClosed hR₀ hKR hcr0 hcrR hgood
    (fun v hv hvr => (mem_semicircle_iff hr0.le).2 ⟨hv, hvr⟩) subset_union_left hSc (hnC _ hwC) hFsub rfl hRSc
    hyL0 hyLre hx₀R (Or.inr hx₀C) hM'b hFc hFpc hFim hwR hw0 hε hfree

/-- **The mirror image**: if `A` contains a real point `x` left of every real point of `C`, every chart point of `A` is
left of every chart point of `C` (reflection `z ↦ −z̄`). -/
theorem lt_of_inv_mem' {ψ : ℂ → ℂ} {K A C : Set ℂ} (hK : IsCompact K) (hψc : ContinuousOn ψ Hbar)
    (hbij : BijOn ψ H (H \ fillH K)) (hreal : ∀ w ∉ H, ψ w ∉ H \ fillH K) {M : ℝ}
    (hM : ∀ w ∈ Hbar, ‖ψ w - w‖ ≤ M)
    (hAc : IsCompact A) (hApc : IsPreconnected A) (hAim : ∀ z ∈ A, 0 ≤ z.im) (hAD : ∀ z ∈ A, z ∉ H \ fillH K)
    (hCc : IsCompact C) (hCpc : IsPreconnected C) (hCim : ∀ z ∈ C, 0 ≤ z.im) (hCD : ∀ z ∈ C, z ∉ H \ fillH K)
    (hAC : Disjoint A C) {x : ℝ} (hxA : ((x : ℝ) : ℂ) ∈ A) (hCx : ∀ z ∈ C, z.im = 0 → x < z.re)
    {x₀ : ℝ} (hx₀C : ((x₀ : ℝ) : ℂ) ∈ C) {wA wC : ℝ} (hwA : ψ wA ∈ A) (hwC : ψ wC ∈ C) : wA < wC := by
  set Rf := LP.reflectC with hRf
  have hRH : ∀ z, LP.reflectHomeo z ∈ H ↔ z ∈ H := fun z => LP.reflectC_mem_H_iff
  have hRb : ∀ S : Set ℂ, IsBounded (LP.reflectHomeo '' S) ↔ IsBounded S := fun S =>
    LP.isBounded_reflectC_image_iff
  have hRHbar : ∀ z ∈ Hbar, Rf z ∈ Hbar := fun z hz => show 0 ≤ (Rf z).im by
    rw [hRf, LP.im_reflectC]; exact hz
  have hD : H \ fillH (Rf '' K) = Rf '' (H \ fillH K) := by
    have h1 := ReverseArc.fillH_image_homeomorph LP.reflectHomeo hRH hRb K
    have h2 := ReverseArc.image_H_diff_homeomorph LP.reflectHomeo hRH (fillH K)
    rw [LP.coe_reflectHomeo] at h1 h2
    rw [h1, h2]
  set ψ' : ℂ → ℂ := fun z => Rf (ψ (Rf z)) with hψ'
  have hψ'c : ContinuousOn ψ' Hbar :=
    LP.continuous_reflectC.comp_continuousOn (hψc.comp LP.continuous_reflectC.continuousOn hRHbar)
  have hψ'bij : BijOn ψ' H (H \ fillH (Rf '' K)) := by
    rw [hD]
    refine ⟨fun z hz => ⟨ψ (Rf z), hbij.mapsTo (LP.reflectC_mem_H_iff.2 hz), rfl⟩,
      fun z hz z' hz' he => ?_, fun y hy => ?_⟩
    · have h1 := LP.reflectC_injective he
      have h2 := hbij.injOn (LP.reflectC_mem_H_iff.2 hz) (LP.reflectC_mem_H_iff.2 hz') h1
      exact LP.reflectC_injective h2
    · obtain ⟨d, hd, rfl⟩ := hy
      obtain ⟨v, hv, rfl⟩ := hbij.surjOn hd
      exact ⟨Rf v, LP.reflectC_mem_H_iff.2 hv, by simp [hψ', hRf]⟩
  have hψ'real : ∀ w ∉ H, ψ' w ∉ H \ fillH (Rf '' K) := by
    intro w hw
    rw [hD]
    rintro ⟨d, hd, he⟩
    have := LP.reflectC_injective he
    exact hreal (Rf w) (fun h => hw (LP.reflectC_mem_H_iff.1 h)) (this ▸ hd)
  have hM' : ∀ w ∈ Hbar, ‖ψ' w - w‖ ≤ M := fun w hw => by
    have h1 := hM _ (hRHbar w hw)
    have h2 : ψ' w - w = Rf (ψ (Rf w) - Rf w) := by simp [hψ', hRf, LP.reflectC]; ring
    rwa [h2, hRf, LP.norm_reflectC]
  have himR : ∀ S : Set ℂ, (∀ z ∈ S, 0 ≤ z.im) → ∀ z ∈ Rf '' S, 0 ≤ z.im := by
    rintro S hS _ ⟨z, hz, rfl⟩
    rw [hRf, LP.im_reflectC]; exact hS z hz
  have hDR : ∀ S : Set ℂ, (∀ z ∈ S, z ∉ H \ fillH K) → ∀ z ∈ Rf '' S, z ∉ H \ fillH (Rf '' K) := by
    rintro S hS _ ⟨z, hz, rfl⟩ hmem
    rw [hD] at hmem
    obtain ⟨d, hd, he⟩ := hmem
    exact hS z hz (LP.reflectC_injective he ▸ hd)
  have hofR : ∀ t : ℝ, Rf ((t : ℝ) : ℂ) = ((-t : ℝ) : ℂ) := fun t => LP.reflectC_ofReal t
  have hlt := lt_of_inv_mem (ψ := ψ') (K := Rf '' K) (A := Rf '' A) (C := Rf '' C) (x := -x) (x₀ := -x₀)
    (wA := -wA) (wC := -wC) (hK.image LP.continuous_reflectC) hψ'c hψ'bij hψ'real hM'
    (hAc.image LP.continuous_reflectC) (hApc.image _ LP.continuous_reflectC.continuousOn) (himR A hAim)
    (hDR A hAD) (hCc.image LP.continuous_reflectC) (hCpc.image _ LP.continuous_reflectC.continuousOn)
    (himR C hCim) (hDR C hCD)
    (by
      rw [Set.disjoint_left]
      rintro _ ⟨a, ha, rfl⟩ ⟨c, hc, he⟩
      exact Set.disjoint_left.1 hAC ha (LP.reflectC_injective he ▸ hc))
    ⟨x, hxA, hofR x⟩
    (by
      rintro _ ⟨c, hc, rfl⟩ hc0
      rw [hRf, LP.im_reflectC] at hc0
      have := hCx c hc hc0
      have e : (Rf c).re = -c.re := by simp [hRf, LP.reflectC]
      rw [e]; linarith)
    ⟨x₀, hx₀C, hofR x₀⟩
    ⟨ψ wA, hwA, by simp only [hψ', hofR, neg_neg]⟩ ⟨ψ wC, hwC, by simp only [hψ', hofR, neg_neg]⟩
  linarith

end Lemma76G

end Sec7

end InteractingSLE
