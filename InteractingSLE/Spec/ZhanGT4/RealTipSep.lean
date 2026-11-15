/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.CrosscutJordan

/-!
# The access curve separates: the deterministic core of §A.4.3

Packet PROVE-ZHAN-GT4-A3. Source: Astra, *Follow-up proofs and dependency audit*, Part A.4.3
(`source/external/AstraIG1/ig1_followup_proofs.txt` L798–L831, ruling R38) and its second rendering, the
additional note's Theorem 2.12 (`ig1_additional_proofs.txt` L1240–L1281, ruling R39): "Suppose instead that
`z = η(T) ∈ ℝ` and `c < W < d`. The access curve `y ↦ f(W + iy)` joins `z` to infinity in the active domain and
divides `ℍ` into two sides."

This file is the planar topology of that sentence, for an abstract boundary map `F` (`IsBoundaryMap`: continuous on
`ℍ̄`, holomorphic data not needed, injective on `ℍ`, `F(ℍ) ⊆ ℍ`, bounded displacement), whose value `p = F(0)` at
the driver coordinate is real.

## The separation

The access arc `α = F(i(0, ∞))` (`accessArc`) runs from `p` to `∞`. For a real pole `x₀ < p`, the Möbius map
`M(z) = (x₀ − z)⁻¹` (`poleInv`) preserves `ℍ`, sends `∞` to `0` and `[p, ∞)` onto `[M(p), 0)`; so `M(α)` is a
crosscut from `M(p)` to `0` (`accessCrosscut`), and with the real segment `[M(p), 0]` it is a Jordan curve
(`isJordanCurve_crosscutCurve`). Its inside `J ⊆ ℍ` pulls back to the **right side** `R = ℍ ∩ M⁻¹(J)` of `α`
(`exists_accessSide`):

* `F` maps the open first quadrant into `R` (it is connected, misses the curve, and near a real point `F(x₁) > p`
  its image enters `J` through the open segment);
* a point of `ℍ \ α` in the closure of `R` is in `R`;
* a connected set `S` missing `α` and the pole whose real points are all `< p` and which meets `R` lies in `ℍ`
  (its `M`-image misses the curve, so it lies in `J ⊆ ℍ`).

## The contradiction (`false_of_real_tip_core`)

If moreover a boundary value `w = F(u)`, `u > 0`, is an interior point not in `F(ℍ)` and is a point `η(t₀)` of a
continuous path, then `w ∈ R`, and a rational time `r ∈ (0, t₀)` has `η(r) ∈ R`. A connected set
`S = G_r([u_r, 0])` from `G_r(0) = η(r)` to a real point, missing `F(ℍ)` and with nonpositive real points, would then
lie in `ℍ` — impossible. In `RealTip.lean`, `F = F̄_T` and `G_r = F̄_r` for a Loewner chain, and the hypotheses are the
interior open sides at the rational times (A.4.2).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Bornology

namespace InteractingSLE.ZhanGT4

open QuantumZipper

/-! ### The Möbius map with a real pole -/

/-- The Möbius map `z ↦ (x₀ − z)⁻¹` with a real pole `x₀`: it preserves `ℍ`, sends `∞` to `0`, and is increasing on
the real ray `(x₀, ∞)`, which it maps onto `(−∞, 0)`. -/
def poleInv (x₀ : ℝ) (z : ℂ) : ℂ := ((x₀ : ℂ) - z)⁻¹

theorem poleInv_im (x₀ : ℝ) (z : ℂ) : (poleInv x₀ z).im = z.im / normSq ((x₀ : ℂ) - z) := by
  simp [poleInv, Complex.inv_im]

theorem sub_ne_zero_of_ne {x₀ : ℝ} {z : ℂ} (hz : z ≠ x₀) : (x₀ : ℂ) - z ≠ 0 :=
  sub_ne_zero.2 (Ne.symm hz)

theorem poleInv_mem_H {x₀ : ℝ} {z : ℂ} (hz : z ∈ H) : poleInv x₀ z ∈ H := by
  have hne : z ≠ x₀ := fun h => by
    have : (0 : ℝ) < z.im := hz
    rw [h, ofReal_im] at this; exact lt_irrefl _ this
  show 0 < (poleInv x₀ z).im
  rw [poleInv_im]
  exact div_pos hz (normSq_pos.2 (sub_ne_zero_of_ne hne))

theorem mem_H_of_poleInv_mem_H {x₀ : ℝ} {z : ℂ} (hz : z ≠ x₀) (h : poleInv x₀ z ∈ H) : z ∈ H := by
  have h' : 0 < (poleInv x₀ z).im := h
  rw [poleInv_im] at h'
  have hn : 0 < normSq ((x₀ : ℂ) - z) := normSq_pos.2 (sub_ne_zero_of_ne hz)
  have := (div_pos_iff_of_pos_right hn).1 h'
  exact this

theorem im_eq_zero_of_poleInv {x₀ : ℝ} {z : ℂ} (hz : z ≠ x₀) (h : (poleInv x₀ z).im = 0) : z.im = 0 := by
  rw [poleInv_im] at h
  have hn : normSq ((x₀ : ℂ) - z) ≠ 0 := (normSq_pos.2 (sub_ne_zero_of_ne hz)).ne'
  rcases div_eq_zero_iff.1 h with h | h
  · exact h
  · exact absurd h hn

theorem poleInv_ofReal (x₀ x : ℝ) : poleInv x₀ (x : ℂ) = ((x₀ - x)⁻¹ : ℝ) := by
  simp [poleInv]

theorem poleInv_ne_zero {x₀ : ℝ} {z : ℂ} (hz : z ≠ x₀) : poleInv x₀ z ≠ 0 :=
  inv_ne_zero (sub_ne_zero_of_ne hz)

theorem poleInv_inj {x₀ : ℝ} {z₁ z₂ : ℂ} (h : poleInv x₀ z₁ = poleInv x₀ z₂) : z₁ = z₂ := by
  have := inv_injective h
  linear_combination -this

theorem continuousAt_poleInv {x₀ : ℝ} {z : ℂ} (hz : z ≠ x₀) : ContinuousAt (poleInv x₀) z :=
  (continuousAt_const.sub continuousAt_id).inv₀ (sub_ne_zero_of_ne hz)

theorem continuousOn_poleInv {x₀ : ℝ} {S : Set ℂ} (hS : (x₀ : ℂ) ∉ S) : ContinuousOn (poleInv x₀) S :=
  fun _ hz => (continuousAt_poleInv fun h => hS (h ▸ hz)).continuousWithinAt

theorem tendsto_poleInv_cobounded (x₀ : ℝ) : Tendsto (poleInv x₀) (cobounded ℂ) (𝓝 0) := by
  have h1 : Tendsto (fun z : ℂ => (x₀ : ℂ) - z) (cobounded ℂ) (cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    refine tendsto_atTop_mono (fun z => ?_) (tendsto_norm_atTop_iff_cobounded.2 tendsto_id |>.atTop_add
      (tendsto_const_nhds (x := -‖(x₀ : ℂ)‖)))
    have := norm_sub_norm_le z (x₀ : ℂ)
    rw [norm_sub_rev] at this
    show ‖z‖ + -‖(x₀ : ℂ)‖ ≤ ‖(x₀ : ℂ) - z‖
    linarith
  exact tendsto_inv₀_cobounded.comp h1

/-! ### Boundary maps and the access arc -/

/-- **A boundary map**: the properties of the continuous extension `F̄_T` of a Loewner inverse map that the
separation argument uses — continuous on `ℍ̄`, injective on `ℍ`, `F(ℍ) ⊆ ℍ`, at bounded distance from the
identity on `ℍ`. -/
structure IsBoundaryMap (F : ℂ → ℂ) : Prop where
  cont : ContinuousOn F Hbar
  inj : InjOn F H
  mapsTo : MapsTo F H H
  bdd : ∃ C : ℝ, ∀ w ∈ H, ‖F w - w‖ ≤ C

/-- **The access arc** `α = F(i(0, ∞))`: the image of the imaginary axis above the driver coordinate. -/
def accessArc (F : ℂ → ℂ) : Set ℂ := (fun y : ℝ => F (I * y)) '' Ioi 0

theorem I_mul_mem_H {y : ℝ} (hy : 0 < y) : I * (y : ℂ) ∈ H := by
  show 0 < (I * (y : ℂ)).im
  simpa using hy

theorem I_mul_mem_Hbar {y : ℝ} (hy : 0 ≤ y) : I * (y : ℂ) ∈ Hbar := by
  show 0 ≤ (I * (y : ℂ)).im
  simpa using hy

theorem accessArc_subset_image (F : ℂ → ℂ) : accessArc F ⊆ F '' H := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨_, I_mul_mem_H hy, rfl⟩

theorem ofReal_mem_Hbar (x : ℝ) : (x : ℂ) ∈ Hbar := by
  show (0 : ℝ) ≤ (x : ℂ).im
  simp

theorem not_mem_H_of_im_eq_zero {z : ℂ} (h : z.im = 0) : z ∉ H := fun hz => by
  have : (0 : ℝ) < z.im := hz
  rw [h] at this; exact lt_irrefl _ this


/-! ### The access crosscut -/

/-- The parameter change `s ↦ s / (1 − s)` from `[0, 1)` onto `[0, ∞)`. -/
def accessParam (s : ℝ) : ℝ := s / (1 - s)

theorem accessParam_nonneg {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : 0 ≤ accessParam s :=
  div_nonneg hs.1 (by linarith [hs.2])

theorem accessParam_pos {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) : 0 < accessParam s :=
  div_pos hs.1 (by linarith [hs.2])

theorem accessParam_eq_zero {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) (h : accessParam s = 0) : s = 0 := by
  rcases div_eq_zero_iff.1 h with h | h
  · exact h
  · linarith [hs.2]

theorem accessParam_inj {s t : ℝ} (hs : s < 1) (ht : t < 1) (h : accessParam s = accessParam t) : s = t := by
  unfold accessParam at h
  rw [div_eq_div_iff (by linarith) (by linarith)] at h
  linarith

theorem tendsto_accessParam : Tendsto accessParam (𝓝[<] 1) atTop := by
  have h1 : Tendsto (fun s : ℝ => 1 - s) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun s hs => ?_⟩
    · have : Tendsto (fun s : ℝ => 1 - s) (𝓝 1) (𝓝 (1 - 1)) := tendsto_const_nhds.sub tendsto_id
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · show (0 : ℝ) < 1 - s
      have : s < 1 := hs
      linarith
  have h2 : Tendsto (fun s : ℝ => (1 - s)⁻¹) (𝓝[<] 1) atTop := tendsto_inv_nhdsGT_zero.comp h1
  have h3 : Tendsto (fun s : ℝ => s) (𝓝[<] 1) (𝓝 1) := tendsto_id.mono_left nhdsWithin_le_nhds
  refine (h2.atTop_mul_pos one_pos h3).congr fun s => ?_
  simp [accessParam, div_eq_mul_inv, mul_comm]

/-- **The access crosscut** `γ(s) = M(F(i s/(1 − s)))` for `s < 1` and `γ(1) = 0`: the image of the access arc
under the Möbius map `M = poleInv x₀`, closed at `M(∞) = 0`. -/
def accessCrosscut (F : ℂ → ℂ) (x₀ : ℝ) (s : ℝ) : ℂ :=
  if s < 1 then poleInv x₀ (F (I * (accessParam s : ℂ))) else 0

variable {F : ℂ → ℂ} {x₀ : ℝ}

theorem accessCrosscut_of_lt {s : ℝ} (hs : s < 1) :
    accessCrosscut F x₀ s = poleInv x₀ (F (I * (accessParam s : ℂ))) := by
  simp [accessCrosscut, hs]

theorem accessCrosscut_one : accessCrosscut F x₀ 1 = 0 := by simp [accessCrosscut]

theorem accessCrosscut_zero (h0 : (F 0).im = 0) :
    accessCrosscut F x₀ 0 = ((x₀ - (F 0).re)⁻¹ : ℝ) := by
  rw [accessCrosscut_of_lt one_pos, show accessParam 0 = 0 by simp [accessParam], ofReal_zero, mul_zero,
    eq_ofReal_re_of_im_eq_zero h0, poleInv_ofReal, ofReal_re]

/-- The values `F(iy)`, `y ≥ 0`, avoid the pole. -/
theorem F_I_mul_ne (hF : IsBoundaryMap F) (hx₀ : x₀ < (F 0).re) {y : ℝ} (hy : 0 ≤ y) :
    F (I * (y : ℂ)) ≠ x₀ := by
  rcases hy.lt_or_eq with hy | rfl
  · intro h
    have := hF.mapsTo (I_mul_mem_H hy)
    rw [h] at this
    exact not_mem_H_of_im_eq_zero (by simp) this
  · intro h
    rw [ofReal_zero, mul_zero] at h
    have := congrArg Complex.re h
    rw [ofReal_re] at this
    linarith

theorem accessCrosscut_mem_H (hF : IsBoundaryMap F) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    accessCrosscut F x₀ s ∈ H := by
  rw [accessCrosscut_of_lt hs.2]
  exact poleInv_mem_H (hF.mapsTo (I_mul_mem_H (accessParam_pos hs)))

theorem tendsto_F_I_mul_cobounded (hF : IsBoundaryMap F) :
    Tendsto (fun y : ℝ => F (I * (y : ℂ))) atTop (cobounded ℂ) := by
  obtain ⟨C, hC⟩ := hF.bdd
  rw [← tendsto_norm_atTop_iff_cobounded]
  refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right atTop (-C) tendsto_id)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  have h1 := hC _ (I_mul_mem_H hy)
  have h2 : ‖I * (y : ℂ)‖ = y := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
  have h3 := norm_sub_norm_le (I * (y : ℂ)) (F (I * (y : ℂ)))
  rw [norm_sub_rev] at h3
  show y + -C ≤ ‖F (I * (y : ℂ))‖
  linarith

theorem continuousOn_accessCrosscut (hF : IsBoundaryMap F) (hx₀ : x₀ < (F 0).re) :
    ContinuousOn (accessCrosscut F x₀) (Icc 0 1) := by
  set g : ℝ → ℂ := fun s => poleInv x₀ (F (I * (accessParam s : ℂ))) with hg
  have hgc : ∀ s ∈ Icc (0 : ℝ) 1, s < 1 → ContinuousWithinAt g (Icc 0 1) s := by
    intro s hs hs1
    have hp : ContinuousAt accessParam s :=
      continuousAt_id.div (continuousAt_const.sub continuousAt_id) (by linarith)
    have hw : ContinuousWithinAt (fun t : ℝ => I * (accessParam t : ℂ)) (Icc 0 1) s :=
      (continuousAt_const.mul (continuous_ofReal.continuousAt.comp hp)).continuousWithinAt
    have hmaps : MapsTo (fun t : ℝ => I * (accessParam t : ℂ)) (Icc 0 1) Hbar := fun t ht =>
      I_mul_mem_Hbar (accessParam_nonneg ht)
    have hFw : ContinuousWithinAt (fun t : ℝ => F (I * (accessParam t : ℂ))) (Icc 0 1) s :=
      ContinuousWithinAt.comp (g := F) (f := fun t : ℝ => I * (accessParam t : ℂ)) (hF.cont _ (hmaps hs)) hw hmaps
    exact ContinuousAt.comp_continuousWithinAt (g := poleInv x₀) (f := fun t : ℝ => F (I * (accessParam t : ℂ)))
      (continuousAt_poleInv (F_I_mul_ne hF hx₀ (accessParam_nonneg hs))) hFw
  intro s hs
  rcases hs.2.lt_or_eq with hs1 | rfl
  · refine (hgc s hs hs1).congr_of_eventuallyEq ?_ (accessCrosscut_of_lt hs1)
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hs1)] with t ht
    exact accessCrosscut_of_lt ht
  · refine ContinuousWithinAt.mono ?_ (Icc_subset_Iic_self (a := (0 : ℝ)))
    rw [← continuousWithinAt_Iio_iff_Iic]
    show Tendsto _ _ _
    rw [accessCrosscut_one]
    have hlim : Tendsto g (𝓝[<] 1) (𝓝 0) :=
      (tendsto_poleInv_cobounded x₀).comp ((tendsto_F_I_mul_cobounded hF).comp tendsto_accessParam)
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (accessCrosscut_of_lt ht).symm

theorem injOn_accessCrosscut (hF : IsBoundaryMap F) (h0 : (F 0).im = 0) (hx₀ : x₀ < (F 0).re) :
    InjOn (accessCrosscut F x₀) (Icc 0 1) := by
  have key : ∀ s ∈ Icc (0 : ℝ) 1, s < 1 → ∀ t ∈ Icc (0 : ℝ) 1, t < 1 →
      accessCrosscut F x₀ s = accessCrosscut F x₀ t → s = t := by
    intro s hs hs1 t ht ht1 h
    rw [accessCrosscut_of_lt hs1, accessCrosscut_of_lt ht1] at h
    have hF' := poleInv_inj h
    have ha := accessParam_nonneg hs
    have hb := accessParam_nonneg ht
    refine accessParam_inj hs1 ht1 ?_
    rcases ha.lt_or_eq with ha | ha <;> rcases hb.lt_or_eq with hb | hb
    · have := hF.inj (I_mul_mem_H ha) (I_mul_mem_H hb) hF'
      have := congrArg Complex.im this
      simpa using this
    · rw [← hb, ofReal_zero, mul_zero] at hF'
      have := hF.mapsTo (I_mul_mem_H ha)
      rw [hF'] at this
      exact absurd this (not_mem_H_of_im_eq_zero h0)
    · rw [← ha, ofReal_zero, mul_zero] at hF'
      have := hF.mapsTo (I_mul_mem_H hb)
      rw [← hF'] at this
      exact absurd this (not_mem_H_of_im_eq_zero h0)
    · rw [← ha, ← hb]
  intro s hs t ht h
  rcases hs.2.lt_or_eq with hs1 | rfl <;> rcases ht.2.lt_or_eq with ht1 | rfl
  · exact key s hs hs1 t ht ht1 h
  · rw [accessCrosscut_one, accessCrosscut_of_lt hs1] at h
    exact absurd h (poleInv_ne_zero (F_I_mul_ne hF hx₀ (accessParam_nonneg hs)))
  · rw [accessCrosscut_one, accessCrosscut_of_lt ht1] at h
    exact absurd h.symm (poleInv_ne_zero (F_I_mul_ne hF hx₀ (accessParam_nonneg ht)))
  · rfl

theorem isRealCrosscut_accessCrosscut (hF : IsBoundaryMap F) (h0 : (F 0).im = 0) (hx₀ : x₀ < (F 0).re) :
    IsRealCrosscut (accessCrosscut F x₀) := by
  refine ⟨continuousOn_accessCrosscut hF hx₀, injOn_accessCrosscut hF h0 hx₀, ?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact accessCrosscut_mem_H hF hs
  · rw [accessCrosscut_zero h0, ofReal_im]
  · rw [accessCrosscut_one, zero_im]

theorem accessCrosscut_re_lt (h0 : (F 0).im = 0) (hx₀ : x₀ < (F 0).re) :
    (accessCrosscut F x₀ 0).re < (accessCrosscut F x₀ 1).re := by
  rw [accessCrosscut_zero h0, accessCrosscut_one, ofReal_re, zero_re]
  exact inv_lt_zero.2 (by linarith)

/-! ### The right side of the access arc -/

/-- A point off the pole whose Möbius image lies on the closed access curve is a point of the access arc, or a real
point `≥ p = F(0)`. -/
theorem mem_accessArc_or_of_poleInv_mem (hF : IsBoundaryMap F) (h0 : (F 0).im = 0) (hx₀ : x₀ < (F 0).re)
    {z : ℂ} (hz : z ≠ x₀) (h : poleInv x₀ z ∈ crosscutCurve (accessCrosscut F x₀)) :
    z ∈ accessArc F ∨ (z.im = 0 ∧ (F 0).re ≤ z.re) := by
  have hγ := isRealCrosscut_accessCrosscut hF h0 hx₀
  rcases h with ⟨s, hs, hzs⟩ | ⟨s, hs, hzs⟩
  · rcases hs.2.lt_or_eq with hs1 | rfl
    · rw [accessCrosscut_of_lt hs1] at hzs
      have hzF := (poleInv_inj hzs).symm
      rcases (accessParam_nonneg hs).lt_or_eq with ha | ha
      · exact Or.inl ⟨_, ha, hzF.symm⟩
      · rw [← ha, ofReal_zero, mul_zero] at hzF
        right
        rw [hzF]
        exact ⟨h0, le_rfl⟩
    · rw [accessCrosscut_one] at hzs
      exact absurd hzs.symm (poleInv_ne_zero hz)
  · right
    have him : (poleInv x₀ z).im = 0 := by rw [← hzs]; exact crosscutSeg_im hγ s
    have hzim := im_eq_zero_of_poleInv hz him
    refine ⟨hzim, ?_⟩
    have hzr : z = (z.re : ℂ) := eq_ofReal_re_of_im_eq_zero hzim
    have hre := congrArg Complex.re hzs
    rw [crosscutSeg_re, accessCrosscut_zero h0, accessCrosscut_one, hzr, poleInv_ofReal] at hre
    simp only [ofReal_re, zero_re] at hre
    by_contra hlt
    push Not at hlt
    have hne : z.re ≠ x₀ := fun h => hz (by rw [hzr, h])
    have hb : x₀ - (F 0).re < 0 := by linarith
    have hbinv : (x₀ - (F 0).re)⁻¹ < 0 := inv_lt_zero.2 hb
    rcases lt_or_gt_of_ne hne with h1 | h1
    · have : 0 < (x₀ - z.re)⁻¹ := inv_pos.2 (by linarith)
      nlinarith [hs.1, hs.2]
    · have ha : x₀ - z.re < 0 := by linarith
      have hlt' : (x₀ - z.re)⁻¹ < (x₀ - (F 0).re)⁻¹ := (inv_lt_inv_of_neg ha hb).2 (by linarith)
      nlinarith [hs.1, hs.2]

/-- **Half-disc neighbourhoods in the inside** of the real points strictly between the ends of a crosscut, for any
open `V ⊆ ℍ` whose frontier is the closed curve (`IsCrosscutDomain.exists_ball_inter_H_subset_inside`, whose proof
uses only the crosscut, without the domain). -/
theorem exists_ball_inter_H_subset_of_frontier_eq {γ : ℝ → ℂ} (hγ : IsRealCrosscut γ)
    (hlt : (γ 0).re < (γ 1).re) {V : Set ℂ} (hVo : IsOpen V) (hVH : V ⊆ H)
    (hfr : frontier V = crosscutCurve γ) {x : ℝ} (hx : x ∈ Ioo (γ 0).re (γ 1).re) :
    ∃ r > (0 : ℝ), ball (x : ℂ) r ∩ H ⊆ V := by
  have hK : IsClosed (γ '' Icc 0 1) := (isCompact_Icc.image_of_continuousOn hγ.1).isClosed
  have hxK : (x : ℂ) ∉ γ '' Icc 0 1 := by
    rintro ⟨s, hs, hsx⟩
    have him : (γ s).im = 0 := by rw [hsx]; simp
    have hre : (γ s).re = x := by rw [hsx]; simp
    rcases hγ.eq_of_im_eq_zero hs him with rfl | rfl
    · linarith [hx.1]
    · linarith [hx.2]
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hK.isOpen_compl _ hxK
  refine ⟨r, hr, ?_⟩
  have hconv : Convex ℝ (ball (x : ℂ) r ∩ H) :=
    (convex_ball _ r).inter (convex_halfSpace_gt (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0)
  have hxV : (x : ℂ) ∈ closure V := by
    have : (x : ℂ) ∈ frontier V := by
      rw [hfr]; exact mem_crosscutCurve_of_real hγ hlt (Ioo_subset_Icc_self hx)
    exact this.1
  obtain ⟨v, hvV, hvd⟩ := Metric.mem_closure_iff.1 hxV r hr
  refine hconv.isPreconnected.subset_left_of_subset_union hVo isClosed_closure.isOpen_compl
    (Set.disjoint_left.2 fun z hz hz' => hz' (subset_closure hz)) (fun z hz => ?_)
    ⟨v, ⟨by rw [mem_ball, dist_comm]; exact hvd, hVH hvV⟩, hvV⟩
  by_cases hzV : z ∈ V
  · exact Or.inl hzV
  refine Or.inr fun hzc => ?_
  have hzf : z ∈ frontier V := ⟨hzc, by rwa [hVo.interior_eq]⟩
  rw [hfr] at hzf
  rcases hzf with hzγ | ⟨s, -, rfl⟩
  · exact hball hz.1 hzγ
  · have : 0 < (crosscutSeg γ s).im := hz.2
    rw [crosscutSeg_im hγ] at this
    exact lt_irrefl _ this

theorem not_mem_H_ofReal (x : ℝ) : (x : ℂ) ∉ H := not_mem_H_of_im_eq_zero (by simp)

/-- **The right side of the access arc.** For a boundary map `F` with `p = F(0)` real, a pole `x₀ < p` and a positive
real coordinate `x₁` with `F(x₁)` real and `> p`, there is an open `R ⊆ ℍ` (the pullback of the inside of the closed
access curve) such that: `F` maps the open first quadrant into `R`; a point of `ℍ \ α` in the closure of `R` is in
`R`; and a preconnected set missing the pole and `α`, whose real points are all `< p`, and which meets `R`, lies in
`ℍ`. -/
theorem exists_accessSide (hF : IsBoundaryMap F) (h0 : (F 0).im = 0) (hx₀ : x₀ < (F 0).re)
    {x₁ : ℝ} (hx₁ : 0 < x₁) (hx₁r : (F x₁).im = 0) (hx₁p : (F 0).re < (F x₁).re) :
    ∃ R : Set ℂ, IsOpen R ∧ R ⊆ H ∧
      (∀ w : ℂ, 0 < w.re → 0 < w.im → F w ∈ R) ∧
      (∀ z ∈ H, z ∈ closure R → z ∉ accessArc F → z ∈ R) ∧
      (∀ S : Set ℂ, IsPreconnected S → (x₀ : ℂ) ∉ S → Disjoint S (accessArc F) →
        (∀ z ∈ S, z.im = 0 → z.re < (F 0).re) → (S ∩ R).Nonempty → S ⊆ H) := by
  set γ := accessCrosscut F x₀ with hγdef
  have hγ := isRealCrosscut_accessCrosscut hF h0 hx₀
  have hlt := accessCrosscut_re_lt (F := F) h0 hx₀
  obtain ⟨J, E, hJo, hEo, -, -, -, -, hJH, hJE, hunion, hfr, -⟩ :=
    exists_inside_of_subset_Hbar (isJordanCurve_crosscutCurve hγ hlt)
      fun z hz => crosscutCurve_im_nonneg hγ hz
  have hHx : ∀ z ∈ H, z ≠ x₀ := fun z hz h => not_mem_H_ofReal x₀ (h ▸ hz)
  have hoff : ∀ z ∈ H, z ∉ accessArc F → poleInv x₀ z ∉ crosscutCurve γ := by
    intro z hz hzα hzΓ
    rcases mem_accessArc_or_of_poleInv_mem hF h0 hx₀ (hHx z hz) hzΓ with h | h
    · exact hzα h
    · exact not_mem_H_of_im_eq_zero h.1 hz
  refine ⟨H ∩ poleInv x₀ ⁻¹' J, ?_, inter_subset_left, ?_, ?_, ?_⟩
  · exact (continuousOn_poleInv fun h => not_mem_H_ofReal x₀ h).isOpen_inter_preimage isOpen_H hJo
  · -- the first quadrant
    set Q : Set ℂ := {w : ℂ | 0 < w.re ∧ 0 < w.im} with hQdef
    have hQ : IsPreconnected Q :=
      ((convex_halfSpace_gt (f := fun z : ℂ => z.re) Complex.reLm.isLinear 0).inter
        (convex_halfSpace_gt (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0)).isPreconnected
    have hQH : Q ⊆ H := fun w hw => hw.2
    have hFQ : IsPreconnected (F '' Q) := hQ.image _ (hF.cont.mono (hQH.trans H_subset_Hbar))
    have hFQH : F '' Q ⊆ H := image_subset_iff.2 fun w hw => hF.mapsTo (hQH hw)
    have hX : IsPreconnected (poleInv x₀ '' (F '' Q)) :=
      hFQ.image _ (continuousOn_poleInv fun h => not_mem_H_ofReal x₀ (hFQH h))
    have hXsub : poleInv x₀ '' (F '' Q) ⊆ J ∪ E := by
      rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      rw [← hunion]
      refine hoff _ (hF.mapsTo (hQH hv)) ?_
      rintro ⟨y, hy, hyv⟩
      have h1 := hF.inj (I_mul_mem_H hy) (hQH hv) hyv
      have h2 := congrArg Complex.re h1
      simp only [mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self] at h2
      linarith [hv.1]
    have hFx₁ : F x₁ = ((F x₁).re : ℂ) := eq_ofReal_re_of_im_eq_zero hx₁r
    have hmeet : (poleInv x₀ '' (F '' Q) ∩ J).Nonempty := by
      set m : ℝ := (x₀ - (F x₁).re)⁻¹ with hmdef
      have hm : m ∈ Ioo (γ 0).re (γ 1).re := by
        rw [hγdef, accessCrosscut_zero h0, accessCrosscut_one, ofReal_re, zero_re]
        exact ⟨(inv_lt_inv_of_neg (by linarith) (by linarith)).2 (by linarith), inv_lt_zero.2 (by linarith)⟩
      obtain ⟨ρ, hρ, hball⟩ := exists_ball_inter_H_subset_of_frontier_eq hγ hlt hJo hJH hfr hm
      have hFx₁ne : F x₁ ≠ x₀ := by
        rw [hFx₁]; intro h
        have := congrArg Complex.re h
        simp only [ofReal_re] at this
        linarith
      have hlim : Tendsto (fun y : ℝ => poleInv x₀ (F ((x₁ : ℂ) + I * y))) (𝓝[>] 0) (𝓝 (m : ℂ)) := by
        have h1 : Tendsto (fun y : ℝ => (x₁ : ℂ) + I * y) (𝓝[>] 0) (𝓝[Hbar] (x₁ : ℂ)) := by
          refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun y hy => ?_⟩
          · have hc : Continuous (fun y : ℝ => (x₁ : ℂ) + I * y) := by fun_prop
            simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
          · show 0 ≤ ((x₁ : ℂ) + I * y).im
            have : (0 : ℝ) < y := hy
            simp [this.le]
        have h2 : Tendsto F (𝓝[Hbar] (x₁ : ℂ)) (𝓝 (F x₁)) := hF.cont _ (ofReal_mem_Hbar x₁)
        have h3 : poleInv x₀ (F x₁) = m := by rw [hFx₁, poleInv_ofReal]
        rw [← h3]
        exact (continuousAt_poleInv hFx₁ne).tendsto.comp (h2.comp h1)
      obtain ⟨y, hyball, hy⟩ := ((hlim.eventually (ball_mem_nhds _ hρ)).and self_mem_nhdsWithin).exists
      have hyQ : (x₁ : ℂ) + I * y ∈ Q := ⟨by simp [hx₁], by simpa using hy⟩
      exact ⟨_, ⟨_, ⟨_, hyQ, rfl⟩, rfl⟩, hball ⟨hyball, poleInv_mem_H (hF.mapsTo (hQH hyQ))⟩⟩
    have hXJ := hX.subset_left_of_subset_union hJo hEo hJE hXsub hmeet
    intro w hwre hwim
    exact ⟨hF.mapsTo (hQH ⟨hwre, hwim⟩), hXJ ⟨_, ⟨w, ⟨hwre, hwim⟩, rfl⟩, rfl⟩⟩
  · -- closure
    intro z hz hzc hzα
    refine ⟨hz, ?_⟩
    have hcl : poleInv x₀ z ∈ closure J := by
      have := (continuousAt_poleInv (hHx z hz)).continuousWithinAt.mem_closure_image hzc
      exact closure_mono (image_subset_iff.2 fun w hw => hw.2) this
    rw [closure_eq_self_union_frontier, hfr] at hcl
    exact hcl.resolve_right (hoff z hz hzα)
  · -- separation
    rintro S hS hSx hSα hSre ⟨z₀, hz₀S, hz₀R⟩
    have hMS : IsPreconnected (poleInv x₀ '' S) := hS.image _ (continuousOn_poleInv hSx)
    have hsub : poleInv x₀ '' S ⊆ J ∪ E := by
      rintro _ ⟨z, hz, rfl⟩
      rw [← hunion]
      intro hzΓ
      have hzx : z ≠ x₀ := fun h => hSx (h ▸ hz)
      rcases mem_accessArc_or_of_poleInv_mem hF h0 hx₀ hzx hzΓ with h | h
      · exact Set.disjoint_left.1 hSα hz h
      · exact absurd (hSre z hz h.1) (not_lt.2 h.2)
    have hJ := hMS.subset_left_of_subset_union hJo hEo hJE hsub ⟨_, mem_image_of_mem _ hz₀S, hz₀R.2⟩
    intro z hz
    exact mem_H_of_poleInv_mem_H (fun h => hSx (h ▸ hz)) (hJH (hJ (mem_image_of_mem _ hz)))

/-! ### The contradiction -/

theorem tendsto_add_I_mul_nhdsWithin_Hbar (u : ℝ) :
    Tendsto (fun y : ℝ => (u : ℂ) + I * y) (𝓝[>] 0) (𝓝[Hbar] (u : ℂ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun y hy => ?_⟩
  · have hc : Continuous (fun y : ℝ => (u : ℂ) + I * y) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  · show 0 ≤ ((u : ℂ) + I * y).im
    have : (0 : ℝ) < y := hy
    simp [this.le]

/-- **The deterministic core of §A.4.3** (additional note, proof of Theorem 2.12). Let `F` be a boundary map whose
value `p = F(0)` at the driver coordinate is real and positive, with a positive real coordinate `x₁` mapped to a real
point `> p`. Suppose a boundary value `w = F(u)`, `u > 0`, lies in `ℍ` but not in `F(ℍ)`, and is a point `η(t₀)`,
`0 < t₀ ≤ T`, of a path `η` continuous on `[0, ∞)`. Suppose finally that at every rational `r ∈ (0, T)` with
`η(r) ∈ ℍ` there is a map `G_r`, continuous on `ℍ̄`, with `G_r(0) = η(r)`, real values off `F(ℍ)`, and a coordinate
`u_r < 0` with `G_r(u_r)` real, such that `G_r` has no real value `> 0` on `[u_r, 0]`. This is impossible.

Proof: `w` is in the right side `R` of the access arc (`exists_accessSide`, pole `p/2`), hence so is `η(r)` for a
rational `r` just below `t₀`; then `G_r([u_r, 0])` is a connected set missing the access arc and the pole, with real
points `≤ 0 < p`, meeting `R` at `η(r)`, so it lies in `ℍ` — but `G_r(u_r)` is real. -/
theorem false_of_real_tip_core {F : ℂ → ℂ} {η : ℝ → ℂ} {G : ℝ → ℂ → ℂ} {T : ℝ}
    (hF : IsBoundaryMap F) (hp : (F 0).im = 0) (hp0 : 0 < (F 0).re)
    {x₁ : ℝ} (hx₁ : 0 < x₁) (hx₁r : (F x₁).im = 0) (hx₁p : (F 0).re < (F x₁).re)
    {u : ℝ} (hu : 0 < u) (huH : F u ∈ H) (hu_img : F u ∉ F '' H)
    (hηc : ContinuousOn η (Ici 0)) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioc 0 T) (hηt₀ : η t₀ = F u)
    (hG : ∀ r : ℚ, 0 < (r : ℝ) → (r : ℝ) < T → η r ∈ H →
      ContinuousOn (G r) Hbar ∧ G r 0 = η r ∧ (∀ v : ℝ, G r v ∉ F '' H) ∧
        ∃ ur : ℝ, ur < 0 ∧ (G r ur).im = 0 ∧ ∀ v ∈ Icc ur 0, (G r v).im = 0 → (G r v).re ≤ 0) :
    False := by
  obtain ⟨R, hRo, hRH, hR1, hR4, hR3⟩ :=
    exists_accessSide (x₀ := (F 0).re / 2) hF hp (by linarith) hx₁ hx₁r hx₁p
  -- the boundary value `w = F(u)` is on the right side
  have hwR : F u ∈ R := by
    refine hR4 _ huH ?_ fun h => hu_img (accessArc_subset_image F h)
    have h2 : Tendsto (fun y : ℝ => F ((u : ℂ) + I * y)) (𝓝[>] 0) (𝓝 (F u)) :=
      (hF.cont _ (ofReal_mem_Hbar u)).tendsto.comp (tendsto_add_I_mul_nhdsWithin_Hbar u)
    refine mem_closure_of_tendsto h2 (eventually_nhdsWithin_of_forall fun y hy => hR1 _ ?_ ?_)
    · simp [hu]
    · have : (0 : ℝ) < y := hy
      simpa using this
  -- a rational time `r < t₀` with `η(r) ∈ R`
  have hcont : ContinuousWithinAt η (Ici 0) t₀ := hηc t₀ (le_of_lt ht₀.1)
  have hev : ∀ᶠ t in 𝓝[Ici 0] t₀, η t ∈ R := hcont (hRo.mem_nhds (hηt₀ ▸ hwR))
  obtain ⟨δ, hδ, hδR⟩ : ∃ δ > (0 : ℝ), ∀ t : ℝ, 0 ≤ t → dist t t₀ < δ → η t ∈ R := by
    obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhdsWithin_iff.1 hev
    exact ⟨δ, hδ, fun t ht hd => hsub ⟨mem_ball.2 hd, ht⟩⟩
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (max_lt ht₀.1 (by linarith : t₀ - δ < t₀))
  have hr0 : (0 : ℝ) < r := lt_of_le_of_lt (le_max_left _ _) hr1
  have hrT : (r : ℝ) < T := lt_of_lt_of_le hr2 ht₀.2
  have hrR : η r ∈ R := by
    refine hδR r hr0.le ?_
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith [le_max_right 0 (t₀ - δ)]
  obtain ⟨hGc, hG0, hGimg, ur, hur, hurr, hGre⟩ := hG r hr0 hrT (hRH hrR)
  -- the boundary arc of the earlier hull, from a real point to the tip `η(r)`
  set S : Set ℂ := (fun v : ℝ => G r v) '' Icc ur 0 with hSdef
  have hS : IsPreconnected S :=
    isPreconnected_Icc.image _ (hGc.comp continuous_ofReal.continuousOn fun v _ => ofReal_mem_Hbar v)
  have hSsub := hR3 S hS ?_ ?_ ?_ ⟨G r 0, ⟨0, ⟨hur.le, le_rfl⟩, rfl⟩, by rw [hG0]; exact hrR⟩
  · exact not_mem_H_of_im_eq_zero hurr (hSsub ⟨ur, ⟨le_rfl, hur.le⟩, rfl⟩)
  · rintro ⟨v, hv, hvx⟩
    have hvx' : G r v = (((F 0).re / 2 : ℝ) : ℂ) := hvx
    have hvim : (G r v).im = 0 := by rw [hvx']; simp
    have := hGre v hv hvim
    rw [hvx', ofReal_re] at this
    linarith
  · refine Set.disjoint_left.2 fun z ⟨v, _, hvz⟩ hzα => hGimg v ?_
    have hvz' : G r v = z := hvz
    rw [hvz']
    exact accessArc_subset_image F hzα
  · rintro _ ⟨v, hv, rfl⟩ him
    exact lt_of_le_of_lt (hGre v hv him) hp0

end InteractingSLE.ZhanGT4
