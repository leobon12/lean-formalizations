/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import QuantumZipper.Proofs.Complex.TopoDegree
import QuantumZipper.Proofs.Zipper.FLTopSepBasic

/-!
# Winding numbers of loops on `[0, 1]` and the crossing lemma

Packet PROVE-ORIENT (the orientation foundation). A loop is a function `γ : ℝ → ℂ`, continuous on `[0, 1]` with
`γ 0 = γ 1`; its **winding number** `windNum γ w` about a point `w` off `γ([0, 1])` is QuantumZipper's degree
`loopDeg` of `t ↦ γ t - w` (Burckel, *Classical Analysis in the Complex Plane*, Definition 4.2: `(L 1 - L 0)/2πi` for a
continuous logarithm `L` of `γ - w`). The `ℝ`-indexed form allows loops glued from pieces on subintervals.

## Main results

* `windNum_spec`, `exists_lift`: the winding number from any continuous logarithm on `[0, 1]`;
* `sub_eq_of_exp_eq`: two continuous logarithms of the same function along a piece of a loop have the same increment
  (QuantumZipper's `flts_sub_const`);
* `windNum_eq_of_norm_sub_lt` (dog on a leash), `windNum_eq_of_isPreconnected` (constant on preconnected sets off the
  loop), `windNum_eq_zero_of_norm_lt` and `windNum_eq_zero_of_isPreconnected` (zero on unbounded such sets);
* **`windNum_add_windNum_eq` (the crossing lemma)**: if two loops run along a common set `A` with continuous
  logarithms of `z - w` (an arc) in opposite directions, then near a point `p` of `A` that the rest of both loops
  avoids, the sum of the two winding numbers takes the same value on every point off `A`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped Real

open QuantumZipper.CA.Topo (loopDeg HasLogOn exists_lift_exp loopDeg_eq_of_lift loopDeg_eq_of_norm_sub_lt
  loopDeg_const two_pi_I_ne_zero')

namespace InteractingSLE.Orientation

/-! ### The winding number -/

/-- The loop `t ↦ γ t - w` on the unit interval. -/
def shiftLoop (γ : ℝ → ℂ) (hγ : ContinuousOn γ (Icc 0 1)) (w : ℂ) : C(unitInterval, ℂ) :=
  ⟨fun t => γ t - w, (hγ.comp_continuous continuous_subtype_val fun t => t.2).sub continuous_const⟩

theorem shiftLoop_ne_zero {γ : ℝ → ℂ} {w : ℂ} (hγ : ContinuousOn γ (Icc 0 1)) (hw : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w) :
    ∀ t, shiftLoop γ hγ w t ≠ 0 := fun t => sub_ne_zero.2 (hw t t.2)

/-- The **winding number** of `γ` on `[0, 1]` about `w` (`0` if `γ` is not continuous on `[0, 1]` or passes through
`w`). For a loop (`γ 0 = γ 1`) it is the degree `(L 1 - L 0)/2πi` of any continuous logarithm `L` of `γ - w`. -/
@[irreducible] def windNum (γ : ℝ → ℂ) (w : ℂ) : ℤ :=
  haveI := Classical.propDecidable
  if h : ContinuousOn γ (Icc 0 1) ∧ ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w then
    loopDeg (shiftLoop γ h.1 w) (shiftLoop_ne_zero h.1 h.2)
  else 0

theorem loopDeg_congr {γ δ : C(unitInterval, ℂ)} (e : γ = δ) (hγ : ∀ t, γ t ≠ 0) (hδ : ∀ t, δ t ≠ 0) :
    loopDeg γ hγ = loopDeg δ hδ := by
  subst e; rfl

theorem windNum_eq_loopDeg {γ : ℝ → ℂ} {w : ℂ} (hγ : ContinuousOn γ (Icc 0 1)) (hw : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w) :
    windNum γ w = loopDeg (shiftLoop γ hγ w) (shiftLoop_ne_zero hγ hw) := by
  unfold windNum
  split
  · rfl
  · rename_i hn
    exact absurd (And.intro hγ hw) hn

/-- **The winding number from a continuous logarithm**: `L 1 - L 0 = 2πi · windNum γ w`. -/
theorem windNum_spec {γ : ℝ → ℂ} {w : ℂ} (hγ : ContinuousOn γ (Icc 0 1)) (hw : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w)
    (hl : γ 0 = γ 1) {L : ℝ → ℂ} (hL : ContinuousOn L (Icc 0 1))
    (hexp : ∀ t ∈ Icc (0 : ℝ) 1, exp (L t) = γ t - w) :
    L 1 - L 0 = (windNum γ w : ℂ) * (2 * π * I) := by
  rw [windNum_eq_loopDeg hγ hw]
  have h := loopDeg_eq_of_lift (shiftLoop γ hγ w) (shiftLoop_ne_zero hγ hw)
    (by simp [shiftLoop, hl]) (L := fun t : unitInterval => L t)
    (hL.comp_continuous continuous_subtype_val fun t => t.2) (fun t => hexp t t.2)
  simpa using h

/-- A continuous logarithm of `γ - w` on `[0, 1]`. -/
theorem exists_lift {γ : ℝ → ℂ} {w : ℂ} (hγ : ContinuousOn γ (Icc 0 1)) (hw : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w) :
    ∃ L : ℝ → ℂ, ContinuousOn L (Icc 0 1) ∧ ∀ t ∈ Icc (0 : ℝ) 1, exp (L t) = γ t - w := by
  obtain ⟨L, hL⟩ := exists_lift_exp (shiftLoop γ hγ w) (shiftLoop_ne_zero hγ hw)
  refine ⟨fun t => L (projIcc 0 1 zero_le_one t), (L.continuous.comp continuous_projIcc).continuousOn,
    fun t ht => ?_⟩
  simp only
  rw [projIcc_of_mem zero_le_one ht, hL]
  rfl

/-- **Two continuous logarithms of the same function along a piece of a curve have the same increment**: if
`exp (F t) = φ (γ t)` on `[s₀, s₁]` and `exp (ℓ z) = φ z` on `A ⊇ γ([s₀, s₁])`, then
`F s₁ - F s₀ = ℓ (γ s₁) - ℓ (γ s₀)`. -/
theorem sub_eq_of_exp_eq {γ F : ℝ → ℂ} {φ ℓ : ℂ → ℂ} {A : Set ℂ} {s₀ s₁ : ℝ} (hs : s₀ ≤ s₁)
    (hγ : ContinuousOn γ (Icc s₀ s₁)) (hF : ContinuousOn F (Icc s₀ s₁)) (hℓ : ContinuousOn ℓ A)
    (hγA : MapsTo γ (Icc s₀ s₁) A) (hFe : ∀ t ∈ Icc s₀ s₁, exp (F t) = φ (γ t))
    (hℓe : ∀ z ∈ A, exp (ℓ z) = φ z) : F s₁ - F s₀ = ℓ (γ s₁) - ℓ (γ s₀) := by
  have h := QuantumZipper.FieldLawler.flts_sub_const isPreconnected_Icc hF (hℓ.comp hγ hγA)
    (fun t ht => by rw [hFe t ht]; exact (hℓe _ (hγA ht)).symm) (right_mem_Icc.2 hs) (left_mem_Icc.2 hs)
  simp only [Function.comp] at h
  linear_combination h

/-! ### Dependence on the point -/

/-- **Dog on a leash**: if `|w - w'| < |γ t - w|` on `[0, 1]`, the winding numbers about `w` and `w'` agree. -/
theorem windNum_eq_of_norm_sub_lt {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1)) (hl : γ 0 = γ 1) {w w' : ℂ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, ‖w - w'‖ < ‖γ t - w‖) : windNum γ w' = windNum γ w := by
  have hw : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w := fun t ht he => by
    have := h t ht; rw [he, sub_self, norm_zero] at this; exact (norm_nonneg _).not_gt this
  have hw' : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w' := fun t ht he => by
    have := h t ht; rw [he, norm_sub_rev] at this; exact lt_irrefl _ this
  rw [windNum_eq_loopDeg hγ hw, windNum_eq_loopDeg hγ hw']
  refine loopDeg_eq_of_norm_sub_lt _ _ _ _ (by simp [shiftLoop, hl]) (by simp [shiftLoop, hl]) fun t => ?_
  have e : shiftLoop γ hγ w' t - shiftLoop γ hγ w t = w - w' := by simp [shiftLoop]
  rw [e]
  exact h t t.2

/-- **Rouché's comparison of two loops**: if `|γ t - δ t| < |δ t - w|` on `[0, 1]`, then
`windNum γ w = windNum δ w`. -/
theorem windNum_eq_of_norm_sub_lt' {γ δ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1)) (hδ : ContinuousOn δ (Icc 0 1))
    (hγl : γ 0 = γ 1) (hδl : δ 0 = δ 1) {w : ℂ} (h : ∀ t ∈ Icc (0 : ℝ) 1, ‖γ t - δ t‖ < ‖δ t - w‖) :
    windNum γ w = windNum δ w := by
  have hδw : ∀ t ∈ Icc (0 : ℝ) 1, δ t ≠ w := fun t ht he => by
    have := h t ht; rw [he, sub_self, norm_zero] at this; exact (norm_nonneg _).not_gt this
  have hγw : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w := fun t ht he => by
    have := h t ht; rw [he, norm_sub_rev] at this; exact lt_irrefl _ this
  rw [windNum_eq_loopDeg hγ hγw, windNum_eq_loopDeg hδ hδw]
  refine loopDeg_eq_of_norm_sub_lt _ _ _ _ (by simp [shiftLoop, hγl]) (by simp [shiftLoop, hδl]) fun t => ?_
  have e : shiftLoop γ hγ w t - shiftLoop δ hδ w t = γ t - δ t := by simp [shiftLoop]
  rw [e]
  exact h t t.2

theorem isCompact_image_Icc {γ : ℝ → ℂ} {a b : ℝ} (hγ : ContinuousOn γ (Icc a b)) : IsCompact (γ '' Icc a b) :=
  isCompact_Icc.image_of_continuousOn hγ

/-- A point off a compact curve has a ball around it that the curve avoids. -/
theorem exists_ball_disjoint {K : Set ℂ} (hK : IsClosed K) {w : ℂ} (hw : w ∉ K) :
    ∃ r > 0, ∀ z ∈ K, r ≤ ‖z - w‖ := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 hK.isOpen_compl w hw
  refine ⟨r, hr, fun z hz => not_lt.1 fun hlt => hsub ?_ hz⟩
  rw [mem_ball, dist_eq_norm]
  exact hlt

/-- **The winding number is constant on preconnected sets off the loop.** -/
theorem windNum_eq_of_isPreconnected {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1)) (hl : γ 0 = γ 1) {S : Set ℂ}
    (hS : IsPreconnected S) (hSγ : Disjoint S (γ '' Icc 0 1)) {w w' : ℂ} (hw : w ∈ S) (hw' : w' ∈ S) :
    windNum γ w = windNum γ w' := by
  have hK := (isCompact_image_Icc hγ).isClosed
  have hcont : ContinuousOn (fun v => windNum γ v) S := by
    intro v hv
    have hvK : v ∉ γ '' Icc 0 1 := Set.disjoint_left.1 hSγ hv
    obtain ⟨r, hr, hrK⟩ := exists_ball_disjoint hK hvK
    refine ((continuousAt_const (y := windNum γ v)).congr ?_).continuousWithinAt
    filter_upwards [ball_mem_nhds v hr] with v' hv'
    refine (windNum_eq_of_norm_sub_lt hγ hl fun t ht => ?_).symm
    calc ‖v - v'‖ = dist v' v := by rw [dist_eq_norm, norm_sub_rev]
      _ < r := mem_ball.1 hv'
      _ ≤ ‖γ t - v‖ := hrK _ (mem_image_of_mem γ ht)
  exact hS.constant hcont hw hw'

/-- A loop has winding number `0` about a point farther from `0` than the whole loop. -/
theorem windNum_eq_zero_of_norm_lt {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1)) (hl : γ 0 = γ 1) {w : ℂ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, ‖γ t‖ < ‖w‖) : windNum γ w = 0 := by
  have hw0 : w ≠ 0 := fun h0 => by
    have := h 0 (left_mem_Icc.2 zero_le_one); rw [h0, norm_zero] at this; exact (norm_nonneg _).not_gt this
  have hγw : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w := fun t ht he => by
    have := h t ht; rw [he] at this; exact lt_irrefl _ this
  rw [windNum_eq_loopDeg hγ hγw]
  rw [loopDeg_eq_of_norm_sub_lt (shiftLoop γ hγ w) (ContinuousMap.const unitInterval (-w)) _
    (fun _ => neg_ne_zero.2 hw0) (by simp [shiftLoop, hl]) rfl fun t => by
      simpa [shiftLoop] using h t t.2]
  exact loopDeg_const (-w) (neg_ne_zero.2 hw0)

/-- **The winding number vanishes on unbounded preconnected sets off the loop.** -/
theorem windNum_eq_zero_of_isPreconnected {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1)) (hl : γ 0 = γ 1)
    {S : Set ℂ} (hS : IsPreconnected S) (hSu : ¬ IsBounded S) (hSγ : Disjoint S (γ '' Icc 0 1)) {w : ℂ}
    (hw : w ∈ S) : windNum γ w = 0 := by
  obtain ⟨M, hM⟩ := (isCompact_image_Icc hγ).isBounded.exists_norm_le
  obtain ⟨v, hvS, hvM⟩ : ∃ v ∈ S, M < ‖v‖ := by
    by_contra hcon
    exact hSu (isBounded_iff_forall_norm_le.2 ⟨M, fun v hv => not_lt.1 fun hlt => hcon ⟨v, hv, hlt⟩⟩)
  rw [windNum_eq_of_isPreconnected hγ hl hS hSγ hw hvS]
  exact windNum_eq_zero_of_norm_lt hγ hl fun t ht => (hM _ (mem_image_of_mem γ ht)).trans_lt hvM

/-- **An arc carries continuous logarithms**: for `γ` continuous and injective on `[a, b]` (`a < b`) and `w` off
`γ([a, b])`, the function `z ↦ z - w` has a continuous logarithm on `γ([a, b])` (QuantumZipper's `hasLogOn_of_arc`
after the affine reparametrization of `[0, 1]`). -/
theorem hasLogOn_sub_image_Icc {γ : ℝ → ℂ} {a b : ℝ} (hab : a < b) (hγ : ContinuousOn γ (Icc a b))
    (hinj : InjOn γ (Icc a b)) {w : ℂ} (hw : w ∉ γ '' Icc a b) : HasLogOn (fun z => z - w) (γ '' Icc a b) := by
  set φ : ℝ → ℝ := fun u => a + u * (b - a) with hφ
  have hba : 0 < b - a := sub_pos.2 hab
  have himg : φ '' Icc 0 1 = Icc a b := by
    ext s
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩
    · intro hs
      refine ⟨(s - a) / (b - a), ⟨div_nonneg (by linarith [hs.1]) hba.le, (div_le_one hba).2 (by linarith [hs.2])⟩,
        ?_⟩
      simp only [hφ]
      field_simp
      ring
  have hmaps : MapsTo φ (Icc 0 1) (Icc a b) := fun u hu => himg ▸ mem_image_of_mem φ hu
  have hφc : Continuous φ := by rw [hφ]; fun_prop
  have h := QuantumZipper.CA.Topo.hasLogOn_of_arc (γ := γ ∘ φ) (hγ.comp hφc.continuousOn hmaps)
    (fun u hu v hv huv => by
      have := hinj (hmaps hu) (hmaps hv) huv
      simp only [hφ] at this
      have h2 : u * (b - a) = v * (b - a) := by linarith
      exact mul_right_cancel₀ hba.ne' h2)
    (g := fun z => z - w) (by fun_prop) (fun z hz he => hw (by
      rw [image_comp, himg] at hz
      rw [← sub_eq_zero.1 he]
      exact hz))
  rwa [image_comp, himg] at h

/-! ### The crossing lemma -/

/-- The ratio `(z - w)/(z - w')` has the continuous logarithm `log ((z - w)/(z - w'))` on a set `K` on which
`|w - w'| < |z - w'|`. -/
theorem log_ratio_props {K : Set ℂ} {w w' : ℂ} (h : ∀ z ∈ K, ‖w - w'‖ < ‖z - w'‖) :
    ContinuousOn (fun z => log ((z - w) / (z - w'))) K ∧
      ∀ z ∈ K, exp (log ((z - w) / (z - w'))) = (z - w) / (z - w') := by
  have hmem : ∀ z ∈ K, (z - w) / (z - w') ∈ slitPlane := fun z hz => by
    have hz0 : z - w' ≠ 0 := fun h0 => by
      have := h z hz; rw [h0, norm_zero] at this; exact (norm_nonneg _).not_gt this
    have e : (z - w) / (z - w') = 1 + (w' - w) / (z - w') := by field_simp; ring
    rw [e]
    refine mem_slitPlane_of_norm_lt_one ?_
    rw [norm_div, div_lt_one (norm_pos_iff.2 hz0), norm_sub_rev]
    exact h z hz
  refine ⟨fun z hz => ?_, fun z hz => exp_log (slitPlane_ne_zero (hmem z hz))⟩
  have hz0 : z - w' ≠ 0 := fun h0 => by
    have := h z hz; rw [h0, norm_zero] at this; exact (norm_nonneg _).not_gt this
  exact ((continuousAt_clog (hmem z hz)).comp (f := fun z => (z - w) / (z - w'))
    ((continuousAt_id.sub continuousAt_const).div (continuousAt_id.sub continuousAt_const) hz0)).continuousWithinAt

/-- **The crossing lemma.** Let `γ` and `δ` be loops on `[0, 1]` that run along a common set `A` on which every
`z - w`, `w ∉ A`, has a continuous logarithm (an arc), in opposite directions: `γ([s₀, s₁]) ⊆ A` from `γ s₀ = δ t₁`
to `γ s₁ = δ t₀`, and `δ([t₀, t₁]) ⊆ A`. If `p` is off the rest of both loops, then near `p` the sum
`windNum γ w + windNum δ w` takes the same value at all points `w ∉ A`: the two contributions of `A` cancel, and the
rest of the two loops is one closed curve that avoids a ball around `p`. -/
theorem windNum_add_windNum_eq {γ δ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1)) (hδ : ContinuousOn δ (Icc 0 1))
    (hγl : γ 0 = γ 1) (hδl : δ 0 = δ 1) {A : Set ℂ} (hA : ∀ w ∉ A, HasLogOn (fun z => z - w) A)
    {s₀ s₁ t₀ t₁ : ℝ} (hs₀ : 0 ≤ s₀) (hs : s₀ ≤ s₁) (hs₁ : s₁ ≤ 1) (ht₀ : 0 ≤ t₀) (ht : t₀ ≤ t₁)
    (ht₁ : t₁ ≤ 1) (hγA : MapsTo γ (Icc s₀ s₁) A) (hδA : MapsTo δ (Icc t₀ t₁) A) (h₀ : γ s₀ = δ t₁)
    (h₁ : γ s₁ = δ t₀) {p : ℂ}
    (hp : p ∉ γ '' Icc 0 s₀ ∪ γ '' Icc s₁ 1 ∪ δ '' Icc 0 t₀ ∪ δ '' Icc t₁ 1) :
    ∃ ε > 0, ∀ w ∈ ball p ε, ∀ w' ∈ ball p ε, w ∉ A → w' ∉ A →
      windNum γ w + windNum δ w = windNum γ w' + windNum δ w' := by
  set K := γ '' Icc 0 s₀ ∪ γ '' Icc s₁ 1 ∪ δ '' Icc 0 t₀ ∪ δ '' Icc t₁ 1 with hKdef
  have hγ1 : ContinuousOn γ (Icc 0 s₀) := hγ.mono (Icc_subset_Icc le_rfl (hs.trans hs₁))
  have hγ2 : ContinuousOn γ (Icc s₁ 1) := hγ.mono (Icc_subset_Icc (hs₀.trans hs) le_rfl)
  have hγm : ContinuousOn γ (Icc s₀ s₁) := hγ.mono (Icc_subset_Icc hs₀ hs₁)
  have hδ1 : ContinuousOn δ (Icc 0 t₀) := hδ.mono (Icc_subset_Icc le_rfl (ht.trans ht₁))
  have hδ2 : ContinuousOn δ (Icc t₁ 1) := hδ.mono (Icc_subset_Icc (ht₀.trans ht) le_rfl)
  have hδm : ContinuousOn δ (Icc t₀ t₁) := hδ.mono (Icc_subset_Icc ht₀ ht₁)
  have hKc : IsClosed K :=
    ((((isCompact_image_Icc hγ1).union (isCompact_image_Icc hγ2)).union (isCompact_image_Icc hδ1)).union
      (isCompact_image_Icc hδ2)).isClosed
  obtain ⟨r, hr, hrK⟩ := exists_ball_disjoint hKc hp
  refine ⟨r / 3, by positivity, fun w hw w' hw' hwA hw'A => ?_⟩
  rw [mem_ball, dist_eq_norm] at hw hw'
  -- points of `K` are far from `w` and `w'`
  have hfar : ∀ v : ℂ, ‖v - p‖ < r / 3 → ∀ z ∈ K, 2 * r / 3 < ‖z - v‖ := fun v hv z hz => by
    have h1 := hrK z hz
    have h2 : ‖z - p‖ ≤ ‖z - v‖ + ‖v - p‖ := by
      calc ‖z - p‖ = ‖(z - v) + (v - p)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    linarith
  have hww' : ‖w - w'‖ < 2 * r / 3 := by
    calc ‖w - w'‖ = ‖(w - p) - (w' - p)‖ := by ring_nf
      _ ≤ ‖w - p‖ + ‖w' - p‖ := norm_sub_le _ _
      _ < r / 3 + r / 3 := add_lt_add hw hw'
      _ = 2 * r / 3 := by ring
  have hKr : ∀ z ∈ K, ‖w - w'‖ < ‖z - w'‖ := fun z hz => hww'.trans (hfar w' hw' z hz)
  -- the loops avoid `w` and `w'`
  have hγK : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ K ∨ γ t ∈ A := fun t ht => by
    rcases le_total t s₀ with h | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨t, ⟨ht.1, h⟩, rfl⟩)))
    rcases le_total t s₁ with h' | h'
    · exact Or.inr (hγA ⟨h, h'⟩)
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨t, ⟨h', ht.2⟩, rfl⟩)))
  have hδK : ∀ t ∈ Icc (0 : ℝ) 1, δ t ∈ K ∨ δ t ∈ A := fun t ht => by
    rcases le_total t t₀ with h | h
    · exact Or.inl (Or.inl (Or.inr ⟨t, ⟨ht.1, h⟩, rfl⟩))
    rcases le_total t t₁ with h' | h'
    · exact Or.inr (hδA ⟨h, h'⟩)
    · exact Or.inl (Or.inr ⟨t, ⟨h', ht.2⟩, rfl⟩)
  have havoid : ∀ v : ℂ, ‖v - p‖ < r / 3 → v ∉ A → ∀ {z : ℂ}, z ∈ K ∨ z ∈ A → z ≠ v := by
    intro v hv hvA z hz hzv
    rcases hz with hz | hz
    · have := hfar v hv z hz; rw [hzv, sub_self, norm_zero] at this; linarith
    · exact hvA (hzv ▸ hz)
  have hγw := fun t ht => havoid w hw hwA (hγK t ht)
  have hγw' := fun t ht => havoid w' hw' hw'A (hγK t ht)
  have hδw := fun t ht => havoid w hw hwA (hδK t ht)
  have hδw' := fun t ht => havoid w' hw' hw'A (hδK t ht)
  -- continuous logarithms along the loops
  obtain ⟨L₁, hL₁, he₁⟩ := exists_lift hγ hγw
  obtain ⟨L₂, hL₂, he₂⟩ := exists_lift hδ hδw
  obtain ⟨L₃, hL₃, he₃⟩ := exists_lift hγ hγw'
  obtain ⟨L₄, hL₄, he₄⟩ := exists_lift hδ hδw'
  have E1 := windNum_spec hγ hγw hγl hL₁ he₁
  have E2 := windNum_spec hδ hδw hδl hL₂ he₂
  have E3 := windNum_spec hγ hγw' hγl hL₃ he₃
  have E4 := windNum_spec hδ hδw' hδl hL₄ he₄
  -- the pieces along `A`
  obtain ⟨ℓ, hℓc, hℓe⟩ := hA w hwA
  obtain ⟨ℓ', hℓc', hℓe'⟩ := hA w' hw'A
  have hsm : Icc s₀ s₁ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hs₀ hs₁
  have htm : Icc t₀ t₁ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc ht₀ ht₁
  have M1 := sub_eq_of_exp_eq (φ := fun z => z - w) hs hγm (hL₁.mono hsm) hℓc hγA
    (fun t ht => he₁ t (hsm ht)) hℓe
  have M2 := sub_eq_of_exp_eq (φ := fun z => z - w) ht hδm (hL₂.mono htm) hℓc hδA
    (fun t ht => he₂ t (htm ht)) hℓe
  have M3 := sub_eq_of_exp_eq (φ := fun z => z - w') hs hγm (hL₃.mono hsm) hℓc' hγA
    (fun t ht => he₃ t (hsm ht)) hℓe'
  have M4 := sub_eq_of_exp_eq (φ := fun z => z - w') ht hδm (hL₄.mono htm) hℓc' hδA
    (fun t ht => he₄ t (htm ht)) hℓe'
  -- the pieces off `A`
  obtain ⟨hlc, hle⟩ := log_ratio_props hKr
  have hratio : ∀ {L L' γ' : ℝ → ℂ} {a b : ℝ}, Icc a b ⊆ Icc (0 : ℝ) 1 →
      (∀ t ∈ Icc (0 : ℝ) 1, exp (L t) = γ' t - w) → (∀ t ∈ Icc (0 : ℝ) 1, exp (L' t) = γ' t - w') →
      (∀ t ∈ Icc (0 : ℝ) 1, γ' t ≠ w') →
      ∀ t ∈ Icc a b, exp (L t - L' t) = (fun z => (z - w) / (z - w')) (γ' t) := by
    intro L L' γ' a b hab he he' hne t ht
    rw [exp_sub, he t (hab ht), he' t (hab ht)]
  have hI1 : Icc 0 s₀ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl (hs.trans hs₁)
  have hI2 : Icc s₁ 1 ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc (hs₀.trans hs) le_rfl
  have hI3 : Icc 0 t₀ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl (ht.trans ht₁)
  have hI4 : Icc t₁ 1 ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc (ht₀.trans ht) le_rfl
  have O1 := sub_eq_of_exp_eq (F := fun t => L₁ t - L₃ t) hs₀ hγ1 ((hL₁.sub hL₃).mono hI1) hlc
    (fun t ht => Or.inl (Or.inl (Or.inl ⟨t, ht, rfl⟩))) (hratio hI1 he₁ he₃ hγw') hle
  have O2 := sub_eq_of_exp_eq (F := fun t => L₁ t - L₃ t) hs₁ hγ2 ((hL₁.sub hL₃).mono hI2) hlc
    (fun t ht => Or.inl (Or.inl (Or.inr ⟨t, ht, rfl⟩))) (hratio hI2 he₁ he₃ hγw') hle
  have O3 := sub_eq_of_exp_eq (F := fun t => L₂ t - L₄ t) ht₀ hδ1 ((hL₂.sub hL₄).mono hI3) hlc
    (fun t ht => Or.inl (Or.inr ⟨t, ht, rfl⟩)) (hratio hI3 he₂ he₄ hδw') hle
  have O4 := sub_eq_of_exp_eq (F := fun t => L₂ t - L₄ t) ht₁ hδ2 ((hL₂.sub hL₄).mono hI4) hlc
    (fun t ht => Or.inr ⟨t, ht, rfl⟩) (hratio hI4 he₂ he₄ hδw') hle
  beta_reduce at O1 O2 O3 O4
  rw [← hγl] at O2
  rw [← h₁] at O3
  rw [← hδl, ← h₀] at O4
  rw [← h₀, ← h₁] at M2 M4
  have key : ((windNum γ w + windNum δ w : ℤ) : ℂ) * (2 * π * I) =
      ((windNum γ w' + windNum δ w' : ℤ) : ℂ) * (2 * π * I) := by
    push_cast
    linear_combination -E1 - E2 + E3 + E4 + O1 + O2 + O3 + O4 + M1 - M3 + M2 - M4
  exact_mod_cast mul_right_cancel₀ two_pi_I_ne_zero' key

end InteractingSLE.Orientation
