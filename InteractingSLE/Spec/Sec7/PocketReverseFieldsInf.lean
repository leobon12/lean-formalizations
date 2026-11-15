/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketJordanInf
import InteractingSLE.Spec.Sec6.Aux40Inf

/-!
# The change pocket opening at the flow seed: the `[0, ∞)`-arc topology of `IsReversePocketInf`

Packet PROVE-STRIPSYS18 (specification §7.4.1, Aux. lemma 130 and the proof of Lemma 7.25, pp. 408–414; Aux. lemma 41
at infinity). When the change pocket `C = changePocket R L r` of Aux. lemma 130 opens at the flow seed (`x₀ = 0`,
`rightLo = 0`), its image `m(C)` under the counterflow chart `m(z) = −1/z` is unbounded: its junction `m(x₀)` is the
counterflow target `∞`. Its frontier consists of the two wall arcs from `m(y₀)` to `∞`, parametrized on `[0, ∞)` by

* `cfArcRInf v = m(R̃(rightHi/(1 + v)))` (the right wall, read backwards from `y₀` to `x₀ = 0`),
* `cfArcLInf v = m(L̃(leftHi/(1 + v)))` (the left wall),

where `R̃ = cayley ∘ R`, `L̃ = cayley ∘ L` in their disc parametrizations. This file proves the topological fields of
`Sec6.IsReversePocketInf` for them (`IsCfPocketInf`, **`IsChangeConfigInc.isCfPocketInf`**) and assembles
`Sec6.IsReversePocketInf` from these and the counterflow's fields (`IsCfPocketInf.isReversePocketInf`).

## Main results

* `frontier_image_negInv_eq`: `∂ m(C) = m̃(∂ cayley(C) \ {−1})` for every open `C ⊆ ℍ` (no hypothesis at the pole);
* `image_div_one_add_Ici`: `v ↦ u/(1 + v)` maps `[0, ∞)` onto `(0, u]`;
* **`IsChangeConfigInc.isCfPocketInf`**, `IsChangeConfigInc.leftLo_eq_zero_of_rightLo_eq_zero`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Function Bornology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open InteractingSLE.WangWu (negInv)
open scoped NNReal

namespace InteractingSLE.Sec7.PocketJordan

open WangWu PocketCoord Lemma71I

/-! ### The frontier of the inverted pocket with the pole on its frontier -/

/-- **The frontier of the inverted pocket**, in general: the counterflow image of the frontier of the Cayley image
with the pole `−1` (the image of the flow seed) removed. -/
theorem frontier_image_negInv_eq {C : Set ℂ} (hCo : IsOpen C) (hCH : C ⊆ H) :
    frontier (negInv '' C) = cfPt '' (frontier (cayley '' C) \ {-1}) := by
  ext z
  constructor
  · intro hz
    have hzH := closure_image_negInv_subset_Hbar hCH (frontier_subset_closure hz)
    exact ⟨_, ⟨neg_cayley_mem_frontier hCo hCH hz, neg_cayley_ne_neg_one hzH⟩, cfPt_neg_cayley hzH⟩
  · rintro ⟨w, ⟨hw, hw1⟩, rfl⟩
    have hw1 : w ≠ -1 := hw1
    have hDo := Lemma71F.isOpen_cayley_image hCo hCH
    rw [hDo.frontier_eq] at hw
    rw [(isOpen_image_negInv' hCo hCH).frontier_eq]
    refine ⟨?_, fun hmem => ?_⟩
    · have := (continuousAt_cfPt hw1).continuousWithinAt.mem_closure_image hw.1
      rwa [← image_negInv_eq hCH] at this
    · rw [image_negInv_eq hCH] at hmem
      obtain ⟨w', hw', hww'⟩ := hmem
      have hw'1 : w' ≠ -1 := fun h => by
        rw [h] at hw'
        exact (Lemma71F.ne_one_of_mem_ball (by
          have := Lemma71F.cayley_image_subset_ball hCH hw'
          rwa [mem_ball_zero_iff, norm_neg, ← mem_ball_zero_iff] at this)) rfl
      have : w' = w := by rw [← neg_cayley_cfPt hw'1, ← neg_cayley_cfPt hw1, hww']
      exact hw.2 (this ▸ hw')

/-- `‖cfPt w‖ → ∞` as `w → −1`, `w ≠ −1`. -/
theorem tendsto_norm_cfPt : Tendsto (fun w => ‖cfPt w‖) (𝓝[≠] (-1)) atTop := by
  have h1 : Tendsto (fun w : ℂ => -w) (𝓝[≠] (-1)) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun w hw => ?_⟩
    · have := ((continuous_neg (G := ℂ)).tendsto (-1)).mono_left (nhdsWithin_le_nhds (s := {-1}ᶜ))
      rwa [neg_neg] at this
    · intro he
      exact hw (by simpa using congrArg Neg.neg he)
  exact tendsto_norm_cobounded_atTop.comp (QuantumZipper.CA.tendsto_cayleyInv_nhdsNE_one.comp h1)

/-! ### The reparametrization `[0, ∞) → (0, u]` -/

/-- **`v ↦ u/(1 + v)` maps `[0, ∞)` onto `(0, u]`** for `u > 0`. -/
theorem image_div_one_add_Ici {u : ℝ} (hu : 0 < u) : (fun v : ℝ => u / (1 + v)) '' Ici 0 = Ioc 0 u := by
  ext s
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv' : (0 : ℝ) ≤ v := hv
    have h1 : (0 : ℝ) < 1 + v := by linarith
    refine ⟨div_pos hu h1, ?_⟩
    rw [div_le_iff₀ h1]
    nlinarith
  · rintro ⟨hs, hsu⟩
    refine ⟨u / s - 1, ?_, ?_⟩
    · have : 1 ≤ u / s := by rw [le_div_iff₀ hs]; linarith
      exact sub_nonneg.2 this
    · simp only
      rw [add_sub_cancel, div_div_eq_mul_div]
      field_simp

theorem div_one_add_mem {u v : ℝ} (hu : 0 < u) (hv : 0 ≤ v) : u / (1 + v) ∈ Ioc 0 u := by
  rw [← image_div_one_add_Ici hu]
  exact ⟨v, hv, rfl⟩

theorem div_one_add_lt {u v : ℝ} (hu : 0 < u) (hv : 0 < v) : u / (1 + v) < u := by
  have h1 : (0 : ℝ) < 1 + v := by linarith
  rw [div_lt_iff₀ h1]
  nlinarith

theorem injOn_div_one_add {u : ℝ} (hu : 0 < u) : InjOn (fun v : ℝ => u / (1 + v)) (Ici 0) := by
  intro v hv v' hv' he
  have h1 : (0 : ℝ) < 1 + v := by linarith [mem_Ici.1 hv]
  have h2 : (0 : ℝ) < 1 + v' := by linarith [mem_Ici.1 hv']
  simp only at he
  rw [div_eq_div_iff h1.ne' h2.ne'] at he
  nlinarith

theorem tendsto_div_one_add {u : ℝ} (hu : 0 < u) :
    Tendsto (fun v : ℝ => u / (1 + v)) atTop (𝓝[Ioc 0 u] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h := (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id).inv_tendsto_atTop
    have h' := h.const_mul u
    rw [mul_zero] at h'
    refine h'.congr fun v => ?_
    simp only [Pi.inv_apply, id]
    rw [div_eq_mul_inv]
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv
    exact div_one_add_mem hu hv

/-! ### One wall arc read backwards from `y₀` to the flow seed -/

section Arc

variable {α : ℝ → ℂ} {u : ℝ}

theorem crosscut_ne_neg_one (hα : IsDiscCrosscut α) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) : α s ≠ -1 :=
  fun he => hs.1.ne' (hα.inj ⟨hs.1.le, hs.2⟩ ⟨le_rfl, zero_le_one⟩ (he.trans hα.zero.symm))

/-- Removing the flow seed `−1 = α 0` from an initial arc of a disc crosscut. -/
theorem crosscut_image_Icc_diff (hα : IsDiscCrosscut α) (hu1 : u ≤ 1) :
    α '' Icc 0 u \ {-1} = α '' Ioc 0 u := by
  ext w
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, hne⟩
    refine ⟨s, ⟨lt_of_le_of_ne hs.1 fun h => hne ?_, hs.2⟩, rfl⟩
    rw [← h]
    exact hα.zero
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, Ioc_subset_Icc_self hs, rfl⟩, crosscut_ne_neg_one hα ⟨hs.1, hs.2.trans hu1⟩⟩

/-- **A wall arc read backwards in the counterflow chart**: `v ↦ m̃(α(u/(1 + v)))` on `[0, ∞)` is continuous,
injective, tends to `∞`, has image `m̃(α((0, u]))`, starts at `m̃(α u)` and lies in `ℍ` for `v > 0`. -/
theorem crosscut_arcInf_props (hα : IsDiscCrosscut α) (hu : 0 < u) (hu1 : u ≤ 1) :
    ContinuousOn (fun v : ℝ => cfPt (α (u / (1 + v)))) (Ici 0) ∧
      InjOn (fun v : ℝ => cfPt (α (u / (1 + v)))) (Ici 0) ∧
      Tendsto (fun v : ℝ => ‖cfPt (α (u / (1 + v)))‖) atTop atTop ∧
      (fun v : ℝ => cfPt (α (u / (1 + v)))) '' Ici 0 = cfPt '' (α '' Ioc 0 u) ∧
      (∀ v ∈ Ioi (0 : ℝ), cfPt (α (u / (1 + v))) ∈ H) := by
  have hmem : ∀ v ∈ Ici (0 : ℝ), u / (1 + v) ∈ Ioc (0 : ℝ) 1 := fun v hv =>
    ⟨(div_one_add_mem hu hv).1, (div_one_add_mem hu hv).2.trans hu1⟩
  have hgc : ContinuousOn (fun v : ℝ => u / (1 + v)) (Ici 0) :=
    continuousOn_const.div (continuousOn_const.add continuousOn_id) fun v hv => by
      have : (0 : ℝ) ≤ v := hv
      positivity
  have hαc : ContinuousOn (fun v : ℝ => α (u / (1 + v))) (Ici 0) :=
    hα.cont.comp hgc fun v hv => Ioc_subset_Icc_self (hmem v hv)
  refine ⟨continuousOn_cfPt.comp hαc fun v hv => crosscut_ne_neg_one hα (hmem v hv), ?_, ?_, ?_, ?_⟩
  · intro v hv v' hv' he
    exact injOn_div_one_add hu hv hv' (hα.inj (Ioc_subset_Icc_self (hmem v hv)) (Ioc_subset_Icc_self (hmem v' hv'))
      (injOn_cfPt (crosscut_ne_neg_one hα (hmem v hv)) (crosscut_ne_neg_one hα (hmem v' hv')) he))
  · have h1 : Tendsto (fun v : ℝ => α (u / (1 + v))) atTop (𝓝 (-1)) := by
      have hc := (hα.cont 0 ⟨le_rfl, zero_le_one⟩).tendsto
      rw [hα.zero] at hc
      exact hc.comp ((tendsto_div_one_add hu).mono_right
        (nhdsWithin_mono _ fun s hs => ⟨hs.1.le, hs.2.trans hu1⟩))
    have h2 : Tendsto (fun v : ℝ => α (u / (1 + v))) atTop (𝓝[≠] (-1)) :=
      tendsto_nhdsWithin_iff.2 ⟨h1, (eventually_ge_atTop (0 : ℝ)).mono fun v hv =>
        crosscut_ne_neg_one hα (hmem v hv)⟩
    exact tendsto_norm_cfPt.comp h2
  · rw [← image_div_one_add_Ici hu, image_image, image_image]
  · intro v hv
    exact cfPt_mem_H (hα.mem_disc _ ⟨(div_one_add_mem hu (le_of_lt hv)).1,
      (div_one_add_lt hu hv).trans_le hu1⟩)

end Arc

/-! ### The two-arc bundle at infinity -/

/-- **The two-arc topology of a reverse-contained pocket at infinity** (the topological fields of
`Sec6.IsReversePocketInf`): `C ⊆ ℍ` is open and connected, its frontier is the union of two arcs
`α₁, α₂ : [0, ∞) → ℂ`, continuous, injective and tending to `∞`, from the common start `y₀ = α₁ 0 = α₂ 0`, whose
parts after `y₀` are disjoint and lie in `ℍ`, the start `y₀` in `ℍ` or equal to `0`. -/
structure IsCfPocketInf (C : Set ℂ) (α₁ α₂ : ℝ → ℂ) : Prop where
  isOpen : IsOpen C
  isConnected : IsConnected C
  subset_H : C ⊆ H
  frontier_eq : frontier C = α₁ '' Ici 0 ∪ α₂ '' Ici 0
  cont₁ : ContinuousOn α₁ (Ici 0)
  cont₂ : ContinuousOn α₂ (Ici 0)
  inj₁ : InjOn α₁ (Ici 0)
  inj₂ : InjOn α₂ (Ici 0)
  tendsto₁ : Tendsto (fun v => ‖α₁ v‖) atTop atTop
  tendsto₂ : Tendsto (fun v => ‖α₂ v‖) atTop atTop
  seed : α₂ 0 = α₁ 0
  sides : ∀ v ∈ Ioi (0 : ℝ), ∀ v' ∈ Ioi (0 : ℝ), α₁ v ≠ α₂ v'
  mem_H₁ : ∀ v ∈ Ioi (0 : ℝ), α₁ v ∈ H
  mem_H₂ : ∀ v ∈ Ioi (0 : ℝ), α₂ v ∈ H
  mem_y : α₁ 0 ∈ H ∨ α₁ 0 = 0

/-- `Sec6.IsReversePocketInf` from the two-arc topology at infinity and the counterflow's fields. -/
theorem IsCfPocketInf.isReversePocketInf {C : Set ℂ} {α₁ α₂ : ℝ → ℂ} (hC : IsCfPocketInf C α₁ α₂) {W : ℝ → ℝ}
    {η : ℝ → ℂ} {τ : ℝ} (trace : IsLoewnerTrace W η) (continuous_W : Continuous W) (W_zero : W 0 = 0)
    (rev₁ : Sec6.IsReverseVisitOrderInf α₁ fun t => η '' Icc 0 t)
    (rev₂ : Sec6.IsReverseVisitOrderInf α₂ fun t => η '' Icc 0 t)
    (visited₁ : ∀ v ∈ Ici (0 : ℝ), ∃ t, α₁ v ∈ η '' Icc 0 t)
    (visited₂ : ∀ v ∈ Ici (0 : ℝ), ∃ t, α₂ v ∈ η '' Icc 0 t)
    (nonneg : 0 ≤ τ) (first_y : η τ = α₁ 0) (fresh_y : α₁ 0 ∉ η '' Ico 0 τ) :
    Sec6.IsReversePocketInf W η C α₁ α₂ τ :=
  ⟨trace, continuous_W, W_zero, hC.isOpen, hC.isConnected, hC.subset_H, hC.frontier_eq, hC.cont₁, hC.cont₂,
    hC.inj₁, hC.inj₂, hC.tendsto₁, hC.tendsto₂, hC.seed, hC.sides, hC.mem_H₁, hC.mem_H₂, hC.mem_y, rev₁, rev₂,
    visited₁, visited₂, nonneg, first_y, fresh_y⟩

section Change

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0}

/-- The right-wall arc in the counterflow chart at infinity, from `m(y₀)` (`v = 0`) to `∞` (`v → ∞`). -/
def cfArcRInf (R L : ℝ≥0 → ℂ) (r : ℝ≥0) (v : ℝ) : ℂ := cfPt (toDisc (realPath R) (rightHi R L r / (1 + v)))

/-- The left-wall arc in the counterflow chart at infinity, from `m(y₀)` (`v = 0`) to `∞` (`v → ∞`). -/
def cfArcLInf (R L : ℝ≥0 → ℂ) (r : ℝ≥0) (v : ℝ) : ℂ := cfPt (toDisc (realPath L) (leftHi R L r / (1 + v)))

end Change

end InteractingSLE.Sec7.PocketJordan

namespace InteractingSLE.Sec7.PocketCoord.IsChangeConfigInc

open WangWu Lemma71I PocketJordan

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0}

/-- When the pocket opens at the flow seed on the right wall, it does so on the left wall too. -/
theorem leftLo_eq_zero_of_rightLo_eq_zero (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0) :
    leftLo R L r = 0 := by
  obtain ⟨-, -, -, ha, -, -, hLa, -⟩ := h.changeCorner_props
  refine h.isDiscCrosscut_left.inj ha ⟨le_rfl, zero_le_one⟩ ?_
  rw [hLa, h.isDiscCrosscut_left.zero, openPt, h0]
  exact h.isDiscCrosscut_right.zero

/-- **The two-arc topology of the change pocket opening at the flow seed, in the counterflow chart**:
`IsCfPocketInf` for `cfPocket` with the arcs `cfArcRInf`, `cfArcLInf` (Aux. lemma 41 at infinity). -/
theorem isCfPocketInf (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0) :
    IsCfPocketInf (cfPocket R L r) (cfArcRInf R L r) (cfArcLInf R L r) := by
  obtain ⟨-, hj1, hj2, hgL, -, -⟩ := h.changeCorners
  obtain ⟨-, -, hfr⟩ := h.cayleyChange_props
  obtain ⟨hu, hv, huv, ha, hb, hab, hLa, hLb⟩ := h.changeCorner_props
  have ha0 := h.leftLo_eq_zero_of_rightLo_eq_zero h0
  have hαR := h.isDiscCrosscut_right
  have hαL := h.isDiscCrosscut_left
  have hu0 : 0 < rightHi R L r := h0 ▸ huv
  have hb0 : 0 < leftHi R L r := ha0 ▸ hab
  obtain ⟨hcR, hiR, htR, himR, hHR⟩ := crosscut_arcInf_props hαR hu0 hv.2
  obtain ⟨hcL, hiL, htL, himL, hHL⟩ := crosscut_arcInf_props hαL hb0 hb.2
  refine ⟨isOpen_image_negInv' h.isOpen_changePocket h.changePocket_subset_H,
    isConnected_image_negInv h.isConnected_changePocket h.changePocket_subset_H,
    PocketJordan.image_negInv_subset_H h.changePocket_subset_H, ?_, hcR, hcL, hiR, hiL, htR, htL, ?_, ?_, hHR, hHL, ?_⟩
  · rw [cfPocket, frontier_image_negInv_eq h.isOpen_changePocket h.changePocket_subset_H, hfr, pocketCurve, hj1, hj2,
      h0, ha0, union_sdiff_distrib, crosscut_image_Icc_diff hαR hv.2, crosscut_image_Icc_diff hαL hb.2, image_union]
    exact congrArg₂ (· ∪ ·) himR.symm himL.symm
  · simp only [cfArcLInf, cfArcRInf, add_zero, div_one]
    rw [hLb]
    rfl
  · intro v hv' v' hv'' he
    have hm := div_one_add_mem hu0 (le_of_lt hv')
    have hm' := div_one_add_mem hb0 (le_of_lt hv'')
    have hlt' := div_one_add_lt hb0 hv''
    have he' := injOn_cfPt (crosscut_ne_neg_one hαR ⟨hm.1, hm.2.trans hv.2⟩)
      (crosscut_ne_neg_one hαL ⟨hm'.1, hm'.2.trans hb.2⟩) he
    refine hgL.2.2.2 _ ⟨ha0 ▸ hm'.1, hlt'⟩ ⟨⟨hm'.1.le, hm'.2.trans hb.2⟩, _, ⟨hm.1.le, hm.2.trans hv.2⟩, he'⟩
  · simp only [cfArcRInf, add_zero, div_one]
    rcases hv.2.lt_or_eq with hv1 | hv1
    · exact Or.inl (cfPt_mem_H (hαR.mem_disc _ ⟨hu0, hv1⟩))
    · right
      rw [hv1, hαR.one, cfPt_one]

end InteractingSLE.Sec7.PocketCoord.IsChangeConfigInc
