/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketJordan
import InteractingSLE.Spec.Sec7.PocketCoordMeas
import InteractingSLE.Spec.Sec7.Lemma71KChart

/-!
# Aux. lemma 130's change pocket in the counterflow chart: Jordan coordinate and two-arc topology

Packet PROVE-STRIPSYS17 (specification §7.4.1, Aux. lemma 130 and the proof of Lemma 7.25, pp. 408–414: "the selected
two-arc Jordan pocket is nondegenerate"; "The erased counterflow is therefore a complete continuous traversal of this
actual Jordan pocket"). The change pocket `changePocket R L r` (PROVE-STRIPSYS8, `PocketCoordJordan.lean`) of the right
wall `R` and the left wall `L` lives in the flow chart. In the compactified (Cayley) picture its closure is bounded by
the right-wall arc `α̃_R[u, v]` and the left-wall arc `α̃_L[a, b]` between the opening contact `x₀` (disc point
`openPt = α̃_R(u) = α̃_L(a)`) and the closing contact `y₀` (`closePt = α̃_R(v) = α̃_L(b)`; `closePt = 1` when `y₀` is
the flow target `∞`).

The counterflow, a Loewner trace from `0` in the chart `m(z) = −1/z`, traverses the inverted pocket `cfPocket = m(C)`
from `m(y₀)` to `m(x₀)`. When the opening contact is not the flow seed (`0 ∉ closure C`: the pocket is bounded in the
counterflow chart; the other case is Aux. lemma 41 at infinity), this file proves:

* **`exists_isJordanCoord_cfPocket`**: a Jordan coordinate of `cfPocket` with `m(x₀) ↦ ∞`, `m(y₀) ↦ 0`
  (`Sec6.IsJordanCoord`, the input of `PocketTraversal.isDrivenCurve_relCurve_of_isReversePocket`);
* **`isCfPocket`**: the two-arc topology of `cfPocket` required by `Sec6.IsReversePocket` (open, connected, bounded, its
  frontier the two arcs `cfArcR`, `cfArcL` parametrized on `[0, 1]` from `m(x₀)` to `m(y₀)`, continuous and injective,
  with disjoint open arcs in `ℍ`, the start `m(y₀)` in `ℍ` or equal to `0`), bundled as `IsCfPocket`;
* `IsCfPocket.isReversePocket`: `Sec6.IsReversePocket` from `IsCfPocket` and the counterflow's fields (trace, reverse
  visit orders, first-visit times, the earlier flow-line part `β`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Function Bornology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open SupercriticalConformalCovariance (IsConformalBijection)
open InteractingSLE.WangWu (negInv)
open scoped NNReal

namespace InteractingSLE.Sec7.PocketJordan

open WangWu PocketCoord Lemma71I

/-! ### The two-arc pocket bundle -/

/-- **The two-arc topology of a reverse-contained pocket** (the topological fields of `Sec6.IsReversePocket`): `C` is
open, connected and bounded, its frontier is the union of two arcs `α₁, α₂ : [0, 1] → ℂ`, continuous and injective,
from the common junction `x₀ = α₁ 0 = α₂ 0` to the common start `y₀ = α₁ 1 = α₂ 1`, whose open subarcs are disjoint,
lying in `ℍ` except possibly at `y₀ = 0`. -/
structure IsCfPocket (C : Set ℂ) (α₁ α₂ : ℝ → ℂ) : Prop where
  isOpen : IsOpen C
  isConnected : IsConnected C
  isBounded : IsBounded C
  frontier_eq : frontier C = α₁ '' Icc 0 1 ∪ α₂ '' Icc 0 1
  cont₁ : ContinuousOn α₁ (Icc 0 1)
  cont₂ : ContinuousOn α₂ (Icc 0 1)
  inj₁ : InjOn α₁ (Icc 0 1)
  inj₂ : InjOn α₂ (Icc 0 1)
  junction : α₂ 0 = α₁ 0
  seed : α₂ 1 = α₁ 1
  sides : ∀ v ∈ Ioo (0 : ℝ) 1, ∀ v' ∈ Ioo (0 : ℝ) 1, α₁ v ≠ α₂ v'
  mem_H₁ : ∀ v ∈ Ico (0 : ℝ) 1, α₁ v ∈ H
  mem_H₂ : ∀ v ∈ Ico (0 : ℝ) 1, α₂ v ∈ H
  mem_y : α₁ 1 ∈ H ∨ α₁ 1 = 0

/-- `Sec6.IsReversePocket` from the two-arc topology and the counterflow's fields. -/
theorem IsCfPocket.isReversePocket {C : Set ℂ} {α₁ α₂ β : ℝ → ℂ} (hC : IsCfPocket C α₁ α₂) {W : ℝ → ℝ}
    {η : ℝ → ℂ} {τ σ : ℝ} (trace : IsLoewnerTrace W η) (continuous_W : Continuous W) (W_zero : W 0 = 0)
    (rev₁ : R16.IsReverseVisitOrder α₁ fun t => η '' Icc 0 t)
    (rev₂ : R16.IsReverseVisitOrder α₂ fun t => η '' Icc 0 t)
    (cont_β : ContinuousOn β (Ici 0)) (inj_β : InjOn β (Ici 0)) (β_zero : β 0 = α₁ 0)
    (tendsto_β : Tendsto (fun t => ‖β t‖) atTop atTop) (mem_H_β : ∀ t ∈ Ici (0 : ℝ), β t ∈ H)
    (rev_β : ∀ t : ℝ, ∀ s ∈ Ici (0 : ℝ), β s ∈ η '' Icc 0 t → α₁ 0 ∈ η '' Icc 0 t)
    (nonneg : 0 ≤ τ) (nonneg_σ : 0 ≤ σ) (first_y : η τ = α₁ 1) (fresh_y : α₁ 1 ∉ η '' Ico 0 τ)
    (first_x : η σ = α₁ 0) (fresh_x : α₁ 0 ∉ η '' Ico 0 σ) :
    Sec6.IsReversePocket W η C α₁ α₂ β τ σ :=
  ⟨trace, continuous_W, W_zero, hC.isOpen, hC.isConnected, hC.isBounded, hC.frontier_eq, hC.cont₁, hC.cont₂,
    hC.inj₁, hC.inj₂, hC.junction, hC.seed, hC.sides, hC.mem_H₁, hC.mem_H₂, hC.mem_y, rev₁, rev₂, cont_β, inj_β,
    β_zero, tendsto_β, mem_H_β, rev_β, nonneg, nonneg_σ, first_y, fresh_y, first_x, fresh_x⟩

/-! ### The corners of the change pocket -/

section Change

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0}

/-- The left-wall parameter (disc parametrization) of the opening corner. -/
def leftLo (R L : ℝ≥0 → ℂ) (r : ℝ≥0) : ℝ := gapLo (toDisc (realPath L)) (toDisc (realPath R)) (discTime r)

/-- The left-wall parameter of the closing corner. -/
def leftHi (R L : ℝ≥0 → ℂ) (r : ℝ≥0) : ℝ := gapHi (toDisc (realPath L)) (toDisc (realPath R)) (discTime r)

/-- The right-wall parameter of the opening corner. -/
def rightLo (R L : ℝ≥0 → ℂ) (r : ℝ≥0) : ℝ :=
  contactMap (toDisc (realPath L)) (toDisc (realPath R)) (leftLo R L r)

/-- The right-wall parameter of the closing corner. -/
def rightHi (R L : ℝ≥0 → ℂ) (r : ℝ≥0) : ℝ :=
  contactMap (toDisc (realPath L)) (toDisc (realPath R)) (leftHi R L r)

/-- The opening contact `x₀` in the disc. -/
def openPt (R L : ℝ≥0 → ℂ) (r : ℝ≥0) : ℂ := toDisc (realPath R) (rightLo R L r)

/-- The closing contact `y₀` in the disc (`1` when `y₀` is the flow target). -/
def closePt (R L : ℝ≥0 → ℂ) (r : ℝ≥0) : ℂ := toDisc (realPath R) (rightHi R L r)

/-- The change pocket in the counterflow chart: `m(C)`, `m(z) = −1/z`. -/
def cfPocket (R L : ℝ≥0 → ℂ) (r : ℝ≥0) : Set ℂ := negInv '' changePocket R L r

/-- The right-wall arc in the counterflow chart, from `m(x₀)` (`s = 0`) to `m(y₀)` (`s = 1`). -/
def cfArcR (R L : ℝ≥0 → ℂ) (r : ℝ≥0) (s : ℝ) : ℂ :=
  cfPt (toDisc (realPath R) (rightLo R L r + s * (rightHi R L r - rightLo R L r)))

/-- The left-wall arc in the counterflow chart, from `m(x₀)` (`s = 0`) to `m(y₀)` (`s = 1`). -/
def cfArcL (R L : ℝ≥0 → ℂ) (r : ℝ≥0) (s : ℝ) : ℂ :=
  cfPt (toDisc (realPath L) (leftLo R L r + s * (leftHi R L r - leftLo R L r)))

end Change

end InteractingSLE.Sec7.PocketJordan

namespace InteractingSLE.Sec7.PocketCoord.IsChangeConfigInc

open WangWu Lemma71I PocketJordan

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0}

/-- **The corners of the change pocket**: the right-wall parameters form a contact gap whose left-wall parameters are
the left-wall gap containing the change parameter, and the change gap is the inside of their pocket curve. -/
theorem changeCorners (h : IsChangeConfigInc R L r) :
    IsContactGap (toDisc (realPath R)) (toDisc (realPath L)) (rightLo R L r) (rightHi R L r) ∧
      contactMap (toDisc (realPath R)) (toDisc (realPath L)) (rightLo R L r) = leftLo R L r ∧
      contactMap (toDisc (realPath R)) (toDisc (realPath L)) (rightHi R L r) = leftHi R L r ∧
      IsContactGap (toDisc (realPath L)) (toDisc (realPath R)) (leftLo R L r) (leftHi R L r) ∧
      discTime r ∈ Ioo (leftLo R L r) (leftHi R L r) ∧
      cayley '' changePocket R L r =
        jordanIn (pocketCurve (toDisc (realPath R)) (toDisc (realPath L)) (rightLo R L r) (rightHi R L r)) := by
  obtain ⟨hg, heq⟩ := h.changeGap_eq
  obtain ⟨hgL, hc⟩ := isContactGap_gapLo_gapHi h.isDiscCrosscut_right h.isDiscCrosscut_left
    (discTime_mem_Icc r) h.notMem_crossRange
  obtain ⟨-, h1, h2⟩ := isContactGap_swap h.isDiscCrosscut_right h.isDiscCrosscut_left h.inc hgL
  obtain ⟨-, -, -, hC⟩ := h.changePocket_eq
  exact ⟨hg, h1, h2, hgL, hc, hC.trans heq⟩

/-- The pocket curve is a Jordan curve, the frontier of the Cayley image, inside the closed disc. -/
theorem cayleyChange_props (h : IsChangeConfigInc R L r) :
    LQGMetric.JordanMap.IsJordanCurve
        (pocketCurve (toDisc (realPath R)) (toDisc (realPath L)) (rightLo R L r) (rightHi R L r)) ∧
      cayley '' changePocket R L r ⊆ ball 0 1 ∧
      frontier (cayley '' changePocket R L r) =
        pocketCurve (toDisc (realPath R)) (toDisc (realPath L)) (rightLo R L r) (rightHi R L r) := by
  obtain ⟨hg, -, -, -, -, hC⟩ := h.changeCorners
  obtain ⟨hJ, hball, -, hfr, -⟩ :=
    pocket_props_of_strictMono h.isDiscCrosscut_right h.isDiscCrosscut_left h.inc hg
  rw [hC]
  exact ⟨hJ, hball, hfr⟩

theorem changePocket_subset_H (h : IsChangeConfigInc R L r) : changePocket R L r ⊆ H := fun _ hz =>
  (h.changePocket_subset hz).1

theorem isOpen_changePocket (h : IsChangeConfigInc R L r) : IsOpen (changePocket R L r) :=
  h.isOpen_isConnected_isSimplyConnected.1

theorem isConnected_changePocket (h : IsChangeConfigInc R L r) : IsConnected (changePocket R L r) :=
  h.isOpen_isConnected_isSimplyConnected.2.1

/-- The two corners of the pocket on the right wall, and their left-wall descriptions. -/
theorem changeCorner_props (h : IsChangeConfigInc R L r) :
    rightLo R L r ∈ Icc (0 : ℝ) 1 ∧ rightHi R L r ∈ Icc (0 : ℝ) 1 ∧ rightLo R L r < rightHi R L r ∧
      leftLo R L r ∈ Icc (0 : ℝ) 1 ∧ leftHi R L r ∈ Icc (0 : ℝ) 1 ∧ leftLo R L r < leftHi R L r ∧
      toDisc (realPath L) (leftLo R L r) = openPt R L r ∧ toDisc (realPath L) (leftHi R L r) = closePt R L r := by
  obtain ⟨hg, h1, h2, hgL, -, -⟩ := h.changeCorners
  obtain ⟨-, e1⟩ := contactMap_mem h.isDiscCrosscut_left hg.1
  obtain ⟨-, e2⟩ := contactMap_mem h.isDiscCrosscut_left hg.2.1
  rw [h1] at e1
  rw [h2] at e2
  exact ⟨hg.1.1, hg.2.1.1, hg.2.2.1, hgL.1.1, hgL.2.1.1, hgL.2.2.1, e1, e2⟩

theorem openPt_mem_frontier (h : IsChangeConfigInc R L r) :
    openPt R L r ∈ frontier (cayley '' changePocket R L r) := by
  obtain ⟨h0, h1, h01, -⟩ := h.changeCorner_props
  rw [h.cayleyChange_props.2.2]
  exact Or.inl ⟨_, ⟨le_rfl, h01.le⟩, rfl⟩

theorem closePt_mem_frontier (h : IsChangeConfigInc R L r) :
    closePt R L r ∈ frontier (cayley '' changePocket R L r) := by
  obtain ⟨h0, h1, h01, -⟩ := h.changeCorner_props
  rw [h.cayleyChange_props.2.2]
  exact Or.inl ⟨_, ⟨h01.le, le_rfl⟩, rfl⟩

theorem openPt_ne_closePt (h : IsChangeConfigInc R L r) : openPt R L r ≠ closePt R L r := fun he =>
  (h.changeCorner_props.2.2.1).ne (h.isDiscCrosscut_right.inj h.changeCorner_props.1 h.changeCorner_props.2.1 he)

theorem closePt_ne_neg_one (h : IsChangeConfigInc R L r) : closePt R L r ≠ -1 := fun he => by
  obtain ⟨h0, h1, h01, -⟩ := h.changeCorner_props
  have := h.isDiscCrosscut_right.inj h1 ⟨le_rfl, zero_le_one⟩ (he.trans h.isDiscCrosscut_right.zero.symm)
  linarith [h0.1]

/-- If the flow seed is not adherent to the pocket, `−1` (its disc image) is not adherent to the Cayley image. -/
theorem neg_one_notMem_closure_cayley (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r)) :
    (-1 : ℂ) ∉ closure (cayley '' changePocket R L r) := by
  intro hm
  have hc : ContinuousAt cayleyInv (-1) :=
    (QuantumZipper.CA.differentiableAt_cayleyInv (by norm_num)).continuousAt
  have hid : cayleyInv '' (cayley '' changePocket R L r) = changePocket R L r := by
    rw [image_image]
    refine (image_congr fun z hz => QuantumZipper.CA.cayleyInv_cayley
      (add_I_ne_zero_of_mem_Hbar (H_subset_Hbar' (h.changePocket_subset_H hz)))).trans (image_id _)
  have := hc.continuousWithinAt.mem_closure_image hm
  rw [hid, show cayleyInv (-1) = 0 by simp [QuantumZipper.CA.cayleyInv]] at this
  exact h0 this

theorem openPt_ne_neg_one (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r)) :
    openPt R L r ≠ -1 := fun he =>
  h.neg_one_notMem_closure_cayley h0 (he ▸ frontier_subset_closure h.openPt_mem_frontier)

theorem rightLo_pos (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r)) :
    0 < rightLo R L r := by
  refine lt_of_le_of_ne h.changeCorner_props.1.1 fun he => h.openPt_ne_neg_one h0 ?_
  rw [openPt, ← he]
  exact h.isDiscCrosscut_right.zero

theorem leftLo_pos (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r)) :
    0 < leftLo R L r := by
  refine lt_of_le_of_ne h.changeCorner_props.2.2.2.1.1 fun he => h.openPt_ne_neg_one h0 ?_
  rw [← h.changeCorner_props.2.2.2.2.2.2.1, ← he]
  exact h.isDiscCrosscut_left.zero

/-- **The change pocket has a Jordan coordinate in the counterflow chart** (bounded case): `m(x₀) ↦ ∞`, `m(y₀) ↦ 0`.
The coordinate is `cfCoord a Ψ q` for any two-point uniformizer `Ψ` of the Cayley image and any `a > 0`. -/
theorem isJordanCoord_cfCoord (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    {Ψ : ℂ → ℂ} (hU : IsBdryUniformizer (cayley '' changePocket R L r) (openPt R L r) (closePt R L r) Ψ) {a : ℝ}
    (ha : 0 < a) :
    Sec6.IsJordanCoord (cfPocket R L r) (cfPt (openPt R L r)) (cfPt (closePt R L r)) (cfCoord a Ψ (closePt R L r)) :=
  PocketJordan.isJordanCoord_cfCoord h.isOpen_changePocket h.changePocket_subset_H hU h.openPt_mem_frontier
    h.closePt_mem_frontier
    h.openPt_ne_closePt (h.openPt_ne_neg_one h0) h.closePt_ne_neg_one ha

/-- The Cayley image of the change pocket has a two-point uniformizer with its boundary extension. -/
theorem exists_isBdryUniformizer (h : IsChangeConfigInc R L r) :
    ∃ Ψ : ℂ → ℂ, IsBdryUniformizer (cayley '' changePocket R L r) (openPt R L r) (closePt R L r) Ψ := by
  obtain ⟨hJ, hball, hfr⟩ := h.cayleyChange_props
  refine PocketJordan.exists_isBdryUniformizer
    (Lemma71F.isOpen_cayley_image h.isOpen_changePocket h.changePocket_subset_H)
    (Lemma71F.isConnected_cayley_image h.isConnected_changePocket h.changePocket_subset_H)
    (isBounded_ball.subset hball) (hfr ▸ hJ)
    h.openPt_mem_frontier h.closePt_mem_frontier h.openPt_ne_closePt

/-- **The change pocket has a Jordan coordinate in the counterflow chart** (bounded case). -/
theorem exists_isJordanCoord_cfPocket (h : IsChangeConfigInc R L r)
    (h0 : (0 : ℂ) ∉ closure (changePocket R L r)) :
    ∃ ψ : ℂ → ℂ, Sec6.IsJordanCoord (cfPocket R L r) (cfPt (openPt R L r)) (cfPt (closePt R L r)) ψ := by
  obtain ⟨Ψ, hU⟩ := h.exists_isBdryUniformizer
  exact ⟨_, h.isJordanCoord_cfCoord h0 hU one_pos⟩

/-- The affine reparametrization `s ↦ lo + s (hi − lo)` maps `[0, 1]` into `[lo, hi]`, `(0, 1)` into `(lo, hi)` and
`[0, 1)` into `[lo, hi)`. -/
theorem affine_mem {lo hi s : ℝ} (hlh : lo < hi) :
    (s ∈ Icc (0 : ℝ) 1 → lo + s * (hi - lo) ∈ Icc lo hi) ∧ (s ∈ Ioo (0 : ℝ) 1 → lo + s * (hi - lo) ∈ Ioo lo hi) ∧
      (s ∈ Ico (0 : ℝ) 1 → lo + s * (hi - lo) ∈ Ico lo hi) := by
  have hd : 0 < hi - lo := sub_pos.2 hlh
  refine ⟨fun hs => ⟨?_, ?_⟩, fun hs => ⟨?_, ?_⟩, fun hs => ⟨?_, ?_⟩⟩
  · nlinarith [hs.1]
  · nlinarith [hs.2]
  · nlinarith [hs.1]
  · nlinarith [hs.2]
  · nlinarith [hs.1]
  · nlinarith [hs.2]

theorem affine_injective {lo hi : ℝ} (hlh : lo < hi) : Injective fun s : ℝ => lo + s * (hi - lo) := fun _ _ he =>
  mul_right_cancel₀ (sub_ne_zero.2 hlh.ne') (add_left_cancel he)

/-- **The two-arc topology of the change pocket in the counterflow chart** (bounded case): `IsCfPocket` for
`cfPocket` with the arcs `cfArcR`, `cfArcL`. -/
theorem isCfPocket (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r)) :
    IsCfPocket (cfPocket R L r) (cfArcR R L r) (cfArcL R L r) := by
  obtain ⟨-, hj1, hj2, hgL, -, -⟩ := h.changeCorners
  obtain ⟨-, -, hfr⟩ := h.cayleyChange_props
  obtain ⟨hu, hv, huv, ha, hb, hab, hLa, hLb⟩ := h.changeCorner_props
  have hu0 := h.rightLo_pos h0
  have ha0 := h.leftLo_pos h0
  have hαR := h.isDiscCrosscut_right
  have hαL := h.isDiscCrosscut_left
  have hIR : Icc (rightLo R L r) (rightHi R L r) ⊆ Icc 0 1 := fun s hs => ⟨hu.1.trans hs.1, hs.2.trans hv.2⟩
  have hIL : Icc (leftLo R L r) (leftHi R L r) ⊆ Icc 0 1 := fun s hs => ⟨ha.1.trans hs.1, hs.2.trans hb.2⟩
  have hRne : ∀ s ∈ Icc (rightLo R L r) (rightHi R L r), toDisc (realPath R) s ≠ -1 := fun s hs he => by
    have := hαR.inj (hIR hs) ⟨le_rfl, zero_le_one⟩ (he.trans hαR.zero.symm)
    linarith [hs.1]
  have hLne : ∀ s ∈ Icc (leftLo R L r) (leftHi R L r), toDisc (realPath L) s ≠ -1 := fun s hs he => by
    have := hαL.inj (hIL hs) ⟨le_rfl, zero_le_one⟩ (he.trans hαL.zero.symm)
    linarith [hs.1]
  have h1 : (-1 : ℂ) ∉ frontier (cayley '' changePocket R L r) := fun hm =>
    h.neg_one_notMem_closure_cayley h0 (frontier_subset_closure hm)
  have eR : cfArcR R L r '' Icc 0 1 = cfPt '' (toDisc (realPath R) '' Icc (rightLo R L r) (rightHi R L r)) := by
    rw [← image_affine_Icc_zero_one huv.le, image_image, image_image]
    rfl
  have eL : cfArcL R L r '' Icc 0 1 = cfPt '' (toDisc (realPath L) '' Icc (leftLo R L r) (leftHi R L r)) := by
    rw [← image_affine_Icc_zero_one hab.le, image_image, image_image]
    rfl
  have hcontR : ContinuousOn (fun s : ℝ => toDisc (realPath R) (rightLo R L r + s * (rightHi R L r - rightLo R L r)))
      (Icc 0 1) :=
    hαR.cont.comp (by fun_prop) fun s hs => hIR ((affine_mem huv).1 hs)
  have hcontL : ContinuousOn (fun s : ℝ => toDisc (realPath L) (leftLo R L r + s * (leftHi R L r - leftLo R L r)))
      (Icc 0 1) :=
    hαL.cont.comp (by fun_prop) fun s hs => hIL ((affine_mem hab).1 hs)
  refine ⟨isOpen_image_negInv' h.isOpen_changePocket h.changePocket_subset_H,
    isConnected_image_negInv h.isConnected_changePocket h.changePocket_subset_H, isBounded_image_negInv h0, ?_,
    continuousOn_cfPt.comp hcontR fun s hs => hRne _ ((affine_mem huv).1 hs),
    continuousOn_cfPt.comp hcontL fun s hs => hLne _ ((affine_mem hab).1 hs), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cfPocket, frontier_image_negInv h.isOpen_changePocket h.changePocket_subset_H h1, hfr, pocketCurve,
      image_union, hj1, hj2, eR, eL]
  · intro s hs s' hs' he
    have hm := (affine_mem huv).1 hs
    have hm' := (affine_mem huv).1 hs'
    exact affine_injective huv (hαR.inj (hIR hm) (hIR hm') (injOn_cfPt (hRne _ hm) (hRne _ hm') he))
  · intro s hs s' hs' he
    have hm := (affine_mem hab).1 hs
    have hm' := (affine_mem hab).1 hs'
    exact affine_injective hab (hαL.inj (hIL hm) (hIL hm') (injOn_cfPt (hLne _ hm) (hLne _ hm') he))
  · simp only [cfArcL, cfArcR, zero_mul, add_zero]
    rw [hLa]
    rfl
  · simp only [cfArcL, cfArcR, one_mul, add_sub_cancel]
    rw [hLb]
    rfl
  · intro s hs s' hs' he
    have hm := (affine_mem huv).2.1 hs
    have hm' := (affine_mem hab).2.1 hs'
    have he' := injOn_cfPt (hRne _ (Ioo_subset_Icc_self hm)) (hLne _ (Ioo_subset_Icc_self hm')) he
    exact hgL.2.2.2 _ hm' ⟨hIL (Ioo_subset_Icc_self hm'), _, hIR (Ioo_subset_Icc_self hm), he'⟩
  · intro s hs
    have hm := (affine_mem huv).2.2 hs
    exact cfPt_mem_H (hαR.mem_disc _ ⟨hu0.trans_le hm.1, hm.2.trans_le hv.2⟩)
  · intro s hs
    have hm := (affine_mem hab).2.2 hs
    exact cfPt_mem_H (hαL.mem_disc _ ⟨ha0.trans_le hm.1, hm.2.trans_le hb.2⟩)
  · simp only [cfArcR, one_mul, add_sub_cancel]
    rcases hv.2.lt_or_eq with hv1 | hv1
    · exact Or.inl (cfPt_mem_H (hαR.mem_disc _ ⟨hu0.trans huv, hv1⟩))
    · right
      rw [hv1, hαR.one, cfPt_one]

/-- **The change pocket is a marked pocket of the right wall** (`Lemma71K.IsMarkedPocket`): the right-wall times in the
closure of its Cayley image are exactly `[rightLo, rightHi]`. This is the pathwise premise of the approach sequences of
the measurable chart (`Lemma71K.exists_markedPocketChart`). -/
theorem isMarkedPocket (h : IsChangeConfigInc R L r) :
    Lemma71K.IsMarkedPocket R (changePocket R L r) (rightLo R L r) (rightHi R L r) := by
  obtain ⟨hg, hj1, hj2, hgL, -, hC⟩ := h.changeCorners
  obtain ⟨hJ, -, hfr⟩ := h.cayleyChange_props
  obtain ⟨hu, hv, huv, ha, hb, hab, hLa, hLb⟩ := h.changeCorner_props
  have hαR := h.isDiscCrosscut_right
  obtain ⟨-, -, hdisj, -, -⟩ := pocket_props_of_strictMono hαR h.isDiscCrosscut_left h.inc hg
  refine ⟨hu.1, huv, hv.2, ?_, hfr ▸ hJ, h.openPt_mem_frontier, h.closePt_mem_frontier, h.openPt_ne_closePt⟩
  ext s
  simp only [mem_Icc]
  constructor
  · rintro ⟨hs, hcl⟩
    rw [closure_eq_self_union_frontier, hfr] at hcl
    rcases hcl with hD | hPC
    · rw [hC] at hD
      exact absurd (Or.inl ⟨s, hs, rfl⟩) (Set.disjoint_left.1 hdisj hD)
    · rcases hPC with ⟨t, ht, he⟩ | ⟨t, ht, he⟩
      · have := hαR.inj ⟨hu.1.trans ht.1, ht.2.trans hv.2⟩ hs he
        exact this ▸ ht
      · rw [hj1, hj2] at ht
        -- `t` is a contact parameter of the left wall inside the closed gap: an end
        have htS : t ∈ Sec7.pocketContactSet (toDisc (realPath L)) (toDisc (realPath R)) :=
          ⟨⟨ha.1.trans ht.1, ht.2.trans hb.2⟩, s, hs, he.symm⟩
        rcases eq_or_lt_of_le ht.1 with hta | hta
        · rw [← hta, hLa] at he
          have := hαR.inj hu hs he
          exact this ▸ ⟨le_rfl, huv.le⟩
        rcases eq_or_lt_of_le ht.2 with htb | htb
        · rw [htb, hLb] at he
          have := hαR.inj hv hs he
          exact this ▸ ⟨huv.le, le_rfl⟩
        exact absurd htS (hgL.2.2.2 t ⟨hta, htb⟩)
  · intro hs
    refine ⟨⟨hu.1.trans hs.1, hs.2.trans hv.2⟩, ?_⟩
    rw [closure_eq_self_union_frontier, hfr]
    exact Or.inr (Or.inl ⟨s, hs, rfl⟩)

/-- The image of the opening contact is not in the inverted pocket. -/
theorem cfPt_openPt_notMem (h : IsChangeConfigInc R L r) : cfPt (openPt R L r) ∉ cfPocket R L r := by
  intro hm
  have hD : -cayley (cfPt (openPt R L r)) ∈ cayley '' changePocket R L r := by
    rw [← image_neg_cayley_image_negInv h.changePocket_subset_H]
    exact mem_image_of_mem _ hm
  have hfr := h.openPt_mem_frontier
  rw [(Lemma71F.isOpen_cayley_image h.isOpen_changePocket h.changePocket_subset_H).frontier_eq] at hfr
  by_cases h1 : openPt R L r = -1
  · -- then `cfPt (openPt) = 0 ∉ ℍ`
    have h0 : cfPt (openPt R L r) = 0 := by
      rw [h1, cfPt, neg_neg]
      simp [QuantumZipper.CA.cayleyInv]
    exact lt_irrefl _
      (show (0 : ℝ) < (0 : ℂ).im from h0 ▸ PocketJordan.image_negInv_subset_H h.changePocket_subset_H hm)
  · rw [neg_cayley_cfPt h1] at hD
    exact hfr.2 hD

/-- On the inverted pocket the counterflow Jordan coordinate is `m ∘ (a Ψ) ∘ cayley ∘ m`. -/
theorem cfCoord_of_mem (h : IsChangeConfigInc R L r) {a : ℝ} {Ψ : ℂ → ℂ} {z : ℂ} (hz : z ∈ cfPocket R L r) :
    cfCoord a Ψ (closePt R L r) z = negInv ((a : ℂ) * Ψ (cayley (negInv z))) := by
  obtain ⟨w, hw, rfl⟩ := hz
  have hwH := h.changePocket_subset_H hw
  have hc : cayley (negInv w) = -cayley w := cayley_negInv (H_subset_Hbar' hwH) (WangWu.ne_zero_of_mem_H hwH)
  have hne : -cayley (negInv w) ≠ closePt R L r := by
    rw [hc, neg_neg]
    intro he
    have hfr := h.closePt_mem_frontier
    rw [(Lemma71F.isOpen_cayley_image h.isOpen_changePocket h.changePocket_subset_H).frontier_eq] at hfr
    exact hfr.2 (he ▸ mem_image_of_mem _ hw)
  rw [cfCoord, cfMap_of_ne hne, WangWu.negInv_negInv, hc, neg_neg]

end InteractingSLE.Sec7.PocketCoord.IsChangeConfigInc
