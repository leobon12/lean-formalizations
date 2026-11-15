/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.WallOrdBasic

/-!
# The clipped walls of a change pocket: contained order, outer corrected order, outer refutation

Packet PROVE-WALL-ORDER (see `WallOrdBasic.lean`). For a change pocket `cfPocket R L r` (both shapes):

* `cfArcRInf_rev`, `cfArcLInf_rev`: a contained wall's clipped order at infinity (bounded: `R7StopIn.cfArcR_rev`,
  `R7StopIn.cfArcL_rev`);
* **`cfArcR_revOff`**, **`cfArcL_revOff`**, **`cfArcRInf_revOff`**, **`cfArcLInf_revOff`**: an outer wall
  (`range R ⊆ S ∪ range M`, `M` the certified frontier on its left, `S` its forbidden side; mirrored on the left) is
  visited in reverse first-visit order off `S`;
* **`exists_cfArcR_side`**, **`exists_cfArcL_side`**: a bounded clipped outer wall sharing no arc with `M` has a point
  on the forbidden side; **`not_isReverseVisitOrder_cfArcR_of_outer`**, **`not_isReverseVisitOrder_cfArcL_of_outer`**:
  hence the clipped order `R16.IsReverseVisitOrder` fails once the opening corner `m(x₀)` is visited.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)
open InteractingSLE.WangWu (negInv)
open scoped NNReal

namespace InteractingSLE.Sec7.WallOrd

open WangWu Lemma71I PocketCoord PocketJordan

variable {R L M : ℝ≥0 → ℂ} {r : ℝ≥0} {η : ℝ → ℂ} {S : Set ℂ}

/-! ### Contained walls at infinity -/

/-- **The right side of a change pocket opening at the flow seed is visited in reverse order when the right wall
is.** -/
theorem cfArcRInf_rev (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0) (hη0 : η 0 = 0)
    (hrevR : IsWallReverseVisit R η) : Sec6.IsReverseVisitOrderInf (cfArcRInf R L r) fun t => η '' Icc 0 t := by
  obtain ⟨-, hv, huv, -⟩ := h.changeCorner_props
  have hu0 : 0 < rightHi R L r := h0 ▸ huv
  have hdR : ∀ v ∈ Ici (0 : ℝ), rightHi R L r / (1 + v) ∈ Ioc (0 : ℝ) 1 := fun v hv' =>
    ⟨(div_one_add_mem hu0 hv').1, (div_one_add_mem hu0 hv').2.trans hv.2⟩
  intro t v₁ hv₁ v₂ hv₂ h12 hvis
  have h1 : (0 : ℝ) < 1 + v₁ := by linarith [mem_Ici.1 hv₁]
  exact wall_rev h.right hη0 hrevR (hdR v₂ hv₂) (hdR v₁ hv₁)
    (div_le_div_of_nonneg_left hu0.le h1 (by linarith)) hvis

/-- **The left side of a change pocket opening at the flow seed is visited in reverse order when the left wall
is.** -/
theorem cfArcLInf_rev (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0) (hη0 : η 0 = 0)
    (hrevL : IsWallReverseVisit L η) : Sec6.IsReverseVisitOrderInf (cfArcLInf R L r) fun t => η '' Icc 0 t := by
  obtain ⟨-, -, -, -, hb, hab, -⟩ := h.changeCorner_props
  have ha0 := h.leftLo_eq_zero_of_rightLo_eq_zero h0
  have hb0 : 0 < leftHi R L r := ha0 ▸ hab
  have hdL : ∀ v ∈ Ici (0 : ℝ), leftHi R L r / (1 + v) ∈ Ioc (0 : ℝ) 1 := fun v hv' =>
    ⟨(div_one_add_mem hb0 hv').1, (div_one_add_mem hb0 hv').2.trans hb.2⟩
  intro t v₁ hv₁ v₂ hv₂ h12 hvis
  have h1 : (0 : ℝ) < 1 + v₁ := by linarith [mem_Ici.1 hv₁]
  exact wall_rev h.left hη0 hrevL (hdL v₂ hv₂) (hdL v₁ hv₁)
    (div_le_div_of_nonneg_left hb0.le h1 (by linarith)) hvis

/-! ### Outer walls: the corrected order -/

/-- The contact order of a right wall with a frontier on its left. -/
theorem contactMono_right (hR : IsSimpleProper R) (hM : IsSimpleProper M)
    (hord : Disjoint (range M) (rightSideOf (range R))) :
    ∀ s₁ s₂ p₁ p₂ : ℝ, s₁ ∈ Icc (0 : ℝ) 1 → s₂ ∈ Icc (0 : ℝ) 1 → p₁ ∈ Icc (0 : ℝ) 1 → p₂ ∈ Icc (0 : ℝ) 1 →
      toDisc (Lemma71I.realPath R) s₁ = toDisc (Lemma71I.realPath M) p₁ →
      toDisc (Lemma71I.realPath R) s₂ = toDisc (Lemma71I.realPath M) p₂ → s₁ ≤ s₂ → p₁ ≤ p₂ :=
  fun _ _ _ _ hs₁ hs₂ hp₁ hp₂ e₁ e₂ h12 => le_of_contact hM.isProperArc.isDiscCrosscut_toDisc
    (OuterGeom.strictMonoOn_contactMap_of_ord hR hM hord) hs₁ hs₂ hp₁ hp₂ e₁ e₂ h12

/-- The contact order of a left wall with a frontier on its right. -/
theorem contactMono_left (hL : IsSimpleProper L) (hM : IsSimpleProper M)
    (hord : Disjoint (range L) (rightSideOf (range M))) :
    ∀ s₁ s₂ p₁ p₂ : ℝ, s₁ ∈ Icc (0 : ℝ) 1 → s₂ ∈ Icc (0 : ℝ) 1 → p₁ ∈ Icc (0 : ℝ) 1 → p₂ ∈ Icc (0 : ℝ) 1 →
      toDisc (Lemma71I.realPath L) s₁ = toDisc (Lemma71I.realPath M) p₁ →
      toDisc (Lemma71I.realPath L) s₂ = toDisc (Lemma71I.realPath M) p₂ → s₁ ≤ s₂ → p₁ ≤ p₂ :=
  fun _ _ _ _ hs₁ hs₂ hp₁ hp₂ e₁ e₂ h12 => le_of_contact_symm hL.isProperArc.isDiscCrosscut_toDisc
    (OuterGeom.strictMonoOn_contactMap_of_ord hM hL hord) hs₁ hs₂ hp₁ hp₂ e₁ e₂ h12

/-- **An outer right wall is visited in reverse order off its forbidden side** (bounded pocket; Consequence R.4). -/
theorem cfArcR_revOff (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hM : IsSimpleProper M) (hord : Disjoint (range M) (rightSideOf (range R))) (hout : range R ⊆ S ∪ range M)
    (hη0 : η 0 = 0) (hrevM : IsWallReverseVisit M η) (havoid : ∀ u, 0 ≤ u → negInv (η u) ∉ S) :
    IsReverseVisitOrderOff S (cfArcR R L r) fun t => η '' Icc 0 t := by
  obtain ⟨-, hv, huv, -⟩ := h.changeCorner_props
  have hu0 := h.rightLo_pos h0
  have hdR : ∀ s ∈ Icc (0 : ℝ) 1, rightLo R L r + s * (rightHi R L r - rightLo R L r) ∈ Ioc (0 : ℝ) 1 :=
    fun s hs => ⟨hu0.trans_le ((PocketCoord.IsChangeConfigInc.affine_mem huv).1 hs).1,
      ((PocketCoord.IsChangeConfigInc.affine_mem huv).1 hs).2.trans hv.2⟩
  intro t v₁ hv₁ v₂ hv₂ h12 hvis hS
  have hle : rightLo R L r + v₁ * (rightHi R L r - rightLo R L r) ≤
      rightLo R L r + v₂ * (rightHi R L r - rightLo R L r) := by
    have := mul_le_mul_of_nonneg_right h12 (sub_nonneg.2 huv.le)
    linarith
  exact wall_revOff h.right hM (contactMono_right h.right hM hord) hout hη0 hrevM havoid (hdR v₁ hv₁)
    (hdR v₂ hv₂) hle hvis hS

/-- **An outer left wall is visited in reverse order off its forbidden side** (bounded pocket). -/
theorem cfArcL_revOff (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hM : IsSimpleProper M) (hord : Disjoint (range L) (rightSideOf (range M))) (hout : range L ⊆ S ∪ range M)
    (hη0 : η 0 = 0) (hrevM : IsWallReverseVisit M η) (havoid : ∀ u, 0 ≤ u → negInv (η u) ∉ S) :
    IsReverseVisitOrderOff S (cfArcL R L r) fun t => η '' Icc 0 t := by
  obtain ⟨-, -, -, -, hb, hab, -⟩ := h.changeCorner_props
  have ha0 := h.leftLo_pos h0
  have hdL : ∀ s ∈ Icc (0 : ℝ) 1, leftLo R L r + s * (leftHi R L r - leftLo R L r) ∈ Ioc (0 : ℝ) 1 :=
    fun s hs => ⟨ha0.trans_le ((PocketCoord.IsChangeConfigInc.affine_mem hab).1 hs).1,
      ((PocketCoord.IsChangeConfigInc.affine_mem hab).1 hs).2.trans hb.2⟩
  intro t v₁ hv₁ v₂ hv₂ h12 hvis hS
  have hle : leftLo R L r + v₁ * (leftHi R L r - leftLo R L r) ≤ leftLo R L r + v₂ * (leftHi R L r - leftLo R L r) := by
    have := mul_le_mul_of_nonneg_right h12 (sub_nonneg.2 hab.le)
    linarith
  exact wall_revOff h.left hM (contactMono_left h.left hM hord) hout hη0 hrevM havoid (hdL v₁ hv₁)
    (hdL v₂ hv₂) hle hvis hS

/-- **An outer right wall is visited in reverse order off its forbidden side** (pocket opening at the flow seed). -/
theorem cfArcRInf_revOff (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0) (hM : IsSimpleProper M)
    (hord : Disjoint (range M) (rightSideOf (range R))) (hout : range R ⊆ S ∪ range M) (hη0 : η 0 = 0)
    (hrevM : IsWallReverseVisit M η) (havoid : ∀ u, 0 ≤ u → negInv (η u) ∉ S) :
    IsReverseVisitOrderInfOff S (cfArcRInf R L r) fun t => η '' Icc 0 t := by
  obtain ⟨-, hv, huv, -⟩ := h.changeCorner_props
  have hu0 : 0 < rightHi R L r := h0 ▸ huv
  have hdR : ∀ v ∈ Ici (0 : ℝ), rightHi R L r / (1 + v) ∈ Ioc (0 : ℝ) 1 := fun v hv' =>
    ⟨(div_one_add_mem hu0 hv').1, (div_one_add_mem hu0 hv').2.trans hv.2⟩
  intro t v₁ hv₁ v₂ hv₂ h12 hvis hS
  have h1 : (0 : ℝ) < 1 + v₁ := by linarith [mem_Ici.1 hv₁]
  exact wall_revOff h.right hM (contactMono_right h.right hM hord) hout hη0 hrevM havoid (hdR v₂ hv₂)
    (hdR v₁ hv₁) (div_le_div_of_nonneg_left hu0.le h1 (by linarith)) hvis hS

/-- **An outer left wall is visited in reverse order off its forbidden side** (pocket opening at the flow seed). -/
theorem cfArcLInf_revOff (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0) (hM : IsSimpleProper M)
    (hord : Disjoint (range L) (rightSideOf (range M))) (hout : range L ⊆ S ∪ range M) (hη0 : η 0 = 0)
    (hrevM : IsWallReverseVisit M η) (havoid : ∀ u, 0 ≤ u → negInv (η u) ∉ S) :
    IsReverseVisitOrderInfOff S (cfArcLInf R L r) fun t => η '' Icc 0 t := by
  obtain ⟨-, -, -, -, hb, hab, -⟩ := h.changeCorner_props
  have ha0 := h.leftLo_eq_zero_of_rightLo_eq_zero h0
  have hb0 : 0 < leftHi R L r := ha0 ▸ hab
  have hdL : ∀ v ∈ Ici (0 : ℝ), leftHi R L r / (1 + v) ∈ Ioc (0 : ℝ) 1 := fun v hv' =>
    ⟨(div_one_add_mem hb0 hv').1, (div_one_add_mem hb0 hv').2.trans hb.2⟩
  intro t v₁ hv₁ v₂ hv₂ h12 hvis hS
  have h1 : (0 : ℝ) < 1 + v₁ := by linarith [mem_Ici.1 hv₁]
  exact wall_revOff h.left hM (contactMono_left h.left hM hord) hout hη0 hrevM havoid (hdL v₂ hv₂)
    (hdL v₁ hv₁) (div_le_div_of_nonneg_left hb0.le h1 (by linarith)) hvis hS

end InteractingSLE.Sec7.WallOrd
