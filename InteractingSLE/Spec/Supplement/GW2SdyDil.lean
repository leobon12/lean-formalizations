/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SfWord
import InteractingSLE.Spec.Supplement.GW2SdfFrame
import InteractingSLE.Spec.Restart.FCKerDReflWord
import InteractingSLE.Spec.Restart.FlowCodeWord

/-!
# Dilated and raised stage words (the word algebra of the near words)

Packet PROVE-GW2-SDE (round 11). Ruling R112 dilates the near comparisons per history by the near scale `s`
(space factor `(√s)⁻¹`), and the stage word of a candidate at angle `θ` is the raised word `upW (θχ) c`
(STAGEMEAN's word map `β y = upW e (stageWord …)`). ROOT2's crossing families are built from the literal flow-line
word of a DILATED word. This file proves that such a family presents the raised stage word:

* `dilW a c` (positions times `a`, heights kept), `index_dilW`, `indexLE_dilW`, `fn_dilW`, `jumps_dilW`,
  `leftLim_dilW`, `rightLim_dilW`, **`jumpSet_dilW`**;
* **`isFlowType_of_dilW`**: a flow-line typing of `dilW a c` at angle `θ` is a typing of `c` with positions times
  `a⁻¹` (`0 < a`);
* **`isFlowType_upW_of`** (the converse of `GW2Sf.isFlowType_of_upW`): a typing at angle `θ` is a typing of the
  raised word at angle `0`;
* **`presentsO_of_isFlowType_dilW`** (even histories) and **`presentsO_true_of_isFlowType_dilW`** (odd histories,
  through the sorted mirror word): the flow-line word of the dilated (mirrored) word at angle `θ` PRESENTS the raised
  stage word `upW (±θχ) c` at the near scale `s`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter
open scoped NNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW2Sdy

open Restart
open PiecewiseConstantBoundaryData (jumpSet leftLim rightLim)

/-- **The dilated word**: positions times `a`, heights kept. -/
def dilW (a : ℝ) (c : BoundaryWord) : BoundaryWord := (c.1, fun i => a * c.2.1 i, c.2.2)

section Dil

variable {a : ℝ}

theorem index_dilW (ha : 0 < a) (c : BoundaryWord) (y : ℝ) : (dilW a c).index y = c.index (y / a) := by
  simp only [BoundaryWord.index, dilW]
  congr 1
  exact Finset.filter_congr fun i _ => by rw [lt_div_iff₀ ha, mul_comm]

theorem indexLE_dilW (ha : 0 < a) (c : BoundaryWord) (y : ℝ) :
    (dilW a c).indexLE y = c.indexLE (y / a) := by
  simp only [BoundaryWord.indexLE, dilW]
  congr 1
  exact Finset.filter_congr fun i _ => by rw [le_div_iff₀ ha, mul_comm]

theorem fn_dilW (ha : 0 < a) (c : BoundaryWord) : (dilW a c).fn = fun y => c.fn (y / a) := by
  funext y
  simp only [BoundaryWord.fn]
  rw [index_dilW ha]
  rfl

theorem jumps_dilW (c : BoundaryWord) : (dilW a c).jumps = c.jumps.image (a * ·) := by
  simp only [BoundaryWord.jumps, dilW, Finset.image_image]
  rfl

theorem leftLim_dilW (ha : 0 < a) (c : BoundaryWord) :
    leftLim (dilW a c).fn = fun y => leftLim c.fn (y / a) := by
  funext y
  rw [BoundaryWord.leftLim_fn, BoundaryWord.leftLim_fn, index_dilW ha]
  rfl

theorem rightLim_dilW (ha : 0 < a) (c : BoundaryWord) :
    rightLim (dilW a c).fn = fun y => rightLim c.fn (y / a) := by
  funext y
  rw [BoundaryWord.rightLim_fn, BoundaryWord.rightLim_fn, indexLE_dilW ha]
  rfl

/-- **The jump set of the dilated word** is the dilated jump set. -/
theorem jumpSet_dilW (ha : 0 < a) (c : BoundaryWord) :
    jumpSet (dilW a c).fn (dilW a c).jumps = (jumpSet c.fn c.jumps).image (a * ·) := by
  unfold PiecewiseConstantBoundaryData.jumpSet
  rw [jumps_dilW, Finset.filter_image]
  congr 1
  refine Finset.filter_congr fun z _ => ?_
  rw [leftLim_dilW ha, rightLim_dilW ha]
  simp only [mul_div_cancel_left₀ _ ha.ne']

theorem filter_lt_image_mul (ha : 0 < a) (S : Finset ℝ) :
    (S.image (a * ·)).filter (· < 0) = (S.filter (· < 0)).image (a * ·) := by
  rw [Finset.filter_image]
  congr 1
  exact Finset.filter_congr fun z _ => ⟨fun h => by nlinarith, fun h => by nlinarith⟩

theorem filter_gt_image_mul (ha : 0 < a) (S : Finset ℝ) :
    (S.image (a * ·)).filter (0 < ·) = (S.filter (0 < ·)).image (a * ·) := by
  rw [Finset.filter_image]
  congr 1
  exact Finset.filter_congr fun z _ => ⟨fun h => by nlinarith, fun h => by nlinarith⟩

theorem card_filter_lt_image_mul (ha : 0 < a) (S : Finset ℝ) :
    ((S.image (a * ·)).filter (· < 0)).card = (S.filter (· < 0)).card := by
  rw [filter_lt_image_mul ha, Finset.card_image_of_injective _ (mul_right_injective₀ ha.ne')]

theorem card_filter_gt_image_mul (ha : 0 < a) (S : Finset ℝ) :
    ((S.image (a * ·)).filter (0 < ·)).card = (S.filter (0 < ·)).card := by
  rw [filter_gt_image_mul ha, Finset.card_image_of_injective _ (mul_right_injective₀ ha.ne')]

theorem orderEmbOfFin_filter_lt_image_mul (ha : 0 < a) (S : Finset ℝ)
    (i : Fin ((S.image (a * ·)).filter (· < 0)).card) :
    ((S.image (a * ·)).filter (· < 0)).orderEmbOfFin rfl i =
      a * (S.filter (· < 0)).orderEmbOfFin rfl (Fin.cast (card_filter_lt_image_mul ha S) i) := by
  have hu := Finset.orderEmbOfFin_unique (s := (S.image (a * ·)).filter (· < 0)) rfl
    (f := fun i => a * (S.filter (· < 0)).orderEmbOfFin rfl (Fin.cast (card_filter_lt_image_mul ha S) i))
    (fun i => by
      have hm := Finset.orderEmbOfFin_mem (S.filter (· < 0)) rfl (Fin.cast (card_filter_lt_image_mul ha S) i)
      rw [Finset.mem_filter] at hm ⊢
      exact ⟨Finset.mem_image_of_mem _ hm.1, mul_neg_of_pos_of_neg ha hm.2⟩)
    (fun i j hij => mul_lt_mul_of_pos_left (((S.filter (· < 0)).orderEmbOfFin rfl).strictMono
      (show Fin.cast (card_filter_lt_image_mul ha S) i < Fin.cast (card_filter_lt_image_mul ha S) j from hij)) ha)
  exact (congrFun hu i).symm

theorem orderEmbOfFin_filter_gt_image_mul (ha : 0 < a) (S : Finset ℝ)
    (i : Fin ((S.image (a * ·)).filter (0 < ·)).card) :
    ((S.image (a * ·)).filter (0 < ·)).orderEmbOfFin rfl i =
      a * (S.filter (0 < ·)).orderEmbOfFin rfl (Fin.cast (card_filter_gt_image_mul ha S) i) := by
  have hu := Finset.orderEmbOfFin_unique (s := (S.image (a * ·)).filter (0 < ·)) rfl
    (f := fun i => a * (S.filter (0 < ·)).orderEmbOfFin rfl (Fin.cast (card_filter_gt_image_mul ha S) i))
    (fun i => by
      have hm := Finset.orderEmbOfFin_mem (S.filter (0 < ·)) rfl (Fin.cast (card_filter_gt_image_mul ha S) i)
      rw [Finset.mem_filter] at hm ⊢
      exact ⟨Finset.mem_image_of_mem _ hm.1, mul_pos ha hm.2⟩)
    (fun i j hij => mul_lt_mul_of_pos_left (((S.filter (0 < ·)).orderEmbOfFin rfl).strictMono
      (show Fin.cast (card_filter_gt_image_mul ha S) i < Fin.cast (card_filter_gt_image_mul ha S) j from hij)) ha)
  exact (congrFun hu i).symm

end Dil

section Typing

variable {nL nR : ℕ} {κ θ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **A flow-line typing of the dilated word is a typing of the word with positions divided by the factor.** -/
theorem isFlowType_of_dilW {a : ℝ} (ha : 0 < a) {c : BoundaryWord}
    (h : FCDet.IsFlowType κ θ (dilW a c) xL xR ρL ρR) :
    FCDet.IsFlowType κ θ c (fun i => a⁻¹ * xL i) (fun j => a⁻¹ * xR j) ρL ρR := by
  rw [Sec5.CfDown.isFlowType_iff_flowTypeAt, Sec5.CfDown.flowTypeAt_eq_data, jumpSet_dilW ha, leftLim_dilW ha,
    rightLim_dilW ha] at h
  rw [Sec5.CfDown.isFlowType_iff_flowTypeAt, Sec5.CfDown.flowTypeAt_eq_data]
  set S := jumpSet c.fn c.jumps
  obtain ⟨eL, eR, hxL, hxR, hρL, hρR⟩ := h
  have cL := card_filter_lt_image_mul ha S
  have cR := card_filter_gt_image_mul ha S
  have eL' : (S.filter (· < 0)).card + 1 = nL := by rw [← cL]; exact eL
  have eR' : (S.filter (0 < ·)).card + 1 = nR := by rw [← cR]; exact eR
  have fL : (S.filter (· < 0)).card + 1 = ((S.image (a * ·)).filter (· < 0)).card + 1 := by rw [cL]
  have fR : (S.filter (0 < ·)).card + 1 = ((S.image (a * ·)).filter (0 < ·)).card + 1 := by rw [cR]
  have hcL : ∀ i, Fin.cast eL' i = Fin.cast eL (Fin.cast fL i) := fun i => Fin.ext rfl
  have hcR : ∀ j, Fin.cast eR' j = Fin.cast eR (Fin.cast fR j) := fun j => Fin.ext rfl
  refine ⟨eL', eR', ?_, ?_, ?_, ?_⟩
  · funext i
    show a⁻¹ * xL (Fin.cast eL' i) = _
    rw [hcL, congrFun hxL (Fin.cast fL i)]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · rw [Fin.cast_succ_eq, Fin.cons_succ, Fin.cons_succ, orderEmbOfFin_filter_lt_image_mul ha, sub_zero, sub_zero,
        ← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul, Fin.cast_rev, Fin.cast_cast, Fin.cast_eq_self]
  · funext i
    show a⁻¹ * xR (Fin.cast eR' i) = _
    rw [hcR, congrFun hxR (Fin.cast fR i)]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · rw [Fin.cast_succ_eq, Fin.cons_succ, Fin.cons_succ, orderEmbOfFin_filter_gt_image_mul ha, sub_zero, sub_zero,
        ← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul, Fin.cast_cast, Fin.cast_eq_self]
  · funext i
    show ρL (Fin.cast eL' i) = _
    rw [hcL, congrFun hρL (Fin.cast fL i)]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · rw [Fin.cast_succ_eq, Fin.cons_succ, Fin.cons_succ]
      simp only [orderEmbOfFin_filter_lt_image_mul ha, mul_div_cancel_left₀ _ ha.ne', Fin.cast_rev, Fin.cast_cast,
        Fin.cast_eq_self]
  · funext i
    show ρR (Fin.cast eR' i) = _
    rw [hcR, congrFun hρR (Fin.cast fR i)]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · rw [Fin.cast_succ_eq, Fin.cons_succ, Fin.cons_succ]
      simp only [orderEmbOfFin_filter_gt_image_mul ha, mul_div_cancel_left₀ _ ha.ne', Fin.cast_cast,
        Fin.cast_eq_self]

/-- **A typing at angle `θ` is a typing of the raised word at angle `0`** (the converse of
`GW2Sf.isFlowType_of_upW`). -/
theorem isFlowType_upW_of {c : BoundaryWord} (ht : FCDet.IsFlowType κ θ c xL xR ρL ρR) :
    FCDet.IsFlowType κ 0 (GW2Rd.upW (θ * chiC κ) c) xL xR ρL ρR := by
  have hJ := GW2Rd.jumpSet_add_const c.isPiecewiseConstantBoundaryData (θ * chiC κ)
  have hL := GW2Rd.leftLim_add_const c.isPiecewiseConstantBoundaryData (θ * chiC κ)
  have hR := GW2Rd.rightLim_add_const c.isPiecewiseConstantBoundaryData (θ * chiC κ)
  rw [Sec5.CfDown.isFlowType_iff_flowTypeAt, Sec5.CfDown.flowTypeAt_eq_data] at ht ⊢
  change Sec5.CfDown.FlowTypeData κ 0 (jumpSet (fun y => c.fn y + θ * chiC κ) c.jumps)
    (leftLim (fun y => c.fn y + θ * chiC κ)) (rightLim (fun y => c.fn y + θ * chiC κ)) 0 xL xR ρL ρR
  rw [hJ, hL, hR]
  obtain ⟨eL, eR, hxL, hxR, hρL, hρR⟩ := ht
  refine ⟨eL, eR, hxL, hxR, ?_, ?_⟩
  · rw [hρL]
    simp only [zero_mul, add_zero, add_sub_add_right_eq_sub]
  · rw [hρR]
    simp only [zero_mul, add_zero, add_sub_add_right_eq_sub]

end Typing

/-- **The dilated word's flow-line word presents the raised stage word** (even histories): if the family's word is
the angle-`θ` flow-line word of `dilW (√s)⁻¹ c`, it presents `upW (θχ) c` at the near scale `s`. -/
theorem presentsO_of_isFlowType_dilW {κ θ : ℝ} {s : ℝ≥0} (hs : s ≠ 0) {c : BoundaryWord} {nL nR : ℕ}
    {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
    (h : FCDet.IsFlowType κ θ (dilW (Real.sqrt s)⁻¹ c) xL xR ρL ρR) :
    GW2Sdf.PresentsO κ (GW2Rd.upW (θ * chiC κ) c) s false xL ρL xR ρR := by
  have hpos : 0 < (Real.sqrt s)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 (by positivity))
  have h1 := isFlowType_of_dilW hpos h
  simp only [inv_inv] at h1
  exact isFlowType_upW_of h1

/-- **The dilated mirror word's flow-line word presents the raised stage word** (odd histories): if the family's word
is the angle-`θ` flow-line word of `dilW (√s)⁻¹ (sreflWord c)`, it presents `upW (−θχ) c` at the near scale `s`
with the sides exchanged. -/
theorem presentsO_true_of_isFlowType_dilW {κ θ : ℝ} {s : ℝ≥0} (hs : s ≠ 0) {c : BoundaryWord} {nL nR : ℕ}
    {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
    (h : FCDet.IsFlowType κ θ (dilW (Real.sqrt s)⁻¹ (FCPlumb.FCKerD.sreflWord c)) xL xR ρL ρR) :
    GW2Sdf.PresentsO κ (GW2Rd.upW (-θ * chiC κ) c) s true xL ρL xR ρR := by
  have hpos : 0 < (Real.sqrt s)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 (by positivity))
  have h1 := isFlowType_of_dilW hpos h
  simp only [inv_inv] at h1
  rw [← neg_neg θ] at h1
  have h2 := FCPlumb.FCKerD.isFlowType_of_sreflWord h1
  exact isFlowType_upW_of h2

end InteractingSLE.Theorem14.GW2Sdy
