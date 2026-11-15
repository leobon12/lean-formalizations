/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1CommonRect
import InteractingSLE.Spec.ZhanGT4.DualA15CofinalFamily

/-!
# Zhan's A.1: the cofinal enclosure family as a protected family, and its exhaustion

Packet PROVE-A1-COMMON. Source: Astra, *Follow-up proofs*, §A.1.5 (`ig1_followup_proofs.txt` L409–L425, R38):
"Enumerate a countable cofinal family of separated polygonal enclosure pairs … Any pair of disjoint compact
prefixes is contained in a member of the countable enclosure family".

A15F's countable family (`goodSeq x₂ pm`, `cofH₁`, `cofH₂`, `cofδ`, `cofq`, `cofd`, caps, `cofTm`;
`DualA15CofinalFamily`)
for the source `x₂ = p` of the large curve and the ordinary marks `pm`:

* **`isEnclFamily_cof`**: it is a protected enclosure family (`A1Common.IsEnclFamily`), so `eight_rect` /
  `g3_rect` apply
  to its lifetime-capped exits;
* **`exists_rect_le`** (exhaustion, for (I2)): whenever the two curves' prefixes at times `s < ζ₁`, `t < ζ₂` (the large
  curve shifted to `p`) are disjoint and avoid the marks, some member's exits satisfy `s ≤ S₁ m`, `t ≤ S₂ m`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Common

open QuantumZipper (H fwdHull)
open A1EightSeed A1SeedField

variable {nm : ℕ} {x₂ : ℝ} {pm : Fin nm → ℝ}

/-- A good enclosure pair is a protected pair (A1-SEEDFIELD's `IsProtectedPair`). -/
theorem GoodEncl.isProtectedPair {i : CofIdx} (h : GoodEncl x₂ pm i) :
    IsProtectedPair i.encl₁ (i.encl₂ x₂) i.sep x₂ i.prot i.rad where
  hull₁ := h.isHPHull₁
  hull₂ := h.isHPHull₂
  sep_pos := h.sep_pos
  sep := h.sep
  src := h.mem_closure_encl₂
  prot_pos := h.prot_pos
  prot_lt := h.prot_lt
  rad_pos := h.rad_pos
  prot := h.protH

/-- The large enclosure of a good pair, translated back to the large curve's own frame, is the filling of its squares;
it is an `ℍ`-hull. -/
theorem GoodEncl.isHPHull_transl {i : CofIdx} (h : GoodEncl x₂ pm i) : IsHPHull (transl (-x₂) (i.encl₂ x₂)) := by
  have e : transl (-x₂) (i.encl₂ x₂) = fillH (sqUnion i.1 i.2.2.1) := by
    rw [CofIdx.encl₂, fillH_image_add, transl, image_image]
    simp
  rw [e]
  refine isHPHull_fillH_of_isPreconnected (isCompact_sqUnion _ _).isBounded ?_
  have hc := h.conn₂.image (fun z : ℂ => z + ((-x₂ : ℝ) : ℂ)) (continuous_id.add continuous_const).continuousOn
  rw [image_union, image_image, image_add_lowerHalf] at hc
  simpa [Restart.lowerHalf] using hc

/-- **The cofinal family is a protected enclosure family** for the source `x₂ > 0` (nonempty family). -/
theorem isEnclFamily_cof (hne : (goodIdx x₂ pm).Nonempty) :
    IsEnclFamily (cofH₁ x₂ pm) (cofH₂ x₂ pm) (cofδ x₂ pm) (cofq x₂ pm) (cofd x₂ pm) x₂
      (fun m => (goodSeq x₂ pm m).cap) (cofTm x₂ pm) where
  pp m := GoodEncl.isProtectedPair (goodSeq_good hne m)
  N_pos m := (goodSeq_good hne m).cap_pos
  N_le _ := cap_le_cofTm le_rfl
  nbhd₁ m := (goodSeq_good hne m).nbhd₁
  nbhd₂ m := (goodSeq_good hne m).nbhd₂
  hull₂ m := GoodEncl.isHPHull_transl (goodSeq_good hne m)

/-- The hull of a path's driver before its lifetime is an `ℍ`-hull. -/
theorem isHPHull_fwdHull_extPath {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) < ζ) : IsHPHull (fwdHull (Strip.extPath w) s) := by
  obtain ⟨r, hsr, -, hcr⟩ := exists_real_btwn_continuousOn hwc hs
  have hr0 : 0 ≤ r := s.coe_nonneg.trans hsr.le
  rw [LocalExt.fwdHull_congr_of_eqOn_of_lt s.coe_nonneg hsr fun u hu => (A1Ref.stopDrv_eqOn _ r hu).symm]
  exact isHPHull_fwdHull (A1Ref.continuous_stopDrv hcr hr0) s.coe_nonneg

/-- **Exhaustion by the cofinal family.** If at times `s < ζ₁` and `t < ζ₂` the prefixes `closure K₁(s) ∪ {0}` of the
small curve and `closure K₂(t) ∪ {x₂}` of the large curve shifted to `x₂` are disjoint and avoid the marks, then some
member `m` of the cofinal family has `s ≤ S₁ m` and `t ≤ S₂ m` for the lifetime-capped exits. -/
theorem exists_rect_le (hx₂ : 0 < x₂) {w₁ w₂ : ℝ≥0 → ℝ} {ζ₁ ζ₂ : ℝ≥0∞}
    (hw₁ : ContinuousOn w₁ {t | (t : ℝ≥0∞) < ζ₁}) (hw₂ : ContinuousOn w₂ {t | (t : ℝ≥0∞) < ζ₂}) {s t : ℝ≥0}
    (hs : (s : ℝ≥0∞) < ζ₁) (ht : (t : ℝ≥0∞) < ζ₂)
    (hdisj : Disjoint (closure (fwdHull (Strip.extPath w₁) s) ∪ {0})
      (closure (fwdHull (Strip.extPath fun u => w₂ u + x₂) t) ∪ {(x₂ : ℂ)}))
    (hp : ∀ j, (pm j : ℂ) ∉ (closure (fwdHull (Strip.extPath w₁) s) ∪ {0}) ∪
      (closure (fwdHull (Strip.extPath fun u => w₂ u + x₂) t) ∪ {(x₂ : ℂ)})) :
    ∃ m : ℕ, s ≤ lifeExit w₁ ζ₁ (cofH₁ x₂ pm m) (goodSeq x₂ pm m).cap ∧
      t ≤ lifeExit (fun u => w₂ u + x₂) ζ₂ (cofH₂ x₂ pm m) (goodSeq x₂ pm m).cap := by
  set N : ℕ := ⌈max (s : ℝ) t⌉₊ + 1 with hN
  have hNpos : 0 < N := Nat.succ_pos _
  have hceil : max (s : ℝ) (t : ℝ) ≤ (N : ℝ) := by
    rw [hN]; push_cast; linarith [Nat.le_ceil (max (s : ℝ) (t : ℝ))]
  have hsN : (s : ℝ) ≤ N := (le_max_left _ _).trans hceil
  have htN : (t : ℝ) ≤ N := (le_max_right _ _).trans hceil
  have hw₂' : ContinuousOn (fun u => w₂ u + x₂) {u | (u : ℝ≥0∞) < ζ₂} := hw₂.add continuousOn_const
  obtain ⟨i, hi, hcap, h₁, h₂⟩ := exists_goodEncl_prefix hx₂ (isHPHull_fwdHull_extPath hw₁ hs)
    (isHPHull_fwdHull_extPath hw₂' ht) hdisj hp N hNpos
  have hmem : i ∈ range (goodSeq x₂ pm) := by rw [range_goodSeq ⟨i, hi⟩]; exact hi
  obtain ⟨m, rfl⟩ := hmem
  refine ⟨m, le_lifeExit ?_ fun u hu => ⟨lt_trans (ENNReal.coe_lt_coe.2 hu) hs, ?_⟩,
    le_lifeExit ?_ fun u hu => ⟨lt_trans (ENNReal.coe_lt_coe.2 hu) ht, ?_⟩⟩
  · rw [hcap, ← NNReal.coe_le_coe]; simpa using hsN
  · exact ((QuantumZipper.fwdHull_mono).1 (NNReal.coe_le_coe.2 hu.le)).trans h₁
  · rw [hcap, ← NNReal.coe_le_coe]; simpa using htN
  · exact ((QuantumZipper.fwdHull_mono).1 (NNReal.coe_le_coe.2 hu.le)).trans h₂

end InteractingSLE.ZhanGT4.A1Common
