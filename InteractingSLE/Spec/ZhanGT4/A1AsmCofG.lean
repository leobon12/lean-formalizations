/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1AsmEncl
import InteractingSLE.Spec.ZhanGT4.A1CommonStoch

/-!
# Zhan's A.1 (G3): the cofinal family with the segment condition

Packet PROVE-A1-ASSEMBLE. Source: Astra, *Follow-up proofs*, §A.1.3 and §A.1.5 (`ig1_followup_proofs.txt` L300–L304,
L409–L425: "Enumerate a countable cofinal family of separated polygonal enclosure pairs … Any pair of disjoint compact
prefixes is contained in a member of the countable enclosure family"); R38.

The G3 records need A1-G3CALC's `IsProtectedPairG`: the protected point `q` lies right of the ordinary mark `qlo`
(`x − y`), and the real segment `(0, q]` is `2δ`-far from the large enclosure. The good indices with this extra
property (`GoodEnclG`) form a countable family, enumerated as A15F does for `GoodEncl`:

* `GoodEnclG`, `goodIdxG`, **`goodIdxG_nonempty`**, `goodSeqG` (`range_goodSeqG`, `goodSeqG_good`);
* the family `cofGH₁`, `cofGH₂`, `cofGδ`, `cofGq`, `cofGd`, `cofGTm`;
* **`isEnclFamily_cofG`**: it is an `A1Common.IsEnclFamily` (so `A1Common.g3_rect` applies);
* **`isProtectedPairG_cofG`**, `qlo_le_cofGq`: every member is a protected pair in A1-G3CALC's sense with `qlo ≤ q`
  (the hypotheses `hpp`, `hxOq` of `seedFieldInputG_of_g3`);
* **`exists_rect_leG`** (exhaustion): disjoint mark-free prefixes, the large one missing the real segment `[0, qlo]`,
  lie in some member's rectangle.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Asm

open QuantumZipper (H fwdHull)
open A1EightSeed A1SeedField A1G3Calc A1Common

/-! ### The good indices with the segment condition -/

section Enum

variable {nm : ℕ} {x₂ qlo : ℝ} {p : Fin nm → ℝ}

/-- **A good enclosure pair with the segment condition**: a `GoodEncl` pair whose protected point is `≥ qlo` and whose
large enclosure is `2δ`-far from the real segment `[0, q]`. -/
structure GoodEnclG (x₂ qlo : ℝ) (p : Fin nm → ℝ) (i : CofIdx) : Prop where
  good : GoodEncl x₂ p i
  lo : qlo ≤ i.prot
  seg : ∀ a ∈ i.encl₂ x₂, ∀ y : ℝ, 0 ≤ y → y ≤ i.prot → 2 * i.sep ≤ ‖a - y‖

/-- The good indices with the segment condition. -/
def goodIdxG (x₂ qlo : ℝ) (p : Fin nm → ℝ) : Set CofIdx := {i | GoodEnclG x₂ qlo p i}

/-- **The family is nonempty** when `0 < qlo < x₂` and the marks avoid the two sources. -/
theorem goodIdxG_nonempty (hqlo : 0 < qlo) (hqlox : qlo < x₂) (hp0 : ∀ m, p m ≠ 0) (hpx : ∀ m, p m ≠ x₂) :
    (goodIdxG x₂ qlo p).Nonempty := by
  have hx₂ : 0 < x₂ := hqlo.trans hqlox
  obtain ⟨i, hi, -, -, -, hlo, hseg⟩ := exists_goodEncl_seg_prefix (p := p) isHPHull_empty isHPHull_empty
    (by
      rw [closure_empty, empty_union, empty_union, disjoint_singleton]
      intro h
      have := congrArg Complex.re h
      simp only [Complex.zero_re, Complex.ofReal_re] at this
      linarith)
    (fun m h => by
      simp only [closure_empty, empty_union, mem_union, mem_singleton_iff] at h
      rcases h with h | h
      · exact hp0 m (by exact_mod_cast h)
      · exact hpx m (by exact_mod_cast h)) hqlo hqlox
    (fun t ht h => by
      simp only [closure_empty, empty_union, mem_singleton_iff] at h
      have := congrArg Complex.re h
      simp only [Complex.ofReal_re] at this
      linarith [ht.2])
    (fun h => by
      simp only [closure_empty, empty_union, mem_singleton_iff] at h
      have := congrArg Complex.re h
      simp only [Complex.ofReal_re, Complex.zero_re] at this
      linarith) 1 one_pos
  exact ⟨i, hi, hlo, hseg⟩

open Classical in
/-- An enumeration of the good indices with the segment condition (a constant default if there are none). -/
def goodSeqG (x₂ qlo : ℝ) (p : Fin nm → ℝ) : ℕ → CofIdx :=
  if h : (goodIdxG x₂ qlo p).Nonempty then
    Classical.choose ((Set.to_countable (goodIdxG x₂ qlo p)).exists_eq_range h)
  else fun _ => default

theorem range_goodSeqG (h : (goodIdxG x₂ qlo p).Nonempty) : range (goodSeqG x₂ qlo p) = goodIdxG x₂ qlo p := by
  unfold goodSeqG
  simp only [h, ↓reduceDIte]
  exact (Classical.choose_spec ((Set.to_countable (goodIdxG x₂ qlo p)).exists_eq_range h)).symm

theorem goodSeqG_good (h : (goodIdxG x₂ qlo p).Nonempty) (k : ℕ) : GoodEnclG x₂ qlo p (goodSeqG x₂ qlo p k) := by
  have : goodSeqG x₂ qlo p k ∈ goodIdxG x₂ qlo p := by rw [← range_goodSeqG h]; exact ⟨k, rfl⟩
  exact this

end Enum

/-! ### The family -/

section Family

variable {nm : ℕ} {x₂ qlo : ℝ} {p : Fin nm → ℝ}

/-- The small enclosure of member `k`. -/
def cofGH₁ (x₂ qlo : ℝ) (p : Fin nm → ℝ) (k : ℕ) : Set ℂ := (goodSeqG x₂ qlo p k).encl₁

/-- The large enclosure of member `k`. -/
def cofGH₂ (x₂ qlo : ℝ) (p : Fin nm → ℝ) (k : ℕ) : Set ℂ := (goodSeqG x₂ qlo p k).encl₂ x₂

/-- The separation of member `k`. -/
def cofGδ (x₂ qlo : ℝ) (p : Fin nm → ℝ) (k : ℕ) : ℝ := (goodSeqG x₂ qlo p k).sep

/-- The protected point of member `k`. -/
def cofGq (x₂ qlo : ℝ) (p : Fin nm → ℝ) (k : ℕ) : ℝ := (goodSeqG x₂ qlo p k).prot

/-- The protection radius of member `k`. -/
def cofGd (x₂ qlo : ℝ) (p : Fin nm → ℝ) (k : ℕ) : ℝ := (goodSeqG x₂ qlo p k).rad

/-- The cap of member `k`. -/
def cofGN (x₂ qlo : ℝ) (p : Fin nm → ℝ) (k : ℕ) : ℝ≥0 := (goodSeqG x₂ qlo p k).cap

/-- The bound of the first `m + 1` caps. -/
def cofGTm (x₂ qlo : ℝ) (p : Fin nm → ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), ((goodSeqG x₂ qlo p j).cap : ℝ) + 1

theorem cap_le_cofGTm {k m : ℕ} (hkm : k ≤ m) : (cofGN x₂ qlo p k : ℝ) ≤ cofGTm x₂ qlo p m := by
  unfold cofGTm cofGN
  have h := Finset.single_le_sum (f := fun j => ((goodSeqG x₂ qlo p j).cap : ℝ)) (fun j _ => NNReal.coe_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hkm))
  linarith

/-- **The segment family is a protected enclosure family** (`A1Common.IsEnclFamily`) for the source `x₂`. -/
theorem isEnclFamily_cofG (hne : (goodIdxG x₂ qlo p).Nonempty) :
    IsEnclFamily (cofGH₁ x₂ qlo p) (cofGH₂ x₂ qlo p) (cofGδ x₂ qlo p) (cofGq x₂ qlo p) (cofGd x₂ qlo p) x₂
      (cofGN x₂ qlo p) (cofGTm x₂ qlo p) where
  pp m := GoodEncl.isProtectedPair (goodSeqG_good hne m).good
  N_pos m := (goodSeqG_good hne m).good.cap_pos
  N_le _ := cap_le_cofGTm le_rfl
  nbhd₁ m := (goodSeqG_good hne m).good.nbhd₁
  nbhd₂ m := (goodSeqG_good hne m).good.nbhd₂
  hull₂ m := GoodEncl.isHPHull_transl (goodSeqG_good hne m).good

/-- **Every member is a protected pair in A1-G3CALC's sense** (`IsProtectedPairG`: the segment `(0, q]` is `2δ`-far
from the large enclosure). -/
theorem isProtectedPairG_cofG (hne : (goodIdxG x₂ qlo p).Nonempty) (m : ℕ) :
    IsProtectedPairG (cofGH₁ x₂ qlo p m) (cofGH₂ x₂ qlo p m) (cofGδ x₂ qlo p m) x₂ (cofGq x₂ qlo p m)
      (cofGd x₂ qlo p m) where
  pair := GoodEncl.isProtectedPair (goodSeqG_good hne m).good
  seg a ha y hy hyq := (goodSeqG_good hne m).seg a ha y hy.le hyq

/-- The protected points of the members are right of `qlo` (`hxOq` of `seedFieldInputG_of_g3`). -/
theorem qlo_le_cofGq (hne : (goodIdxG x₂ qlo p).Nonempty) (m : ℕ) : qlo ≤ cofGq x₂ qlo p m :=
  (goodSeqG_good hne m).lo

/-- **Exhaustion by the segment family.** If at times `s < ζ₁` and `t < ζ₂` the prefixes `closure K₁(s) ∪ {0}` of the
small curve and `closure K₂(t) ∪ {x₂}` of the large curve shifted to `x₂` are disjoint and avoid the marks, the first
avoids `qlo` and the second misses the real segment `[0, qlo]`, then some member `m` of the segment family has
`s ≤ S₁ m` and `t ≤ S₂ m` for the lifetime-capped exits. -/
theorem exists_rect_leG (hqlo : 0 < qlo) (hqlox : qlo < x₂) {w₁ w₂ : ℝ≥0 → ℝ} {ζ₁ ζ₂ : ℝ≥0∞}
    (hw₁ : ContinuousOn w₁ {t | (t : ℝ≥0∞) < ζ₁}) (hw₂ : ContinuousOn w₂ {t | (t : ℝ≥0∞) < ζ₂}) {s t : ℝ≥0}
    (hs : (s : ℝ≥0∞) < ζ₁) (ht : (t : ℝ≥0∞) < ζ₂)
    (hdisj : Disjoint (closure (fwdHull (Strip.extPath w₁) s) ∪ {0})
      (closure (fwdHull (Strip.extPath fun u => w₂ u + x₂) t) ∪ {(x₂ : ℂ)}))
    (hp : ∀ j, (p j : ℂ) ∉ (closure (fwdHull (Strip.extPath w₁) s) ∪ {0}) ∪
      (closure (fwdHull (Strip.extPath fun u => w₂ u + x₂) t) ∪ {(x₂ : ℂ)}))
    (hseg : ∀ r ∈ Icc (0 : ℝ) qlo, (r : ℂ) ∉ closure (fwdHull (Strip.extPath fun u => w₂ u + x₂) t) ∪ {(x₂ : ℂ)})
    (hq₁ : (qlo : ℂ) ∉ closure (fwdHull (Strip.extPath w₁) s) ∪ {0}) :
    ∃ m : ℕ, s ≤ lifeExit w₁ ζ₁ (cofGH₁ x₂ qlo p m) (cofGN x₂ qlo p m) ∧
      t ≤ lifeExit (fun u => w₂ u + x₂) ζ₂ (cofGH₂ x₂ qlo p m) (cofGN x₂ qlo p m) := by
  set N : ℕ := ⌈max (s : ℝ) t⌉₊ + 1 with hN
  have hNpos : 0 < N := Nat.succ_pos _
  have hceil : max (s : ℝ) (t : ℝ) ≤ (N : ℝ) := by
    rw [hN]; push_cast; linarith [Nat.le_ceil (max (s : ℝ) (t : ℝ))]
  have hsN : (s : ℝ) ≤ N := (le_max_left _ _).trans hceil
  have htN : (t : ℝ) ≤ N := (le_max_right _ _).trans hceil
  have hw₂' : ContinuousOn (fun u => w₂ u + x₂) {u | (u : ℝ≥0∞) < ζ₂} := hw₂.add continuousOn_const
  obtain ⟨i, hi, hcap, h₁, h₂, hlo, hsg⟩ := exists_goodEncl_seg_prefix (isHPHull_fwdHull_extPath hw₁ hs)
    (isHPHull_fwdHull_extPath hw₂' ht) hdisj hp hqlo hqlox hseg hq₁ N hNpos
  have hmem : i ∈ range (goodSeqG x₂ qlo p) := by
    rw [range_goodSeqG ⟨i, ⟨hi, hlo, hsg⟩⟩]; exact ⟨hi, hlo, hsg⟩
  obtain ⟨m, rfl⟩ := hmem
  refine ⟨m, le_lifeExit ?_ fun u hu => ⟨lt_trans (ENNReal.coe_lt_coe.2 hu) hs, ?_⟩,
    le_lifeExit ?_ fun u hu => ⟨lt_trans (ENNReal.coe_lt_coe.2 hu) ht, ?_⟩⟩
  · rw [cofGN, hcap, ← NNReal.coe_le_coe]; simpa using hsN
  · exact ((QuantumZipper.fwdHull_mono).1 (NNReal.coe_le_coe.2 hu.le)).trans h₁
  · rw [cofGN, hcap, ← NNReal.coe_le_coe]; simpa using htN
  · exact ((QuantumZipper.fwdHull_mono).1 (NNReal.coe_le_coe.2 hu.le)).trans h₂

end Family

end InteractingSLE.ZhanGT4.A1Asm
