import QuantumZipper.Proofs.Zipper.LocLenBridge
import QuantumZipper.Proofs.Zipper.F1ReadMeasVague
import QuantumZipper.Proofs.Zipper.E1Glue

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75), task R2a (tool): a measurable reader of open-arc lengths

`arcRd γ x b c := ⨆ n, vagueRd γ x (b + δₙ) (c − δₙ)` with `δₙ = (c − b)/(n + 3)` (and `0` if
`c ≤ b`), where `F1.vagueRd` is the certificate-free measurable reader of the mass of a closed
interval (F1ReadMeasVague.lean).

* `measurable_arcRd`: `(x, b, c) ↦ arcRd γ x b c` is measurable, with no certificate on `x`;
* `arcRd_eq_arcLen`: whenever the dyadic approximations of `x` have a local vague limit on an
  open `U ⊇ (b, c)`, `arcRd γ x b c = arcLen γ x b c` (the open arc is the increasing union of
  the closed intervals `[b + δₙ, c − δₙ]`, continuity from below).

This is the open-arc analogue of the reader used for `B5.LocLengthsMeasStmt`
(`F1.locLengthsMeasStmt_holds`). Own elementary argument (continuity of measure from below).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace LocLen

/-- The shrinking margin `δₙ = (c − b)/(n + 3)`. -/
def arcMargin (b c : ℝ) (n : ℕ) : ℝ := (c - b) / ((n : ℝ) + 3)

open Classical in
/-- **Measurable reader of the open-arc length** of `(b, c)`. -/
def arcRd (γ : ℝ) (x : FieldSample) (b c : ℝ) : ℝ≥0∞ :=
  if b < c then ⨆ n : ℕ, F1.vagueRd γ x (b + arcMargin b c n) (c - arcMargin b c n) else 0

/-- Measurability of the open-arc reader along measurable data. -/
theorem measurable_arcRd_comp (γ : ℝ) {α : Type*} [MeasurableSpace α] {X : α → FieldSample}
    {b c : α → ℝ} (hX : Measurable X) (hb : Measurable b) (hc : Measurable c) :
    Measurable fun a => arcRd γ (X a) (b a) (c a) := by
  classical
  have hv := F1.measurable_vagueRd γ
  have hsup : Measurable fun a => ⨆ n : ℕ,
      F1.vagueRd γ (X a) (b a + arcMargin (b a) (c a) n) (c a - arcMargin (b a) (c a) n) := by
    refine Measurable.iSup fun n => ?_
    have hm : Measurable fun a => arcMargin (b a) (c a) n := by
      unfold arcMargin; exact (hc.sub hb).div_const _
    have hg : Measurable fun a =>
        (X a, b a + arcMargin (b a) (c a) n, c a - arcMargin (b a) (c a) n) :=
      hX.prodMk ((hb.add hm).prodMk (hc.sub hm))
    exact Measurable.comp (g := fun q : FieldSample × ℝ × ℝ => F1.vagueRd γ q.1 q.2.1 q.2.2)
      (f := fun a => (X a, b a + arcMargin (b a) (c a) n, c a - arcMargin (b a) (c a) n)) hv hg
  have hS : MeasurableSet {a | b a < c a} := measurableSet_lt hb hc
  have e : (fun a => arcRd γ (X a) (b a) (c a)) = {a | b a < c a}.piecewise
      (fun a => ⨆ n : ℕ, F1.vagueRd γ (X a) (b a + arcMargin (b a) (c a) n)
        (c a - arcMargin (b a) (c a) n)) (fun _ => 0) := by
    funext a
    by_cases h : b a < c a
    · rw [Set.piecewise_eq_of_mem {a | b a < c a} _ _ (show a ∈ {a | b a < c a} from h)]
      unfold arcRd; exact if_pos h
    · rw [Set.piecewise_eq_of_notMem {a | b a < c a} _ _ (show a ∉ {a | b a < c a} from h)]
      unfold arcRd; exact if_neg h
  rw [e]
  exact hsup.piecewise hS measurable_const

theorem arcMargin_pos {b c : ℝ} (h : b < c) (n : ℕ) : 0 < arcMargin b c n :=
  div_pos (sub_pos.2 h) (by positivity)

theorem Icc_arcMargin_subset {b c : ℝ} (h : b < c) (n : ℕ) :
    Icc (b + arcMargin b c n) (c - arcMargin b c n) ⊆ Ioo b c := by
  intro y hy
  have hp := arcMargin_pos h n
  exact ⟨by linarith [hy.1], by linarith [hy.2]⟩

theorem arcMargin_anti {b c : ℝ} (h : b < c) : Antitone (arcMargin b c) := by
  intro n m hnm
  unfold arcMargin
  have hn : (n : ℝ) ≤ m := by exact_mod_cast hnm
  exact div_le_div_of_nonneg_left (sub_pos.2 h).le (by positivity) (by linarith)

theorem iUnion_Icc_arcMargin {b c : ℝ} (h : b < c) :
    (⋃ n : ℕ, Icc (b + arcMargin b c n) (c - arcMargin b c n)) = Ioo b c := by
  refine subset_antisymm (iUnion_subset (Icc_arcMargin_subset h)) fun y hy => ?_
  have hd : 0 < min (y - b) (c - y) := lt_min (sub_pos.2 hy.1) (sub_pos.2 hy.2)
  have ht : Tendsto (fun n : ℕ => arcMargin b c n) atTop (𝓝 0) := by
    unfold arcMargin
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 3) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simpa using h1.const_div_atTop (c - b)
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hd)).exists
  exact mem_iUnion.2 ⟨n, by linarith [min_le_left (y - b) (c - y)],
    by linarith [min_le_right (y - b) (c - y)]⟩

/-- **The reader computes the open-arc length** whenever a local vague limit exists on an open
set containing the arc. -/
theorem arcRd_eq_arcLen {γ : ℝ} {x : FieldSample} {U : Set ℝ} (hU : IsOpen U) {ν : Measure ℝ}
    (hν : IsVagueLimitOnR U (bdryApprox γ x) ν) {b c : ℝ} (hbc : Ioo b c ⊆ U) :
    arcRd γ x b c = arcLen γ x b c := by
  unfold arcRd
  split_ifs with h
  · rw [arcLen_eq_of_isVagueLimitOnR hν hbc, ← iUnion_Icc_arcMargin h]
    have hmono : Monotone fun n : ℕ => Icc (b + arcMargin b c n) (c - arcMargin b c n) :=
      fun n m hnm => Icc_subset_Icc (by linarith [arcMargin_anti h hnm])
        (by linarith [arcMargin_anti h hnm])
    rw [hmono.measure_iUnion]
    refine iSup_congr fun n => ?_
    exact F1.vagueRd_eq hU hν ((Icc_arcMargin_subset h n).trans hbc)
  · have : Ioo b c = ∅ := Ioo_eq_empty h
    unfold arcLen
    rw [this, measure_empty]

end LocLen
end QuantumZipper
