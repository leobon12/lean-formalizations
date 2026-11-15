/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1LifeType
import InteractingSLE.Spec.Supplement.GW2JointDetFix
import InteractingSLE.Spec.Sec5.Cond44Ref
import InteractingSLE.Spec.Sec4.Prob41Flow
import InteractingSLE.Spec.Exist.StagedLawData
import InteractingSLE.WangWu.Lemma421Seed
import InteractingSLE.WangWu.Shift.Basic

/-!
# GW2's relative determination: the angle of the explored flow line as a height shift

Packet PROVE-GW2-RELDET. GB6's relative-determination engine (`Supp8.Q3Stop.ae_isStopDrvMatch_of_hasRelSafe`: K2's
inputs (S), (L) under the joint law of a record and a relative variable give the stopped driver match) reads the
explored curve as the angle-`0` flow line of its field, with a canonical driver code at angle `0`. GW2's explored curve
is a flow line at an angle `θ`. A flow line of `h` at angle `θ` with data `b` is the angle-`0` flow line of `h + θχ`
with data `b + θχ` (the coupling field and the force data are unchanged). This file makes that exact:

* `leftLim_add_const`, `rightLim_add_const`, `jumpSet_add_const`: one-sided limits and genuine jumps of `b + a`;
* **`isFlowLineDriver_shift_iff`**: `IsFlowLineDriver κ (b − θχ) J θ P (h − θχ) W ζ ↔ IsFlowLineDriver κ b J 0 P h W ζ`;
* `upW` (the word with all heights raised by `a`), its data, sortedness, measurability, round trip;
* `shiftCode k θ F` (`(c, f) ↦ F (c − θχ, f − θχ)`) and **`isCanonicalDriverCode_shiftCode`**: a canonical driver code
  at angle `θ` gives a canonical driver code at angle `0`; `shiftCode_upW`: on the raised word and field it is `F`;
* `countable_range_wordType_upW_retStop`: the raised GB6/GW2 conditional words have countably many word types.

Deterministic and measure-theoretic bookkeeping only; no named input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Restart Exist.StagedLaw PiecewiseConstantBoundaryData

/-! ### One-sided limits and jumps of shifted data -/

section Limits

variable {b : ℝ → ℝ} {J : Finset ℝ}

/-- Piecewise-constant data equal their left limit on a punctured left neighbourhood. -/
theorem exists_Ioo_eq_leftLim (hb : IsPiecewiseConstantBoundaryData b J) (z : ℝ) :
    ∃ lo < z, ∀ t ∈ Ioo lo z, b t = leftLim b z := by
  set M : Finset ℝ := insert (z - 1) (J.filter (· < z)) with hM
  have hMne : M.Nonempty := Finset.insert_nonempty _ _
  have hmz : M.max' hMne < z := by
    rcases Finset.mem_insert.1 (M.max'_mem hMne) with h' | h'
    · rw [h']; linarith
    · exact (Finset.mem_filter.1 h').2
  have hnoJ : ∀ w ∈ J, w ∉ Ioo (M.max' hMne) z := fun w hwJ hw =>
    absurd (M.le_max' w (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hwJ, hw.2⟩))) (not_le.2 hw.1)
  set m := (M.max' hMne + z) / 2 with hm
  have hmI : m ∈ Ioo (M.max' hMne) z := ⟨by rw [hm]; linarith, by rw [hm]; linarith⟩
  have hconst : ∀ t ∈ Ioo (M.max' hMne) z, b t = b m := fun t ht =>
    Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant hb hnoJ hmI ht
  have hL : leftLim b z = b m := Sec4.leftLim_eq_of_forall hmz hconst
  exact ⟨M.max' hMne, hmz, fun t ht => (hconst t ht).trans hL.symm⟩

/-- Piecewise-constant data equal their right limit on a punctured right neighbourhood. -/
theorem exists_Ioo_eq_rightLim (hb : IsPiecewiseConstantBoundaryData b J) (z : ℝ) :
    ∃ hi, z < hi ∧ ∀ t ∈ Ioo z hi, b t = rightLim b z := by
  set M : Finset ℝ := insert (z + 1) (J.filter (z < ·)) with hM
  have hMne : M.Nonempty := Finset.insert_nonempty _ _
  have hzm : z < M.min' hMne := by
    rcases Finset.mem_insert.1 (M.min'_mem hMne) with h' | h'
    · rw [h']; linarith
    · exact (Finset.mem_filter.1 h').2
  have hnoJ : ∀ w ∈ J, w ∉ Ioo z (M.min' hMne) := fun w hwJ hw =>
    absurd (M.min'_le w (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hwJ, hw.1⟩))) (not_le.2 hw.2)
  set m := (z + M.min' hMne) / 2 with hm
  have hmI : m ∈ Ioo z (M.min' hMne) := ⟨by rw [hm]; linarith, by rw [hm]; linarith⟩
  have hconst : ∀ t ∈ Ioo z (M.min' hMne), b t = b m := fun t ht =>
    Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant hb hnoJ hmI ht
  have hR : rightLim b z = b m := Sec4.rightLim_eq_of_forall hzm hconst
  exact ⟨M.min' hMne, hzm, fun t ht => (hconst t ht).trans hR.symm⟩

theorem leftLim_add_const (hb : IsPiecewiseConstantBoundaryData b J) (a : ℝ) :
    leftLim (fun y => b y + a) = fun z => leftLim b z + a := by
  funext z
  obtain ⟨lo, hlo, hc⟩ := exists_Ioo_eq_leftLim hb z
  exact Sec4.leftLim_eq_of_forall hlo fun t ht => by rw [hc t ht]

theorem rightLim_add_const (hb : IsPiecewiseConstantBoundaryData b J) (a : ℝ) :
    rightLim (fun y => b y + a) = fun z => rightLim b z + a := by
  funext z
  obtain ⟨hi, hhi, hc⟩ := exists_Ioo_eq_rightLim hb z
  exact Sec4.rightLim_eq_of_forall hhi fun t ht => by rw [hc t ht]

theorem jumpSet_add_const (hb : IsPiecewiseConstantBoundaryData b J) (a : ℝ) :
    jumpSet (fun y => b y + a) J = jumpSet b J := by
  unfold jumpSet
  rw [leftLim_add_const hb, rightLim_add_const hb]
  congr 1
  ext y
  simp only [ne_eq, add_left_inj]

theorem isPiecewiseConstant_add_const (hb : IsPiecewiseConstantBoundaryData b J) (a : ℝ) :
    IsPiecewiseConstantBoundaryData (fun y => b y + a) J := fun y hy =>
  (hb y hy).mono fun z hz => by simp only [hz]

end Limits

/-! ### The angle of a flow-line driver as a height shift -/

/-- Adding a constant to the field and to the translate-add constant at `0` cancel. -/
theorem isTranslateAddConst_zero_flowField_iff (a : ℝ) (f g : DistOn upperHalfPlaneOpens) :
    IsTranslateAddConst 0 a (Exist.flowField 0 (-a) f) g ↔ IsTranslateAddConst 0 0 f g := by
  have key : ∀ φ φ' : TestOn upperHalfPlaneOpens, (∀ z : ℂ, φ' z = φ (z + 0)) → φ' = φ := fun φ φ' hφ => by
    ext z
    rw [hφ z, add_zero]
  constructor
  · intro h φ φ' hφ
    have e := key φ φ' hφ
    rw [h φ φ' hφ, e, WangWu.Shift.flowField_zero_apply]
    ring
  · intro h φ φ' hφ
    have e := key φ φ' hφ
    rw [h φ φ' hφ, e, WangWu.Shift.flowField_zero_apply]
    ring

/-- **A flow line at angle `θ` is the angle-`0` flow line of the raised field and data.** For piecewise-constant `b`
and `a = θ χ(κ)`: `IsFlowLineDriver κ (b − a) J θ P (h − a) W ζ ↔ IsFlowLineDriver κ b J 0 P h W ζ` (the coupling
field and the force word are the same on both sides). -/
theorem isFlowLineDriver_shift_iff {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} :
    IsFlowLineDriver κ (fun y => b y + -(θ * chiC κ)) J θ P (fun ω => Exist.flowField 0 (-(θ * chiC κ)) (h ω))
        W ζ ↔ IsFlowLineDriver κ b J 0 P h W ζ := by
  rw [isFlowLineDriver_eq_flowDrvOf, isFlowLineDriver_eq_flowDrvOf, jumpSet_add_const hb, leftLim_add_const hb,
    rightLim_add_const hb]
  unfold flowDrvOf
  have e1 : (-(leftLim b 0 + -(θ * chiC κ) + θ * chiC κ) / sleLambda κ - 1) =
      (-(leftLim b 0 + 0 * chiC κ) / sleLambda κ - 1) := by ring
  have e2 : ((rightLim b 0 + -(θ * chiC κ) + θ * chiC κ) / sleLambda κ - 1) =
      ((rightLim b 0 + 0 * chiC κ) / sleLambda κ - 1) := by ring
  have e3 : ∀ y : ℝ, (rightLim b y + -(θ * chiC κ) - (leftLim b y + -(θ * chiC κ))) / sleLambda κ =
      (rightLim b y - leftLim b y) / sleLambda κ := fun y => by ring
  simp only [e1, e2, e3]
  have e4 : ∀ (g : Ω → DistOn upperHalfPlaneOpens),
      (∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (Exist.flowField 0 (-(θ * chiC κ)) (h ω)) (g ω)) ↔
        ∀ ω, IsTranslateAddConst 0 (0 * chiC κ) (h ω) (g ω) := fun g => by
    rw [zero_mul]
    exact forall_congr' fun ω => isTranslateAddConst_zero_flowField_iff _ _ _
  simp only [e4]

/-! ### Raised words -/

/-- The word with every height raised by `a` (same jump positions). -/
def upW (a : ℝ) (c : BoundaryWord) : BoundaryWord := (c.1, c.2.1, fun j => c.2.2 j + a)

theorem upW_fn (a : ℝ) (c : BoundaryWord) : (upW a c).fn = fun y => c.fn y + a := rfl

theorem upW_jumps (a : ℝ) (c : BoundaryWord) : (upW a c).jumps = c.jumps := rfl

theorem isSorted_upW (a : ℝ) {c : BoundaryWord} (hc : c.IsSorted) : (upW a c).IsSorted := hc

theorem upW_neg_upW (a : ℝ) (c : BoundaryWord) : upW (-a) (upW a c) = c := by
  obtain ⟨n, x, q⟩ := c
  simp only [upW, add_neg_cancel_right]

theorem measurable_upW (a : ℝ) : Measurable (upW a) := by
  refine measurable_fst.prodMk (Measurable.prodMk (measurable_fst.comp measurable_snd) ?_)
  exact measurable_pi_iff.2 fun j =>
    ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)).add measurable_const

/-- Heights of the raised word, for the type counting. -/
theorem upW_heights (a : ℝ) (c : BoundaryWord) (j : ℕ) : (upW a c).2.2 j = c.2.2 j + a := rfl

/-! ### The shifted canonical code -/

/-- **The angle-`θ` code read at angle `0`**: `(c, f) ↦ F (c − θχ, f − θχ)`. -/
def shiftCode (k θ : ℝ) (F : BoundaryWord × DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞) :
    BoundaryWord × DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞ :=
  fun p => F (upW (-(θ * chiC k)) p.1, Exist.flowField 0 (-(θ * chiC k)) p.2)

/-- On the raised word and the raised field the shifted code is the original code. -/
theorem shiftCode_upW (k θ : ℝ) (F : BoundaryWord × DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞)
    (c : BoundaryWord) (f : DistOn upperHalfPlaneOpens) :
    shiftCode k θ F (upW (θ * chiC k) c, Exist.flowField 0 (θ * chiC k) f) = F (c, f) := by
  simp only [shiftCode, upW_neg_upW, WangWu.ChamberCond.flowField_zero_neg_flowField]

/-- **A canonical driver code at angle `θ` gives a canonical driver code at angle `0`** (`shiftCode`). -/
theorem isCanonicalDriverCode_shiftCode {k θ : ℝ}
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode k θ F) : IsCanonicalDriverCode k 0 (shiftCode k θ F) := by
  refine ⟨hF.1.comp (((measurable_upW _).comp measurable_fst).prodMk
    ((Exist.measurable_flowField 0 _).comp measurable_snd)), ?_, ?_⟩
  · intro c hc Ω _ Q _ h W L hG hWm hLm hWc hmatch
    have hG' : IsGFFWithBoundaryData Q (fun ω => Exist.flowField 0 (-(θ * chiC k)) (h ω))
        (upW (-(θ * chiC k)) c).fn (upW (-(θ * chiC k)) c).jumps :=
      Sec5.Cond44Ref.isGFFWithBoundaryData_flowField_zero hG _
    have h1 := hF.2.1 (upW (-(θ * chiC k)) c) (isSorted_upW _ hc) Q _ W L hG' hWm hLm hWc hmatch
    exact (isFlowLineDriver_shift_iff c.isPiecewiseConstantBoundaryData).1 h1
  · intro c Ω _ Q _ h W L hW
    have h1 := (isFlowLineDriver_shift_iff (θ := θ) c.isPiecewiseConstantBoundaryData).2 hW
    exact hF.2.2 (upW (-(θ * chiC k)) c) Q _ W L h1

/-! ### Word types of raised conditional words -/

/-- The raised returned stop words have countably many word types. -/
theorem countable_range_wordType_upW_retStop (k κ θ a l e : ℝ) (c : BoundaryWord) :
    (range fun r : RecData =>
      Supp8.Q3Stop.wordType k (upW e (GW2JointKernel.retWord a l (stopWord κ (c, θ, r))))).Countable := by
  obtain ⟨Hs, hHs, N, hN⟩ := BW1Life.retStopWord_bounded κ θ a l c
  refine (Supp8.Q3Stop.countable_typeSet k (hHs.image fun x => x + e) (N + 1)).mono ?_
  rintro _ ⟨r, rfl⟩
  exact Supp8.Q3Stop.wordType_mem_typeSet k _ (H := (fun x => x + e) '' Hs) (fun j => ⟨_, (hN r).1 j, rfl⟩)
    (hN r).2

end InteractingSLE.Theorem14.GW2Rd
