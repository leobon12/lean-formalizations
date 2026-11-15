/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2Part3PC

/-!
# The real Loewner flow along a shifted driver

Packet PROVE-PROP59-NODETREE. Specification §5.2, proof of Proposition 5.9 (p. 144, Figure 5.8): along a finite
alternating exploration the marks of a later piece are the images, under the piece's relative driver, of the marks at
its start. This file proves that this piecewise transport is the transport by the whole driver (the flow property of
the real Loewner equation), so that the strict separation of a simple curve's mark images applies to the marks
reached through any number of switches.

* `shiftDrv w S`: the driver after `S`, relative to `w S`;
* `isPosSol_shift`, `isPosSol_concat`: positive solutions restrict and concatenate at `S`;
* `alive_shift`, `alive_of_shift`;
* `rightImg_le_gImg_of_le`;
* **`rightImg_shiftDrv`**: `R^{w(S+·)−w(S)}_u(R^w_S(x) − w S) = R^w_{S+u}(x) − w S`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Prop59NodeTree

open MartChar.RealFlow

/-- **The driver after time `S`**, relative to its value at `S`. -/
def shiftDrv (w : ℝ → ℝ) (S : ℝ) : ℝ → ℝ := fun r => w (S + r) - w S

variable {w : ℝ → ℝ}

theorem continuous_shiftDrv (hw : Continuous w) (S : ℝ) : Continuous (shiftDrv w S) :=
  (hw.comp (continuous_const.add continuous_id)).sub continuous_const

theorem shiftDrv_zero (S : ℝ) : shiftDrv w S 0 = 0 := by simp [shiftDrv]

theorem shiftDrv_neg (S : ℝ) : shiftDrv (fun r => -w r) S = fun r => -shiftDrv w S r := by
  funext r
  simp only [shiftDrv]
  ring

/-- A positive solution through `S + u`, read after `S`, solves the shifted equation from its value at `S`. -/
theorem isPosSol_shift {y S u : ℝ} {X : ℝ → ℝ} (hS : 0 ≤ S) (hu : 0 ≤ u) (hX : IsPosSol w y (S + u) X) :
    IsPosSol (shiftDrv w S) (X S) u (fun r => X (S + r)) := by
  have hc : ContinuousOn (fun v => 2 / X v) (Icc 0 (S + u)) :=
    continuousOn_const.div hX.1 fun v hv => ((hX.2 v hv).1).ne'
  refine ⟨hX.1.comp (continuous_const.add continuous_id).continuousOn fun r hr =>
    ⟨by linarith [hr.1], by linarith [hr.2]⟩, fun r hr => ?_⟩
  have hr' : S + r ∈ Icc 0 (S + u) := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hS' : S ∈ Icc 0 (S + u) := ⟨hS, by linarith⟩
  refine ⟨(hX.2 _ hr').1, ?_⟩
  have e1 := (hX.2 _ hr').2
  have e2 := (hX.2 _ hS').2
  have hi1 : IntervalIntegrable (fun v => 2 / X v) volume 0 S :=
    (hc.mono (by rw [uIcc_of_le hS]; exact Icc_subset_Icc_right (by linarith))).intervalIntegrable
  have hi2 : IntervalIntegrable (fun v => 2 / X v) volume S (S + r) :=
    (hc.mono (by
      rw [uIcc_of_le (by linarith [hr.1])]
      exact Icc_subset_Icc hS (by linarith [hr.2]))).intervalIntegrable
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hcomp : ∫ v in (0 : ℝ)..r, 2 / X (S + v) = ∫ v in S..S + r, 2 / X v := by
    have h := intervalIntegral.integral_comp_add_left (fun v => 2 / X v) S (a := 0) (b := r)
    simp only [add_zero] at h
    exact h
  show X (S + r) = X S - shiftDrv w S r + ∫ v in (0 : ℝ)..r, 2 / X (S + v)
  rw [hcomp, shiftDrv, e1, e2, ← hsplit]
  ring

/-- **Positive solutions concatenate at `S`.** -/
theorem isPosSol_concat {y S u : ℝ} {X X' : ℝ → ℝ} (hS : 0 ≤ S) (hu : 0 ≤ u) (hX : IsPosSol w y S X)
    (hX' : IsPosSol (shiftDrv w S) (X S) u X') :
    IsPosSol w y (S + u) (fun v => if v ≤ S then X v else X' (v - S)) := by
  classical
  set Y : ℝ → ℝ := fun v => if v ≤ S then X v else X' (v - S) with hYdef
  have hX'0 : X' 0 = X S := by
    have := (hX'.2 0 ⟨le_rfl, hu⟩).2
    rw [this, shiftDrv_zero, intervalIntegral.integral_same]
    ring
  have hYc : ContinuousOn Y (Icc 0 (S + u)) := by
    refine ContinuousOn.if (fun v hv => ?_) ?_ ?_
    · have hfr : frontier {v : ℝ | v ≤ S} = {S} := frontier_Iic
      rw [hfr] at hv
      rw [mem_singleton_iff.1 hv.2, sub_self, hX'0]
    · refine hX.1.mono fun v hv => ⟨hv.1.1, ?_⟩
      exact closure_minimal (fun _ h => h) isClosed_Iic hv.2
    · have hcl : closure {v : ℝ | ¬ v ≤ S} ⊆ Ici S :=
        closure_minimal (fun v hv => le_of_lt (not_le.1 hv)) isClosed_Ici
      refine hX'.1.comp (continuous_id.sub continuous_const).continuousOn fun v hv => ?_
      have h1 : S ≤ v := hcl hv.2
      exact ⟨by linarith, by linarith [hv.1.2]⟩
  have hYpos : ∀ v ∈ Icc 0 (S + u), 0 < Y v := by
    intro v hv
    by_cases hvS : v ≤ S
    · simp only [hYdef, hvS, ↓reduceIte]; exact (hX.2 v ⟨hv.1, hvS⟩).1
    · simp only [hYdef, hvS, ↓reduceIte]
      exact (hX'.2 _ ⟨by linarith [not_le.1 hvS], by linarith [hv.2]⟩).1
  have hc : ContinuousOn (fun v => 2 / Y v) (Icc 0 (S + u)) :=
    continuousOn_const.div hYc fun v hv => (hYpos v hv).ne'
  have hint : ∀ a b, 0 ≤ a → a ≤ b → b ≤ S + u → IntervalIntegrable (fun v => 2 / Y v) volume a b :=
    fun a b ha hab hb => (hc.mono (by rw [uIcc_of_le hab]; exact Icc_subset_Icc ha hb)).intervalIntegrable
  have hagree : ∀ v, 0 ≤ v → v ≤ S → ∫ r in (0 : ℝ)..v, 2 / X r = ∫ r in (0 : ℝ)..v, 2 / Y r := by
    intro v hv hvS
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hv] at hr
    simp only [hYdef, show r ≤ S from hr.2.trans hvS, ↓reduceIte]
  refine ⟨hYc, fun v hv => ⟨hYpos v hv, ?_⟩⟩
  by_cases hvS : v ≤ S
  · simp only [hYdef, hvS, ↓reduceIte]
    rw [(hX.2 v ⟨hv.1, hvS⟩).2, hagree v hv.1 hvS]
  · have hSv : S < v := not_le.1 hvS
    simp only [hYdef, hvS, ↓reduceIte]
    have hv' : v - S ∈ Icc 0 u := ⟨by linarith, by linarith [hv.2]⟩
    rw [(hX'.2 _ hv').2, (hX.2 S ⟨hS, le_rfl⟩).2, hagree S hS le_rfl]
    have hcomp : ∫ r in (0 : ℝ)..v - S, 2 / X' r = ∫ r in S..v, 2 / Y r := by
      have h := intervalIntegral.integral_comp_sub_right (fun r => 2 / X' r) S (a := S) (b := v)
      rw [sub_self] at h
      rw [← h]
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hSv.le] at hr
      by_cases hrS : r ≤ S
      · have hrS' : r = S := le_antisymm hrS hr.1
        simp only [hYdef, hrS', sub_self, hX'0, ite_self]
      · simp only [hYdef, hrS, ↓reduceIte]
    rw [hcomp, ← intervalIntegral.integral_add_adjacent_intervals (hint 0 S le_rfl hS (by linarith))
      (hint S v hS hSv.le hv.2)]
    simp only [shiftDrv, add_sub_cancel]
    ring

/-- An alive point stays alive along the shifted driver, from its flow value at `S`. -/
theorem alive_shift (hw : Continuous w) {y S u : ℝ} (hS : 0 ≤ S) (hu : 0 ≤ u) (h : Alive w y (S + u)) :
    Alive (shiftDrv w S) (cflow w y S) u ∧
      gImg (shiftDrv w S) (cflow w y S) u = gImg w y (S + u) - w S := by
  have hX := h.isPosSol hw
  have hsh := isPosSol_shift hS hu hX
  refine ⟨⟨_, hsh⟩, ?_⟩
  rw [gImg, gImg, cflow_eq_of_isPosSol (continuous_shiftDrv hw S) hsh ⟨hu, le_rfl⟩, shiftDrv]
  ring

/-- A point alive at `S` whose flow value stays alive along the shifted driver is alive at `S + u`. -/
theorem alive_of_shift (hw : Continuous w) {y S u : ℝ} (hS : 0 ≤ S) (hu : 0 ≤ u) (h : Alive w y S)
    (h' : Alive (shiftDrv w S) (cflow w y S) u) : Alive w y (S + u) :=
  ⟨_, isPosSol_concat hS hu (h.isPosSol hw) (h'.isPosSol (continuous_shiftDrv hw S))⟩

/-- The geometric image of `x` is at most the image of every alive point `y ≥ x`. -/
theorem rightImg_le_gImg_of_le (hw : Continuous w) {x y t : ℝ} (ht : 0 ≤ t) (hxy : x ≤ y) (hy : Alive w y t) :
    rightImg w x t ≤ gImg w y t := by
  rcases hxy.lt_or_eq with hlt | rfl
  · exact rightImg_le_gImg hw ht hlt hy
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hy' : Alive w (x + ε) t := hy.of_le hw (by linarith) ht
    have h1 := rightImg_le_gImg hw ht (by linarith : x < x + ε) hy'
    have h2 := (cflow_lt_and_sub_le hw hy (by linarith : x < x + ε) ht ⟨ht, le_rfl⟩).2
    simp only [gImg] at h1 ⊢
    linarith

/-- **The flow property of the geometric images**: the image of `x` at `S + u` is the image, along the shifted
driver, of its image at `S` (all relative to `w S`). -/
theorem rightImg_shiftDrv (hw : Continuous w) {S u : ℝ} (hS : 0 ≤ S) (hu : 0 ≤ u) (x : ℝ) :
    rightImg (shiftDrv w S) (rightImg w x S - w S) u = rightImg w x (S + u) - w S := by
  have hw' := continuous_shiftDrv hw S
  apply le_antisymm
  · rw [le_sub_iff_add_le]
    show _ ≤ sInf (imgSet w x (S + u))
    refine le_csInf (imgSet_nonempty hw x (by linarith)) ?_
    rintro _ ⟨y, hxy, hy, rfl⟩
    obtain ⟨hy', hg⟩ := alive_shift hw hS hu hy
    have hyS : Alive w y S := hy.mono (by linarith)
    have hx' : rightImg w x S - w S ≤ cflow w y S := by
      have := rightImg_le_gImg hw hS hxy hyS
      simp only [gImg] at this
      linarith
    have key := rightImg_le_gImg_of_le hw' hu hx' hy'
    linarith
  · rw [sub_le_iff_le_add]
    show sInf (imgSet w x (S + u)) ≤ _
    have hne := imgSet_nonempty hw' (rightImg w x S - w S) hu
    suffices h : sInf (imgSet w x (S + u)) - w S ≤ sInf (imgSet (shiftDrv w S) (rightImg w x S - w S) u) by
      have e : rightImg (shiftDrv w S) (rightImg w x S - w S) u =
          sInf (imgSet (shiftDrv w S) (rightImg w x S - w S) u) := rfl
      linarith
    refine le_csInf hne ?_
    rintro _ ⟨y', hxy', hy', rfl⟩
    have hlt : rightImg w x S < y' + w S := by linarith
    obtain ⟨y, hxy, hyS, hgy⟩ := ZhanGT4.A2X.P3.exists_alive_gImg_eq_of_rightImg_lt hw hS hlt
    have hc : cflow w y S = y' := by
      simp only [gImg] at hgy
      linarith
    rw [← hc] at hy' ⊢
    have hyu := alive_of_shift hw hS hu hyS hy'
    obtain ⟨-, hg⟩ := alive_shift hw hS hu hyu
    have := rightImg_le_gImg hw (by linarith) hxy hyu
    rw [hg]
    exact sub_le_sub_right this _

end InteractingSLE.Sec5.Prop59NodeTree
