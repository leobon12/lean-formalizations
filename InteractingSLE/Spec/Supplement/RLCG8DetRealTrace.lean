/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetRealChart

/-! # G8: the restarted trace is interior between its two endpoints -/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE.RLC.G8Det.RealBoundary

variable {α : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}

/-- Yuan's shifted trace, translated to the original hydrodynamic coordinates,
has the original future as its continuous inverse image. -/
theorem cutInv_cutTrace (hw : Continuous w) (hw0 : w 0 = 0)
    (hgen : IsGeneratingTrace w ⊤ α) (a : ℝ≥0) {t : ℝ} (ht : 0 ≤ t) :
    cutInv w a (cutTrace w a t) = α ((a : ℝ) + t).toNNReal := by
  dsimp only [cutInv, cutTrace]
  rw [add_sub_cancel_right, YuanSimpleApprox.trMap_zero_left
    (by simpa only [Real.toNNReal_zero] using hw0)]
  exact ((isLoewnerTrace_of_isGeneratingTrace hgen).extendFrom_shift_tip
    (hw.comp continuous_real_toNNReal)
    (by simpa only [Real.toNNReal_zero] using hw0) a.2 ht).2.1

theorem continuousOn_cutTrace (hw : Continuous w) (hw0 : w 0 = 0)
    (hgen : IsGeneratingTrace w ⊤ α) (a : ℝ≥0) : ContinuousOn (cutTrace w a) (Ici 0) :=
  ((isLoewnerTrace_of_isGeneratingTrace hgen).isLoewnerTrace_shift
    (hw.comp continuous_real_toNNReal)
    (by simpa only [Real.toNNReal_zero] using hw0) a.2).2.1.add_const _

theorem cutTrace_zero (hw : Continuous w) (a : ℝ≥0) : cutTrace w a 0 = (w a : ℂ) := by
  have hz : loewnerTip (shiftDrive (fun s : ℝ => w s.toNNReal) a) 0 = 0 :=
    loewnerTip_shiftDrive_zero (hw.comp continuous_real_toNNReal) a
  change loewnerTip (shiftDrive (fun s : ℝ => w s.toNNReal) a) 0 + w a = (w a : ℂ)
  rw [hz, zero_add]

theorem cutTrace_mem_Hbar (hw : Continuous w) (hw0 : w 0 = 0)
    (hgen : IsGeneratingTrace w ⊤ α) (a : ℝ≥0) {t : ℝ} (ht : 0 ≤ t) : cutTrace w a t ∈ Hbar := by
  have h := ((isLoewnerTrace_of_isGeneratingTrace hgen).extendFrom_shift_tip
    (hw.comp continuous_real_toNNReal)
    (by simpa only [Real.toNNReal_zero] using hw0) a.2 ht).1
  change 0 ≤ (loewnerTip (shiftDrive (fun s : ℝ => w s.toNNReal) a) t + w a).im
  rw [add_im, ofReal_im, add_zero]
  exact h

/-- The entire actual restarted hull is the filling of this compact trace. -/
theorem fwdHull_eq_fillH_cutTrace (hw : Continuous w) (hw0 : w 0 = 0)
    (hgen : IsGeneratingTrace w ⊤ α) (a : ℝ≥0) {T : ℝ} (hT : 0 ≤ T) :
    fwdHull (cutDrive w a) T = fillH (cutTrace w a '' Icc 0 T) := by
  let V := shiftDrive (fun s : ℝ => w s.toNNReal) a
  have hV : cutDrive w a = fun t => V t + w a := by
    funext t
    simp only [V, cutDrive, shiftDrive, Real.toNNReal_coe, sub_add_cancel]
  have hη : IsLoewnerTrace V (loewnerTip V) :=
    (isLoewnerTrace_of_isGeneratingTrace hgen).isLoewnerTrace_shift
    (hw.comp continuous_real_toNNReal) (by simpa only [Real.toNNReal_zero] using hw0) a.2
  rw [hV, ConformalImageFull.fwdHull_add_const]
  calc
    _ = (fun z : ℂ => z + w a) '' fillH (loewnerTip V '' Icc 0 T) :=
      congrArg (fun S : Set ℂ => (fun z : ℂ => z + w a) '' S) (hη.2.2 T hT)
    _ = fillH (cutTrace w a '' Icc 0 T) := by
      have haff : (fun z : ℂ => z + w a) = ⇑(affHomeo 1 zero_lt_one (w a)) := by
        funext z
        simp only [coe_affHomeo, Complex.ofReal_one, one_mul]
      rw [haff, ← fillH_image_affHomeo, image_image]
      simp only [coe_affHomeo, ofReal_one, one_mul, V]
      rfl

/-- No real contacts occur between the cut and the terminal landing. A real
shifted point would invert to an already visited old trace point. -/
theorem cutTrace_mem_H (hi : Function.Injective α) (hw : Continuous w) (hw0 : w 0 = 0)
    (hgen : IsGeneratingTrace w ⊤ α) {a : ℝ≥0} {t : ℝ} (ht : 0 < t)
    (hH : α ((a : ℝ) + t).toNNReal ∈ H) : cutTrace w a t ∈ H := by
  have hbar := cutTrace_mem_Hbar hw hw0 hgen a ht.le
  change 0 < (cutTrace w a t).im
  change 0 ≤ (cutTrace w a t).im at hbar
  apply lt_of_le_of_ne hbar
  intro him
  have htold := Sec6.mem_trace_of_trMap_real (isLoewnerTrace_of_isGeneratingTrace hgen)
    (hw.comp continuous_real_toNNReal) (by simpa only [Real.toNNReal_zero] using hw0) a.2
    (w := cutTrace w a t - w a) (by
      simpa only [sub_im, ofReal_im, sub_zero] using him.symm)
    (by
      change cutInv w a (cutTrace w a t) ∈ H
      rw [cutInv_cutTrace hw hw0 hgen a ht.le]
      exact hH)
  change cutInv w a (cutTrace w a t) ∈ (fun s : ℝ => α s.toNNReal) '' Icc 0 (a : ℝ) at htold
  rw [cutInv_cutTrace hw hw0 hgen a ht.le] at htold
  obtain ⟨s, hs, he⟩ := htold
  have heq := hi he
  have hs' : s.toNNReal ≤ a := (Real.toNNReal_le_iff_le_coe).2 hs.2
  have hat : a < ((a : ℝ) + t).toNNReal := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (by linarith [a.2])]
    linarith only [ht]
  exact (not_lt_of_ge (heq ▸ hs')) hat

/-- The terminal shifted point is real because its physical inverse is real. -/
theorem cutTrace_terminal_real (hcα : Continuous α) (hw : Continuous w) (hw0 : w 0 = 0)
    (hgen : IsGeneratingTrace w ⊤ α) {a σ : ℝ≥0} (haσ : a ≤ σ) {q : ℝ} (hασ : α σ = q) :
    (cutTrace w a ((σ : ℝ) - a)).im = 0 := by
  have ht : (0 : ℝ) ≤ σ - a := sub_nonneg.2 (by exact_mod_cast haσ)
  apply le_antisymm _ (cutTrace_mem_Hbar hw hw0 hgen a ht)
  apply not_lt.1
  intro hpos
  have hp := (cutInv_mem_domain hcα hw hw0 hgen (a := a) hpos).1
  rw [cutInv_cutTrace hw hw0 hgen a ht, add_sub_cancel, Real.toNNReal_coe, hασ] at hp
  exact lt_irrefl (0 : ℝ) (show 0 < (q : ℂ).im from hp)

end InteractingSLE.RLC.G8Det.RealBoundary
