/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow19Transfer

/-! # The theorem top's exact hcap from admission of thin-window records

CAPTURE chooses the word height, phase, seed/landing neighborhood and
access tests. Its remaining input below asks only that sufficiently thin
candidates accept the actual initial record. Finite contact, arbitrarily
thin capture, stay, endpoint convergence and finite-restriction survival
are proved here, independently of any chosen reference height.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow19
open Aux61SlitW Aux61R1C Aux61Asm2 Aux61GR1F Aux61GWord Aux61GInst Aux61FibData LawUnique
universe u
variable {S : SourceSetting.{u}}

/-- The regular cut preserves completed captures at all good samples. -/
theorem completedCapture_cut_of_good (C : RestartChoices S) (i : C.Idx)
    {p : S.Ω × HistorySpace 0 0} (hg : p ∈ Aux61Asm2.goodSet S (family C))
    (hc : Aux61GRec.completedCapture (S.marksData (family C)) i p) :
    Aux61GRec.completedCapture (S.marksData (cutSource S (family C))) i p := by
  obtain ⟨hi, hf, hs, y, hy, hl⟩ := hc
  have he : p ∈ (family C).event i := hi
  have hcut : p ∈ (cutSource S (family C)).event i := ⟨he, hg⟩
  have heq : inPath ((cutSource S (family C)).event i)
      (sourceChart (cutSource S (family C)) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
      ((cutSource S (family C)).path i) ((cutSource S (family C)).contact i) p =
    inPath ((family C).event i)
      (sourceChart (family C) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
      ((family C).path i) ((family C).contact i) p := by
    funext v
    simp only [inPath, hcut, he, true_and]
    rfl
  refine ⟨hi, hf, ?_, y, hy, ?_⟩
  · intro v hv
    change inPath ((cutSource S (family C)).event i)
      (sourceChart (cutSource S (family C)) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
      ((cutSource S (family C)).path i) ((cutSource S (family C)).contact i) p v ∈
      ((cutSource S (family C)).data i).V
    rw [heq]
    exact hs v hv
  · change Tendsto (inPath ((cutSource S (family C)).event i)
      (sourceChart (cutSource S (family C)) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
      ((cutSource S (family C)).path i) ((cutSource S (family C)).contact i) p)
      (𝓝[<] ((cutSource S (family C)).contact i p).toNNReal) (𝓝 (y : ℂ))
    rw [heq]
    exact hl

namespace SeedPlacement
variable {C : RestartChoices S} (P : SeedPlacement C)
include P

/-- Port the source's thin captures to R103's family. The sole additional
mathematical input is CAPTURE's initial-record admission on a sufficiently
small seed-plus-landing neighborhood. It does not assume a stay condition,
completed capture, finite contact or a choice of reference height.
The conclusion is exactly the current theorem top's `hcap` type. -/
theorem completed_cover_of_admission (hsel : ∀ i, MeasurableSet (C.selected i))
    (W : WindowFields C.toR1Restart)
    (hAdmission : ∀ᵐ p ∂S.μ, S.windowEvent p →
      ∀ t : Aux61GWindow17.GoodTime S, t.1 = S.t → ∀ y : ℝ, y ≠ 0 →
      Tendsto (timePath S t p) (𝓝[<] (timeContact S t p).toNNReal) (𝓝 (y : ℂ)) →
      ∃ O : Set ℝ, IsOpen O ∧ 0 ∈ O ∧ y ∈ O ∧
        ∀ J : Aux61GWindow17.AllowedWindow,
          timeRecord S t p ∈ Aux61GWindow17.windowRecords S t J →
          (∀ z ∈ closure (outerBuffer J.1.1), z.im = 0 → z.re ∈ O) →
          ∃ i : C.Idx, C.q i.1 = t.1 ∧ C.record i.1 p ∈ C.toR1Restart.selected i ∧
            bufferedWindow J.1.1 ⊆ (C.data i.1).V ∧ y ∈ Ioo (C.left i.1) (C.right i.1)) :
    ∀ᵐ p ∂S.μ, S.windowEvent p → ∃ i,
      Aux61GRec.completedCapture (S.marksData (cutSource S (family C))) i p := by
  filter_upwards [ae_capture_in_real_open S, hAdmission, P.ae_good hsel W] with p hc ha hg hw
  obtain ⟨t, ht, k, -, -, hf, y, hy, hl, hthin⟩ := hc hw
  obtain ⟨O, hO, hO0, hOy, hencode⟩ := ha hw t ht y hy hl
  obtain ⟨J, -, hrecord, hreal, hstay, -⟩ := hthin O hO hO0 hOy
  obtain ⟨i, hq, hi, hV, hI⟩ := hencode J hrecord hreal
  exact ⟨i, completedCapture_cut_of_good C i hg
    (P.completedCapture_of_time_capture i t hq hi hf J hstay hl hV hI)⟩

end SeedPlacement
end InteractingSLE.Sec5.Aux61GWindow19
