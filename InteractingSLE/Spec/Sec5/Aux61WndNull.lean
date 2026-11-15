/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61ActCut
import InteractingSLE.Spec.Sec5.Aux61GCaptureNextWindow
import InteractingSLE.Spec.Sec5.Aux61GRecCapture
import InteractingSLE.Spec.Sec5.TwoMarkTrace12Assembly

/-! # The dyadic fibre cover of a null window event, and the pointwise-capture route to it

Packet PROVE-AUX61-WINDOW. The tops of Theorems 1.2–1.5 take the fibre leaf `Aux61Act.DyActFibreCoverOn` (currently
from `Aux61R1C.dyCover_of_choices_both`, whose `ChoiceInputs.completed_window` asks for completion at **every**
selected index; `Aux61WndPair` shows that for fixed-time families this field is equivalent to the window-null target).

A dyadic fibre cover of an event that is almost surely false holds trivially (`hasDyActFibreCover_of_ae_not`: no
cover sets are needed). Hence the fibre leaf follows from the window-null statement (`dyActFibreCoverOn_of_
restartWindowNullQOn`), which the existing **pointwise-capture** route proves without the every-selected-index
clause: from MARKS facts, the physical slit wiring and an almost-sure *existential* completed capture
(`dyActFibreCoverOn_of_marks_capture`, through `Aux61GRec.ae_not_of_marks_capture_cover`), or from the normalized R1
source of `Aux61GCaptureNext` (`dyCover_of_normalized_capture`, `dyCover_of_normalized_capture_both`). These are
drop-in replacements for `dyCover_of_choices_both`.

The reflected reference avoidance `Aux61Cov.R5NegStatement` used by `Aux61GRec`/`Aux61GCaptureNext` is supplied by
the proved `TwoMark.Trace12.r5NegStatement`, so it is not a hypothesis here. Nothing here assumes a source statement.
R48: no Theorem 1.2/1.3 hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Wnd

open Aux61SlitW Aux61Asm2 Aux61SlitWX Aux61Kernel Aux61ULoc Aux61Marks LawUnique

universe u

/-- **A dyadic fibre cover of an almost surely false event**: no cover sets are needed. -/
theorem hasDyActFibreCover_of_ae_not {X : Type u} [MeasurableSpace X] {μ : Measure X} {E : X → Prop}
    {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop} (h : ∀ᵐ x ∂μ, ¬ E x) :
    Aux61Act.HasDyActFibreCover μ E Ref := by
  refine ⟨Unit, inferInstance, fun _ => ∅, PUnit.{u + 1}, inferInstance, fun _ => 0, fun _ => univ,
    fun _ => MeasurableSet.empty, h.mono fun x hx hE => absurd hE hx, fun _ => ?_, fun _ => ?_⟩
  · simp
  · exact ae_of_all _ fun _ hx => absurd hx (notMem_empty _)

/-- **The fibre leaf from the window-null statement.** -/
theorem dyActFibreCoverOn_of_restartWindowNullQOn {G : ℝ → ℝ → ℝ → Prop}
    {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop} (h : RestartWindowNullQOn.{u} G) :
    Aux61Act.DyActFibreCoverOn.{u} G Ref := by
  intro t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P hP hf η ζ hh hfl
    Ω₂ mΩ₂ P₂ hP₂ h₂ W₂ ζ₂ hcf hlaw k hK hk s hs
  exact hasDyActFibreCover_of_ae_not
    (h t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P hf η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)

/-- **The fibre leaf from the window-null statement of every source setting.** -/
theorem dyActFibreCoverOn_of_source_null
    (hnull : ∀ S : SourceSetting.{u}, ∀ᵐ p ∂S.μ, ¬ S.windowEvent p)
    {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop} :
    Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Ref :=
  dyActFibreCoverOn_of_restartWindowNullQOn (Aux61GCaptureNext.restartWindowNullQOn_of_source_exclusion hnull)

/-- **The fibre leaf from MARKS data with pointwise completed capture.** For each source setting, MARKS facts of some
MARKS data on the glued space, its physical slit wiring, and an almost-sure *existential* completed capture of the
window event (some index whose selected restart completes in its window and lands in its reference interval) give the
fibre leaf. No completion is required at the other selected indices. -/
theorem dyActFibreCoverOn_of_marks_capture (D : ∀ S : SourceSetting.{u}, MarksData S.μ)
    (hF : ∀ S : SourceSetting.{u}, MarksFacts S.μ (D S))
    (W : ∀ S : SourceSetting.{u}, Aux61Asm.SlitWiringData ((D S).toAsmData (hF S)))
    (hW : ∀ S : SourceSetting.{u}, Aux61Asm.SlitWiring S.μ ((D S).toAsmData (hF S)) (W S))
    (hcap : ∀ S : SourceSetting.{u}, ∀ᵐ p ∂S.μ, S.windowEvent p → ∃ i, Aux61GRec.completedCapture (D S) i p)
    {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop} :
    Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Ref :=
  dyActFibreCoverOn_of_source_null fun S =>
    Aux61GRec.ae_not_of_marks_capture_cover (hF S) (W S) (hW S) TwoMark.Trace12.r5NegStatement (hcap S)

/-- **The fibre leaf from the normalized R1 source of `Aux61GCaptureNext` with pointwise completed capture**: a
drop-in replacement for `Aux61R1C.dyCover_of_choices_both` at one universe, without the every-selected-index
completed-window clause and with component (not full-ball) comparisons. -/
theorem dyCover_of_normalized_capture (D : ∀ S : SourceSetting.{u}, R1Restart S)
    (h : ∀ S : SourceSetting.{u}, (D S).HasChart)
    (R : ∀ S : SourceSetting.{u}, ReaderFacts (D S))
    (hTip : ∀ S : SourceSetting.{u}, OwnTipForwardLimit S)
    (V : ∀ S : SourceSetting.{u}, WindowData (D S) (h S))
    (hExit : ∀ S : SourceSetting.{u}, PhysicalExit (D S) (h S))
    (C : ∀ S : SourceSetting.{u}, ∀ i, Aux61GPrime.ZeroComparisons
      (S.marksData (cutSource S (source (D S) (h S)))) i)
    (hcaptured_cover : ∀ S : SourceSetting.{u}, ∀ᵐ p ∂S.μ, S.windowEvent p →
      ∃ i, Aux61GRec.completedCapture
        (S.marksData (cutSource S (source (D S) (h S)))) i p) :
    Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin :=
  dyActFibreCoverOn_of_restartWindowNullQOn
    (Aux61GCaptureNext.restartWindowNullQOn_of_normalized_capture D h R hTip V hExit C
      TwoMark.Trace12.r5NegStatement hcaptured_cover)

end InteractingSLE.Sec5.Aux61Wnd
