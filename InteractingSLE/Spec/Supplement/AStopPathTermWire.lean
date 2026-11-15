/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AStopPathTerm
import InteractingSLE.Spec.Supplement.AStopPathWire

/-!
# The terminal case proved; the source statements from items 4–5 and Lemma 7.5

Packet PROVE-T15-ASTOP-PATH. **`aStopTerminalSndStatement`** and **`aStopTerminalFstStatement`** prove the terminal
case of item 6 (`AStopTerminalSndStatement`, `AStopTerminalFstStatement`) from `threshold_terminal` at every ordinary
sample, with the flow line's terminal bad incident height (FCK2's `ae_original_terminal_bad_incident`). Hence
**`retOrdAStopSourceSndStatement_of_safe`** and **`retOrdAStopSourceFstSeedStatement_of_safe`**: the two source
statements of Theorem 1.5's leaf 3 follow from Lemma 7.5 and items 4–5 alone (`AStopSafeSndStatement`,
`AStopSafeFstStatement`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped NNReal ENNReal

open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn)

namespace InteractingSLE.RLC.AStopPath

open Supp7 Restart PiecewiseConstantBoundaryData MartChar.RealFlow OrdModel
open Exist.StagedLaw.BoundaryWord (shiftW)

universe u

theorem contStop_ne_top_of_contLife {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {a : ℝ≥0} {K : Set ℂ}
    (h : contLife η ζ a K ≠ ⊤) : contStop η ζ a K ≠ ⊤ := fun ht => h (by rw [contLife, ht, ENNReal.top_sub_coe])

theorem IsAMono.congr_K {ψ : ℂ → ℂ} {K K' : Set ℂ} (hM : IsAMono ψ K) (hK : K = K') : IsAMono ψ K' := hK ▸ hM

/-- **The terminal case of the A-stopped second continuation, proved.** -/
theorem aStopTerminalSndStatement : AStopTerminalSndStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag c hc
  have hp₁ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁
  have hp₂ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂
  have hbad := FCPlumb.ae_original_terminal_bad_incident hκ hb hη₂
  filter_upwards [hp₁, hp₂, hag, hc, hbad] with ω hp₁ω hp₂ω hagω hcω hbadω hord hstop hoff W hWc hW0 hg hV nL nR
    ρL ρR htype
  obtain ⟨hG, ha₁, ha₂⟩ := hagω hord.1 hord.2.1
  have hS : IsOrdSample d η₁ η₂ ζ₁ ζ₂ x₁ x₂ ω := ⟨hG, hp₁ω, hp₂ω, hx, ha₁, ha₂, hord⟩
  have hR := hS.isRetCont_snd hd
  have hA := hS.isAChart_snd hd
  have hM := hS.isAMono_snd hd
  obtain ⟨-, hunt⟩ := hcω hord
  rw [hS.D_eq hd] at hg hV ⊢
  have hfin := contStop_ne_top_of_contLife (canonRetLife_ne_top hR hV).1
  rw [hstop] at hfin
  have hpos : 0 < (ζ₂ ω).toNNReal :=
    ENNReal.toNNReal_pos (ne_of_gt (lt_of_le_of_lt zero_le hord.2.1)) hfin
  exact threshold_terminal hR hA hM hκ hb hunt htype hWc hW0 hg hV hstop hoff
    (hbadω _ hpos (ENNReal.coe_toNNReal hfin))

/-- **The terminal case of the A-stopped first continuation, proved.** -/
theorem aStopTerminalFstStatement : AStopTerminalFstStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag c hc
  have hp₁ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁
  have hp₂ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂
  have hbad := FCPlumb.ae_original_terminal_bad_incident hκ hb hη₁
  filter_upwards [hp₁, hp₂, hag, hc, hbad] with ω hp₁ω hp₂ω hagω hcω hbadω hord hstop hoff W hWc hW0 hg hV nL nR
    ρL ρR htype
  obtain ⟨hG, ha₁, ha₂⟩ := hagω hord.1 hord.2.1
  have hS : IsOrdSample d η₁ η₂ ζ₁ ζ₂ x₁ x₂ ω := ⟨hG, hp₁ω, hp₂ω, hx, ha₁, ha₂, hord⟩
  have hR := hS.isRetCont_fst hd
  have hK : η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r = η₂ ω '' Icc 0 d.r ∪ η₁ ω '' Icc 0 d.u := union_comm _ _
  have hA := (hS.isAChart_fst hd).congr_K hK
  have hM := (hS.isAMono_fst hd).congr_K hK
  obtain ⟨-, hunt⟩ := hcω hord
  have hunt' := isUntouchedWord_shift (hK ▸ hunt) (tipPos d η₁ ω)
  rw [hS.D_eq hd, OrdDet.canonRetLife_shift, hK] at hV ⊢
  rw [hK] at hstop hoff
  have hg' : IsGeneratingTrace W (canonRetLife (H \ fillH (η₂ ω '' Icc 0 d.r ∪ η₁ ω '' Icc 0 d.u))
      (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) (ζ₁ ω) d.u (η₂ ω '' Icc 0 d.r ∪ η₁ ω '' Icc 0 d.u) 0)
      (canonRetPath (H \ fillH (η₂ ω '' Icc 0 d.r ∪ η₁ ω '' Icc 0 d.u))
        (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) (ζ₁ ω) d.u (η₂ ω '' Icc 0 d.r ∪ η₁ ω '' Icc 0 d.u) 0) := by
    rw [hS.D_eq hd, OrdDet.canonRetLife_shift, hK] at hg
    refine isGeneratingTrace_congr_le hg fun t _ => ?_
    rw [OrdDet.canonRetPath_shift _ (d.fwd ω), add_sub_cancel_right]
  have hfin := contStop_ne_top_of_contLife (canonRetLife_ne_top hR hV).1
  rw [hstop] at hfin
  have hpos : 0 < (ζ₁ ω).toNNReal :=
    ENNReal.toNNReal_pos (ne_of_gt (lt_of_le_of_lt zero_le hord.1)) hfin
  exact threshold_terminal hR hA hM hκ hb hunt' htype hWc hW0 hg' hV hstop hoff
    (hbadω _ hpos (ENNReal.coe_toNNReal hfin))

/-- **The A-stopped second continuation's source inputs from Lemma 7.5 and items 4–5.** -/
theorem retOrdAStopSourceSndStatement_of_safe (hL75 : Theorem15.Lemma75Statement.{u})
    (hsafe : AStopSafeSndStatement.{u}) : RetOrdAStopSourceSndStatement.{u} :=
  retOrdAStopSourceSndStatement_of_inputs hL75 hsafe aStopTerminalSndStatement

/-- **The A-stopped first continuation's seeded source inputs from Lemma 7.5 and items 4–5.** -/
theorem retOrdAStopSourceFstSeedStatement_of_safe (hL75 : Theorem15.Lemma75Statement.{u})
    (hsafe : AStopSafeFstStatement.{u}) : RetOrdAStopSourceFstSeedStatement.{u} :=
  retOrdAStopSourceFstSeedStatement_of_inputs hL75 hsafe aStopTerminalFstStatement

end InteractingSLE.RLC.AStopPath
