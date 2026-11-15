/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdtWit
import InteractingSLE.Spec.Supplement.GW1ActiveLaw
import InteractingSLE.Spec.Supplement.GW2ScheduleLaw
import InteractingSLE.Spec.Supplement.GW2SdpRoot

/-!
# The canonical launch word is the explicit stop word of the last piece, off finite sets

Packet PROVE-GW2-SDE (round 19, decision D45 item 2). The canonical family of a GW2 schedule is built with the source's
abstract stop law `βA`; its word at the launch of instruction `n + 1` is `βA (word_n, θ_n, record_n)`. The explicit stop
word `stopWord κ` is also a stop law (`GW1W.isStopLaw_stopWord`), so GW1's explicit successor witness
(`GW1W.isStageWitness_succ_expl`) gives a second witness of the same staged history at `n + 1`, with word
`stopWord κ (word_n, θ_n, record_n)` (consecutive launches: no re-centring). Two witnesses have the same data off their
jumps (`GW2Sdt.ae_fn_eq_of_stageWitness`):

* **`ae_canonWord_fn_eq_stopWord`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Sdt

open Exist Exist.Staged Exist.StagedLaw Restart GW2Schedule GW2Tip

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u}) {βA : BoundaryWord × ℝ × RecData → BoundaryWord}
  {c₀ : BoundaryWord} {b : ℝ → ℝ} {jumps : Finset ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The canonical word at a launch is the explicit stop word of the previous piece off finite sets**: for a GW2
schedule `⟨x, true, scheduleProgram 0 L⟩`, almost surely, when the first `n + 1` pieces succeed and instruction
`n + 1` exists, the canonical word before `n + 1` has the data of `stopWord κ (word_n, θ_n, record_n)` off the jumps. -/
theorem ae_canonWord_fn_eq_stopWord (h13 : Theorem13Statement.{u}) (hβA : IsStopLaw.{u} κ βA)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y)
    (hh : IsGFFWithBoundaryData P h b jumps) (x : ℝ) (L : List (ℝ × ℝ≥0)) (n : ℕ)
    (hn : n + 1 < (scheduleProgram 0 L).length) :
    ∀ᵐ ω ∂P, AllSucc (specDelta ⟨x, true, scheduleProgram 0 L⟩)
        (fun j => canonFam hκ h12p βA c₀ (specAngle ⟨x, true, scheduleProgram 0 L⟩)
          (specDelta ⟨x, true, scheduleProgram 0 L⟩) x h j ω) (n + 1) →
      ∀ y ∉ (canonWord hκ h12p βA c₀ (specAngle ⟨x, true, scheduleProgram 0 L⟩)
          (specDelta ⟨x, true, scheduleProgram 0 L⟩) κ b jumps ⟨x, true, scheduleProgram 0 L⟩ h (n + 1) ω).jumps ∪
          (stopWord κ (canonWord hκ h12p βA c₀ (specAngle ⟨x, true, scheduleProgram 0 L⟩)
            (specDelta ⟨x, true, scheduleProgram 0 L⟩) κ b jumps ⟨x, true, scheduleProgram 0 L⟩ h n ω,
            instrAngle ⟨x, true, scheduleProgram 0 L⟩ n,
            pastMap κ b jumps ⟨x, true, scheduleProgram 0 L⟩
              (canonFam hκ h12p βA c₀ (specAngle ⟨x, true, scheduleProgram 0 L⟩)
                (specDelta ⟨x, true, scheduleProgram 0 L⟩) x h) (n + 1) ω (Fin.last n))).jumps,
        (canonWord hκ h12p βA c₀ (specAngle ⟨x, true, scheduleProgram 0 L⟩)
          (specDelta ⟨x, true, scheduleProgram 0 L⟩) κ b jumps ⟨x, true, scheduleProgram 0 L⟩ h (n + 1) ω).fn y =
        (stopWord κ (canonWord hκ h12p βA c₀ (specAngle ⟨x, true, scheduleProgram 0 L⟩)
          (specDelta ⟨x, true, scheduleProgram 0 L⟩) κ b jumps ⟨x, true, scheduleProgram 0 L⟩ h n ω,
          instrAngle ⟨x, true, scheduleProgram 0 L⟩ n,
          pastMap κ b jumps ⟨x, true, scheduleProgram 0 L⟩
            (canonFam hκ h12p βA c₀ (specAngle ⟨x, true, scheduleProgram 0 L⟩)
              (specDelta ⟨x, true, scheduleProgram 0 L⟩) x h) (n + 1) ω (Fin.last n))).fn y := by
  classical
  set spec : ExplSpec := ⟨x, true, scheduleProgram 0 L⟩ with hspec
  set θ := specAngle spec with hθ
  set Δ := specDelta spec with hΔ
  set C := canonFam hκ h12p βA c₀ θ Δ x h with hC
  have hprog : IsFlowProg spec.2.2 θ Δ := isFlowProg_spec x true L
  have hΔt : ∀ j, Δ j ≠ ⊤ := specDelta_ne_top spec
  have hlaw := canon_stageLaw hκ h12p βA c₀ θ Δ h13 hβA hb hc₀J hc₀ hh (spec := spec) rfl hprog hΔt
  have hCm : ∀ j, Measurable (C j) := fun j => measurable_canonFam hκ h12p βA c₀ θ Δ x hβA.1 hh.1 j
  have hCreg : ∀ j ω, IsRegularDriver (C j ω) := fun j ω => isRegularDriver_canonFam hκ h12p βA c₀ θ Δ x h j ω
  obtain ⟨βk, Yk, hWk, hform⟩ := GW1W.isStageWitness_succ_expl (GW1W.isStopLaw_stopWord.{u} hκ) runMeasStatement
    hκ hb hh (k := n + 1) (Nat.succ_pos n) (fun j _ => hCm j) (fun j _ => hCreg j) (fun j _ => (hlaw j).2)
    (fun ℓ ω => canonWord hκ h12p βA c₀ θ Δ κ b jumps spec h ℓ ω)
    (fun ℓ ω => canonField hκ h12p βA c₀ θ Δ x h ℓ ω) (fun ℓ _ => (hlaw ℓ).1)
  have huniq := ae_fn_eq_of_stageWitness hb (k := n + 1) (fun j _ => hCm j) (fun j _ => hCreg j) (hlaw (n + 1)).1 hWk
  filter_upwards [huniq] with ω hu hs
  have hl1 : (ExplState.run κ b jumps spec (fun j => C j ω) (n + 1 + 1)).2.2.2.1 (n + 1) ≠ none :=
    (launch_ne_none_iff (κ := κ) (b := b) (jumps := jumps) θ Δ rfl hprog hΔt _ hn).2 hs
  have hl0 : (ExplState.run κ b jumps spec (fun j => C j ω) (n + 1)).2.2.2.1 n ≠ none :=
    (launch_ne_none_iff (κ := κ) (b := b) (jumps := jumps) θ Δ rfl hprog hΔt _ (lt_trans (Nat.lt_succ_self n) hn)).2
      (hs.mono (Nat.le_succ n))
  have hβk := hform n ω (Nat.lt_succ_self n) hl1 hl0 (fun j h1 h2 => absurd h2 (by omega))
  rw [sub_self, Complex.zero_re, GW2Sdp.shiftW_zero] at hβk
  intro y hy
  rw [← hβk] at hy ⊢
  exact hu hl1 y hy

end InteractingSLE.Theorem14.GW2Sdt
