/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2KdInputs

/-!
# SB2(1) from the exact erased-driver input

This conditional assembly leaves the source statement unchanged. All launch
chart/word construction and conditional realization are proved; the only new
mathematical hypothesis is `SB2ErasedDriverInputsStatement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Sec4 Exist.Staged Exist.StagedLaw Restart WalkInf

/-- The original driver/link target from the explicit geometric driver and
canonical-code input. No source premise or conclusion is modified. -/
theorem sb2DriverLinkAmbStatement_of_erasedInputs
    (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hinputs : SB2ErasedDriverInputsStatement h12p) : SB2DriverLinkAmbStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh hadm E hE hER hreg
    k u ψ hu hψ hL hH η ζ hη hS1
  let H : SB2LaunchProblem κ b jumps P h E k u ψ η ζ :=
    ⟨hκ, hκ4, hb, hh, hadm, hE, hER, hreg, hu, hψ, hL, hH, hη, hS1⟩
  let w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
  have hprog := isBoundaryContinuedProgram_boundaryWalkSpec b jumps
    (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hS : IsStagedHistory κ b jumps P h w (E w) := hE w hprog
  have hR : StagedPiecesRegular κ b jumps P w (E w) := hER w hprog
  have hamb : ∀ t, t < 0 → t ∉ jumps →
      b t + -(Real.pi / 2) * chiC κ < sleLambda κ :=
    fun t ht htJ => Ly.height_lt_of_cumWeightLeft hκ (hadm t ht htJ)
  obtain ⟨m, cw, T, hm, hcw, hmc, heq, hG, hcc, hT, hcover⟩ :=
    exists_k2Launch_countable_types hκ hb hh (w := w) rfl hS hR
      (hreg w) hamb k ψ hu
  let I : K2LaunchInputs κ b jumps P h E k u ψ :=
    ⟨m, cw, T, hm, hcw, hmc, heq, hG, hcc, hT, hcover⟩
  obtain ⟨D, γ, hDm, hDr, hcode, hgeom⟩ := hinputs κ b jumps P h E k u ψ η ζ H I
  have h𝒢 := hS.2.1 (k + 1)
  have hF : MeasurableSet[pastSigma κ b jumps w (E w) (k + 1)]
      (launchSet κ b jumps E (k + 1)) :=
    measurableSet_launch_pastSigma hb hS.1 (hreg w) (k + 1)
  have hWm : ∀ t, Measurable (fun ω => (D ω).1 t) :=
    fun t => (measurable_pi_apply t).comp hDm.fst
  have hVm : Measurable (fun ω => (D ω).2) := hDm.snd
  have hD := isCondFlowLineDriverOn_of_codeMatch h12p h13 hκ ψ h𝒢 hF
    I.word_measurable I.chart_measurable I.frozen I.field hWm hVm
    (fun ω => (hDr ω).1) hcode
  have hDa := hD.congr_chart
    (I.chart_eq.mono fun ω he hFω => ⟨(he hFω).symm, rfl, rfl⟩)
  have hfreeze : ∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E (k + 1) →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps w (E w) (k + 1)) ω₀),
        launchChart κ b jumps E (k + 1) ω = launchChart κ b jumps E (k + 1) ω₀ ∧
        launchEntry κ b jumps E (k + 1) u ω = launchEntry κ b jumps E (k + 1) u ω₀ := by
    filter_upwards [CondDriverBridge.ae_ae_run_eq_of_le (P := P) (κ := κ)
      (b := b) (jumps := jumps) w (fun j _ => hreg w j) h𝒢 le_rfl]
      with ω₀ hrun _
    filter_upwards [hrun] with ω hrunω
    refine ⟨?_, (launchEntry_eq_of_run_eq (u := u) hrunω).2⟩
    unfold launchChart
    rw [launches_run_succ_of_run_eq w hrunω]
  exact ⟨fun ω => (I.word ω).fn, fun ω => (I.word ω).jumps,
    fun t ω => (D ω).1 t, fun ω => (D ω).2, hDa,
    ae_remainderLink_of_condDriver_trace h13 hκ h𝒢 hF hDa hfreeze hDr hgeom⟩

/-- The ambient upper launch conclusion follows from the active-word theorem
and the same explicitly named remaining erased-driver input. -/
theorem sb2UpperLaunchEntryLAmbStatement_of_erasedInputs
    (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hword : SB2ActiveWordAmbStatement.{u})
    (hinputs : SB2ErasedDriverInputsStatement h12p) :
    Ly.SB2UpperLaunchEntryLAmbStatement.{u} :=
  sb2UpperLaunchEntryLAmbStatement_of_parts h13 hword
    (sb2DriverLinkAmbStatement_of_erasedInputs h12p h13 hinputs)

end InteractingSLE.Theorem14.SB.Lv
