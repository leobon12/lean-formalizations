/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvVPositive
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvVZero
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvVG3

/-!
# R66 converse assembly from the two explicitly remaining mathematical inputs

This is a conditional helper, not an unconditional proof of the successor.
The clock construction and tilt-locality statements are defined in
`FlowStopIdentCMIConvVClock`; every other assembly step is proved.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI

/-- The corrected converse follows from regularized clocks and tilted hull locality. -/
theorem cmiConverseVStatement_of_inputs
    (hclock : CMIVPositiveClockStatement.{u}) (hlocal : CMIVTiltLocalityStatement.{u}) :
    CMIConverseVStatement.{u} := by
  intro κ hκ hκ4 b bR J JR hb hbR O hO hbO N hN hNO V hV hVb hVN
    a c hIO hVI hsN F q hq hFq hFΔ y θ S mS Q₀ hQ₀ H₀ hH s hs hslim
    Λ hΛm hΛ k hk hQ Γ U h' 𝓕₀ W₀ VL₀ VR₀ B₀ htr hC hg hX _W₁ _hpath _hkernel
  let D : CMIVSetting S := {
    κ := κ
    κ_pos := hκ
    κ_lt_four := hκ4
    b := b
    bR := bR
    J := J
    JR := JR
    b_pc := hb
    bR_pc := hbR
    O := O
    O_open := hO
    boundary_eq := hbO
    N := N
    N_open := hN
    N_real := hNO
    V := V
    V_open := hV
    V_bounded := hVb
    closureV_subset := hVN
    a := a
    c := c
    interval_subset := hIO
    closureV_real := hVI
    hull_subset := hsN
    F := F
    q := q
    q_extension := hq
    cutoff_eq := hFq
    cutoff_harmonic := hFΔ
    y := y
    θ := θ
    Q₀ := Q₀
    Q₀_prob := hQ₀
    H₀ := H₀
    H₀_gff := hH
    s := s
    s_bound := hs
    s_limit := hslim
    Λ := Λ
    Λ_measurable := hΛm
    pairing_limit := hΛ
    k := k
    k_pos := hk
    tilt_prob := hQ
    Γ := Γ
    U := U
    h' := h'
    filt := 𝓕₀
    W₀ := W₀
    VL₀ := VL₀
    VR₀ := VR₀
    B₀ := B₀
    translate := htr
    coupling := hC
    trace := hg
    killed := hX }
  change ∃ e', Measurable e' ∧
    (e' =ᵐ[D.Q₀] fun ω => RLC.exitTime D.V (D.Γ ω) (D.U ω)) ∧
    ∃ (ν : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure ν),
      StoppedExtend.IsStoppedFlowLine D.κ D.bR D.JR D.y D.θ (D.tilt.prod ν)
        (fun p => D.shiftedField p.1) (fun p => D.Γ p.1) (fun p => e' p.1)
  by_cases hseed : FlowStopIdentG.SeedStop D.κ D.b D.J D.y D.θ D.V
  · obtain ⟨ν, hν, hc⟩ := D.exists_isStoppedFlowLine_zero
    exact ⟨fun _ => 0, measurable_const, (D.ae_exit_zero hseed).mono (fun _ h => h.symm), ν, hν, hc⟩
  · obtain ⟨C⟩ := hclock D hseed
    obtain ⟨ν, hν, hc⟩ := C.exists_isStoppedFlowLine hlocal
    exact ⟨C.e, C.measurable, C.ae_exit, ν, hν, hc⟩

end InteractingSLE.Restart.FlowStopIdentCMI

namespace InteractingSLE.RLC
open Restart.FlowStopIdentCMI

/-- G3 uses the corrected converse, conditional on its two remaining mathematical inputs. -/
theorem g3SourceStatement_of_CMIVInputs
    (hclock : CMIVPositiveClockStatement.{0}) (hlocal : CMIVTiltLocalityStatement.{0})
    (hT : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ThroughKernelStatement.{0, 0} κ)
    (h12p : Exist.Staged.Theorem12ParamStatement.{0}) (h13 : Exist.Theorem13Statement.{0}) :
    G3SourceStatement.{0} :=
  g3SourceStatement_of_CMIConverseV (cmiConverseVStatement_of_inputs hclock hlocal) hT h12p h13

end InteractingSLE.RLC
