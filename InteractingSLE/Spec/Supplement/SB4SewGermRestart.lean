/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4SewGermPath
import InteractingSLE.Spec.Restart.StagedEntranceInst

/-!
# StagedEntrance with the past determination, kernel and frontier supplied

The past is a Borel reconstruction of its staged record. The reverse decoder
gives the kernel identity, and the physical complement formula for the launch
chart gives its frontier condition. The trace reconstruction hypotheses and
the positive-time interior condition of the landed restart theorem remain
explicit; this does not assert that arbitrary real-contact stages satisfy it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.SewGerm

open Exist.Staged Sec6
open Restart.StagedEntrance (frozenPath)

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- Apply the landed staged restart after deriving three of its inputs from
the actual labelled path reconstruction and the physical chart domain. -/
theorem isEntranceHistoryLocal_staged_of_pathRecords
    (h12p : Exist.Staged.Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (k : ℕ) (θ : ℝ)
    {α : Ω → ℝ≥0 → ℂ} {x : ℂ} (hxH : x ∉ H) (hαc : ∀ ω, Continuous (α ω))
    (hα0 : ∀ ω, α ω 0 = x) (hαm : ∀ t, Measurable fun ω => α ω t)
    {q₀ : ℚ≥0} (m : ℝ≥0) {r : ℝ≥0 → PastData k → ℂ}
    (hrm : ∀ t, Measurable (r t))
    (hr : ∀ t : ℝ≥0, (fun ω => frozenPath (α ω) q₀ t) =ᵐ[P]
      fun ω => r t (pastMap κ b jumps spec E k ω))
    {ψ : (Fin 1 → Hist) → PastData k} (hψ : Measurable ψ)
    (hrec : pastMap κ b jumps spec E k =ᵐ[P] fun ω => ψ (frozenHistory α q₀ ω))
    (hloc₀ : IsEntranceHistoryLocal (fun ω => frozenPath (α ω) q₀)
      (WholeField.centredField h u₀) P)
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hℓ : ∀ ω, LocallyIntegrableOn (fun w => (c ω).2.2 ((c ω).2.1 w)) H)
    (hlaunch : ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k =
      some (c ω, θ))
    (hdom : ∀ ω, ∃ z₀ : ℂ, ((c ω).dom : Set ℂ) =
      connectedComponentIn (H \ (α ω '' Icc 0 (q₀ : ℝ≥0))) z₀)
    {β ηc : Ω → ℝ≥0 → ℂ} (hηc : ∀ ω, Continuous (ηc ω))
    (hηm : ∀ t, Measurable fun ω => ηc ω t) (hη0 : ∀ ω, ηc ω 0 = 0)
    (htrβ : ∀ᵐ ω ∂P, IsGeneratingTrace (E k ω).1 (E k ω).2 (β ω))
    (hηβ : ∀ᵐ ω ∂P, ∀ t, ηc ω t = β ω (Restart.capTime m (E k ω).2 t))
    (hdetη : ∀ᵐ ω₀ ∂P, ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => ηc ω t) =ᵐ[condExpKernel P (Restart.StagedEntrance.pastSigma α q₀) ω₀]
        fun ω => f (Chart.chartTransport (hc ω₀) 1 0 (chiC κ) (h ω)))
    (hcat : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, 0 < s → ηc ω s ∈ H ∧
      frozenPath (α ω) ((q₀ : ℝ≥0) + m) ((q₀ : ℝ≥0) + s) = (c ω).2.1 (ηc ω s)) :
    IsEntranceHistoryLocal (fun ω => frozenPath (α ω) ((q₀ : ℝ≥0) + m))
      (WholeField.centredField h u₀) P := by
  have hdet₀ := frozenPath_determined_of_staged h12p h13 hκ hκ4 hb hh hE hR u₀ hrm hr
  have hK := ae_condExpKernel_stage_eq_path hE hαm hrm hr hψ hrec
  have hfr : ∀ ω, ∀ z ∈ H, z ∈ closure ((c ω).dom : Set ℂ) →
      z ∉ (c ω).dom → z ∈ α ω '' Icc 0 (q₀ : ℝ≥0) := by
    intro ω
    obtain ⟨z₀, hz₀⟩ := hdom ω
    exact Restart.StagedEntrance.mem_of_mem_closure_dom
      (isCompact_Icc.image (hαc ω)).isClosed hz₀
  exact Restart.StagedEntrance.Staged.isEntranceHistoryLocal_frozenPath_staged hκ hκ4 hh hu₀
    hE hreg k θ hxH hαc hα0 hαm m hdet₀ hloc₀ hK hc hℓ hlaunch hfr
    hηc hηm hη0 htrβ hηβ hdetη hcat

end InteractingSLE.Theorem14.SB.SewGerm
