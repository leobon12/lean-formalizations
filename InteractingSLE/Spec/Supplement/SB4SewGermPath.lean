/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4SewLawUnion
import InteractingSLE.Spec.Supplement.KernelTower2
import InteractingSLE.Spec.Restart.StagedEntranceStaged
import InteractingSLE.Spec.Sec7.StripMark

/-!
# Staged records and continuous retained paths

This file supplies the field-determination and conditional-kernel identity
needed by StagedEntrance from Borel reconstruction of a finite path from its
staged record, and reconstruction of the record from that labelled path.
Entrance-history locality then gives the stage's marked locality. The actual
continuous parametrization and its reconstruction maps are explicit inputs.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.SewGerm

open Exist.Staged LocalSets
open Restart.StagedEntrance (frozenPath)

/-- The stopped history used by StagedEntrance for a continuous retained path. -/
def frozenHistory {Ω : Type u} (α : Ω → ℝ≥0 → ℂ) (T : ℝ≥0) : Ω → Fin 1 → Sec6.Hist :=
  fun ω _ => Sec6.histOf (Sec6.pathCoord (frozenPath (α ω) T)) (T : ℝ≥0∞)

/-- The same history encoded directly from the finite staged record. -/
def encodedHistory {k : ℕ} (r : ℝ≥0 → PastData k → ℂ) (T : ℝ≥0) :
    PastData k → Fin 1 → Sec6.Hist :=
  fun R _ => Sec6.histOf (fun q => r (q : ℝ≥0) R) (T : ℝ≥0∞)

theorem measurable_encodedHistory {k : ℕ} {r : ℝ≥0 → PastData k → ℂ}
    (hrm : ∀ t, Measurable (r t)) (T : ℝ≥0) : Measurable (encodedHistory r T) :=
  measurable_pi_iff.2 fun _ => Sec6.measurable_histOf.comp
    (measurable_const.prodMk (measurable_pi_iff.2 fun q => hrm (q : ℝ≥0)))

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {α : Ω → ℝ≥0 → ℂ} {T : ℝ≥0}
  {r : ℝ≥0 → PastData k → ℂ}

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- Countably many rational coordinates identify the entire stopped history. -/
theorem ae_frozenHistory_eq_encodedHistory
    (hr : ∀ t : ℝ≥0, (fun ω => frozenPath (α ω) T t) =ᵐ[P]
      fun ω => r t (pastMap κ b jumps spec E k ω)) :
    frozenHistory α T =ᵐ[P] fun ω => encodedHistory r T (pastMap κ b jumps spec E k ω) := by
  have hall : ∀ᵐ ω ∂P, ∀ q : ℚ≥0,
      frozenPath (α ω) T (q : ℝ≥0) = r (q : ℝ≥0) (pastMap κ b jumps spec E k ω) :=
    ae_all_iff.2 fun q => hr (q : ℝ≥0)
  filter_upwards [hall] with ω hω
  funext i
  apply congrArg (fun c => Sec6.histOf c (T : ℝ≥0∞))
  funext q
  exact hω q

/-- The kernel identity required by StagedEntrance follows from the two Borel
record reconstructions; it need not be assumed as an equality of kernels. -/
theorem ae_condExpKernel_stage_eq_path
    (hE : IsStagedHistory κ b jumps P h spec E)
    (hαm : ∀ t, Measurable fun ω => α ω t) (hrm : ∀ t, Measurable (r t))
    (hr : ∀ t : ℝ≥0, (fun ω => frozenPath (α ω) T t) =ᵐ[P]
      fun ω => r t (pastMap κ b jumps spec E k ω))
    {ψ : (Fin 1 → Sec6.Hist) → PastData k} (hψ : Measurable ψ)
    (hrec : pastMap κ b jumps spec E k =ᵐ[P] fun ω => ψ (frozenHistory α T ω)) :
    ∀ᵐ ω ∂P, condExpKernel P (_root_.InteractingSLE.pastSigma κ b jumps spec E k) ω =
      condExpKernel P (Restart.StagedEntrance.pastSigma α T) ω :=
  KernelTower.ae_condExpKernel_comap_eq (Measurable.of_comap_le (hE.2.1 k))
    (Restart.StagedEntrance.measurable_pastHist hαm) hψ (measurable_encodedHistory hrm T)
    hrec (ae_frozenHistory_eq_encodedHistory hr)

/-- A continuous parametrization reconstructed from the actual staged record
is determined by the centred field, using Theorems 1.2--1.3 only. -/
theorem frozenPath_determined_of_staged
    (h12p : Exist.Staged.Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) (u₀ : ℂ → ℝ)
    (hrm : ∀ t, Measurable (r t))
    (hr : ∀ t : ℝ≥0, (fun ω => frozenPath (α ω) T t) =ᵐ[P]
      fun ω => r t (pastMap κ b jumps spec E k ω)) (t : ℝ≥0) :
    ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => frozenPath (α ω) T t) =ᵐ[P]
        fun ω => f (WholeField.centredField h u₀ ω) := by
  obtain ⟨f, hfm, hfe⟩ :=
    StagedDet.exists_pastMap_eq_comp_field h12p h13 hκ hκ4 hb hh hE hR k
  refine ⟨fun X => r t (f (X + SupercriticalConformalCovariance.GM24.smoothDist
    upperHalfPlaneOpens u₀)), (hrm t).comp
      (hfm.comp (Coupling.measurable_add_distOnConst _)), ?_⟩
  filter_upwards [hr t, hfe] with ω hrω hfω
  simp only [hrω, hfω, WholeField.centredField, sub_add_cancel, Function.comp_apply]

/-- Discharge one of the two stage marked-locality inputs using the retained
continuous path and its entrance-history locality. The record decoder preserves
all labels and flags; no assertion about them follows from the range alone. -/
theorem isHistoryAvoidanceLocal_stage_of_path
    (h12p : Exist.Staged.Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) (u₀ : ℂ → ℝ)
    (hαc : ∀ ω, Continuous (α ω)) {x : ℂ} (hα0 : ∀ ω, α ω 0 = x)
    (hαm : ∀ t, Measurable fun ω => α ω t) (hrm : ∀ t, Measurable (r t))
    (hr : ∀ t : ℝ≥0, (fun ω => frozenPath (α ω) T t) =ᵐ[P]
      fun ω => r t (pastMap κ b jumps spec E k ω))
    {ψ : (Fin 1 → Sec6.Hist) → PastData k} (hψ : Measurable ψ)
    (hrec : pastMap κ b jumps spec E k =ᵐ[P] fun ω => ψ (frozenHistory α T ω))
    (hset : ∀ᵐ ω ∂P, α ω '' Icc 0 T ∩ H = WalkLaw.stageSet κ b jumps spec E k ω)
    (hentr : Sec6.IsEntranceHistoryLocal
      (fun ω => frozenPath (α ω) T) (WholeField.centredField h u₀) P) :
    WholeField.IsHistoryAvoidanceLocal (_root_.InteractingSLE.pastSigma κ b jumps spec E k)
      (WalkLaw.stageSet κ b jumps spec E k) (WholeField.centredField h u₀) P := by
  have hdet := frozenPath_determined_of_staged h12p h13 hκ hκ4 hb hh hE hR u₀ hrm hr
  have hp := Sec6.isHistoryAvoidanceLocal_explored
    (η := fun _ : Fin 1 => fun ω => frozenPath (α ω) T) (x := fun _ => x)
    (τ := fun _ _ => (T : ℝ≥0∞)) (S := fun _ _ _ => (T : ℝ≥0∞))
    (WholeField.measurable_centredField hh.1 u₀)
    (fun _ ω => Restart.StagedEntrance.continuous_frozenPath (hαc ω))
    (fun _ ω => by rw [Restart.StagedEntrance.frozenPath_zero]; exact hα0 ω)
    (fun _ t => hαm _) (fun _ => hdet) (fun _ => hentr)
    (fun _ => measurable_const) (fun _ _ _ _ _ => rfl) (fun _ _ => rfl)
  rw [show Sec6.explored (fun _ : Fin 1 => fun ω => frozenPath (α ω) T)
    (fun _ _ => (T : ℝ≥0∞)) = fun ω => α ω '' Icc 0 T ∩ H from
      funext Restart.StagedEntrance.explored_frozenPath] at hp
  have hle := KernelTower.comap_le_aeSigma_comap hψ hrec
  exact WalkLaw.isHistoryAvoidanceLocal_congr_ae hset
    (Sec7.StripMark.isHistoryAvoidanceLocal_of_ae_le hp fun F hF => hle F hF)

end InteractingSLE.Theorem14.SB.SewGerm
