/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRBoundaryAccess
import InteractingSLE.Spec.Supplement.GW4SafeRBoundaryMean

/-!
# GW4: only the surviving incident boundary limits remain

The actual version assumptions supply the continuous inverse extension. Its
boundary values agree with the canonical `extendFrom` landing. Consequently
the full phase representation follows from limits away from finitely many
physical points, without any separate growth, extension or uniqueness input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdMapInv logDerivFwd)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW4Fix

open Restart Exist.StagedLaw Sec7.PhaseSel Sec7.Aux119Heights
  Supp8.Q3Stop LocalSets WholeField MartChar

/-- **Open boundary input.** The actual mean's corrected limits at surviving
current accesses. Physical exceptions retain all their fibers. Continuous
inverse extension and full-fiber uniqueness are consequences, not fields. -/
def ComponentBoundaryLimits {Ω : Type*} [MeasurableSpace Ω]
    (k : ℝ) (c₀ : BoundaryWord) (F : Frame) (ν : Measure Ω)
    (X : Ω → DistOn upperHalfPlaneOpens) (Wd : ℝ≥0 → Ω → ℝ) (GT : Set Ω)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (u₀ : ℂ → ℝ)
    (B : ℝ≥0 → Ω → Set ℂ) (d : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ t (g : Ω → DistOn upperHalfPlaneOpens), IsLocalSetMean (B t) (centredField X u₀) ν g →
    ∀ᵐ ω ∂ν, lineClock F Wd GT V t ω < V ω →
      let q := (lineClock F Wd GT V t ω).toNNReal
      let inv := fwdMapInv (wpath R ω) q
      let vL := fun i => componentVL k c₀ X R V i q ω - R q ω
      let vR := fun j => componentVR k c₀ X R V j q ω - R q ω
      ∃ E : Set ℂ, E.Finite ∧ ∀ x : ℝ, x ∉ forceJumpSet vL vR →
        extendFrom H inv (x : ℂ) ∉ E →
        Tendsto (fun y => harmRep (g ω) (H \ B t ω) (inv y) + u₀ (inv y) +
            chiC k * (logDerivFwd (wpath R ω) q (inv y)).im)
          (𝓝[H] (x : ℂ))
          (𝓝 (phaseData k (typedRhoL (wordType k c₀)) (typedRhoR (wordType k c₀))
            vL vR (d q ω) x))

/-- Actual relative hull geometry discharges the inverse-extension part of
the incident-germ input. Only the corrected surviving limits are assumed. -/
theorem componentIncidentGerms_of_boundaryLimits {Ω : Type*} [MeasurableSpace Ω]
    {k : ℝ} {c₀ : BoundaryWord} {F : Frame} (hF : F.IsOk) {ν : Measure Ω}
    {X : Ω → DistOn upperHalfPlaneOpens} {Wd R : ℝ≥0 → Ω → ℝ}
    {GT : Set Ω} {V : Ω → ℝ≥0∞} {u₀ : ℂ → ℝ} {B : ℝ≥0 → Ω → Set ℂ}
    {d : ℝ≥0 → Ω → ℝ} (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω))
    (hGTae : ∀ᵐ ω ∂ν, ω ∈ GT) (hver : IsGW4RelVersionR ν Wd F.c F.C R V)
    (hlim : ComponentBoundaryLimits k c₀ F ν X Wd GT R V u₀ B d) :
    ComponentIncidentGerms k c₀ F ν X Wd GT R V u₀ B d := by
  intro t g hg
  filter_upwards [ae_inverse_extension_of_relVersion hF hGT hGTae hver, hlim t g hg]
    with ω hExt hSide hlt
  let q := (lineClock F Wd GT V t ω).toNNReal
  have hq : (q : ℝ≥0∞) < V ω := by
    rw [show (q : ℝ≥0∞) = lineClock F Wd GT V t ω from
      ENNReal.coe_toNNReal (ne_top_of_lt hlt)]
    exact hlt
  obtain ⟨Fb, hFb, hFbc⟩ := hExt q hq
  obtain ⟨E, hE, hs⟩ := hSide hlt
  refine ⟨Fb, E, hFb, hFbc, hE, fun x hx hxE => ?_⟩
  apply hs x hx
  have hland : extendFrom H (fwdMapInv (wpath R ω) q) (x : ℂ) = Fb x := by
    apply extendFrom_eq
    · rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
      exact Sec7.Aux29Cor.real_mem_Hbar x
    · exact Sec7.Aux29Cor.tendsto_inv_of_extension
        (c := Chart.id.loewner (wpath R ω) q) hFb hFbc (Sec7.Aux29Cor.real_mem_Hbar x)
  rwa [hland]

/-- The complete phase-word boundary representation, with no inverse-access,
growth, Poisson-extension or uniqueness premise beyond the actual GW4 context. -/
theorem componentPhaseRepresentation_of_boundaryLimits {Ω : Type*} [MeasurableSpace Ω]
    {k : ℝ} (hk : 0 < k) {c₀ : BoundaryWord} {F : Frame} (hF : F.IsOk)
    {ν : Measure Ω} [IsProbabilityMeasure ν] {X : Ω → DistOn upperHalfPlaneOpens}
    {Wd R : ℝ≥0 → Ω → ℝ} {GT : Set Ω} {V : Ω → ℝ≥0∞}
    {hWm : ∀ r, Measurable (Wd r)} {u₀ : ℂ → ℝ}
    {ℋ : ℝ≥0 → MeasurableSpace Ω} {B : ℝ≥0 → Ω → Set ℂ} {d : ℝ≥0 → Ω → ℝ}
    (hX : IsGFFWithBoundaryData ν X c₀.fn c₀.jumps)
    (hloc : ComponentLineLocality c₀ F ν X Wd GT R V hWm u₀ ℋ B)
    (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω)) (hGTae : ∀ᵐ ω ∂ν, ω ∈ GT)
    (hver : IsGW4RelVersionR ν Wd F.c F.C R V)
    (hlim : ComponentBoundaryLimits k c₀ F ν X Wd GT R V u₀ B d) :
    ComponentPhaseRepresentation k c₀ F ν X Wd GT R V u₀ B d :=
  componentPhaseRepresentation_of_incidentGerms hk hX hloc
    hver.1.1.2.2.1 hver.1.1.2.1
    (componentIncidentGerms_of_boundaryLimits hF hGT hGTae hver hlim)

end InteractingSLE.Theorem14.GW4Fix
