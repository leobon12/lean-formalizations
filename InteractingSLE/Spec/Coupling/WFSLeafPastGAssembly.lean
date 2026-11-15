/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafPastGProcess
import QuantumZipper.Proofs.Probability.GermZeroOne

/-!
# WFS from the continuous closed process and its initial scalar mean

The former raw-past comparison at every dyadic time is derived. Only the
initial conditional mean remains as a separate input. Its constancy follows
from triviality of the actual driving germ, but that germ identification is
not proved here.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WFS

open LawUnique Restart.StoppedExtendWF LQGMetric

/-- Conditioning on a trivial sigma algebra gives a constant conditional mean.
This is the existing independence characterization specialized to triviality. -/
theorem exists_condExp_constant_of_trivialSigma
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (htriv : QuantumZipper.GermZeroOne.IsTrivialSigma (mΩ := mΩ) m P)
    {Z : Ω → ℝ} (hZ : StronglyMeasurable[mΩ] Z) :
    ∃ c : ℝ, P[Z | m] =ᵐ[P] fun _ => c :=
  ⟨∫ ω, Z ω ∂P, condExp_indep_eq le_rfl hm hZ (htriv.indep (mΩ := mΩ) hm).symm⟩

/-- Remaining initial-time input. Only the conditional mean of the bounded
lifetime discount at time zero is required to be a.e. constant. -/
def InitialSurvivalMeanStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR →
    ∀ R : HistorySpace nL nR → ℝ≥0∞, Measurable R → IsHistGalmarino R →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
      (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ V : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens)
      (hC : IsCouplingThrough κ xL xR ρL ρR P 𝓕 W VL VR B ζ V h),
      (∀ᵐ ω ∂P, V ω = R (killedHistory W VL VR V ω)) →
      (∀ᵐ ω ∂P, 0 < V ω) →
      ∃ c : ℝ, P[fun ω => survivalDiscount (V ω) | drivingFiltration P hC.2.2.2.2.choose 0] =ᵐ[P]
        fun _ => c

/-- The previous all-dyadic raw-past input follows from continuity of the
closed process and its a.e. constant initial value. -/
theorem survivalPastCondExpStatement_of_closedProcess_initial
    {κ : ℝ} (hκ : 0 < κ) (hclosed : ContinuousClosedSurvivalProcessStatement.{u} κ)
    (hinitial : InitialSurvivalMeanStatement.{u} κ) : SurvivalPastCondExpStatement.{u} κ := by
  intro nL nR xL xR ρL ρR hF R hm hgal Ω mΩ P hP 𝓕 W VL VR B ζ V h hC hself hpos
  obtain ⟨X, hXa, hXc, hXe⟩ := hclosed xL xR ρL ρR hF R hm hgal P 𝓕 W VL VR B ζ V h hC hself hpos
  obtain ⟨c, hc0⟩ := hinitial xL xR ρL ρR hF R hm hgal P 𝓕 W VL VR B ζ V h hC hself hpos
  have hc : ∀ᵐ ω ∂P, ContinuousOn (Restart.Aux54.dState W VL VR ω) {t | (t : ℝ≥0∞) < V ω} := by
    filter_upwards [hC.1.isSLEEvolutionUpTo.ae_path] with ω hp
    exact (continuousOn_state_of_isSLEPathUpTo hp).mono (fun t ht => ht.trans_le (hC.2.1 ω))
  intro p
  exact condExp_driving_eq_rawPast_of_initial hC.2.2.2.2.choose hc
    (ae_nonzero_dyadic_killedHistory hκ hC) hXa hXc ⟨c, (hXe 0).trans hc0⟩ hXe (dyadicTime p)

/-- The unchanged WFS target from continuous closed-process existence and the
single initial-mean input. No positive-time raw-past comparison is assumed. -/
theorem throughKernelStatement_of_closedProcess_initial
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hclosed : ContinuousClosedSurvivalProcessStatement.{u} κ)
    (hinitial : InitialSurvivalMeanStatement.{u} κ) : ThroughKernelStatement.{u, u} κ :=
  throughKernelStatement_of_closedSurvivalProcess h12 h13 hκ hclosed
    (survivalPastCondExpStatement_of_closedProcess_initial hκ hclosed hinitial)

end InteractingSLE.WFS
