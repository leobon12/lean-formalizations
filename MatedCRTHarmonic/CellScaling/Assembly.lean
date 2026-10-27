import Mathlib
import MatedCRTHarmonic.MesoModel.Meso
import MatedCRTHarmonic.CellScaling.CellCount
import MatedCRTHarmonic.CellScaling.Scaling

/-!
# Scaling and cell-count estimates for the unit-mesh model

For a unit-mesh model `M` (`MesoModel.MatedCRTUnitMesoModel γ`) realized by the SLE/LQG cone data
(`ConeRealization M`):
* `matedCRTProposition24RadiusInput_of_cone` — **the cone-radius asymptotic**, no input beyond the cone's definition;
* `matedCRTProposition23GridScalingInput_of_cone` (in `CellScaling.Scaling`) — **the joint-scaling identity**;
* `matedCRTProposition25CellCountInput_of_cone` (in `CellScaling.CellCount`) — **the cell-count bound**;
* `unitCellDiamEventually_of_cellFamily` — the cell-diameter clause that the cell-count bound needs, from the same chain as
  `hEventuallyScaled` (the joint-scaling identity + the scaled-grid estimate + Borel–Cantelli);
* `unitMesoscopicOutput_of_cone` — `unitMesoscopicOutput_of_interfaces` (`UnitMesoscopicOutput`)
  with its inputs `h23, h24, h25` discharged, and `cellModelExists_of_cone` (with the recurrence input);
* `matedCRTUnitMesoscopicInput_of_cone` — the same in the single-coupling form.

The scaled-grid estimate enters in its bad-event form, so no measurability of the mesh
events and no Borel premise on the unit event is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellScaling

open MatedCRTHarmonic

/-- **Cone-radius asymptotic** in the interface form `MesoModel.MatedCRTProposition24RadiusInput`: for the cone
realization, a.s. `log₂ R_{2^k} / k → a_γ`. Needs only that `B'` is a Brownian motion (the definition of the cone). -/
theorem matedCRTProposition24RadiusInput_of_cone {γ : ℝ} {M : MesoModel.MatedCRTUnitMesoModel γ}
    (D : ConeRealization M) : MesoModel.MatedCRTProposition24RadiusInput M := by
  filter_upwards [ae_tendsto_logb_coneScale M.hγ.1 M.hγ.2 D.B D.brownian', D.radius_eq] with ω h hrad
  have hfun : (fun k : ℕ => Real.logb 2 (M.radius ω k) / k) =
      (fun k : ℕ => Real.logb 2 (coneScale γ γ (fun t => D.B t ω) (fun t => D.B' t ω) (2 ^ k)) / k) := by
    funext k
    rw [hrad k]
  rw [hfun]
  exact h

private theorem assembly_mesh_eq_rpow (k : ℕ) : CellFamily.mesh k = (2 : ℝ) ^ (-(k : ℝ)) := by
  simp [CellFamily.mesh, zpow_neg, zpow_natCast, Real.rpow_neg, Real.rpow_natCast]

private theorem assembly_summable_mesh_rpow {α C : ℝ} (hα : 0 < α) :
    Summable (fun k : ℕ => C * (CellFamily.mesh k) ^ α) := by
  have hr0 : 0 ≤ (2 : ℝ) ^ (-α) := by positivity
  have hr1 : (2 : ℝ) ^ (-α) < 1 := by
    calc (2 : ℝ) ^ (-α) < (2 : ℝ) ^ (0 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
      _ = 1 := by simp
  refine ((summable_geometric_of_lt_one hr0 hr1).mul_left C).congr (fun k => ?_)
  rw [assembly_mesh_eq_rpow, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 2
  ring

/-- **The mesh-level scaled-grid bound** for the model's random family, in bad-event form: the outer measure of the failure of `ScaledGridControl` at `q, ρ` is at most
`C ε_k^α` (the conclusion of `CellFamily.cellFamily_compl_of_interfaces_bad`). No measurability conjunct. -/
def CellFamilyMeshOutput {γ : ℝ} (M : MesoModel.MatedCRTUnitMesoModel γ) : Prop :=
  ∃ χ β α p₀ C : ℝ, 0 < α ∧ ∀ k : ℕ,
    M.coupled.family.P {ω | (M.coupled.family.H k ω).ScaledGridControl 1 (CellFamily.mesh k) χ β M.q M.ρ p₀}ᶜ ≤
      ENNReal.ofReal (C * CellFamily.mesh k ^ α)

/-- The corrected scaled-grid interfaces give `CellFamilyMeshOutput` (`cellFamilyCompl_of_interfaces`). -/
theorem cellFamilyMeshOutput_of_interfaces {γ : ℝ} (M : MesoModel.MatedCRTUnitMesoModel γ)
    (h26 : MesoModel.MatedCRTCellFamilyInterfaces M) : CellFamilyMeshOutput M := by
  obtain ⟨χ, β, α, p₀, C, -, -, -, hα, -, hScaled⟩ := MesoModel.cellFamilyCompl_of_interfaces M h26
  exact ⟨χ, β, α, p₀, C, hα, hScaled⟩

/-- The unit-scale scaled-grid event holds almost surely for all large `k`, by joint scaling,
the mesh-level bad-event bound, and Borel–Cantelli. Hence `UnitCellDiamEventually M`. -/
theorem unitCellDiamEventually_of_cellFamily {γ : ℝ} (M : MesoModel.MatedCRTUnitMesoModel γ)
    (h23 : MesoModel.MatedCRTProposition23GridScalingInput M) (h26 : CellFamilyMeshOutput M) :
    UnitCellDiamEventually M := by
  obtain ⟨χ, β, α, p₀, C, hα, hScaled⟩ := h26
  set BadUnit : ℕ → Set M.coupled.family.Ω := fun k =>
    {ω | ¬ (M.unitEmbedding ω).ScaledGridControl (M.radius ω k) (CellFamily.mesh k) χ β M.q M.ρ p₀}
  have hbound : ∀ k, M.coupled.family.P (BadUnit k) ≤
      ENNReal.ofReal (max 0 C * (CellFamily.mesh k) ^ α) := by
    intro k
    have hmesh : 0 < CellFamily.mesh k := by unfold CellFamily.mesh; positivity
    calc M.coupled.family.P (BadUnit k) = M.coupled.family.P
          {ω | ¬ (M.coupled.family.H k ω).ScaledGridControl 1 (CellFamily.mesh k) χ β M.q M.ρ p₀} :=
          h23 k χ β p₀
      _ ≤ ENNReal.ofReal (C * (CellFamily.mesh k) ^ α) := hScaled k
      _ ≤ ENNReal.ofReal (max 0 C * (CellFamily.mesh k) ^ α) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right 0 C)
            (Real.rpow_nonneg (le_of_lt hmesh) α))
  have hae := Growth.ae_eventually_notMem_of_real_summable_bound M.coupled.family.P BadUnit
    (fun k => max 0 C * (CellFamily.mesh k) ^ α)
    (fun k => mul_nonneg (le_max_left 0 C) (Real.rpow_nonneg (by unfold CellFamily.mesh; positivity) α))
    (assembly_summable_mesh_rpow hα) hbound
  apply unitCellDiamEventually_of_scaledGrid M (χ := χ) (β := β) (p₀ := p₀)
  filter_upwards [hae] with ω hω
  filter_upwards [hω] with k hk
  simp only [BadUnit, mem_ofPred_eq, not_not] at hk
  rw [← assembly_mesh_eq_rpow]
  exact hk

/-- **The unit-mesh mesoscopic output conditional on the named inputs.**
`unitMesoscopicOutput_of_interfaces` uses `h23, h24, h25` produced here. Inputs are the
SLE-dependent bundle inputs `ConeJointScaling`, `BoundaryLengthCovariance`, `AreaParametrization`; the SLE-free
inputs to prove `AreaScalingLaw`, `AreaBallMoment`, `MeshGridEventMeasurable`; and the corrected scaled-grid estimate
interfaces. No Borel premise on the unit event. -/
theorem unitMesoscopicOutput_of_cone {γ : ℝ} (M : MesoModel.MatedCRTUnitMesoModel γ)
    (D : ConeRealization M) (h23 : ConeJointScaling D) (hBL : BoundaryLengthCovariance D)
    (hpar : AreaParametrization D) (hscale : AreaScalingLaw D) (hmom : AreaBallMoment D)
    (hmeas : MeshGridEventMeasurable) (h26 : MesoModel.MatedCRTCellFamilyInterfaces M) :
    MesoModel.UnitMesoscopicOutput M := by
  have hgrid := matedCRTProposition23GridScalingInput_of_cone D h23 hBL hmeas
  have hdiam := unitCellDiamEventually_of_cellFamily M hgrid (cellFamilyMeshOutput_of_interfaces M h26)
  exact MesoModel.unitMesoscopicOutput_of_interfaces M hgrid
    (matedCRTProposition24RadiusInput_of_cone D)
    (matedCRTProposition25CellCountInput_of_cone D hpar hscale hmom hdiam) h26

/-- **`CellModelExists γ`, conditional on the named inputs:** compose `unitMesoscopicOutput_of_cone`
with `MesoModel.cellModelExists_of_inputs` and the recurrence input. -/
theorem cellModelExists_of_cone {γ : ℝ} (M : MesoModel.MatedCRTUnitMesoModel γ)
    (D : ConeRealization M) (h23 : ConeJointScaling D) (hBL : BoundaryLengthCovariance D)
    (hpar : AreaParametrization D) (hscale : AreaScalingLaw D) (hmom : AreaBallMoment D)
    (hmeas : MeshGridEventMeasurable) (h26 : MesoModel.MatedCRTCellFamilyInterfaces M)
    (hrec : MesoModel.MatedCRTRecurrenceInput γ) : MatedCRT.CellModelExists γ :=
  MesoModel.cellModelExists_of_inputs M
    (unitMesoscopicOutput_of_cone M D h23 hBL hpar hscale hmom hmeas h26) hrec

end MatedCRTHarmonic.CellScaling
