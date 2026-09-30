import QuantumZipper.Proofs.Section5.Prop16Area

/-!
# Proposition 1.6, node D4-MEAS (part 1): D4-a with countable-coordinate measurability

`Prop16Area.areaConvergesInLawOn_of_tvLocal` (D4-a) asks for `AEMeasurable (Y c) P` into
`FieldSample = Measure ℂ → ℝ` with the product σ-algebra over *all* measures `μ`, including
non-s-finite ones, at which parameter integrals need not be measurable; for the zoomed canonical
fields of Proposition 1.6 this is out of reach (and not needed). Every LQG quantity used by D4-a
depends on the sample only through `avgReg`, hence only through the countably many raw
coordinates `Factorization.coords`. Replacing `Y c ω` by `reconstruct (coords (Y c ω))`
(blueprint A4) leaves all area measures and all local coordinates unchanged, so D4-a holds with

* `hY` replaced by `AEMeasurable (fun ω => coords (Y c ω)) P`, and
* TV-local convergence stated for the laws of the local coordinates `locField R ∘ Y c` directly.

Own elementary argument (measurability plumbing; AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Area

open TV Factorization

/-- The reconstruction of a sample from its raw coordinates. -/
abbrev recon (x : FieldSample) : FieldSample := reconstruct (coords x)

theorem coords_recon (x : FieldSample) : coords (recon x) = coords x := by
  funext i
  exact reconstruct_coords_apply x i

theorem locField_recon (R : ℕ) (x : FieldSample) : locField R (recon x) = locField R x := by
  funext n
  simp only [locField, coords_recon]

theorem areaApprox_recon (γ : ℝ) (x : FieldSample) : areaApprox γ (recon x) = areaApprox γ x := by
  funext k
  simp only [areaApprox, avgReg_reconstruct_coords]

theorem qAreaMeasureOn_recon (γ : ℝ) (x : FieldSample) (U : Set ℂ) :
    qAreaMeasureOn γ (recon x) U = qAreaMeasureOn γ x U := by
  unfold qAreaMeasureOn; rw [areaApprox_recon]

theorem qAreaMeasure_recon (γ : ℝ) (x : FieldSample) :
    qAreaMeasure γ (recon x) = qAreaMeasure γ x := by
  unfold qAreaMeasure; rw [areaApprox_recon]

end Prop16Area

end QuantumZipper
