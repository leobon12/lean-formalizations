import QuantumZipper.Proofs.Zipper.XAreaPCLog
import QuantumZipper.Proofs.Zipper.XAreaPCEnergy
import QuantumZipper.Proofs.GFF.SmoothingConvergence
import QuantumZipper.Proofs.LQG.CoordChangeSmooth
import QuantumZipper.Proofs.Zipper.WedgeUnzipScale
import QuantumZipper.Proofs.RS.TraceShift
import QuantumZipper.Proofs.Zipper.JointModRandom
import QuantumZipper.Proofs.Zipper.RegContRandom
import QuantumZipper.Proofs.Thm12.CharFun
import QuantumZipper.Proofs.Zipper.MeasUnzipFlow

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X-A-pc: the measurability node `XPCMeasStmt`

Main result: `xPCMeasStmt_holds : XPCMeasStmt`.

For `f ∈ PZ` (driver `W = Wof κ T hT f` with `W 0 = 0`), `t ∈ [0,T]`, `z ∈ ℍ`:

* the pushed circle `muP = fc(z, r).map ψ` equals `fc(z, r).map (flowJ f (t, ·))`, since `fc(z, r)`
  lives a.e. on `ℍ` (`TwoPoint.foldedCircle_ae_mem_H`) where `flowJ` is `ψ = f_t⁻¹`; `flowJ` is
  jointly measurable (`MeasUnzip.measurable_flowJ`);
* the image circle `muI = fc(c, ρ)` with `c = f_t⁻¹(z) = Fm(revPath f, z)` and
  `ρ = r ‖(f_t⁻¹)'(z)‖ = r ‖Dm(revPath f, z)‖` is the image of the fixed measure
  `(2π)⁻¹ Leb|[0,2π)` under `θ ↦ foldH (circleMap c ρ θ)`, jointly measurable in `(f, θ)`.

Then `evalReg (x + ℓ) (ν.map ψ_p)` is measurable in the parameter for jointly measurable `ψ`
(limit of partial integrals, as in `G1Meas.measurable_evalReg_map_param`), and the `if` is handled
by `Measurable.ite` on the measurable set `PZ`. Own elementary bookkeeping (no published source
needed: standard measurability of parametric integrals, mathlib `integral_prod_right'`).
-/

noncomputable section

open MeasureTheory Filter Set

namespace QuantumZipper.E6
namespace XAreaPC

open CharFun RegCont UnzipInvariance MeasUnzip

/-- `evalReg` of a parameter-dependent field at the image of a fixed s-finite measure (on any
measurable space) under a jointly measurable parameter-dependent map is measurable. -/
theorem measurable_evalReg_map_gen {Z α : Type*} [MeasurableSpace Z] [MeasurableSpace α]
    {y : Z → FieldSample} (hy : Measurable y) {ψ : Z → α → ℂ}
    (hψ : Measurable fun p : Z × α => ψ p.1 p.2) (ν : Measure α) [SFinite ν] :
    Measurable fun p => evalReg (y p) (ν.map (ψ p)) := by
  have hψp : ∀ p, Measurable (ψ p) := fun p => hψ.comp (measurable_const.prodMk measurable_id)
  have e : ∀ p (k : ℕ), ∫ w, avgReg (y p) k w ∂(ν.map (ψ p)) =
      ∫ z, avgReg (y p) k (ψ p z) ∂ν := fun p k =>
    integral_map (hψp p).aemeasurable
      ((measurable_avgReg k).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hk : ∀ k : ℕ, StronglyMeasurable fun p => ∫ z, avgReg (y p) k (ψ p z) ∂ν := fun k =>
    StronglyMeasurable.integral_prod_right'
      (f := fun q : Z × α => avgReg (y q.1) k (ψ q.1 q.2))
      ((measurable_avgReg k).comp ((hy.comp measurable_fst).prodMk hψ)).stronglyMeasurable
  unfold evalReg
  simp_rw [e]
  exact (StronglyMeasurable.limUnder hk).measurable

/-- The normalized Lebesgue measure on `[0, 2π)`. -/
def angMeas : Measure ℝ := (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Ico 0 (2 * Real.pi))

/-- The folded circle as the image of the fixed measure `angMeas`. -/
theorem foldedCircle_eq_map_angMeas (c : ℂ) (ρ : ℝ) :
    foldedCircle c ρ = angMeas.map fun θ => foldH (circleMap c ρ θ) := by
  unfold foldedCircle circleUnif angMeas
  rw [Measure.map_smul, Measure.map_smul, Measure.map_map measurable_foldH (measurable_circleMap _ _)]
  · rfl
  · exact (measurable_foldH.comp (measurable_circleMap _ _)).aemeasurable
  · exact measurable_foldH.aemeasurable

instance sFinite_angMeas : SFinite angMeas := by
  unfold angMeas; infer_instance

end XAreaPC
end QuantumZipper.E6
