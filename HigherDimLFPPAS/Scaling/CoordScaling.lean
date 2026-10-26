import HigherDimLFPPAS.Core.Interfaces
import HigherDimLQGMetric.Metric.WeylAxioms
import HigherDimLQGMetric.Sphere.Scaling

/-!
# Coordinate scaling in the paper's recentered form

The strong metric coordinate axiom and its constant Weyl rule give the scale factor. The
almost-sure affine sphere-average identity identifies the recentering constant with `h_r(z)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLFPPAS.Scaling

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

theorem coordScaling_holds {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Core.Setting d ξ Q κ D P h) : Core.CoordScaling ξ Q D P h := by
  intro r hr z
  let g : Ω → DistRd d := fun ω => recentAff r z (h ω)
  have hwhole : IsWholeSpaceLGF h P := hS.field.1
  have hgNorm : IsNormalizedLGF g P :=
    isNormalizedLGF_recentAff (le_trans (by norm_num) hS.dim) hwhole hr z
  have hg : IsWholeSpaceLGF g P := hgNorm.1
  filter_upwards [hS.strong.coord P h hwhole.isLGFPlusCont r hr z,
    hS.strong.ae_apply_addFun_const hg.isLGFPlusCont,
    hwhole.ae_sphereAvg_affineComp (le_trans (by norm_num) hS.dim) hr z one_pos 0]
    with ω hcoord hw hsphere
  intro u v
  let c : ℝ := sphereAvg (h ω) r z
  have hs : sphereAvg (affineComp r z (h ω)) 1 0 = c := by
    simpa only [c, mul_one, smul_zero, zero_add] using hsphere
  have hcoord' := hcoord u v
  have hw' := hw (c + Q * Real.log r) u v
  have he : addConst (g ω) (c + Q * Real.log r) =
      addConst (affineComp r z (h ω)) (Q * Real.log r) := by
    dsimp [g, recentAff]
    rw [addConst_addConst, hs]
    congr 1
    ring
  rw [addFun_const, he] at hw'
  have hexp : Real.exp (ξ * (c + Q * Real.log r)) =
      r ^ (ξ * Q) * Real.exp (ξ * c) := by
    rw [mul_add, Real.exp_add, Real.rpow_def_of_pos hr]
    rw [show ξ * (Q * Real.log r) = Real.log r * (ξ * Q) by ring]
    ring
  calc
    (D (h ω)).1 (z + r • u, z + r • v) =
        (D (h ω)).1 (r • u + z, r • v + z) :=
      congrArg (D (h ω)).1 (Prod.ext (add_comm _ _) (add_comm _ _))
    _ = (D (addConst (affineComp r z (h ω)) (Q * Real.log r))).1 (u, v) := hcoord'
    _ = Real.exp (ξ * (c + Q * Real.log r)) * (D (g ω)).1 (u, v) := hw'
    _ = r ^ (ξ * Q) * Real.exp (ξ * c) * (D (g ω)).1 (u, v) := by rw [hexp]
    _ = r ^ (ξ * Q) * Real.exp (ξ * sphereAvg (h ω) r z) *
        (D (recentAff r z (h ω))).1 (u, v) := by rfl

end HigherDimLFPPAS.Scaling
