import HigherDimLQGMetric.Sec10.Cor102Algebra

/-!
# Corollary 10.2 in the sharp weak class

The exact dilation identity and weak translation covariance imply strong axiom (IV).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory
open HigherDimLFPP (Rd)

/-- The sharp weak class satisfies all four strong metric axioms. -/
theorem cor102Sharp_of (h14s : Theorem14SharpStmt) : Cor102SharpShape := by
  intro d hd ξ Q hξ hQ D hD
  let hW : IsWeakExpMetric d ξ D (fun s => s ^ (ξ * Q)) := hD
  refine ⟨hW.measurable, hW.length, hW.locality, hW.weyl, ?_⟩
  intro Ω _ P _ h hh r hr z
  have hg : IsLGFPlusCont (fun ω => affineComp r z (h ω)) P :=
    s8c_lgfPlusCont_affine hh hr z
  have hf := s8c_transform_eq_ae h14s hd hξ hQ hD r hr P
    (fun ω => affineComp r z (h ω)) hg
  have ht := hW.translation P h hh z
  have hc := hW.ae_apply_addFun_const hg
  filter_upwards [hf, ht, hc] with ω hfω htω hcω u v
  let g : DistRd d := affineComp r z (h ω)
  have hfield : affineComp r⁻¹ 0 g = affineComp 1 z (h ω) := by
    dsimp only [g]
    rw [affineComp_affineComp]
    simp only [smul_zero, zero_add, mul_inv_cancel₀ hr.ne']
  have hscale : r ^ (ξ * Q) = Real.exp (ξ * (Q * Real.log r)) := by
    rw [Real.rpow_def_of_pos hr]
    congr 1
    ring
  have hp : 0 < r ^ (ξ * Q) := Real.rpow_pos_of_pos hr _
  have hfactor := hfω 0 u v
  simp only [addFun_zero] at hfactor
  change (s8c_transform ξ Q r hr D g).1 (u,v) = (D g).1 (u,v) at hfactor
  rw [s8c_transform_apply, hfield] at hfactor
  have hbase : (D (affineComp 1 z (h ω))).1 (r • u, r • v) =
      r ^ (ξ * Q) * (D g).1 (u,v) :=
    (inv_mul_eq_iff_eq_mul₀ hp.ne').mp hfactor
  have htrans := htω (r • u) (r • v)
  have hconst := hcω (Q * Real.log r) u v
  change (D (addConst g (Q * Real.log r))).1 (u,v) =
    Real.exp (ξ * (Q * Real.log r)) * (D g).1 (u,v) at hconst
  calc
    (D (h ω)).1 (r • u + z, r • v + z) =
        (D (affineComp 1 z (h ω))).1 (r • u, r • v) := htrans.symm
    _ = r ^ (ξ * Q) * (D g).1 (u,v) := hbase
    _ = Real.exp (ξ * (Q * Real.log r)) * (D g).1 (u,v) := by rw [hscale]
    _ = (D (addConst (affineComp r z (h ω)) (Q * Real.log r))).1 (u,v) := hconst.symm

end HigherDimLQGMetric
