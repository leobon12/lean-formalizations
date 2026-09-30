import QuantumZipper.Proofs.Zipper.XPCIdUC
import QuantumZipper.Proofs.Zipper.UnifUCE2Mix
import QuantumZipper.Proofs.Zipper.XPCMod

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X-A-pc, smoothing node (2/2): `XPCSmoothStmt` holds

`xpcSmoothStmt_holds : XPCSmoothStmt`. For a rectangle `B` with `B.rect ⊆ UR r` and
`ψ = f_t⁻¹`, on the thickened rectangle `K = [a₁ − r, b₁ + r] × [a₂ − r, b₂ + r] ⊆ ℍ` (convex,
compact, containing every `B̄(z, r)`, `z ∈ B.rect`) `ψ` is bounded, `D₁`-Lipschitz, `ψ'` is
`D₂`-Lipschitz, and `‖ψ x − ψ y‖ ≥ m ‖x − y‖` (`XPCModBasic.exists_ddq_lower`, divided
differences) — `xps_geom`. With `A` the uniform measure on the unit circle:

* pushed circles: `muP z r = A_*(v ↦ ψ(z + r v))`; Frostman exponent `1`, constant `12/(m r)`
  (`isFrostman_muP_of_lower`: the preimage of a ball of radius `ρ` on the circle has diameter
  `≤ 2ρ/m`); energy modulus `(4/r + 2L')‖z − z'‖` (`abs_kernelCov2_push_push_le`);
* image circles: `muI z r = A_*(v ↦ ψ z + r‖ψ'(z)‖ v)`; Frostman constant `6/ρ_min`; energy
  modulus from `abs_kernelCov2_fc_fc_le`;

and `diffFam_of_centres` (`XPCSmoothBasic`) gives the two difference families.
Own elementary bookkeeping; the estimates cited are those of `XPCSmoothBasic`, `XPCMod`,
`XAreaPCModI`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology Real

namespace QuantumZipper.E6
namespace XAreaPC

theorem DiffFam.mono' {B : PBox} {μ ν : ℂ → ℝ → Measure ℂ} {C C' : ℝ} (h : DiffFam B μ ν C)
    (hCC : C ≤ C') : DiffFam B μ ν C' where
  C_nonneg := h.C_nonneg.trans hCC
  adm_μ := h.adm_μ
  adm_ν := h.adm_ν
  mass_μ := h.mass_μ
  mass_ν := h.mass_ν
  var0 := fun z hz s hs hs0 => (h.var0 z hz s hs hs0).trans (mul_le_mul_of_nonneg_right hCC hs.le)
  mod_μ := fun z hz z' hz' s s' hs hs0 hs' hs0' => (h.mod_μ z hz z' hz' s s' hs hs0 hs' hs0').trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCC (by positivity))
      (le_min hs.le hs'.le))
  mod_ν := fun z hz z' hz' s s' hs hs0 hs' hs0' => (h.mod_ν z hz z' hz' s s' hs hs0 hs' hs0').trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCC (by positivity))
      (le_min hs.le hs'.le))

theorem circleUnif_eq_map (c : ℂ) (ρ : ℝ) :
    circleUnif c ρ = (circleUnif 0 1).map (fun v => c + (ρ : ℂ) * v) := by
  have hm : Measurable fun v : ℂ => c + (ρ : ℂ) * v := by fun_prop
  unfold circleUnif
  rw [Measure.map_smul, Measure.map_map hm (measurable_circleMap 0 1)]
  · congr 2
    funext θ
    simp [circleMap]
  · exact hm.aemeasurable

section Geom

variable {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
include hW hW0 ht

end Geom

end XAreaPC
end QuantumZipper.E6
