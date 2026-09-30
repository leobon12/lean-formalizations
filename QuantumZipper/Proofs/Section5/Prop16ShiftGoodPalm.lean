import QuantumZipper.Proofs.Section5.Prop16ShiftGoodRep
import QuantumZipper.Proofs.Section5.Prop16ShiftGood

/-!
# Proposition 1.6, node C′: the Palm shift is a continuous function on `D`

This file proves `PalmCircRepStmt` (`Prop16ShiftGood.lean`) for the mixed GFF of Proposition 1.6,
hence `Prop16PalmShiftGoodStmt` unconditionally.

The representative used is the pointwise limit of the Palm shift on shrinking dyadic circles,

`palmPsi D S x z = limUnder_n mixedGreenSample D S x (foldedCircle z 2^{-n})`,

which by `Prop16ShiftGoodBasic.tendsto_mixedGreenSample_fc` equals the M6 kernel
`mixedGreenK K k x z` at every interior point `z ≠ x` of a compact `K` with `K3.MixedLocalHyp`
containing `x` and the small circles around `x` — in particular that value does not depend on the
choice of `K`. Since every compact `L ⊆ D` is contained in such a `K`
(`Prop16ShiftGoodRep.exists_compact_mixedLocalHyp`), the pointwise identity, the continuity of
`palmPsi` on `D`, and the circle values of the Palm shift follow.

Source: Sheffield, arXiv:1012.4797, Prop. 1.6 (p. 25): near the free-arc point `x` the Palm shift is
`G_D(x, ·) = -2 log|· − x| + harmonic`, a genuine function on `D`; the formal gluing is an own
elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal ComplexConjugate

namespace QuantumZipper

namespace Prop16Asm

open Prop16Area Prop16Area.G

/-- The Palm shift as a function of the point, read as the limit of its values on shrinking
folded circles. -/
def palmPsi (D S : Set ℂ) (x : ℝ) (z : ℂ) : ℝ :=
  limUnder atTop fun n : ℕ => mixedGreenSample D S x (foldedCircle z (radius n))

/-- At an interior point of a valid compact, `palmPsi` is the M6 kernel value. -/
theorem palmPsi_eq_kernel {D S K : Set ℂ} {R : ℝ} {k : ℂ → ℂ → ℝ}
    (hL : K3.MixedLocalHyp D S K R) (hk : ContinuousOn (Function.uncurry k) (K ×ˢ K))
    (hkc : ∀ μ ν : Measure ℂ, IsAdmissibleH μ → μ Kᶜ = 0 → IsAdmissibleH ν → ν Kᶜ = 0 →
      dualCov D (mixedSpace D S) μ ν = kernelCov (fun x y => neumannH x y + k x y) μ ν)
    {x : ℝ} (hx : (x : ℂ) ∈ K) (hev : ∀ᶠ n in atTop, Palm.fcK x n Kᶜ = 0) {z : ℂ}
    (hz : z ∈ interior K) (hzH : z ∈ Hbar) (hne : z ≠ (x : ℂ)) :
    palmPsi D S x z = mixedGreenK K k x z := by
  obtain ⟨ε, hε, hεK⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hz)
  have hdx : 0 < dist z (x : ℂ) := dist_pos.2 hne
  set ρ : ℝ := min (ε / 2) (dist z (x : ℂ) / 2) with hρdef
  have hρ : 0 < ρ := lt_min (by linarith) (by linarith)
  have hρx : ρ < dist z (x : ℂ) := by
    have h1 : ρ ≤ dist z (x : ℂ) / 2 := min_le_right _ _
    linarith
  have hρ' : ρ < ε := by
    have h1 : ρ ≤ ε / 2 := min_le_left _ _
    linarith
  have hball : closedBall z ρ ∩ Hbar ⊆ K := fun w hw =>
    hεK (by rw [mem_ball]; linarith [Metric.mem_closedBall.1 hw.1])
  exact (tendsto_mixedGreenSample_fc hL hk hkc hx hev hρ hball hzH
    (continuousOn_mixedGreenK_ball hk hx hρ hρx hball)
    (continuousAt_mixedGreenK hk hx hzH (mem_interior_iff_mem_nhds.1 hz) hne)).limUnder_eq

/-- The circle values of the Palm shift are the integrals of `palmPsi` against the circle. -/
theorem mixedGreenSample_eq_ofFun_palmPsi {D : Set ℂ} {c d x : ℝ} (hgeo : K3.Prop16Geometry D c d)
    (hx : x ∈ Ioo c d) {cc : ℂ} {r : ℝ} (hc : cc ∈ Hbar) (hr : 0 < r)
    (hsub : closedBall cc r ∩ Hbar ⊆ D) :
    mixedGreenSample D (realSet (Icc c d)) x (foldedCircle cc r) =
      ∫ z, palmPsi D (realSet (Icc c d)) x z ∂(foldedCircle cc r) := by
  have hDH : D ⊆ H := hgeo.2.2.2.1
  obtain ⟨K, R, hR, hL, hxK, hLint, hev⟩ :=
    exists_compact_mixedLocalHyp hgeo hx (isCompact_closedBall_inter_Hbar cc r) hsub
  obtain ⟨k, hk, hkc⟩ := K3.mixedLocalKernel (D := D) (c := c) (d := d) (K := K) (R := R) hgeo hL
  rw [mixedGreenSample_fc_eq hL hk hkc hxK hev hc hr (fun w hw => interior_subset (hLint hw))]
  refine integral_congr_ae ?_
  filter_upwards [ae_fc_mem_ball_inter hc hr] with w hw
  have hwD : w ∈ D := hsub hw
  have hwne : w ≠ (x : ℂ) := by
    intro h
    have h2 : (0 : ℝ) < w.im := hDH hwD
    rw [h] at h2
    simp at h2
  exact (palmPsi_eq_kernel hL hk hkc hxK hev (hLint hw) (H_subset_Hbar (hDH hwD)) hwne).symm

/-- `palmPsi` is continuous on `D`. -/
theorem continuousOn_palmPsi {D : Set ℂ} {c d x : ℝ} (hgeo : K3.Prop16Geometry D c d)
    (hx : x ∈ Ioo c d) : ContinuousOn (palmPsi D (realSet (Icc c d)) x) D := by
  have hDo : IsOpen D := hgeo.1
  have hDH : D ⊆ H := hgeo.2.2.2.1
  intro z hz
  obtain ⟨ρ, hρ, hρD⟩ := Metric.mem_nhds_iff.1 (hDo.mem_nhds hz)
  have hCD : closedBall z (ρ / 2) ⊆ ball z ρ := fun w hw => by
    rw [mem_ball]; linarith [Metric.mem_closedBall.1 hw]
  obtain ⟨K, R, hR, hL, hxK, hLint, hev⟩ :=
    exists_compact_mixedLocalHyp hgeo hx (isCompact_closedBall z (ρ / 2)) (fun w hw => hρD (hCD hw))
  obtain ⟨k, hk, hkc⟩ := K3.mixedLocalKernel (D := D) (c := c) (d := d) (K := K) (R := R) hgeo hL
  -- points of the inner ball are interior points of `K`, inside `D`
  have hne_of_mem : ∀ w ∈ ball z (ρ / 2), w ≠ (x : ℂ) := by
    intro w hw h
    have h2 : (0 : ℝ) < w.im := hDH (hρD (hCD (ball_subset_closedBall hw)))
    rw [h] at h2
    simp at h2
  have hpoint : ∀ w ∈ ball z (ρ / 2), palmPsi D (realSet (Icc c d)) x w = mixedGreenK K k x w :=
    fun w hw => palmPsi_eq_kernel hL hk hkc hxK hev
      (hLint (ball_subset_closedBall hw))
      (H_subset_Hbar (hDH (hρD (hCD (ball_subset_closedBall hw)))))
      (hne_of_mem w hw)
  have hkz : ContinuousAt (fun w => mixedGreenK K k x w) z :=
    continuousAt_mixedGreenK hk hxK (H_subset_Hbar (hDH (hρD (mem_ball_self hρ))))
      (mem_interior_iff_mem_nhds.1 (hLint (mem_closedBall_self (by linarith))))
      (hne_of_mem z (mem_ball_self (by linarith)))
  have hEq : (fun w => mixedGreenK K k x w) =ᶠ[𝓝 z] (palmPsi D (realSet (Icc c d)) x) :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds z (half_pos hρ)) fun w hw => (hpoint w hw).symm
  exact (hkz.congr hEq).continuousWithinAt

/-- **The Palm shift is a continuous function on `D`** (`PalmCircRepStmt`). -/
theorem palmCircRepStmt_proved : PalmCircRepStmt := by
  intro D c d x hgeo hx
  refine ⟨palmPsi D (realSet (Icc c d)) x, continuousOn_palmPsi hgeo hx, ?_⟩
  intro n k z hz hW
  exact mixedGreenSample_eq_ofFun_palmPsi hgeo hx (CircleCont.dyadicRoundC_mem_Hbar hz n)
    (radius_pos k) hW

/-- **Node C′ of Proposition 1.6** (`Prop16PalmShiftGoodStmt`), unconditionally. -/
theorem prop16PalmShiftGoodStmt_proved : Prop16PalmShiftGoodStmt :=
  prop16PalmShiftGoodStmt_of_palmCircRep palmCircRepStmt_proved

end Prop16Asm

end QuantumZipper
