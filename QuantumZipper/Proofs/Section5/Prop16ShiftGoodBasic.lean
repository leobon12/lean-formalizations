import QuantumZipper.Proofs.Section5.Prop16NodeBKernel
import QuantumZipper.Proofs.Section5.Prop16LocalAssembly

/-!
# Proposition 1.6, node C′: elementary lemmas on the Palm shift of a mixed GFF

The Palm shift `mixedGreenSample D S x` of the mixed GFF (`Prop16PalmZoom.lean`) is the Green
function `G_D(x, ·)` of `D` with free boundary on `S = [c,d]`, read at the free-arc point `x`. By
K3 node M6 (`K3.mixedLocalKernel`, `Prop16NodeBKernel.mixedGreenSample_eq`), on every admissible
measure carried by a compact `K` with `K3.MixedLocalHyp D S K R` containing `x` the sample equals
the kernel integral `∫ z, mixedGreenK K k x z ∂μ`, i.e. `-2 log‖x - z‖ + k(z, x)` with `k`
continuous on `K × K`. This file isolates the elementary analytic facts needed to read that off
as a *function* on `D`:

* `abs_integral_foldedCircle_sub_le`, `tendsto_integral_foldedCircle_radius`: at a point `z` where
  `f` is continuous, the folded-circle averages `∫ w, f w ∂foldedCircle z 2^{-n}` converge to
  `f z` (a probability measure shrinking to a point; own elementary proofs);
* `continuousOn_mixedGreenK_ball`, `continuousAt_mixedGreenK`: the kernel `mixedGreenK K k x ·` is
  continuous on half-balls inside `K` that avoid `x`, and at interior points `≠ x`;
* `mixedGreenSample_fc_eq`: the per-compact circle form of the Palm shift;
* `tendsto_mixedGreenSample_fc`: `mixedGreenSample D S x (foldedCircle z 2^{-n}) → mixedGreenK K k
  x z` for a half-ball `closedBall z ρ ∩ ℍ̄ ⊆ K` on which the kernel is continuous.

The last statement is what makes the Palm shift a *function* of `z` on `int K` (and, applied to
two compact covers of the same point, independent of the compact `K`): the remaining step to one
continuous representative on `D` is the compact cover and gluing argument of `Prop16ShiftGood.lean`.

Sources: Duplantier–Sheffield, arXiv:0808.1560, §3.3 (p. 22) for `G_D = -log|·| + harmonic` near a
free arc; the analytic lemmas here are own elementary proofs.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal ComplexConjugate

namespace QuantumZipper

namespace Prop16Asm

open Prop16Area Prop16Area.G

/-! ## 1. Folded circles shrink to their centre -/

/-- `w ↦ neumannH (x : ℂ) w` is continuous at every `w ∈ ℍ̄` with `w ≠ x`. -/
theorem continuousAt_neumannH_ofReal {x : ℝ} {w : ℂ} (hw : w ≠ (x : ℂ)) (hwH : w ∈ Hbar) :
    ContinuousAt (fun u => neumannH (x : ℂ) u) w := by
  have h1 : ((x : ℂ)) ≠ w := fun h => hw h.symm
  have h2 : ((x : ℂ)) ≠ conj w := by
    intro h
    have him : w.im = 0 := by
      have := congrArg Complex.im h
      simpa using this
    have hre : x = w.re := by
      have := congrArg Complex.re h
      simpa using this
    exact hw (Complex.ext (by simp [hre]) (by simp [him]))
  have hA : ‖(x : ℂ) - w‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 h1)
  have hB : ‖(x : ℂ) - conj w‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 h2)
  have c1 : ContinuousAt (fun u : ℂ => Real.log ‖(x : ℂ) - u‖) w :=
    ContinuousAt.log (by fun_prop) hA
  have c2 : ContinuousAt (fun u : ℂ => Real.log ‖(x : ℂ) - conj u‖) w :=
    ContinuousAt.log (by fun_prop) hB
  exact ContinuousAt.sub (f := fun u : ℂ => -Real.log ‖(x : ℂ) - u‖)
    (g := fun u : ℂ => Real.log ‖(x : ℂ) - conj u‖) c1.neg c2

/-- **Folded circle averages.** If `f` is continuous on the half-disc `closedBall z ρ ∩ ℍ̄` and
`|f w - f z| ≤ ε` for `dist w z < δ`, then the average of `f` over `foldedCircle z r` is within
`ε` of `f z` whenever `r < δ` and `r ≤ ρ`. -/
theorem abs_integral_foldedCircle_sub_le {f : ℂ → ℝ} {z : ℂ} {ρ δ ε : ℝ} (hρ : 0 < ρ)
    (hcont : ContinuousOn f (closedBall z ρ ∩ Hbar)) (hzH : z ∈ Hbar)
    (hδ : ∀ w, dist w z < δ → |f w - f z| ≤ ε) {r : ℝ} (hr : 0 < r) (hrδ : r < δ)
    (hrρ : r ≤ ρ) :
    |∫ w, f w ∂(foldedCircle z r) - f z| ≤ ε := by
  have hint : Integrable f (foldedCircle z r) :=
    integrable_fc_of_continuousOn hzH hr
      (hcont.mono (inter_subset_inter_left _ (closedBall_subset_closedBall hrρ)))
  refine abs_integral_sub_le_of_ae hint ?_
  filter_upwards [ae_fc_mem_ball_inter hzH hr] with w hw
  exact hδ w (lt_of_le_of_lt (Metric.mem_closedBall.1 hw.1) hrδ)

/-- **Folded circles shrink to their centre.** For `f` continuous on a half-disc around
`z ∈ ℍ̄`, `∫ w, f w ∂foldedCircle z (2^{-n}) → f z`. -/
theorem tendsto_integral_foldedCircle_radius {f : ℂ → ℝ} {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hcont : ContinuousOn f (closedBall z ρ ∩ Hbar)) (hzH : z ∈ Hbar) (hz : ContinuousAt f z) :
    Tendsto (fun n : ℕ => ∫ w, f w ∂(foldedCircle z (radius n))) atTop (𝓝 (f z)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hmem : f ⁻¹' Metric.ball (f z) (ε / 2) ∈ 𝓝 z :=
    hz.preimage_mem_nhds (Metric.ball_mem_nhds _ (by linarith))
  obtain ⟨δ, hδ, hδf⟩ := Metric.mem_nhds_iff.1 hmem
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (tendsto_radius_zero_nodeB.eventually (gt_mem_nhds (lt_min hδ hρ)))
  refine ⟨N, fun n hn => ?_⟩
  have h1 : radius n < δ := lt_of_lt_of_le (hN n hn) (min_le_left _ _)
  have h2 : radius n ≤ ρ := (lt_of_lt_of_le (hN n hn) (min_le_right _ _)).le
  have hbound : ∀ w, dist w z < δ → |f w - f z| ≤ ε / 2 := fun w hw => by
    have := hδf hw
    rw [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at this
    exact this.le
  have hmain := abs_integral_foldedCircle_sub_le hρ hcont hzH hbound (radius_pos n) h1 h2
  rw [Real.dist_eq]
  exact lt_of_le_of_lt hmain (by linarith)

/-! ## 2. The mixed Green kernel on compact pieces -/

section Kernel

variable {K : Set ℂ} {k : ℂ → ℂ → ℝ}

/-- `k(·, x)` is continuous on `K` for `x ∈ K`. -/
theorem continuousOn_k_fixed (hk : ContinuousOn (Function.uncurry k) (K ×ˢ K)) {x : ℝ}
    (hx : (x : ℂ) ∈ K) : ContinuousOn (fun w => k w (x : ℂ)) K :=
  hk.comp (continuous_id.prodMk continuous_const).continuousOn fun w hw => ⟨hw, hx⟩

/-- `remK K k (·, x)` is continuous on `K` for `x ∈ K`. -/
theorem continuousOn_remK_fixed (hk : ContinuousOn (Function.uncurry k) (K ×ˢ K)) {x : ℝ}
    (hx : (x : ℂ) ∈ K) : ContinuousOn (fun w => remK K k w (x : ℂ)) K :=
  (continuousOn_k_fixed hk hx).congr fun w hw => remK_of_mem (k := k) hw hx

/-- The mixed Green kernel `mixedGreenK K k x ·` is continuous at points `z ≠ x` that are
interior points of `K`. -/
theorem continuousAt_mixedGreenK (hk : ContinuousOn (Function.uncurry k) (K ×ˢ K)) {x : ℝ}
    (hx : (x : ℂ) ∈ K) {z : ℂ} (hzH : z ∈ Hbar) (hzK : K ∈ 𝓝 z) (hne : z ≠ (x : ℂ)) :
    ContinuousAt (fun w => mixedGreenK K k x w) z := by
  have hN : ContinuousAt (fun w => neumannH (x : ℂ) w) z :=
    continuousAt_neumannH_ofReal hne hzH
  have hkz : ContinuousAt (fun w => k w (x : ℂ)) z :=
    (continuousOn_k_fixed hk hx).continuousAt hzK
  have hEq : (fun w => remK K k w (x : ℂ)) =ᶠ[𝓝 z] (fun w => k w (x : ℂ)) := by
    filter_upwards [hzK] with w hw
    exact remK_of_mem (k := k) hw hx
  have hsum : ContinuousAt
      ((fun w => neumannH (x : ℂ) w) + fun w => remK K k w (x : ℂ)) z :=
    hN.add (hkz.congr hEq.symm)
  show ContinuousAt (fun w => neumannH (x : ℂ) w + remK K k w (x : ℂ)) z
  exact hsum

/-- The mixed Green kernel is continuous on a half-ball inside `K` that keeps away from `x`. -/
theorem continuousOn_mixedGreenK_ball (hk : ContinuousOn (Function.uncurry k) (K ×ˢ K))
    {x : ℝ} (hx : (x : ℂ) ∈ K) {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hρx : ρ < dist z (x : ℂ))
    (hball : closedBall z ρ ∩ Hbar ⊆ K) :
    ContinuousOn (fun w => mixedGreenK K k x w) (closedBall z ρ ∩ Hbar) := by
  intro w hw
  have hwK : w ∈ K := hball hw
  have hwz : dist w z ≤ ρ := Metric.mem_closedBall.1 hw.1
  have hdw : dist w (x : ℂ) ≠ 0 := by
    intro h0
    have h1 : dist z (x : ℂ) ≤ dist z w + dist w (x : ℂ) := dist_triangle _ _ _
    rw [dist_comm z w, h0, add_zero] at h1
    linarith
  have hN : ContinuousAt (fun u => neumannH (x : ℂ) u) w :=
    continuousAt_neumannH_ofReal (fun h => hdw (by rw [h, dist_self])) hw.2
  have hrem : ContinuousOn (fun u => remK K k u (x : ℂ)) (closedBall z ρ ∩ Hbar) :=
    (continuousOn_remK_fixed hk hx).mono hball
  have hgoal : ContinuousWithinAt
      ((fun u => neumannH (x : ℂ) u) + fun u => remK K k u (x : ℂ))
      (closedBall z ρ ∩ Hbar) w :=
    hN.continuousWithinAt.add (hrem w hw)
  change ContinuousWithinAt (fun u => neumannH (x : ℂ) u + remK K k u (x : ℂ)) _ w
  exact hgoal

variable {D S : Set ℂ} {R : ℝ}

/-- **The Palm shift on a circle carried by a compact.** On a folded circle contained in a
compact `K` with `K3.MixedLocalHyp D S K R` containing `x`, `mixedGreenSample D S x` is the kernel
integral (no junk value). -/
theorem mixedGreenSample_fc_eq (hL : K3.MixedLocalHyp D S K R)
    (hk : ContinuousOn (Function.uncurry k) (K ×ˢ K))
    (hkc : ∀ μ ν : Measure ℂ, IsAdmissibleH μ → μ Kᶜ = 0 → IsAdmissibleH ν → ν Kᶜ = 0 →
      dualCov D (mixedSpace D S) μ ν = kernelCov (fun x y => neumannH x y + k x y) μ ν)
    {x : ℝ} (hx : (x : ℂ) ∈ K) (hev : ∀ᶠ n in atTop, Palm.fcK x n Kᶜ = 0) {c : ℂ} (hc : c ∈ Hbar)
    {r : ℝ} (hr : 0 < r) (hKc : closedBall c r ∩ Hbar ⊆ K) :
    mixedGreenSample D S x (foldedCircle c r) = ∫ z, mixedGreenK K k x z ∂(foldedCircle c r) :=
  mixedGreenSample_eq hL hk hkc (isAdmissibleH_foldedCircle hc hr)
    ((mem_ae_iff (μ := foldedCircle c r) (s := K)).1
      ((ae_fc_mem_ball_inter hc hr).mono hKc)) hx hev

/-- **The Palm shift read at shrinking circles.** At a point `z ∈ ℍ̄` with `z ≠ x` and a half-ball
`closedBall z ρ ∩ ℍ̄ ⊆ K` on which the kernel is continuous, the circle values of the Palm shift
converge to `mixedGreenK K k x z`. -/
theorem tendsto_mixedGreenSample_fc (hL : K3.MixedLocalHyp D S K R)
    (hk : ContinuousOn (Function.uncurry k) (K ×ˢ K))
    (hkc : ∀ μ ν : Measure ℂ, IsAdmissibleH μ → μ Kᶜ = 0 → IsAdmissibleH ν → ν Kᶜ = 0 →
      dualCov D (mixedSpace D S) μ ν = kernelCov (fun x y => neumannH x y + k x y) μ ν)
    {x : ℝ} (hx : (x : ℂ) ∈ K) (hev : ∀ᶠ n in atTop, Palm.fcK x n Kᶜ = 0) {z : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hball : closedBall z ρ ∩ Hbar ⊆ K) (hzH : z ∈ Hbar)
    (hcont : ContinuousOn (fun w => mixedGreenK K k x w) (closedBall z ρ ∩ Hbar))
    (hzat : ContinuousAt (fun w => mixedGreenK K k x w) z) :
    Tendsto (fun n : ℕ => mixedGreenSample D S x (foldedCircle z (radius n))) atTop
      (𝓝 (mixedGreenK K k x z)) := by
  have hevK : ∀ᶠ n in atTop, closedBall z (radius n) ∩ Hbar ⊆ K := by
    filter_upwards [tendsto_radius_zero_nodeB.eventually (gt_mem_nhds hρ)] with n hn
    intro w hw
    exact hball ⟨(Metric.mem_closedBall.1 hw.1).trans hn.le, hw.2⟩
  refine (tendsto_integral_foldedCircle_radius hρ hcont hzH hzat).congr' ?_
  filter_upwards [hevK] with n hn
  exact (mixedGreenSample_fc_eq hL hk hkc hx hev hzH (radius_pos n) hn).symm

end Kernel

end Prop16Asm

end QuantumZipper
