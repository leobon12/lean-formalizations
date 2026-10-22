import HigherDimLQGMetric.LogEnergy.DecayOuter
set_option autoImplicit false
noncomputable section
open MeasureTheory
open HigherDimLFPP (Rd)
namespace HigherDimLQGMetric

theorem decayLocalKernelSpatial_eq_logDiff {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ε : ℝ) (x u : Rd d)
    (hx : x ∈ ann 0 a b) (hu : u ∈ Metric.closedBall 0 b) :
    decayLocalKernelSpatial ha hb ε (x,u) = logDiff (ε,x,u) := by
  have hxa : a ≤ ‖x‖ := by simpa [ann] using hx.1.le
  have hxb : ‖x‖ ≤ b := by simpa [ann] using hx.2.le
  have hub : ‖u‖ ≤ b := by simpa [Metric.mem_closedBall] using hu
  simp [decayLocalKernelSpatial, decayLocalKernel,
    decayAnnCutoff_eq_one ha hb x hxa hxb, decayOuterCutoff_eq_one hb u hub]

theorem logCovRd_affineInner_eq_potential {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) {ε : ℝ} (hε : 0 < ε)
    (φ ψ : TestRd0 d)
    (hφ : tsupport φ.1 ⊆ ann 0 a b)
    (hψ : tsupport ψ.1 ⊆ Metric.closedBall 0 b) :
    logCovRd φ.1 (testAffinePull ε 0 ψ.1) =
      ε^d * ∫ x : Rd d, φ.1 x * decayKernelPotential ha (ha.trans hab) ε ψ.1 x := by
  unfold logCovRd
  have hinner (x : Rd d) :
      (∫ y : Rd d, φ.1 x * (-Real.log ‖x-y‖) *
          (testAffinePull ε 0 ψ.1) y) =
      ε^d * (φ.1 x * decayKernelPotential ha (ha.trans hab) ε ψ.1 x) := by
    rw [integral_eq_pow_mul_integral_comp_affinePt _ hε 0]
    congr 1
    have hψpull (u : Rd d) : (testAffinePull ε 0 ψ.1) (ε • u + 0) = ψ.1 u := by
      rw [testAffinePull_apply hε.ne' 0 ψ.1]
      simp [smul_smul, inv_mul_cancel₀ hε.ne']
    simp_rw [hψpull, add_zero]
    by_cases hx : x ∈ tsupport φ.1
    swap
    · have hz : φ.1 x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hz, decayKernelPotential]
    have hxa : x ∈ ann 0 a b := hφ hx
    let A : Rd d → ℝ := fun u => φ.1 x * (-Real.log ‖x‖) * ψ.1 u
    let B : Rd d → ℝ := fun u => φ.1 x *
      decayLocalKernelSpatial ha (ha.trans hab) ε (x,u) * ψ.1 u
    have hAint : Integrable A := (integrable_testOn ψ.1).const_mul _
    have hA0 : (∫ u, A u) = 0 := by
      change ∫ u : Rd d, (φ.1 x * -Real.log ‖x‖) * ψ.1 u = 0
      rw [integral_const_mul, ψ.2, mul_zero]
    have hpoint (u : Rd d) :
        φ.1 x * (-Real.log ‖x-ε • u‖) * ψ.1 u = A u + B u := by
      by_cases hu : u ∈ tsupport ψ.1
      · have hub := hψ hu
        dsimp [A,B]
        rw [show decayLocalKernelSpatial ha (ha.trans hab) ε (x,u) = logDiff (ε,x,u)
          from decayLocalKernelSpatial_eq_logDiff ha (ha.trans hab) ε x u hxa hub]
        simp [logDiff]
        ring
      · have hz : ψ.1 u = 0 := image_eq_zero_of_notMem_tsupport hu
        simp [A,B,hz]
    have heq : (fun u : Rd d => φ.1 x * (-Real.log ‖x - ε • u‖) * ψ.1 u) =
        fun u => A u + B u := funext hpoint
    rw [heq, integral_add_of_integral_eq_zero hAint hA0]
    change (∫ u : Rd d, B u) =
      φ.1 x * decayKernelPotential ha (ha.trans hab) ε ψ.1 x
    have hfun : B = fun u => φ.1 x *
        (decayLocalKernelSpatial ha (ha.trans hab) ε (x,u) * ψ.1 u) := by
      funext u; dsimp [B]; ring
    rw [hfun, integral_const_mul]
    rfl
  simp_rw [hinner]
  rw [integral_const_mul]
end HigherDimLQGMetric
