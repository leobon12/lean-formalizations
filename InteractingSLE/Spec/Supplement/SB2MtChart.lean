/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MtKer

/-!
# K2's chart inputs for the canonical relative chart family

Packet PROVE-SB2-LCMEAN, round 12. The kernel half at a relative version (`Mt.hasSafeLaw_hasSafeMembers_of_stageLines`)
asks of its chart family: conformality and a continuous, harmonic lift at every sample, and measurable domain events,
forward map and lift for the version's initial σ-algebra. For the canonical relative chart
`Φ ω = Mo.hullChart (fillH (K ω)) (x₀ ω)` of F2b (`K` compact, `K ∪ lowerHalf` preconnected, `K` dyadic-hit measurable
for a σ-algebra `m`, `x₀` measurable for `m`) all of these hold:

* `harmonicOnNhd_lift_hullChart`: the lift `Im (canonDerivLog A)` is harmonic on `ℍ ∖ A` (the imaginary part of an
  analytic logarithm of the derivative);
* **`hullChart_k2Inputs`**: the six chart inputs, for any σ-algebra `m`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Mt

/-- **The lift of the canonical hull chart is harmonic** on its domain `ℍ ∖ A`. -/
theorem harmonicOnNhd_lift_hullChart {A : Set ℂ} (hA : IsHPHull A) (x₀ : ℝ) :
    InnerProductSpace.HarmonicOnNhd (Mo.hullChart A x₀).2.2 (Mo.hullChart A x₀).dom := by
  rw [Mo.coe_dom_hullChart hA x₀]
  obtain ⟨hL, -⟩ := Restart.isCanonicalDerivLog_canonDerivLog hA
  have hU : IsOpen (H \ A) := hA.2.2.1
  intro z hz
  exact (hL.1.analyticAt (hU.mem_nhds hz)).harmonicAt_im

/-- **K2's chart inputs for the canonical relative chart family** `ω ↦ hullChart (fillH (K ω)) (x₀ ω)`: conformal, with
continuous and harmonic lift at every sample, and with measurable domain events, forward map and lift for any
σ-algebra `m` for which `K` is dyadic-hit measurable and `x₀` is measurable. -/
theorem hullChart_k2Inputs {Ω : Type*} {m : MeasurableSpace Ω} {K : Ω → Set ℂ} {x₀ : Ω → ℝ}
    (hK : @Restart.IsDyadicHitMeasurable Ω m K) (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) (hx₀ : Measurable[m] x₀) :
    (∀ ω, (Mo.hullChart (fillH (K ω)) (x₀ ω)).IsConformal) ∧
      (∀ ω, ContinuousOn (Mo.hullChart (fillH (K ω)) (x₀ ω)).2.2 (Mo.hullChart (fillH (K ω)) (x₀ ω)).dom) ∧
      (∀ ω, InnerProductSpace.HarmonicOnNhd (Mo.hullChart (fillH (K ω)) (x₀ ω)).2.2
        (Mo.hullChart (fillH (K ω)) (x₀ ω)).dom) ∧
      (∀ z, MeasurableSet[m] {ω | z ∈ (Mo.hullChart (fillH (K ω)) (x₀ ω)).dom}) ∧
      (∀ z, Measurable[m] ({ω | z ∈ (Mo.hullChart (fillH (K ω)) (x₀ ω)).dom}.indicator
        fun ω => (Mo.hullChart (fillH (K ω)) (x₀ ω)).1 z)) ∧
      ∀ z, Measurable[m] ({ω | z ∈ (Mo.hullChart (fillH (K ω)) (x₀ ω)).dom}.indicator
        fun ω => (Mo.hullChart (fillH (K ω)) (x₀ ω)).2.2 z) := by
  have hA : ∀ ω, IsHPHull (fillH (K ω)) := Mo.isHPHull_fillH hKc hKp
  exact ⟨fun ω => Mo.isConformal_hullChart (hA ω) (x₀ ω), fun ω => Mo.continuousOn_lift_hullChart (hA ω) (x₀ ω),
    fun ω => harmonicOnNhd_lift_hullChart (hA ω) (x₀ ω),
    fun z => @Mo.measurableSet_mem_dom_hullChart Ω m K x₀ hK hKc hKp z,
    fun z => @Mo.measurable_indicator_fwd_hullChart Ω m K x₀ hK hKc hKp hx₀ z,
    fun z => @Mo.measurable_indicator_lift_hullChart Ω m K x₀ hK hKc hKp z⟩

end InteractingSLE.Theorem14.SB.Mt
