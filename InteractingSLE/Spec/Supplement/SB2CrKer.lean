/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CrSafe
import InteractingSLE.Spec.Restart.DomainMarkovAux79Line

/-!
# (S) for a chart field from line kernels and line means, under a strict time change

Packet PROVE-SB2-CONDFIN (round 8, D44). `Aux79.hasSafeLaw_of_lineKernel` conditions on the live event `F`, an event
of the physical filtration at time `0`. At the root (B-time indexing), the live event is the root event, an event of
the relative filtration at time `0` (the entrance) but not of the physical one. Here the conditioning event is a
separate physical event `M ⊇ F` (time `0`), the time change is strict (`Cr.hasSafeLaw_of_lineLawS`), and the line
kernels, means and regularity are needed only on `M` where the clock is positive.

* **`hasSafeLaw_of_lineKernelS`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open QuantumZipper (H zeroGFFTestCov fwdHull)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Cr

open Restart.DomainMarkov Restart.DomainMarkov.Aux79 Restart.DomainMarkov.K2 Restart.DomainMarkov.Mean Coupling Ito

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {nL nR : ℕ} {κ : ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {F : Set Ω}

/-- **(S) for the chart field from the line kernels and means, under a strict time change**, with the conditioning
event `M` (time `0`) containing the live event `F`. -/
theorem hasSafeLaw_of_lineKernelS {𝓖 𝓗' : Filtration ℝ≥0 mΩ} {M : Set Ω} (hM : MeasurableSet[𝓖 0] M)
    (hFM : ∀ᵐ ω ∂P, ω ∈ F → ω ∈ M)
    {Qc : ℝ≥0 → Ω → ℝ≥0} {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (a k : ℝ)
    (hQc : ∀ ω, Continuous fun t => Qc t ω) (hQm : ∀ ω, Monotone fun t => Qc t ω) (hQ0 : ∀ ω, Qc 0 ω = 0)
    (hQa : ∀ t, Measurable[𝓖 t] (Qc t))
    (h𝓗' : ∀ q D, MeasurableSet[𝓗' q] D → ∀ t, MeasurableSet[𝓖 t] (D ∩ {ω | q < Qc t ω}))
    (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < ζ ω → ∃ t, q ≤ Qc t ω)
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsForceReg W VL VR ζ ω)
    (hregM : ∀ t, ∀ᵐ ω ∂P, ω ∈ M → 0 < Qc t ω → IsForceReg W VL VR ζ ω)
    (hS : ∀ (ψ : TestOn upperHalfPlaneOpens) t,
      MeasurableSet[𝓖 t] ({ω | 0 < Qc t ω} ∩ lineSafe Qc W ζ (tsupport ψ) t))
    (𝒢L : ℝ≥0 → MeasurableSpace Ω) (h𝒢L : ∀ t, 𝓖 t ≤ 𝒢L t) (h𝒢Lm : ∀ t, 𝒢L t ≤ mΩ)
    (Mk : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hker : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ M → 0 < Qc t ω →
      (Qc t ω : ℝ≥0∞) < ζ ω →
      tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (Qc t ω)) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢L t] ω =
        Complex.exp (Complex.I * (Mk t ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (Qc t ω))) φ φ :
            ℝ) : ℂ)))
    (hmean : ∀ (t : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ M → 0 < Qc t ω →
      ω ∈ lineSafe Qc W ζ (tsupport ψ) t → Chart.chartTransport (hc ω) 1 a k (Mk t ω) ψ =
        ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) (Qc t ω) (bheProc κ ρL ρR W VL VR ω (Qc t ω)) z * ψ z) :
    HasSafeLaw κ ρL ρR P 𝓗' F ζ W VL VR fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) := by
  have hXψ : ∀ ψ : TestOn upperHalfPlaneOpens, Measurable fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) ψ :=
    fun ψ => ((measurable_pi_apply ψ).comp (Measurable.of_comap_le le_rfl)).comp
      (Chart.measurable_chartTransport_random' hc (fun z => 𝓖.le 0 _ (hdom z))
        (fun z => (hfwd z).mono (𝓖.le 0) le_rfl) (fun z => (hliftm z).mono (𝓖.le 0) le_rfl) hliftc hh 1 a k)
  refine hasSafeLaw_of_lineLawS hXψ hQc hQm hQ0 hQa h𝓗' hreach hreg hS 𝒢L h𝒢L h𝒢Lm fun ψ t => ?_
  have h0t : 𝓖 0 ≤ 𝒢L t := (𝓖.mono (zero_le (a := t))).trans (h𝒢L t)
  have hE : MeasurableSet[𝒢L t] (M ∩ ({ω | 0 < Qc t ω} ∩ lineSafe Qc W ζ (tsupport ψ) t)) :=
    (h0t _ hM).inter (h𝒢L t _ (hS ψ t))
  have hkey := ae_condExp_cexp_chartTransport_eq_cfAt_rand (P := P) (ρL := ρL) (ρR := ρR) (VL := VL) (VR := VR)
    (h𝒢Lm t) hc (fun z => h0t _ (hdom z)) (fun z => (hfwd z).mono h0t le_rfl)
    (fun z => (hliftm z).mono h0t le_rfl) hliftc hh a k (Qc t) (Mset := M ∩ {ω | 0 < Qc t ω}) (fun φ => by
      filter_upwards [hker t φ] with ω hω hωM hlt hsupp using hω hωM.1 hωM.2 hlt hsupp) ψ hE
    (by
      filter_upwards [hregM t] with ω hω hωE
      exact ⟨⟨hωE.1, hωE.2.1⟩, hωE.2.2, (hω hωE.1 hωE.2.1).2.1, (hω hωE.1 hωE.2.1).1⟩)
    (by
      filter_upwards [hmean t ψ] with ω hω hωE using hω hωE.1 hωE.2.1 hωE.2.2)
  filter_upwards [hkey, hFM] with ω hω hωM hωF hpos hωS
  exact hω ⟨hωM hωF, hpos, hωS⟩

end InteractingSLE.Theorem14.SB.Cr
