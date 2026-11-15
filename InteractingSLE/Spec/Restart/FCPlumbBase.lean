/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.DomainMarkovAux79Line
import InteractingSLE.Spec.Restart.DomainMarkovAux79FC
import InteractingSLE.Spec.Restart.DomainMarkovLocCrit

/-!
# The first-contact line-mean interface for K2

This file names the first-contact continuation's Aux. 79 line-mean identity and adapts it to the
existing K2 line-kernel theorem. The identity itself is supplied by the separate Aux. 79 packet.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC zeroGFFTestCov)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE

namespace Restart.FCPlumb

open Chart DomainMarkov DomainMarkov.Aux79 K2 WholeField
open Coupling

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The exact deterministic-line characteristic-kernel input required by Aux. 79's K2 assembler. For the
first-contact continuation this is the proposition obtained by gluing the capped `shUnion` kernels over the
first-contact boxes and identifying their complementary domains with the chart images of the driver hulls.
-/
def FCLineKernelStatement {F : Set Ω} {Qc : ℝ≥0 → Ω → ℝ≥0} {c : Ω → Chart}
    {h : Ω → DistOn upperHalfPlaneOpens} (𝒢L : ℝ≥0 → MeasurableSpace Ω)
    (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P,
    ω ∈ F → (Qc t ω : ℝ≥0∞) < ζ ω →
      tsupport φ ⊆ (c ω).2.1 ''
        (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (Qc t ω)) →
          P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢L t] ω =
            Complex.exp (Complex.I * (M t ω φ : ℂ) -
              (((1 / 2 : ℝ) * zeroGFFTestCov
                ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (Qc t ω))) φ φ : ℝ) : ℂ))

/-- **The first-contact Aux. 79 line-mean identity** at deterministic shifted lines. This is the
`hmean` input of `Aux79.hasSafeLaw_of_lineKernel`, with the first-contact chart height shift `a`
and the force-point coefficient `χ(κ)`. It is a named interface for PROVE-FCAUX79's result.
-/
def FCLineMeanStatement {F : Set Ω}
    {Qc : ℝ≥0 → Ω → ℝ≥0} {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (a : ℝ) (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ (t : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P,
    ω ∈ F → ω ∈ lineSafe Qc W ζ (tsupport ψ) t →
      Chart.chartTransport (hc ω) 1 a (chiC κ) (M t ω) ψ =
        ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) (Qc t ω)
          (bheProc κ ρL ρR W VL VR ω (Qc t ω)) z * ψ z

/-- K2's (S) input for the first-contact chart field, from the existing line-kernel assembler and
the named first-contact line-mean identity.
-/
theorem hasSafeLaw_of_FCLineMean [IsProbabilityMeasure P]
    {𝓖 𝓗' : Filtration ℝ≥0 mΩ} {F : Set Ω} (hF : MeasurableSet[𝓖 0] F)
    {Qc : ℝ≥0 → Ω → ℝ≥0} {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) (a : ℝ)
    (hQc : ∀ ω, Continuous fun t => Qc t ω) (hQm : ∀ ω, Monotone fun t => Qc t ω)
    (hQ0 : ∀ ω, Qc 0 ω = 0) (hQa : ∀ t, Measurable[𝓖 t] (Qc t))
    (h𝓗' : ∀ q D, MeasurableSet[𝓗' q] D → ∀ t,
      MeasurableSet[𝓖 t] (D ∩ {ω | q ≤ Qc t ω}))
    (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F →
      (q : ℝ≥0∞) < ζ ω → ∃ t, q ≤ Qc t ω)
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsForceReg W VL VR ζ ω)
    (hS : ∀ (ψ : TestOn upperHalfPlaneOpens) t,
      MeasurableSet[𝓖 t] (lineSafe Qc W ζ (tsupport ψ) t))
    (𝒢L : ℝ≥0 → MeasurableSpace Ω) (h𝒢L : ∀ t, 𝓖 t ≤ 𝒢L t)
    (h𝒢Lm : ∀ t, 𝒢L t ≤ mΩ)
    (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hker : FCLineKernelStatement (P := P) (F := F) (Qc := Qc) (c := c) (W := W)
      (ζ := ζ) (h := h) 𝒢L M)
    (hmean : FCLineMeanStatement (P := P) (κ := κ) (ρL := ρL) (ρR := ρR)
      (F := F) (Qc := Qc) (c := c) (W := W) (VL := VL) (VR := VR) (ζ := ζ)
      hc a M) :
    HasSafeLaw κ ρL ρR P 𝓗' F ζ W VL VR fun ω =>
      Chart.chartTransport (hc ω) 1 a (chiC κ) (h ω) := by
  exact hasSafeLaw_of_lineKernel hF hc hdom hfwd hliftm hliftc hh a (chiC κ)
    hQc hQm hQ0 hQa h𝓗' hreach hreg hS 𝒢L h𝒢L h𝒢Lm M hker hmean

/-- The (L) input for the first-contact continuation, with the marked random set taken to be the later-line
union `shUnion η₁ η₂ t 0`. The locality and chart-domain identity are precisely the geometric inputs required by
`hasSafeMembers_of_lineLocal`; measurability of the random set is supplied by the existing `measurable_shUnion`.
-/
theorem hasSafeMembers_of_FCShUnion [IsProbabilityMeasure P]
    {𝓖 𝓗' : Filtration ℝ≥0 mΩ} {F : Set Ω} {Qc : ℝ≥0 → Ω → ℝ≥0}
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom) (a k : ℝ)
    (hQc : ∀ ω, Continuous fun t => Qc t ω) (hQm : ∀ ω, Monotone fun t => Qc t ω)
    (hQ0 : ∀ ω, Qc 0 ω = 0) (hQa : ∀ t, Measurable[𝓖 t] (Qc t))
    (h𝓗' : ∀ q D, MeasurableSet[𝓗' q] D → ∀ t,
      MeasurableSet[𝓖 t] (D ∩ {ω | q ≤ Qc t ω}))
    (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F →
      (q : ℝ≥0∞) < ζ ω → ∃ t, q ≤ Qc t ω)
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsForceReg W VL VR ζ ω)
    (hS : ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t,
      MeasurableSet[𝓖 t] (lineSafe Qc W ζ (ballsK Fb) t))
    (η₁ η₂ : Ω → ℝ≥0 → ℂ)
    (hc₁ : ∀ ω, Continuous (η₁ ω)) (hc₂ : ∀ ω, Continuous (η₂ ω))
    (hηm₁ : ∀ t, Measurable fun ω => η₁ ω t) (hηm₂ : ∀ t, Measurable fun ω => η₂ ω t)
    (ℋ : ℝ≥0 → MeasurableSpace Ω) (h𝓖ℋ : ∀ t, 𝓖 t ≤ ℋ t) (hℋ : ∀ t, ℋ t ≤ mΩ)
    (hopen : ∀ t ω, IsOpen (H \ shUnion η₁ η₂ t 0 ω))
    (hloc : ∀ t, IsHistoryAvoidanceLocal (ℋ t) (shUnion η₁ η₂ t 0)
      (centredField h u₀) P)
    (hBK : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (Qc t ω : ℝ≥0∞) < ζ ω →
      H \ shUnion η₁ η₂ t 0 ω = (c ω).2.1 ''
        (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (Qc t ω))) :
    HasSafeMembers P 𝓗' F ζ W fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) := by
  have hBm (t : ℝ≥0) : Measurable[mΩ, hittingSigma] (shUnion η₁ η₂ t 0) :=
    measurable_shUnion hc₁ hc₂ hηm₁ hηm₂ t 0
  have hBc (t : ℝ≥0) (ω : Ω) :
      shUnion η₁ η₂ t 0 ω ⊆ H ∧ IsOpen (H \ shUnion η₁ η₂ t 0 ω) :=
    ⟨inter_subset_right, hopen t ω⟩
  exact hasSafeMembers_of_lineLocal hhm hu₀ hh0 hc hdom hfwd hliftm hliftc hlift a k
    hQc hQm hQ0 hQa h𝓗' hreach hreg hS ℋ h𝓖ℋ hℋ (shUnion η₁ η₂ · 0) hBm hBc hloc hBK

end Restart.FCPlumb

end InteractingSLE
