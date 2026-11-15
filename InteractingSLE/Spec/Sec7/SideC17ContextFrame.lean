/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC17ContextSource
import InteractingSLE.Spec.Sec7.SideC17Family
import InteractingSLE.Spec.Sec7.SideC11Marks

/-! # R100's native zero-offset mean in the actual physical contexts

PROVE-SIDE-COLLAR2. All original mean, branch, transport and native-word
inputs are supplied. The tests and their events remain unrefined.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire.T12Asm3
open Current LocalSets WholeField Sec7 Sec7.SideC17 Sec7.PocketWordIn Sec7.Aux119Heights

variable {Ωw : BothLow → Type} [∀ i, MeasurableSpace (Ωw i)] [∀ i, StandardBorelSpace (Ωw i)]
    {baseWord : ∀ i, Now.StripObjects (Ωw i)} [∀ i, IsProbabilityMeasure (baseWord i).measure]
    {hWordb : ∀ i, IsPiecewiseConstantBoundaryData (baseWord i).boundary (baseWord i).jumps}

/-- The physical context supplies the actual native initial mean with
R100's relift and offset zero, for every ready test simultaneously. -/
theorem PhysCtx.exists_zeroFrame_initial_mean (hC : PhysCtx Ωw baseWord hWordb) (i : BothLow) :
    let x := Relay.words T12Asm2.cond44Holds baseWord hWordb i
    let d := wordSafeObjects i x (hC.wordT i)
    ∃ (G₀ : SideTest (Ωw i) → Ωw i → DistOn upperHalfPlaneOpens)
      (n : SideTest (Ωw i) → Ωw i → ℤ),
      (∀ j, j.Ready d → Measurable[(j.target i d).walls] (n j)) ∧
      InitialPocketConjugateFlowMeanWithChart i d
        (fun j ω => zeroFrameChart ((j.target i d).baseChart ω) (n j ω)) G₀
        (fun j => j.canonicalInitialFlowMean i d) (fun _ _ => 1) (fun _ => 0) ∧
      ∀ j, j.Ready d →
        IsLocalSetMean (j.capacityReference i d 0) (j.target i d).zeroField d.measure
          (initialTransportedMeans i d G₀ j) ∧
        ∀ᵐ ω ∂d.measure, ω ∈ j.event → ∀ z ∈ (j.target i d).domain ω,
          harmRep (initialTransportedMeans i d G₀ j ω) (H \ j.capacityReference i d 0 ω) z +
              (j.target i d).harmonic z + chiC (j.target i d).kappa *
                (zeroFrameChart ((j.target i d).baseChart ω) (n j ω)).2.2 z =
            j.initialWordExtension i d ω (((j.target i d).baseChart ω).1 z) := by
  let x := Relay.words T12Asm2.cond44Holds baseWord hWordb i
  let hS := hC.wordT i
  let d := wordSafeObjects i x hS
  obtain ⟨G₀, n, hn, hSource⟩ := hC.exists_initial_source i
  have hd : 16 / (16 / i.kappa) = i.kappa := by field_simp
  obtain ⟨hT, hTr, _, hu₁⟩ := counterflowObjects_spec hS.counterflow
  have hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(π * chiC (16 / i.kappa)))
      (chiC i.kappa) (d.field ω) (d.chartField ω) := by
    simpa only [d, wordSafeObjects, hd] using hT
  have hTr' : ∀ ω, IsTranslateAddConst 0 0 (d.chartField ω) (d.translatedField ω) := by
    simpa only [d, wordSafeObjects, hd, zero_mul] using hTr
  have hHarm : EqOn d.harmonic d.coupledMean H :=
    fun z _ => congrFun (hC.harmonic_eq i hS.counterflow) z
  have hFrame := initialPocketFlowFrame_zeroFrame_of_conjugateMean i d G₀
    (fun j => j.canonicalInitialFlowMean i d) n hT' hTr' (hC.hWordu₀ i).1 hu₁.1 hHarm
    (hC.hWordvα i).continuous (fun q => (hC.hWordvL i q).continuous) hSource
  refine ⟨G₀, n, hn, hSource.zeroFrame, ?_⟩
  intro j hj
  obtain ⟨hG, hF⟩ := hFrame j hj
  refine ⟨hG, ?_⟩
  filter_upwards [hF] with ω hFω hω z hz
  have hA : ω ∈ (j.target i d).event := by simpa only [SideTest.target_event] using hω
  have hc := j.isDomainChart_baseChart hj (hC.hWordvα i).continuous
    (hC.hWordvL i j.seed).continuous hA
  rw [← j.canonicalInitialFlowMean_normalization hj hA (hc.fwd_mem hz)]
  exact hFω hA z hz

end InteractingSLE.Wire.T12Asm3
