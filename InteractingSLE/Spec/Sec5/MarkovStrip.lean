/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Markov
import InteractingSLE.Spec.Sec4.Counterflow

/-!
# The counterflow Markov principle at its own stopping times (§5)

Packet PROVE-SEC5-D. §5 ("The ambient strip counterflow in this section is explicitly `η' = CF_d(h)`") conditions on an
initial counterflow segment `η'([0, τ'])` at a counterflow stopping time and maps `𝒮 ∖ K'_{τ'}` back (proofs of
Proposition 5.1, p. 135, and Proposition 5.9, p. 140). The counterflow `CF_d(h + αχ)` of the Sec4 carrier
`IsStripCounterflowDriver κ α q` is the Theorem 1.1 curve, in the chart `M_q`, of the parameter field `h'` (the chart
transport of `h`); its driver `W` is coupled with `h'` by the frozen optional hull specification
(`exists_isOptionalHullCoupling`). Aux. lemma 53 (`IsOptionalHullCoupling.restart_condExp`) therefore applies to the
counterflow at every finite stopping time of its driving filtration: after mapping out the initial segment by `f_T`,
the restarted counterflow driver `W_{T+·} − W_T` with the current force data is coupled with the field as Theorem 1.1
demands (`IsStripCounterflowDriver.restart_condExp`).

* `isOptionalHullCoupling_of_isFlowLineDriver_zero`: an angle-`0` driver of the frozen `IsFlowLineDriver` is an optional
  hull coupling of the field itself (the translation by `0·χ` is the identity);
* `Sec4.IsStripCounterflowDriver.exists_isOptionalHullCoupling`: the data of a strip counterflow;
* `Sec4.IsStripCounterflowDriver.restart_condExp`: the counterflow Markov principle at its own stopping times.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper

namespace InteractingSLE

namespace Sec5

namespace Markov

/-- A translation by `0` with constant `0` is the identity. -/
theorem eq_of_isTranslateAddConst_zero {h h' : LQGMetric.DistOn upperHalfPlaneOpens}
    (ht : IsTranslateAddConst 0 0 h h') : h' = h := by
  ext φ
  have := ht φ φ fun z => by rw [Complex.ofReal_zero, add_zero]
  rw [this, zero_mul, add_zero]

/-- **An angle-`0` flow-line driver is an optional hull coupling of the field itself.** -/
theorem isOptionalHullCoupling_of_isFlowLineDriver_zero {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hd : IsFlowLineDriver κ b jumps 0 P h W ζ) :
    ∃ (𝓕 : Filtration ℝ≥0 mΩ) (VL : Fin (flowLineNL b jumps 0) → ℝ≥0 → Ω → ℝ)
      (VR : Fin (flowLineNR b jumps 0) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ),
      IsOptionalHullCoupling κ (flowLineXL b jumps 0) (flowLineXR b jumps 0)
        (flowLineRhoL κ b jumps 0 0) (flowLineRhoR κ b jumps 0 0) P 𝓕 W VL VR B ζ h := by
  obtain ⟨h', 𝓕, VL, VR, B, ht, hC⟩ := hd
  have he : h' = h := funext fun ω => eq_of_isTranslateAddConst_zero (by simpa using ht ω)
  subst he
  exact ⟨𝓕, VL, VR, B, hC⟩

variable {κ α q : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The data of a strip counterflow** `CF_d(h + αχ)` (Sec4 carrier): the parameter field `h'` (chart transport of `h`
by `M_q`, coefficient `χ(16/κ)`), its piecewise constant boundary data `b'`, and the frozen optional hull coupling of
`h'` with the counterflow driver `W` (parameter `16/κ`, angle `0`). -/
theorem _root_.InteractingSLE.Sec4.IsStripCounterflowDriver.exists_isOptionalHullCoupling
    (hS : Sec4.IsStripCounterflowDriver κ α q P h W ζ) :
    ∃ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
      (𝓕 : Filtration ℝ≥0 mΩ) (VL : Fin (flowLineNL b' jumps' 0) → ℝ≥0 → Ω → ℝ)
      (VR : Fin (flowLineNR b' jumps' 0) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ),
      IsPiecewiseConstantBoundaryData b' jumps' ∧
      (∀ ω, IsChartTransport (Sec4.stripCounterflowChart q) (-1) (-((α + Real.pi) * chiC κ))
        (chiC (16 / κ)) (h ω) (h' ω)) ∧
      IsOptionalHullCoupling (16 / κ) (flowLineXL b' jumps' 0) (flowLineXR b' jumps' 0)
        (flowLineRhoL (16 / κ) b' jumps' 0 0) (flowLineRhoR (16 / κ) b' jumps' 0 0) P 𝓕 W VL VR B ζ h' := by
  obtain ⟨b', jumps', h', hb, htr, hd⟩ := hS
  obtain ⟨𝓕, VL, VR, B, hC⟩ := isOptionalHullCoupling_of_isFlowLineDriver_zero hd
  exact ⟨b', jumps', h', 𝓕, VL, VR, B, hb, htr, hC⟩

open Sec2.Restart in
/-- **The counterflow Markov principle at its own stopping times** (Aux. lemma 53 for `η' = CF_d(h + αχ)`; §5,
proofs of Propositions 5.1 and 5.9: "conditioning `h` on `η'([0, τ'])` and conformally mapping `𝒮 ∖ K'_{τ'}` back").
For a strip counterflow there are the parameter field `h'` (in the chart `M_q`) and its coupling with the counterflow
driver such that, at every finite stopping time `T` of the driving filtration, the restarted counterflow driver
`W_{T+·} − W_T` with the current force data satisfies the conditional-law clause of Theorem 1.1 with `h'`, in the
original domain of the chart `f_T` (`IsOptionalHullCoupling.restart_condExp`): for every later stopping time `τ'` of
`𝓕_{T+·}`, every bounded harmonic extension `u` of the force data at `τ'` and every `φ` supported in `F_T(ℍ ∖ K'_{τ'})`,
`E[e^{i (h', φ)} | 𝓕_{T+τ'}]` is the characteristic function of the restarted coupling mean read through `f_T` (minus
`χ(16/κ) arg f_T′`) plus a zero-boundary GFF on `F_T(ℍ ∖ K'_{τ'})`. -/
theorem _root_.InteractingSLE.Sec4.IsStripCounterflowDriver.restart_condExp
    (hS : Sec4.IsStripCounterflowDriver κ α q P h W ζ) :
    ∃ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
      (𝓕 : Filtration ℝ≥0 mΩ) (VL : Fin (flowLineNL b' jumps' 0) → ℝ≥0 → Ω → ℝ)
      (VR : Fin (flowLineNR b' jumps' 0) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ),
      IsPiecewiseConstantBoundaryData b' jumps' ∧
      (∀ ω, IsChartTransport (Sec4.stripCounterflowChart q) (-1) (-((α + Real.pi) * chiC κ))
        (chiC (16 / κ)) (h ω) (h' ω)) ∧
      IsOptionalHullCoupling (16 / κ) (flowLineXL b' jumps' 0) (flowLineXR b' jumps' 0)
        (flowLineRhoL (16 / κ) b' jumps' 0 0) (flowLineRhoR (16 / κ) b' jumps' 0 0) P 𝓕 W VL VR B ζ h' ∧
      ∀ (hX : IsMeasurableKilledDriving W VL VR ζ) (T : Ω → ℝ≥0)
        (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
        (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime (restartFiltration (drivingFiltration P hX) T hT) τ),
        (∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < restartLife ζ T ω) → ∀ u : Ω → ℂ → ℝ,
        (∀ ω, IsBoundedHarmonicExtension
          (forceBoundaryData (16 / κ) (flowLineRhoL (16 / κ) b' jumps' 0 0) (flowLineRhoR (16 / κ) b' jumps' 0 0)
            (fun i => restartMark (VL i) W T ((τ ω).untopD 0) ω - restartDrv W T ((τ ω).untopD 0) ω)
            (fun i => restartMark (VR i) W T ((τ ω).untopD 0) ω - restartDrv W T ((τ ω).untopD 0) ω))
          (forceJumpSet
            (fun i => restartMark (VL i) W T ((τ ω).untopD 0) ω - restartDrv W T ((τ ω).untopD 0) ω)
            (fun i => restartMark (VR i) W T ((τ ω).untopD 0) ω - restartDrv W T ((τ ω).untopD 0) ω))
          (u ω)) →
        ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, tsupport φ ⊆ (restartChart W T ω).2.1 ''
            (H \ fwdHull (fun s : ℝ => restartDrv W T s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
          condExp hτ.measurableSpace P (fun ω' => Complex.exp (Complex.I * (h' ω' φ : ℂ))) ω =
            Complex.exp (Complex.I * ((∫ z, (couplingMean (16 / κ) (fun s : ℝ => restartDrv W T s.toNNReal ω)
                ((τ ω).untopD 0 : ℝ≥0) (u ω) ((restartChart W T ω).1 z) - 0 -
                  chiC (16 / κ) * (restartChart W T ω).2.2 z) * φ z : ℝ) : ℂ) -
              (((1 / 2 : ℝ) * zeroGFFTestCov ((restartChart W T ω).2.1 ''
                (H \ fwdHull (fun s : ℝ => restartDrv W T s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)))
                  φ φ : ℝ) : ℂ)) := by
  obtain ⟨b', jumps', h', 𝓕, VL, VR, B, hb, htr, hC⟩ := hS.exists_isOptionalHullCoupling
  exact ⟨b', jumps', h', 𝓕, VL, VR, B, hb, htr, hC, fun hX T hT τ hτ hτζ u hu φ =>
    hC.restart_condExp hX hT τ hτ hτζ u hu φ⟩

end Markov

end Sec5

end InteractingSLE
