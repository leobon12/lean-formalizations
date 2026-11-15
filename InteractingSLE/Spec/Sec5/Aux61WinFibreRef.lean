/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61WinFibreKernel
import InteractingSLE.Spec.Sec5.Aux61R45Converse

/-!
# The tilted restart fibre is a stopped reference flow line; transfer of null events (Aux. lemmas 62 and 64)

Packet PROVE-AUX61-WIN. Specification Aux. lemma 62 (p. 263: "uniqueness of the integrated finite-force driving law
identifies the weighted stopped path law […] It is sufficient, in particular, to transfer probability-zero events
about the first boundary endpoint") and Aux. lemma 64 (p. 265: "The reference probability of ending in `I₀` at that
contact is zero, hence so is the actual probability on this localized event"); Astra's follow-up 4 L248–L262.

* `RestartFibre.Comparison.Clock` — the clock and locality data of the tilted fibre: right-continuous filtration, the
  clock `e` a stopping time with announcing sequences in the fibre's and in the reference driving filtration, the
  reference threshold bound, the killed driving measurability, strict-stop locality of the hulls for the shifted field
  under the tilt, the generating trace, and the normalization of the tilt (these are the fields of PROVE-AUX61-R45's
  `Aux61R45.ReferenceSetting` other than the kernel, which is `isCouplingCharFun_tilt`);
* **`Clock.toReferenceSetting`**: the tilted fibre as a reference setting;
* **`Clock.exists_isStoppedFlowLine`**: on an independent Brownian enlargement the tilted fibre's path stopped at `e`
  is a stopped flow line of the reference word (R4, PROVE-AUX61-R45's `ReferenceSetting.exists_isStoppedFlowLine`);
* **`Clock.ae_of_stoppedFlowLine`** (the transfer): every almost-sure property of stopped reference flow lines (for
  instance GB7a's exclusion of a first endpoint in the comparison interval, piece R5) holds almost surely for the
  fibre's path and clock under the fibre's own law `P` — the density is strictly positive.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Win

open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open Sec7.PocketTraversal

universe u

namespace RestartFibre

variable {S : Type u} [mS : MeasurableSpace S] {D : RestartFibre S}

namespace Comparison

/-- **The clock and locality data of the tilted fibre**: see the module docstring. -/
structure Clock (C : D.Comparison) where
  Γ : S → ℝ≥0 → ℂ
  tilt_prob : IsProbabilityMeasure C.tilt
  rightContinuous : D.filt.IsRightContinuous
  adapted : StronglyAdapted D.filt D.W
  stopping : IsStoppingTime D.filt fun ω => (D.e ω : WithTop ℝ≥0)
  nullSets : ∀ A, MeasurableSet A → C.tilt A = 0 → MeasurableSet[D.filt 0] A
  T : ℕ → S → ℝ≥0
  announcing : Coupling.IsAnnouncingSeq D.filt C.tilt D.e T
  killed : IsMeasurableKilledDriving D.W (geomLW D.W fun _ => flowLineXL C.bR C.JR 0)
    (geomRW D.W fun _ => flowLineXR C.bR C.JR 0) D.e
  driving_le : drivingFiltration C.tilt killed ≤ D.filt
  σ : ℕ → S → ℝ≥0
  referenceAnnouncing : Coupling.IsAnnouncingSeq (drivingFiltration C.tilt killed) C.tilt D.e σ
  threshold : ∀ᵐ ω ∂C.tilt, D.e ω ≤ MartChar.thresholdTime
    (flowLineRhoL D.κ C.bR C.JR 0 0) (flowLineRhoR D.κ C.bR C.JR 0 0) (D.W · ω)
    (fun i t => geomLW D.W (fun _ => flowLineXL C.bR C.JR 0) i t ω)
    (fun j t => geomRW D.W (fun _ => flowLineXR C.bR C.JR 0) j t ω)
  locality : ∀ (τ : S → WithTop ℝ≥0) (_ : IsStoppingTime D.filt τ),
    (∀ᵐ ω ∂C.tilt, (τ ω : ℝ≥0∞) < D.e ω) →
    IsLocalSet (fun ω => fwdHull (Ito.rpath (D.W · ω)) ((τ ω).untopD 0 : ℝ≥0)) C.chartField C.tilt
  trace : ∀ᵐ ω ∂C.tilt, IsGeneratingTrace (D.W · ω) (D.e ω) (fun t => Γ ω t - 0)

variable {C : D.Comparison}

/-- A field is a translate of itself by `0` with the constant `0`. -/
theorem isTranslateAddConst_zero (κ : ℝ) (X : DistOn upperHalfPlaneOpens) :
    IsTranslateAddConst 0 ((0 : ℝ) * QuantumZipper.chiC κ) X X := by
  intro φ φ' hφ
  have e : φ' = φ := DFunLike.ext _ _ fun z => by rw [hφ z, Complex.ofReal_zero, add_zero]
  rw [e, zero_mul, zero_mul, add_zero]

theorem measurable_chartField : Measurable C.chartField :=
  (Coupling.measurable_add_distOnConst _).comp D.measurable_field

/-- **The tilted fibre as a reference setting** (the input of PROVE-AUX61-R45's general-mean converse). -/
def Clock.toReferenceSetting (K : C.Clock) : Aux61R45.ReferenceSetting S where
  κ := D.κ
  κ_pos := D.κ_pos
  b := C.bR
  J := C.JR
  y := 0
  θ := 0
  P := C.tilt
  prob := K.tilt_prob
  field := C.chartField
  chartField := C.chartField
  measurable_field := measurable_chartField
  translate := fun ω => isTranslateAddConst_zero D.κ (C.chartField ω)
  Γ := K.Γ
  e := D.e
  W := D.W
  zero := D.zero
  continuous := D.continuous
  filt := D.filt
  rightContinuous := K.rightContinuous
  adapted := K.adapted
  stopping := K.stopping
  nullSets := K.nullSets
  T := K.T
  announcing := K.announcing
  killed := K.killed
  driving_le := K.driving_le
  σ := K.σ
  referenceAnnouncing := K.referenceAnnouncing
  threshold := K.threshold
  kernel := C.isCouplingCharFun_tilt
  locality := K.locality
  trace := K.trace

/-- **R4 for the tilted fibre**: on an independent Brownian enlargement, the path stopped at `e` is a stopped flow
line of the reference word from `0`. -/
theorem Clock.exists_isStoppedFlowLine (K : C.Clock) :
    ∃ (ν : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure ν),
      Restart.StoppedExtend.IsStoppedFlowLine D.κ C.bR C.JR 0 0 (C.tilt.prod ν)
        (fun p => C.chartField p.1) (fun p => K.Γ p.1) (fun p => D.e p.1) :=
  K.toReferenceSetting.exists_isStoppedFlowLine

/-- **Transfer of almost-sure path properties from the stopped reference to the fibre** (Aux. lemma 62's
"probability-zero events about the first boundary endpoint"): if every stopped flow line of the reference word, on
every probability space, almost surely has the property `Φ` of its path and clock, then the fibre's path and clock
have `Φ` almost surely under the fibre's own law. -/
theorem Clock.ae_of_stoppedFlowLine (K : C.Clock) {Φ : (ℝ≥0 → ℂ) → ℝ≥0∞ → Prop}
    (hΦ : ∀ {Ω : Type u} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
      (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (e : Ω → ℝ≥0∞),
      Restart.StoppedExtend.IsStoppedFlowLine D.κ C.bR C.JR 0 0 Q h η e → ∀ᵐ ω ∂Q, Φ (η ω) (e ω)) :
    ∀ᵐ ω ∂D.P, Φ (K.Γ ω) (D.e ω) := by
  let _ := K.tilt_prob
  obtain ⟨ν, hν, hst⟩ := K.exists_isStoppedFlowLine
  have hprod := hΦ (C.tilt.prod ν) _ _ _ hst
  have h2 : ∀ᵐ ω ∂C.tilt, ∀ᵐ x ∂ν, Φ (K.Γ ω) (D.e ω) := Measure.ae_ae_of_ae_prod hprod
  have h3 : ∀ᵐ ω ∂C.tilt, Φ (K.Γ ω) (D.e ω) := h2.mono fun ω hω => by
    obtain ⟨_, hx⟩ := hω.exists
    exact hx
  exact C.tilt_equivalent.2.ae_le h3

end Comparison

end RestartFibre

end InteractingSLE.Sec5.Aux61Win
