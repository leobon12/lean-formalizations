/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61R2Glue
import InteractingSLE.Spec.Sec5.Aux61R2TiltData
import InteractingSLE.Spec.Sec5.Aux61R45ClockAssembly

/-!
# The clock of the corrected fibre from PROVE-AUX61-R45's reference clock (piece R2f, reduced)

Packet PROVE-AUX61-R2. PROVE-AUX61-R45 constructs, from a fibre's own killed driver and path (`ClockSource`), the
regularized exit clock of a buffer with announcing sequences, an adapted continuous driver, killed measurability,
the reference threshold and the generating trace (`ClockSource.exists_referenceClock`, with the three named path
inputs `hU_announcing`, `hU_leftLimit`, `hinterior`). This file turns such a `ReferenceClock` (seed `0`) into the
`Clock` of the corrected fibre's canonical tilt: every field except locality under the tilt is transported from the
fibre's law to the equivalent tilted law.

* `nullSigma_congr`, `usualAugmentation_congr`, **`drivingFiltration_congr`**: the completed driving filtration only
  depends on the null sets, hence is the same for equivalent laws;
* `isAnnouncingSeq_of_ac`: announcing sequences pass to absolutely continuous laws;
* **`RefFibre.TiltData.clockOfReferenceClock`**: the clock of a tilted fibre whose driver, clock and filtration are
  those of a reference clock (seed `0`) of a clock source with the fibre's law, given the tilt is a probability
  measure (`RefFibre.isProbabilityMeasure_tilt` for the canonical tilt) and locality of the pre-clock hulls for the
  shifted field under the tilt.

What is left of R2f after this file is exactly the `locality` input (and R45's three path inputs for the fibre).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61R2

open QuantumZipper (fwdHull)
open Sec7.PocketTraversal

universe u

/-- The σ-algebra of null sets only depends on the null sets. -/
theorem nullSigma_congr {Ω : Type*} [MeasurableSpace Ω] {P Q : Measure Ω} (h1 : P ≪ Q) (h2 : Q ≪ P) :
    nullSigma P = nullSigma Q := by
  unfold nullSigma
  congr 1
  ext s
  exact ⟨fun ⟨hs, h0⟩ => ⟨hs, h2 h0⟩, fun ⟨hs, h0⟩ => ⟨hs, h1 h0⟩⟩

/-- The usual augmentation is the same for equivalent laws. -/
theorem usualAugmentation_congr {Ω : Type*} [MeasurableSpace Ω] {P Q : Measure Ω} (h1 : P ≪ Q) (h2 : Q ≪ P)
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) : usualAugmentation 𝓕 P = usualAugmentation 𝓕 Q := by
  have h := nullSigma_congr h1 h2
  unfold usualAugmentation
  simp only [h]

/-- **The completed driving filtration is the same for equivalent laws.** -/
theorem drivingFiltration_congr {Ω : Type*} [MeasurableSpace Ω] {P Q : Measure Ω} (h1 : P ≪ Q) (h2 : Q ≪ P)
    {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hX : IsMeasurableKilledDriving W VL VR ζ) : drivingFiltration P hX = drivingFiltration Q hX :=
  usualAugmentation_congr h1 h2 _

/-- The killed driving filtration only depends on the killed processes. -/
theorem killedDrivingFiltration_congr {Ω : Type*} [MeasurableSpace Ω] {nL nR : ℕ}
    {W W' : ℝ≥0 → Ω → ℝ} {VL VL' : Fin nL → ℝ≥0 → Ω → ℝ} {VR VR' : Fin nR → ℝ≥0 → Ω → ℝ} {ζ ζ' : Ω → ℝ≥0∞}
    (hW : W = W') (hVL : VL = VL') (hVR : VR = VR') (hζ : ζ = ζ') (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hX' : IsMeasurableKilledDriving W' VL' VR' ζ') : killedDrivingFiltration hX = killedDrivingFiltration hX' := by
  subst hW hVL hVR hζ
  rfl

/-- Announcing sequences pass to absolutely continuous laws. -/
theorem isAnnouncingSeq_of_ac {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {P Q : Measure Ω}
    {ζ : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0} (h : Coupling.IsAnnouncingSeq 𝓖 P ζ T) (hQP : Q ≪ P) :
    Coupling.IsAnnouncingSeq 𝓖 Q ζ T :=
  ⟨h.1, h.2.1, fun n => hQP.ae_le (h.2.2.1 n), hQP.ae_le h.2.2.2⟩

namespace RefFibre

variable {S : Type u} [mS : MeasurableSpace S] {D : RefFibre S}

namespace TiltData

/-- **The clock of the tilted fibre from a reference clock** (R2f): if the fibre's law, driver, clock and filtration
are those of a reference clock (seed `0`, the fibre's reference word, angle `0`) of a clock source started at `0`, the
tilt is a probability measure and the pre-clock hulls are local for the shifted field under the tilt, then the
tilted fibre has its `Clock` (all other fields transported from the fibre's law to the equivalent tilted law). -/
def clockOfReferenceClock (T : D.TiltData) (CS : Aux61R45.ClockSource S) (hy : CS.y = 0) {V : Set ℂ}
    (RC : Aux61R45.ReferenceClock CS D.κ D.bR D.JR 0 V) (hP : D.P = CS.P) (hW : D.W = RC.W) (he : D.e = RC.e)
    (hfilt : D.filt = CS.driving) (hprob : IsProbabilityMeasure T.tilt)
    (hloc : ∀ (τ : S → WithTop ℝ≥0) (_ : IsStoppingTime D.filt τ),
      (∀ᵐ ω ∂T.tilt, (τ ω : ℝ≥0∞) < D.e ω) →
      IsLocalSet (fun ω => fwdHull (Ito.rpath (D.W · ω)) ((τ ω).untopD 0 : ℝ≥0)) D.chartField T.tilt) :
    T.Clock :=
  have hQP : T.tilt ≪ CS.P := hP ▸ T.tilt_equivalent.1
  have hPQ : CS.P ≪ T.tilt := hP ▸ T.tilt_equivalent.2
  have hkilled : IsMeasurableKilledDriving D.W (geomLW D.W fun _ => flowLineXL D.bR D.JR 0)
      (geomRW D.W fun _ => flowLineXR D.bR D.JR 0) D.e := by
    have h := RC.killed
    rw [hy] at h
    rw [hW, he]; exact h
  have hdrv : drivingFiltration T.tilt hkilled = drivingFiltration CS.P RC.killed := by
    rw [drivingFiltration_congr hQP hPQ hkilled]
    have key : ∀ y : ℝ, y = 0 → ∀ X : IsMeasurableKilledDriving RC.W (geomLW RC.W fun _ => flowLineXL D.bR D.JR y)
        (geomRW RC.W fun _ => flowLineXR D.bR D.JR y) RC.e,
        drivingFiltration CS.P hkilled = drivingFiltration CS.P X := by
      intro y hy0 X
      subst hy0
      have hL : (geomLW D.W fun _ => flowLineXL D.bR D.JR 0) = geomLW RC.W fun _ => flowLineXL D.bR D.JR 0 := by
        rw [hW]
      have hR : (geomRW D.W fun _ => flowLineXR D.bR D.JR 0) = geomRW RC.W fun _ => flowLineXR D.bR D.JR 0 := by
        rw [hW]
      unfold drivingFiltration
      rw [killedDrivingFiltration_congr hW hL hR he hkilled X]
    exact key CS.y hy RC.killed
  { Γ := CS.Γ
    tilt_prob := hprob
    rightContinuous := by rw [hfilt]; infer_instance
    adapted := by rw [hfilt, hW]; exact RC.adapted
    stopping := by rw [hfilt, he]; exact RC.stopping
    nullSets := fun A hA h0 => by
      rw [hfilt]
      exact Ito.measurableSet_usualAugmentation_of_null hA (hPQ h0) 0
    Tn := RC.T
    announcing := by rw [hfilt, he]; exact isAnnouncingSeq_of_ac RC.announcing hQP
    killed := hkilled
    driving_le := by rw [hdrv, hfilt]; exact RC.driving_le
    σ := RC.T
    referenceAnnouncing := by rw [hdrv, he]; exact isAnnouncingSeq_of_ac RC.referenceAnnouncing hQP
    threshold := by
      have h := RC.threshold
      rw [hy] at h
      rw [hW, he]
      exact hQP.ae_le h
    locality := hloc
    trace := by
      rw [hW, he]
      refine hQP.ae_le ?_
      filter_upwards [RC.trace] with ω hω
      simpa only [hy, Complex.ofReal_zero] using hω }

end TiltData

end RefFibre

end InteractingSLE.Sec5.Aux61R2
