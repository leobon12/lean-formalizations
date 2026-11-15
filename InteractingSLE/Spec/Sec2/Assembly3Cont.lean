/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.Assembly3Path

/-!
# Theorem 2.2, uniqueness for the admissible entrances: continuation at the horizon

Packet PROVE-SEC2-PATCH4.

* `Assembly3.isIntegratedSLEEvolution_contClosed`: the variant of
  `Assembly2.isIntegratedSLEEvolution_cont` in which the local solution is only given up to the
  continuation time `T` itself (not beyond): the processes being continuous at `T`, the local
  solution before `T` followed by the maximal solution driven by the increments of `B` after `T` is
  an integrated `SLE_a(ρ)` evolution. This is what a Girsanov change of measure cut at `T` provides.
* `Assembly3.stopK`: a process that is adapted and continuous before a random time `ζ`, killed at
  `ζ` and stopped at a stopping time `T`; it is adapted (`measurable_stopK`: the killed process is
  right-continuous, hence progressively measurable) and continuous where `T < ζ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace Assembly3

open Assembly Assembly2

variable {a : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

section ContClosed

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsRightContinuous] {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ≥0}

/-- **Continuation at the horizon.** Let `W`, `V` be continuous adapted processes that almost
surely form a local solution of the ordered word `(xL; xR)` up to a positive finite stopping time
`T` at which the word seen from the driver is almost surely good. Then the local solution before
`T`, followed by the maximal local solution driven by the increments of `B` after `T`, is an
integrated `SLE_a(ρ)` evolution. -/
theorem isIntegratedSLEEvolution_contClosed (ha : 0 < a) (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hWa : ∀ t, Measurable[𝓕 t] (W t))
    (hVLa : ∀ i t, Measurable[𝓕 t] (VL i t)) (hVRa : ∀ j t, Measurable[𝓕 t] (VR j t))
    (hWc : ∀ ω, Continuous (W · ω)) (hVLc : ∀ i ω, Continuous (VL i · ω))
    (hVRc : ∀ j ω, Continuous (VR j · ω))
    (hpath : ∀ᵐ ω ∂P, IsSLEPathUpTo a xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (B · ω) (T ω))
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) (hT0 : ∀ ω, 0 < T ω)
    (hgood : ∀ᵐ ω ∂P, GoodWord ρL ρR (contWord W VL VR T ω)) :
    IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕
      (fun t ω => (contState a ρL ρR W VL VR B T t ω).1)
      (fun i t ω => (contState a ρL ρR W VL VR B T t ω).2.1 i)
      (fun j t ω => (contState a ρL ρR W VL VR B T t ω).2.2 j) B
      (fun ω => (T ω : ℝ≥0∞) + contLife a ρL ρR W VL VR B T ω) := by
  have hBa : ∀ t, Measurable[𝓕 t] (B t) := hB.2.1
  have hξ := measurable_contWord hWa hVLa hVRa hWc hVLc hVRc hT
  have hgp := ae_mem_of_strongMarkov hB hBc hT hξ (measurableSet_goodPair (a := a) (ρL := ρL)
    (ρR := ρR)) (ae_mem_goodPair ha hB hBc)
  refine ⟨hB, fun t A hA => ?_, fun i t A hA => ?_, fun j t A hA => ?_, ?_⟩
  · exact measurableSet_contState hWa hVLa hVRa hWc hVLc hVRc hBa hBc hT t (measurable_fst hA)
  · exact measurableSet_contState hWa hVLa hVRa hWc hVLc hVRc hBa hBc hT t
      (((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)) hA)
  · exact measurableSet_contState hWa hVLa hVRa hWc hVLc hVRc hBa hBc hT t
      (((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)) hA)
  · filter_upwards [hpath, hgood, hgp] with ω hp hg hgp'
    obtain ⟨h0, hN⟩ := hgp' hg
    have hgc : Continuous (QuantumZipper.StrongMarkov.smPath B T ω) :=
      ((hBc ω).comp (continuous_const.add continuous_id)).sub continuous_const
    have h₂ := isIntegratedSLEPath_maxCode_of_good (a := a) hg hgc h0 hN
    have hc : ContinuousAt (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)) (T ω) :=
      ((hWc ω).prodMk ((continuous_pi fun i => hVLc i ω).prodMk
        (continuous_pi fun j => hVRc j ω))).continuousAt
    exact hp.isIntegratedSLEPath_concat_closed (hT0 ω) hc (hBc ω).continuousAt h₂ fun t => rfl

end ContClosed

/-! ### Killed and stopped processes -/

section Stop

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞}
  {T : Ω → ℝ≥0} {X : ℝ≥0 → Ω → ℝ}

/-- The process `X` killed at `ζ` and stopped at `T`. -/
def stopK (ζ : Ω → ℝ≥0∞) (T : Ω → ℝ≥0) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Girsanov.killed ζ X (min t (T ω)) ω

/-- A process continuous before `ζ`, killed at `ζ`, is right-continuous. -/
theorem continuousWithinAt_killed {ω : Ω} (hXc : ContinuousOn (X · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (t : ℝ≥0) : ContinuousWithinAt (Girsanov.killed ζ X · ω) (Ici t) t := by
  by_cases ht : (t : ℝ≥0∞) < ζ ω
  · have hU : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} :=
      isOpen_lt ENNReal.continuous_coe continuous_const
    refine ((hXc.continuousAt (hU.mem_nhds ht)).congr ?_).continuousWithinAt
    filter_upwards [hU.mem_nhds ht] with s hs
    exact (Girsanov.killed_of_lt hs).symm
  · refine continuousWithinAt_const (b := (0 : ℝ)).congr (fun s hs => ?_) ?_
    · have : ¬ (s : ℝ≥0∞) < ζ ω := fun h => ht (lt_of_le_of_lt (by exact_mod_cast hs) h)
      simp [Girsanov.killed, this]
    · simp [Girsanov.killed, ht]

/-- **The killed and stopped process is adapted.** -/
theorem measurable_stopK (hX : AdaptedBefore 𝓕 ζ X)
    (hXc : ∀ ω, ContinuousOn (X · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) (t : ℝ≥0) :
    Measurable[𝓕 t] (stopK ζ T X t) := by
  have hK : StronglyAdapted 𝓕 (Girsanov.killed ζ X) := fun s =>
    (Girsanov.measurable_killed hX s).stronglyMeasurable
  have hprog := isStronglyProgressive_of_rightContinuous hK fun ω s =>
    continuousWithinAt_killed (hXc ω) s
  have h := hprog.stronglyAdapted_stoppedProcess hT t
  have e : stopK ζ T X t = stoppedProcess (Girsanov.killed ζ X)
      (fun ω => (T ω : WithTop ℝ≥0)) t := by
    funext ω
    simp only [stopK, stoppedProcess, ← WithTop.coe_min]
    rfl
  rw [e]
  exact h.measurable

/-- The killed and stopped process is continuous where `T < ζ`. -/
theorem continuous_stopK {ω : Ω} (hXc : ContinuousOn (X · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hTζ : (T ω : ℝ≥0∞) < ζ ω) : Continuous (stopK ζ T X · ω) := by
  have hlt : ∀ t : ℝ≥0, ((min t (T ω) : ℝ≥0) : ℝ≥0∞) < ζ ω := fun t =>
    lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) hTζ
  have e : (stopK ζ T X · ω) = fun t => X (min t (T ω)) ω :=
    funext fun t => Girsanov.killed_of_lt (hlt t)
  rw [e]
  exact hXc.comp_continuous (continuous_id.min continuous_const) hlt

/-- The killed and stopped process agrees with the process up to `T < ζ`. -/
theorem stopK_of_le {ω : Ω} (hTζ : (T ω : ℝ≥0∞) < ζ ω) {t : ℝ≥0} (ht : t ≤ T ω) :
    stopK ζ T X t ω = X t ω := by
  rw [stopK, min_eq_left ht]
  exact Girsanov.killed_of_lt (lt_of_le_of_lt (by exact_mod_cast ht) hTζ)

end Stop

end Assembly3

end Sec2

end InteractingSLE
