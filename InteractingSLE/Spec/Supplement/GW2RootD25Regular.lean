/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootD25Physical

/-!
# Regularity in the original physical flow clock

Packet PROVE-T14-GW2ROOT2. Physical tip continuity follows from the actual
boundary chart, and physical boundary occupation is the original flow's
boundary occupation. Driver continuity follows by composing the landed
relative driver with the strictly increasing actual capacity clock.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootD25

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.CoordB RootB23

variable {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
  {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) (ζ ω) α)
  (hW : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω}) (hW0 : W 0 ω = 0)
  {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ ω) (hsH : α s ∈ H)
  {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ}
  (hγ : IsGeneratingTrace e.1 e.2 γ) {v : ℝ≥0}
  (hv : (v : ℝ≥0∞) < min
    (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
      ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) e.2)
  {a : ℝ≥0} (ha : 0 < a)

include hα hW hW0 hs hsH he hγ hv ha

theorem continuousOn_physicalObservationRead_snd :
    ContinuousOn (fun t : ℝ => (physicalObservationRead a s v t.toNNReal
      (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)).2) (Icc 0 (v : ℝ)) := by
  have hc := ((continuousOn_const (c := ((a : ℝ) : ℂ))).mul
    (RootA22.continuousOn_record_relBdry_before_contact
    W ζ ω hα hW hW0 hs he hγ hv)).comp continuous_real_toNNReal.continuousOn
    (fun t (ht : t ∈ Icc (0 : ℝ) v) =>
      ⟨zero_le, Real.toNNReal_le_iff_le_coe.mpr ht.2⟩)
  apply hc.congr
  intro t ht
  exact physicalObservationRead_snd_eq W ζ ω hα hW hW0 hs hsH he hγ hv ha
    (Real.toNNReal_le_iff_le_coe.mpr ht.2)

/-- Null boundary occupation is proved in physical capacity, without
transporting a null set through an arbitrary inverse time change. -/
theorem volume_physicalObservationRead_snd_notMem_H :
    volume {t : ℝ | t ∈ Ioo 0 (v : ℝ) ∧ (physicalObservationRead a s v t.toNNReal
      (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)).2 ∉ H} = 0 := by
  apply measure_mono_null ?_ (hγ.volume_setOf_notMem_H he.1 he.2.1)
  intro t ht
  have htv : t.toNNReal ≤ v := Real.toNNReal_le_iff_le_coe.mpr ht.1.2.le
  refine ⟨ht.1.1.le, (ENNReal.coe_le_coe.mpr htv).trans_lt (lt_min_iff.mp hv).2, ?_⟩
  exact fun htH => ht.2 ((physicalObservationRead_snd_mem_H_iff
    W ζ ω hα hW hW0 hs hsH he hγ hv ha htv).2 htH)

omit hW hs in
/-- Every strictly earlier physical time lies in the continuous portion
of the actual relative driver. The original driver is only extended by
`toNNReal` to express the real-time regularity required by `ExperimentGeometry`. -/
theorem continuousAt_physicalObservationRead_fst (hWc : Continuous (W · ω))
    (hζ : ζ ω = ⊤) {t : ℝ} (htv : t.toNNReal < v) :
    ContinuousAt (fun q : ℝ => (physicalObservationRead a s v q.toNNReal
      (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)).1) t := by
  have hs : (s : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
  let c := fun q => (RootZ21.forwardCapacity s q p).toNNReal
  obtain ⟨_, hcdrv, _⟩ := relative_readers_generatingTrace_before_contact
    W ζ ω hα hWc hW0 hζ hsH he hγ hv
  obtain ⟨_, hmono, hcont⟩ := RootZ21.forwardCapacity_regular_before_contact
    W ζ ω hα hWc.continuousOn hW0 hs hsH he hγ hv
  have hc : ContinuousOn c (Icc 0 v) :=
    continuous_real_toNNReal.comp_continuousOn hcont
  have hcomp : ContinuousOn (fun q => relativeDriverRead s v (c q) p) (Iio v) := by
    apply hcdrv.comp (hc.mono fun q hq => ⟨zero_le, hq.le⟩)
    intro q hq
    apply ENNReal.coe_lt_coe.mpr
    apply NNReal.coe_lt_coe.mp
    rw [Real.coe_toNNReal _ (RootZ21.forwardCapacity_nonneg _ _ _),
      Real.coe_toNNReal _ (RootZ21.forwardCapacity_nonneg _ _ _)]
    exact hmono ⟨zero_le, hq.le⟩ ⟨zero_le, le_rfl⟩ hq
  have hAt := (((continuousOn_const (c := (a : ℝ))).mul hcomp).continuousAt
    (isOpen_Iio.mem_nhds htv)).comp continuous_real_toNNReal.continuousAt
  apply hAt.congr
  exact Eventually.of_forall fun q =>
    (congrArg Prod.fst (physicalObservationRead_eq ha s v q.toNNReal p)).symm

end InteractingSLE.Theorem14.GW2TipSystem.RootD25
