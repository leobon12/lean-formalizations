/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWZTopology

/-! # Identifying the selected component by its original target

Original-target collars identify the physical domain of the weak chart
with that of the fully normalized chart. No equality of chart maps or
of inherited lifts is inferred from equality of domains.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWAC
open Aux61SlitW Aux61SlitWX Aux61R1C Aux61Restart Aux61Asm2 LawUnique

/-- Two retained components marked by the original right target agree.
This is the existing target-collar uniqueness theorem in physical form. -/
theorem component_eq_of_target {K : Set ℂ} {η : ℝ → ℂ} {r : ℝ} {b d : ℂ}
    (hc : ContinuousOn η (Icc 0 r)) (h0 : η 0 = 0) (hH : MapsTo η (Ioc 0 r) H)
    (hK : (1 : ℂ) ∉ closure K)
    (hb : (1 : ℂ) ∈ closure (restartComponent K η r b))
    (hd : (1 : ℂ) ∈ closure (restartComponent K η r d)) :
    restartComponent K η r b = restartComponent K η r d :=
  connectedComponentIn_eq_of_original_target_collars
    (exists_original_right_target_component_collar hc h0 hH hK hb)
    (exists_original_right_target_component_collar hc h0 hH hK hd)

universe u
variable {S : SourceSetting.{u}} (C : RestartChoices S)

/-- The target-mark clause alone identifies the weak chart's physical
domain with the normalized R1 domain on the actual selected samples. -/
theorem ae_domain_eq_normalized_of_target (hsel : ∀ i, MeasurableSet (C.selected i))
    (htarget : ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i → (1 : ℂ) ∈ closure
      ((sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom : Set ℂ)) :
    ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i →
      (sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom =
        (sourceChart (source C.toR1Restart C.hasChart) (rationalTime S.s)
          S.own.W S.own.VL S.own.VR S.life i p).dom := by
  have R := Aux61SlitWZ.readers C hsel
  intro i
  filter_upwards [Aux61SlitWZ.ae_domain C i, R.ae_domain C.hasChart i,
    S.physical_path, S.counterflow_retained_geometry, htarget i]
    with p hd hn hp hcf ht he
  obtain ⟨b, hb⟩ := hd he
  obtain ⟨d, hd⟩ := hn he
  have hm := (chart_spec C.toR1Restart C.hasChart i).target
    (sourceRecord C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)
  change (1 : ℂ) ∈ closure ((sourceChart (source C.toR1Restart C.hasChart)
    (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom : Set ℂ) at hm
  apply TopologicalSpace.Opens.ext
  rw [hb, hd]
  exact component_eq_of_target (hp.2.2.cont.mono Icc_subset_Ici_self) hp.2.2.zero
    (fun t ht => hp.2.2.mem_H t ht.1) (hcf (rationalTime S.s)).2.2.2
    (hb ▸ ht he) (hd ▸ hm)

end InteractingSLE.Sec5.Aux61SlitWAC
