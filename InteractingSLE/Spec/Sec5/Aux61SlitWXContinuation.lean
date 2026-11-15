/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWXGeometry

/-! # The physical continuation stays in the selected component until contact -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H fwdHull fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWX
open Aux61SlitW Aux61Asm2 Aux61Restart Aux61FibData Aux61Marks Aux61ULoc LawUnique

/-- A continuous simple continuation cannot change retained component
before hitting the obstacle. Its initial component is fixed by the current
collar, not by an assumed future segment. -/
theorem continuation_mem_component {W : ℝ → ℝ} {η : ℝ → ℂ} {K : Set ℂ} {r : ℝ≥0}
    {c : Chart} {b : ℂ} {ρ : ℝ≥0 → ℂ} {T : ℝ≥0∞}
    (hg : SourceChartGeometry W η K r c) (hW : Continuous W) (hW0 : W 0 = 0)
    (hη : IsLoewnerTrace W η) (harc : WangWu.IsProperArc η)
    (hKo : IsOpen (H \ K)) (hclear : 0 < infDist (η r) K)
    (hdom : (c.dom : Set ℂ) = restartComponent K η r b)
    (hρ : Continuous ρ) (hversion : ∀ v : ℝ≥0, ρ v = η (r + (v : ℝ)))
    (hfirst : T = hitTime (fun _ : Unit => ρ) (fun _ => (H \ K)ᶜ) ())
    {v : ℝ≥0} (hv0 : 0 < v) (hvT : (v : ℝ≥0∞) < T) : ρ v ∈ c.dom := by
  have : (𝓝[H] (0 : ℂ)).NeBot := PrimeEnd.approachH_neBot (0 : ℝ)
  have hfreq : ∃ᶠ w in 𝓝[H] 0, fwdMapInv W r w ∈ restartComponent K η r b := by
    rw [← hdom]
    exact (eventually_mem_of_collar hg.collar).frequently
  obtain ⟨t, hrt, -, -, hnew⟩ := exists_fresh_segment_in_incident_component
    hW hW0 hη r.coe_nonneg (lt_add_one (r : ℝ))
    (harc.inj.mono Icc_subset_Ici_self) (fun u hu => harc.mem_H u hu.1)
    (harc.mem_H r (NNReal.coe_pos.2 hg.start_pos)) hKo hclear hfreq
  obtain ⟨a, ha0, havt⟩ := exists_between (lt_min (NNReal.coe_pos.2 hv0) (sub_pos.2 hrt))
  have hav := havt.trans_le (min_le_left _ _)
  have hat := havt.trans_le (min_le_right _ _)
  let w : ℝ≥0 := ⟨a, ha0.le⟩
  have hwv : w ∈ Ioc 0 v := ⟨NNReal.coe_pos.1 ha0, NNReal.coe_le_coe.1 hav.le⟩
  have hwD : ρ w ∈ restartComponent K η r b := by
    rw [hversion]
    apply hnew
    change (r : ℝ) < r + a ∧ r + a ≤ t
    constructor
    · linarith
    · linarith [hat]
  have hsub : ρ '' Ioc 0 v ⊆ retainedDomain K η r := by
    rintro _ ⟨u, hu, rfl⟩
    have hoff := notMem_of_lt_hitTime (ρ := fun _ : Unit => ρ) (F := fun _ => (H \ K)ᶜ)
      (x := ()) (u := u) (by rw [← hfirst]; exact (ENNReal.coe_le_coe.2 hu.2).trans_lt hvT)
    have hfree : ρ u ∈ H \ K := not_not.1 hoff
    refine ⟨hfree.1, ?_⟩
    rintro (hK | ⟨z, hz, heq⟩)
    · exact hfree.2 hK
    · rw [hversion] at heq
      have hzu := harc.inj hz.1 (by positivity : (0 : ℝ) ≤ r + (u : ℝ)) heq
      have hupos : (0 : ℝ) < u := NNReal.coe_pos.2 hu.1
      linarith [hz.2]
  have hconn := (isPreconnected_Ioc.image ρ hρ.continuousOn).subset_connectedComponentIn
    (show ρ w ∈ ρ '' Ioc 0 v from ⟨w, hwv, rfl⟩) hsub
  rw [← connectedComponentIn_eq hwD] at hconn
  change ρ '' Ioc 0 v ⊆ restartComponent K η r b at hconn
  rw [← hdom] at hconn
  exact hconn ⟨v, ⟨hv0, le_rfl⟩, rfl⟩

end InteractingSLE.Sec5.Aux61SlitWX
