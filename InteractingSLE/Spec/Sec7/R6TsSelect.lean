/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TrWindow

/-!
# Selecting fixed negative-side R.6 data from the common interval

PROVE-R6-TWO, Astra §§2.5 and 4 (R98). The interval, its compact
envelope, and both test points are chosen here. There is no physical
neighbourhood hypothesis at the force landing.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec7.R6Ts

open PocketStopSide

/-- The connected shared interval, its real boundary correspondence,
the current-tip local ball, and shared-wall balls supply all the
same-time data needed by the checked real-time window. The chosen
compact interval lies strictly to the left of the driver. -/
theorem sameTimeLeftData_of_incident_interval
    {O I₀ : Chart} {EO : ℂ → ℂ} {P : Set ℂ} {p : ℂ} {v w : ℝ}
    (hIncl : (I₀.dom : Set ℂ) ⊆ O.dom)
    (hEOc : ContinuousOn EO Hbar) (hEO0 : EO 0 = p)
    (hfibre : ∀ x : ℝ, EO (x : ℂ) = p → x = 0)
    {S : Set ℝ} (hSo : IsOpen S) (hSc : IsPreconnected S)
    (hvS : v ∈ S) (h0S : 0 ∈ S) (hv : v < 0)
    (hcollars : ∀ x ∈ S, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆ O.1 '' (I₀.dom : Set ℂ))
    (hlanding : ∀ x ∈ S, EO (x : ℂ) ∈ P)
    {g : ℝ → ℝ} (hg : StrictMonoOn g S) (hg0 : g 0 = 0) (hgv : g v = w)
    (hlim : ∀ x ∈ S, Tendsto (pocketTransitionChart O I₀).1
      (𝓝[((pocketTransitionChart O I₀).dom : Set ℂ)] (x : ℂ)) (𝓝 (g x : ℂ)))
    (htip : ∃ r > 0, (O.dom : Set ℂ) ∩ ball p r ⊆ I₀.dom)
    (hshared : ∀ x ∈ S, x < v →
      ∃ r > 0, (O.dom : Set ℂ) ∩ ball (EO (x : ℂ)) r ⊆ I₀.dom) :
    Nonempty (R6Tr.SameTimeLeftData O I₀ EO P p v w) := by
  obtain ⟨δ, hδ, hδS⟩ := Metric.isOpen_iff.1 hSo v hvS
  let a := v - δ / 2
  let y := v - δ / 4
  have hav : a < v := by dsimp [a]; linarith
  have hay : a < y := by dsimp [a, y]; linarith
  have hyv : y < v := by dsimp [y]; linarith
  have haS : a ∈ S := by
    apply hδS
    rw [mem_ball, Real.dist_eq, abs_of_neg (sub_neg.2 hav)]
    dsimp [a]
    linarith
  have hyS : y ∈ S := hSc.ordConnected.out haS hvS ⟨hay.le, hyv.le⟩
  obtain ⟨ξ, hvξ, hξ0, -, hξp, hξball⟩ := R6Tr.exists_negative_exposed_landing
    hEOc hEO0 hfibre isOpen_univ (mem_univ p) htip hv
  let b := ξ / 2
  have hξb : ξ < b := by dsimp [b]; linarith
  have hb0 : b < 0 := by dsimp [b]; linarith
  have hbS : b ∈ S := hSc.ordConnected.out hvS h0S ⟨(hvξ.trans hξb).le, hb0.le⟩
  have hξS : ξ ∈ S := hSc.ordConnected.out hvS h0S ⟨hvξ.le, hξ0.le⟩
  have hKS : Icc a b ⊆ S := hSc.ordConnected.out haS hbS
  have hyJ : y ∈ Ioo a b := ⟨hay, hyv.trans (hvξ.trans hξb)⟩
  have hξJ : ξ ∈ Ioo a b := ⟨hav.trans hvξ, hξb⟩
  refine ⟨{
    compact := Icc a b, interval := Ioo a b, shared := y, exposed := ξ, boundary := g,
    isCompact := isCompact_Icc, interval_subset := Ioo_subset_Icc_self,
    isOpen := isOpen_Ioo, isPreconnected := isPreconnected_Ioo,
    shared_mem := hyJ, exposed_mem := hξJ,
    shared_lt := hyv, lt_exposed := hvξ, exposed_neg := hξ0,
    inclusion := hIncl,
    collars := fun x hx => hcollars x (hKS hx),
    avoids_tip := ?_,
    landing_mem := fun x hx => hlanding x (hKS (Ioo_subset_Icc_self hx)),
    boundary_limit := fun x hx => hlim x (hKS (Ioo_subset_Icc_self hx)),
    shared_image_lt := ?_, lt_exposed_image := ?_, exposed_image_neg := ?_,
    shared_ball := hshared y hyS hyv, exposed_ball := hξball }⟩
  · intro x hx heq
    exact (hx.2.trans_lt hb0).ne (hfibre x heq)
  · rw [← hgv]
    exact hg hyS hvS hyv
  · rw [← hgv]
    exact hg hvS hξS hvξ
  · rw [← hg0]
    exact hg hξS h0S hξ0

end InteractingSLE.Sec7.R6Ts
