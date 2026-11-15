/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWLandingFields

/-! # Selected-access landing checked at one good sample -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW
open Aux61FibData Aux61GInst Aux61Restart
open WangWu (negInv)

/-- The landing clause at one good sample requires only that sample's
physical trace and first-contact facts. This form applies before cutting
the restart events to a measurable set of pointwise-good samples. -/
theorem selected_landing_at_of_retained {X : Type*} [MeasurableSpace X]
    {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞}
    (hs : IsRestartSpec E c ρ T) {x : X} (hx : x ∈ E)
    {Wcf : ℝ → ℝ} {β η : ℝ → ℂ} {s r : ℝ} (hs0 : 0 ≤ s)
    (hβ : IsLoewnerTrace Wcf β) (hη : ContinuousOn η (Icc 0 r))
    (hηH : MapsTo η (Icc 0 r) Hbar) {b : ℂ}
    (hb : b ∈ retainedDomain (negInv '' fwdHull Wcf s) η r)
    (hdom : ((c x).dom : Set ℂ) = restartComponent (negInv '' fwdHull Wcf s) η r b)
    (hT : T x = hitTime ρ (fun _ => (H \ negInv '' fwdHull Wcf s)ᶜ) x)
    {U V : Set ℂ} (hUb : Bornology.IsBounded U) {δ : ℝ} (hVU : V ⊆ seedExitWindow U δ)
    (hseed : ∀ a : ℝ, |a| < δ →
      boundedInverse (c x) (a : ℂ) ∉ oldModelBoundary (counterflowRecord β s)) :
    0 < T x → Aux61FibData.exitTime E c ρ T V x = T x → T x < ⊤ →
      ∃ L : ℂ, L ∉ V ∧ Tendsto (inPath E c ρ T x) (𝓝[<] (T x).toNNReal) (𝓝 L) := by
  have hsingle : IsRestartSpec (univ : Set Unit) (fun _ => c x) (fun _ => ρ x) (fun _ => T x) :=
    { measurableSet := MeasurableSet.univ
      measT := measurable_const
      measρ := fun _ => measurable_const
      contρ := fun _ _ => hs.contρ x hx
      chart := ⟨fun _ => MeasurableSet.const _,
        fun _ => measurable_const.indicator (MeasurableSet.const _),
        fun _ => measurable_const.indicator (MeasurableSet.const _)⟩
      conf := fun _ _ => hs.conf x hx
      start_mem := fun _ _ => hs.start_mem x hx
      start_lim := fun _ _ => hs.start_lim x hx
      inside := fun _ _ => hs.inside x hx }
  have hpath : inPath (univ : Set Unit) (fun _ => c x) (fun _ => ρ x) (fun _ => T x) () =
      inPath E c ρ T x := by
    funext u
    simp only [inPath, mem_univ, hx, true_and]
  have htime : Aux61FibData.exitTime (univ : Set Unit) (fun _ => c x) (fun _ => ρ x)
      (fun _ => T x) V () = Aux61FibData.exitTime E c ρ T V x := by
    unfold Aux61FibData.exitTime
    congr 1
    funext a
    have hm : () ∈ winEv (univ : Set Unit) (fun _ => c x) (fun _ => ρ x) (fun _ => T x) V a ↔
        x ∈ winEv E c ρ T V a := by
      simp only [winEv, mem_ofPred_eq, mem_univ, hx, true_and, hpath]
    rw [hm]
  have hland := hasAccessLanding_glued_subwindow hsingle hs0
    (fun _ _ => hβ) (fun _ _ => hη) (fun _ _ => hηH) (fun _ _ => hb) (fun _ _ => hdom)
    (fun _ _ => hT) hUb hVU (fun _ _ => hseed)
  intro hpos heq hfin
  obtain ⟨L, hLV, hlim⟩ := hland () (mem_univ ()) hpos (htime.trans heq) hfin
  exact ⟨L, hLV, by rw [hpath] at hlim; exact hlim⟩

end InteractingSLE.Sec5.Aux61SlitW
