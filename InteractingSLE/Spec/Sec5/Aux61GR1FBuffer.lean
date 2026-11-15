/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GNextTarget
import InteractingSLE.Spec.Sec5.Aux61GContHistory

/-! # Physical boundedness of a restart window and escape at infinite contact

A compact chart buffer whose bounded inverse extension avoids the physical
point at infinity has bounded physical inverse image. A proper continuation
cannot remain in that image forever. These are deterministic stop facts;
they assert no past measurability for a future capture.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GR1F
open Aux61GInst Aux61FibData

/-- Avoiding the pole of the inverse Cayley map on a compact buffer gives
boundedness of the actual physical inverse image of the window. -/
theorem isBounded_inverse_window {c : Chart} (hc : c.IsConformal)
    {V B : Set ℂ} (hVB : V ⊆ B) (hBc : IsCompact (closure B))
    (hF : ContinuousOn (boundedInverse c) Hbar)
    (hfinite : ∀ z ∈ closure B ∩ Hbar, boundedInverse c z ≠ 1) :
    Bornology.IsBounded (c.2.1 '' (V ∩ H)) := by
  have hK : IsCompact (closure B ∩ Hbar) :=
    hBc.inter_right QuantumZipper.isClosed_Hbar
  have hFc : IsCompact (boundedInverse c '' (closure B ∩ Hbar)) :=
    hK.image_of_continuousOn (hF.mono inter_subset_right)
  have hcc : ContinuousOn cayleyInv (boundedInverse c '' (closure B ∩ Hbar)) :=
    QuantumZipper.CA.continuousOn_cayleyInv.mono (by
      rintro w ⟨z, hz, rfl⟩
      exact hfinite z hz)
  refine (hFc.image_of_continuousOn hcc).isBounded.subset ?_
  rintro w ⟨z, hz, rfl⟩
  refine ⟨boundedInverse c z, ⟨z, ⟨subset_closure (hVB hz.1),
    QuantumZipper.H_subset_Hbar hz.2⟩, rfl⟩, ?_⟩
  rw [Aux61GNext.boundedInverse_eqOn_of_conformal hc hz.2]
  exact QuantumZipper.CA.cayleyInv_cayley
    (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (show 0 < (c.2.1 z).im from hc.2.1 hz.2).le)

/-- At a positive time inside the chart domain, the limit-defined chart
path is the actual forward chart value. No restart-law assumption is used. -/
theorem inPath_eq_fwd_of_mem {X : Type*} {E : Set X} {c : X → Chart}
    {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {x : X} {u : ℝ≥0}
    (hx : x ∈ E) (hu : (u : ℝ≥0∞) < T x) (hc : (c x).IsConformal)
    (hmem : ρ x u ∈ (c x).dom) :
    inPath E c ρ T x u = (c x).1 (ρ x u) := by
  have : (𝓝[((c x).dom : Set ℂ)] (ρ x u)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hmem)
  simp only [inPath, hx, hu, and_self, ite_true]
  exact ((continuousAt_fwd hc hmem).tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq

/-- If contact never occurs, physical properness forces exit from any
window having bounded physical inverse image. -/
theorem exists_exit_of_contact_top {X : Type*} {E : Set X} {c : X → Chart}
    {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ} {x : X}
    (hx : x ∈ E) (hc : (c x).IsConformal) (hT : T x = ⊤)
    (hinside : ∀ u : ℝ≥0, 0 < u → ρ x u ∈ (c x).dom)
    (hproper : Tendsto (fun u : ℝ≥0 => ‖ρ x u‖) atTop atTop)
    (hbounded : Bornology.IsBounded ((c x).2.1 '' (V ∩ H))) :
    ∃ u : ℝ≥0, (u : ℝ≥0∞) < T x ∧ inPath E c ρ T x u ∉ V := by
  obtain ⟨R, hR⟩ := hbounded.exists_norm_le
  have hev := (hproper.eventually (eventually_gt_atTop R)).and (eventually_gt_atTop (0 : ℝ≥0))
  obtain ⟨u, huR, hu0⟩ := hev.exists
  have hu : (u : ℝ≥0∞) < T x := hT ▸ ENNReal.coe_lt_top
  refine ⟨u, hu, fun hV => ?_⟩
  rw [inPath_eq_fwd_of_mem hx hu hc (hinside u hu0)] at hV
  have hmem : ρ x u ∈ (c x).2.1 '' (V ∩ H) :=
    ⟨(c x).1 (ρ x u), ⟨hV, hc.fwd_mem (hinside u hu0)⟩,
      hc.inv_fwd (hinside u hu0)⟩
  exact (not_le_of_gt huR) (hR _ hmem)

end InteractingSLE.Sec5.Aux61GR1F
