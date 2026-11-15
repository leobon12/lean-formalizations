/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1RestartLawEntrance
import InteractingSLE.Foundations.Topology.PathComplement

/-!
# Terminal chart values belong to the retained boundary

The boundary extension is taken from the existing regular-piece chart theory.
The range condition is preserved by recentring and by finite Loewner steps.
This supplies the terminal reader needed for capped entrance histories.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Theorem14.GW1RestartFinal

/-- Boundary limits of a conformal inverse at finite real chart points lie on
the frontier of its domain. -/
theorem boundary_limit_mem_frontier {c : Chart} (hc : c.IsConformal)
    {p q : ℂ} (hp : p ∈ Hbar) (hpH : p ∉ H)
    (hq : Tendsto c.2.1 (𝓝[H] p) (𝓝 q)) : q ∈ frontier (c.dom : Set ℂ) := by
  have := GW1P.neBot_nhdsWithin_H hp
  have hcl : q ∈ closure (c.dom : Set ℂ) :=
    mem_closure_of_tendsto hq (eventually_nhdsWithin_of_forall fun z hz => hc.inv_mem_dom hz)
  rw [c.dom.isOpen.frontier_eq]
  refine ⟨hcl, ?_⟩
  intro hqd
  have hf : Tendsto c.1 (𝓝 q) (𝓝 (c.1 q)) :=
    (hc.differentiableOn_fwd.continuousOn.continuousAt (c.dom.isOpen.mem_nhds hqd)).tendsto
  have he : Tendsto (fun z => c.1 (c.2.1 z)) (𝓝[H] p) (𝓝 p) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id |>.congr'
      (eventually_nhdsWithin_of_forall fun z hz => (hc.2.2 z hz).symm)
  have hpq : p = c.1 q := tendsto_nhds_unique he (hf.comp hq)
  exact hpH (hpq ▸ hc.fwd_mem hqd)

/-- An inverse chart has boundary values only on the retained physical range
or outside the upper half-plane. The limit map is not required to be Borel off
the closed half-plane; a Borel reader is constructed below. -/
def HasBoundaryRange (c : Chart) (A : Set ℂ) : Prop :=
  ∃ f : ℂ → ℂ, (∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p))) ∧
    ∀ p ∈ Hbar, p ∉ H → f p ∈ A ∨ f p ∉ H

theorem HasBoundaryRange.mono {c : Chart} {A B : Set ℂ}
    (h : HasBoundaryRange c A) (hAB : A ⊆ B) : HasBoundaryRange c B := by
  obtain ⟨f, hf, hr⟩ := h
  exact ⟨f, hf, fun p hp hpH => (hr p hp hpH).imp (fun hA => hAB hA) id⟩

/-- The initial translation has real boundary values. -/
theorem hasBoundaryRange_recenter_id (x : ℝ) (A : Set ℂ) :
    HasBoundaryRange (Chart.id.recenter x) A := by
  refine ⟨fun z => z + (x : ℂ), ?_, ?_⟩
  · intro p _
    rw [CounterflowRange.recenter_id_inv]
    exact ((continuous_id.add continuous_const).tendsto p).mono_left nhdsWithin_le_nhds
  · intro p _ hpH
    right
    change ¬ 0 < p.im at hpH
    change ¬ 0 < (p + (x : ℂ)).im
    simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using hpH

/-- A literal real recentring preserves the retained boundary range. -/
theorem HasBoundaryRange.recenter {c : Chart} {A : Set ℂ}
    (h : HasBoundaryRange c A) (x : ℝ) : HasBoundaryRange (c.recenter x) A := by
  obtain ⟨f, hf, hr⟩ := h
  have hH : ∀ z : ℂ, z + (x : ℂ) ∈ H ↔ z ∈ H := by
    intro z
    change 0 < (z + (x : ℂ)).im ↔ 0 < z.im
    simp only [Complex.add_im, Complex.ofReal_im, add_zero]
  have hHb : ∀ z ∈ Hbar, z + (x : ℂ) ∈ Hbar := by
    intro z hz
    change 0 ≤ z.im at hz
    change 0 ≤ (z + (x : ℂ)).im
    simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using hz
  refine ⟨fun z => f (z + (x : ℂ)), ?_, ?_⟩
  · intro p hp
    exact (hf _ (hHb p hp)).comp (tendsto_nhdsWithin_iff.2
      ⟨((continuous_id.add continuous_const).tendsto p).mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall fun z hz => (hH z).2 hz⟩)
  · intro p hp hpH
    exact hr _ (hHb p hp) (fun hz => hpH ((hH p).1 hz))

/-- The range invariant gives a Borel reader on the entire plane, with the
same actual boundary limits. -/
theorem HasBoundaryRange.exists_terminalChartReader {c : Chart} {A : Set ℂ}
    (h : HasBoundaryRange c A) (hc : c.IsConformal) :
    ∃ read : ℂ → ℂ, GW1RestartLaw.IsTerminalChartReader c A read ∧
      ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (read p)) := by
  classical
  obtain ⟨f, hf, hr⟩ := h
  let read := Hbar.piecewise f (fun _ => 0)
  have he : ∀ p ∈ Hbar, read p = f p := fun p hp => Set.piecewise_eq_of_mem _ _ _ hp
  have hm : Measurable read :=
    (GW1P.continuousOn_of_tendsto hf).measurable_piecewise continuousOn_const
      QuantumZipper.isClosed_Hbar.measurableSet
  refine ⟨read, ⟨hm, ?_, ?_⟩, fun p hp => (he p hp).symm ▸ hf p hp⟩
  · intro p hp
    have hp' : p ∈ Hbar := (show 0 < p.im from hp).le
    rw [he p hp']
    have := GW1P.neBot_nhdsWithin_H hp'
    exact tendsto_nhds_unique (hf p hp') (hc.1.continuousOn p hp)
  · intro p hp hpH
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar] at hp
    rw [he p hp]
    exact hr p hp hpH

end InteractingSLE.Theorem14.GW1RestartFinal
