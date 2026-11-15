/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6SourceCStops

/-!
# The source GB6 hypotheses provide measurable relative drivers

Only the flow-line drivers' adaptation and path regularity and the assumed
generating traces enter this construction. The remaining named input is
causal physical read-back for the specific constructed coordinates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.GB6.SourceC

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {κcf κ θcf θ : ℝ} {b b' : ℝ → ℝ} {J J' : Finset ℝ}
  {h h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
  {W Wα : ℝ≥0 → Ω → ℝ} {ζ ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}

/-- Full measurable relative-driver coordinates from exactly the relevant
flow-line and generating-trace hypotheses of GB6. -/
theorem exists_relative_driver_of_flowlines
    (hcf : IsFlowLineDriver κcf b' J' θcf P h' W ζ)
    (hflow : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hγ : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω))
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω)) (s : ℝ≥0) (hs : 0 < s) :
    ∃ (D : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ≥0∞), RelativeDriverCoordinates s P W Wα ζα γ α D L := by
  have hcfreg := ae_driver_zero_continuousOn hcf
  have hflowreg := ae_driver_zero_continuousOn hflow
  have hc : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ W 0 ω = 0 ∧ Continuous (W · ω) ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω) := by
    filter_upwards [hcfreg, hγ] with ω hr ht
    refine ⟨ht.1, hr.1, continuousOn_univ.1 (hr.2.mono fun t _ => ?_), ht.2⟩
    rw [mem_ofPred_eq, ht.1]
    exact ENNReal.coe_lt_top
  have hf : ∀ᵐ ω ∂P, Wα 0 ω = 0 ∧ ContinuousOn (Wα · ω) {t | (t : ℝ≥0∞) < ζα ω} ∧
      IsGeneratingTrace (Wα · ω) (ζα ω) (α ω) := by
    filter_upwards [hflowreg, hα] with ω hr ht
    exact ⟨hr.1, hr.2, ht⟩
  obtain ⟨_, 𝓕, _, _, _, _, hC⟩ := hcf
  obtain ⟨_, 𝓕α, _, _, _, _, hA⟩ := hflow
  exact exists_relative_driver hC.1.2.1 hA.1.2.1 hc hf s hs

section Chosen

variable (hcf : IsFlowLineDriver κcf b' J' θcf P h' W ζ)
    (hflow : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hγ : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω))
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω)) (s : ℝ≥0) (hs : 0 < s)

/-- Fix the measurable driver supplied by the source construction. -/
def sourceDriver : ℝ≥0 → Ω → ℝ :=
  (exists_relative_driver_of_flowlines hcf hflow hγ hα s hs).choose

/-- Fix its full relative lifetime, with the zero-driver/top-life default
off the common measurable source event. -/
def sourceLife : Ω → ℝ≥0∞ :=
  (exists_relative_driver_of_flowlines hcf hflow hγ hα s hs).choose_spec.choose

theorem sourceCoordinates_spec : RelativeDriverCoordinates s P W Wα ζα γ α
    (sourceDriver hcf hflow hγ hα s hs) (sourceLife hcf hflow hγ hα s hs) :=
  (exists_relative_driver_of_flowlines hcf hflow hγ hα s hs).choose_spec.choose_spec

/-- The exact remaining hypothesis: almost-sure causal physical read-back
for the specific fully constructed relative coordinates. -/
def HasSourceReadout : Prop := ∃ (g : ℝ≥0 → Ω → ℝ) (G : RelDrv.Version.GaugeReadout),
  AESeparationReadout P (gb6Rec s Wα ζα)
    (sourceDriver hcf hflow hγ hα s hs) (sourceLife hcf hflow hγ hα s hs) g G

/-- All source technical measurability is discharged. A causal physical
read-back for the constructed coordinates gives the stopped versions. -/
theorem exists_versions_of_sourceReadout (hread : HasSourceReadout hcf hflow hγ hα s hs) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ m, RelDrv.IsGB6RelVersion s P W Wα ζα γ α (R m) (V m)) ∧
      ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < RelDrv.gb6Tc s γ α ω →
          ∃ m, ENNReal.ofReal (RelDrv.gb6Clock s W Wα ω t) < V m ω := by
  obtain ⟨g, G, hg⟩ := hread
  have hC := sourceCoordinates_spec hcf hflow hγ hα s hs
  exact exists_versions_of_ae_readout hC hg

end Chosen

end InteractingSLE.Supp8.GB6.SourceC
