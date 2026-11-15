/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6CoordBAtlas

/-!
# The remaining causal physical separation input

Boundary extension and measurable local-driver gluing are proved in the
`GB6CoordB` modules. The proposition here isolates physical separation read
back from the record and the relative driver, including real visits. It is a
named hypothesis, not an assertion that such a readout has been constructed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.GB6.CoordB

open RelDrv RelDrv.Version Exist.StagedLaw

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The exact remaining physical read-back input. A positive continuous
separation gauge must be recoverable causally from the initial record and
the relative driver, and must vanish at any finite terminal relative time. -/
structure CausalSeparationReadout (rec : Ω → RecData) (D : ℝ≥0 → Ω → ℝ)
    (L : Ω → ℝ≥0∞) (g : ℝ≥0 → Ω → ℝ) (G : GaugeReadout) : Prop where
  measurable : ∀ t, Measurable (g t)
  continuous : ∀ ω, Continuous (g · ω)
  zero_pos : ∀ ω, 0 < g 0 ω
  positive : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < L ω → 0 < g t ω
  terminal : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) = L ω → g t ω = 0
  readout_measurable : ∀ t, Measurable (G t)
  causal : IsCausal G
  readout_zero : ∀ ω, G 0 (rec ω, fun _ => 0) = g 0 ω
  readout : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < L ω →
    G t (rec ω, fun u => D u ω) = g t ω

/-- Conditional assembly with the driver facts separated from the genuinely
missing causal physical read-back. The target version predicate is unchanged. -/
theorem exists_versions_of_relative_driver_and_readout {P : Measure Ω} {s : ℝ≥0}
    {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    {D : ℝ≥0 → Ω → ℝ} {L : Ω → ℝ≥0∞} {g : ℝ≥0 → Ω → ℝ} {G : GaugeReadout}
    (hDa : AdaptedBefore (Filtration.const ℝ≥0 mΩ le_rfl) L D)
    (hDc : ∀ ω, ContinuousOn (D · ω) {u | (u : ℝ≥0∞) < L ω})
    (hD0 : ∀ ω, D 0 ω = 0)
    (hread : CausalSeparationReadout (gb6Rec s Wα ζα) D L g G)
    (hrel : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      (∀ u : ℝ≥0, (u : ℝ≥0∞) < L ω → ∃ t : ℝ≥0,
        (t : ℝ≥0∞) < gb6Tc s γ α ω ∧ (u : ℝ) < gb6Clock s W Wα ω t) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω →
        0 ≤ gb6Clock s W Wα ω t ∧ ENNReal.ofReal (gb6Clock s W Wα ω t) < L ω ∧
        QuantumZipper.fwdHull (fun r : ℝ => D r.toNNReal ω) (gb6Clock s W Wα ω t) =
          relMap (fun r : ℝ => Wα r.toNNReal ω) s ''
            QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) t) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ m, IsGB6RelVersion s P W Wα ζα γ α (R m) (V m)) ∧
      ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω →
          ∃ m, ENNReal.ofReal (gb6Clock s W Wα ω t) < V m ω := by
  exact exists_versions_of_coordinates
    (⟨hDa, hDc, hD0, hread.measurable, hread.continuous, hread.zero_pos, hread.positive,
      hread.terminal, hread.readout_measurable, hread.causal, hread.readout_zero,
      hread.readout, hrel⟩ : RelativeGaugeCoordinates s P W Wα ζα γ α D L g G)

end InteractingSLE.Supp8.GB6.CoordB
