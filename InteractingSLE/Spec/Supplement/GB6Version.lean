/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6VersionFreeze

/-!
# GB6 versions from measurable relative coordinates

This file constructs the whole family of versions, including their stopping
rules and exhaustion, from a local relative driver and a causal physical
separation gauge. `RelativeGaugeCoordinates` records the precise coordinate
facts needed for this construction; it does not assert their existence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Supp8.GB6.RelDrv.Version

open Exist.StagedLaw

/-- Measurable local relative coordinates and a physical separation readout.
The driver is constrained only before `L`; the gauge is a continuous positive
function there, vanishes at a finite endpoint, and can be read causally from
the record and relative driver. The last clause identifies the relative hulls
and the full relative clock interval on the interior-tip event. -/
structure RelativeGaugeCoordinates (s : ℝ≥0) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (W Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ)
    (D : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ≥0∞) (g : ℝ≥0 → Ω → ℝ) (G : GaugeReadout) : Prop where
  adapted : AdaptedBefore (Filtration.const ℝ≥0 mΩ le_rfl) L D
  continuous : ∀ ω, ContinuousOn (D · ω) {u | (u : ℝ≥0∞) < L ω}
  zero : ∀ ω, D 0 ω = 0
  gauge_measurable : ∀ t, Measurable (g t)
  gauge_continuous : ∀ ω, Continuous (g · ω)
  gauge_zero_pos : ∀ ω, 0 < g 0 ω
  gauge_positive : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < L ω → 0 < g t ω
  gauge_terminal : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) = L ω → g t ω = 0
  readout_measurable : ∀ t, Measurable (G t)
  readout_causal : IsCausal G
  readout_zero : ∀ ω, G 0 (gb6Rec s Wα ζα ω, fun _ => 0) = g 0 ω
  readout : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < L ω → G t (gb6Rec s Wα ζα ω, fun u => D u ω) = g t ω
  relative : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
    (∀ u : ℝ≥0, (u : ℝ≥0∞) < L ω → ∃ t : ℝ≥0,
      (t : ℝ≥0∞) < gb6Tc s γ α ω ∧ (u : ℝ) < gb6Clock s W Wα ω t) ∧
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω →
      0 ≤ gb6Clock s W Wα ω t ∧ ENNReal.ofReal (gb6Clock s W Wα ω t) < L ω ∧
      QuantumZipper.fwdHull (fun r : ℝ => D r.toNNReal ω) (gb6Clock s W Wα ω t) =
        relMap (fun r : ℝ => Wα r.toNNReal ω) s ''
          QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) t

section Construction

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {s : ℝ≥0}
  {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
  {D : ℝ≥0 → Ω → ℝ} {L : Ω → ℝ≥0∞} {g : ℝ≥0 → Ω → ℝ} {G : GaugeReadout}

variable (hC : RelativeGaugeCoordinates s P W Wα ζα γ α D L g G)

/-- The measurable positive-distance stop. -/
def coordStop (m : ℕ) (ω : Ω) : ℝ≥0 := localStop (g · ω) m

/-- The frozen measurable driver at a positive-distance stop. -/
def coordDriver (m : ℕ) : ℝ≥0 → Ω → ℝ := freeze D (coordStop (g := g) m)

include hC

theorem coordStop_lt (m : ℕ) (ω : Ω) : (coordStop (g := g) m ω : ℝ≥0∞) < L ω :=
  localStop_lt (hC.gauge_continuous ω) (hC.gauge_zero_pos ω) (hC.gauge_terminal ω) m

theorem measurable_coordStop (m : ℕ) : Measurable (coordStop (g := g) m) :=
  measurable_gaugeStop hC.gauge_measurable hC.gauge_continuous
    (((hC.gauge_measurable 0).div_const 2).min
      (measurable_const : Measurable fun _ : Ω => 1 / ((m : ℝ) + 1))) (m + 1)

theorem measurable_coordDriver (m : ℕ) (t : ℝ≥0) : Measurable (coordDriver (D := D) (g := g) m t) :=
  measurable_freeze hC.adapted hC.continuous ((measurable_coordStop hC) m) ((coordStop_lt hC) m) t

/-- The explicit prefix rule for `coordStop`, with the starting distance read
from the record at the zero path. -/
theorem coordStop_prefix_rule (m : ℕ) (t : ℝ≥0) :
    ∃ B : Set (RecData × (ℝ≥0 → ℝ)), MeasurableSet B ∧ IsDetUpTo t B ∧
      ∀ ω, ((coordStop (g := g) m ω : ℝ≥0∞) ≤ t ↔
        (gb6Rec s Wα ζα ω, fun u => coordDriver (D := D) (g := g) m u ω) ∈ B) := by
  let ε : RecData → ℝ := fun r => gaugeLevel (G 0 (r, fun _ => 0)) m
  have hε : Measurable ε :=
    (((hC.readout_measurable 0).comp (measurable_id.prodMk measurable_const)).div_const 2).min
      measurable_const
  refine ⟨prefixHitSet G ε (m + 1) t, measurableSet_prefixHitSet hC.readout_measurable hε _ _,
    isDetUpTo_prefixHitSet hC.readout_causal _ _ _, fun ω => ?_⟩
  have hεω : ε (gb6Rec s Wα ζα ω) = gaugeLevel (g 0 ω) m := by
    change gaugeLevel (G 0 (gb6Rec s Wα ζα ω, fun _ => 0)) m = gaugeLevel (g 0 ω) m
    rw [hC.readout_zero ω]
  have hread : ∀ u ≤ gaugeStop (g · ω) (ε (gb6Rec s Wα ζα ω)) (m + 1),
      G u (gb6Rec s Wα ζα ω, fun u => coordDriver (D := D) (g := g) m u ω) = g u ω := by
    intro u hu
    rw [hεω] at hu
    have hu' : u ≤ coordStop (g := g) m ω := hu
    calc
      _ = G u (gb6Rec s Wα ζα ω, fun u => D u ω) := hC.readout_causal u _ _ _ fun v hv =>
        freeze_eq (hv.trans hu')
      _ = g u ω := hC.readout ω u ((ENNReal.coe_le_coe.2 hu').trans_lt ((coordStop_lt hC) m ω))
  have htest := mem_prefixHitSet_iff (hC.gauge_continuous ω) (by positivity : (0 : ℝ≥0) < m + 1)
    (show ε (gb6Rec s Wα ζα ω) < g 0 ω by rw [hεω]; exact gaugeLevel_lt (hC.gauge_zero_pos ω) m)
    hread t
  rw [hεω] at htest
  exact (ENNReal.coe_le_coe.trans htest.symm)

/-- Measurable relative coordinates give all clauses of one stopped version. -/
theorem isGB6RelVersion_coordDriver (m : ℕ) :
    IsGB6RelVersion s P W Wα ζα γ α (coordDriver (D := D) (g := g) m)
      (fun ω => (coordStop (g := g) m ω : ℝ≥0∞)) := by
  refine ⟨(measurable_coordDriver hC) m,
    continuous_freeze hC.continuous ((coordStop_lt hC) m), ?_, ?_,
    measurable_coe_nnreal_ennreal.comp ((measurable_coordStop hC) m), ?_, ?_⟩
  · intro ω
    simpa only [coordDriver, freeze, zero_min] using hC.zero ω
  · intro ω t ht
    exact freeze_after (ENNReal.coe_le_coe.1 ht)
  · intro t
    obtain ⟨B, hBm, hBt, hB⟩ := (coordStop_prefix_rule hC) m t
    exact ⟨B, hBm, hBt, ae_of_all _ hB⟩
  · filter_upwards [hC.relative] with ω hrel hs hαs
    obtain ⟨hcover, hK⟩ := hrel hs hαs
    refine ⟨ENNReal.coe_pos.2 (localStop_pos (hC.gauge_continuous ω) (hC.gauge_zero_pos ω) m),
      fun u hu => hcover u (hu.trans ((coordStop_lt hC) m ω)), fun t ht hav => ?_⟩
    obtain ⟨ha0, -, hKt⟩ := hK t ht
    have hav' : gb6Clock s W Wα ω t ≤ coordStop (g := g) m ω :=
      (ENNReal.ofReal_le_coe).1 hav
    exact (fwdHull_freeze_eq (hC.continuous ω) ((coordStop_lt hC) m ω) ha0 hav').trans hKt

/-- The whole family exhausts every relative clock value before contact. -/
theorem coordStop_exhausts : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω →
      ∃ m, ENNReal.ofReal (gb6Clock s W Wα ω t) < (coordStop (g := g) m ω : ℝ≥0∞) := by
  filter_upwards [hC.relative] with ω hrel hs hαs t ht
  obtain ⟨-, haL, -⟩ := (hrel hs hαs).2 t ht
  have hnn : ((gb6Clock s W Wα ω t).toNNReal : ℝ≥0∞) < L ω := haL
  obtain ⟨m, hm⟩ := exists_lt_localStop (hC.gauge_continuous ω)
    (t := (gb6Clock s W Wα ω t).toNNReal) fun u hu =>
      hC.gauge_positive ω u ((ENNReal.coe_le_coe.2 hu).trans_lt hnn)
  exact ⟨m, ENNReal.coe_lt_coe.2 hm⟩

/-- Construction of exhausting versions from the concrete coordinate facts. -/
theorem exists_versions_of_coordinates :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ m, IsGB6RelVersion s P W Wα ζα γ α (R m) (V m)) ∧
      ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω →
          ∃ m, ENNReal.ofReal (gb6Clock s W Wα ω t) < V m ω :=
  ⟨coordDriver (D := D) (g := g), fun m ω => (coordStop (g := g) m ω : ℝ≥0∞),
    (isGB6RelVersion_coordDriver hC), (coordStop_exhausts hC)⟩

end Construction

/-- **Remaining input, not proved here.** The GB6 setting admits a measurable
local relative driver and a causal physical separation readout, including at
real boundary visits. This contains no stopping-time or exhaustion premise;
those conclusions are proved by `exists_versions_of_coordinates`. -/
def GB6RelativeGaugeStatement : Prop :=
  ∀ (κ θ : ℝ), 0 < κ → κ < 4 → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζ ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ)
    (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsPiecewiseConstantBoundaryData b' J' →
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω)) →
    IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ →
    (∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop) →
    IsFlowLineDriver κ b J θ P h Wα ζα →
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) →
    ∀ s : ℝ≥0, ∃ (D : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ≥0∞)
      (g : ℝ≥0 → Ω → ℝ) (G : GaugeReadout),
      RelativeGaugeCoordinates s P W Wα ζα γ α D L g G

/-- Conditional reduction only: measurable relative coordinates and the
physical readout imply the original, unchanged version statement. -/
theorem gb6RelVersionStatement_of_relativeGauge
    (hcoordinates : GB6RelativeGaugeStatement.{u}) : GB6RelVersionStatement.{u} := by
  intro κ θ hκ hκ4 hθl hθr Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h'
    hb hG hb' hchart hcf hγ hflow hα s
  obtain ⟨D, L, g, G, hC⟩ := hcoordinates κ θ hκ hκ4 hθl hθr Ω mΩ P hP
    h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hchart hcf hγ hflow hα s
  exact exists_versions_of_coordinates hC

end InteractingSLE.Supp8.GB6.RelDrv.Version
