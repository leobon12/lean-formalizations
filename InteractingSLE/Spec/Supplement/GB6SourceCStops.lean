/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6SourceCDriver

/-!
# Stopped versions from almost-sure causal read-back

The prefix stopping rule is an almost-sure identity. Its read-back premise
therefore need not constrain arbitrary null-set defaults of the source
coordinates. All driver and gauge path regularity remains all-sample.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.GB6.SourceC

open RelDrv RelDrv.Version Exist.StagedLaw

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Causal read-back is needed only on a common co-null source event.
The driver and gauge still satisfy all-sample path regularity. -/
structure AESeparationReadout (P : Measure Ω) (rec : Ω → RecData) (D : ℝ≥0 → Ω → ℝ)
    (L : Ω → ℝ≥0∞) (g : ℝ≥0 → Ω → ℝ) (G : GaugeReadout) : Prop where
  measurable : ∀ t, Measurable (g t)
  continuous : ∀ ω, Continuous (g · ω)
  zero_pos : ∀ ω, 0 < g 0 ω
  positive : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < L ω → 0 < g t ω
  terminal : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) = L ω → g t ω = 0
  readout_measurable : ∀ t, Measurable (G t)
  causal : IsCausal G
  readout : ∀ᵐ ω ∂P, G 0 (rec ω, fun _ => 0) = g 0 ω ∧
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → G t (rec ω, fun u => D u ω) = g t ω

/-- The original stopped-version predicate follows from source coordinates
and almost-sure causal read-back. No all-sample read-back is assumed. -/
theorem exists_versions_of_ae_readout {P : Measure Ω} {s : ℝ≥0}
    {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    {D : ℝ≥0 → Ω → ℝ} {L : Ω → ℝ≥0∞} {g : ℝ≥0 → Ω → ℝ} {G : GaugeReadout}
    (hC : RelativeDriverCoordinates s P W Wα ζα γ α D L)
    (hread : AESeparationReadout P (gb6Rec s Wα ζα) D L g G) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ m, IsGB6RelVersion s P W Wα ζα γ α (R m) (V m)) ∧
      ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω →
          ∃ m, ENNReal.ofReal (gb6Clock s W Wα ω t) < V m ω := by
  have hv : ∀ m ω, (coordStop (g := g) m ω : ℝ≥0∞) < L ω :=
    fun m ω => localStop_lt (hread.continuous ω) (hread.zero_pos ω) (hread.terminal ω) m
  have hvm : ∀ m, Measurable (coordStop (g := g) m) := fun m =>
    measurable_gaugeStop hread.measurable hread.continuous
      (((hread.measurable 0).div_const 2).min
        (measurable_const : Measurable fun _ : Ω => 1 / ((m : ℝ) + 1))) (m + 1)
  have hR : ∀ m, IsGB6RelVersion s P W Wα ζα γ α (coordDriver (D := D) (g := g) m)
      (fun ω => (coordStop (g := g) m ω : ℝ≥0∞)) := by
    intro m
    refine ⟨fun t => measurable_freeze hC.adapted hC.continuous (hvm m) (hv m) t,
      continuous_freeze hC.continuous (hv m), ?_, ?_, measurable_coe_nnreal_ennreal.comp (hvm m), ?_, ?_⟩
    · intro ω
      simpa only [coordDriver, freeze, zero_min] using hC.zero ω
    · intro ω t ht
      exact freeze_after (ENNReal.coe_le_coe.1 ht)
    · intro t
      let ε : RecData → ℝ := fun r => gaugeLevel (G 0 (r, fun _ => 0)) m
      have hε : Measurable ε :=
        (((hread.readout_measurable 0).comp (measurable_id.prodMk measurable_const)).div_const 2).min measurable_const
      refine ⟨prefixHitSet G ε (m + 1) t, measurableSet_prefixHitSet hread.readout_measurable hε _ _,
        isDetUpTo_prefixHitSet hread.causal _ _ _, ?_⟩
      filter_upwards [hread.readout] with ω hω
      have hεω : ε (gb6Rec s Wα ζα ω) = gaugeLevel (g 0 ω) m := by
        change gaugeLevel (G 0 (gb6Rec s Wα ζα ω, fun _ => 0)) m = _
        rw [hω.1]
      have hrd : ∀ u ≤ gaugeStop (g · ω) (ε (gb6Rec s Wα ζα ω)) (m + 1),
          G u (gb6Rec s Wα ζα ω, fun u => coordDriver (D := D) (g := g) m u ω) = g u ω := by
        intro u hu
        rw [hεω] at hu
        have hu' : u ≤ coordStop (g := g) m ω := hu
        calc
          _ = G u (gb6Rec s Wα ζα ω, fun u => D u ω) := hread.causal u _ _ _ fun v hv' =>
            freeze_eq (hv'.trans hu')
          _ = g u ω := hω.2 u ((ENNReal.coe_le_coe.2 hu').trans_lt (hv m ω))
      have htst := mem_prefixHitSet_iff (hread.continuous ω) (by positivity : (0 : ℝ≥0) < m + 1)
        (show ε (gb6Rec s Wα ζα ω) < g 0 ω by rw [hεω]; exact gaugeLevel_lt (hread.zero_pos ω) m) hrd t
      rw [hεω] at htst
      exact ENNReal.coe_le_coe.trans htst.symm
    · filter_upwards [hC.relative] with ω hrel hs hαs
      obtain ⟨hcover, hK⟩ := hrel hs hαs
      refine ⟨ENNReal.coe_pos.2 (localStop_pos (hread.continuous ω) (hread.zero_pos ω) m),
        fun u hu => hcover u (hu.trans (hv m ω)), fun t ht hav => ?_⟩
      obtain ⟨ha0, -, hKt⟩ := hK t ht
      exact (fwdHull_freeze_eq (hC.continuous ω) (hv m ω) ha0 (ENNReal.ofReal_le_coe.1 hav)).trans hKt
  refine ⟨coordDriver (D := D) (g := g), fun m ω => (coordStop (g := g) m ω : ℝ≥0∞), hR, ?_⟩
  filter_upwards [hC.relative] with ω hrel hs hαs t ht
  obtain ⟨-, haL, -⟩ := (hrel hs hαs).2 t ht
  obtain ⟨m, hm⟩ := exists_lt_localStop (hread.continuous ω)
    (t := (gb6Clock s W Wα ω t).toNNReal) fun u hu =>
      hread.positive ω u ((ENNReal.coe_le_coe.2 hu).trans_lt haL)
  exact ⟨m, ENNReal.coe_lt_coe.2 hm⟩

end InteractingSLE.Supp8.GB6.SourceC
