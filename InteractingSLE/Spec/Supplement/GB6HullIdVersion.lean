/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6HullIdRule
import InteractingSLE.Spec.Supplement.GB6SourceCReadout

/-!
# GB6: relative versions whose stops are path rules

Packet PROVE-GB6-HULLID. `IsGB6RelVersion` (PROVE-GB6-RELDRV) asks only that `{V ≤ t}` be, for each `t` separately and
almost surely, an event of the record and the path on `[0, t]`. The corrected Aux. 54 (R79) needs more: the stop must
be a Galmarino rule of the killed history. This file records the stronger form that GB6-VERSION's gauge stops actually
have and proves it from the same input:

* `IsGB6RelVersionR`: a GB6 version whose stop is almost surely `ρ (record, path)` for a measurable path rule `ρ`
  (`IsPathRule`);
* `GB6RelVersionRStatement`: `GB6RelVersionStatement` with `IsGB6RelVersionR`;
* `isGB6RelVersionR_coord` / `exists_versionsR_of_ae_readout`: GB6-VERSION's gauge-stop versions
  (`coordDriver`, `coordStop`) are R-form versions, with the rule `hitRule` of the countable prefix test;
* **`gb6RelVersionRStatement_of_sourceReadout`**: `GB6SourceReadoutStatement → GB6RelVersionRStatement` (the same and
  only remaining input as `SourceC.gb6RelVersionStatement_of_sourceReadout`).

The proof of `isGB6RelVersionR_coord`'s first conjunct follows `SourceC.exists_versions_of_ae_readout`
(PROVE-GB6-VERSION), whose stopped-version clauses are not exported separately. Nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Supp8.GB6.HullId

open RelDrv RelDrv.Version Exist.StagedLaw SourceC

/-- **A GB6 relative version stopped by a path rule**: `IsGB6RelVersion`, and almost surely the stop is a measurable
path rule of the record of the flow prefix and of the relative driver. -/
def IsGB6RelVersionR (s : ℝ≥0) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W Wα : ℝ≥0 → Ω → ℝ)
    (ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) : Prop :=
  IsGB6RelVersion s P W Wα ζα γ α R V ∧
    ∃ ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞, Measurable ρ ∧ IsPathRule ρ ∧
      ∀ᵐ ω ∂P, V ω = ρ (gb6Rec s Wα ζα ω, fun u => R u ω)

/-- **Exhausting relative versions stopped by path rules** (binders of `GB6RelVersionStatement`). -/
def GB6RelVersionRStatement : Prop :=
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
    ∀ s : ℝ≥0, ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ m, IsGB6RelVersionR s P W Wα ζα γ α (R m) (V m)) ∧
      ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H → ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω →
        ∃ m, ENNReal.ofReal (gb6Clock s W Wα ω t) < V m ω

/-- An R-form version is a version. -/
theorem IsGB6RelVersionR.isGB6RelVersion {s : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hv : IsGB6RelVersionR s P W Wα ζα γ α R V) : IsGB6RelVersion s P W Wα ζα γ α R V := hv.1

/-- The R-form statement implies the original version statement. -/
theorem gb6RelVersionStatement_of_R (hV : GB6RelVersionRStatement.{u}) : GB6RelVersionStatement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf hcomp hfl hα s
  obtain ⟨R, V, hv, hexh⟩ := hV κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf hcomp hfl
    hα s
  exact ⟨R, V, fun m => (hv m).1, hexh⟩

section Coord

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {s : ℝ≥0}
  {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
  {D : ℝ≥0 → Ω → ℝ} {L : Ω → ℝ≥0∞} {g : ℝ≥0 → Ω → ℝ} {G : GaugeReadout}

/-- The gauge level read from the record at the zero path. -/
def recLevel (G : GaugeReadout) (m : ℕ) (r : RecData) : ℝ := gaugeLevel (G 0 (r, fun _ => 0)) m

theorem measurable_recLevel (hG : ∀ t, Measurable (G t)) (m : ℕ) : Measurable (recLevel G m) :=
  (((hG 0).comp (measurable_id.prodMk measurable_const)).div_const 2).min measurable_const

/-- **GB6-VERSION's gauge-stop versions are stopped by the prefix-test path rule.** -/
theorem isGB6RelVersionR_coord (hC : RelativeDriverCoordinates s P W Wα ζα γ α D L)
    (hread : AESeparationReadout P (gb6Rec s Wα ζα) D L g G) (m : ℕ) :
    IsGB6RelVersionR s P W Wα ζα γ α (coordDriver (D := D) (g := g) m)
      (fun ω => (coordStop (g := g) m ω : ℝ≥0∞)) := by
  have hv : ∀ ω, (coordStop (g := g) m ω : ℝ≥0∞) < L ω :=
    fun ω => localStop_lt (hread.continuous ω) (hread.zero_pos ω) (hread.terminal ω) m
  have hvm : Measurable (coordStop (g := g) m) :=
    measurable_gaugeStop hread.measurable hread.continuous
      (((hread.measurable 0).div_const 2).min
        (measurable_const : Measurable fun _ : Ω => 1 / ((m : ℝ) + 1))) (m + 1)
  have hε : Measurable (recLevel G m) := measurable_recLevel hread.readout_measurable m
  -- on the read-back event, the readout of the frozen driver is the gauge through the stop
  have hrd : ∀ᵐ ω ∂P, recLevel G m (gb6Rec s Wα ζα ω) = gaugeLevel (g 0 ω) m ∧
      ∀ u ≤ gaugeStop (g · ω) (recLevel G m (gb6Rec s Wα ζα ω)) (m + 1),
        G u (gb6Rec s Wα ζα ω, fun u => coordDriver (D := D) (g := g) m u ω) = g u ω := by
    filter_upwards [hread.readout] with ω hω
    have hεω : recLevel G m (gb6Rec s Wα ζα ω) = gaugeLevel (g 0 ω) m := by
      change gaugeLevel (G 0 (gb6Rec s Wα ζα ω, fun _ => 0)) m = _
      rw [hω.1]
    refine ⟨hεω, fun u hu => ?_⟩
    rw [hεω] at hu
    have hu' : u ≤ coordStop (g := g) m ω := hu
    calc
      _ = G u (gb6Rec s Wα ζα ω, fun u => D u ω) := hread.causal u _ _ _ fun v hv' =>
        freeze_eq (hv'.trans hu')
      _ = g u ω := hω.2 u ((ENNReal.coe_le_coe.2 hu').trans_lt (hv ω))
  refine ⟨⟨fun t => measurable_freeze hC.adapted hC.continuous hvm hv t,
    continuous_freeze hC.continuous hv, ?_, ?_, measurable_coe_nnreal_ennreal.comp hvm, ?_, ?_⟩,
    hitRule G (recLevel G m) (m + 1), measurable_hitRule hread.readout_measurable hε,
    isPathRule_hitRule hread.causal, ?_⟩
  · intro ω
    simpa only [coordDriver, freeze, zero_min] using hC.zero ω
  · intro ω t ht
    exact freeze_after (ENNReal.coe_le_coe.1 ht)
  · intro t
    refine ⟨prefixHitSet G (recLevel G m) (m + 1) t, measurableSet_prefixHitSet hread.readout_measurable hε _ _,
      isDetUpTo_prefixHitSet hread.causal _ _ _, ?_⟩
    filter_upwards [hrd] with ω hω
    have htst := mem_prefixHitSet_iff (hread.continuous ω) (by positivity : (0 : ℝ≥0) < m + 1)
      (show recLevel G m (gb6Rec s Wα ζα ω) < g 0 ω by rw [hω.1]; exact gaugeLevel_lt (hread.zero_pos ω) m)
      hω.2 t
    rw [hω.1] at htst
    exact ENNReal.coe_le_coe.trans htst.symm
  · filter_upwards [hC.relative] with ω hrel hs hαs
    obtain ⟨hcover, hK⟩ := hrel hs hαs
    refine ⟨ENNReal.coe_pos.2 (localStop_pos (hread.continuous ω) (hread.zero_pos ω) m),
      fun u hu => hcover u (hu.trans (hv ω)), fun t ht hav => ?_⟩
    obtain ⟨ha0, -, hKt⟩ := hK t ht
    exact (fwdHull_freeze_eq (hC.continuous ω) (hv ω) ha0 (ENNReal.ofReal_le_coe.1 hav)).trans hKt
  · filter_upwards [hrd] with ω hω
    rw [hitRule_eq_gaugeStop (hread.continuous ω) (by positivity : (0 : ℝ≥0) < m + 1)
      (show recLevel G m (gb6Rec s Wα ζα ω) < g 0 ω by rw [hω.1]; exact gaugeLevel_lt (hread.zero_pos ω) m)
      hω.2, hω.1]
    rfl

/-- **Exhausting R-form versions from source coordinates and almost-sure causal read-back.** -/
theorem exists_versionsR_of_ae_readout (hC : RelativeDriverCoordinates s P W Wα ζα γ α D L)
    (hread : AESeparationReadout P (gb6Rec s Wα ζα) D L g G) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ m, IsGB6RelVersionR s P W Wα ζα γ α (R m) (V m)) ∧
      ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω →
          ∃ m, ENNReal.ofReal (gb6Clock s W Wα ω t) < V m ω := by
  refine ⟨coordDriver (D := D) (g := g), fun m ω => (coordStop (g := g) m ω : ℝ≥0∞),
    isGB6RelVersionR_coord hC hread, ?_⟩
  filter_upwards [hC.relative] with ω hrel hs hαs t ht
  obtain ⟨-, haL, -⟩ := (hrel hs hαs).2 t ht
  obtain ⟨m, hm⟩ := exists_lt_localStop (hread.continuous ω)
    (t := (gb6Clock s W Wα ω t).toNNReal) fun u hu =>
      hread.positive ω u ((ENNReal.coe_le_coe.2 hu).trans_lt haL)
  exact ⟨m, ENNReal.coe_lt_coe.2 hm⟩

/-- At a zero flow prefix the interior-tip event is null: the zero driver with the constant stop `1` is an R-form
version (constant rule). -/
theorem exists_versionsR_at_zero (hα0 : ∀ᵐ ω ∂P, α ω 0 = 0) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ m, IsGB6RelVersionR 0 P W Wα ζα γ α (R m) (V m)) ∧
      ∀ᵐ ω ∂P, ((0 : ℝ≥0) : ℝ≥0∞) < ζα ω → α ω 0 ∈ H →
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc 0 γ α ω →
          ∃ m, ENNReal.ofReal (gb6Clock 0 W Wα ω t) < V m ω := by
  have hnull : ∀ᵐ ω ∂P, α ω 0 ∉ H := by
    filter_upwards [hα0] with ω hω hH
    rw [hω] at hH
    exact (lt_irrefl (0 : ℝ)) hH
  refine ⟨fun _ _ _ => 0, fun _ _ => 1, fun m => ⟨⟨fun _ => measurable_const, fun _ => continuous_const,
    fun _ => rfl, fun _ _ _ => rfl, measurable_const, fun t => ⟨{_p | (1 : ℝ≥0∞) ≤ t}, MeasurableSet.const _,
      fun _ _ _ _ => Iff.rfl, ae_of_all _ fun _ => Iff.rfl⟩, ?_⟩,
    fun _ => 1, measurable_const, fun _ _ _ _ => rfl, ae_of_all _ fun _ => rfl⟩, ?_⟩
  · filter_upwards [hnull] with ω hω _ hH
    exact (hω hH).elim
  · filter_upwards [hnull] with ω hω _ hH
    exact (hω hH).elim

end Coord

/-- **R-form versions from the remaining read-back input** (`SourceC.GB6SourceReadoutStatement`, the same input as
`SourceC.gb6RelVersionStatement_of_sourceReadout`). -/
theorem gb6RelVersionRStatement_of_sourceReadout (hread : GB6SourceReadoutStatement.{u}) :
    GB6RelVersionRStatement.{u} := by
  intro κ θ hκ hκ4 hθl hθr Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h'
    hb hG hb' hchart hcf hγ hflow hα s
  by_cases hs : s = 0
  · subst s
    exact exists_versionsR_at_zero (hα.mono fun _ hω => hω.1)
  · have hsp : 0 < s := lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ s) (Ne.symm hs)
    have hγ' : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω) := hγ.mono fun _ hω => ⟨hω.1, hω.2.1⟩
    obtain ⟨g, G, hg⟩ := hread κ θ hκ hκ4 hθl hθr Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h'
      hb hG hb' hchart hcf hγ hflow hα s hsp
    exact exists_versionsR_of_ae_readout (sourceCoordinates_spec hcf hflow hγ' hα s hsp) hg

end InteractingSLE.Supp8.GB6.HullId
