/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdLife
import InteractingSLE.Spec.Supplement.GW2RdTop
import InteractingSLE.Spec.Supplement.SBTail2RetainWord
import InteractingSLE.Spec.Supplement.CounterflowSeedGerm

/-!
# GW2's relative determination, part 7: `GW2RdVersionStatement` from two one-curve facts

Packet PROVE-GW2-RELDET (handoff §4.1). GB6's versions (`GaugeE.gb6LiveReadoutStatement` →
`Q3Stop.gb6RelVersionAStatement_of_readoutCoord`) are rerun for GW2's explored curve, the EXTENDED flow
`(regW s Wα ζα, extTr s Wα ζα α)` (`GW2RdExt`), with the counterflow retained:

* relative coordinates: `SourceC.exists_relative_driver` (the extended flow is continuous with a generating trace on
  `[0, ∞)` almost surely at an admissible seed);
* GB6's live separation readout without `κ < 4` (`hasLiveReadout_nr`, the counterflow's no-return from
  `GW4Ident.CounterflowNoReturnStatement`), which needs the extended trace to be transient: on `{ζα < ∞}` it is
  (`tendsto_norm_trace_of_frozen`), on `{ζα = ∞}` this is `FlowTransientStatement` (proved from Theorem 1.3);
* the CAP at the flow's lifetime: the read-back physical trace's distance to a closed set `B` hit exactly at the
  lifetime (named input `FlowLifetimeHitStatement`), `capGauge`, `capLife_facts`; `exists_capReadout` and the capped
  announced versions `isGB6RelVersionA_capCoord` (`GW2RdCap`);
* the cap clause of `IsGW2RelVersion` and the exhaustion before `min(ζα, T_c)` (`exists_lt_clock_of_lt_capLife`,
  `lt_capLife`, `hull_clock_contact_of_ext`).

Statements about ONE flow line of a GFF (`0 < κ < 4`, angle in `[−π/2, π/2]`):

* **`FlowLifetimeHitStatement`** (NAMED, NOT proved here): there is a closed set `B` such that almost surely the trace
  avoids `B` before the lifetime and is in `B` at a finite positive lifetime (the continuation threshold is the first
  hit of the bad boundary set);
* **`FlowTransientStatement`**: almost surely on `{ζα = ∞}` the trace tends to `∞` — PROVED from Theorem 1.3
  (`flowTransientStatement_of_thm13`).

Proved: **`gw2RdVersionStatement_of_lifetime`**: `GW2RdVersionStatement` from the counterflow's no-return and these two;
`counterflowNoReturn_of_thm13` (the no-return from Theorem 1.3, as `Wire.counterflowNoReturnStatement_of_theorem13`);
**`flowTransientStatement_of_thm13`** (the frozen Theorem 1.3 contains transience on `{ζ = ∞}` for every word);
**`gw2RdVersionStatement_of_thm13_hit`**; **`gw2JointDetC2Statement_of_thm12_thm13_hit`**: GW2's root determination
from Theorems 1.2–1.3, `FlowLifetimeHitStatement` and `GW2RdSafeStatement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.RelDrv.Version Supp8.GB6.HullId Supp8.GB6.SourceC
  Supp8.GB6.ReadD Supp8.Q3Stop Exist.StagedLaw Exist.Staged Restart Sec7.StripSysField GW2TipSystem
  Theorem14.GW2JointKernel

/-! ### The two one-curve statements -/

/-- **Named statement (NOT proved here): the lifetime of a flow line is the first hit of a closed set.** For a flow
line of a GFF with piecewise-constant data (`0 < κ < 4`, angle `θ ∈ [−π/2, π/2]`) there is a closed set `B` such that
almost surely the trace avoids `B` before the lifetime and lies in `B` at a finite positive lifetime. (For a simple
flow line `B` is the closed bad boundary set: the points where the trace's collision with the marks has total weight at
most `−2`; the statement contains that the trace does not land exactly on a mark at an admissible collision.) -/
def FlowLifetimeHitStatement : Prop :=
  ∀ (κ θ : ℝ), 0 < κ → κ < 4 → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (h : Ω → DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞)
    (α : Ω → ℝ≥0 → ℂ),
    IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J → IsFlowLineDriver κ b J θ P h Wα ζα →
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) →
    ∃ B : Set ℂ, IsClosed B ∧ ∀ᵐ ω ∂P, (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζα ω → α ω t ∉ B) ∧
      ∀ T : ℝ≥0, (T : ℝ≥0∞) = ζα ω → 0 < T → α ω T ∈ B

/-- **Named statement (NOT proved here): a flow line of infinite lifetime is transient.** For a flow line of a GFF
with piecewise-constant data (`0 < κ < 4`, angle `θ ∈ [−π/2, π/2]`), almost surely on `{ζα = ∞}` its trace tends to
`∞` (Aux. lemma 7 on the event of infinite lifetime; for admissible words `Zhan.aux7Statement`). -/
def FlowTransientStatement : Prop :=
  ∀ (κ θ : ℝ), 0 < κ → κ < 4 → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (h : Ω → DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞)
    (α : Ω → ℝ≥0 → ℂ),
    IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J → IsFlowLineDriver κ b J θ P h Wα ζα →
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) →
    ∀ᵐ ω ∂P, ζα ω = ⊤ → Tendsto (fun t => ‖α ω t‖) atTop atTop

/-! ### Two sample facts of the extended flow -/

/-- The regularized flow driver is frozen from the lifetime on. -/
theorem regW_frozen {Ω : Type*} (s : ℝ≥0) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (ω : Ω) (t : ℝ≥0)
    (ht : ζα ω ≤ t) : regW s Wα ζα t ω = regW s Wα ζα (ζα ω).toNNReal ω := by
  obtain ⟨-, -, hfrz, -⟩ :=
    StagedReg.isRegularDriver_regularize (s : ℝ≥0∞) (fun r => GW2JointKernel.cfKW Wα ζα r ω, ζα ω)
  have hsnd : (StagedReg.regularize (s : ℝ≥0∞) (fun r => GW2JointKernel.cfKW Wα ζα r ω, ζα ω)).2 = ζα ω :=
    StagedReg.regularize_snd _ _
  rw [hsnd] at hfrz
  exact hfrz t ht

/-- Drivers that agree before `Tα` have the same relative clock before `Tα`. -/
theorem relClock_eq_of_lt_lifetime {s : ℝ≥0} {w wb wα : ℝ≥0 → ℝ} {Tα : ℝ≥0∞}
    (heq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tα → wb t = wα t) {t : ℝ≥0} (htα : (t : ℝ≥0∞) < Tα) :
    relClock (fun r : ℝ => w r.toNNReal) s (fun r : ℝ => wb r.toNNReal) t =
      relClock (fun r : ℝ => w r.toNNReal) s (fun r : ℝ => wα r.toNNReal) t := by
  obtain ⟨t₂, htt₂, ht₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 htα
  have htt₂' : t < t₂ := by exact_mod_cast htt₂
  have hK : QuantumZipper.fwdHull (fun r : ℝ => wb r.toNNReal) t =
      QuantumZipper.fwdHull (fun r : ℝ => wα r.toNNReal) t :=
    fwdHull_eq_of_eqOn t.coe_nonneg (NNReal.coe_lt_coe.2 htt₂') fun r hr => heq r.toNNReal
      (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)) ht₂)
  unfold relClock
  rw [hK]

/-! ### `GW2RdVersionStatement` -/

/-- **GW2's exhausting capped versions from the counterflow's no-return and two one-curve facts** (conditional
helper). -/
theorem gw2RdVersionStatement_of_lifetime (hNR : GW4Ident.CounterflowNoReturnStatement.{u})
    (hhit : FlowLifetimeHitStatement.{u}) (htr : FlowTransientStatement.{u}) : GW2RdVersionStatement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hh hb' hT hcf hpL hpR hreg hfl hα hseed s
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := hreg.mono fun ω hω => hω.1
  have hγ' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω) := hreg.mono fun ω hω => by
    rw [hω.1]
    exact hω.2.1
  have hrecm : Measurable (gb6Rec s W ζ) := (measurable_recOf_cfE hcf s).2
  have hgoodrec := ae_gb6RecGood hcf hγ' s
  by_cases hs0 : s = 0
  · -- a zero counterflow prefix: the interior-tip event is null
    subst hs0
    have hγ0 : ∀ᵐ ω ∂P, γ ω 0 = 0 := hreg.mono fun _ hω => hω.2.1.1
    have hnull : ∀ᵐ ω ∂P, γ ω 0 ∉ H := hγ0.mono fun ω hω hH => by
      rw [hω] at hH
      exact (lt_irrefl (0 : ℝ)) hH
    obtain ⟨R, V, hRV, -⟩ := exists_versionsR_at_zero (P := P) (W := regW 0 Wα ζα) (Wα := W) (ζα := ζ)
      (γ := extTr 0 Wα ζα α) hγ0
    refine ⟨R, V, fun m => ⟨⟨hRV m, fun _ _ => 0, fun _ => measurable_const, fun _ _ _ _ _ => rfl,
      fun _ _ => ENNReal.zero_ne_top, fun _ _ _ _ => le_rfl, ?_⟩, ?_⟩, ?_⟩
    · filter_upwards [hgoodrec, hγ0] with ω hg hω hm
      obtain ⟨-, hH⟩ := (mem_gb6TS_iff hg).2 hm
      rw [hω] at hH
      exact ((lt_irrefl (0 : ℝ)) hH).elim
    · filter_upwards [hnull] with ω hω hH using absurd hH hω
    · filter_upwards [hnull] with ω hω hH using absurd hH hω
  have hs : 0 < s := pos_iff_ne_zero.2 hs0
  set Wb : ℝ≥0 → Ω → ℝ := regW s Wα ζα with hWb
  set αb : Ω → ℝ≥0 → ℂ := extTr s Wα ζα α with hαb
  have hpos : ∀ᵐ ω ∂P, 0 < ζα ω := SB.Retain.ae_lifetime_pos_of_seed_admissible hfl hseed
  have hext := ae_extTr_spec hκ hfl hα s
  -- the extended flow: continuous, from `0`, with a transient generating trace
  have hexpl : ∀ᵐ ω ∂P, Continuous (Wb · ω) ∧ Wb 0 ω = 0 ∧ IsGeneratingTrace (Wb · ω) ⊤ (αb ω) ∧
      Tendsto (fun t => ‖αb ω t‖) atTop atTop := by
    filter_upwards [hext, hpos, htr κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J Wα ζα α hb hh hfl hα] with ω he hp hti
    obtain ⟨hc, h0, -, hgen, hag⟩ := he hp
    refine ⟨hc, h0, hgen, ?_⟩
    rcases eq_or_ne (ζα ω) ⊤ with htop | hfin
    · have he' : αb ω = α ω := funext fun u => hag u (by rw [htop]; exact le_top)
      rw [he']
      exact hti htop
    · have hζS : (((ζα ω).toNNReal : ℝ≥0) : ℝ≥0∞) = ζα ω := ENNReal.coe_toNNReal hfin
      have hS : (0 : ℝ≥0) < (ζα ω).toNNReal := by
        rw [← ENNReal.coe_lt_coe, hζS]
        simpa using hp
      exact tendsto_norm_trace_of_frozen hc h0 hS (fun t ht => regW_frozen s Wα ζα ω t (by
        rw [← hζS]; exact_mod_cast ht)) hgen
  have hexpl' : ∀ᵐ ω ∂P, Continuous (Wb · ω) ∧ Wb 0 ω = 0 ∧ IsGeneratingTrace (Wb · ω) ⊤ (αb ω) :=
    hexpl.mono fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
  -- the counterflow: regularity and no-return
  have hcfreg := Supp8.GB6.ae_driver_zero_continuousOn hcf
  have hnr : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζ ω → α' v ≠ 0 := by
    have h1 := hNR κ hκ hκ4 b J hb P h hh W ζ ⟨b', J', h', hb', hT, hcf⟩ hζ
    filter_upwards [h1, hζ] with ω hω hz α' hα' v hv _
    rw [hz] at hα'
    exact hω α' hα' v hv
  -- relative coordinates for the extended flow
  obtain ⟨_, 𝓕cf, _, _, _, _, hCcf⟩ := id hcf
  have hWa : AdaptedBefore (Filtration.const ℝ≥0 mΩ le_rfl) (fun _ => (⊤ : ℝ≥0∞)) Wb := by
    intro t A hA
    have e : {ω | (t : ℝ≥0∞) < (fun _ => (⊤ : ℝ≥0∞)) ω ∧ Wb t ω ∈ A} = Wb t ⁻¹' A := by
      ext ω
      simp only [mem_ofPred_eq, ENNReal.coe_lt_top, true_and, mem_preimage]
    rw [e]
    exact (measurable_regW hfl s t) hA
  have hcfE : ∀ᵐ ω ∂P, (fun _ : Ω => (⊤ : ℝ≥0∞)) ω = ⊤ ∧ Wb 0 ω = 0 ∧ Continuous (Wb · ω) ∧
      IsGeneratingTrace (Wb · ω) ⊤ (αb ω) := hexpl'.mono fun _ h => ⟨rfl, h.2.1, h.1, h.2.2⟩
  have hflE : ∀ᵐ ω ∂P, W 0 ω = 0 ∧ ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      IsGeneratingTrace (W · ω) (ζ ω) (γ ω) := by
    filter_upwards [hcfreg, hγ'] with ω hr ht using ⟨hr.1, hr.2, ht⟩
  obtain ⟨D, L, hC⟩ := SourceC.exists_relative_driver (P := P) hWa hCcf.1.2.1 hcfE hflE s hs
  -- GB6's live readout, the read-back and the cap at the flow's lifetime
  have hLive := hasLiveReadout_nr hcf hγ' hnr hexpl s hs hC
  have hread := ae_physicalReadback_nr hcf hγ' hnr hexpl' s hs hC
  have hsep := ae_separationRead_regular_nr hcf hγ' hnr hexpl' s hs hC
  obtain ⟨B, hBc, hB⟩ := hhit κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J Wα ζα α hb hh hfl hα
  set Lζ : Ω → ℝ≥0∞ := fun ω => capLife (gb6Clock s Wb W ω) (gb6Tc s αb γ ω) (ζα ω) with hLζ
  have hcapF : ∀ᵐ ω ∂P, gb6Rec s W ζ ω ∈ gb6TS s → 0 < Lζ ω ∧
      (∀ u : ℝ≥0, (u : ℝ≥0∞) < L ω → (u : ℝ≥0∞) < Lζ ω →
        physicalTrace s u (gb6Rec s W ζ ω, fun v => D v ω) ∉ B) ∧
      ∀ u : ℝ≥0, (u : ℝ≥0∞) < L ω → (u : ℝ≥0∞) = Lζ ω →
        physicalTrace s u (gb6Rec s W ζ ω, fun v => D v ω) ∈ B := by
    filter_upwards [hread, hgoodrec, hext, hpos, hB] with ω hrω hg he hp hBω hm
    obtain ⟨hs', hsH⟩ := (mem_gb6TS_iff hg).2 hm
    obtain ⟨ha0, ham, -, -, hcapω⟩ := hrω hs' hsH
    obtain ⟨-, -, -, -, hag⟩ := he hp
    exact capLife_facts ha0 ham hcapω hp hag hBω.1 hBω.2
  have hζcap : ∀ᵐ ω ∂P, gb6Rec s W ζ ω ∈ gb6TS s → 0 < Lζ ω ∧
      ContinuousOn (fun t => capGauge s B t (gb6Rec s W ζ ω, fun u => D u ω)) {t | (t : ℝ≥0∞) < L ω} ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → (t : ℝ≥0∞) < Lζ ω →
        0 < capGauge s B t (gb6Rec s W ζ ω, fun u => D u ω)) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → (t : ℝ≥0∞) = Lζ ω → capGauge s B t (gb6Rec s W ζ ω, fun u => D u ω) = 0 := by
    classical
    filter_upwards [hcapF, hsep] with ω hcω hsω hm
    obtain ⟨hL0, hout, hin⟩ := hcω hm
    obtain ⟨-, -, -, -, hX⟩ := hsω hm
    refine ⟨hL0, ?_, fun t ht htL => ?_, fun t ht htL => ?_⟩
    · unfold capGauge
      split_ifs
      · exact ContinuousOn.inf continuousOn_const ((continuous_infDist_pt B).comp_continuousOn hX)
      · exact continuousOn_const
    · have hn := hout t ht htL
      unfold capGauge
      split_ifs with hne
      · exact lt_min zero_lt_one ((hBc.notMem_iff_infDist_pos hne).1 hn)
      · exact zero_lt_one
    · have hm' := hin t ht htL
      have hne : B.Nonempty := ⟨_, hm'⟩
      unfold capGauge
      simp only [hne, ↓reduceIte, infDist_zero_of_mem hm']
      exact min_eq_right zero_le_one
  obtain ⟨D', L', Lg, g, G', hC', hrd, hle, -, hLg⟩ := exists_capReadout hC hrecm hgoodrec hLive
    (measurable_capGauge s B) (isCausal_capGauge s B) (capGauge_nonneg s B) hζcap
  refine ⟨fun m => coordDriver (D := D') (g := g) m, fun m ω => (coordStop (g := g) m ω : ℝ≥0∞),
    fun m => ⟨isGB6RelVersionA_capCoord hC' hrd hle m, ?_⟩, ?_⟩
  · -- the cap: every relative time before a stop is the clock of a time before the flow's lifetime
    filter_upwards [hLg, hgoodrec, hζ, hread, hC.relative, hext, hpos] with ω hLgω hg hz hrω hrel he hp hsH u hu
    have hs' : (s : ℝ≥0∞) < ζ ω := by rw [hz]; exact ENNReal.coe_lt_top
    have hm : gb6Rec s W ζ ω ∈ gb6TS s := (mem_gb6TS_iff hg).1 ⟨hs', hsH⟩
    have hV := coordStop_lt_cap hrd m ω
    rw [hLgω hm] at hV
    have hu' := hu.trans hV
    obtain ⟨-, -, hac, -, -⟩ := hrω hs' hsH
    obtain ⟨hcov, -⟩ := hrel hs' hsH
    obtain ⟨t, htζ, hut⟩ := exists_lt_clock_of_lt_capLife hac hp hcov (lt_min_iff.1 hu').1 (lt_min_iff.1 hu').2
    obtain ⟨-, -, heq, -, -⟩ := he hp
    refine ⟨t, htζ, ?_⟩
    have hcl := relClock_eq_of_lt_lifetime (s := s) (w := fun t => W t ω) heq htζ
    have hcl' : gb6Clock s Wb W ω t = gw2Clock s W Wα ω t := hcl
    rwa [hcl'] at hut
  · -- exhaustion before the end time
    filter_upwards [hLg, hgoodrec, hζ, hread, hC.relative, hext, hpos] with ω hLgω hg hz hrω hrel he hp hsH t ht
    have hs' : (s : ℝ≥0∞) < ζ ω := by rw [hz]; exact ENNReal.coe_lt_top
    have hm : gb6Rec s W ζ ω ∈ gb6TS s := (mem_gb6TS_iff hg).1 ⟨hs', hsH⟩
    have htζ : (t : ℝ≥0∞) < ζα ω := (lt_min_iff.1 ht).1
    have htc := (lt_min_iff.1 ht).2
    obtain ⟨-, -, heq, -, hag⟩ := he hp
    obtain ⟨-, hcl, hTc⟩ := hull_clock_contact_of_ext (w := fun t => W t ω) heq hag htζ htc
    obtain ⟨ha0, ham, -, -, -⟩ := hrω hs' hsH
    obtain ⟨-, hK⟩ := hrel hs' hsH
    obtain ⟨-, hlt, -⟩ := hK t hTc
    have h1 : ENNReal.ofReal (gb6Clock s Wb W ω t) < Lg ω := by
      rw [hLgω hm]
      exact lt_min hlt (lt_capLife ha0 ham htζ hTc)
    obtain ⟨m, hm'⟩ := exists_lt_coordStop_cap hrd h1
    refine ⟨m, ?_⟩
    have hcl' : gb6Clock s Wb W ω t = gw2Clock s W Wα ω t := hcl
    rwa [hcl'] at hm'

/-! ### Wiring -/

/-- **The counterflow does not return to its start, from Theorem 1.3** (the proof of
`Wire.counterflowNoReturnStatement_of_theorem13`, without importing the wiring layer). -/
theorem counterflowNoReturn_of_thm13 (h13 : Exist.Theorem13Statement.{u}) :
    GW4Ident.CounterflowNoReturnStatement.{u} := by
  apply CfNoReturn.counterflowNoReturnStatement_of_twoSeedComplete
  intro κ hκ rL rR _ _ Ω mΩ P _ 𝓕 W VL VR B ζ hE
  exact (h13 (lt_trans (show (0 : ℝ) < 4 by norm_num) hκ) LP.isOrderedForceWord_twoSeed hE).mono
    fun _ hω => hω.2

/-- **A flow line of infinite lifetime is transient, from Theorem 1.3** (`FlowTransientStatement`): the frozen
Theorem 1.3 gives a generating trace that tends to `∞` on `{ζ = ∞}` for every word, and generating traces of one
driver agree (`StoppedExtend.trace_eq_of_driver_eq`). -/
theorem flowTransientStatement_of_thm13 (h13 : Exist.Theorem13Statement.{u}) : FlowTransientStatement.{u} := by
  intro κ θ hκ _ _ _ Ω mΩ P hP h b J Wα ζα α _ _ hfl hα
  have := hP
  obtain ⟨_, 𝓕, VL, VR, B, -, hC⟩ := id hfl
  have hord := Theorem15.isOrderedForceWord_flowLine b J 0
  filter_upwards [h13 hκ hord hC.1, hα, Supp8.GB6.ae_driver_zero_continuousOn hfl] with ω hω hαω hd hz
  obtain ⟨-, η, hη, htrη⟩ := hω
  have heq := Restart.StoppedExtend.trace_eq_of_driver_eq hαω hd.2 hd.1 hη hd.2 hd.1 le_rfl le_rfl
    (fun _ _ => rfl)
  refine (htrη hz).congr' (Eventually.of_forall fun t => ?_)
  show ‖η t‖ = ‖α ω t‖
  rw [heq t (by rw [hz]; exact le_top)]

/-- **`GW2RdVersionStatement` from Theorem 1.3 and the lifetime-hit statement** (conditional helper). -/
theorem gw2RdVersionStatement_of_thm13_hit (h13 : Exist.Theorem13Statement.{u})
    (hhit : FlowLifetimeHitStatement.{u}) : GW2RdVersionStatement.{u} :=
  gw2RdVersionStatement_of_lifetime (counterflowNoReturn_of_thm13 h13) hhit (flowTransientStatement_of_thm13 h13)

/-- **GW2's root determination from Theorems 1.2–1.3, the lifetime-hit statement and the relative safe law**
(conditional helper). -/
theorem gw2JointDetC2Statement_of_thm12_thm13_hit (h12p₀ : Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (hhit : FlowLifetimeHitStatement.{u})
    (hS : GW2RdSafeStatement.{u}) : GW2JointDetC2Statement.{u} :=
  gw2JointDetC2Statement_of_versions_safe h12p₀ h13₀ (gw2RdVersionStatement_of_thm13_hit h13 hhit) hS

end InteractingSLE.Theorem14.GW2Rd
