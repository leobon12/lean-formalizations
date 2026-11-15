/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvCells

/-!
# SB2(1)'s identification from K2 in the entrance σ-algebra

Packet PROVE-T14-SB2DRV. K2 needs its live event in the conditioning σ-algebra and the relative driver
adapted from time `0`. The entrance event `{T_L < ζ}` of SB2(1) is not an event of the retained past
`pastSigma (k + 1)`, and off it no actual relative driver exists, so K2 cannot be run on the launch
event with that σ-algebra. The source conditions on more: "The entrance point `L` [...] Its first
visit [...] is a stopping rule of this retained staged history. The initial erased portion adds no set
in `D_A` [...] Thus even the full erased history, its entry germ and stopping flags leave the same
conditional field in `D_A`" (supplement p. 632). Accordingly:

* `SB2EntranceK2Statement` (named input): an **entrance σ-algebra** `𝒢' ⊇ pastSigma (k + 1)` with a
  live event `F' ∈ 𝒢'` covering the entrance event on the launch event, under whose conditional laws
  the field read in the launch chart is still the GFF of the launch word on `F'` (the erasure); a
  globally continuous relative driver `W` adapted to a filtration `𝓗` with `𝒢' ≤ 𝓗 0`; K2's (S) and
  (L) on every admissible force-type cell of `F'`; integrability of the chart pairings on `F'`; and, almost
  surely on the entrance event, the generating trace and the remainder link of `W` with the cell's
  geometric threshold as lifetime (the link and the lifetime reconstruction);
* `ae_frozen_chart_of_le`: the recentred version chart is frozen under the conditional laws given
  any σ-algebra containing the retained past (from the frozen run);
* **`sb2RemainderCodeStatement_of_entranceK2`**: `SB2RemainderCodeStatement` from Theorems 1.2–1.3 and
  `SB2EntranceK2Statement`, through `ae_codeMatch_of_k2_cells`; the admissible seed on the entrance
  event follows from the link (`not_seed_of_thr_pos`);
* `sb2DriverLinkAmbStatement_of_entranceK2`: hence SB2(1)'s driver and link.

**R48.** Theorems 1.2–1.3 are hypotheses; this serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Sec4 Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Exist.Staged Exist.StagedLaw
  Supp8.Q3Stop WalkInf Sec7.PocketTraversal

/-- The recentred version chart of a launch chart record (the chart of `K2LaunchInputs.chart_measurable`). -/
def K2LaunchInputs.chart {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ}
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (ω : Ω) : Chart :=
  (verChart κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω).recenter (I.entry ω)

/-- **Named input: K2 in SB2(1)'s entrance σ-algebra** (supplement pp. 631–633: the geometry of the
erasure, the initial and optional Gaussian kernels of the marked union, the erased history leaving the
same conditional field in `D_A`, integrated uniqueness). For every SB2(1) launch problem and every
compatible launch chart record there are an entrance σ-algebra `𝒢'` (a sub-σ-algebra, bound as a
subtype so that it never becomes an instance) and live event `F'`, a filtration
`𝓗` and an adapted, globally continuous relative driver `W` from `0` with a relative trace `Γ`, such that:
(1) `pastSigma (k + 1) ≤ 𝒢' ≤ 𝓗 0`, `F' ∈ 𝒢'`, `F'` lies in the launch event and covers almost all of
the entrance event there; (2) on `F'`, conditionally on `𝒢'`, the field read in the recentred launch
chart is the GFF of the launch word; (3) the chart pairings of the flow-rule field are integrable on `F'`;
(4) K2's (S) and (L) hold on every admissible force-type cell of `F'`, with the cell's geometric
threshold as lifetime; (5) for a relative lifetime `Vg`: almost surely on the entrance event `Γ` is a
generating trace of `W` up to `Vg`, linked to the actual upper flow (the geometry of the erasure), and
(6) `Vg` is the geometric threshold of the sample's force-type cell (the lifetime reconstruction). -/
def SB2EntranceK2Statement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (_H : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ),
    ∃ (𝒢' : {m : MeasurableSpace Ω // m ≤ mΩ}) (F' : Set Ω) (𝓗 : Filtration ℝ≥0 mΩ)
      (W : ℝ≥0 → Ω → ℝ) (Γ : Ω → ℝ≥0 → ℂ),
      pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ≤ 𝒢'.1 ∧
      𝒢'.1 ≤ 𝓗 0 ∧ MeasurableSet[𝒢'.1] F' ∧ F' ⊆ launchSet κ b jumps E (k + 1) ∧
      (∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
        firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω → ω ∈ F') ∧
      (∀ᵐ ω₀ ∂P, ω₀ ∈ F' → ∃ h' : Ω → DistOn upperHalfPlaneOpens,
        (∀ ω, IsChartTransport (I.chart ω₀) 1 0 (chiC κ) (h ω) (h' ω)) ∧
        IsGFFWithBoundaryData (condExpKernel P 𝒢'.1 ω₀) h' (I.word ω₀).fn (I.word ω₀).jumps) ∧
      (∀ ω, W 0 ω = 0) ∧ (∀ ω, Continuous fun t => W t ω) ∧ StronglyAdapted 𝓗 W ∧
      (∀ φ : TestOn upperHalfPlaneOpens, IntegrableOn (fun ω =>
        Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ) (h ω) φ) F' P) ∧
      (∀ w ∈ I.types,
        HasSafeLaw κ (typedRhoL w) (typedRhoR w) P 𝓗 (seedCell κ ψ I.word F' w)
          (FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w)) W
          (geomLW W (cellXL κ ψ I.word w)) (geomRW W (cellXR κ ψ I.word w))
          (fun ω => Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ) (h ω)) ∧
        HasSafeMembers P 𝓗 (seedCell κ ψ I.word F' w)
          (FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w)) W
          (fun ω => Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ) (h ω))) ∧
      ∃ Vg : Ω → ℝ≥0∞,
        (∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
          firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω →
          IsGeneratingTrace (fun t => W t ω) (Vg ω) (Γ ω) ∧
            IsRemainderLink (launchChart κ b jumps E (k + 1) ω) (η ω) (ζ ω)
              (realMin (lowerPrefix κ b jumps E (k + 1) u ω))
              (fun t => Γ ω t + launchEntry κ b jumps E (k + 1) u ω) (Vg ω)) ∧
        ∀ w ∈ I.types, ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
          firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω →
          ω ∈ wordTypeCell κ ψ I.word F' w →
          Vg ω = FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω

/-- A remainder link at an entrance gives a positive relative lifetime. -/
theorem pos_of_isRemainderLink {c : Chart} {η ηr : ℝ≥0 → ℂ} {ζ V : ℝ≥0∞} {L : ℝ}
    (hl : IsRemainderLink c η ζ L ηr V) (hv : firstVisit η ζ L < ζ) : 0 < V := by
  obtain ⟨σ, hσ0, -, -, hσ⟩ := hl hv
  have h0 := (hσ 0).1
  rw [hσ0, add_zero, ENNReal.coe_toNNReal (ne_top_of_lt hv)] at h0
  exact_mod_cast h0.2 hv

/-- **The recentred version chart is frozen under the conditional laws given any σ-algebra
containing the retained past**, on the launch event (the run through `k + 1` instructions is frozen,
`CondDriverBridge.ae_ae_run_eq_of_le`, hence the launch chart and its entry; the version chart agrees
with them almost surely on the launch event). -/
theorem ae_frozen_chart_of_le {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    {𝒢' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (H : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (h𝒢' : 𝒢' ≤ mΩ)
    (hpast : pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ≤ 𝒢') :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E (k + 1) →
      ∀ᵐ ω ∂(condExpKernel P 𝒢' ω₀), I.chart ω = I.chart ω₀ := by
  let w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
  have hprog := isBoundaryContinuedProgram_boundaryWalkSpec b jumps
    (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hS : IsStagedHistory κ b jumps P h w (E w) := H.staged w hprog
  have hF : MeasurableSet[𝒢'] (launchSet κ b jumps E (k + 1)) :=
    hpast _ (measurableSet_launch_pastSigma H.boundary hS.1 (H.drivers_regular w) (k + 1))
  filter_upwards [CondDriverBridge.ae_ae_run_eq_of_le (P := P) (κ := κ) (b := b) (jumps := jumps) w
      (fun j _ => H.drivers_regular w j) h𝒢' hpast,
    Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢' I.chart_eq,
    Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝒢' hF, I.chart_eq]
    with ω₀ hrun hceq hmem hc₀ hF₀
  filter_upwards [hrun, hceq, hmem hF₀] with ω hrunω hceqω hFω
  unfold K2LaunchInputs.chart
  rw [hceqω hFω, hc₀ hF₀]
  have h1 : launchChart κ b jumps E (k + 1) ω = launchChart κ b jumps E (k + 1) ω₀ := by
    unfold launchChart
    rw [launches_run_succ_of_run_eq w hrunω]
  rw [h1, (launchEntry_eq_of_run_eq (u := u) hrunω).2]

/-- **SB2(1)'s per-sample identification from K2 in the entrance σ-algebra.** On the entrance event
the sample lies in `F'` and in the cell of its own force type; the link forces a positive threshold,
hence an admissible seed (`not_seed_of_thr_pos`), so the sample lies in the admissible cell, where K2
gives the canonical code (`ae_codeMatch_of_k2_cells`). -/
theorem sb2RemainderCodeStatement_of_entranceK2 (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hK : SB2EntranceK2Statement.{u}) :
    SB2RemainderCodeStatement h12p := by
  intro κ b jumps Ω _ _ P _ h E k u ψ η ζ H I
  obtain ⟨G', F', 𝓗, W, Γ, hpast, h𝒢𝓗, hF'm, hF'sub, hF'vis, herase, hW0, hWc, hWa,
    hint, hK2, Vg, hlink, hlife⟩ := hK κ b jumps P h E k u ψ η ζ H I
  have hcw' : Measurable[G'.1] I.word := I.word_measurable.mono hpast le_rfl
  have hc' : IsMeasChart G'.1 I.chart := I.chart_measurable.mono hpast
  have hcc' := ae_frozen_chart_of_le H I G'.2 hpast
  have hG' : ∀ᵐ ω₀ ∂P, ω₀ ∈ F' → IsPiecewiseConstantBoundaryData (I.word ω₀).fn (I.word ω₀).jumps ∧
      ∃ h' : Ω → DistOn upperHalfPlaneOpens,
        (∀ ω, IsChartTransport (I.chart ω₀) 1 0 (chiC κ) (h ω) (h' ω)) ∧
        IsGFFWithBoundaryData (condExpKernel P G'.1 ω₀) h' (I.word ω₀).fn (I.word ω₀).jumps := by
    filter_upwards [I.field, herase] with ω₀ hf he hω₀
    exact ⟨(hf (hF'sub hω₀)).1, he hω₀⟩
  have hcodes := ae_codeMatch_of_k2_cells (θ := ψ) h12p h13 H.kappa_pos h𝒢𝓗 hF'm hcw' hc'
    (hcc'.mono fun ω h hω => h (hF'sub hω)) H.field.1 hG' hW0 hWc hWa hint I.types_countable
    (fun w hw => (hK2 w hw).1) (fun w hw => (hK2 w hw).2)
  filter_upwards [hcodes, hlink, (ae_ball_iff I.types_countable).2 hlife, hF'vis, I.cover]
    with ω hcode hl hlf hvisF hcov hF hvis
  have hωF' := hvisF hF hvis
  obtain ⟨w₀, hw₀e⟩ : ∃ w₀, angleWordType κ ψ (I.word ω) = w₀ := ⟨_, rfl⟩
  have hw₀ : w₀ ∈ I.types := hw₀e ▸ hcov hF
  have hcell : ω ∈ wordTypeCell κ ψ I.word F' w₀ := ⟨hωF', hw₀e⟩
  obtain ⟨hgen, hlk⟩ := hl hF hvis
  rw [hlf w₀ hw₀ hF hvis hcell] at hgen hlk
  have hpos := pos_of_isRemainderLink hlk hvis
  have hxL0 : ∀ ω i, cellXL κ ψ I.word w₀ ω i ≤ 0 := fun ω =>
    (FCDet.isOrderedForceWord_typeXL (I.word ω)).2.1
  have hxR0 : ∀ ω j, 0 ≤ cellXR κ ψ I.word w₀ ω j := fun ω =>
    (FCDet.isOrderedForceWord_typeXL (I.word ω)).2.2.2
  have hsc : ω ∈ seedCell κ ψ I.word F' w₀ := ⟨hcell, not_seed_of_thr_pos hW0 hWc hxL0 hxR0 hpos⟩
  exact ⟨fun t => W t ω, _, Γ ω, (hWc ω).continuousOn, hcode w₀ hw₀ hsc, hgen, hlk⟩

/-- **SB2(1)'s clauses (1) and (3) at the launches after the first from Theorems 1.2–1.3 and K2 in
the entrance σ-algebra.** -/
theorem sb2DriverLinkAmbStatement_of_entranceK2 (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hK : SB2EntranceK2Statement.{u}) :
    SB2DriverLinkAmbStatement.{u} :=
  sb2DriverLinkAmbStatement_of_remainderCode h12p h13
    (sb2RemainderCodeStatement_of_entranceK2 h12p h13 hK)

/-! ### Route B: the retained past itself as the conditioning σ-algebra -/

/-- **Named input, route B: K2 in the retained past on the whole launch event.** As
`SB2EntranceK2Statement` with `𝒢' = pastSigma (k + 1)` and `F' = launchSet (k + 1)`: the erasure clause is
then the landed `K2LaunchInputs.field`, but the relative driver `W` must be defined, adapted and satisfy
K2's (S) and (L) on the whole launch event (off the entrance event it is any canonical continuation; the
erasure of p. 632 is then needed inside (S) and (L)). -/
def SB2LaunchK2Statement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (_H : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ),
    ∃ (𝓗 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (Γ : Ω → ℝ≥0 → ℂ),
      pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ≤ 𝓗 0 ∧
      (∀ ω, W 0 ω = 0) ∧ (∀ ω, Continuous fun t => W t ω) ∧ StronglyAdapted 𝓗 W ∧
      (∀ φ : TestOn upperHalfPlaneOpens, IntegrableOn (fun ω =>
        Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ) (h ω) φ)
        (launchSet κ b jumps E (k + 1)) P) ∧
      (∀ w ∈ I.types,
        HasSafeLaw κ (typedRhoL w) (typedRhoR w) P 𝓗 (seedCell κ ψ I.word (launchSet κ b jumps E (k + 1)) w)
          (FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w)) W
          (geomLW W (cellXL κ ψ I.word w)) (geomRW W (cellXR κ ψ I.word w))
          (fun ω => Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ) (h ω)) ∧
        HasSafeMembers P 𝓗 (seedCell κ ψ I.word (launchSet κ b jumps E (k + 1)) w)
          (FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w)) W
          (fun ω => Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ) (h ω))) ∧
      ∃ Vg : Ω → ℝ≥0∞,
        (∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
          firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω →
          IsGeneratingTrace (fun t => W t ω) (Vg ω) (Γ ω) ∧
            IsRemainderLink (launchChart κ b jumps E (k + 1) ω) (η ω) (ζ ω)
              (realMin (lowerPrefix κ b jumps E (k + 1) u ω))
              (fun t => Γ ω t + launchEntry κ b jumps E (k + 1) u ω) (Vg ω)) ∧
        ∀ w ∈ I.types, ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
          firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω →
          ω ∈ wordTypeCell κ ψ I.word (launchSet κ b jumps E (k + 1)) w →
          Vg ω = FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω

/-- **Route B implies route A**: take `𝒢' = pastSigma (k + 1)`, `F' = launchSet (k + 1)`; the erasure
clause is the landed conditional chart field (`K2LaunchInputs.field`). -/
theorem sb2EntranceK2Statement_of_launchK2 (hB : SB2LaunchK2Statement.{u}) :
    SB2EntranceK2Statement.{u} := by
  intro κ b jumps Ω _ _ P _ h E k u ψ η ζ H I
  obtain ⟨𝓗, W, Γ, h0, hW0, hWc, hWa, hint, hK2, Vg, hlink, hlife⟩ := hB κ b jumps P h E k u ψ η ζ H I
  have hprog := isBoundaryContinuedProgram_boundaryWalkSpec b jumps
    (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hS := H.staged (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) hprog
  refine ⟨⟨_, hS.2.1 (k + 1)⟩, launchSet κ b jumps E (k + 1), 𝓗, W, Γ, le_rfl, h0,
    measurableSet_launch_pastSigma H.boundary hS.1 (H.drivers_regular _) (k + 1), subset_rfl,
    Eventually.of_forall fun _ hF _ => hF, ?_, hW0, hWc, hWa, hint, hK2, Vg, hlink, hlife⟩
  filter_upwards [I.field] with ω₀ hf hF
  exact (hf hF).2

/-- **SB2(1)'s clauses (1) and (3) at the launches after the first from Theorems 1.2–1.3 and route B.** -/
theorem sb2DriverLinkAmbStatement_of_launchK2 (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hB : SB2LaunchK2Statement.{u}) :
    SB2DriverLinkAmbStatement.{u} :=
  sb2DriverLinkAmbStatement_of_entranceK2 h12p h13 (sb2EntranceK2Statement_of_launchK2 hB)

end InteractingSLE.Theorem14.SB.Lv
