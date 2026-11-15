/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2LaterChain

/-!
# GB6's identification for staged prefixes: the equality form of the launch datum

Packet PROVE-T14-TIP12. Proposition GB6 (supplement p. 518, `source/spec/p481-528.md` L929–L933): "Conditional on the
marked prefix, the portion of `η` before its first contact with `α[0, σ]`, in the chart of `U` taking `(y, p)` to
`(0, ∞)`, is the complete canonical counterflow of the conditional component field. Its relative lifetime is
infinite." GW1's induction datum 2 (p. 618) and GW2a (p. 623) use it for staged prefixes; GB9 (p. 525) and follow-up
note A.4 use it to identify the joint chart of every later stage ("put the joint flow tip and the retained
counterflow tip at `0` and `∞`").

The landed launch datum `GW2Later.HasLaunchPair` (PROVE-T14-BR6) records only **containment**: the conditional
counterflow's tips, read through the launch chart, are points of the original completed counterflow range. GW2's later
stages need **equality**: the conditional counterflow *is* the original counterflow before its first contact with the
retained prefix, up to a time change (PROVE-T14-TIP11 §4.1, item 1). This file states the equality datum in the
time-change form of Corollary BR4a (`BR4a.BR4aStatement`, the root-`v` case of the same assertion) and relates it to
the landed chain:

* `contactSet`: the retained prefix before the launch of instruction `k` (the root and the launched pieces' physical
  ranges; the source's `α[0, σ]`);
* **`HasLaunchPairEq`**: under the conditional law given the retained past, for every field `h'` that is `h` read in
  the launch chart, a centred counterflow `Wk` of `h'` with infinite lifetime and a continuous strictly increasing time
  change `ℓ` onto the times before the first contact of the original counterflow with the retained prefix, such that
  the tips of `Wk` read through the launch chart are exactly the original counterflow's tips at the changed times;
* **`HasLaunchPairEq.hasLaunchPair`**: equality implies the landed containment datum;
* **`GB6StagedEqStatement`** (named): the equality datum at every launch `k ≥ 1` of a GW2 schedule (GB6 for the
  retained staged prefix), and **`gb6StagedPairStatement_of_eq`**: it implies the landed
  `GW2Later.GB6StagedPairStatement`;
* **`ae_hasLaunchPairEq_zero_root_arc`**: the equality datum at the first launch from a root `v` of the first low right
  arc, from Corollary BR4a (the prefix is `{v}`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2TipSystem

open CounterflowRange GW2Schedule GW2aMulti GW2Sched GW2Later

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The retained prefix before the launch of instruction `k`** (GB6's `α[0, σ]`): the root and the physical ranges of
the pieces launched so far. -/
def contactSet (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) :
    Set ℂ :=
  {(spec.1 : ℂ)} ∪ ⋃ p ∈ (ExplState.run κ b jumps spec D k).1, p.1.tipSet p.2.1 p.2.2

/-- Before the first launch the retained prefix is the root. -/
theorem contactSet_zero (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    contactSet κ b jumps spec D 0 = {(spec.1 : ℂ)} := by
  have h0 : (ExplState.run κ b jumps spec D 0).1 = [] := by
    simp [ExplState.run, ExplState.init]
  simp [contactSet, h0]

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **GB6's datum at the launch of instruction `k`, equality form**, at a sample `ω₀` of the retained past. If
instruction `k` launches a piece of `ω₀` in the chart `c`, then for every field `h'` that is `h` read in `c`, under the
conditional law `ν` given the retained past there are a centred counterflow driver `Wk` of `h'` and a time change `ℓ`
(measurable in the sample at each time) such that, `ν`-almost surely, `Wk` has infinite lifetime, `ℓ` is continuous,
strictly increasing, with range the times before the first contact of the original counterflow `W'` with the retained
prefix (`contactSet`), and the tips of `Wk` read through `c` and the inversion are exactly the tips of `W'` at the
changed times. (Corollary BR4a is this assertion for the prefix `{v}`.) -/
def HasLaunchPairEq (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (P : Measure Ω) [IsFiniteMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (spec : ExplSpec)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (ω₀ : Ω) : Prop :=
  ∀ (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
    ∀ h' : Ω → DistOn upperHalfPlaneOpens,
      (∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω) (h' ω)) →
      ∃ (Wk : ℝ≥0 → Ω → ℝ) (ζk : Ω → ℝ≥0∞) (ℓ : Ω → ℝ≥0 → ℝ≥0),
        IsCenteredCounterflowDriver κ (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) h' Wk ζk ∧
        (∀ u, Measurable fun ω => ℓ ω u) ∧
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), ζk ω = ⊤ ∧ Continuous (ℓ ω) ∧
          StrictMono (ℓ ω) ∧
          range (ℓ ω) = {t : ℝ≥0 | (t : ℝ≥0∞) < firstTipTime infinitySourceChart (fun s => W' s ω)
            (contactSet κ b jumps spec (fun j => E j ω₀) k)} ∧
          ∀ (r : ℝ≥0) (z : ℂ), (c.trans infinitySourceChart).tipAt (fun s => Wk s ω) r z ↔
            infinitySourceChart.tipAt (fun s => W' s ω) (ℓ ω r) z

omit [StandardBorelSpace Ω] in
/-- A tip of the original counterflow lies in its completed range. -/
theorem mem_counterflowCompletedRange_of_tipAt {W : ℝ≥0 → ℝ} {t : ℝ≥0} {z : ℂ}
    (hz : infinitySourceChart.tipAt W t z) : z ∈ counterflowCompletedRange W := by
  have h2 : z ∈ infinitySourceChart.tipSet W ⊤ := by
    rw [Chart.tipSet_eq_tipAt]
    exact ⟨t, le_top, hz⟩
  exact mem_union_left _ h2

/-- **Equality implies containment**: the equality datum gives the landed containment datum `HasLaunchPair`. -/
theorem HasLaunchPairEq.hasLaunchPair {P : Measure Ω} [IsFiniteMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {W' : ℝ≥0 → Ω → ℝ} {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {ω₀ : Ω}
    (hEq : HasLaunchPairEq κ b jumps P h W' spec E k ω₀) : HasLaunchPair κ b jumps P h W' spec E k ω₀ := by
  intro c θ hl h' htr
  obtain ⟨Wk, ζk, ℓ, hcf, -, hae⟩ := hEq c θ hl h' htr
  refine ⟨Wk, ζk, hcf, hae.mono fun ω hω => hω.1, hae.mono fun ω hω r z hz => ?_⟩
  exact mem_counterflowCompletedRange_of_tipAt ((hω.2.2.2.2 r z).1 hz)

/-- **Named input: Proposition GB6 for the retained prefix of a GW2 schedule, equality form** (supplement p. 518; GW1's
induction datum 2, p. 618; GW2a, p. 623; GB9, p. 525). The setting of `GW2Later.GB6StagedPairStatement` verbatim, with
the equality datum `HasLaunchPairEq` in place of the containment datum: at almost every sample whose switching tips
before the launch of instruction `k ≥ 1` are interior, the conditional counterflow targeted at the current tip is the
original counterflow before its first contact with the retained prefix, up to a time change. -/
def GB6StagedEqStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      ∀ x : ℝ, (x = 0 ∨ x ∈ lowerArcRoots κ b jumps) → ∀ l : List (ℝ × ℝ≥0),
        (∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) → l.Pairwise (fun p q => p.2 < q.2) →
        ∀ k : ℕ, 1 ≤ k → ∀ᵐ ω₀ ∂P,
          SwitchTipsInterior ⟨x, true, scheduleProgram 0 l⟩ (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω₀) k →
          HasLaunchPairEq κ b jumps P h W' ⟨x, true, scheduleProgram 0 l⟩ (E ⟨x, true, scheduleProgram 0 l⟩) k ω₀

/-- **GB6's staged equality implies the landed staged containment** (`GW2Later.GB6StagedPairStatement`). -/
theorem gb6StagedPairStatement_of_eq (hG : GB6StagedEqStatement.{u}) : GB6StagedPairStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg x hx l hl hlp k hk
  filter_upwards [hG κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg x hx l hl hlp k hk] with ω₀ hω₀ hint
  exact (hω₀ hint).hasLaunchPair

/-- **The equality datum at the first launch from a root `v` of the first low right arc** (Corollary BR4a: GW2,
p. 621, "BR4a gives the full conditional pair targeted at `v`"): the conditional law given the empty past is `P`, the
field read in the root chart is BR4a's field, and the retained prefix is `{v}`. Named inputs: BR4a, Theorem 1.3 (and at
`0`, for GW0). -/
theorem ae_hasLaunchPairEq_zero_root_arc (hBR4a : BR4a.BR4aStatement.{u}) (hT13 : Exist.Theorem13Statement.{u})
    (hT13₀ : Exist.Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {v : ℝ}
    (hv : v ∈ lowerArcRoots κ b jumps) {l : List (ℝ × ℝ≥0)} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω₀ : Ω) :
    HasLaunchPairEq κ b jumps P h W' ⟨v, true, scheduleProgram 0 l⟩ E 0 ω₀ := by
  have hGW0 : GW0.GW0ForwardStatement.{u} := BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀
  have hv0 := pos_of_mem_lowerArcRoots hv
  have hvR : ∀ᵐ ω ∂P, (v : ℂ) ∈ infinitySourceChart.tipSet (fun t => W' t ω) ⊤ := by
    filter_upwards [GW2Cone.ae_mem_counterflowCompletedRange_of_theorem13 hT13 hGW0 hκ hκ4 hb hh hcf hζ' hv hv0
      le_rfl] with ω hω
    rcases hω with hω | hω
    · exact hω
    · exact absurd (Complex.ofReal_eq_zero.1 (mem_singleton_iff.1 hω)) hv0.ne'
  obtain ⟨hv', Wv, ζv, ℓ, htrv, hcfv, hℓm, hae⟩ := hBR4a κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' v hv0.ne' hvR
  intro c θ hl h' htr
  have hc := eq_recenter_of_launch_zero hl
  subst hc
  have hh' : h' = hv' := funext fun ω => by
    rw [GW2aPiece.eq_flowField_of_isChartTransport (htr ω), GW2aPiece.eq_flowField_of_isChartTransport (htrv ω)]
  subst hh'
  have hν : condExpKernel P (pastSigma κ b jumps ⟨v, true, scheduleProgram 0 l⟩ E 0) ω₀ = P := by
    rw [GW1.pastSigma_zero_eq_bot]
    exact GW1.condExpKernel_bot_apply P ω₀
  have hS : contactSet κ b jumps ⟨v, true, scheduleProgram 0 l⟩ (fun j => E j ω₀) 0 = {(v : ℂ)} :=
    contactSet_zero _ _
  rw [hν, hS]
  exact ⟨Wv, ζv, ℓ, hcfv, hℓm, hae⟩

omit [StandardBorelSpace Ω] in
/-- A path tending to a finite point whose values are eventually nonzero has no inversion `−1/F` tending to `0`. -/
theorem not_tendsto_neg_inv_zero {F : ℝ → ℂ} {p : ℂ} (hF : Tendsto F (𝓝[>] 0) (𝓝 p))
    (hne : ∀ᶠ y in 𝓝[>] (0 : ℝ), F y ≠ 0) : ¬ Tendsto (fun y => -(F y)⁻¹) (𝓝[>] 0) (𝓝 0) := by
  intro h
  have h1 : Tendsto (fun y => F y * -(F y)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 (p * 0)) := hF.mul h
  have h2 : (fun _ : ℝ => (-1 : ℂ)) =ᶠ[𝓝[>] (0 : ℝ)] fun y => F y * -(F y)⁻¹ :=
    hne.mono fun y hy => by field_simp
  have h3 : Tendsto (fun y => F y * -(F y)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 (-1)) := tendsto_const_nhds.congr' h2
  have := tendsto_nhds_unique h1 h3
  norm_num at this

omit [StandardBorelSpace Ω] in
/-- **The original counterflow has no finite-time tip at its target `0`**: with a generating trace and a continuous
driver from `0`, the first tip time of `{0}` is `⊤` (the chart path has a finite limit at every finite time, so its
inversion cannot tend to `0`). -/
theorem firstTipTime_zero_eq_top {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace W ⊤ γ) (hWc : Continuous W)
    (hW0 : W 0 = 0) : firstTipTime infinitySourceChart W {0} = ⊤ := by
  unfold firstTipTime
  refine le_antisymm le_top (le_iInf₂ fun t ht => ?_)
  exfalso
  obtain ⟨z, hz, htip⟩ := ht
  rw [mem_singleton_iff] at hz
  subst hz
  have hlim := hγ.tendsto_fwdMapInv_mul_I hWc.continuousOn hW0 (t := t) ENNReal.coe_lt_top
  have hWc' : Continuous fun s : ℝ => W s.toNNReal := hWc.comp continuous_real_toNNReal
  have hW0' : (fun s : ℝ => W s.toNNReal) 0 = 0 := by simpa using hW0
  have hne : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ),
      QuantumZipper.fwdMapInv (fun s : ℝ => W s.toNNReal) t ((y : ℂ) * Complex.I) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hH := QuantumZipper.RS.fwdMapInv_mem_H hWc' hW0' (NNReal.coe_nonneg t)
      (w := (y : ℂ) * Complex.I) (by show 0 < ((y : ℂ) * Complex.I).im; simpa using hy)
    intro h0
    rw [h0] at hH
    exact (lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hH))
  exact not_tendsto_neg_inv_zero hlim hne htip

/-- **The equality datum at the first launch from the root `0`**: the original counterflow itself, with the identity
time change (the conditional law given the empty past is `P`, the field read in the root chart is `h`, the retained
prefix is `{0}`, which the original counterflow never meets at a finite time). Named input: Theorem 1.3 (for the
counterflow's generating trace). -/
theorem ae_hasLaunchPairEq_zero_root_zero (hT13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {l : List (ℝ × ℝ≥0)}
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω₀ : Ω) :
    HasLaunchPairEq κ b jumps P h W' ⟨0, true, scheduleProgram 0 l⟩ E 0 ω₀ := by
  intro c θ hl h' htr
  have hc := eq_recenter_of_launch_zero hl
  subst hc
  have hh' : h' = h := funext fun ω => by
    rw [GW2aPiece.eq_flowField_of_isChartTransport (htr ω), Sec7.Prop74B.flowField_zero_zero]
  subst hh'
  have hν : condExpKernel P (pastSigma κ b jumps ⟨0, true, scheduleProgram 0 l⟩ E 0) ω₀ = P := by
    rw [GW1.pastSigma_zero_eq_bot]
    exact GW1.condExpKernel_bot_apply P ω₀
  have hS : contactSet κ b jumps ⟨0, true, scheduleProgram 0 l⟩ (fun j => E j ω₀) 0 = {((0 : ℝ) : ℂ)} :=
    contactSet_zero _ _
  rw [hν, hS]
  have hcf' := hcf
  obtain ⟨b', J', h'', -, -, hfl⟩ := hcf'
  have hk : 0 < 16 / κ := by positivity
  refine ⟨W', ζ', fun _ => id, hcf, fun u => measurable_const, ?_⟩
  filter_upwards [GW2aSingle.ae_chosenTrace hT13 hk hfl, hζ', Supp8.GB6.ae_driver_zero_continuousOn hfl]
    with ω hγω hζω hdω
  rw [hζω] at hγω hdω
  have hWc : Continuous fun t => W' t ω := by
    have hc := hdω.2
    simp only [ENNReal.coe_lt_top, ofPred_true] at hc
    exact continuousOn_univ.1 hc
  refine ⟨hζω, continuous_id, strictMono_id, ?_, fun r z => tipAt_recenter_zero_trans⟩
  rw [Complex.ofReal_zero, firstTipTime_zero_eq_top hγω.1 hWc hdω.1, range_id]
  ext t
  simp

end GW2TipSystem

end Theorem14

end InteractingSLE
