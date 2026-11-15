/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkSideWord
import InteractingSLE.Spec.Sec5.CrossCondStagedMeanFlow

/-!
# Theorem 1.4's walk leaves: the own mean of a walk prefix

Packet PROVE-T14-WALKSIDE. Lemma GW1, proof (pp. 618–620: the conditional field after a stage is the GFF of the stop
word in the chart at the stop) and Lemma GW3, proof (p. 636: "On an ordinary selected subarc the incoming own germ is
…"). For a staged history `E` of a program `w` whose instruction `ℓ` is an angle-`θ` flow, and a time `τ`, the
**capped program** `capSpec w ℓ θ τ` run with the same drivers is a staged history (`isStagedHistory_capSpec`); the
landed single-stage law (`Exist.StagedLaw.stageLaw`, `post_stage`) gives, given its retained past `𝓗` before
`ℓ + 1`, the law of the field read in the record chart at `τ`: Gaussian with the data of the stop word. Read through
the chart of the capped run (the launch chart composed with the record chart) and the landed
`Sec5.CrossCond.Staged.ae_apply_eq_chartMean_of_chartLaw`, every local-set mean of a set retained with `𝓗` whose
complement contains the prefix chart's domain as a clopen part is the chart mean of the stop word there.

* `capEvent`: instruction `ℓ` launched and `τ` precedes the piece's lifetime; `measurableSet_capEvent`;
* `chart_trans_recChart`: the launch chart composed with the record chart is the capped run's chart;
* **`ae_capMean`**: the prefix's own mean.

The chart is taken through a version `c'` measurable in `𝓗` (hypotheses of the landed lemma). R48: this uses only the
landed staged law; it serves Theorem 1.4.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkSide

open Exist.StagedLaw Exist.Staged Restart LocalSets

/-! ### The capped launch event -/

section Event

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {w : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ℓ : ℕ} {θ : ℝ} {t : ℝ≥0∞}

omit [StandardBorelSpace Ω] in
/-- **The capped launch event**: instruction `ℓ` of `w` launched a piece and `τ` precedes its lifetime. -/
def capEvent (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (w : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ℓ : ℕ)
    (τ : ℝ≥0) : Set Ω :=
  {ω | (ExplState.run κ b jumps w (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none ∧ (τ : ℝ≥0∞) < (E ℓ ω).2}

/-- **The capped launch event is an event of the capped program's retained past** (the launch record and the
threshold flag of the retained datum). -/
theorem measurableSet_capEvent (hb : IsPiecewiseConstantBoundaryData b jumps) (hEm : ∀ j, Measurable (E j))
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (hℓ : ℓ ≤ w.2.2.length) (hwℓ : w.2.2[ℓ]? = some (Sum.inl (θ, t)))
    (τ : ℝ≥0) :
    MeasurableSet[pastSigma κ b jumps (capSpec w ℓ θ τ) E (ℓ + 1)] (capEvent κ b jumps w E ℓ τ) := by
  have hm : MeasurableSet (capEvent κ b jumps w E ℓ τ) :=
    (measurableSet_launch_self runMeasStatement hb (fun j _ => hEm j) (fun j _ => hreg j)).inter
      (measurableSet_lt measurable_const (measurable_snd.comp (hEm ℓ)))
  refine measurableSet_pastSigma_of_runs runMeasStatement hb (fun j _ => hEm j) (fun j _ => hreg j) hm
    fun ω ω' he hω => ?_
  have hrun := he (ℓ + 1) le_rfl
  have hl : (ExplState.run κ b jumps w (fun j => E j ω') (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
    rw [← launches_run_capSpec_succ (τ := (τ : ℝ≥0∞)) hℓ hwℓ, ← hrun, launches_run_capSpec_succ hℓ hwℓ]
    exact hω.1
  refine ⟨hl, ?_⟩
  have h1 := retained_run_capSpec_succ (fun j => E j ω) hℓ hwℓ hω.1 (τ : ℝ≥0∞)
  have h2 := retained_run_capSpec_succ (fun j => E j ω') hℓ hwℓ hl (τ : ℝ≥0∞)
  rw [hrun, h2] at h1
  have hflag := congrArg (fun r : (ℝ≥0 → ℝ) × ℝ≥0∞ × Bool => r.2.2) h1
  simp only [retOf, decide_eq_decide] at hflag
  exact not_le.1 fun h => not_le.2 hω.2 (hflag.1 h)

end Event

/-! ### The capped run's chart is the launch chart composed with the record chart -/

section Chart

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {w : ExplSpec} {ℓ : ℕ} {θ : ℝ} {t : ℝ≥0∞}

/-- **The launch chart composed with the record chart of the piece stopped at `τ` is the chart of the capped run.** -/
theorem chart_trans_recChart (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (hℓ : ℓ ≤ w.2.2.length)
    (hwℓ : w.2.2[ℓ]? = some (Sum.inl (θ, t))) {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps w D (ℓ + 1)).2.2.2.1 ℓ = some (c, θ')) (τ : ℝ≥0)
    (hreg : IsRegularDriver (D ℓ)) (hg : LocalExt.IsDrvGood (recHist (recOf (τ : ℝ≥0∞) (D ℓ)))) :
    (ExplState.run κ b jumps (capSpec w ℓ θ τ) D ℓ).2.2.2.2.1.trans (recChart (recOf (τ : ℝ≥0∞) (D ℓ))) =
      (ExplState.run κ b jumps (capSpec w ℓ θ τ) D (ℓ + 1)).2.2.2.2.1 := by
  rw [recChart_eq_loewner hreg hg, Sec5.CrossCond.Staged.trans_id_loewner, chart_run_capSpec_succ hℓ hwℓ D hl τ,
    run_capSpec_of_le hℓ D le_rfl]
  rfl

end Chart

/-! ### The prefix's own mean -/

section Mean

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {w : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ℓ : ℕ} {θ : ℝ} {t : ℝ≥0∞}

/-- **The own mean of a prefix** (Lemma GW1's stop word, read in the prefix chart). Let `E` be a staged history of `w`
with drivers regular at every sample, instruction `ℓ` of `w` an angle-`θ` flow, `τ` a time, and `𝓗` the retained past
of the capped program before `ℓ + 1`. Let `B` be a local set of the centred field, history-avoidance local for `𝓗`,
and `c'` a version of the capped run's chart measurable in `𝓗` (the hypotheses of the landed chart-mean lemma) whose
domain is a clopen part of `ℍ \ B` on the capped launch event. Then there is a word `β` such that every local-set
mean `g` of `B` satisfies, almost surely on the capped launch event, for every test function `φ` supported in the
domain of `c'`, `g(φ) = ∫ (𝔤 ∘ F − χ ℓ) φ − ∫ 𝔥₀ φ`, with `𝔤` the bounded harmonic mean of the stop word
`stopWord κ (β, θ, recOf τ (E ℓ))` and `F`, `ℓ` the forward map and lift of `c'`; and the record of the piece stopped at
`τ` is almost surely good there. -/
theorem ae_capMean (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hE : IsStagedHistory κ b jumps P h w E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (hℓ : ℓ < w.2.2.length) (hwℓ : w.2.2[ℓ]? = some (Sum.inl (θ, t)))
    (τ : ℝ≥0) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {B : Ω → Set ℂ}
    (hBm : Measurable[mΩ, hittingSigma] B) (hBloc : IsLocalSet B (WholeField.centredField h u₀) P)
    (hBmark : WholeField.IsHistoryAvoidanceLocal (pastSigma κ b jumps (capSpec w ℓ θ τ) E (ℓ + 1)) B
      (WholeField.centredField h u₀) P)
    {c' : Ω → Chart} (hc'c : ∀ ω, (c' ω).IsConformal) (hc'l : ∀ ω, ContinuousOn (c' ω).2.2 (c' ω).dom)
    (hdom : ∀ z, MeasurableSet[pastSigma κ b jumps (capSpec w ℓ θ τ) E (ℓ + 1)] {ω | z ∈ (c' ω).dom})
    (hfwd : ∀ z, Measurable[pastSigma κ b jumps (capSpec w ℓ θ τ) E (ℓ + 1)]
      ({ω | z ∈ (c' ω).dom}.indicator fun ω => (c' ω).1 z))
    (hCm : ∀ (z : ℂ) (ε : ℝ), MeasurableSet[pastSigma κ b jumps (capSpec w ℓ θ τ) E (ℓ + 1)]
      {ω | Metric.closedBall z ε ⊆ (c' ω).dom})
    (hliftm : ∀ z, Measurable[pastSigma κ b jumps (capSpec w ℓ θ τ) E (ℓ + 1)]
      ({ω | z ∈ (c' ω).dom}.indicator fun ω => (c' ω).2.2 z))
    (hc'eq : ∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps w E ℓ τ →
      c' ω = (ExplState.run κ b jumps (capSpec w ℓ θ τ) (fun j => E j ω) (ℓ + 1)).2.2.2.2.1)
    (hAD : ∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps w E ℓ τ →
      ((c' ω).dom : Set ℂ) ⊆ H \ B ω ∧ IsOpen ((H \ B ω) \ (c' ω).dom))
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean B (WholeField.centredField h u₀) P g) :
    ∃ β : Ω → BoundaryWord,
      (∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps w E ℓ τ → LocalExt.IsDrvGood (recHist (recOf (τ : ℝ≥0∞) (E ℓ ω)))) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      ω ∈ capEvent κ b jumps w E ℓ τ → tsupport φ ⊆ (c' ω).dom →
        g ω φ = (∫ z, ((stopWord κ (β ω, θ, recOf (τ : ℝ≥0∞) (E ℓ ω))).mean ((c' ω).1 z) -
          chiC κ * (c' ω).2.2 z) * φ z) - ∫ z, u₀ z * φ z := by
  set w' := capSpec w ℓ θ (τ : ℝ≥0∞) with hw'
  have hS : IsStagedHistory κ b jumps P h w' E := isStagedHistory_capSpec hb hE hreg hℓ hwℓ
  have hβA := GW1W.isStopLaw_stopWord.{u} hκ
  obtain ⟨β, Y, hβ, hY, hpath, hker⟩ := stageLaw (spec := w') (E := E) hβA runMeasStatement hκ hb hh ℓ
    (fun j _ => hS.1 j) (fun j _ => hreg j) (fun j _ => hS.2.2.2 j)
  have hpost := post_stage (spec := w') (E := E) (ℓ := ℓ) hβA runMeasStatement hκ hb hh
    (fun j _ => hS.1 j) (fun j _ => hreg j) (hS.2.2.2 ℓ) hβ hY hpath hker
  have hpm : Measurable (pastMap κ b jumps w' E (ℓ + 1)) :=
    measurable_pastMap runMeasStatement hb w' (fun j _ => hS.1 j) (fun j _ => hreg j) (ℓ + 1) le_rfl
  have hY' : Measurable fun ω => recField κ (pastMap κ b jumps w' E (ℓ + 1) ω (Fin.last ℓ)) (Y ω) :=
    Measurable.comp (g := fun q : RecData × DistOn upperHalfPlaneOpens => recField κ q.1 q.2)
      (f := fun ω => (pastMap κ b jumps w' E (ℓ + 1) ω (Fin.last ℓ), Y ω)) (measurable_recField κ)
      ((measurable_pi_iff.1 hpm (Fin.last ℓ)).prodMk hY)
  -- on the capped launch event: the capped launch, its record, its finite stop
  have hlaunch : ∀ ω, ω ∈ capEvent κ b jumps w E ℓ τ →
      (ExplState.run κ b jumps w' (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := fun ω hω => by
    rw [launches_run_capSpec_succ hℓ.le hwℓ]; exact hω.1
  have hrec : ∀ ω, ω ∈ capEvent κ b jumps w E ℓ τ →
      pastMap κ b jumps w' E (ℓ + 1) ω (Fin.last ℓ) = recOf (τ : ℝ≥0∞) (E ℓ ω) := fun ω hω => by
    change readRec ((ExplState.run κ b jumps w' (fun j => E j ω) (ℓ + 1)).2.2.1 ℓ) = _
    rw [retained_run_capSpec_succ (fun j => E j ω) hℓ.le hwℓ hω.1]
    rfl
  have hfin : ∀ ω, min (instrTime w' ℓ) (E ℓ ω).2 ≠ ⊤ := fun ω => by
    rw [instrTime_capSpec hℓ.le]
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  -- the field read in the chart
  have htr : ∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps w E ℓ τ →
      IsChartTransport (c' ω) 1 0 (chiC κ) (h ω)
        (recField κ (pastMap κ b jumps w' E (ℓ + 1) ω (Fin.last ℓ)) (Y ω)) := by
    filter_upwards [hpath, hpost.1, hc'eq] with ω hpω hgω hcω hω
    obtain ⟨hconf, hlift, hT⟩ := hpω (hlaunch ω hω)
    have hT2 := isChartTransport_recField κ (pastMap κ b jumps w' E (ℓ + 1) ω (Fin.last ℓ)) (Y ω)
    have htrans := IsChartTransport.trans hconf (isConformal_recChart _) hlift (continuousOn_recChart_lift _) hT hT2
    have hg' := hgω (hlaunch ω hω) (hfin ω)
    rw [instrTime_capSpec hℓ.le] at hg'
    obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hω.1
    have hchart : (ExplState.run κ b jumps w' (fun j => E j ω) ℓ).2.2.2.2.1.trans
        (recChart (pastMap κ b jumps w' E (ℓ + 1) ω (Fin.last ℓ))) = c' ω := by
      rw [hrec ω hω, chart_trans_recChart (fun j => E j ω) hℓ.le hwℓ hcθ τ (hreg ℓ ω) hg', ← hcω hω]
    rw [hchart] at htrans
    exact htrans
  -- the Gaussian chart law of the stop word
  have hlaw : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps w E ℓ τ →
      P[fun ω' => Complex.exp (Complex.I *
          (recField κ (pastMap κ b jumps w' E (ℓ + 1) ω' (Fin.last ℓ)) (Y ω') ψ : ℂ)) |
        pastSigma κ b jumps w' E (ℓ + 1)] ω = gaussCF (stopWord κ (β ω, θ, recOf (τ : ℝ≥0∞) (E ℓ ω))) ψ := by
    intro ψ
    filter_upwards [hpost.2 ψ] with ω h1 hω
    have h2 := h1 (hlaunch ω hω) (hfin ω)
    rw [instrAngle_capSpec hℓ.le, hrec ω hω] at h2
    exact h2
  refine ⟨β, ?_, fun φ => ?_⟩
  · filter_upwards [hpost.1] with ω hgω hω
    have hg' := hgω (hlaunch ω hω) (hfin ω)
    rwa [instrTime_capSpec hℓ.le] at hg'
  exact Sec5.CrossCond.Staged.ae_apply_eq_chartMean_of_chartLaw (hS.2.1 (ℓ + 1)) hc'c hdom hfwd hCm hliftm hc'l hh
    hu₀ hY' (measurableSet_capEvent hb hE.1 hreg hℓ.le hwℓ τ) htr
    (β := fun ω => stopWord κ (β ω, θ, recOf (τ : ℝ≥0∞) (E ℓ ω))) hlaw hBm hBloc hBmark hAD hg φ

end Mean

end InteractingSLE.Theorem14.WalkSide
