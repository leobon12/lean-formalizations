/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StripRevVisitReg
import InteractingSLE.Spec.Sec5.Lemma57

/-!
# Lemma 5.7's reverse visits for the physical source prefixes

Packet PROVE-REVVISIT. Theorem 1.2's leaf `hRefReverseVisit` is `Prop513Wire.StripReverseVisitLaw` for the physical
source prefixes `stripTree q E n` (`q = e^{πx₀}`): the angle-varying flow lines of the Figure 5.1 field with angles
`±π/2` (inside (5.3)) and rational switching and terminal times, pulled back to the chart `E`. This is Lemma 5.7
(specification p. 138) for these prefixes, in the form "reverse first-visit order on every closed prefix".

The proof of Lemma 5.7 has three inputs (Remark 5.8): (a) continuity of the explored path, (b) continuity of the
counterflow up to its target, and (c) "the first-exit conditional law in the remaining component": at each time `σ`,
given `η([0, σ])`, the counterflow mapped by the conformal map `ψ` of the remaining domain is the counterflow of the
mapped conditional field, with the boundary data of Figure 5.5 (right panel, general `ℓ`), and Lemma 4.5 makes it exit
at `η(σ)`. Then a density argument over rational times concludes.

**Proved here.** (a) and (b) for the actual objects (`StripRevVisitReg`; Lemma 5.6's availability, continuity,
simplicity, interiority and determination of the prefixes from the restricted Section 4.2 input `h44`); Lemma 4.5
for the conditional counterflow (Aux. lemma 7 at `16/κ` from the clearance form of Part A, through
`MarkovOther.ae_isFirstHitPoint_of_restart`); the height step "`−λ − θᵢχ ≤ −λ′` and `λ − θᵢχ ≥ λ′`" in the form of
`IsBoundedRestartDatum` (every angle list in `[−π/2, π/2]`); the time-`0` exit; and the density argument
(`StripRevVisitPath`).

**Named inputs** (two forms, the first implies the second):
* `StagedPrefixRestartStatement`: the conditional law (c) for these prefixes, in the kernel form of
  `Sec5.CounterflowSegmentRestartStatement` (the one-angle version), with the lower data of the mapped field bounded
  as in Figure 5.5 for general `ℓ` (`IsBoundedRestartDatum`);
* `StagedPrefixFirstHitStatement`: its consequence, the first exit at each positive rational time.

Both take, besides the setting, Lemma 5.6's facts as premises (`PrefixRegular`, availability, determination by the
field), which `h44` supplies here.

## Main results

* `PrefixRegular`, `prefixRegular_of_h44`, `exists_comap_tree` (Lemma 5.6's facts for the prefixes);
* `StagedPrefixRestartStatement`, `StagedPrefixFirstHitStatement` (named inputs);
* **`stagedPrefixFirstHitStatement_of_restart`**: the conditional law gives the first exits (Lemma 4.5 for `κ′`);
* **`stripReverseVisitLaw_of_stagedPrefixFirstHit`**, **`stripReverseVisitLaw_of_stagedPrefixRestart`**:
  `StripReverseVisitLaw (e^{πx₀}) P E γ` in the exact setting of the binder `hVisit` of
  `Wire.current_prop513_path_of_clearance_reverseVisit_candExp`, from `h44`, the clearance form of Part A and either
  named input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped Real NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.StripRevVisit

open QuantumZipper Sec4 Prop513Schedule Prop513TreeExtract Prop513Target Prop513Wire MarkovOther
open LQGMetric Restart Exist Exist.Staged Exist.StagedLaw

/-- **Lemma 5.6 for the actual prefixes** (the facts Lemma 5.7's proof starts from: "We first note that `η` is
almost surely continuous by Lemma 5.6"): almost surely every actual Q prefix is continuous and injective on its
closed horizon, starts at `0` and stays in `ℍ` at positive times. -/
def PrefixRegular {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (E : Schedule → ℕ → Ω → Driver) : Prop :=
  ∀ᵐ ω ∂P, ∀ n, ContinuousOn (driverTree E n ω) (Icc 0 (treeTime n)) ∧
    InjOn (driverTree E n ω) (Icc 0 (treeTime n)) ∧ driverTree E n ω 0 = 0 ∧
    ∀ t : ℝ, 0 < t → t ≤ treeTime n → driverTree E n ω t ∈ H

/-- **Named input: Lemma 5.7's first-exit conditional law for the physical source prefixes** (specification p. 138:
"Fix an `η` stopping time `σ` such that `η([0, σ])` almost surely does not contain `z₀`. We apply a conformal
transformation `ψ : 𝒮 ∖ η([0, σ]) → 𝒮` which fixes `±∞` and sends `η(σ)` to `0`; the boundary data for the GFF which
describes the evolution of `ψ(η′)` is as in the right panel of Figure 5.5 (with the obvious generalization from
`ℓ = 2` to other values of `ℓ`)"; Remark 5.8: "the first-exit conditional law in the remaining component").

Setting (that of `Prop513Wire.StripReverseVisitLaw` in the Theorem 1.2 wiring): `0 < κ < 4`; `h` is the strip field
with the Figure 5.1 data and the standing bounds; `γ` is the trace (chart `M_q`, `q = e^{πx₀}`) of the counterflow
`η′ = CF_d(h)` from `z₀ = x₀ + i`; `E` is the staged history of the field in chart `Q` for every Proposition 5.13
schedule (angles `±π/2`, rational switching and terminal times); every scheduled piece is available through its
requested time, and the prefixes are continuous, simple and interior (Lemma 5.6) and determined by `h` (Lemma 5.6's
determination clause for the extreme angles, which is how the source couples them with the counterflow). For every
prefix `n` and positive rational time `σ` below its horizon there are: a space `S` of chart paths `γS` with lifetimes
`U` (continuous up to their lifetimes, measurable coordinates), a measurable event `M`, a measurable chart datum
`β = (Q, c)`, a measurable restart variable `X` and a Markov kernel `K` that is the conditional law of `X` given `β` on
`M`, such that almost every datum is a bounded restart datum (the mapped lower data are `≤ −λ′` left of the tip image
and `≥ λ′` right of it: Figure 5.5 for general `ℓ`, angles in `[−π/2, π/2]`) under which the chart path has the
flow-line trace law for `κ′ = 16/κ` (Theorem 2.4's converse); and almost surely `ω ∈ M` and the completed
counterflow is the chart path in the restart chart of `ℍ ∖ η([0, σ])` with tip `η(σ)` (`η = stripTree q E n`, the
physical prefix in the chart `E`). -/
def StagedPrefixRestartStatement : Prop :=
  ∀ κ x₀ a b a' b' : ℝ, ∀ (hκ : 0 < κ), κ < 4 → ∀ (hb : IsFig51Bounds κ a b a' b'),
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens),
    IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀} →
  ∀ (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (γ : Ω → ℝ≥0 → ℂ),
    IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ →
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)) →
  ∀ E : Schedule → ℕ → Ω → Driver,
    (∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (fun ω => targetField κ (Real.exp (π * x₀)) (Real.exp_pos _) (h ω)) (scheduleSpec s) (E s)) →
    (∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s)) →
    (∀ᵐ ω ∂P, ∀ s, scheduleAvailable E s ω ∧ scheduleAvailableClosed E s ω) →
    PrefixRegular P E →
    (∃ ξ : ℕ → Ω → ℝ → ℂ, (∀ n t, Measurable[MeasurableSpace.comap h inferInstance] fun ω => ξ n ω t) ∧
      ∀ᵐ ω ∂P, ∀ n, EqOn (ξ n ω) (driverTree E n ω) (Icc 0 (treeTime n))) →
  ∀ (n : ℕ) (σ : ℚ), 0 < (σ : ℝ) → (σ : ℝ) < treeTime n →
    ∃ (S : Type) (_ : MeasurableSpace S) (γS : S → ℝ≥0 → ℂ) (U : S → ℝ≥0∞) (M : Set Ω)
      (β : Ω → ℝ × BoundaryWord) (X : Ω → S) (K : Kernel (ℝ × BoundaryWord) S),
      (∀ t, Measurable fun s => γS s t) ∧ Measurable U ∧
      (∀ s, ContinuousOn (γS s) {u | (u : ℝ≥0∞) ≤ U s}) ∧
      MeasurableSet M ∧ Measurable β ∧ Measurable X ∧ IsMarkovKernel K ∧
      (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K ∧
      (∀ᵐ d ∂(P.restrict M).map β,
        IsBoundedRestartDatum κ 0 a' b' d ∧ IsFlowLineTraceLaw (16 / κ) d.2 (K d) γS U) ∧
      ∀ᵐ ω ∂P, ω ∈ M ∧ IsCounterflowChartContinuation (stripTree (Real.exp (π * x₀)) E n ω '' Icc 0 (σ : ℝ))
          (stripTree (Real.exp (π * x₀)) E n ω σ) (stripCounterflowPath (Real.exp (π * x₀)) (γ ω))
          (β ω).1 (γS (X ω)) (U (X ω))

/-- **The determination of the physical prefixes by the field** (Lemma 5.6's determination clause for the extreme
angles), from the restricted Section 4.2 input: a family `ξ`, measurable for `σ(h)`, equal to every actual Q prefix
on its closed horizon almost surely. -/
theorem exists_comap_tree (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{u})
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    {E : Schedule → ℕ → Ω → Driver}
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (fun ω => targetField κ (Real.exp (π * x₀)) (Real.exp_pos _) (h ω)) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s)) :
    ∃ ξ : ℕ → Ω → ℝ → ℂ, (∀ n t, Measurable[MeasurableSpace.comap h inferInstance] fun ω => ξ n ω t) ∧
      ∀ᵐ ω ∂P, ∀ n, EqOn (ξ n ω) (driverTree E n ω) (Icc 0 (treeTime n)) := by
  let c := sourceWord (x₀ := x₀) hκ hb
  have hc : ExtremeHeights κ c := sourceWord_extreme hκ hb
  have hhQ := sourceWord_gff hκ hb hG
  have hh𝒢 : Measurable[MeasurableSpace.comap h inferInstance] h := measurable_iff_comap_le.2 le_rfl
  have hmQ := (measurable_targetField κ (Real.exp (π * x₀)) (Real.exp_pos _)).comp hh𝒢
  obtain ⟨ξ, hξm, -, -, he⟩ := exists_measurable_extreme_tree_of_stagedPiecesRegular
    h44 hκ hκ4 c hc hhQ hE hR hmQ
  exact ⟨ξ, hξm, ae_driverTree_eq (prefixTraceRegularity_of_stagedPiecesRegular h44 hκ hκ4 c hc hhQ hE hR) he⟩

/-- **Lemma 5.6 for the actual prefixes**, from the restricted Section 4.2 input. -/
theorem prefixRegular_of_h44 (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{u})
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    {E : Schedule → ℕ → Ω → Driver}
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (fun ω => targetField κ (Real.exp (π * x₀)) (Real.exp_pos _) (h ω)) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s)) :
    PrefixRegular P E := by
  have hc := sourceWord_extreme (x₀ := x₀) hκ hb
  have hhQ := sourceWord_gff hκ hb hG
  filter_upwards [ae_driverTree_regular h44 hκ hκ4 _ hc hhQ hE hR,
    ae_driverTree_interior h44 hκ hκ4 _ hc hhQ hE hR] with ω hreg hint n
  exact ⟨(hreg n).1, (hreg n).2, (hint n).1, (hint n).2⟩

/-- **Named input (per-time form): Lemma 5.7's first exit for the physical source prefixes** (specification p. 138:
"This implies that `η′` almost surely exits `𝒮 ∖ η([0, σ])` at `η(σ)`"). Setting and premises of
`StagedPrefixRestartStatement`. For every prefix `n` and positive rational time `σ` below its horizon, almost surely
the completed counterflow first hits `∂_L𝒮 ∪ η([0, σ])` at `η(σ)` (`η = stripTree q E n`, `q = e^{πx₀}`). It follows
from `StagedPrefixRestartStatement` and Lemma 4.5 for `κ′` (`stagedPrefixFirstHitStatement_of_restart`); a direct
proof (as PROVE-CFRESTART5's route for the one-angle Lemma 4.7 in the chart `Q`) may also supply it. -/
def StagedPrefixFirstHitStatement : Prop :=
  ∀ κ x₀ a b a' b' : ℝ, ∀ (hκ : 0 < κ), κ < 4 → ∀ (hb : IsFig51Bounds κ a b a' b'),
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens),
    IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀} →
  ∀ (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (γ : Ω → ℝ≥0 → ℂ),
    IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ →
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)) →
  ∀ E : Schedule → ℕ → Ω → Driver,
    (∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (fun ω => targetField κ (Real.exp (π * x₀)) (Real.exp_pos _) (h ω)) (scheduleSpec s) (E s)) →
    (∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s)) →
    (∀ᵐ ω ∂P, ∀ s, scheduleAvailable E s ω ∧ scheduleAvailableClosed E s ω) →
    PrefixRegular P E →
    (∃ ξ : ℕ → Ω → ℝ → ℂ, (∀ n t, Measurable[MeasurableSpace.comap h inferInstance] fun ω => ξ n ω t) ∧
      ∀ᵐ ω ∂P, ∀ n, EqOn (ξ n ω) (driverTree E n ω) (Icc 0 (treeTime n))) →
  ∀ (n : ℕ) (σ : ℚ), 0 < (σ : ℝ) → (σ : ℝ) < treeTime n →
    ∀ᵐ ω ∂P, IsFirstHitPoint (stripCounterflowPath (Real.exp (π * x₀)) (γ ω)) 1
      (lowerLineH ∪ stripTree (Real.exp (π * x₀)) E n ω '' Icc 0 (σ : ℝ))
      (stripTree (Real.exp (π * x₀)) E n ω σ)

/-- **The first exit after a physical prefix, from the conditional law** (Lemma 5.7's proof: "Lemma 4.5 (see also
Figure 4.4) thus implies that `ψ(η′)` does not hit `∂_L𝒮 ∖ {0}` and exits `𝒮` at `0`. This implies that `η′` almost
surely exits `𝒮 ∖ η([0, σ])` at `η(σ)`"): the named conditional law and Lemma 4.5 for `κ′ = 16/κ` (Aux. lemma 7 from
the clearance form of Part A, with the height step `isRestartTargetDatum_of_isBoundedRestartDatum`) give the
per-time first exit. -/
theorem stagedPrefixFirstHitStatement_of_restart (hA : PartAInputsSixteenDivOfClearance)
    (hRS : StagedPrefixRestartStatement.{u}) : StagedPrefixFirstHitStatement.{u} := by
  intro κ x₀ a b a' b' hκ hκ4 hb Ω _ _ P _ h hG W ζ γ hcf htr E hE hR hav hreg hdet n σ hσ hσT
  obtain ⟨S, mS, γS, U, M, β, X, K, hγm, hUm, hγc, hM, hβ, hX, hK, hlaw, hdat, hpath⟩ :=
    hRS κ x₀ a b a' b' hκ hκ4 hb P h hG W ζ γ hcf htr E hE hR hav hreg hdet n σ hσ hσT
  have hκ' : 0 < 16 / κ := by positivity
  have h7 : Aux7Statement.{0} (16 / κ) := aux7Statement_sixteen_div_of_partA_of_clearance hA hκ hκ4
  have hdat' : ∀ᵐ d ∂(P.restrict M).map β,
      IsRestartTargetDatum (16 / κ) d ∧ IsFlowLineTraceLaw (16 / κ) d.2 (K d) γS U :=
    hdat.mono fun d hd => ⟨isRestartTargetDatum_of_isBoundedRestartDatum hκ hκ4 hb hd.1, hd.2⟩
  have hξ : ∀ᵐ ω ∂P, ContinuousOn (stripCounterflowPath (Real.exp (π * x₀)) (γ ω)) (Icc 0 1) :=
    (ae_counterflow_regular hA hκ hκ4 hb hG hcf htr).mono fun _ hω => hω.2.2
  have hz : ∀ ω, stripTree (Real.exp (π * x₀)) E n ω σ ∈
      stripTree (Real.exp (π * x₀)) E n ω '' Icc 0 (σ : ℝ) := fun ω => ⟨σ, ⟨hσ.le, le_rfl⟩, rfl⟩
  have hfirst := ae_isFirstHitPoint_of_restart hκ' h7 hγm hUm hγc hM hβ hX hlaw hdat' hξ hz
    (A := fun ω => stripTree (Real.exp (π * x₀)) E n ω '' Icc 0 (σ : ℝ))
    (z := fun ω => stripTree (Real.exp (π * x₀)) E n ω σ) (G := fun _ => True) (hpath.mono fun _ hω _ => hω)
  exact hfirst.mono fun _ hω => hω trivial

/-- **`hRefReverseVisit` from the per-time first exit** (Lemma 5.7's density step: "By choosing a dense collection
of stopping times (e.g., the positive rationals) and using the continuity of `η′` and `η` we conclude that the range
of `η′` contains `η`. Moreover, the proof clearly also implies that the points of `η` are hit by `η′` in reverse
chronological order"): `Prop513Wire.StripReverseVisitLaw` in the exact setting of the binder `hVisit` of
`Wire.current_prop513_path_of_clearance_reverseVisit_candExp`, from the restricted Section 4.2 input `h44` (Lemma 5.6
for the prefixes: availability, continuity, simplicity, interiority, determination), the clearance form of Part A
(the counterflow's continuity up to its target and interiority) and `StagedPrefixFirstHitStatement`. -/
theorem stripReverseVisitLaw_of_stagedPrefixFirstHit (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{u})
    (hA : PartAInputsSixteenDivOfClearance) (hFH : StagedPrefixFirstHitStatement.{u})
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    {E : Schedule → ℕ → Ω → Driver}
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (fun ω => targetField κ (Real.exp (π * x₀)) (Real.exp_pos _) (h ω)) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s)) :
    StripReverseVisitLaw (Real.exp (π * x₀)) P E γ := by
  set q := Real.exp (π * x₀) with hqdef
  have hq : 0 < q := Real.exp_pos _
  have hc := sourceWord_extreme (x₀ := x₀) hκ hb
  have hhQ := sourceWord_gff hκ hb hG
  have hhit : ∀ᵐ ω ∂P, ∀ n, ∀ σ : ℚ, 0 < (σ : ℝ) → (σ : ℝ) < treeTime n →
      IsFirstHitPoint (stripCounterflowPath q (γ ω)) 1 (lowerLineH ∪ stripTree q E n ω '' Icc 0 (σ : ℝ))
        (stripTree q E n ω σ) := by
    refine ae_all_iff.2 fun n => ae_all_iff.2 fun σ => ?_
    by_cases hσ : 0 < (σ : ℝ) ∧ (σ : ℝ) < treeTime n
    · filter_upwards [hFH κ x₀ a b a' b' hκ hκ4 hb P h hG W ζ γ hcf htr E hE hR
        (ae_all_available_of_stagedPiecesRegular h44 hκ hκ4 _ hc hhQ hE hR)
        (prefixRegular_of_h44 h44 hκ hκ4 hb hG hE hR) (exists_comap_tree h44 hκ hκ4 hb hG hE hR)
        n σ hσ.1 hσ.2] with ω hω _ _ using hω
    · exact Eventually.of_forall fun ω h1 h2 => absurd ⟨h1, h2⟩ hσ
  filter_upwards [hhit, ae_counterflow_regular hA hκ hκ4 hb hG hcf htr,
    ae_stripTree_regular h44 hκ hκ4 hq _ hc hhQ hE hR] with ω hω ⟨hγ0, hγH, hγc⟩ hreg n s t hs hst ht
  obtain ⟨hcont, hinj, h0, -⟩ := hreg n
  exact reverseVisit_of_firstHit hq (treeTime_pos n) hγc hγ0 hγH hcont (hinj.mono Ico_subset_Icc_self) h0
    (hω n) s t hs hst ht

/-- **`hRefReverseVisit` from the conditional law**: `Prop513Wire.StripReverseVisitLaw` in the setting of the binder
`hVisit` of `Wire.current_prop513_path_of_clearance_reverseVisit_candExp`, from `h44`, the clearance form of Part A and
the named conditional law `StagedPrefixRestartStatement` (Lemma 5.7's proof, specification p. 138). -/
theorem stripReverseVisitLaw_of_stagedPrefixRestart (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{u})
    (hA : PartAInputsSixteenDivOfClearance) (hRS : StagedPrefixRestartStatement.{u})
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    {E : Schedule → ℕ → Ω → Driver}
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (fun ω => targetField κ (Real.exp (π * x₀)) (Real.exp_pos _) (h ω)) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s)) :
    StripReverseVisitLaw (Real.exp (π * x₀)) P E γ :=
  stripReverseVisitLaw_of_stagedPrefixFirstHit h44 hA (stagedPrefixFirstHitStatement_of_restart hA hRS)
    hκ hκ4 hb hG hcf htr hE hR

end InteractingSLE.Sec5.StripRevVisit
