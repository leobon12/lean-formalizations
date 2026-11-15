/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2LaterInt
import InteractingSLE.Spec.Supplement.KernelTower
import InteractingSLE.Spec.Sec7.Prop74BShift

/-!
# GW2a's later pieces by GW1's induction: the conditional pair propagated launch by launch

Packet PROVE-T14-BR6. Lemma GW1's proof (supplement pp. 618–620) carries the induction datum 2 — the complete
conditional counterflow pair targeted at the current incoming tip — from one launch to the next: "Apply GB6, within the
independently established complete conditional pair in item 2, to every available interior-tip prefix of `β_j`";
"auxiliary stage encodings may be forgotten by the tower property". GW2a (p. 623) uses the same induction for
interior angle switches.

The datum at a launch (`HasLaunchPair`) is a statement about the conditional law at one sample; it is not a measurable
event of the sample, so the induction cannot pass it to `P` launch by launch (a non-measurable property that holds
almost surely under almost every conditional law need not hold `P`-almost surely; ruling R51). The induction is
therefore run on the kernels: `KernelTower.ae_ae_of_chain` carries only the measurable containment event of the target
piece down the chain of retained pasts, with the tower property at each step.

* `HasLaunchPairInt`: the datum at launch `j`, required only when the first `j` pieces were successful and their
  switching tips are interior (GB6's `p ∈ D`).
* `hasLaunchPair_zero_root_zero`, `ae_hasLaunchPair_zero_root_arc`: the datum at the first launch — the original
  counterflow itself from the root `0`, Corollary BR4a's pair from a root `v` of the first low right arc.
* **`GB6PastStepStatement`** (named input): GW1's inductive step — GB6 applied in the conditional world of the
  retained past, to the next piece, together with the tower property of the retained-past kernels.
* **`ae_later_piece_subset_of_step`**: the piece launched at `k ≥ 1` lies in the completed counterflow range almost
  surely, when the switching tips are almost surely interior.
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

namespace GW2Later

open CounterflowRange GW2Schedule GW2aMulti GW2Sched

/-- GW1's induction datum 2 at launch `j`, required when the first `j` pieces were successful (own times `Δ`) and their
switching tips are interior. -/
def HasLaunchPairInt (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ)
    (spec : ExplSpec) (Δ : ℕ → ℝ≥0∞) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (j : ℕ) (ω : Ω) : Prop :=
  AllSucc Δ (fun i => E i ω) j → SwitchTipsInterior spec (fun i => E i ω) j →
    HasLaunchPair κ b jumps P h W' spec E j ω

/-- **Named input: GW1's inductive step — GB6 in the conditional world of the retained past** (supplement pp. 618–620,
623). For a GW2 schedule from `0` or from a root of the first low right arc and a staged history with regular pieces:
at almost every sample `ω₀` at which the conditional counterflow pair is available at launch `j`, almost every sample
of the conditional law given the retained past before `j` has the conditional counterflow pair at launch `j + 1` (when
the first `j + 1` pieces were successful with interior switching tips). This is GB6's main assertion for the piece
launched at `j` in the conditional world given the retained past ("Conditional on the marked prefix, the portion of `η`
before its first contact with `α[0, σ]`, in the chart of `U` taking `(y, p)` to `(0, ∞)`, is the complete canonical
counterflow of the conditional component field. Its relative lifetime is infinite."), with the regular conditional
law given the longer retained past in place of the conditional law given the piece in that world (GW1, p. 620:
"auxiliary stage encodings may be forgotten by the tower property"). -/
def GB6PastStepStatement : Prop :=
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
        ∀ j : ℕ, ∀ᵐ ω₀ ∂P,
          HasLaunchPairInt κ b jumps P h W' ⟨x, true, scheduleProgram 0 l⟩ (schedDelta 0 l)
              (E ⟨x, true, scheduleProgram 0 l⟩) j ω₀ →
            ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps ⟨x, true, scheduleProgram 0 l⟩
                (E ⟨x, true, scheduleProgram 0 l⟩) j) ω₀),
              HasLaunchPairInt κ b jumps P h W' ⟨x, true, scheduleProgram 0 l⟩ (schedDelta 0 l)
                (E ⟨x, true, scheduleProgram 0 l⟩) (j + 1) ω

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- Reading through the root-`0` chart and the inversion is reading through the inversion. -/
theorem tipAt_recenter_zero_trans {W : ℝ≥0 → ℝ} {r : ℝ≥0} {z : ℂ} :
    ((Chart.id.recenter 0).trans infinitySourceChart).tipAt W r z ↔ infinitySourceChart.tipAt W r z := by
  unfold Chart.tipAt
  have e : ((Chart.id.recenter 0).trans infinitySourceChart).2.1 = infinitySourceChart.2.1 := by
    funext w
    simp [Chart.trans, Chart.recenter, Chart.id]
  rw [e]

omit [StandardBorelSpace Ω] in
/-- The first launch of a GW2 schedule is in the root chart. -/
theorem eq_recenter_of_launch_zero {x : ℝ} {l : List (ℝ × ℝ≥0)} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {c : Chart} {θ : ℝ}
    (hl : (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩ D (0 + 1)).2.2.2.1 0 = some (c, θ)) :
    c = Chart.id.recenter x := by
  have hk : 0 < (scheduleProgram 0 l).length := by
    by_contra h0
    rw [launches_run_succ_of_length_le κ b jumps _ D (not_lt.1 h0)] at hl
    exact absurd hl (by simp)
  have h1 := (launches_run_gw2 (κ := κ) (b := b) (jumps := jumps) (spec := ⟨x, true, scheduleProgram 0 l⟩) rfl
    (isFlowProg_scheduleProgram 0 l) (schedDelta_ne_top 0 l) D hk).1 (allSucc_zero _ D)
  rw [h1] at hl
  simp only [Option.some.injEq, Prod.mk.injEq] at hl
  rw [← hl.1]
  rfl

/-- **The datum at the first launch from the root `0`**: the original counterflow itself (the conditional law given the
empty past is `P`, and the field read in the root chart is `h`). -/
theorem hasLaunchPair_zero_root_zero {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {l : List (ℝ × ℝ≥0)} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω₀ : Ω) :
    HasLaunchPair κ b jumps P h W' ⟨0, true, scheduleProgram 0 l⟩ E 0 ω₀ := by
  intro c θ hl h' htr
  have hc := eq_recenter_of_launch_zero hl
  subst hc
  have hh' : h' = h := funext fun ω => by
    rw [GW2aPiece.eq_flowField_of_isChartTransport (htr ω), Sec7.Prop74B.flowField_zero_zero]
  subst hh'
  have hν : condExpKernel P (pastSigma κ b jumps ⟨0, true, scheduleProgram 0 l⟩ E 0) ω₀ = P := by
    rw [GW1.pastSigma_zero_eq_bot]
    exact GW1.condExpKernel_bot_apply P ω₀
  rw [hν]
  refine ⟨W', ζ', hcf, hζ', Eventually.of_forall fun ω r z hz => ?_⟩
  have h1 : infinitySourceChart.tipAt (fun s => W' s ω) r z := tipAt_recenter_zero_trans.1 hz
  have h2 : z ∈ infinitySourceChart.tipSet (fun s => W' s ω) ⊤ := by
    rw [Chart.tipSet_eq_tipAt]
    exact ⟨r, le_top, h1⟩
  exact mem_union_left _ h2

/-- **The datum at the first launch from a root `v` of the first low right arc**: Corollary BR4a's pair targeted at `v`
(GW2, p. 621: "BR4a gives the full conditional pair targeted at `v`"). Named inputs: BR4a, Theorem 1.3 (and at `0`, for
GW0). -/
theorem ae_hasLaunchPair_zero_root_arc (hBR4a : BR4a.BR4aStatement.{u}) (hT13 : Exist.Theorem13Statement.{u})
    (hT13₀ : Exist.Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {v : ℝ}
    (hv : v ∈ lowerArcRoots κ b jumps) {l : List (ℝ × ℝ≥0)} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω₀ : Ω) :
    HasLaunchPair κ b jumps P h W' ⟨v, true, scheduleProgram 0 l⟩ E 0 ω₀ := by
  have hGW0 : GW0.GW0ForwardStatement.{u} := BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀
  have hv0 := pos_of_mem_lowerArcRoots hv
  have hvR : ∀ᵐ ω ∂P, (v : ℂ) ∈ infinitySourceChart.tipSet (fun t => W' t ω) ⊤ := by
    filter_upwards [GW2Cone.ae_mem_counterflowCompletedRange_of_theorem13 hT13 hGW0 hκ hκ4 hb hh hcf hζ' hv hv0
      le_rfl] with ω hω
    rcases hω with hω | hω
    · exact hω
    · exact absurd (Complex.ofReal_eq_zero.1 (mem_singleton_iff.1 hω)) hv0.ne'
  obtain ⟨hv', Wv, ζv, ℓ, htrv, hcfv, -, hae⟩ := hBR4a κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' v hv0.ne' hvR
  intro c θ hl h' htr
  have hc := eq_recenter_of_launch_zero hl
  subst hc
  have hh' : h' = hv' := funext fun ω => by
    rw [GW2aPiece.eq_flowField_of_isChartTransport (htr ω), GW2aPiece.eq_flowField_of_isChartTransport (htrv ω)]
  subst hh'
  have hν : condExpKernel P (pastSigma κ b jumps ⟨v, true, scheduleProgram 0 l⟩ E 0) ω₀ = P := by
    rw [GW1.pastSigma_zero_eq_bot]
    exact GW1.condExpKernel_bot_apply P ω₀
  rw [hν]
  refine ⟨Wv, ζv, hcfv, hae.mono fun ω hω => hω.1, hae.mono fun ω hω r z hz => ?_⟩
  have h2 : z ∈ infinitySourceChart.tipSet (fun s => W' s ω) ⊤ := by
    rw [Chart.tipSet_eq_tipAt]
    exact ⟨ℓ ω r, le_top, (hω.2.2.2.2 r z).1 hz⟩
  exact mem_union_left _ h2

/-- **GW2a's later pieces by GW1's induction.** For a GW2 schedule from `0` or a root `v` of the first low right arc, a
staged history with regular pieces (ruling R51), and `k ≥ 1`: if almost surely the switching tips before `k` are
interior whenever the first `k` pieces were successful, the piece launched at `k` lies in the completed counterflow
range almost surely. The conditional pair is started at the first launch (`hasLaunchPair_zero_root_zero`,
`ae_hasLaunchPair_zero_root_arc`), propagated by GW1's inductive step (named input `GB6PastStepStatement`), and only the
measurable containment event of the target piece (`exists_measurable_piece_event`) is carried down the chain of
retained pasts by the tower property (`KernelTower.ae_ae_of_chain`). Named inputs: `GB6PastStepStatement`, Corollary
BR4a (boundary roots), GB6's restart law, Theorem 1.3 (also at `0`, for GW0). -/
theorem ae_later_piece_subset_of_step (hStep : GB6PastStepStatement.{u}) (hBR4a : BR4a.BR4aStatement.{u})
    (hGB6 : Supp8.GB6.GB6RestartStatement.{u}) (hT13 : Exist.Theorem13Statement.{u})
    (hT13₀ : Exist.Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {x : ℝ} (hx : x = 0 ∨ x ∈ lowerArcRoots κ b jumps) {l : List (ℝ × ℝ≥0)}
    (hl : ∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (hlt : l.Pairwise (fun p q => p.2 < q.2))
    {k : ℕ} (hint : ∀ᵐ ω ∂P, AllSucc (schedDelta 0 l) (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k →
      SwitchTipsInterior ⟨x, true, scheduleProgram 0 l⟩ (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k) :
    ∀ᵐ ω ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩
        (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) (k + 1)).2.2.2.1 k = some (c, θ) →
      c.tipSet (stoppedDriver ⟨x, true, scheduleProgram 0 l⟩ (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k)
          (pieceStop ⟨x, true, scheduleProgram 0 l⟩ (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k) ⊆
        counterflowCompletedRange (fun t => W' t ω) := by
  set spec : ExplSpec := ⟨x, true, scheduleProgram 0 l⟩ with hspec
  have hBC : IsBoundaryContinuedProgram spec.2.2 := isBoundaryContinuedProgram_scheduleProgram hl 0
  have hGW0 : GW0.GW0ForwardStatement.{u} := BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀
  have hS := hE spec hBC
  by_cases hk : k < spec.2.2.length
  · have hprog : IsFlowProg spec.2.2 (schedAngle l) (schedDelta 0 l) := isFlowProg_scheduleProgram 0 l
    have hklen : k < l.length := by
      have := length_scheduleProgram 0 l
      simp only [hspec] at hk
      omega
    obtain ⟨A, hAm, hker, hpath⟩ := exists_measurable_piece_event hGB6 hGW0 hT13 hκ hκ4 hcf hζ' (spec := spec) rfl
      hprog (schedDelta_ne_top 0 l) hS (hER spec hBC) hk (schedAngle_mem_Icc hl hklen)
    set L : Set Ω := {ω | AllSucc (schedDelta 0 l) (fun j => E spec j ω) k} with hLdef
    have hL𝒢 : MeasurableSet[pastSigma κ b jumps spec (E spec) k] L :=
      measurableSet_allSucc rfl hprog (schedDelta_ne_top 0 l) (E spec) hk.le
    have hA'm : MeasurableSet (Lᶜ ∪ A) := ((hS.2.1 k) _ hL𝒢).compl.union hAm
    have htop : ∀ᵐ ω ∂P, HasLaunchPairInt κ b jumps P h W' spec (schedDelta 0 l) (E spec) k ω →
        ∀ᵐ y ∂(condExpKernel P (pastSigma κ b jumps spec (E spec) k) ω), y ∈ Lᶜ ∪ A := by
      filter_upwards [hker, hint, Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) (hS.2.1 k) hL𝒢.compl]
        with ω hk1 hi hLc hD
      by_cases hωL : ω ∈ L
      · filter_upwards [hk1 hωL (hD hωL (hi hωL))] with y hy using Or.inr hy
      · filter_upwards [hLc hωL] with y hy using Or.inl hy
    have hstep : ∀ j < k, ∀ᵐ ω ∂P, HasLaunchPairInt κ b jumps P h W' spec (schedDelta 0 l) (E spec) j ω →
        ∀ᵐ y ∂(condExpKernel P (pastSigma κ b jumps spec (E spec) j) ω),
          HasLaunchPairInt κ b jumps P h W' spec (schedDelta 0 l) (E spec) (j + 1) y := fun j _ =>
      hStep κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER x hx l hl hlt j
    have hchain := KernelTower.ae_ae_of_chain (P := P) (𝒢 := fun j => pastSigma κ b jumps spec (E spec) j)
      (fun j => Exist.StagedLaw.pastSigma_mono (κ := κ) (b := b) (jumps := jumps) spec (E spec) (Nat.le_succ j))
      (fun j => hS.2.1 j) (D := fun j ω => HasLaunchPairInt κ b jumps P h W' spec (schedDelta 0 l) (E spec) j ω)
      hA'm k htop hstep 0 (Nat.zero_le k)
    have hD0 : ∀ ω, HasLaunchPairInt κ b jumps P h W' spec (schedDelta 0 l) (E spec) 0 ω := by
      intro ω _ _
      rcases hx with rfl | hv
      · exact hasLaunchPair_zero_root_zero hcf hζ' (E spec) ω
      · exact ae_hasLaunchPair_zero_root_arc hBR4a hT13 hT13₀ hκ hκ4 hb hh hcf hζ' hv (E spec) ω
    have hν : ∀ ω, condExpKernel P (pastSigma κ b jumps spec (E spec) 0) ω = P := fun ω => by
      rw [GW1.pastSigma_zero_eq_bot]
      exact GW1.condExpKernel_bot_apply P ω
    have hP : ∀ᵐ y ∂P, y ∈ Lᶜ ∪ A := by
      obtain ⟨ω, hω⟩ := hchain.exists
      have h1 := hω (hD0 ω)
      rwa [hν] at h1
    filter_upwards [hP] with ω hω c θ hlk
    have hs : ω ∈ L := by
      by_contra hns
      rw [(launches_run_gw2 (κ := κ) (b := b) (jumps := jumps) (spec := spec) rfl hprog (schedDelta_ne_top 0 l)
        (fun j => E spec j ω) hk).2 hns] at hlk
      exact absurd hlk (by simp)
    exact hpath ω (hω.resolve_left (not_not.2 hs)) c θ hlk
  · refine Eventually.of_forall fun ω c θ hlk => ?_
    rw [launches_run_succ_of_length_le κ b jumps spec _ (not_lt.1 hk)] at hlk
    exact absurd hlk (by simp)

/-- **GW2's schedule containment by GW1's induction** (both roots): the physical set of a GW2 schedule with almost
surely interior switching tips lies in the completed counterflow range. Named inputs: `GB6PastStepStatement`,
Corollary BR4a, GB6's restart law, Theorem 1.3. -/
theorem ae_physSet_subset_of_step (hStep : GB6PastStepStatement.{u}) (hBR4a : BR4a.BR4aStatement.{u})
    (hGB6 : Supp8.GB6.GB6RestartStatement.{u}) (hT13 : Exist.Theorem13Statement.{u})
    (hT13₀ : Exist.Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {x : ℝ} (hx : x = 0 ∨ x ∈ lowerArcRoots κ b jumps) {l : List (ℝ × ℝ≥0)}
    (hl : ∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (hlt : l.Pairwise (fun p q => p.2 < q.2))
    (hint : ∀ k, ∀ᵐ ω ∂P, AllSucc (schedDelta 0 l) (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k →
      SwitchTipsInterior ⟨x, true, scheduleProgram 0 l⟩ (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k) :
    ∀ᵐ ω ∂P, ExplState.physSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩
        (fun k => E ⟨x, true, scheduleProgram 0 l⟩ k ω) ⊆ counterflowCompletedRange (fun t => W' t ω) := by
  have hGW0 : GW0.GW0ForwardStatement.{u} := BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀
  have hS := hE ⟨x, true, scheduleProgram 0 l⟩ (isBoundaryContinuedProgram_scheduleProgram hl 0)
  rcases hx with rfl | hv
  · refine ae_physSet_subset_of_launches κ b jumps (isFlowProgram_scheduleProgram 0 l)
      (E := fun j ω => E ⟨0, true, scheduleProgram 0 l⟩ j ω) (Eventually.of_forall fun ω => Or.inr rfl)
      fun k => ?_
    rcases k with _ | k
    · exact ae_launch_zero_subset_root_zero hGB6 hGW0 hT13 hκ hκ4 hb hh hcf hζ' hl hS
    · exact ae_later_piece_subset_of_step hStep hBR4a hGB6 hT13 hT13₀ hκ hκ4 hb hh hcf hζ' hE hER (Or.inl rfl) hl
        hlt (hint (k + 1))
  · refine ae_physSet_subset_of_launches κ b jumps (isFlowProgram_scheduleProgram 0 l)
      (E := fun j ω => E ⟨x, true, scheduleProgram 0 l⟩ j ω) ?_ fun k => ?_
    · exact GW2Cone.ae_mem_counterflowCompletedRange_of_theorem13 hT13 hGW0 hκ hκ4 hb hh hcf hζ' hv
        (pos_of_mem_lowerArcRoots hv) le_rfl
    rcases k with _ | k
    · exact ae_launch_zero_subset_root_arc hBR4a hGB6 hGW0 hT13 hκ hκ4 hb hh hcf hζ' hv hl hS
    · exact ae_later_piece_subset_of_step hStep hBR4a hGB6 hT13 hT13₀ hκ hκ4 hb hh hcf hζ' hE hER (Or.inr hv) hl
        hlt (hint (k + 1))

end GW2Later

end Theorem14

end InteractingSLE
