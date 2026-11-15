/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TipSystemGB6

/-!
# GB6's staged equality datum by GW1's induction (kernel chain form)

Packet PROVE-GW2-SCHED. Lemma GW1's proof (supplement pp. 618–620) carries the induction datum 2 — the complete
conditional counterflow pair targeted at the current incoming tip — from one launch to the next: "Apply GB6, within the
independently established complete conditional pair in item 2, to every available interior-tip prefix of `β_j`";
"auxiliary stage encodings may be forgotten by the tower property". GB6's assertion is an **equality** (p. 518:
"the portion of `η` before its first contact with `α[0, σ]` … is the complete canonical counterflow of the conditional
component field"), recorded at a launch by `GW2TipSystem.HasLaunchPairEq` (PROVE-T14-TIP12).

**What the induction proves.** The inductive step is a statement about the conditional laws: at almost every sample
`ω₀` carrying the datum at launch `j`, almost every sample of the conditional law given the retained past before `j`
carries the datum at launch `j + 1` (named input `GB6StagedEqStepStatement`, the equality form of the landed
`GW2Later.GB6PastStepStatement`). The datum is not a measurable event of the sample (it quantifies over drivers and
time changes), so the step cannot be integrated against `P` launch by launch (ruling R51: a property that holds almost
surely under almost every conditional law need not hold `P`-almost surely). The induction therefore carries only
**measurable consequences** of the datum down the chain of retained pasts (`KernelTower.ae_ae_of_chain`):

* `HasLaunchPairEqInt`: the datum at launch `j`, required only when the first `j` pieces were successful and their
  switching tips are interior;
* **`GB6StagedEqStepStatement`** (named input): GW1's inductive step with GB6's equality;
* `hasLaunchPairEq_zero`: the datum at the first launch from either kind of root (PROVE-T14-TIP12's base cases);
* **`ae_of_gb6StagedEqStep`**: every measurable event that is almost sure under the conditional law at launch `k`
  whenever the datum holds there is `P`-almost sure;
* **`ae_later_piece_subset_of_eqStep`**, **`ae_physSet_subset_of_eqStep`**: GW2's schedule containment from the
  equality step (the landed `GW2Later.ae_physSet_subset_of_step` with `GB6StagedEqStepStatement` in place of
  `GB6PastStepStatement`).

The `P`-almost-sure form `GW2TipSystem.GB6StagedEqStatement` is not a consequence of a kernel-form step (a
Sierpiński-type set can be null under every conditional law and of full outer `P`-measure); every consumer of the
datum in the stage experiment (A.3–A.5) only needs measurable consequences, which `ae_of_gb6StagedEqStep` supplies.
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

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- GB6's equality datum at launch `j`, required when the first `j` pieces were successful (own times `Δ`) and their
switching tips are interior. -/
def HasLaunchPairEqInt (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (W' : ℝ≥0 → Ω → ℝ) (spec : ExplSpec) (Δ : ℕ → ℝ≥0∞) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (j : ℕ) (ω : Ω) :
    Prop :=
  AllSucc Δ (fun i => E i ω) j → SwitchTipsInterior spec (fun i => E i ω) j →
    HasLaunchPairEq κ b jumps P h W' spec E j ω

/-- The equality datum with its launch condition gives the containment datum with its launch condition. -/
theorem HasLaunchPairEqInt.hasLaunchPairInt {P : Measure Ω} [IsFiniteMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {spec : ExplSpec} {Δ : ℕ → ℝ≥0∞}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {j : ℕ} {ω : Ω} (hD : HasLaunchPairEqInt κ b jumps P h W' spec Δ E j ω) :
    HasLaunchPairInt κ b jumps P h W' spec Δ E j ω :=
  fun hs hi => (hD hs hi).hasLaunchPair

/-- **Named input: GW1's inductive step with GB6's equality** (supplement pp. 518–520, 618–620, 623). The setting of
`GW2Later.GB6PastStepStatement` verbatim, with the equality datum `HasLaunchPairEq` in place of the containment datum:
at almost every sample `ω₀` at which the conditional counterflow at launch `j` is the original counterflow before its
first contact with the retained prefix (up to a time change), almost every sample of the conditional law given the
retained past before `j` has the same datum at launch `j + 1` (when the first `j + 1` pieces were successful with
interior switching tips). This is GB6's main assertion for the piece launched at `j`, applied in the conditional world
given the retained past (the counterflow there is the original one before contact, by the datum at `j`; GB6 removes
the part after the first contact with the new piece), with the regular conditional law given the longer retained past
in place of the conditional law given the piece in that world ("auxiliary stage encodings may be forgotten by the
tower property", p. 620). -/
def GB6StagedEqStepStatement : Prop :=
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
          HasLaunchPairEqInt κ b jumps P h W' ⟨x, true, scheduleProgram 0 l⟩ (schedDelta 0 l)
              (E ⟨x, true, scheduleProgram 0 l⟩) j ω₀ →
            ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps ⟨x, true, scheduleProgram 0 l⟩
                (E ⟨x, true, scheduleProgram 0 l⟩) j) ω₀),
              HasLaunchPairEqInt κ b jumps P h W' ⟨x, true, scheduleProgram 0 l⟩ (schedDelta 0 l)
                (E ⟨x, true, scheduleProgram 0 l⟩) (j + 1) ω

/-- **The equality datum at the first launch, from either kind of root** (PROVE-T14-TIP12's base cases: the original
counterflow itself from the root `0`; Corollary BR4a's pair from a root of the first low right arc). -/
theorem hasLaunchPairEq_zero (hBR4a : BR4a.BR4aStatement.{u}) (hT13 : Exist.Theorem13Statement.{u})
    (hT13₀ : Exist.Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {x : ℝ}
    (hx : x = 0 ∨ x ∈ lowerArcRoots κ b jumps) {l : List (ℝ × ℝ≥0)} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω₀ : Ω) :
    HasLaunchPairEq κ b jumps P h W' ⟨x, true, scheduleProgram 0 l⟩ E 0 ω₀ := by
  rcases hx with rfl | hv
  · exact ae_hasLaunchPairEq_zero_root_zero hT13 hκ hcf hζ' E ω₀
  · exact ae_hasLaunchPairEq_zero_root_arc hBR4a hT13 hT13₀ hκ hκ4 hb hh hcf hζ' hv E ω₀

/-- **GB6's staged equality by GW1's induction, for measurable consequences.** For a GW2 schedule from `0` or a root
of the first low right arc and a staged history with regular pieces: if a measurable event `A` is almost sure under the
conditional law given the retained past before launch `k` at almost every sample carrying the equality datum at `k`,
then `A` is `P`-almost sure. The datum starts at the first launch (`hasLaunchPairEq_zero`), is propagated by the named
step, and only `A` is integrated (`KernelTower.ae_ae_of_chain`). -/
theorem ae_of_gb6StagedEqStep (hStep : GB6StagedEqStepStatement.{u}) (hBR4a : BR4a.BR4aStatement.{u})
    (hT13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {x : ℝ} (hx : x = 0 ∨ x ∈ lowerArcRoots κ b jumps) {l : List (ℝ × ℝ≥0)}
    (hl : ∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (hlt : l.Pairwise (fun p q => p.2 < q.2))
    {A : Set Ω} (hA : MeasurableSet A) (k : ℕ)
    (htop : ∀ᵐ ω₀ ∂P, HasLaunchPairEqInt κ b jumps P h W' ⟨x, true, scheduleProgram 0 l⟩ (schedDelta 0 l)
        (E ⟨x, true, scheduleProgram 0 l⟩) k ω₀ →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps ⟨x, true, scheduleProgram 0 l⟩
        (E ⟨x, true, scheduleProgram 0 l⟩) k) ω₀), ω ∈ A) :
    ∀ᵐ ω ∂P, ω ∈ A := by
  set spec : ExplSpec := ⟨x, true, scheduleProgram 0 l⟩ with hspec
  have hS := hE spec (isBoundaryContinuedProgram_scheduleProgram hl 0)
  have hchain := KernelTower.ae_ae_of_chain (P := P) (𝒢 := fun j => pastSigma κ b jumps spec (E spec) j)
    (fun j => Exist.StagedLaw.pastSigma_mono (κ := κ) (b := b) (jumps := jumps) spec (E spec) (Nat.le_succ j))
    (fun j => hS.2.1 j) (D := fun j ω => HasLaunchPairEqInt κ b jumps P h W' spec (schedDelta 0 l) (E spec) j ω)
    hA k htop (fun j _ => hStep κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER x hx l hl hlt j) 0
    (Nat.zero_le k)
  have hD0 : ∀ ω, HasLaunchPairEqInt κ b jumps P h W' spec (schedDelta 0 l) (E spec) 0 ω :=
    fun ω _ _ => hasLaunchPairEq_zero hBR4a hT13 hT13₀ hκ hκ4 hb hh hcf hζ' hx (E spec) ω
  have hν : ∀ ω, condExpKernel P (pastSigma κ b jumps spec (E spec) 0) ω = P := fun ω => by
    rw [GW1.pastSigma_zero_eq_bot]
    exact GW1.condExpKernel_bot_apply P ω
  obtain ⟨ω, hω⟩ := hchain.exists
  have h1 := hω (hD0 ω)
  rwa [hν] at h1

/-- **GW2a's later pieces from GB6's equality step.** As `GW2Later.ae_later_piece_subset_of_step`, with the equality
step `GB6StagedEqStepStatement` in place of the containment step: for `k ≥ 1`, if almost surely the switching tips
before `k` are interior whenever the first `k` pieces were successful, the piece launched at `k` lies in the completed
counterflow range almost surely. The measurable containment event of the piece (`exists_measurable_piece_event`) is
the consequence carried by `ae_of_gb6StagedEqStep`. -/
theorem ae_later_piece_subset_of_eqStep (hStep : GB6StagedEqStepStatement.{u}) (hBR4a : BR4a.BR4aStatement.{u})
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
    have htop : ∀ᵐ ω ∂P, HasLaunchPairEqInt κ b jumps P h W' spec (schedDelta 0 l) (E spec) k ω →
        ∀ᵐ y ∂(condExpKernel P (pastSigma κ b jumps spec (E spec) k) ω), y ∈ Lᶜ ∪ A := by
      filter_upwards [hker, hint, Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) (hS.2.1 k) hL𝒢.compl]
        with ω hk1 hi hLc hD
      by_cases hωL : ω ∈ L
      · filter_upwards [hk1 hωL ((hD hωL (hi hωL)).hasLaunchPair)] with y hy using Or.inr hy
      · filter_upwards [hLc hωL] with y hy using Or.inl hy
    have hP : ∀ᵐ y ∂P, y ∈ Lᶜ ∪ A :=
      ae_of_gb6StagedEqStep hStep hBR4a hT13 hT13₀ hκ hκ4 hb hh hcf hζ' hE hER hx hl hlt hA'm k htop
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

/-- **GW2's schedule containment from GB6's equality step** (both roots): as `GW2Later.ae_physSet_subset_of_step`,
with `GB6StagedEqStepStatement` in place of `GB6PastStepStatement`. Named inputs: the equality step, Corollary BR4a,
GB6's restart law, Theorem 1.3. -/
theorem ae_physSet_subset_of_eqStep (hStep : GB6StagedEqStepStatement.{u}) (hBR4a : BR4a.BR4aStatement.{u})
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
    · exact ae_later_piece_subset_of_eqStep hStep hBR4a hGB6 hT13 hT13₀ hκ hκ4 hb hh hcf hζ' hE hER (Or.inl rfl)
        hl hlt (hint (k + 1))
  · refine ae_physSet_subset_of_launches κ b jumps (isFlowProgram_scheduleProgram 0 l)
      (E := fun j ω => E ⟨x, true, scheduleProgram 0 l⟩ j ω) ?_ fun k => ?_
    · exact GW2Cone.ae_mem_counterflowCompletedRange_of_theorem13 hT13 hGW0 hκ hκ4 hb hh hcf hζ' hv
        (pos_of_mem_lowerArcRoots hv) le_rfl
    rcases k with _ | k
    · exact ae_launch_zero_subset_root_arc hBR4a hGB6 hGW0 hT13 hκ hκ4 hb hh hcf hζ' hv hl hS
    · exact ae_later_piece_subset_of_eqStep hStep hBR4a hGB6 hT13 hT13₀ hκ hκ4 hb hh hcf hζ' hE hER (Or.inr hv)
        hl hlt (hint (k + 1))

end GW2TipSystem

end Theorem14

end InteractingSLE
