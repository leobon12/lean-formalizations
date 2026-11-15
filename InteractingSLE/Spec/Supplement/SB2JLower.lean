/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JRight
import InteractingSLE.Spec.Supplement.SBTail2TraceCompare
import InteractingSLE.Spec.Supplement.SBLxBase
import InteractingSLE.Spec.Supplement.GW2Sched

/-!
# Lemma SB2(2) in the mirrored entry form (ruling R93), checked against its SB4 consumer

Packet PROVE-T14-SB2FIN4. Ruling R93 fixes SB2(2)'s target as the mirror image of R91's entry form: the upper own-angle
history `A` (the schedule `l` from `u ≤ 0`, with the bridge `[u, 0]`) is conditioned on its own past at its next launch
(instruction `k`, launch chart `c`); the remaining lower walk starts "from the prime end over `R` selected by its free
right collar" (`R = max(A ∩ ℝ)`, supplement p. 631, `source/spec/p625-671.md` L121), i.e. at the right entry value
`e_R = g_A(R⁺) ≥ 0` of `c`; conditionally, it is again a lower walk of the retained conditional field.

**Chart and sign (the question left by PROVE-T14-SB2FIN3 §R3).** The SB4 consumer
`Retain.ae_actualTailSewing_of_frame_word` takes the new upper piece as a flow-line driver of a field `hl` from `0`
(the launch clause of the upper history: `hl = h'` read in `c`) and the lower tail as a staged lower walk of
`affField m hl` (from `0`) with `m ≤ 0`. Since `affField m f` is `f ∘ (· − m)` (the point `0` of `f`'s frame sits at
`m`), the lower tail starts at `−m` in `c`'s frame and the upper seed at `m` in the tail's frame. So the consumer's
`m` is `−e_R`, and `m ≤ 0` is exactly `e_R ≥ 0`: the lower tail enters right of the upper tip. **There is no
mismatch**; the statement below is written in the consumer's coordinates (`m = −e_R`, data `affData 1 m b'`, field
`affField m h'`), and `ae_actualTailSewing_of_sb2LowerLaunchEntry` composes it with the consumer in Lean.

* `bridgeHeights`, `IsActiveHighWord` (SB2(2)'s active word on `(m, 0)` in the consumer's classification form, p. 632:
  old upper sides `λ − ψ_jχ`, `−λ − ψ_jχ`, low groups, or the retained bridge heights), `relLowerSpec`;
* **`SB2LowerLaunchEntryStatement`** (the target): S1-type premise only at launch samples (as R94 for SB2(1)); the
  conclusion has the entry clause `IsRightEntryValue c R (−m)`, `m ≤ 0`, the active word, the relative lower walk as
  a regular staged history under the conditional law, the right-record clause of ruling R95 (`WalkRightAdds` of the
  relative walk), and the pathwise link with the actual lower walk (the landed `SB2LowerRegStatement`'s two set
  inclusions);
* `SB2LowerRelStatement` (named input: the target with the entry point fixed, `m = −upperEntry …`, and `0 ≤ e_R` as
  a clause) and **`sb2LowerLaunchEntryStatement_of_rel`** (the entry clause is proved:
  `isRightEntryValue_upperLaunchChart`);
* **`ae_actualTailSewing_of_sb2LowerLaunchEntry`**: SB2(2) + SB3 + the upper history's own launch clause feed the
  consumer directly (`hm`, `hEL`, `hclass`, `hθ`, `hbridge` supplied; `hpos`, `hread`, `hframe` stay the consumer's).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lu

open Lx Leaf FlowDilate Sec4 Exist.Staged Exist.StagedLaw

/-- The original heights of the retained bridge `(u, 0)` (SB4's `original` word for distinct seeds,
`Leaf.distinctSeed_bridge`). -/
def bridgeHeights (b : ℝ → ℝ) (jumps : Finset ℝ) (u : ℝ) : Set ℝ := b '' {x | x ∈ Ioo u 0 ∧ x ∉ jumps}

/-- **SB2(2)'s active word** (p. 632: "For the second assertion reflect this construction [...] If the erased upper
history has an old right side of angle `ψ_j`, its height is `λ − ψ_jχ`"), on the relative interval `(m, 0)` of the
lower tail's frame (`= (0, e_R)` of the launch chart, between the upper tip and `R`), in the classification form of
SB4's consumer: every height of the recentred data is an old upper side height of a schedule angle, a low height, or a
retained bridge height. -/
def IsActiveHighWord (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (u : ℝ) (l : List (ℝ × ℝ≥0)) (b' : ℝ → ℝ)
    (jumps' : Finset ℝ) (m : ℝ) : Prop :=
  ∀ y ∈ Ioo m 0, y ∉ affJumps 1 m jumps' →
    (∃ p ∈ l, affData 1 m b' y = sleLambda κ - p.1 * chiC κ ∨ affData 1 m b' y = -sleLambda κ - p.1 * chiC κ) ∨
      affData 1 m b' y ≤ -sleLambda κ - -(Real.pi / 2) * chiC κ ∨ affData 1 m b' y ∈ bridgeHeights b jumps u

/-- The relative lower walk program in the lower tail's frame (data `affData 1 m b'`). -/
def relLowerSpec (b' : ℝ → ℝ) (jumps' : Finset ℝ) (m : ℝ) : ExplSpec :=
  boundaryWalkSpec (affData 1 m b') (affJumps 1 m jumps') (-(Real.pi / 2)) true

/-- **Lemma SB2(2), entry form** (ruling R93; supplement p. 631, `source/spec/p625-671.md` L121 and the proof
L123–L133). The setting of `SB2LowerRegStatement`, with Theorem 1.4's complete centred counterflow (ruling R96: the
counterflow binder of the SB chain): the upper own-angle history `A = upperPrefix … k` (schedule `l`
from `u ≤ 0`, angles in `(−π/2, π/2]`, with the bridge `[u, 0]` whose lower left groups are admissible), on the closed
left of the completed lower walk at every launch sample. Let instruction `k` of the upper history launch in the chart
`c`. Then for almost every such sample `ω₀` and every witness `(b', jumps', h')` of the launch clause (`h'` the field
read in `c`, a GFF with data `b'` conditionally on the upper history's own past), there are `m ≤ 0` and drivers `EL`
such that

* (entry) `−m` is the right entry value of `c` at `R = max(A ∩ ℝ)` ("the prime end over `R` selected by its free right
  collar");
* (active word) `IsActiveHighWord` on `(m, 0)`;
* (law) conditionally, `EL` is a regular staged lower walk of the recentred field `affField m h'` with data
  `affData 1 m b'` (the lower tail starts at `0`, the upper tip sits at `m`): "again a finite simple proper lower walk
  of the retained conditional field";
* (R95) the relative walk's connectors and zero-lifetime pieces add only real points `≥ 0` (its thresholds are right
  records);
* (link) almost surely the actual lower walk's part off `fillH A` lies in the relative walk's physical image through
  `c.recenter (−m)`, which lies in the actual lower walk ("erase `B` through its unique visit to `R` and lift the
  remaining tail into `D_A`"). -/
def SB2LowerLaunchEntryStatement : Prop :=
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
    ∀ (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ), u ≤ 0 → l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
      ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
        (ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) (k + 1)).2.2.2.1 k =
            some (c, θ) →
        ∀ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
          IsPiecewiseConstantBoundaryData b' jumps' →
          (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (h' ω)) →
          IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
            h' b' jumps' →
          ∃ (m : ℝ) (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞), m ≤ 0 ∧
            IsRightEntryValue c (realMax (upperPrefix κ b jumps E u l k ω₀)) (-m) ∧
            IsActiveHighWord κ b jumps u l b' jumps' m ∧
            IsStagedHistory κ (affData 1 m b') (affJumps 1 m jumps')
              (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
              (fun ω => affField m one_pos (h' ω)) (relLowerSpec b' jumps' m) EL ∧
            StagedPiecesRegular κ (affData 1 m b') (affJumps 1 m jumps')
              (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
              (relLowerSpec b' jumps' m) EL ∧
            (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
              WalkRightAdds κ (affData 1 m b') (affJumps 1 m jumps') (fun _ => EL) ω) ∧
            ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
              lowerWalkSet κ b jumps E ω ∩ (H \ fillH (upperPrefix κ b jumps E u l k ω)) ⊆
                  relPhysSet κ (affData 1 m b') (affJumps 1 m jumps') (c.recenter (-m))
                    (relLowerSpec b' jumps' m) (fun j => EL j ω) ∧
                relPhysSet κ (affData 1 m b') (affJumps 1 m jumps') (c.recenter (-m))
                    (relLowerSpec b' jumps' m) (fun j => EL j ω) ⊆ lowerWalkSet κ b jumps E ω

/-- **Named input: Lemma SB2(2) with its entry point fixed** (`m = −e_R`, `e_R = upperEntry …` the right entry value
of the launch chart at `R`; the only possible entry by `Lx.IsRightEntryValue.eq_rightEntry`): the setting and
hypotheses of `SB2LowerLaunchEntryStatement`; almost surely on the launch event `e_R ≥ 0` (the upper tip is the chart's
boundary point `0`, left of the prime end over `R`); and at almost every launch, for every witness, the active word,
the relative lower walk's law, its right records and the pathwise link of `SB2LowerLaunchEntryStatement` hold with
`m = −e_R`. The entry clause itself is proved (`sb2LowerLaunchEntryStatement_of_rel`). -/
def SB2LowerRelStatement : Prop :=
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
    ∀ (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ), u ≤ 0 → l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
      (∀ᵐ ω₀ ∂P, ω₀ ∈ upperLaunchSet κ b jumps E u l k → 0 ≤ upperEntry κ b jumps E u l k ω₀) ∧
      ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
        (ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) (k + 1)).2.2.2.1 k =
            some (c, θ) →
        ∀ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
          IsPiecewiseConstantBoundaryData b' jumps' →
          (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (h' ω)) →
          IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
            h' b' jumps' →
          ∃ EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
            IsActiveHighWord κ b jumps u l b' jumps' (-upperEntry κ b jumps E u l k ω₀) ∧
            IsStagedHistory κ (affData 1 (-upperEntry κ b jumps E u l k ω₀) b')
              (affJumps 1 (-upperEntry κ b jumps E u l k ω₀) jumps')
              (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
              (fun ω => affField (-upperEntry κ b jumps E u l k ω₀) one_pos (h' ω))
              (relLowerSpec b' jumps' (-upperEntry κ b jumps E u l k ω₀)) EL ∧
            StagedPiecesRegular κ (affData 1 (-upperEntry κ b jumps E u l k ω₀) b')
              (affJumps 1 (-upperEntry κ b jumps E u l k ω₀) jumps')
              (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
              (relLowerSpec b' jumps' (-upperEntry κ b jumps E u l k ω₀)) EL ∧
            (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
              WalkRightAdds κ (affData 1 (-upperEntry κ b jumps E u l k ω₀) b')
                (affJumps 1 (-upperEntry κ b jumps E u l k ω₀) jumps') (fun _ => EL) ω) ∧
            ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
              lowerWalkSet κ b jumps E ω ∩ (H \ fillH (upperPrefix κ b jumps E u l k ω)) ⊆
                  relPhysSet κ (affData 1 (-upperEntry κ b jumps E u l k ω₀) b')
                    (affJumps 1 (-upperEntry κ b jumps E u l k ω₀) jumps')
                    (c.recenter (-(-upperEntry κ b jumps E u l k ω₀)))
                    (relLowerSpec b' jumps' (-upperEntry κ b jumps E u l k ω₀)) (fun j => EL j ω) ∧
                relPhysSet κ (affData 1 (-upperEntry κ b jumps E u l k ω₀) b')
                    (affJumps 1 (-upperEntry κ b jumps E u l k ω₀) jumps')
                    (c.recenter (-(-upperEntry κ b jumps E u l k ω₀)))
                    (relLowerSpec b' jumps' (-upperEntry κ b jumps E u l k ω₀)) (fun j => EL j ω) ⊆
                  lowerWalkSet κ b jumps E ω

/-- The upper schedule program is boundary-continued (its angles are in `(−π/2, π/2]`). -/
theorem isBoundaryContinuedProgram_upperSpec {u : ℝ} {l : List (ℝ × ℝ≥0)}
    (hl : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) :
    IsBoundaryContinuedProgram (upperSpec u l).2.2 :=
  GW2Sched.isBoundaryContinuedProgram_scheduleProgram (fun p hp => ⟨(hl p hp).1.le, (hl p hp).2⟩) 0

/-- **The entry value at the upper launches, almost surely** (from `StagedPiecesRegular` of the upper schedule
program and `isRightEntryValue_upperLaunchChart`). -/
theorem ae_isRightEntryValue_upperEntry {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)}
    (hER : StagedPiecesRegular κ b jumps P (upperSpec u l) (E (upperSpec u l))) (k : ℕ) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ upperLaunchSet κ b jumps E u l k →
      IsRightEntryValue (upperLaunchChart κ b jumps E u l k ω₀) (realMax (upperPrefix κ b jumps E u l k ω₀))
        (upperEntry κ b jumps E u l k ω₀) := by
  filter_upwards [hER] with ω₀ hR₀ hF
  exact isRightEntryValue_upperLaunchChart (fun j c' θ' hl' =>
    hR₀ j θ' _ c' (eq_launch_of_launches _ _ hl').1 hl') hF

/-- **Lemma SB2(2) in entry form from the named input with the entry point fixed**: the entry clause
`IsRightEntryValue c R e_R` is proved at every regular launch (`ae_isRightEntryValue_upperEntry`); `m := −e_R`. -/
theorem sb2LowerLaunchEntryStatement_of_rel (hrel : SB2LowerRelStatement.{u}) :
    SB2LowerLaunchEntryStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hl hlθ hL hleft
  obtain ⟨hnn, hmain⟩ := hrel κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hl hlθ hL hleft
  filter_upwards [hnn, hmain, ae_isRightEntryValue_upperEntry (hER _ (isBoundaryContinuedProgram_upperSpec hlθ)) k]
    with ω₀ hnn₀ hmain₀ hent₀
  intro c θ hlaunch b' J' h' hb' hT' hG'
  have hF := mem_upperLaunchSet hlaunch
  have hent := hent₀ hF
  rw [upperLaunchChart_eq hlaunch] at hent
  obtain ⟨EL, hw, hst, hreg, hra, hlink⟩ := hmain₀ c θ hlaunch b' J' h' hb' hT' hG'
  refine ⟨-upperEntry κ b jumps E u l k ω₀, EL, neg_nonpos.2 (hnn₀ hF), ?_, hw, hst, hreg, hra, hlink⟩
  rw [neg_neg]
  exact hent

/-- The angle of a launched instruction of a schedule program is one of the schedule's angles. -/
theorem exists_mem_of_scheduleProgram_getElem? : ∀ (τ₀ : ℝ≥0) (l : List (ℝ × ℝ≥0)) (k : ℕ) {θ : ℝ} {t : ℝ≥0∞},
    (scheduleProgram τ₀ l)[k]? = some (Sum.inl (θ, t)) → ∃ q ∈ l, θ = q.1
  | _, [], _, _, _, h => by simp [scheduleProgram] at h
  | τ₀, p :: l, 0, θ, t, h => by
    simp only [scheduleProgram, List.getElem?_cons_zero, Option.some.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
    exact ⟨p, List.mem_cons_self, h.1.symm⟩
  | τ₀, p :: l, k + 1, θ, t, h => by
    simp only [scheduleProgram, List.getElem?_cons_succ] at h
    obtain ⟨q, hq, rfl⟩ := exists_mem_of_scheduleProgram_getElem? p.2 l k h
    exact ⟨q, List.mem_cons_of_mem _ hq, rfl⟩

/-- **SB2(2) feeds SB4's consumer** (the check of ruling R93 in Lean): at almost every launch `(c, θ)` of the upper
schedule program, the launch witness `(b', jumps', h')` (whose driver is the `k`-th upper piece, a flow line of `h'`
from `0`) together with SB2(2)'s `m ≤ 0` and lower tail `EL` satisfies every hypothesis of
`Retain.ae_actualTailSewing_of_frame_word` that concerns the pair — `hm`, `hEL` (SB2(2)'s law clause, in the same
frame `affField m h'`), `hclass` (SB2(2)'s active word), `hθ` (the launched angle is a schedule angle), `hbridge`
(the bridge heights, from SB4's hybrid premise via `Leaf.distinctSeed_bridge`) — so only the consumer's own remaining
inputs `hpos`, `hread` and `hframe` are left. -/
theorem ae_actualTailSewing_of_sb2LowerLaunchEntry (hSB2 : SB2LowerLaunchEntryStatement.{u})
    (hSB3 : SB3InductionGenStatement.{u}) (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} {k : ℕ} (hu : u ≤ 0) (hl : l.Pairwise (fun p q => p.2 < q.2))
    (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
    (hgaps : ∀ p ∈ l, ∀ q ∈ l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ)
    (hL : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    (hH : ∀ p ∈ l, ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + p.1 * chiC κ) ∨
      κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    (hleft : ∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) :
    ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) (k + 1)).2.2.2.1 k =
          some (c, θ) →
      ∃ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens) (m : ℝ)
        (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞),
        IsPiecewiseConstantBoundaryData b' jumps' ∧ (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (h' ω)) ∧
        IsFlowLineDriver κ b' jumps' θ
          (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀) h'
          (fun t ω => (E (upperSpec u l) k ω).1 t) (fun ω => (E (upperSpec u l) k ω).2) ∧
        m ≤ 0 ∧ IsRightEntryValue c (realMax (upperPrefix κ b jumps E u l k ω₀)) (-m) ∧
        ∀ {f : ℂ → ℂ} {A S : Ω → Set ℂ} {T : ℝ≥0∞},
          (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
            0 < (E (upperSpec u l) k ω).2) →
          (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
            A ω ⊆ f '' (GW2aSingle.chosenTrace (fun t ω => (E (upperSpec u l) k ω).1 t)
              (fun ω => (E (upperSpec u l) k ω).2) ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ min T (E (upperSpec u l) k ω).2})) →
          (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
            Retain.RetainedTailFrame f (S ω) (relWalkSet κ (affData 1 m b') (affJumps 1 m jumps') EL ω) m) →
          ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
            HasActualTailSewing (A ω) (S ω) := by
  have hEu := hE _ (isBoundaryContinuedProgram_upperSpec (u := u) hlθ)
  filter_upwards [hSB2 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hl hlθ hL hleft,
    hEu.2.2.2 k]
    with ω₀ hS hW
  intro c θ hlaunch
  obtain ⟨b', J', h', hb', hT', hfl⟩ := hW c θ hlaunch
  have hG' := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ hb' hfl
  obtain ⟨m, EL, hm, hent, hword, hst, hreg, -, -⟩ := hS c θ hlaunch b' J' h' hb' hT' hG'
  refine ⟨b', J', h', m, EL, hb', hT', hfl, hm, hent, ?_⟩
  intro f A S T hpos hread hframe
  have hθ : ∃ q ∈ l, θ = q.1 :=
    exists_mem_of_scheduleProgram_getElem? 0 l k (eq_launch_of_launches _ _ hlaunch).1
  exact Retain.ae_actualTailSewing_of_frame_word hSB3 h12 h13 hκ hκ4 hb' hfl hm (fun _ => ⟨hst, hreg⟩)
    (fun p hp => (hlθ p hp).1) hgaps (distinctSeed_bridge hL hH) hθ hword hpos hread hframe

end InteractingSLE.Theorem14.SB.Lu
