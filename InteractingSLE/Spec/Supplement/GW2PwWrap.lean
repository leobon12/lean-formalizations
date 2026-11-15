/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmStepA
import InteractingSLE.Spec.Supplement.GW2KcNil
import InteractingSLE.Spec.Supplement.GW2RuLive

/-!
# GW2's open lines: Claim(k) at every history (root `0`), by induction over the history

Packet PROVE-GW2-STAGEMEAN, R122 round (prefix `GW2Pw`; the `GW2Psm*` modules are landed).

* `historyTime_pos`, `historyTime_lt_cons`: the history time is positive and, on an ordered history, the prefix's time
  is before the entry's;
* `prefixChoice`: the prefix choice of the step (GEOM2's word map at the prefix, record event `univ`);
* **`StepInputsStatement`**: the inputs of `GW2Psm.claim_step` that PROVE-GW2-RELDET proves ((R3) `hcover`, and `hF`:
  version agreement + (R4) word recursion), for a prefix candidate of the entry's angle and cap;
* **`claimAt_all`**: `GW2Psm.ClaimAt` at every ordered history, every candidate, every announced version, every
  choice with GEOM2's word map and RELDET's `u₀`, every word type — from GEOM2's base `GW2Kc.claimAt_nil`,
  `GW2Psm.claim_step`, (R1) `GW2Psm.PrefixLifeStatement` and `StepInputsStatement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Pw

open Exist Staged StagedLaw GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The history time is positive.** -/
theorem historyTime_pos (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    0 < historyTime c r l := by
  cases l with
  | nil => rw [GW2Ru.historyTime_nil]; exact c.hQpos _ r.1.2.2.2
  | cons e l' =>
    obtain ⟨θ, q⟩ := e
    rw [Gm.historyTime_cons]
    exact c.hQpos _ q.2

/-- **On an ordered history the prefix's time is before the entry's.** -/
theorem historyTime_lt_cons (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (e : EntryIdx c.Θ c.Q)
    (l' : List (EntryIdx c.Θ c.Q)) (hord : (historyProgram c r (e :: l')).Pairwise (fun p q => p.2 < q.2)) :
    historyTime c r l' < (e.2 : ℝ≥0) := by
  rw [GW2Psm.historyProgram_cons, List.pairwise_append] at hord
  have h := hord.2.2
  cases l' with
  | nil =>
    rw [GW2Ru.historyTime_nil]
    refine h (rootEntry r.1) ?_ _ (List.mem_singleton_self _)
    simp [historyProgram, entryList, schedOf]
  | cons e' l'' =>
    obtain ⟨θ', q'⟩ := e'
    rw [Gm.historyTime_cons]
    refine h ((θ' : ℝ), (q' : ℝ≥0)) ?_ _ (List.mem_singleton_self _)
    rw [GW2Psm.historyProgram_cons]
    simp

section Wrap

open WholeField LocalSets GW2Rd GW2Rz GW2Sde Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Restart
  Restart.DomainMarkov MartChar.RealFlow GW2JointKernel Sec7.PocketTraversal Supp8.RelSafe GW2Psm
open QuantumZipper (chiC)

/-- **The prefix choice of the Claim(k) step**: GEOM2's word map at the prefix `(l', a')`, record event `univ`, the
history's centring `u₀`. -/
abbrev prefixChoice {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l' : List (EntryIdx c.Θ c.Q)) (a' : ℕ) (cw : BoundaryWord) (u₀ : ℂ → ℝ) : GW2Sdh.SchedChoice Ω :=
  GW2Wm.wmChoiceX c.κ cw (rootPt r.1) c.s (historyProgram c r l') ((entryList l').length + 1)
    (length_historyProgram c r l') (candAngle c r l' a') univ u₀ (fun _ => ⊥)

/-- **The inputs of the Claim(k) step** (pieces (R3), (R2)+clocks and (R4) of PROVE-GW2-RELDET; see the STAGEMEAN
handoff): for a history `e :: l'` at root `0`, a prefix candidate `a'` of `e`'s angle and cap `e.2`, and any
announced version of the history's instance with GEOM2's word map, there are a good set and a version family of the
prefix instance (choice `prefixChoice`) such that the history's live event is covered by the prefix's live events
below the cap at the entry's duration (`hcover` of `claim_step`) and, on them, the stage starts and the versions agree
up to the history's stage start and GEOM2's word recursion holds (`hF` of `claim_step`). -/
def StepInputsStatement : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (e : EntryIdx c.Θ c.Q) (l' : List (EntryIdx c.Θ c.Q)) (a a' : ℕ), rootPt r.1 = 0 → 0 < c.s →
    (historyProgram c r (e :: l')).Pairwise (fun p q => p.2 < q.2) →
    candidateAngle c r a' = (e.1 : ℝ) → candidateCap c r a' = (e.2 : ℝ≥0) →
    ∀ (cw : BoundaryWord) {GT : Set Ω}
      (_hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) (schedTr c r (e :: l') a)
        c.α ω) ∧ MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
      {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
      (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r (e :: l') a) (schedTr c r (e :: l') a) c.α
        R V), (∀ ω, V ω ≠ ⊤) → ∀ (ch : GW2Sdh.SchedChoice Ω),
      ch.β = GW2Wm.schedWordMapX c.κ cw (rootPt r.1) c.s (historyProgram c r (e :: l'))
        ((entryList (e :: l')).length + 1) (length_historyProgram c r (e :: l')) (candAngle c r (e :: l') a) →
      ∀ w : WordType,
      ∃ (GT' : Set Ω) (_hGT' : (∀ ω ∈ GT', PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a')
          (schedTr c r l' a') c.α ω) ∧ MeasurableSet GT' ∧
          (∀ᵐ ω ∂c.P, ω ∈ GT' ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
        (R' : ℕ → ℝ≥0 → Ω → ℝ) (V' : ℕ → Ω → ℝ≥0∞)
        (hA' : ∀ n, IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l' a') (schedTr c r l' a') c.α
          (R' n) (V' n)) (_hV' : ∀ n ω, V' n ω ≠ ⊤),
        (∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).E
            ((GW2Rv.schedInstSX c r (e :: l') a GT hA ch).srecX c r (e :: l') (rootPt r.1)) →
          (0 : ℝ≥0∞) < (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).capX c (rootPt r.1) ω →
          ∃ n, (GW2Rv.schedInstSX c r l' a' GT' (hA' n) (prefixChoice c r l' a' cw ch.u₀)).srecX c r l'
              (rootPt r.1) ω ∈ (GW2Rv.schedInstSX c r l' a' GT' (hA' n) (prefixChoice c r l' a' cw ch.u₀)).E ∧
            (GW2Rv.schedInstSX c r l' a' GT' (hA' n) (prefixChoice c r l' a' cw ch.u₀)).clockX c (rootPt r.1)
                ((e.2 : ℝ≥0) - historyTime c r l') ω <
              (GW2Rv.schedInstSX c r l' a' GT' (hA' n) (prefixChoice c r l' a' cw ch.u₀)).capX c (rootPt r.1) ω) ∧
        (∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).E
            ((GW2Rv.schedInstSX c r (e :: l') a GT hA ch).srecX c r (e :: l') (rootPt r.1)) →
          (0 : ℝ≥0∞) < (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).capX c (rootPt r.1) ω → ∀ n : ℕ,
          (GW2Rv.schedInstSX c r l' a' GT' (hA' n) (prefixChoice c r l' a' cw ch.u₀)).srecX c r l' (rootPt r.1) ω ∈
              (GW2Rv.schedInstSX c r l' a' GT' (hA' n) (prefixChoice c r l' a' cw ch.u₀)).E →
          (GW2Rv.schedInstSX c r l' a' GT' (hA' n) (prefixChoice c r l' a' cw ch.u₀)).clockX c (rootPt r.1)
              ((e.2 : ℝ≥0) - historyTime c r l') ω <
            (GW2Rv.schedInstSX c r l' a' GT' (hA' n) (prefixChoice c r l' a' cw ch.u₀)).capX c (rootPt r.1) ω →
          (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') GT' (V' n) (historyTime c r l') ω +
              ((GW2Rv.schedInstSX c r l' a' GT' (hA' n) (prefixChoice c r l' a' cw ch.u₀)).clockX c (rootPt r.1)
                ((e.2 : ℝ≥0) - historyTime c r l') ω).toNNReal =
            stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) GT V (historyTime c r (e :: l')) ω) ∧
          (∀ u ≤ stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) GT V (historyTime c r (e :: l')) ω,
            R' n u ω = R u ω) ∧
          ch.β ((GW2Rv.schedInstSX c r (e :: l') a GT hA ch).srecX c r (e :: l') (rootPt r.1) ω) =
            GW2Rd.upW (candAngle c r (e :: l') a * chiC c.κ)
              (stopWord c.κ (GW2Wm.baseWordX c.κ cw (rootPt r.1) c.s (historyProgram c r l')
                ((entryList l').length + 1) (length_historyProgram c r l')
                  ((GW2Rv.schedInstSX c r l' a' GT' (hA' n) (prefixChoice c r l' a' cw ch.u₀)).srecX c r l'
                    (rootPt r.1) ω),
                (e.1 : ℝ), recOf (((GW2Rv.schedInstSX c r l' a' GT' (hA' n)
                  (prefixChoice c r l' a' cw ch.u₀)).clockX c (rootPt r.1) ((e.2 : ℝ≥0) - historyTime c r l')
                    ω).toNNReal : ℝ≥0∞) (fun q => stgDrv (fun u => R' n u ω)
                    (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') GT' (V' n) (historyTime c r l') ω) q,
                    ⊤))))

/-- **Claim(k) at every history** (root `0`): by induction on the history, from GEOM2's base `GW2Kc.claimAt_nil`, the
step `GW2Psm.claim_step`, (R1) and the step inputs. -/
theorem claimAt_all (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) (hR1 : PrefixLifeStatement.{u})
    (hIn : StepInputsStatement.{u}) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (hr0 : rootPt r.1 = 0) (hs0 : 0 < c.s) {cw : BoundaryWord}
    (hcw : GW2Kb.IsCfWordOf c.κ c.P c.h c.W c.ζ cw) :
    ∀ l : List (EntryIdx c.Θ c.Q), (historyProgram c r l).Pairwise (fun p q => p.2 < q.2) →
    ∀ (a : ℕ) {GT : Set Ω}
      (_hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω) ∧
        MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
      {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
      (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V),
      (∀ ω, V ω ≠ ⊤) → ∀ ch : GW2Sdh.SchedChoice Ω, IsBoundedHarmonicExtension c.b c.jumps ch.u₀ →
      Measurable ch.β → MeasurableSet ch.E₀ →
      ch.β = GW2Wm.schedWordMapX c.κ cw (rootPt r.1) c.s (historyProgram c r l) ((entryList l).length + 1)
        (length_historyProgram c r l) (candAngle c r l a) →
      ch.σa = specOffset c.κ + candAngle c r l a * chiC c.κ →
      ∀ w : WordType, ClaimAt c r l a GT hA ch w := by
  intro l
  induction l with
  | nil =>
    intro _ a GT hGT R V hA hV ch hu₀ _ _ hβ hσa w
    exact GW2Kc.claimAt_nil h12 h13 c r a hr0 hs0 hGT hA hV ch hu₀ hcw hβ hσa w
  | cons e l' ih =>
    intro hord a GT hGT R V hA hV ch hu₀ hβm hE₀ hβ hσa w
    obtain ⟨a', ha'θ, ha'cap, -⟩ := exists_candidate c r e.1 e.2 0
    have hord' : (historyProgram c r l').Pairwise (fun p q => p.2 < q.2) := by
      have h := hord
      rw [GW2Psm.historyProgram_cons, List.pairwise_append] at h
      exact h.1
    have hlt := historyTime_lt_cons c r e l' hord
    have hT : historyTime c r (e :: l') = (e.2 : ℝ≥0) := by
      obtain ⟨θ, q⟩ := e
      exact Gm.historyTime_cons c r l' θ q
    have hθ : candidateAngle c r a' = (e.1 : ℝ) := by rw [ha'θ]
    have hcapE : candidateCap c r a' = (e.2 : ℝ≥0) := by rw [ha'cap]
    have hδ : historyTime c r l' + ((e.2 : ℝ≥0) - historyTime c r l') = historyTime c r (e :: l') := by
      rw [hT]
      exact add_tsub_cancel_of_le hlt.le
    have hδ0 : 0 < (e.2 : ℝ≥0) - historyTime c r l' := tsub_pos_of_lt hlt
    have hδcap : (e.2 : ℝ≥0) - historyTime c r l' < candidateCap c r a' := by
      rw [hcapE]
      exact tsub_lt_self ((historyTime_pos c r l').trans hlt) (historyTime_pos c r l')
    have hcap : historyTime c r (e :: l') ≤ historyTime c r l' + candidateCap c r a' := by
      rw [hT, hcapE]
      exact le_add_self
    obtain ⟨GT', hGT', R', V', hA', hV', hcover, hF⟩ :=
      hIn c r e l' a a' hr0 hs0 hord hθ hcapE cw hGT hA hV ch hβ w
    have hβm' : Measurable (prefixChoice c r l' a' cw ch.u₀).β :=
      (GW2Wm.wmChoiceX_targets c.κ cw (rootPt r.1) c.s (historyProgram c r l') _ (length_historyProgram c r l')
        (candAngle c r l' a') univ ch.u₀ (fun _ => ⊥)).1
    have hIH : ∀ (n : ℕ) (w' : WordType), ClaimAt c r l' a' GT' (hA' n) (prefixChoice c r l' a' cw ch.u₀) w' :=
      fun n w' => ih hord' a' hGT' (hA' n) (hV' n) (prefixChoice c r l' a' cw ch.u₀) hu₀ hβm' MeasurableSet.univ rfl
        rfl w'
    exact claim_step h12 h13 h12₀ h13₀ hR1 c r e l' a a' hr0 hs0 hord hord' hθ hcap _ hδ hδ0 hδcap hGT hA hV ch hu₀
      hβm hE₀ hσa w hGT' hA' hV' (prefixChoice c r l' a' cw ch.u₀) rfl rfl hβm' MeasurableSet.univ cw
      (length_historyProgram c r l') rfl rfl hIH hcover hF

end Wrap

end InteractingSLE.Theorem14.GW2Pw
