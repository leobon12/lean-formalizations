/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NwIn
import InteractingSLE.Spec.Supplement.GW2RuLive
import InteractingSLE.Spec.Supplement.GW2SdoWord

/-!
# Claim(k) at every history (root `0`), by induction over the history

Packet PROVE-GW2-NOTHR (round 5, decision D52 revised: NOTHR takes Claim(k)'s induction wrapper). From GEOM2's base
`GW2Kc.claimAt_nil` and STAGEMEAN's step `GW2Psm.claim_step`, with RELDET's pieces consumed as their statements
((R1) `GW2Psm.PrefixLifeStatement`, (R2) `GW2Psm.PrefixContactStatement`, (R3) `PrefixLiveCoverStatement`, the prefix
identification `PrefixIdentStatement`, (R4) `BetaConsStatement`):

* **`historyTime_pos`**, **`historyTime_lt_cons`**: the history time is positive and increases along the history;
* **`prefixCh`**: the prefix choice of the step, GEOM2's word map at the prefix with record event off RELDET's
  zero-lifetime records (as (R3) needs) and the history's centring;
* **`claimAt_cons`**: the step at one history. The prefix instances use the canonical exhausting version family
  (`GW2Rv.exists_schedVersionsXA_strict`) and ROOTX's good set. `claim_step`'s `hcover` is (R3). Its `hF` comes
  from the prefix identification, (R4) and (R2), read on the live event.
* **`claimAt_all`**: `GW2Psm.ClaimAt` at every time-ordered history (root `0`), every candidate, every announced version
  with finite stops, every choice with GEOM2's word map, a bounded harmonic centring, a measurable record event and
  the candidate's offset, and every word type.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Nw

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31
  GW2Rz GW2Wm GW2Rd Sec5.Prop513Schedule Supp8 Supp8.Q3Stop GW2Psm WholeField LocalSets GW2JointKernel

variable {Ω : Type u} [MeasurableSpace Ω]

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

/-- **The prefix choice of the step**: GEOM2's word map at the prefix `(l', a')`, the record event off RELDET's
zero-lifetime records, the history's centring `u₀`. -/
abbrev prefixCh (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l' : List (EntryIdx c.Θ c.Q)) (a' : ℕ)
    (cw : BoundaryWord) (u₀ : ℂ → ℝ) : GW2Sdh.SchedChoice Ω :=
  GW2Wm.wmChoiceX c.κ cw (rootPt r.1) c.s (historyProgram c r l') ((entryList l').length + 1)
    (length_historyProgram c r l') (candAngle c r l' a') (launchBadRec c r l' a')ᶜ u₀ (fun _ => ⊥)

variable [StandardBorelSpace Ω]

/-- **Claim(k) at one history, for every candidate, version, admissible choice and word type** (root `0`). -/
def ClaimAll (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (cw : BoundaryWord) (l : List (EntryIdx c.Θ c.Q)) :
    Prop :=
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
    ∀ w : WordType, ClaimAt c r l a GT hA ch w

/-- **The Claim(k) step at one history** (root `0`): Claim(k) at the prefix gives it at `e :: l'`, from STAGEMEAN's
`claim_step` with RELDET's pieces. -/
theorem claimAt_cons (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hR1 : PrefixLifeStatement.{u}) (hR2 : PrefixContactStatement.{u}) (hR3 : PrefixLiveCoverStatement.{u})
    (hId : PrefixIdentStatement.{u}) (hR4 : BetaConsStatement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (hr0 : rootPt r.1 = 0) (hs0 : 0 < c.s) (cw : BoundaryWord) (e : EntryIdx c.Θ c.Q) (l' : List (EntryIdx c.Θ c.Q))
    (hord : (historyProgram c r (e :: l')).Pairwise (fun p q => p.2 < q.2)) (hIH : ClaimAll c r cw l') :
    ClaimAll c r cw (e :: l') := by
  intro a GT hGT R V hA hV ch hu₀ hβm hE₀ hβ hσa w
  have hx : (0 : ℝ) ≤ rootPt r.1 := by rw [hr0]
  obtain ⟨a', ha'θ, ha'cap, -⟩ := exists_candidate c r e.1 e.2 0
  have hord' : (historyProgram c r l').Pairwise (fun p q => p.2 < q.2) := by
    have h := hord
    rw [GW2Psm.historyProgram_cons, List.pairwise_append] at h
    exact h.1
  have hTO : TimeOrdered 0 (historyProgram c r (e :: l')) := Gm.timeOrdered_of_pairwise_lt hord
  have hlt := historyTime_lt_cons c r e l' hord
  have hT : historyTime c r (e :: l') = (e.2 : ℝ≥0) := by
    obtain ⟨θ, q⟩ := e
    exact Gm.historyTime_cons c r l' θ q
  have hθ : candidateAngle c r a' = (e.1 : ℝ) := by rw [ha'θ]
  have hcapE : candidateCap c r a' = (e.2 : ℝ≥0) := by rw [ha'cap]
  have hlt' : historyTime c r l' < historyTime c r (e :: l') := hT ▸ hlt
  have hTT : historyTime c r l' ≤ historyTime c r (e :: l') := hlt'.le
  have hδ : historyTime c r l' + (historyTime c r (e :: l') - historyTime c r l') = historyTime c r (e :: l') :=
    add_tsub_cancel_of_le hTT
  have hδ0 : 0 < historyTime c r (e :: l') - historyTime c r l' := tsub_pos_of_lt hlt'
  have hδcap : historyTime c r (e :: l') - historyTime c r l' < candidateCap c r a' := by
    rw [hcapE, hT]
    exact tsub_lt_self ((historyTime_pos c r l').trans hlt) (historyTime_pos c r l')
  have hcap : historyTime c r (e :: l') ≤ historyTime c r l' + candidateCap c r a' := by
    rw [hT, hcapE]
    exact le_add_self
  -- the prefix instances: ROOTX's good set, the canonical exhausting family, GEOM2's word map off `launchBadRec`
  obtain ⟨R', V', hA', -, -, hV', hex'⟩ := GW2Rv.exists_schedVersionsXA_strict h13 c r l' a' hx
  have hGT' := schedGTX_spec h13 c r l' a'
  set ch' := prefixCh c r l' a' cw ch.u₀ with hch'
  have hβm' : Measurable ch'.β := (GW2Wm.wmChoiceX_targets c.κ cw (rootPt r.1) c.s (historyProgram c r l') _
    (length_historyProgram c r l') (candAngle c r l' a') (launchBadRec c r l' a')ᶜ ch.u₀ (fun _ => ⊥)).1
  have hE₀' : MeasurableSet ch'.E₀ := (measurableSet_launchBadRec c r l' a').compl
  have hIH' : ∀ (n : ℕ) (w' : WordType), ClaimAt c r l' a' (schedGTX h13 c r l' a') (hA' n) ch' w' :=
    fun n w' => hIH a' hGT' (hA' n) (hV' n) ch' hu₀ hβm' hE₀' rfl rfl w'
  -- (R3): the prefix live cover
  have hcover := hR3 h13 c r hx hs0 e l' a a' hθ hcap hTT hGT hA hV ch hA' hex' ch' rfl w
  -- the stage starts, the versions and the words, from the prefix identification, (R4) and (R2)
  set I := GW2Rv.schedInstSX c r (e :: l') a GT hA ch with hIdef
  have hρ := hA.1.2.choose_spec
  have hfin : ∀ᵐ ω ∂c.P, I.srecX c r (e :: l') (rootPt r.1) ω ∈ I.E →
      stgStartMX (rootPt r.1) c.s c.W c.ζ I.W I.GT I.V I.T ω ≠ ⊤ :=
    Eventually.of_forall fun ω _ => ne_top_of_le_ne_top (hV ω) (min_le_right _ _)
  have hEgood := GW2Sde.StageInst.E_good_of_recordX I hA.1.1 hρ.2.1 hρ.2.2 inter_subset_right hfin
  have hF : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w ch.β I.E (I.srecX c r (e :: l') (rootPt r.1)) →
      (0 : ℝ≥0∞) < I.capX c (rootPt r.1) ω → ∀ n : ℕ,
      (GW2Rv.schedInstSX c r l' a' (schedGTX h13 c r l' a') (hA' n) ch').srecX c r l' (rootPt r.1) ω ∈
          (GW2Rv.schedInstSX c r l' a' (schedGTX h13 c r l' a') (hA' n) ch').E →
      (GW2Rv.schedInstSX c r l' a' (schedGTX h13 c r l' a') (hA' n) ch').clockX c (rootPt r.1)
          (historyTime c r (e :: l') - historyTime c r l') ω <
          (GW2Rv.schedInstSX c r l' a' (schedGTX h13 c r l' a') (hA' n) ch').capX c (rootPt r.1) ω →
      (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') (schedGTX h13 c r l' a') (V' n) (historyTime c r l') ω +
          ((GW2Rv.schedInstSX c r l' a' (schedGTX h13 c r l' a') (hA' n) ch').clockX c (rootPt r.1)
            (historyTime c r (e :: l') - historyTime c r l') ω).toNNReal =
        stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) GT V (historyTime c r (e :: l')) ω) ∧
      (∀ u ≤ stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) GT V (historyTime c r (e :: l')) ω,
        R' n u ω = R u ω) ∧
      ch.β (I.srecX c r (e :: l') (rootPt r.1) ω) =
        GW2Rd.upW (candAngle c r (e :: l') a * chiC c.κ)
          (stopWord c.κ (GW2Wm.baseWordX c.κ cw (rootPt r.1) c.s (historyProgram c r l')
            ((entryList l').length + 1) (length_historyProgram c r l')
              ((GW2Rv.schedInstSX c r l' a' (schedGTX h13 c r l' a') (hA' n) ch').srecX c r l' (rootPt r.1) ω),
            (e.1 : ℝ), recOf (((GW2Rv.schedInstSX c r l' a' (schedGTX h13 c r l' a') (hA' n) ch').clockX c
              (rootPt r.1) (historyTime c r (e :: l') - historyTime c r l') ω).toNNReal : ℝ≥0∞)
              (fun q => stgDrv (fun u => R' n u ω)
                (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') (schedGTX h13 c r l' a') (V' n)
                  (historyTime c r l') ω) q, ⊤))) := by
    filter_upwards [ae_all_iff.2 fun n => hId h13 c r hx hs0 e l' a a' hθ hcap hTT hGT hA.1.1 (hA' n).1.1,
      ae_all_iff.2 fun n => hR4 h13 c r hx hs0 cw e l' a a' hθ hcap hTO hGT hA hV (hA' n) (hV' n) ch ch' hβ rfl,
      hEgood, GW2Psm.ae_lt_contactX_all hGT.1 hs0 hx hA.1.1, hR2 c r e l' a a' hθ hcap, hGT.2.2, hGT'.2.2]
      with ω hIdω hR4ω hEgω hconω hR2ω hGTω hGT'ω hlive _ n _ hclk'
    have hEω : I.srecX c r (e :: l') (rootPt r.1) ω ∈ I.E := hlive.1
    have hold : oldSuccess c r (e :: l') ω := (GW2Sdi.augRec_mem_succRec_iff c r (e :: l') _ ω).1 hEω.1.2
    obtain ⟨hgood, hSV⟩ := hEgω hEω
    have hω : ω ∈ GT := hGTω.2 hgood
    have hω' : ω ∈ schedGTX h13 c r l' a' := hGT'ω.2 hgood
    have hTc := hconω hω (historyTime c r (e :: l')) hSV
    have hTV : ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a)
        (historyTime c r (e :: l')) ω) < V ω := by
      have h1 : min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) GT (historyTime c r (e :: l')) ω)
          (V ω) < V ω := hSV
      rw [physClockX_eq_clockX hGT.1 hs0 hx hω hTc] at h1
      exact (min_lt_iff.1 h1).resolve_right (lt_irrefl _)
    have hTc' := hR2ω hold hTc
    have hT'V : ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') (historyTime c r (e :: l')) ω) <
        V' n ω := by
      set m := stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') (schedGTX h13 c r l' a') (V' n)
        (historyTime c r l') ω with hmdef
      have hm : m ≠ ⊤ := ne_top_of_le_ne_top (hV' n ω) (min_le_right _ _)
      have h1 : min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') (schedGTX h13 c r l' a')
          (historyTime c r l' + (historyTime c r (e :: l') - historyTime c r l')) ω) (V' n ω) - m <
          V' n ω - m := by
        have h := hclk'
        change _ < V' n ω - ((m.toNNReal : ℝ≥0) : ℝ≥0∞) at h
        rwa [ENNReal.coe_toNNReal hm] at h
      have h2 : min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') (schedGTX h13 c r l' a')
          (historyTime c r l' + (historyTime c r (e :: l') - historyTime c r l')) ω) (V' n ω) < V' n ω := by
        by_contra hge
        rw [le_antisymm (min_le_right _ _) (not_lt.1 hge)] at h1
        exact lt_irrefl _ h1
      rw [hδ] at h2
      rw [← physClockX_eq_clockX hGT'.1 hs0 hx hω' hTc']
      exact (min_lt_iff.1 h2).resolve_right (lt_irrefl _)
    obtain ⟨hRR, hstart⟩ := hIdω n hold hgood hTc hTV hT'V
    obtain ⟨hβeq, -⟩ := hR4ω n hold hgood hTc hTV hT'V
    have hS := GW2Sdo.stgStartX_eq_clockX hGT.1 hs0 hx hω hTc hTV
    have hRR' : ∀ u ≤ stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) GT V (historyTime c r (e :: l')) ω,
        R' n u ω = R u ω := fun u hu => (hRR u (hS ▸ hu)).symm
    refine ⟨hstart, hRR', ?_⟩
    rw [hβeq]
    congr 4
    refine GW2Wm.recOf_congr_top fun u hu => ?_
    have hle : stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') (schedGTX h13 c r l' a') (V' n)
        (historyTime c r l') ω + u ≤
        stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) GT V (historyTime c r (e :: l')) ω := by
      rw [← hstart]
      exact add_le_add le_rfl hu
    simp only [stgDrv]
    rw [hRR' _ hle, hRR' _ (le_self_add.trans hle)]
  exact claim_step h12 h13 h12₀ h13₀ hR1 c r e l' a a' hr0 hs0 hord hord' hθ hcap _ hδ hδ0 hδcap hGT hA hV ch hu₀
    hβm hE₀ hσa w hGT' hA' hV' ch' rfl rfl hβm' hE₀' cw (length_historyProgram c r l') rfl rfl hIH' hcover hF

/-- **Claim(k) at every time-ordered history** (root `0`): GEOM2's base `GW2Kc.claimAt_nil` and the step
`claimAt_cons`. -/
theorem claimAt_all (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hR1 : PrefixLifeStatement.{u}) (hR2 : PrefixContactStatement.{u}) (hR3 : PrefixLiveCoverStatement.{u})
    (hId : PrefixIdentStatement.{u}) (hR4 : BetaConsStatement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (hr0 : rootPt r.1 = 0) (hs0 : 0 < c.s) {cw : BoundaryWord} (hcw : GW2Kb.IsCfWordOf c.κ c.P c.h c.W c.ζ cw) :
    ∀ l : List (EntryIdx c.Θ c.Q), (historyProgram c r l).Pairwise (fun p q => p.2 < q.2) → ClaimAll c r cw l := by
  intro l
  induction l with
  | nil =>
    intro _ a GT hGT R V hA hV ch hu₀ _ _ hβ hσa w
    exact GW2Kc.claimAt_nil h12 h13 c r a hr0 hs0 hGT hA hV ch hu₀ hcw hβ hσa w
  | cons e l' ih =>
    intro hord
    have hord' : (historyProgram c r l').Pairwise (fun p q => p.2 < q.2) := by
      have h := hord
      rw [GW2Psm.historyProgram_cons, List.pairwise_append] at h
      exact h.1
    exact claimAt_cons h12 h13 h12₀ h13₀ hR1 hR2 hR3 hId hR4 c r hr0 hs0 cw e l' hord (ih hord')

end InteractingSLE.Theorem14.GW2Nw
