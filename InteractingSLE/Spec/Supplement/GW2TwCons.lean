/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2KxStep
import InteractingSLE.Spec.Supplement.GW2NwStep
import InteractingSLE.Spec.Supplement.GW2TvIdent

/-!
# Claim(k) at a root `x`: the induction step at one history, and the induction

Packet PROVE-GW2-RELDET (round 34, decision D58 item 2). GEOM2's `GW2Kx.claim_stepX` is STAGEMEAN's step at a root
`x ∈ {0} ∪ lowerArcRoots`, with STAGEMEAN's inputs. RELDET's round-33 pieces hold at every root `x ≥ 0`, so they
discharge them:

* `prefixLiveCoverStatement`, `prefixIdentStatement`, `betaConsStatement`: NOTHR's verbatim statements
  `GW2Nw.PrefixLiveCoverStatement`, `GW2Nw.PrefixIdentStatement`, `GW2Nw.BetaConsStatement` (from
  `ae_prefixLiveCover`, `ae_prefixIdent`, `ae_beta_cons`);
* **`claimAt_all_root0`**: NOTHR's `GW2Nw.claimAt_all` (root `0`) with every input discharged;
* `ClaimAllX`: `GW2Kx.ClaimAtX` at one history for every candidate, announced version with finite stops, choice
  with GEOM2's word map and word type (NOTHR's `GW2Nw.ClaimAll` in the root-`x` chart);
* **`claimAtX_cons`**: the step at one history at every root `x ∈ {0} ∪ lowerArcRoots`, no open input (NOTHR's
  `claimAt_cons` with `claim_stepX`);
* **`claimAtX_all_of_nil`**: the induction from the base `ClaimAllX c r cw []`;
* `claimAllX_nil_root0`, **`claimAtX_all_root0`**: the base and the induction at the root `0` (GEOM2's
  `GW2Kc.claimAt_nil`, `GW2Kx.claimAtX_iff_claimAt_root0`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31
  GW2Rz GW2Wm Sec5.Prop513Schedule Supp8 Supp8.Q3Stop GW2Psm WholeField LocalSets GW2JointKernel

/-! ### NOTHR's statements of RELDET's pieces -/

/-- NOTHR's `GW2Nw.PrefixLiveCoverStatement` is RELDET's `ae_prefixLiveCover`. -/
theorem prefixLiveCoverStatement : GW2Nw.PrefixLiveCoverStatement.{u} := by
  intro Ω _ _ h13 c r hx hs e l' a a' hθ hcap hTT GT hGT R V hA hV ch R' V' hA' hex' ch' hE₀' w
  exact ae_prefixLiveCover h13 c r hx hs e l' a a' hθ hcap hTT hGT hA hV ch hA' hex' ch' hE₀' w

/-- NOTHR's `GW2Nw.PrefixIdentStatement` is RELDET's `ae_prefixIdent`. -/
theorem prefixIdentStatement : GW2Nw.PrefixIdentStatement.{u} := by
  intro Ω _ _ h13 c r hx hs e l' a a' hθ hcap hTT GT hGT R V hA R' V' hA'
  exact ae_prefixIdent h13 c r hx hs e l' a a' hθ hcap hTT hGT hA hA'

/-- NOTHR's `GW2Nw.BetaConsStatement` is RELDET's `ae_beta_cons`. -/
theorem betaConsStatement : GW2Nw.BetaConsStatement.{u} := by
  intro Ω _ _ h13 c r hx hs cw e l' a a' hθ hcap hord GT hGT R V hA hV R' V' hA' hV' ch ch' hβ hβ'
  exact ae_beta_cons h13 c r hx hs cw e l' a a' hθ hcap hord hGT hA hV hA' hV' ch ch' hβ hβ'

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **Claim(k) at every time-ordered history at the root `0`**, with no open input: NOTHR's `GW2Nw.claimAt_all` with
RELDET's pieces. -/
theorem claimAt_all_root0 (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (hr0 : rootPt r.1 = 0) (hs0 : 0 < c.s) {cw : BoundaryWord}
    (hcw : GW2Kb.IsCfWordOf c.κ c.P c.h c.W c.ζ cw) :
    ∀ l : List (EntryIdx c.Θ c.Q), (historyProgram c r l).Pairwise (fun p q => p.2 < q.2) →
      GW2Nw.ClaimAll c r cw l :=
  GW2Nw.claimAt_all h12 h13 h12₀ h13₀ prefixLifeStatement prefixContactStatement prefixLiveCoverStatement
    prefixIdentStatement betaConsStatement c r hr0 hs0 hcw

/-! ### The root-`x` step -/

/-- **Claim(k) at one history in the root-`x` chart**, for every candidate, announced version with finite stops,
choice with GEOM2's word map (bounded harmonic centring, measurable record event, the candidate's offset) and word
type: NOTHR's `GW2Nw.ClaimAll` with GEOM2's `GW2Kx.ClaimAtX`. -/
def ClaimAllX (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (cw : BoundaryWord) (l : List (EntryIdx c.Θ c.Q)) :
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
    ∀ w : WordType, GW2Kx.ClaimAtX c r l a GT hA ch w

/-- **The Claim(k) step at one history at a root `x ∈ {0} ∪ lowerArcRoots`**, with no open input: Claim(k) at the
prefix gives it at `e :: l'` (GEOM2's `claim_stepX` with RELDET's pieces). -/
theorem claimAtX_cons (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (hroot : rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps)
    (hs0 : 0 < c.s) (cw : BoundaryWord) (e : EntryIdx c.Θ c.Q) (l' : List (EntryIdx c.Θ c.Q))
    (hord : (historyProgram c r (e :: l')).Pairwise (fun p q => p.2 < q.2)) (hIH : ClaimAllX c r cw l') :
    ClaimAllX c r cw (e :: l') := by
  intro a GT hGT R V hA hV ch hu₀ hβm hE₀ hβ hσa w
  have hx : (0 : ℝ) ≤ rootPt r.1 :=
    hroot.elim (fun h => h.ge) fun h => (GW2Sched.pos_of_mem_lowerArcRoots h).le
  obtain ⟨a', ha'θ, ha'cap, -⟩ := exists_candidate c r e.1 e.2 0
  have hord' : (historyProgram c r l').Pairwise (fun p q => p.2 < q.2) := by
    have h := hord
    rw [GW2Psm.historyProgram_cons, List.pairwise_append] at h
    exact h.1
  have hTO : TimeOrdered 0 (historyProgram c r (e :: l')) := Gm.timeOrdered_of_pairwise_lt hord
  have hlt := GW2Nw.historyTime_lt_cons c r e l' hord
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
    exact tsub_lt_self ((GW2Nw.historyTime_pos c r l').trans hlt) (GW2Nw.historyTime_pos c r l')
  have hcap : historyTime c r (e :: l') ≤ historyTime c r l' + candidateCap c r a' := by
    rw [hT, hcapE]
    exact le_add_self
  -- the prefix instances: ROOTX's good set, the canonical exhausting family, GEOM2's word map off `launchBadRec`
  obtain ⟨R', V', hA', -, -, hV', hex'⟩ := GW2Rv.exists_schedVersionsXA_strict h13 c r l' a' hx
  have hGT' := schedGTX_spec h13 c r l' a'
  set ch' := GW2Nw.prefixCh c r l' a' cw ch.u₀ with hch'
  have hβm' : Measurable ch'.β := (GW2Wm.wmChoiceX_targets c.κ cw (rootPt r.1) c.s (historyProgram c r l') _
    (length_historyProgram c r l') (candAngle c r l' a') (launchBadRec c r l' a')ᶜ ch.u₀ (fun _ => ⊥)).1
  have hE₀' : MeasurableSet ch'.E₀ := (measurableSet_launchBadRec c r l' a').compl
  have hIH' : ∀ (n : ℕ) (w' : WordType), GW2Kx.ClaimAtX c r l' a' (schedGTX h13 c r l' a') (hA' n) ch' w' :=
    fun n w' => hIH a' hGT' (hA' n) (hV' n) ch' hu₀ hβm' hE₀' rfl rfl w'
  -- (R3): the prefix live cover
  have hcover := ae_prefixLiveCover h13 c r hx hs0 e l' a a' hθ hcap hTT hGT hA hV ch hA' hex' ch' rfl w
  -- the stage starts, the versions and the words: the prefix identification, (R4) and (R2)
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
    filter_upwards [ae_all_iff.2 fun n => ae_prefixIdent h13 c r hx hs0 e l' a a' hθ hcap hTT hGT hA.1.1 (hA' n).1.1,
      ae_all_iff.2 fun n => ae_beta_cons h13 c r hx hs0 cw e l' a a' hθ hcap hTO hGT hA hV (hA' n) (hV' n) ch ch' hβ
        rfl,
      hEgood, GW2Psm.ae_lt_contactX_all hGT.1 hs0 hx hA.1.1, prefixContactStatement c r e l' a a' hθ hcap, hGT.2.2,
      hGT'.2.2]
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
  exact GW2Kx.claim_stepX h12 h13 h12₀ h13₀ prefixLifeStatement c r e l' a a' hroot hs0 hord hord' hθ hcap _ hδ hδ0
    hδcap hGT hA hV ch hu₀ hβm hE₀ hσa w hGT' hA' hV' ch' rfl rfl hβm' hE₀' cw (length_historyProgram c r l') rfl
    rfl hIH' hcover hF

/-! ### The induction -/

/-- **Claim(k) at every time-ordered history at a root `x ∈ {0} ∪ lowerArcRoots`, from the base** (conditional
helper: the base `ClaimAllX c r cw []` is GEOM2's root-`x` base). -/
theorem claimAtX_all_of_nil (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (hroot : rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps)
    (hs0 : 0 < c.s) (cw : BoundaryWord) (hnil : ClaimAllX c r cw []) :
    ∀ l : List (EntryIdx c.Θ c.Q), (historyProgram c r l).Pairwise (fun p q => p.2 < q.2) → ClaimAllX c r cw l := by
  intro l
  induction l with
  | nil => exact fun _ => hnil
  | cons e l' ih =>
    intro hord
    have hord' : (historyProgram c r l').Pairwise (fun p q => p.2 < q.2) := by
      have h := hord
      rw [GW2Psm.historyProgram_cons, List.pairwise_append] at h
      exact h.1
    exact claimAtX_cons h12 h13 h12₀ h13₀ c r hroot hs0 cw e l' hord (ih hord')

/-- **The base at the root `0` in the root-`x` chart** (GEOM2's `GW2Kc.claimAt_nil`). -/
theorem claimAllX_nil_root0 (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (hr0 : rootPt r.1 = 0) (hs0 : 0 < c.s) {cw : BoundaryWord}
    (hcw : GW2Kb.IsCfWordOf c.κ c.P c.h c.W c.ζ cw) : ClaimAllX c r cw [] := by
  intro a GT hGT R V hA hV ch hu₀ _ _ hβ hσa w
  exact (GW2Kx.claimAtX_iff_claimAt_root0 c r [] a hr0 GT hA ch w).2
    (GW2Kc.claimAt_nil h12 h13 c r a hr0 hs0 hGT hA hV ch hu₀ hcw hβ hσa w)

/-- **Claim(k) in the root-`x` chart at every time-ordered history at the root `0`**, with no open input. -/
theorem claimAtX_all_root0 (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (hr0 : rootPt r.1 = 0) (hs0 : 0 < c.s) {cw : BoundaryWord}
    (hcw : GW2Kb.IsCfWordOf c.κ c.P c.h c.W c.ζ cw) :
    ∀ l : List (EntryIdx c.Θ c.Q), (historyProgram c r l).Pairwise (fun p q => p.2 < q.2) → ClaimAllX c r cw l :=
  claimAtX_all_of_nil h12 h13 h12₀ h13₀ c r (Or.inl hr0) hs0 cw (claimAllX_nil_root0 h12 h13 c r hr0 hs0 hcw)

end InteractingSLE.Theorem14.GW2Rd
