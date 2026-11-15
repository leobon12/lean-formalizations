/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NwStep
import InteractingSLE.Spec.Wire.T14CurTop

/-!
# The `mean` statement from Claim(k) (root `0`, strictly time-ordered histories)

Packet PROVE-GW2-NOTHR (round 5, decision D52 revised). STAGEMEAN's `GW2Psm.meanX_inst` turns Claim(k) into the
`mean` statement `stageMeanAtX`, given a version stopped at the candidate's stop (decision D49 (A)). Its inputs are:
`hclaim` (Claim(k), `claimAt_all`); `hfar` (`GW2Psm.ae_farR_srecX`); and `hcapb`/`hlife` from the stop property
(`GW2Psm.lt_stop_of_clockX`, `capb_of_stop`, `life_of_stop`).

* **`meanX_hist`**: `stageMeanAtX` at ROOTX's root-`0` instance of every strictly time-ordered history, every
  candidate, every announced version stopped at the candidate's stop, every choice with GEOM2's word map, every word
  type and every stage time;
* **`cfWordCanon`**, **`isCfWordOf_cfWordCanon`**: a counterflow word of every source (GEOM2's `exists_isCfWordOf`);
* **`hmeanF_root0`**: the `hmeanF` binder of Theorem 1.4's current top, at the top's instances
  `T14Cur.instC ver (T14Cur.baseWm cw)`. It holds at roots `0` and strictly time-ordered histories, for version
  families stopped at the candidate's stop and counterflow words `cw`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Nw

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31
  GW2Rz GW2Wm GW2Rd Sec5.Prop513Schedule Supp8 Supp8.Q3Stop GW2Psm WholeField LocalSets GW2JointKernel

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The `mean` statement at a root-`0` instance of a strictly time-ordered history** (D49: the version is stopped
at the candidate's stop on the live event). -/
theorem meanX_hist (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hR1 : PrefixLifeStatement.{u}) (hR2 : PrefixContactStatement.{u}) (hR3 : PrefixLiveCoverStatement.{u})
    (hId : PrefixIdentStatement.{u}) (hR4 : BetaConsStatement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (hr0 : rootPt r.1 = 0) (hs0 : 0 < c.s) {cw : BoundaryWord} (hcw : GW2Kb.IsCfWordOf c.κ c.P c.h c.W c.ζ cw)
    (l : List (EntryIdx c.Θ c.Q)) (hord : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2)) (a : ℕ)
    {GT : Set Ω} (hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤) (ch : GW2Sdh.SchedChoice Ω) (hu₀ : IsBoundedHarmonicExtension c.b c.jumps ch.u₀)
    (hkc : ch.kc = chiC c.κ) (hβm : Measurable ch.β) (hE₀ : MeasurableSet ch.E₀)
    (hβ : ch.β = GW2Wm.schedWordMapX c.κ cw (rootPt r.1) c.s (historyProgram c r l) ((entryList l).length + 1)
      (length_historyProgram c r l) (candAngle c r l a))
    (hσa : ch.σa = specOffset c.κ + candAngle c r l a * chiC c.κ) (w : WordType)
    (hVd : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r l a GT hA ch).E
        ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) →
      V ω ≤ physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (historyTime c r l + candStop c r l a ω) ω)
    (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens)
    (hg : IsLocalSetMean ((GW2Rv.schedInstSX c r l a GT hA ch).B t) (centredField c.h ch.u₀) c.P g)
    (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂c.P, stageMeanAtX (GW2Rv.schedInstSX c r l a GT hA ch) c r l (rootPt r.1) w t ψ ω (g ω) := by
  have hx : (0 : ℝ) ≤ rootPt r.1 := by rw [hr0]
  have hstop : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r l a GT hA ch).E
        ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) →
      (GW2Rv.schedInstSX c r l a GT hA ch).clockX c (rootPt r.1) t ω <
        (GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1) ω → t < candStop c r l a ω := by
    filter_upwards [hVd] with ω hω hlive hlt
    exact lt_stop_of_clockX c r l a hs0 hx hGT.1 hA hV ch (hω hlive) hlt
  have hcapb : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r l a GT hA ch).E
        ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) →
      (GW2Rv.schedInstSX c r l a GT hA ch).clockX c (rootPt r.1) t ω <
        (GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1) ω → t < candidateCap c r a := by
    filter_upwards [hstop] with ω hω hlive hlt
    exact capb_of_stop (hω hlive hlt)
  have hlife : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r l a GT hA ch).E
        ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) →
      (GW2Rv.schedInstSX c r l a GT hA ch).clockX c (rootPt r.1) t ω <
        (GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1) ω → (t : ℝ≥0∞) < candLife c r l a ω := by
    filter_upwards [hstop] with ω hω hlive hlt
    exact life_of_stop (hω hlive hlt)
  have hfar := ae_farR_srecX c r l a hGT hA hV ch cw (length_historyProgram c r l) (candAngle c r l a) hβ w
  have hclaim := claimAt_all h12 h13 h12₀ h13₀ hR1 hR2 hR3 hId hR4 c r hr0 hs0 hcw l hord a hGT hA hV ch hu₀ hβm hE₀
    hβ hσa w
  exact meanX_inst h12 h13 h12₀ h13₀ c r l a hr0 hord hs0 hGT hA hV ch hu₀ hkc hβm hE₀ w t hcapb hlife hfar hclaim
    g hg ψ

/-- **A counterflow word of every source** (GEOM2's `GW2Kb.exists_isCfWordOf` at the source's counterflow). -/
def cfWordCanon : Wire.T14Cur.CfWord.{u} := fun _ _ _ c _ => (GW2Kb.exists_isCfWordOf c.hcf).choose

theorem isCfWordOf_cfWordCanon (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) : GW2Kb.IsCfWordOf c.κ c.P c.h c.W c.ζ (cfWordCanon Ω c r) :=
  (GW2Kb.exists_isCfWordOf c.hcf).choose_spec

/-- **The `hmeanF` binder of Theorem 1.4's current top at roots `0` and strictly time-ordered histories**, at the
top's instances `T14Cur.instC ver (T14Cur.baseWm cw)`. It holds for every version family stopped at the candidate's
stop (D49 (A)) and every word `cw` of the source's counterflow, from RELDET's pieces. -/
theorem hmeanF_root0 (hR1 : PrefixLifeStatement.{u}) (hR2 : PrefixContactStatement.{u})
    (hR3 : PrefixLiveCoverStatement.{u}) (hId : PrefixIdentStatement.{u}) (hR4 : BetaConsStatement.{u})
    (ver : GW2Rv.SchedVerXFamily.{u}) (cw : Wire.T14Cur.CfWord.{u})
    (hcw : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), GW2Kb.IsCfWordOf c.κ c.P c.h c.W c.ζ (cw Ω c r))
    (hVd : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      (historyProgram c r l).Pairwise (fun p q => p.2 < q.2) → (h : GW2Rv.GoodRoot c r) → ∀ (a n : ℕ)
      (w : WordType), ∀ᵐ ω ∂c.P,
        ω ∈ liveEvRec c.κ w (Wire.T14Cur.instC ver (Wire.T14Cur.baseWm cw) Ω c r l a n h).β
          (Wire.T14Cur.instC ver (Wire.T14Cur.baseWm cw) Ω c r l a n h).E
          ((Wire.T14Cur.instC ver (Wire.T14Cur.baseWm cw) Ω c r l a n h).srecX c r l (rootPt r.1)) →
        (ver Ω c r l a).V n ω ≤ physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a)
          (schedGTX Wire.T14Asm7.h13 c r l a) (historyTime c r l + candStop c r l a ω) ω) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)), (historyProgram c r l).Pairwise (fun p q => p.2 < q.2) →
      (h : GW2Rv.GoodRoot c r) → rootPt r.1 = 0 → ∀ (a n : ℕ) (w : WordType) (t : ℝ≥0)
      (g : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean ((Wire.T14Cur.instC ver (Wire.T14Cur.baseWm cw) Ω c r l a n h).B t)
        (centredField c.h (Wire.T14Cur.instC ver (Wire.T14Cur.baseWm cw) Ω c r l a n h).u₀) c.P g →
      ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
        stageMeanAtX (Wire.T14Cur.instC ver (Wire.T14Cur.baseWm cw) Ω c r l a n h) c r l (rootPt r.1) w t ψ ω
          (g ω) := by
  intro Ω _ _ c r l hord h hr0 a n w t g hg ψ
  have hTO : TimeOrdered 0 (historyProgram c r l) := Gm.timeOrdered_of_pairwise_lt hord
  have hβ : (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a).β = GW2Wm.schedWordMapX c.κ (cw Ω c r)
      (rootPt r.1) c.s (historyProgram c r l) ((entryList l).length + 1) (length_historyProgram c r l)
      (candAngle c r l a) := by
    rw [GW2Rd.schedChoiceLinesX_β Wire.T14Asm7.h12 Wire.T14Asm7.h13 (Wire.T14Cur.baseWm cw) c r l a]
    rfl
  have hσa : (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a).σa =
      specOffset c.κ + candAngle c r l a * chiC c.κ := by
    show (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 (Wire.T14Cur.baseWm cw) Ω c r l a).σa = _
    unfold GW2Rd.schedChoiceLinesX
    split_ifs
    rfl
  have hkc : (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a).kc = chiC c.κ := by
    show (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 (Wire.T14Cur.baseWm cw) Ω c r l a).kc = _
    unfold GW2Rd.schedChoiceLinesX
    split_ifs
    rfl
  have hu₀ := GW2Rd.schedChoiceLinesX_u₀ Wire.T14Asm7.h12 Wire.T14Asm7.h13 (Wire.T14Cur.baseWm cw) c r l a hTO
  have hβm : Measurable (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a).β := by
    rw [GW2Rd.schedChoiceLinesX_β Wire.T14Asm7.h12 Wire.T14Asm7.h13 (Wire.T14Cur.baseWm cw) c r l a]
    exact (Wire.T14Cur.hword_baseWm cw Ω c r l hTO h a).1
  have hE₀ : MeasurableSet (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a).E₀ := by
    rw [GW2Rd.schedChoiceLinesX_E₀ Wire.T14Asm7.h12 Wire.T14Asm7.h13 (Wire.T14Cur.baseWm cw) c r l a]
    exact Wire.T14Cur.hE₀_baseWm cw Ω c r l hTO h a
  exact meanX_hist Wire.T14Asm7.h12 Wire.T14Asm7.h13 Wire.T14Asm7.h12₀ Wire.T14Asm7.h13₀ hR1 hR2 hR3 hId hR4 c r
    hr0 h.2 (hcw Ω c r) l hord a (schedGTX_spec Wire.T14Asm7.h13 c r l a) ((ver Ω c r l a).isA h.1 n)
    ((ver Ω c r l a).fin n) (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a) hu₀ hkc hβm hE₀ hβ hσa w
    (hVd Ω c r l hord h a n w) t g hg ψ

end InteractingSLE.Theorem14.GW2Nw
