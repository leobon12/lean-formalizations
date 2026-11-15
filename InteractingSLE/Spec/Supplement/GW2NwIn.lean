/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmStepA
import InteractingSLE.Spec.Supplement.GW2KcNil
import InteractingSLE.Spec.Supplement.GW2PsmMeanI
import InteractingSLE.Spec.Supplement.GW2PsmCapB
import InteractingSLE.Spec.Supplement.GW2PsmFarX
import InteractingSLE.Spec.Supplement.GW2RvStrict
import InteractingSLE.Spec.Supplement.GW2TpRoot

/-!
# Claim(k)'s induction wrapper: RELDET's step inputs as consumed statements

Packet PROVE-GW2-NOTHR (round 5, decision D52 revised). The induction over the history (GEOM2's base
`GW2Kc.claimAt_nil` + STAGEMEAN's step `GW2Psm.claim_step`) consumes RELDET's pieces (STAGEMEAN's handoff, R1–R4).
(R1) and (R2) are the landed statements `GW2Psm.PrefixLifeStatement` and `GW2Psm.PrefixContactStatement`. The other
three are RELDET's delivered lemmas (`GW2Tv*`, not yet landed). They are stated here verbatim, so RELDET's lemmas are
their proofs:

* **`PrefixLiveCoverStatement`** (R3, `GW2Rd.ae_prefixLiveCover`);
* **`PrefixIdentStatement`** (the stage starts and the versions agree; `GW2Rd.ae_prefixIdent`);
* **`BetaConsStatement`** (R4, the word recursion at the instance records; `GW2Rd.ae_beta_cons`).
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
  GW2Rz GW2Wm GW2Rd Sec5.Prop513Schedule Supp8 Supp8.Q3Stop

/-- **RELDET's (R3) prefix live cover**: the statement of `GW2Rd.ae_prefixLiveCover`, verbatim. -/
def PrefixLiveCoverStatement : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (_hx : 0 ≤ rootPt r.1) (_hs : 0 < c.s) (e : EntryIdx c.Θ c.Q) (l' : List (EntryIdx c.Θ c.Q)) (a a' : ℕ)
      (_hθ : candidateAngle c r a' = (e.1 : ℝ))
      (_hcap : historyTime c r (e :: l') ≤ historyTime c r l' + candidateCap c r a')
      (_hTT : historyTime c r l' ≤ historyTime c r (e :: l'))
      {GT : Set Ω}
      (_hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) (schedTr c r (e :: l') a) c.α ω) ∧
        MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
      {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
      (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r (e :: l') a) (schedTr c r (e :: l') a) c.α R V)
      (_hV : ∀ ω, V ω ≠ ⊤) (ch : GW2Sdh.SchedChoice Ω)
      {R' : ℕ → ℝ≥0 → Ω → ℝ} {V' : ℕ → Ω → ℝ≥0∞}
      (hA' : ∀ n, IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l' a') (schedTr c r l' a') c.α (R' n)
        (V' n))
      (_hex' : ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → ∀ t : ℝ≥0,
        (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l' a') c.α ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') t ω) < V' n ω)
      (ch' : GW2Sdh.SchedChoice Ω) (_hE₀' : ch'.E₀ = (launchBadRec c r l' a')ᶜ) (w : WordType),
  ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).E
          ((GW2Rv.schedInstSX c r (e :: l') a GT hA ch).srecX c r (e :: l') (rootPt r.1)) →
        (0 : ℝ≥0∞) < (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).capX c (rootPt r.1) ω →
        ∃ n, (GW2Rv.schedInstSX c r l' a' (schedGTX h13 c r l' a') (hA' n) ch').srecX c r l' (rootPt r.1) ω ∈
            (GW2Rv.schedInstSX c r l' a' (schedGTX h13 c r l' a') (hA' n) ch').E ∧
          (GW2Rv.schedInstSX c r l' a' (schedGTX h13 c r l' a') (hA' n) ch').clockX c (rootPt r.1)
              (historyTime c r (e :: l') - historyTime c r l') ω <
            (GW2Rv.schedInstSX c r l' a' (schedGTX h13 c r l' a') (hA' n) ch').capX c (rootPt r.1) ω

/-- **RELDET's prefix identification (stage starts and versions)**: the statement of `GW2Rd.ae_prefixIdent`,
verbatim. -/
def PrefixIdentStatement : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (_hx : 0 ≤ rootPt r.1) (_hs : 0 < c.s) (e : EntryIdx c.Θ c.Q) (l' : List (EntryIdx c.Θ c.Q))
      (a a' : ℕ) (_hθ : candidateAngle c r a' = (e.1 : ℝ))
      (_hcap : historyTime c r (e :: l') ≤ historyTime c r l' + candidateCap c r a')
      (_hTT : historyTime c r l' ≤ historyTime c r (e :: l')) {GT : Set Ω}
      (_hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) (schedTr c r (e :: l') a) c.α ω) ∧
        MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
      {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
      (_hA : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r (e :: l') a) (schedTr c r (e :: l') a) c.α R V)
      {R' : ℝ≥0 → Ω → ℝ} {V' : Ω → ℝ≥0∞}
      (_hA' : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l' a') (schedTr c r l' a') c.α R' V'),
  ∀ᵐ ω ∂c.P, oldSuccess c r (e :: l') ω → cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
        (historyTime c r (e :: l') : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r (e :: l') a) c.α ω →
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) (historyTime c r (e :: l')) ω) <
          V ω →
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') (historyTime c r (e :: l')) ω) < V' ω →
        (∀ u ≤ (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) (historyTime c r (e :: l')) ω).toNNReal,
            R u ω = R' u ω) ∧
          stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') (schedGTX h13 c r l' a') V' (historyTime c r l') ω +
              (stgClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') (schedGTX h13 c r l' a') V' (historyTime c r l')
                (historyTime c r (e :: l') - historyTime c r l') ω).toNNReal =
            stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) GT V (historyTime c r (e :: l')) ω

/-- **RELDET's (R4) word recursion**: the statement of `GW2Rd.ae_beta_cons`, verbatim. -/
def BetaConsStatement : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (_hx : 0 ≤ rootPt r.1) (_hs : 0 < c.s) (cw : BoundaryWord) (e : EntryIdx c.Θ c.Q) (l' : List (EntryIdx c.Θ c.Q))
      (a a' : ℕ) (_hθ : candidateAngle c r a' = (e.1 : ℝ))
      (_hcap : historyTime c r (e :: l') ≤ historyTime c r l' + candidateCap c r a')
      (_hord : TimeOrdered 0 (historyProgram c r (e :: l'))) {GT : Set Ω}
      (_hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) (schedTr c r (e :: l') a) c.α ω) ∧
        MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
      {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
      (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r (e :: l') a) (schedTr c r (e :: l') a) c.α R V)
      (_hV : ∀ ω, V ω ≠ ⊤) {R' : ℝ≥0 → Ω → ℝ} {V' : Ω → ℝ≥0∞}
      (hA' : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l' a') (schedTr c r l' a') c.α R' V')
      (_hV' : ∀ ω, V' ω ≠ ⊤) (ch ch' : GW2Sdh.SchedChoice Ω)
      (_hβ : ch.β = schedWordMapX c.κ cw (rootPt r.1) c.s (historyProgram c r (e :: l'))
        ((entryList (e :: l')).length + 1) (length_historyProgram c r (e :: l')) (candAngle c r (e :: l') a))
      (_hβ' : ch'.β = schedWordMapX c.κ cw (rootPt r.1) c.s (historyProgram c r l') ((entryList l').length + 1)
        (length_historyProgram c r l') (candAngle c r l' a')),
  ∀ᵐ ω ∂c.P, oldSuccess c r (e :: l') ω → cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
        (historyTime c r (e :: l') : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r (e :: l') a) c.α ω →
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) (historyTime c r (e :: l')) ω) <
          V ω →
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') (historyTime c r (e :: l')) ω) < V' ω →
        ch.β ((GW2Rv.schedInstSX c r (e :: l') a GT hA ch).srecX c r (e :: l') (rootPt r.1) ω) =
            upW (candAngle c r (e :: l') a * chiC c.κ)
              (stopWord c.κ (baseWordX c.κ cw (rootPt r.1) c.s (historyProgram c r l') ((entryList l').length + 1)
                  (length_historyProgram c r l')
                  ((GW2Rv.schedInstSX c r l' a' (schedGTX h13 c r l' a') hA' ch').srecX c r l' (rootPt r.1) ω),
                (e.1 : ℝ),
                recOf ((((GW2Rv.schedInstSX c r l' a' (schedGTX h13 c r l' a') hA' ch').clockX c (rootPt r.1)
                    (historyTime c r (e :: l') - historyTime c r l') ω).toNNReal : ℝ≥0) : ℝ≥0∞)
                  (fun u => stgDrv (fun v => R v ω) (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a')
                    (schedGTX h13 c r l' a') V' (historyTime c r l') ω) u, ⊤))) ∧
          ch'.β ((GW2Rv.schedInstSX c r l' a' (schedGTX h13 c r l' a') hA' ch').srecX c r l' (rootPt r.1) ω) =
            upW ((e.1 : ℝ) * chiC c.κ)
              (baseWordX c.κ cw (rootPt r.1) c.s (historyProgram c r l') ((entryList l').length + 1)
                (length_historyProgram c r l')
                ((GW2Rv.schedInstSX c r l' a' (schedGTX h13 c r l' a') hA' ch').srecX c r l' (rootPt r.1) ω))

end InteractingSLE.Theorem14.GW2Nw
