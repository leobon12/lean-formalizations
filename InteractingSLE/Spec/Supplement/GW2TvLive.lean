/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TvCont
import InteractingSLE.Spec.Supplement.GW2SdoNear
import InteractingSLE.Spec.Supplement.GW2RvStrict

/-!
# Claim(k), piece (R3): the prefix live cover

Packet PROVE-GW2-RELDET (round 33), for PROVE-GW2-STAGEMEAN's Claim(k) step (STAGEMEAN's handoff, "For RELDET").
Let `I` be the corrected root-`x` instance of the history `e :: l'` and a current candidate `a` (any good set, any
announced version with finite cap, any choice), and `I'ₙ` the corrected instances of the prefix `(l', a')`, `a'` a
candidate of `e`'s angle whose cap reaches past `e`'s end, along any family of announced versions that exhausts the
clock before the contact (e.g. ROOTX's canonical family `GW2Rv.exists_schedVersionsXA_strict`), with a choice whose
record event is RELDET's `(launchBadRec c r l' a')ᶜ` (GEOM2's `baseWm`, also after `chL`).

**`ae_prefixLiveCover`**: almost surely on `I`'s live event with a positive stage cap, there is `n` such that the
prefix record of `I'ₙ` is live (`I'ₙ.srecX ∈ I'ₙ.E`) and the prefix stage clock at the entry's duration
`δ = T − T'` is below the prefix stage cap. Ingredients:

* the positive cap puts the history time before the current contact (STAGEMEAN's `ae_lt_contactX_all`), hence before
  the prefix contact (R2, `prefixContactStatement`);
* the history's success (from the record, `augRec_mem_succRec_iff`) gives the prefix's success and, by R1
  (`prefixLifeStatement`), a positive prefix lifetime, so the prefix record is off `launchBadRec`
  (`ae_mem_launchBadRec_iff`);
* the exhaustion gives `n` with the prefix clock at `T` below `V'ₙ`; then the prefix stage start is below `V'ₙ`
  (SDE's `mem_aliveRecX`) and the prefix stage clock at `δ` is below the stage cap.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31
  GW2Rz GW2Sde Supp8.Q3Stop

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **(R3) The prefix live cover**: almost surely on the live event of the history's instance with a positive stage
cap, some prefix instance of an exhausting version family is live with its stage clock at the entry's duration
below its stage cap. -/
theorem ae_prefixLiveCover (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) (e : EntryIdx c.Θ c.Q) (l' : List (EntryIdx c.Θ c.Q)) (a a' : ℕ)
    (hθ : candidateAngle c r a' = (e.1 : ℝ))
    (hcap : historyTime c r (e :: l') ≤ historyTime c r l' + candidateCap c r a')
    (hTT : historyTime c r l' ≤ historyTime c r (e :: l'))
    {GT : Set Ω}
    (hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) (schedTr c r (e :: l') a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r (e :: l') a) (schedTr c r (e :: l') a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤) (ch : GW2Sdh.SchedChoice Ω)
    {R' : ℕ → ℝ≥0 → Ω → ℝ} {V' : ℕ → Ω → ℝ≥0∞}
    (hA' : ∀ n, IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l' a') (schedTr c r l' a') c.α (R' n)
      (V' n))
    (hex' : ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → ∀ t : ℝ≥0,
      (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l' a') c.α ω →
      ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') t ω) < V' n ω)
    (ch' : GW2Sdh.SchedChoice Ω) (hE₀' : ch'.E₀ = (launchBadRec c r l' a')ᶜ) (w : WordType) :
    ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).E
        ((GW2Rv.schedInstSX c r (e :: l') a GT hA ch).srecX c r (e :: l') (rootPt r.1)) →
      (0 : ℝ≥0∞) < (GW2Rv.schedInstSX c r (e :: l') a GT hA ch).capX c (rootPt r.1) ω →
      ∃ n, (GW2Rv.schedInstSX c r l' a' (schedGTX h13 c r l' a') (hA' n) ch').srecX c r l' (rootPt r.1) ω ∈
          (GW2Rv.schedInstSX c r l' a' (schedGTX h13 c r l' a') (hA' n) ch').E ∧
        (GW2Rv.schedInstSX c r l' a' (schedGTX h13 c r l' a') (hA' n) ch').clockX c (rootPt r.1)
            (historyTime c r (e :: l') - historyTime c r l') ω <
          (GW2Rv.schedInstSX c r l' a' (schedGTX h13 c r l' a') (hA' n) ch').capX c (rootPt r.1) ω := by
  obtain ⟨hGT', -, hGTae'⟩ := schedGTX_spec h13 c r l' a'
  have hρ : ∀ᵐ ω ∂c.P, ∀ n, V' n ω = (hA' n).1.2.choose (cfRec c.s c.W c.ζ ω, fun u => R' n u ω) :=
    ae_all_iff.2 fun n => (hA' n).1.2.choose_spec.2.2
  filter_upwards [GW2Psm.ae_lt_contactX_all hGT.1 hs hx hA.1.1, hGT.2.2, hGTae',
    prefixContactStatement c r e l' a a' hθ hcap,
    ae_mem_launchBadRec_iff c r l' a' h13, hex', hρ] with ω hcon hGTω hGTω' hcont hbad hexω hρω hlive hcap0
  -- the history's success and the good record, from the live record
  obtain ⟨⟨⟨-, hsucc⟩, halive⟩, -⟩ := hlive
  have hold : oldSuccess c r (e :: l') ω := (GW2Sdi.augRec_mem_succRec_iff c r (e :: l') _ ω).1 hsucc
  have hgood : cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s := by
    have h := halive.1
    have hd := (augDec_specX (x₀ := rootPt r.1) (s := c.s) (W := schedW c r (e :: l') a) (Wα := c.W) (ζα := c.ζ)
      (GT := GT) (V := V) (T := historyTime c r (e :: l')) (R := R) (rec := cfRec c.s c.W c.ζ)
      (x := stageEncRec c r (e :: l')) (ω := ω) (by rw [stgRecDec_stageEncRec]; rfl) (hA.1.1.2.1 ω)
      (hA.1.1.2.2.1 ω)).1
    change augσ _ (augRec (stageEncRec c r (e :: l'))
      (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) GT V (historyTime c r (e :: l')) R) ω) ∈ _ at h
    rwa [hd] at h
  have hω := hGTω.2 hgood
  have hω' := hGTω'.2 hgood
  have hold' := GW2Psm.oldSuccess_of_cons c r e l' ω hold
  -- the history time is before both contacts
  have hstart : min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) GT (historyTime c r (e :: l')) ω)
      (V ω) < V ω := by
    have h := hcap0
    change (0 : ℝ≥0∞) < V ω - ((min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) GT
      (historyTime c r (e :: l')) ω) (V ω)).toNNReal : ℝ≥0∞) at h
    rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top (hV ω) (min_le_right _ _))] at h
    exact tsub_pos_iff_lt.1 h
  have hTc := hcon hω (historyTime c r (e :: l')) hstart
  have hTc' := hcont hold hTc
  have hT'c' : (historyTime c r l' : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l' a') c.α ω :=
    (ENNReal.coe_le_coe.2 hTT).trans_lt hTc'
  -- the prefix version covering the clock at `T`
  obtain ⟨n, hn⟩ := (hexω hgood (historyTime c r (e :: l')) hTc').exists
  obtain ⟨-, hmono, -⟩ := clockX_props hGT' hs hx hω'
  have hle : ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') (historyTime c r l') ω) ≤
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') (historyTime c r (e :: l')) ω) :=
    hmono hT'c' hTc' hTT
  have hcl : ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') (historyTime c r l') ω) <
      V' n ω := hle.trans_lt hn
  refine ⟨n, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · -- off `launchBadRec`: the prefix candidate lives past the entry's duration
    rw [hE₀']
    intro hmem
    have hlife := prefixLifeStatement c r e l' a' hθ hcap ω hold
    rw [(hbad hold' _).1 hmem] at hlife
    exact absurd hlife (not_lt.2 zero_le)
  · exact (GW2Sdi.augRec_mem_succRec_iff c r l' _ ω).2 hold'
  · -- the prefix stage start is below the prefix cap
    refine GW2Sdo.mem_aliveRecX (hA' n).1.2.choose_spec.2.1 ?_ ((hA' n).1.1.2.1 ω) ((hA' n).1.1.2.2.1 ω) hgood
      (hρω n) ?_
    · rw [stgRecDec_stageEncRec]
      rfl
    · show (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') (schedGTX h13 c r l' a') (V' n)
        (historyTime c r l') ω : ℝ≥0∞) < V' n ω
      rw [GW2Sdo.stgStartX_eq_clockX hGT' hs hx hω' hT'c' hcl]
      exact hcl
  · -- the prefix stage clock at the entry's duration is below the prefix stage cap
    have hphT := physClockX_eq_clockX hGT' hs hx hω' hTc'
    have hphT' := physClockX_eq_clockX hGT' hs hx hω' hT'c'
    change min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') (schedGTX h13 c r l' a')
        (historyTime c r l' + (historyTime c r (e :: l') - historyTime c r l')) ω) (V' n ω) -
        min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') (schedGTX h13 c r l' a') (historyTime c r l') ω)
          (V' n ω) <
      V' n ω - ((min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') (schedGTX h13 c r l' a')
        (historyTime c r l') ω) (V' n ω)).toNNReal : ℝ≥0∞)
    rw [add_tsub_cancel_of_le hTT, hphT, hphT', min_eq_left hn.le, min_eq_left hcl.le,
      ENNReal.coe_toNNReal ENNReal.ofReal_ne_top]
    exact (ENNReal.cancel_of_ne ENNReal.ofReal_ne_top).tsub_lt_tsub_right_of_le hle hn

end InteractingSLE.Theorem14.GW2Rd
