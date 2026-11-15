/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TvWord

/-!
# Claim(k): the prefix identification at one sample (version conversion and stage starts)

Packet PROVE-GW2-RELDET (round 33), for PROVE-GW2-STAGEMEAN's Claim(k) step: the two facts of the step's "prefix
identification at one sample" (STAGEMEAN's item 2(i)) that the pieces R1–R4 do not state on their own.

**`ae_prefixIdent`**: almost surely, at a sample with the history's success, a good record, the history time `T`
before the current contact, and the clocks at `T` below both caps,
* the history's version `R` and the prefix's version `R'` agree up to the clock at `T` (ROOTX's
  `version_eq_of_drv_eq`, with the explored drivers agreeing on `[0, T]`, `ae_schedW_schedTr_cons_eq`);
* the prefix stage start plus the prefix stage clock at the entry's duration is the history's stage start (the stage
  chart's time in `claim_of_prefix_pair`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31
  GW2Rz GW2Wm Sec5.Prop513Schedule

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The prefix identification at one sample**: the two versions agree up to the clock at the entry's end, and the
prefix stage start plus the prefix stage clock at the entry's duration is the history's stage start. -/
theorem ae_prefixIdent (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) (e : EntryIdx c.Θ c.Q) (l' : List (EntryIdx c.Θ c.Q))
    (a a' : ℕ) (hθ : candidateAngle c r a' = (e.1 : ℝ))
    (hcap : historyTime c r (e :: l') ≤ historyTime c r l' + candidateCap c r a')
    (hTT : historyTime c r l' ≤ historyTime c r (e :: l')) {GT : Set Ω}
    (hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) (schedTr c r (e :: l') a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r (e :: l') a) (schedTr c r (e :: l') a) c.α R V)
    {R' : ℝ≥0 → Ω → ℝ} {V' : Ω → ℝ≥0∞}
    (hA' : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l' a') (schedTr c r l' a') c.α R' V') :
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
          stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) GT V (historyTime c r (e :: l')) ω := by
  obtain ⟨hGT', -, hGTae'⟩ := schedGTX_spec h13 c r l' a'
  filter_upwards [ae_schedW_schedTr_cons_eq h13 c r, hGT.2.2, hGTae', prefixContactStatement c r e l' a a' hθ hcap,
    GW2Ru.versionAtX_of_isRelVersionX hA, GW2Ru.versionAtX_of_isRelVersionX hA']
    with ω hcons hGTω hGTω' hcont hVA hVA' hold hgood hTc hVT hV'T
  set T := historyTime c r (e :: l') with hTdef
  set T' := historyTime c r l' with hT'def
  obtain ⟨hdrv, -, -, -⟩ := hcons e l' a a' hθ hcap hold
  have hω := hGTω.2 hgood
  have hω' := hGTω'.2 hgood
  have hTc' := hcont hold hTc
  have hT'c' : (T' : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l' a') c.α ω :=
    (ENNReal.coe_le_coe.2 hTT).trans_lt hTc'
  obtain ⟨-, hmono, hzero⟩ := clockX_props hGT.1 hs hx hω
  obtain ⟨-, hmono', -⟩ := clockX_props hGT' hs hx hω'
  refine ⟨fun u hu => ?_, ?_⟩
  · rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ T) with hT0 | hT0
    · have hc0 : (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) T ω).toNNReal = 0 := by
        rw [← hT0]
        have h0 := hzero
        rw [ENNReal.ofReal_eq_zero] at h0
        exact Real.toNNReal_of_nonpos h0
      have hu0 : u = 0 := le_antisymm (hc0 ▸ hu) zero_le
      rw [hu0, hA.2.2.1 ω, hA'.2.2.1 ω]
    · exact GW2Ru.version_eq_of_drv_eq hGT.1 hGT' hs hx hω hω' (hVA hgood) (hVA' hgood) hT0 hTc hTc' hdrv hVT
        hV'T u hu
  · have hclk : ∀ t ≤ T, clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') t ω =
        clockX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) t ω := fun t ht =>
      (GW2Sdo.clockX_congr fun u hu => hdrv u (hu.trans ht)).symm
    have hle' : ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') T' ω) ≤
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') T ω) := hmono' hT'c' hTc' hTT
    have hlt' := hle'.trans_lt hV'T
    have hphT := physClockX_eq_clockX hGT' hs hx hω' hTc'
    have hphT' := physClockX_eq_clockX hGT' hs hx hω' hT'c'
    have hle : (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) T' ω).toNNReal ≤
        (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) T ω).toNNReal :=
      Real.toNNReal_le_toNNReal ((ENNReal.ofReal_le_ofReal_iff (RootJ32.forwardCapacity_nonneg _ _ _ _)).1
        (hmono ((ENNReal.coe_le_coe.2 hTT).trans_lt hTc) hTc hTT))
    rw [GW2Sdo.stgStartX_eq_clockX hGT' hs hx hω' hT'c' hlt', GW2Sdo.stgStartX_eq_clockX hGT.1 hs hx hω hTc hVT]
    unfold stgClockX stgStartMX
    rw [add_tsub_cancel_of_le hTT, hphT, hphT', min_eq_left hV'T.le, min_eq_left hlt'.le]
    change (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') T' ω).toNNReal +
      ((((clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') T ω).toNNReal : ℝ≥0) : ℝ≥0∞) -
        (((clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') T' ω).toNNReal : ℝ≥0) : ℝ≥0∞)).toNNReal = _
    rw [← ENNReal.coe_sub, ENNReal.toNNReal_coe, hclk T le_rfl, hclk T' hTT, add_tsub_cancel_of_le hle]

end InteractingSLE.Theorem14.GW2Rd
