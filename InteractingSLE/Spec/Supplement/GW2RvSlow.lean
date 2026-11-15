/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RvDrv
import InteractingSLE.Spec.Supplement.GW2RvInst
import InteractingSLE.Spec.Supplement.GW2BkExh


/-!
# GW2 at a root `x`: decision D3's slow stage variables (BUF's S1 and S3 at a root)

Packet PROVE-GW2-ROOTX, round 4. BUF's `GW2BiInst`, `GW2BiCov`, `GW2BiSlowStop`, `GW2BiSlowFam`, `GW2BkExh` at the
root point `x = rootPt r.1 ≥ 0`, on the corrected root-`x` instance `GW2Rv.schedInstSX`:

* `live_of_gain_pos`, `ae_rootCapAt_eq_clockX` (J32's capacity reader is the root-`x` clock before the buffer),
  **`ae_physClockX_eq_histCap`**, **`ae_stgStartX_eq_histCap`**, **`ae_j32DriverId_schedInstSX`**,
  `ae_histCap_add_gainX`, `ae_gain_le_sub_of_ltX`, **`ae_stopCovers_eventuallyX`**;
* `lowCapStopX` (a lower cap `Vlow − start` as a root-`x` stage stop), **`lowCapStopX_good`**;
* `ae_version_eq_leX`, `ae_lowCap_rule_eqX`;
* `slowInstX`, `slowCapStopX`, `slowStageVarX` (decision D3's slow variable `n`: the instance of version `n + 1` with
  the cap `V n` as its stop), **`lowCapStopX_good_family`** (strict caps on the good records),
  `ae_slowStageVarX_stop_eq`, **`vDriverIdN_slowStageVarX`**, `vStopCoversN_slowStageVarX`,
  **`vStopExhaustsN_slowStageVarX`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Rv

open Exist Staged StagedLaw Restart Supp8 Supp8.GB6 Supp8.GB6.RelDrv GW2TipSystem GW2TipSystem.RootC24 GW2Rd
  GW2Rz GW2Sde GW2Sdi GW2Sdx GW2Sdy GW2Bh GW2KM2 GW2TipSystem.SchedRule Supp8.GB6.HullId

variable {Ω : Type u} [MeasurableSpace Ω]

/-- A positive gain makes the sample live. -/
theorem live_of_gain_pos {Ω' : Type u} [MeasurableSpace Ω'] (c : SourceData Ω') (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) {ξ : Ω'} (hgain : 0 < GW2Sdg.rootGain c r l a ξ) :
    0 < (RootJ31.sourceSample c r l a ξ).1 := by
  rw [GW2Sdg.sourceSample_fst]
  exact ENNReal.mul_pos (pow_ne_zero _ (by norm_num)) (ENNReal.coe_ne_zero.2 hgain.ne')

/-! ### The history's capacity at a root -/

section Hist

variable [StandardBorelSpace Ω] (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

include h13 in
/-- J32's capacity reader at a time before the buffer is the root-`x` clock (live samples). -/
theorem ae_rootCapAt_eq_clockX :
    ∀ᵐ ξ ∂c.P, 0 < (RootJ31.sourceSample c r l a ξ).1 →
      ∀ t ≤ RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ,
        GW2Sdg.rootCapAt c r l a t ξ = clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ := by
  filter_upwards [ae_exactPair_rootX h13 c r l a] with ξ hpair hlive t ht
  obtain ⟨-, -, hK⟩ := hpair hlive
  unfold GW2Sdg.rootCapAt
  rw [GW2Bf.forwardCapacity_future_eq_exact c r l a ξ ht, (hK t ht).1]

include h13 in
/-- **The root-`x` physical clock at the history time is the history's capacity** (live samples). -/
theorem ae_physClockX_eq_histCap (hx : 0 ≤ rootPt r.1) :
    ∀ᵐ ξ ∂c.P, 0 < (RootJ31.sourceSample c r l a ξ).1 →
      physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) (RootJ31.historyTime c r l) ξ =
        ((GW2Sdg.rootHistCap c r l a ξ : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨hGT, -, hGTae⟩ := schedGTX_spec h13 c r l a
  filter_upwards [ae_exactPair_rootX h13 c r l a, hGTae, ae_rootCapAt_eq_clockX h13 c r l a]
    with ξ hpair hGξ hcap hlive
  obtain ⟨hgx, hTc, -⟩ := hpair hlive
  have hξ : ξ ∈ schedGTX h13 c r l a := hGξ.2 hgx
  have hs := pos_of_physGoodX (hGT ξ hξ)
  have hT : ((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ :=
    (ENNReal.coe_le_coe.2 le_self_add).trans_lt hTc
  rw [physClockX_eq_clockX hGT hs hx hξ hT]
  unfold GW2Sdg.rootHistCap
  rw [hcap hlive _ le_self_add]
  rfl

include h13 in
/-- **The root-`x` stage start is the history's capacity** (live samples, below the cap). -/
theorem ae_stgStartX_eq_histCap (hx : 0 ≤ rootPt r.1) (V : Ω → ℝ≥0∞) :
    ∀ᵐ ξ ∂c.P, 0 < (RootJ31.sourceSample c r l a ξ).1 → ((GW2Sdg.rootHistCap c r l a ξ : ℝ≥0) : ℝ≥0∞) < V ξ →
      stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) V (RootJ31.historyTime c r l) ξ =
        GW2Sdg.rootHistCap c r l a ξ := by
  filter_upwards [ae_physClockX_eq_histCap h13 c r l a hx] with ξ hcl hlive hV
  change (min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
    (RootJ31.historyTime c r l) ξ) (V ξ)).toNNReal = _
  rw [hcl hlive, min_eq_left hV.le, ENNReal.toNNReal_coe]

include h13 in
/-- **`VDriverId` for the corrected root-`x` instance's stage driver** (BUF's `GW2Bh.ae_j32DriverId_schedInstS` at
the root point). -/
theorem ae_j32DriverId_schedInstSX (hx : 0 ≤ rootPt r.1) {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (ch : GW2Sdh.SchedChoice Ω) :
    ∀ᵐ ξ ∂c.P, ∀ u : ℝ≥0, u < GW2Sdg.rootGain c r l a ξ →
      (u : ℝ≥0∞) < V ξ - (GW2Sdg.rootHistCap c r l a ξ : ℝ≥0∞) →
      GW2Bf.j32Read c r l a (GW2Sdg.rootHistCap c r l a ξ + u) ξ -
          GW2Bf.j32Read c r l a (GW2Sdg.rootHistCap c r l a ξ) ξ =
        (schedInstSX c r l a (schedGTX h13 c r l a) hA ch).drvX c (rootPt r.1) u ξ := by
  filter_upwards [ae_j32DriverId_versionX h13 c r l a hx hA.1.1, ae_stgStartX_eq_histCap h13 c r l a hx V]
    with ξ hid hst u hu hV
  have hlive := live_of_gain_pos c r l a (lt_of_le_of_lt zero_le hu)
  have hV0 : ((GW2Sdg.rootHistCap c r l a ξ : ℝ≥0) : ℝ≥0∞) < V ξ :=
    (le_self_add).trans_lt (lt_tsub_iff_left.1 hV)
  have hV' : ((GW2Sdg.rootHistCap c r l a ξ + u : ℝ≥0) : ℝ≥0∞) < V ξ := by
    rw [ENNReal.coe_add]
    exact lt_tsub_iff_left.1 hV
  rw [hid u hu hV']
  change _ = stgDrv (fun u => R u ξ)
    (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) V (RootJ31.historyTime c r l) ξ) u
  rw [hst hlive hV0]
  rfl

include h13 in
/-- **The history's capacity plus the gain is the root-`x` clock at the buffer time** (live samples). -/
theorem ae_histCap_add_gainX :
    ∀ᵐ ξ ∂c.P, 0 < GW2Sdg.rootGain c r l a ξ →
      ((GW2Sdg.rootHistCap c r l a ξ + GW2Sdg.rootGain c r l a ξ : ℝ≥0) : ℝ≥0∞) =
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a)
          (RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ) ξ) := by
  filter_upwards [ae_rootCapAt_eq_clockX h13 c r l a] with ξ hcap hgain
  have hlive := live_of_gain_pos c r l a hgain
  set T := RootJ31.historyTime c r l
  set v := RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ
  have hT0 : 0 ≤ GW2Sdg.rootCapAt c r l a T ξ := RootJ32.forwardCapacity_nonneg _ _ _ _
  have hgain' : (0 : ℝ) < GW2Sdg.rootCapAt c r l a v ξ - GW2Sdg.rootCapAt c r l a T ξ := by
    have h := hgain
    unfold GW2Sdg.rootGain at h
    exact Real.toNNReal_pos.1 h
  have hsum : GW2Sdg.rootHistCap c r l a ξ + GW2Sdg.rootGain c r l a ξ = (GW2Sdg.rootCapAt c r l a v ξ).toNNReal := by
    unfold GW2Sdg.rootHistCap GW2Sdg.rootGain
    rw [← Real.toNNReal_add hT0 hgain'.le, add_sub_cancel]
  rw [hsum, hcap hlive v le_rfl]
  rfl

include h13 in
/-- **A cap beyond the buffer's root-`x` clock covers the gain.** -/
theorem ae_gain_le_sub_of_ltX :
    ∀ᵐ ξ ∂c.P, ∀ V : ℝ≥0∞, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a)
        (RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ) ξ) ≤ V →
      (GW2Sdg.rootGain c r l a ξ : ℝ≥0∞) ≤ V - (GW2Sdg.rootHistCap c r l a ξ : ℝ≥0∞) := by
  filter_upwards [ae_histCap_add_gainX h13 c r l a] with ξ hsum V hV
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ GW2Sdg.rootGain c r l a ξ) with h0 | hpos
  · rw [← h0, ENNReal.coe_zero]
    exact zero_le
  · refine ENNReal.le_sub_of_add_le_left ENNReal.coe_ne_top ?_
    rw [← ENNReal.coe_add, hsum hpos]
    exact hV

include h13 in
/-- **The stops of an exhausting root-`x` family cover the gain eventually** (BUF's `GW2Bh.ae_stopCovers_eventually`
at a root). -/
theorem ae_stopCovers_eventuallyX {Vn : ℕ → Ω → ℝ≥0∞}
    (hev : ∀ᵐ ξ ∂c.P, cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s → ∀ t : ℝ≥0,
      (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
      ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) < Vn n ξ) :
    ∀ᵐ ξ ∂c.P, ∀ᶠ n in atTop,
      (GW2Sdg.rootGain c r l a ξ : ℝ≥0∞) ≤ Vn n ξ - (GW2Sdg.rootHistCap c r l a ξ : ℝ≥0∞) := by
  filter_upwards [hev, ae_exactPair_rootX h13 c r l a, ae_gain_le_sub_of_ltX h13 c r l a]
    with ξ hevξ hpair hcov
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ GW2Sdg.rootGain c r l a ξ) with h0 | hpos
  · refine Eventually.of_forall fun n => ?_
    rw [← h0, ENNReal.coe_zero]
    exact zero_le
  · obtain ⟨hgx, hTc, -⟩ := hpair (live_of_gain_pos c r l a hpos)
    filter_upwards [hevξ hgx _ hTc] with n hn
    exact hcov (Vn n ξ) hn.le

end Hist

/-! ### The slow stop at a root -/

open Classical in
/-- **A lower cap as a root-`x` stage stop** (BUF's `GW2Bh.lowCapStop` at the root `x₀`): `Vlow − start` on the good
records, read by the stage rule of `ρ` on the killed
stage path. -/
def lowCapStopX (c : SourceData Ω) (l : List (EntryIdx c.Θ c.Q)) (I : StageInst Ω) (x₀ : ℝ)
    (Vlow : Ω → ℝ≥0∞) (ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞) : StageStop Ω where
  stop ω := if cfRec c.s c.W c.ζ ω ∈ goodX x₀ c.s then
    Vlow ω - (stgStartX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ω : ℝ≥0∞) else 0
  rule y e := if augσ ((entryList l).length + 1) y ∈ goodX x₀ c.s then
    stageRule ρ (augσ ((entryList l).length + 1)) augA augPre (y, killPath e) else 0

/-- **The lower cap is a good root-`x` stage stop** (BUF's `GW2Bh.lowCapStop_good` at the root `x₀`). -/
theorem lowCapStopX_good {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} {l : List (EntryIdx c.Θ c.Q)}
    {x₀ : ℝ} {I : StageInst Ω} (hI : I.GoodX c r l x₀) {Vlow : Ω → ℝ≥0∞} {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hρm : Measurable ρ) (hρ : IsPathRule ρ) (hVm : Measurable Vlow) (hVfin : ∀ ω, I.V ω ≠ ⊤)
    (hVρ : ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX x₀ c.s → Vlow ω = ρ (cfRec c.s c.W c.ζ ω, fun u => I.R u ω))
    (hle : ∀ᵐ ω ∂c.P, Vlow ω ≤ I.V ω)
    (hlt : ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX x₀ c.s → Vlow ω < I.V ω) :
    (lowCapStopX c l I x₀ Vlow ρ).GoodX I c r l x₀ := by
  classical
  set N := (entryList l).length + 1 with hN
  have hsρ : IsPathRule (stageRule ρ (augσ N) augA augPre) := isPathRule_stageRule hρ _ _ _
  have hsρm : Measurable (stageRule ρ (augσ N) augA augPre) :=
    measurable_stageRule hρm (measurable_augσ N) measurable_augA measurable_augPre
  have hstart : Measurable (stgStartX x₀ c.s c.W c.ζ I.W I.GT I.V I.T) :=
    measurable_stgStartX_of_pre hI.measurable_pre
  have hrecm : Measurable (cfRec c.s c.W c.ζ) := measurable_gb6Rec_src c
  have hRc := hI.version.2.1
  have hR0 := hI.version.2.2.1
  -- the decoders of the stage record
  have hdec : ∀ ω, augσ N (I.srecX c r l x₀ ω) = cfRec c.s c.W c.ζ ω ∧
      augA (I.srecX c r l x₀ ω) = stgStartX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ω ∧
      ∀ t ≤ augA (I.srecX c r l x₀ ω), augPre (I.srecX c r l x₀ ω) t = I.R t ω := fun ω =>
    augDec_specX (stgRecDec_stageEncRec c r l ω) (hRc ω) (hR0 ω)
  refine ⟨fun y t => ?_, ?_, ?_, ?_, ?_⟩
  · -- the rule is a stopping rule of the killed path
    by_cases hy : augσ N y ∈ goodX x₀ c.s
    · have he : {e : (ℝ≥0 → ℝ) × ℝ≥0∞ | (lowCapStopX c l I x₀ Vlow ρ).rule y e ≤ (t : ℝ≥0∞)} =
          {e | stageRule ρ (augσ N) augA augPre (y, killPath e) ≤ (t : ℝ≥0∞)} := by
        ext e
        simp only [lowCapStopX, ← hN, hy, ↓reduceIte, mem_ofPred_eq]
      rw [he]
      exact measurableSet_killPath_le hsρ hsρm y t
    · have he : {e : (ℝ≥0 → ℝ) × ℝ≥0∞ | (lowCapStopX c l I x₀ Vlow ρ).rule y e ≤ (t : ℝ≥0∞)} = univ := by
        ext e
        simp only [lowCapStopX, ← hN, hy, ↓reduceIte, mem_ofPred_eq, zero_le, mem_univ]
      rw [he]
      exact MeasurableSet.univ
  · -- the stop is measurable
    exact Measurable.ite ((measurableSet_goodX x₀ c.s).preimage hrecm)
      (hVm.sub (measurable_coe_nnreal_ennreal.comp hstart)) measurable_const
  · -- the stop is the rule read on the record and the killed stage path
    filter_upwards [hVρ, hlt] with ω hVρω hltω
    obtain ⟨hσ, hA, hpre⟩ := hdec ω
    by_cases hm : cfRec c.s c.W c.ζ ω ∈ goodX x₀ c.s
    · have hrule : (lowCapStopX c l I x₀ Vlow ρ).rule (I.srecX c r l x₀ ω) ((fun t => I.drvX c x₀ t ω), I.capX c x₀ ω) =
          stageRule ρ (augσ N) augA augPre
            (I.srecX c r l x₀ ω, killPath ((fun t => I.drvX c x₀ t ω), I.capX c x₀ ω)) := by
        simp only [lowCapStopX, ← hN, hσ, hm, ↓reduceIte]
      have hstop : (lowCapStopX c l I x₀ Vlow ρ).stop ω =
          Vlow ω - (stgStartX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ω : ℝ≥0∞) := by
        simp only [lowCapStopX, hm, ↓reduceIte]
      rw [hrule, hstop]
      have hpre' : ∀ t ≤ augA (I.srecX c r l x₀ ω), augPre (I.srecX c r l x₀ ω) t = (fun u => I.R u ω) t := hpre
      by_cases hVA : Vlow ω ≤ (stgStartX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ω : ℝ≥0∞)
      · -- a lower cap before the start: both sides are `0`
        rw [tsub_eq_zero_of_le hVA]
        refine (stageRule_eq_zero_of_le hρ hσ hpre' ?_ _).symm
        rw [← hVρω hm, hA]
        exact hVA
      · -- after the start: the killed path is read before the cap
        have hVA' : (stgStartX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ω : ℝ≥0∞) < Vlow ω := not_le.1 hVA
        have hdrv : stageRule ρ (augσ N) augA augPre (I.srecX c r l x₀ ω, fun t => I.drvX c x₀ t ω) =
            Vlow ω - (stgStartX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ω : ℝ≥0∞) := by
          have h1 := stageRule_stgDrv (ρ := ρ) (σ := augσ N) (A := augA) (pre := augPre)
            (x := I.srecX c r l x₀ ω) (hRc ω) (continuous_augPre _) hσ hpre'
          rw [hA] at h1
          rw [← hVρω hm] at h1
          exact h1
        have hcapgt : stageRule ρ (augσ N) augA augPre (I.srecX c r l x₀ ω, fun t => I.drvX c x₀ t ω) <
            I.capX c x₀ ω := by
          rw [hdrv]
          change _ < I.V ω - _
          rw [lt_tsub_iff_left, add_tsub_cancel_of_le hVA'.le]
          exact hltω hm
        rw [rule_killPath_eq hsρ (I.srecX c r l x₀ ω) ((fun t => I.drvX c x₀ t ω), I.capX c x₀ ω) hcapgt]
        exact hdrv.symm
    · have hrule : (lowCapStopX c l I x₀ Vlow ρ).rule (I.srecX c r l x₀ ω)
          ((fun t => I.drvX c x₀ t ω), I.capX c x₀ ω) = 0 := by
        simp only [lowCapStopX, ← hN, hσ, hm, ↓reduceIte]
      have hstop : (lowCapStopX c l I x₀ Vlow ρ).stop ω = 0 := by
        simp only [lowCapStopX, hm, ↓reduceIte]
      rw [hrule, hstop]
  · -- the stop is below the cap
    filter_upwards [hle] with ω hleω _
    by_cases hm : cfRec c.s c.W c.ζ ω ∈ goodX x₀ c.s
    · simp only [lowCapStopX, hm, ↓reduceIte]
      exact tsub_le_tsub_right hleω _
    · simp only [lowCapStopX, hm, ↓reduceIte]
      exact zero_le
  · -- a finite stop is strictly below the cap on the record event
    filter_upwards [hlt, hI.E_good] with ω hltω hEω hE _
    obtain ⟨hm, hst⟩ := hEω hE
    have hstart' : (stgStartX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ω : ℝ≥0∞) < I.V ω := by
      have hfin : stgStartMX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ω ≠ ⊤ :=
        ne_top_of_le_ne_top (hVfin ω) (min_le_right _ _)
      change ((stgStartMX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ω).toNNReal : ℝ≥0∞) < I.V ω
      rw [ENNReal.coe_toNNReal hfin]
      exact hst
    simp only [lowCapStopX, hm, ↓reduceIte]
    change _ < I.V ω - _
    by_cases hVA : Vlow ω ≤ (stgStartX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ω : ℝ≥0∞)
    · rw [tsub_eq_zero_of_le hVA]
      exact tsub_pos_of_lt hstart'
    · rw [lt_tsub_iff_left, add_tsub_cancel_of_le (not_le.1 hVA).le]
      exact hltω hm


/-! ### Two root-`x` versions agree up to the lower cap -/

section Cap

variable {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'} {x : ℝ} {s : ℝ≥0} {W' : ℝ≥0 → Ω' → ℝ}
  {ζ' : Ω' → ℝ≥0∞} {w : ℝ≥0 → Ω' → ℝ} {γ α : Ω' → ℝ≥0 → ℂ} {GT : Set Ω'}

/-- **Two root-`x` versions agree up to the lower cap, endpoint included** (BUF's `GW2Bh.ae_version_eq_le` at a
root). -/
theorem ae_version_eq_leX (hGT : ∀ ω ∈ GT, PhysGoodX x s W' ζ' w γ α ω) (hx : 0 ≤ x)
    (hGTae : ∀ᵐ ω ∂P, ω ∈ GT ↔ cfRec s W' ζ' ω ∈ goodX x s) {R R' : ℝ≥0 → Ω' → ℝ} {V V' : Ω' → ℝ≥0∞}
    (hver : IsRelVersionX x s P W' ζ' w γ α R V) (hver' : IsRelVersionX x s P W' ζ' w γ α R' V')
    (hle : ∀ᵐ ω ∂P, V ω ≤ V' ω) :
    ∀ᵐ ω ∂P, cfRec s W' ζ' ω ∈ goodX x s → ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ V ω → R u ω = R' u ω := by
  have hRc := hver.2.1
  have hRc' := hver'.2.1
  filter_upwards [ae_version_eqX hGT hx hGTae hver hver', hle] with ω hω hleω hm u hu
  have hlt : ∀ c' : ℝ≥0, c' < u → R c' ω = R' c' ω := fun c' hc' => by
    have h1 : (c' : ℝ≥0∞) < V ω := (ENNReal.coe_lt_coe.2 hc').trans_le hu
    exact hω hm c' h1 (h1.trans_le hleω)
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with h0 | hpos
  · rw [← h0, hver.2.2.1 ω, hver'.2.2.1 ω]
  · have heq : EqOn (fun t => R t ω) (fun t => R' t ω) (Iio u) := fun t ht => hlt t ht
    have hcl := heq.closure (hRc ω) (hRc' ω)
    rw [closure_Iio' (show (Iio u).Nonempty from ⟨0, hpos⟩)] at hcl
    exact hcl (le_refl u)

/-- **The lower cap read along the next root-`x` version's driver** (BUF's `GW2Bh.ae_lowCap_rule_eq` at a root). -/
theorem ae_lowCap_rule_eqX (hGT : ∀ ω ∈ GT, PhysGoodX x s W' ζ' w γ α ω) (hx : 0 ≤ x)
    (hGTae : ∀ᵐ ω ∂P, ω ∈ GT ↔ cfRec s W' ζ' ω ∈ goodX x s) {R R' : ℝ≥0 → Ω' → ℝ} {V V' : Ω' → ℝ≥0∞}
    (hver : IsRelVersionXR x s P W' ζ' w γ α R V) (hver' : IsRelVersionX x s P W' ζ' w γ α R' V')
    (hle : ∀ᵐ ω ∂P, V ω ≤ V' ω) :
    ∀ᵐ ω ∂P, cfRec s W' ζ' ω ∈ goodX x s → V ω = hver.2.choose (cfRec s W' ζ' ω, fun u => R' u ω) := by
  obtain ⟨-, hρ, hVρ⟩ := hver.2.choose_spec
  filter_upwards [ae_version_eq_leX hGT hx hGTae hver.1 hver' hle, hVρ] with ω hag hVω hm
  rw [hVω]
  exact (hρ (cfRec s W' ζ' ω) (fun u => R u ω) (fun u => R' u ω) fun u hu =>
    hag hm u (hu.trans_eq hVω.symm)).symm

end Cap

/-! ### The slow stage variables at a root -/

section Family

variable [StandardBorelSpace Ω] (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) {R : ℕ → ℝ≥0 → Ω → ℝ} {V : ℕ → Ω → ℝ≥0∞}
  (hA : ∀ n, IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α (R n) (V n))
  (ch : ℕ → GW2Sdh.SchedChoice Ω)

/-- The root-`x` slow instance of version `n + 1`. -/
abbrev slowInstX (n : ℕ) : StageInst Ω := schedInstSX c r l a (schedGTX h13 c r l a) (hA (n + 1)) (ch n)

/-- **Decision D3's slow stage stop `n` at a root**: the cap `V n` on the root-`x` instance of version `n + 1`. -/
abbrev slowCapStopX (n : ℕ) : StageStop Ω :=
  lowCapStopX c l (slowInstX h13 c r l a hA ch n) (rootPt r.1) (V n) (hA n).1.2.choose

/-- **Decision D3's slow stage variable `n` at a root.** -/
abbrev slowStageVarX (n : ℕ) : StageVar Ω :=
  (slowInstX h13 c r l a hA ch n).varX c r l (rootPt r.1) (slowCapStopX h13 c r l a hA ch n)

/-- **The root-`x` slow stage stops are good** (strict caps on the good records). -/
theorem lowCapStopX_good_family (hx : 0 ≤ rootPt r.1) (hmono : ∀ n ω, V n ω ≤ V (n + 1) ω)
    (hfin : ∀ n ω, V n ω ≠ ⊤)
    (hstrict : ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → ∀ n, V n ω < V (n + 1) ω)
    (hI : ∀ n, (slowInstX h13 c r l a hA ch n).GoodX c r l (rootPt r.1)) (n : ℕ) :
    (slowCapStopX h13 c r l a hA ch n).GoodX (slowInstX h13 c r l a hA ch n) c r l (rootPt r.1) := by
  obtain ⟨hGT, -, hGTae⟩ := schedGTX_spec h13 c r l a
  obtain ⟨hρm, hρ, -⟩ := (hA n).1.2.choose_spec
  have hrule := ae_lowCap_rule_eqX hGT hx hGTae (hA n).1 (hA (n + 1)).1.1 (ae_of_all _ (hmono n))
  refine lowCapStopX_good (hI n) hρm hρ (hA n).1.1.2.2.2.2.1 (hfin (n + 1)) hrule (ae_of_all _ (hmono n)) ?_
  filter_upwards [hstrict] with ω hω hm
  exact hω hm n

/-- **The root-`x` slow stop on live samples.** -/
theorem ae_slowStageVarX_stop_eq (hx : 0 ≤ rootPt r.1) (n : ℕ) :
    ∀ᵐ ξ ∂c.P, 0 < (RootJ31.sourceSample c r l a ξ).1 →
      ((GW2Sdg.rootHistCap c r l a ξ : ℝ≥0) : ℝ≥0∞) < V (n + 1) ξ →
      (slowStageVarX h13 c r l a hA ch n).stop ξ = V n ξ - (GW2Sdg.rootHistCap c r l a ξ : ℝ≥0∞) := by
  classical
  filter_upwards [ae_exactPair_rootX h13 c r l a, ae_stgStartX_eq_histCap h13 c r l a hx (V (n + 1))]
    with ξ hpair hst hlive hV
  obtain ⟨hm, -, -⟩ := hpair hlive
  change (if cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s then V n ξ - (stgStartX (rootPt r.1) c.s c.W c.ζ
    (schedW c r l a) (schedGTX h13 c r l a) (V (n + 1)) (RootJ31.historyTime c r l) ξ : ℝ≥0∞) else 0) = _
  simp only [hm, ↓reduceIte]
  rw [hst hlive hV]

/-- **SDE's `VDriverIdN` for the root-`x` slow stage variables.** -/
theorem vDriverIdN_slowStageVarX (hx : 0 ≤ rootPt r.1) (hmono : ∀ n ω, V n ω ≤ V (n + 1) ω)
    (hfin : ∀ n ω, V n ω ≠ ⊤) {Vp : VPkgXFamily.{u}} (n : ℕ)
    (hvar : (Vp Ω c r).slowVar l a n = slowStageVarX h13 c r l a hA ch n) :
    VDriverIdN Vp Ω c r l a n := by
  classical
  filter_upwards [ae_j32DriverId_schedInstSX h13 c r l a hx (hA (n + 1)) (ch n),
    ae_slowStageVarX_stop_eq h13 c r l a hA ch hx n, ae_exactPair_rootX h13 c r l a,
    ae_physClockX_eq_histCap h13 c r l a hx] with ξ hid hstop hpair hcl _ u hu hlt
  rw [hvar] at hlt ⊢
  have hlive := live_of_gain_pos c r l a (lt_of_le_of_lt zero_le hu)
  by_cases hV : ((GW2Sdg.rootHistCap c r l a ξ : ℝ≥0) : ℝ≥0∞) < V (n + 1) ξ
  · rw [hstop hlive hV] at hlt
    exact hid u hu (hlt.trans_le (tsub_le_tsub_right (hmono n ξ) _))
  · -- the history's capacity is past the next cap: the stop is `0`
    exfalso
    obtain ⟨hm, -, -⟩ := hpair hlive
    have h0 : (slowStageVarX h13 c r l a hA ch n).stop ξ = 0 := by
      change (if cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s then V n ξ - (stgStartX (rootPt r.1) c.s c.W c.ζ
        (schedW c r l a) (schedGTX h13 c r l a) (V (n + 1)) (RootJ31.historyTime c r l) ξ : ℝ≥0∞) else 0) = 0
      simp only [hm, ↓reduceIte]
      refine tsub_eq_zero_of_le ?_
      have hfin' : stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) (V (n + 1))
          (RootJ31.historyTime c r l) ξ ≠ ⊤ := ne_top_of_le_ne_top (hfin (n + 1) ξ) (min_le_right _ _)
      change V n ξ ≤ ((stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) (V (n + 1))
        (RootJ31.historyTime c r l) ξ).toNNReal : ℝ≥0∞)
      rw [ENNReal.coe_toNNReal hfin']
      change V n ξ ≤ min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
        (RootJ31.historyTime c r l) ξ) (V (n + 1) ξ)
      rw [hcl hlive, min_eq_right (not_lt.1 hV)]
      exact hmono n ξ
    rw [h0] at hlt
    exact (not_lt.2 zero_le) hlt

/-- **SDE's `VStopCoversN` for the root-`x` slow stage variables**, from coverage of the gain eventually in `n`. -/
theorem vStopCoversN_slowStageVarX (hx : 0 ≤ rootPt r.1) (hmono : ∀ n ω, V n ω ≤ V (n + 1) ω)
    {Vp : VPkgXFamily.{u}} (hvar : ∀ n, (Vp Ω c r).slowVar l a n = slowStageVarX h13 c r l a hA ch n)
    (hcov : ∀ᵐ ξ ∂c.P, ∀ᶠ n in atTop,
      (GW2Sdg.rootGain c r l a ξ : ℝ≥0∞) ≤ V n ξ - (GW2Sdg.rootHistCap c r l a ξ : ℝ≥0∞)) :
    VStopCoversN Vp Ω c r l a := by
  filter_upwards [hcov, ae_all_iff.2 fun n => ae_slowStageVarX_stop_eq h13 c r l a hA ch hx n]
    with ξ hcovξ hstopξ _
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ GW2Sdg.rootGain c r l a ξ) with h0 | hpos
  · refine Eventually.of_forall fun n => ?_
    rw [← h0, ENNReal.coe_zero]
    exact zero_le
  · have hlive := live_of_gain_pos c r l a hpos
    filter_upwards [hcovξ] with n hn
    have hlt : ((GW2Sdg.rootHistCap c r l a ξ : ℝ≥0) : ℝ≥0∞) < V n ξ :=
      tsub_pos_iff_lt.1 ((ENNReal.coe_pos.2 hpos).trans_le hn)
    rw [hvar n, hstopξ n hlive (hlt.trans_le (hmono n ξ))]
    exact hn

/-- **D3a's exhaust form for the root-`x` slow stage variables** (exhausting family). -/
theorem vStopExhaustsN_slowStageVarX (hx : 0 ≤ rootPt r.1) (hmono : ∀ n ω, V n ω ≤ V (n + 1) ω)
    {Vp : VPkgXFamily.{u}} (hvar : ∀ n, (Vp Ω c r).slowVar l a n = slowStageVarX h13 c r l a hA ch n)
    (hev : ∀ᵐ ξ ∂c.P, cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s → ∀ t : ℝ≥0,
      (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
      ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) < V n ξ) :
    VStopExhaustsN Vp Ω c r l a :=
  vStopExhaustsN_of_vStopCoversN (vStopCoversN_slowStageVarX h13 c r l a hA ch hx hmono hvar
    (ae_stopCovers_eventuallyX h13 c r l a hev))

end Family

end InteractingSLE.Theorem14.GW2Rv
