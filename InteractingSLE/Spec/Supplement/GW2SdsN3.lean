/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdsStage
import InteractingSLE.Spec.Supplement.GW2SdsSeed

/-!
# The near structure (N3) at the instance, assembled

Packet PROVE-GW2-SDE (round 18). Almost surely on J32's alive event over the scaled cover, the base word of any
root-`x` version of a candidate whose stop passes the history's clock (GEOM2's `GW2Wm.baseWordX` on the instance's
stage record, with the source counterflow word `cfWordSrc c`) has ROOT2's upper or lower structure at the near scale
`nearRootScale r.2 (nearLam l)`, in both orientations:

* the base word is the stage word flowed through the version's pieces (GEOM2's `GW2Wm.baseWordX_augRecX`);
* its far heights: GEOM2's `farL/farR_stageWord`, `farL/farR_rootWordX` (seed positivity, `gb6TS`);
* its root word's side forms: the root `0` (`rootForms_zero_src`) and the lower-arc roots (`rootForms_lowerArc`), by
  ROOT2's `RootSeedOK` on the cover event;
* junctions strictly off the tip at the stage start (`ae_stageJunctions`);
* the first piece: span `≥ 6√s` on the span-gap cover (`GW2Sdr.ae_firstSpan`), or both junctions `≥ 3√s` on the
  junction-gap cover (`ae_firstJunctions`).

Results: **`ae_nearStruct_span`** (`J32S GW2Sdr.gapFam2`), **`ae_nearStruct_junction`** (`J32S GW2Sdq.gapFam`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Sds

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2TipSystem.RootH10
  GW2Rz GW2Rd GW2Wm GW2Schedule

/-- The first record's prefix of the past of a driver. -/
theorem pastFirst_pastOf (cf : RecData) (R : ℝ≥0 → ℝ) (b : ℕ → ℝ≥0) :
    ∀ n, GW2Sdp.pastFirst n (pastOf cf R b (n + 1)) = pastOf cf R b 1
  | 0 => rfl
  | n + 1 => pastFirst_pastOf cf R b n

/-- The angles of a history program are in `[−π/2, π/2]` (`0` beyond its length). -/
theorem progAngle_mem_Icc {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (j : ℕ) :
    progAngle (historyProgram c r l) j ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  unfold progAngle
  by_cases hj : j < (historyProgram c r l).length
  · rw [List.getD_eq_getElem _ _ hj]
    exact GW2Olm.mem_Icc_futureProgram c r l 0 _ (List.mem_append_left _ (List.getElem_mem hj))
  · rw [List.getD_eq_default _ _ (not_lt.1 hj)]
    exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

/-- **The root word's side forms at every covered root** (source counterflow word). -/
theorem rootForms_src {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω) (x : RootIdx c.Θ c.Q)
    (hseed : RootCv.RootSeedOK c x) (r : RecData) (hr : rtime r = c.s)
    (hxA : (rootPt x : ℂ) ∉ closure (Supp8.Q3Rel.invHull (rdrv r) c.s)) :
    (∀ h ∈ GW2Sdp.rootHeightsL (GW2Wm.rootWordX c.κ (cfWordSrc c) (rootPt x) c.s r), h ∈ oldLeftHeights c.κ ∨
      ∃ S : ℝ, -2 < S ∧ h = -sleLambda (16 / c.κ) * (1 + S) + Real.pi * chiC c.κ) ∧
    (∀ h ∈ GW2Sdp.rootHeightsR (GW2Wm.rootWordX c.κ (cfWordSrc c) (rootPt x) c.s r), h ∈ oldRightHeights c.κ ∨
      ∃ S : ℝ, -2 < S ∧ h = sleLambda (16 / c.κ) * (1 + S) - Real.pi * chiC c.κ) := by
  rcases hseed.2 with hnone | ⟨hpos, hJ, hs⟩
  · have h0 : rootPt x = 0 := by unfold rootPt; rw [hnone]
    rw [h0]
    exact rootForms_zero_src c r hr
  · exact rootForms_lowerArc c hpos hJ hs r hr hxA

section Untouched

variable {Ω : Type*} {x : ℝ} {s : ℝ≥0} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {w : ℝ≥0 → Ω → ℝ}
  {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} (hGT : ∀ ω ∈ GT, PhysGoodX x s W' ζ' w γ α ω) (hx : 0 ≤ x)

include hGT hx

/-- **The root is untouched by the counterflow at time `s`** on the good event. -/
theorem root_notMem_closure_invHull {ω : Ω} (hω : ω ∈ GT) {τ : ℝ≥0} (hτc : (τ : ℝ≥0∞) < contactX x s γ α ω) :
    (x : ℂ) ∉ closure (Supp8.Q3Rel.invHull (rdrv (cfRec s W' ζ' ω)) s) := by
  obtain ⟨⟨hwc, hw0, hγ⟩, ⟨hα, hW, hW0, hζ⟩, harc, -, -⟩ := hGT ω hω
  have he := Gm.isRegularDriver_top hwc hw0
  have hv : (τ : ℝ≥0∞) < min (contactX x s γ α ω) ((fun t => w t ω), (⊤ : ℝ≥0∞)).2 := by
    rw [min_top_right]; exact hτc
  have hsafe0 := RootH29.trace_mem_record_relSafe W' ζ' ω hα hW hW0 hζ hx harc he hγ hv (t := 0) zero_le
  rw [hγ.1, add_zero] at hsafe0
  exact hsafe0.2

omit hx in
/-- The counterflow record has its own time `s` on the good event. -/
theorem rtime_cfRec_of_good {ω : Ω} (hω : ω ∈ GT) : rtime (cfRec s W' ζ' ω) = s := by
  obtain ⟨-, ⟨-, -, -, hζ⟩, -, -, -⟩ := hGT ω hω
  rw [cfRec, rtime_recOf_coe, GW2JointKernel.cfE_snd, hζ, min_top_right, ENNReal.toNNReal_coe]

end Untouched

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The instance's base word is the flowed stage word with its structure inputs** (one sample): on J32's alive event
with the good facts, the base word on the record of a version passing the history's clock is the stage word of the
version's past, whose root word has the side forms and the far heights, and whose stage junctions are strictly off the
tip. -/
theorem ae_baseWord_inputs (h13 : Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) {R : ℝ≥0 → Ω → ℝ}
    {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hfin : ∀ ω, V ω ≠ ⊤) :
    ∀ᵐ ω ∂c.P, ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω) < V ω →
      GW2Wm.baseWordX c.κ (cfWordSrc c) (rootPt r.1) c.s (historyProgram c r l) ((entryList l).length + 1)
          (GW2Ru.length_historyProgram c r l)
          (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) V
            (historyTime c r l) R) ω) =
        GW2JDetR5.stageWord (κ := c.κ) (GW2Wm.rootWordX c.κ (cfWordSrc c) (rootPt r.1) c.s)
          (progAngle (historyProgram c r l)) ((entryList l).length + 1)
          (pastOf (cfRec c.s c.W c.ζ ω) (fun u => R u ω)
            (trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) V (historyProgram c r l)
              ((entryList l).length + 1) (historyTime c r l) ω) ((entryList l).length + 1)) ∧
      ((∀ h ∈ GW2Sdp.rootHeightsL (GW2Wm.rootWordX c.κ (cfWordSrc c) (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)),
          h ∈ oldLeftHeights c.κ ∨ ∃ S : ℝ, -2 < S ∧ h = -sleLambda (16 / c.κ) * (1 + S) + Real.pi * chiC c.κ) ∧
        (∀ h ∈ GW2Sdp.rootHeightsR (GW2Wm.rootWordX c.κ (cfWordSrc c) (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)),
          h ∈ oldRightHeights c.κ ∨ ∃ S : ℝ, -2 < S ∧ h = sleLambda (16 / c.κ) * (1 + S) - Real.pi * chiC c.κ)) ∧
      (0 < markPos (rdrv (cfRec c.s c.W c.ζ ω)) (rtime (cfRec c.s c.W c.ζ ω)) 0 ∧
        markPosL (rdrv (cfRec c.s c.W c.ζ ω)) (rtime (cfRec c.s c.W c.ζ ω)) 0 < 0) := by
  obtain ⟨hGT, -, hGTae⟩ := schedGTX_spec h13 c r l a
  filter_upwards [GW2Ru.ae_alive_goodEvent h13 c r, hGTae] with ω hgood hGTω halive hV
  obtain ⟨hcf, hcon⟩ := hgood l halive
  have hω := hGTω.2 hcf
  have hTc := hcon a
  have hord := RootJ32.timeOrdered_historyProgram_of_alive c r l ω halive
  set L := historyProgram c r l with hL
  set N := (entryList l).length + 1 with hNdef
  have hLN : L.length = N := GW2Ru.length_historyProgram c r l
  have hTj : ∀ j < N, schedTime 0 L j ≤ historyTime c r l := fun j hj =>
    GW2Ru.schedTime_le_historyTime c r l hord (by rw [hLN]; exact hj.le)
  have hjT : ∀ j < N, schedTime 0 L j ≤ Sec5.Prop513Schedule.lastTime 0 L := fun j hj => by
    rw [← GW2Sde.historyTime_eq_lastTime]
    exact hTj j hj
  have hconj : ∀ j, 0 < j → j < N → (schedTime 0 L j : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω :=
    fun j _ hj => (ENNReal.coe_le_coe.2 (hTj j hj)).trans_lt hTc
  have hagree : ∀ u ≤ historyTime c r l, joinedRead L
      (fun i => (fun j : Fin N => stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) j ω) (Fin.cast hLN i)) u =
        schedW c r l a u ω := fun u hu => by
    have e1 : schedW c r l a u ω = Gm.futureJoined c r l a ω u :=
      congrFun (schedW_of_oldSuccess c r l a (RootJ32.oldSuccess_of_alive c r l ω halive)) u
    rw [e1, GW2Bf.futureJoined_eq_histJoined c r l a ω hu]
    rfl
  have hbase := baseWordX_augRecX (x₀ := rootPt r.1) (sp := c.s) (W := schedW c r l a) (Wα := c.W) (ζα := c.ζ)
    (GT := schedGTX h13 c r l a) (V := V) (T := historyTime c r l) (R := R) (γ := schedTr c r l a)
    (α := c.α) c.κ (cfWordSrc c) hGT hs hx L N hLN (xr := stageEncRec c r l) (ω := ω)
    (P := fun j : Fin N => stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) j ω) rfl (hA.2.1 ω)
    (hA.2.2.1 ω) hω (hfin ω) hTj hjT hconj hagree
  refine ⟨hbase, ?_, hcf.1.2.2.1, hcf.1.2.2.2⟩
  -- the root word's side forms
  have halive32 := halive
  obtain ⟨hcover, -, -⟩ := RootJ32.alive_spec c r l ω halive32
  have hseed : RootCv.RootSeedOK c r.1 := hcover.1
  exact rootForms_src c r.1 hseed _ (rtime_cfRec_of_good hGT hω) (root_notMem_closure_invHull hGT hx hω hTc)

/-- **The first boundary of the instance's past is the clock at the root time** (on the good event, before the
contact, below the stop). -/
theorem trueBdX_one (h13 : Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) {V : Ω → ℝ≥0∞} {ω : Ω}
    (hω : ω ∈ schedGTX h13 c r l a) (hord : Sec5.Prop513Schedule.TimeOrdered 0 (historyProgram c r l))
    (hTc : (historyTime c r l : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω)
    (hV : ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω) < V ω) :
    trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) V (historyProgram c r l)
        ((entryList l).length + 1) (historyTime c r l) ω 1 =
      (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c (r.1, 0) []) ω).toNNReal := by
  obtain ⟨hGT, -, -⟩ := schedGTX_spec h13 c r l a
  have hTle := GW2Sdr.historyTime_root_le c r l hord
  have hTc0 : ((historyTime c (r.1, 0) [] : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω :=
    (ENNReal.coe_le_coe.2 hTle).trans_lt hTc
  have hmono := (clockX_props hGT hs hx hω).2.1
  have hV0 : ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c (r.1, 0) []) ω) <
      V ω := (hmono hTc0 hTc hTle).trans_lt hV
  have hroot : historyTime c (r.1, 0) [] = (rootEntry r.1).2 := GW2Ru.historyTime_nil c (r.1, 0)
  unfold trueBdX
  rw [ite_eq_right (one_ne_zero)]
  split_ifs with h1
  · have e : schedTime 0 (historyProgram c r l) 1 = historyTime c (r.1, 0) [] := by
      rw [Gm.schedTime_succ_eq_getElem (by rw [GW2Ru.length_historyProgram]; omega), hroot]
      rfl
    rw [e]
    exact GW2Sdo.stgStartX_eq_clockX hGT hs hx hω hTc0 hV0
  · have hl : (entryList l).length = 0 := by omega
    have hl0 : l = [] := by
      have : l.length = 0 := by simpa [entryList] using hl
      exact List.eq_nil_of_length_eq_zero this
    subst hl0
    have e : historyTime c r [] = historyTime c (r.1, 0) [] := by
      rw [GW2Ru.historyTime_nil c r, hroot]
    rw [GW2Sdo.stgStartX_eq_clockX hGT hs hx hω hTc hV, e]

/-- **The first piece of the instance's past is the version's record up to the root clock.** -/
theorem pastOf_one_eq {cf : RecData} {R : ℝ≥0 → ℝ} (hR0 : R 0 = 0) {b : ℕ → ℝ≥0} (hb0 : b 0 = 0) :
    (pastOf cf R b 1).2 = recOf ((b 1 : ℝ≥0) : ℝ≥0∞) (R, ⊤) := by
  change recOf ((b 1 - b 0 : ℝ≥0) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R (b 0) u, ⊤) = _
  have hR : (fun u => GW2Rd.stgDrv R (b 0) u) = R := by
    funext u
    simp only [GW2Rd.stgDrv, hb0, zero_add, hR0, sub_zero]
  rw [hR, hb0, tsub_zero]

/-- **(N3) on the span-gap cover**: almost surely on J32S's alive event (gap `GW2Sdr.gapFam2`), the base word of
any root-`x` version of a candidate whose stop passes the history's clock has ROOT2's upper or lower structure at the
near scale, in both orientations. -/
theorem ae_nearStruct_span (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hfin : ∀ ω, V ω ≠ ⊤) :
    ∀ᵐ ω ∂c.P, ω ∈ ((GW2Sdz.J32S GW2Sdr.gapFam2 Ω c).experiment r).data.alive
        ((GW2Sdz.J32S GW2Sdr.gapFam2 Ω c).G r) l →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω) < V ω →
      ∀ flip : Bool, GW2Sdy.NearStruct c.κ (GW2Sdh.nearRootScale r.2 (GW2Sdh.nearLam Ω c r l ω)) flip
        (GW2Wm.baseWordX c.κ (cfWordSrc c) (rootPt r.1) c.s (historyProgram c r l) ((entryList l).length + 1)
          (GW2Ru.length_historyProgram c r l)
          (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a)
            (schedGTX Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} c r l a) V (historyTime c r l) R) ω)) := by
  have h13 : Exist.Theorem13Statement.{u} := Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u}
  obtain ⟨hGT, -, hGTae⟩ := schedGTX_spec h13 c r l a
  filter_upwards [ae_baseWord_inputs h13 c r l a hx hs hA hfin, ae_stageJunctions h13 c r l a hx hs hA,
    GW2Sdr.ae_firstSpan c r l a hx hs hA, GW2Ru.ae_alive_goodEvent h13 c r, hGTae]
    with ω hin hjun hspan hgood hGTω halive hV flip
  have halive32 := GW2Sdz.alive_scaled_subset GW2Sdr.gapFam2 Ω c r l halive
  obtain ⟨hbase, ⟨hformL, hformR⟩, hpos, hneg⟩ := hin halive32 hV
  obtain ⟨hjL, hjR⟩ := hjun halive32 hV
  have hsp := hspan halive hV
  obtain ⟨hcf, hcon⟩ := hgood l halive32
  have hω := hGTω.2 hcf
  have hord := RootJ32.timeOrdered_historyProgram_of_alive c r l ω halive32
  rw [hbase]
  set n := (entryList l).length with hn
  set b := trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) V (historyProgram c r l)
    (n + 1) (historyTime c r l) ω with hb
  set cf := cfRec c.s c.W c.ζ ω with hcf'
  have hroot := GW2Wm.pastRoot_pastOf cf (fun u => R u ω) b (n + 1)
  have hb0 : b 0 = 0 := by rw [hb]; unfold trueBdX; rw [ite_eq_left rfl]
  have hb1 := trueBdX_one h13 c r l a hx hs hω hord (hcon a) hV
  have hfirst : 6 * Real.sqrt (GW2Sdh.nearRootScale r.2 (GW2Sdh.nearLam Ω c r l ω)) ≤
      GW2Sdp.junctionR 1 (GW2Sdp.pastFirst n (pastOf cf (fun u => R u ω) b (n + 1))) -
        GW2Sdp.junctionL 1 (GW2Sdp.pastFirst n (pastOf cf (fun u => R u ω) b (n + 1))) := by
    rw [pastFirst_pastOf]
    change _ ≤ markPos (rdrv (pastOf cf (fun u => R u ω) b 1).2) (rtime (pastOf cf (fun u => R u ω) b 1).2) 0 -
      markPosL (rdrv (pastOf cf (fun u => R u ω) b 1).2) (rtime (pastOf cf (fun u => R u ω) b 1).2) 0
    rw [pastOf_one_eq (hA.2.2.1 ω) hb0]
    rw [← hb] at hb1
    rw [hb1]
    exact hsp
  have hθ : ∀ j, progAngle (historyProgram c r l) j ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    progAngle_mem_Icc c r l
  have hs' : GW2Sdh.nearRootScale r.2 (GW2Sdh.nearLam Ω c r l ω) ≠ 0 :=
    GW2Sdh.nearRootScale_ne_zero r.2 (GW2Sdh.nearLam_ne Ω c r l ω)
  have hfarL : GW2Wm.FarL (GW2JDetR5.stageWord (κ := c.κ) (GW2Wm.rootWordX c.κ (cfWordSrc c) (rootPt r.1) c.s)
      (progAngle (historyProgram c r l)) (n + 1) (pastOf cf (fun u => R u ω) b (n + 1)))
      (-sleLambda (16 / c.κ) + Real.pi * chiC c.κ) :=
    GW2Wm.farL_stageWord c.hκ (progAngle (historyProgram c r l))
      (A₀ := {p : RecData | 0 < markPos (rdrv p) (rtime p) 0})
      (fun p hp => GW2Wm.farL_rootWordX c.hκ (cfWordSrc c) (rootPt r.1) c.s p hp) (n + 1) _
      (by rw [hroot]; exact hpos)
  have hfarR : GW2Wm.FarR (GW2JDetR5.stageWord (κ := c.κ) (GW2Wm.rootWordX c.κ (cfWordSrc c) (rootPt r.1) c.s)
      (progAngle (historyProgram c r l)) (n + 1) (pastOf cf (fun u => R u ω) b (n + 1)))
      (sleLambda (16 / c.κ) - Real.pi * chiC c.κ) :=
    GW2Wm.farR_stageWord c.hκ (progAngle (historyProgram c r l))
      (A₀ := {p : RecData | markPosL (rdrv p) (rtime p) 0 < 0})
      (fun p hp => GW2Wm.farR_rootWordX c.hκ (cfWordSrc c) (rootPt r.1) c.s p hp) (n + 1) _
      (by rw [hroot]; exact hneg)
  exact GW2Sdr.nearStruct_stageWord_span c.hκ c.hκ4 _ _ hθ n _ hs' flip
    (by rw [hroot]; exact hformL) (by rw [hroot]; exact hformR) hfarL hfarR hjL hjR hfirst

/-- **(N3) on the junction-gap cover**: almost surely on J32S's alive event (gap `GW2Sdq.gapFam`), the base word of
any root-`x` version of a candidate whose stop passes the history's clock has ROOT2's upper or lower structure at the
near scale, in both orientations. -/
theorem ae_nearStruct_junction (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hfin : ∀ ω, V ω ≠ ⊤) :
    ∀ᵐ ω ∂c.P, ω ∈ ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive
        ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω) < V ω →
      ∀ flip : Bool, GW2Sdy.NearStruct c.κ (GW2Sdh.nearRootScale r.2 (GW2Sdh.nearLam Ω c r l ω)) flip
        (GW2Wm.baseWordX c.κ (cfWordSrc c) (rootPt r.1) c.s (historyProgram c r l) ((entryList l).length + 1)
          (GW2Ru.length_historyProgram c r l)
          (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a)
            (schedGTX Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} c r l a) V (historyTime c r l) R) ω)) := by
  have h13 : Exist.Theorem13Statement.{u} := Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u}
  obtain ⟨hGT, -, hGTae⟩ := schedGTX_spec h13 c r l a
  filter_upwards [ae_baseWord_inputs h13 c r l a hx hs hA hfin, ae_stageJunctions h13 c r l a hx hs hA,
    ae_firstJunctions c r l a hx hs hA, GW2Ru.ae_alive_goodEvent h13 c r, hGTae]
    with ω hin hjun hspan hgood hGTω halive hV flip
  have halive32 := GW2Sdz.alive_scaled_subset GW2Sdq.gapFam Ω c r l halive
  obtain ⟨hbase, ⟨hformL, hformR⟩, hpos, hneg⟩ := hin halive32 hV
  obtain ⟨hjL, hjR⟩ := hjun halive32 hV
  have hsp := hspan halive hV
  obtain ⟨hcf, hcon⟩ := hgood l halive32
  have hω := hGTω.2 hcf
  have hord := RootJ32.timeOrdered_historyProgram_of_alive c r l ω halive32
  rw [hbase]
  set n := (entryList l).length with hn
  set b := trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) V (historyProgram c r l)
    (n + 1) (historyTime c r l) ω with hb
  set cf := cfRec c.s c.W c.ζ ω with hcf'
  have hroot := GW2Wm.pastRoot_pastOf cf (fun u => R u ω) b (n + 1)
  have hb0 : b 0 = 0 := by rw [hb]; unfold trueBdX; rw [ite_eq_left rfl]
  have hb1 := trueBdX_one h13 c r l a hx hs hω hord (hcon a) hV
  have hfirst : 3 * Real.sqrt (GW2Sdh.nearRootScale r.2 (GW2Sdh.nearLam Ω c r l ω)) ≤
      -GW2Sdp.junctionL 1 (GW2Sdp.pastFirst n (pastOf cf (fun u => R u ω) b (n + 1))) ∧
      3 * Real.sqrt (GW2Sdh.nearRootScale r.2 (GW2Sdh.nearLam Ω c r l ω)) ≤
        GW2Sdp.junctionR 1 (GW2Sdp.pastFirst n (pastOf cf (fun u => R u ω) b (n + 1))) := by
    rw [pastFirst_pastOf]
    change _ ≤ -markPosL (rdrv (pastOf cf (fun u => R u ω) b 1).2) (rtime (pastOf cf (fun u => R u ω) b 1).2) 0 ∧
      _ ≤ markPos (rdrv (pastOf cf (fun u => R u ω) b 1).2) (rtime (pastOf cf (fun u => R u ω) b 1).2) 0
    rw [pastOf_one_eq (hA.2.2.1 ω) hb0]
    rw [← hb] at hb1
    rw [hb1]
    exact hsp
  have hθ : ∀ j, progAngle (historyProgram c r l) j ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    progAngle_mem_Icc c r l
  have hs' : GW2Sdh.nearRootScale r.2 (GW2Sdh.nearLam Ω c r l ω) ≠ 0 :=
    GW2Sdh.nearRootScale_ne_zero r.2 (GW2Sdh.nearLam_ne Ω c r l ω)
  have hfarL : GW2Wm.FarL (GW2JDetR5.stageWord (κ := c.κ) (GW2Wm.rootWordX c.κ (cfWordSrc c) (rootPt r.1) c.s)
      (progAngle (historyProgram c r l)) (n + 1) (pastOf cf (fun u => R u ω) b (n + 1)))
      (-sleLambda (16 / c.κ) + Real.pi * chiC c.κ) :=
    GW2Wm.farL_stageWord c.hκ (progAngle (historyProgram c r l))
      (A₀ := {p : RecData | 0 < markPos (rdrv p) (rtime p) 0})
      (fun p hp => GW2Wm.farL_rootWordX c.hκ (cfWordSrc c) (rootPt r.1) c.s p hp) (n + 1) _
      (by rw [hroot]; exact hpos)
  have hfarR : GW2Wm.FarR (GW2JDetR5.stageWord (κ := c.κ) (GW2Wm.rootWordX c.κ (cfWordSrc c) (rootPt r.1) c.s)
      (progAngle (historyProgram c r l)) (n + 1) (pastOf cf (fun u => R u ω) b (n + 1)))
      (sleLambda (16 / c.κ) - Real.pi * chiC c.κ) :=
    GW2Wm.farR_stageWord c.hκ (progAngle (historyProgram c r l))
      (A₀ := {p : RecData | markPosL (rdrv p) (rtime p) 0 < 0})
      (fun p hp => GW2Wm.farR_rootWordX c.hκ (cfWordSrc c) (rootPt r.1) c.s p hp) (n + 1) _
      (by rw [hroot]; exact hneg)
  exact GW2Sdp.nearStruct_stageWord' c.hκ c.hκ4 _ _ hθ n _ hs' flip
    (by rw [hroot]; exact hformL) (by rw [hroot]; exact hformR) hfarL hfarR hjL hjR hfirst

end InteractingSLE.Theorem14.GW2Sds
