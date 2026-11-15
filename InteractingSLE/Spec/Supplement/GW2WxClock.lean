/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2WmClock
import InteractingSLE.Spec.Supplement.GW2RzStage

/-!
# GW2's stage word map at a root `x`: the decoder reads ROOTX's clock and stage starts (decision D8)

Packet PROVE-GW2-GEOM2 (round 8: the root-`x` side of the word map, for PROVE-GW2-ROOTX's D8 rebuild). The word map's
decoder (`GW2Wm.stageDec`) reads the intermediate relative stage boundaries with ROOT2's capacity reader
`RootH29.forwardCapacity x s T_j` at the physical stage times `T_j = schedTime 0 L j`. ROOTX's root-`x` clock is the
same reader with the explored record at the time (`GW2Rz.clockX`), and ROOTX's root-`x` stage start is
`GW2Rz.stgStartX = (min (physClockX T) V).toNNReal`, with `physClockX = ofReal clockX` before the root-`x` contact on
the good event (`GW2Rz.physClockX_eq_clockX`). So:

* **`stageRead_eq_clockX`** (deterministic, one sample): at a root `x`, the decoder's reading at `T_j` IS ROOTX's
  `clockX` at `T_j`, as soon as the joined physical driver of the decoded pieces is the explored driver up to `T_j`;
* **`stageDec_augRecX`**: on ROOTX's root-`x` augmented record `augRec x (stgPreRecX …)` the decoder returns the root
  record followed by the records of the instance's own relative driver between the boundaries `instBd …`
  (ROOTX's `GW2Rz.augDec_specX`);
* `trueBdX` (the instance's own root-`x` stage starts at the physical stage times), **`instBd_eq_trueBdX`**,
  **`stageDec_augRecX_trueBd`**: on the good event, before the root-`x` contact, the decoder's boundaries are the
  root-`x` stage starts `stgStartX` at the earlier physical stage times.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2Wm

open Restart Exist.Staged Exist.StagedLaw Supp8.GB6 GW2TipSystem

section Read

variable {Ω : Type*} {W' w : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {s : ℝ≥0} {ω : Ω}

/-- **At a root `x` the decoder's boundary reading is ROOTX's clock** `GW2Rz.clockX` at the physical stage time
`T_j`, when the joined physical driver of the decoded pieces is the explored driver up to `T_j`. -/
theorem stageRead_eq_clockX (x : ℝ) (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N) (z : RecData)
    (P : Fin N → RecData) (hz : decHist N z = (cfRec s W' ζ' ω, P)) (j : ℕ)
    (hjT : GW2Schedule.schedTime 0 L j ≤ Sec5.Prop513Schedule.lastTime 0 L)
    (hwc : Continuous fun t => w t ω) (hw0 : w 0 ω = 0)
    (hagree : ∀ u ≤ GW2Schedule.schedTime 0 L j,
      RootJ31.joinedRead L (fun i => P (Fin.cast hN i)) u = w u ω) :
    stageRead x s L N hN z j = GW2Rz.clockX x s W' ζ' w (GW2Schedule.schedTime 0 L j) ω := by
  set q := GW2Schedule.schedTime 0 L j with hqdef
  unfold stageRead GW2Rz.clockX GW2Rz.recPair
  rw [hz]
  have hJ := RootJ31.continuous_joinedRead L (fun i => P (Fin.cast hN i))
  have hEq : EqOn (rdrv (RootJ31.joinedRecord L fun i => P (Fin.cast hN i)))
      (rdrv (recOf (q : ℝ≥0∞) ((fun t => w t ω), ⊤))) (Icc 0 (q : ℝ)) := by
    intro u hu
    have hu0 : (u.toNNReal : ℝ) = u := Real.coe_toNNReal _ hu.1
    have huq : u.toNNReal ≤ q := Real.toNNReal_le_iff_le_coe.2 hu.2
    rw [← hu0]
    unfold RootJ31.joinedRecord
    rw [Gm.rdrv_recOfDriver hJ.1 hJ.2, min_eq_left (huq.trans hjT), hagree _ huq,
      Gm.rdrv_recOf_eq (Gm.isRegularDriver_top hwc hw0) (by simp) (by simpa using hwc.continuousOn)]
    congr 1
    rw [show min (q : ℝ≥0∞) ((fun t => w t ω), (⊤ : ℝ≥0∞)).2 = q from min_eq_left le_top, ENNReal.toNNReal_coe,
      min_eq_left huq]
  have hH : QuantumZipper.fwdHull (rdrv (RootJ31.joinedRecord L fun i => P (Fin.cast hN i))) q =
      QuantumZipper.fwdHull (rdrv (recOf (q : ℝ≥0∞) ((fun t => w t ω), ⊤))) q :=
    LocalExt.fwdHull_congr_of_continuousOn (t' := (q : ℝ) + 1) (continuous_rdrv _).continuousOn
      (continuous_rdrv _).continuousOn q.coe_nonneg (by linarith) hEq
  unfold RootH29.forwardCapacity RootH29.forwardHull RootH29.translatedHull
  rw [hH]

end Read

section Inst

variable {Ω : Type*} {x₀ : ℝ} {sp : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {GT : Set Ω} {V : Ω → ℝ≥0∞}
  {T : ℝ≥0} {R : ℝ≥0 → Ω → ℝ}

/-- **The decoder on ROOTX's root-`x` augmented record** returns the root record followed by the records of the
instance's own relative driver between the boundaries `instBd …` (clipped at the root-`x` stage start). -/
theorem stageDec_augRecX (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N) {xr : Ω → RecData}
    {ω : Ω} {cf : RecData} {P : Fin N → RecData} (hx : xr ω = GW2Rd.stageEnc N (cf, P))
    (hRc : Continuous fun u => R u ω) (hR0 : R 0 ω = 0) :
    stageDec x s L N hN (GW2Rd.augRec xr (GW2Rz.stgPreRecX x₀ sp Wα ζα W GT V T R) ω) =
      pastOf cf (fun u => R u ω) (instBd x s L N hN cf P (GW2Rz.stgStartX x₀ sp Wα ζα W GT V T ω)) N := by
  have hd := decHist_augRec N (y := GW2Rz.stgPreRecX x₀ sp Wα ζα W GT V T R) hx
  have hσ : GW2Rd.stgRecDec N (xr ω) = cf := by
    unfold GW2Rd.stgRecDec
    rw [hx, (GW2Rd.stageEnc N).symm_apply_apply]
  obtain ⟨-, hA, hPre⟩ := GW2Rz.augDec_specX (x₀ := x₀) (s := sp) (W := W) (Wα := Wα) (ζα := ζα) (GT := GT)
    (V := V) (T := T) (rec := fun _ => cf) (ω := ω) hσ hRc hR0
  have hbd : stageBd x s L N hN (GW2Rd.augRec xr (GW2Rz.stgPreRecX x₀ sp Wα ζα W GT V T R) ω) =
      instBd x s L N hN cf P (GW2Rz.stgStartX x₀ sp Wα ζα W GT V T ω) := by
    funext j
    unfold stageBd stageRead instBd
    rw [hd, hA]
  unfold stageDec
  rw [hd, hbd]
  refine pastOf_congr cf (B := GW2Rz.stgStartX x₀ sp Wα ζα W GT V T ω) (fun u hu => hPre u (hA ▸ hu)) N
    fun j _ => ?_
  unfold instBd
  split_ifs
  · exact bot_le
  · exact min_le_right _ _
  · exact le_rfl

/-- **The instance's own root-`x` stage starts at the physical stage times** `T_j = schedTime 0 L j` (`0` at
`j = 0`, the stage start at `T` from `j = N` on). -/
def trueBdX (x₀ : ℝ) (sp : ℝ≥0) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (GT : Set Ω)
    (V : Ω → ℝ≥0∞) (L : List (ℝ × ℝ≥0)) (N : ℕ) (T : ℝ≥0) (ω : Ω) (j : ℕ) : ℝ≥0 :=
  if j = 0 then 0 else if j < N then GW2Rz.stgStartX x₀ sp Wα ζα W GT V (GW2Schedule.schedTime 0 L j) ω
  else GW2Rz.stgStartX x₀ sp Wα ζα W GT V T ω

variable {γ α : Ω → ℝ≥0 → ℂ}

/-- **On the good event, before the root-`x` contact, the decoder's boundaries are the root-`x` stage starts** at the
earlier physical stage times (ROOTX's `physClockX_eq_clockX`, `monotone_physClockX`). -/
theorem instBd_eq_trueBdX (hGT : ∀ ω ∈ GT, GW2Rz.PhysGoodX x₀ sp Wα ζα W γ α ω) (hs : 0 < sp) (hx : 0 ≤ x₀)
    (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N) {ω : Ω} (hω : ω ∈ GT) (hV : V ω ≠ ⊤)
    {P : Fin N → RecData} (hT : ∀ j < N, GW2Schedule.schedTime 0 L j ≤ T)
    (hcon : ∀ j, 0 < j → j < N → (GW2Schedule.schedTime 0 L j : ℝ≥0∞) < GW2Rz.contactX x₀ sp γ α ω)
    (hread : ∀ j, 0 < j → j < N →
      RootH29.forwardCapacity x₀ sp (GW2Schedule.schedTime 0 L j)
          (cfRec sp Wα ζα ω, RootJ31.joinedRecord L fun i => P (Fin.cast hN i)) =
        GW2Rz.clockX x₀ sp Wα ζα W (GW2Schedule.schedTime 0 L j) ω) :
    instBd x₀ sp L N hN (cfRec sp Wα ζα ω) P (GW2Rz.stgStartX x₀ sp Wα ζα W GT V T ω) =
      trueBdX x₀ sp Wα ζα W GT V L N T ω := by
  funext j
  unfold instBd trueBdX
  split_ifs with h0 hj
  · rfl
  · have hj0 : 0 < j := Nat.pos_of_ne_zero h0
    rw [hread j hj0 hj]
    have hph := GW2Rz.physClockX_eq_clockX hGT hs hx hω (hcon j hj0 hj)
    have hmono := GW2Rz.monotone_physClockX hGT hs hx ω (hT j hj)
    set a := GW2Rz.physClockX x₀ sp Wα ζα W GT (GW2Schedule.schedTime 0 L j) ω with ha
    set b := GW2Rz.physClockX x₀ sp Wα ζα W GT T ω with hb
    have ha_top : a ≠ ⊤ := by rw [hph]; exact ENNReal.ofReal_ne_top
    have hcl : (GW2Rz.clockX x₀ sp Wα ζα W (GW2Schedule.schedTime 0 L j) ω).toNNReal = a.toNNReal := by
      rw [hph]
      simp only [ENNReal.ofReal, ENNReal.toNNReal_coe]
    change min (GW2Rz.clockX x₀ sp Wα ζα W (GW2Schedule.schedTime 0 L j) ω).toNNReal (min b (V ω)).toNNReal =
      (min a (V ω)).toNNReal
    have hbV : min b (V ω) ≠ ⊤ := ne_top_of_le_ne_top hV (min_le_right _ _)
    have hmin : (min a (min b (V ω))).toNNReal = min a.toNNReal (min b (V ω)).toNNReal := by
      rcases le_total a (min b (V ω)) with h | h
      · rw [min_eq_left h, min_eq_left (ENNReal.toNNReal_mono hbV h)]
      · rw [min_eq_right h, min_eq_right (ENNReal.toNNReal_mono ha_top h)]
    rw [hcl, ← hmin, ← min_assoc, min_eq_left hmono]
  · rfl

/-- **The decoder on ROOTX's root-`x` record returns the instance's own relative stage records**: the root record,
then the records of the relative driver between the root-`x` stage starts at the physical stage times, on the good
event before the root-`x` contact, when the joined physical driver is the explored driver up to `T`. -/
theorem stageDec_augRecX_trueBd (hGT : ∀ ω ∈ GT, GW2Rz.PhysGoodX x₀ sp Wα ζα W γ α ω) (hs : 0 < sp)
    (hx : 0 ≤ x₀) (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N) {xr : Ω → RecData} {ω : Ω}
    {P : Fin N → RecData} (hxr : xr ω = GW2Rd.stageEnc N (cfRec sp Wα ζα ω, P))
    (hRc : Continuous fun u => R u ω) (hR0 : R 0 ω = 0) (hω : ω ∈ GT) (hV : V ω ≠ ⊤)
    (hT : ∀ j < N, GW2Schedule.schedTime 0 L j ≤ T)
    (hjT : ∀ j < N, GW2Schedule.schedTime 0 L j ≤ Sec5.Prop513Schedule.lastTime 0 L)
    (hcon : ∀ j, 0 < j → j < N → (GW2Schedule.schedTime 0 L j : ℝ≥0∞) < GW2Rz.contactX x₀ sp γ α ω)
    (hagree : ∀ u ≤ T, RootJ31.joinedRead L (fun i => P (Fin.cast hN i)) u = W u ω) :
    stageDec x₀ sp L N hN (GW2Rd.augRec xr (GW2Rz.stgPreRecX x₀ sp Wα ζα W GT V T R) ω) =
      pastOf (cfRec sp Wα ζα ω) (fun u => R u ω) (trueBdX x₀ sp Wα ζα W GT V L N T ω) N := by
  rw [stageDec_augRecX x₀ sp L N hN hxr hRc hR0]
  have hgood := hGT ω hω
  congr 1
  refine instBd_eq_trueBdX hGT hs hx L N hN hω hV hT hcon fun j hj0 hj => ?_
  have hz : decHist N (GW2Rd.augRec xr (fun _ => GW2Rd.pairEnc (xr ω, xr ω)) ω) = (cfRec sp Wα ζα ω, P) :=
    decHist_augRec N hxr
  have h := stageRead_eq_clockX (s := sp) (W' := Wα) (ζ' := ζα) (w := W) (ω := ω) x₀ L N hN
    (GW2Rd.augRec xr (fun _ => GW2Rd.pairEnc (xr ω, xr ω)) ω) P hz j (hjT j hj) hgood.1.1 hgood.1.2.1
    fun u hu => hagree u (hu.trans (hT j hj))
  unfold stageRead at h
  rw [hz] at h
  exact h

end Inst

end InteractingSLE.Theorem14.GW2Wm
