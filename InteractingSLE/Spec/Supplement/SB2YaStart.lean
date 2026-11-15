/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2YaFld
import InteractingSLE.Spec.Supplement.SB2JvV5
import InteractingSLE.Spec.Supplement.SB2JvHead
import InteractingSLE.Spec.Supplement.SB2JwZero
import InteractingSLE.Spec.Supplement.SB2JwStage0
import InteractingSLE.Spec.Supplement.SB2LoAE
import InteractingSLE.Spec.Supplement.SB2LoHead
import InteractingSLE.Spec.Supplement.SB2JqArc

/-!
# The start configuration at `relOff`

Packet PROVE-T14-SB2LIFT (round 31; item 4). The start disjunction of `ClauseTW` at the offset `relOff`, from GW1's run
facts, LIFTSET's root facts and the lift relation at the root:
* **`pieceStartV_of`**: off a zero root at a positive shifted lifetime, `PieceStartV` (the relative fields by
  `rootFields`, the actual ones by `launch_seed_of_not_zeroRoot`, `piece_fields_of_launch`, `head_of_pieceStart`);
* **`arcStart_of_zeroRoot`**: at a zero root, `ArcStart` (`arcStartData_of_zeroRoot_ae`, `head_of_arcStart`);
* **`arcStart_of_corner`**: off a zero root at a zero shifted lifetime (the start piece first visits `R` at its end),
  `ArcStart`: after the piece the walk stands at `R` on an outward right threshold.
Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {D₁ D₂ : ℕ → Drv}
  {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {c : Chart} {m : ℝ} {A : Set ℂ}

/-- Before a launch every earlier launch was finite, so `RecInv` and `PtRec` hold up to it. -/
theorem recInv_ptRec_upto_launch (hP : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hlm : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j) {n : ℕ}
    (hnd : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) ≠ stDone) :
    ∀ k, k ≤ n → RecInv κ b₁ J₁ θ D₁ k ∧ PtRec (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k) := by
  have hfin : ∀ i, i < n → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + 1)).2.2.2.1 i ≠ none →
      (D₁ i).2 ≠ ⊤ := by
    intro i hi hl htop
    have hd : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + 1)) = stDone := by
      rw [launch_walk hl]
      exact (launch_eq_of_top _ i (D₁ i) θ ⊤ (by rw [htop, min_self])).2.2.2.2.1
    exact hnd (done_of_le hd (by omega))
  exact recInv_ptRec_run_le hP hfin hlm hlh

/-- A launching instruction is followed by a connector instruction. -/
theorem succ_lt_length_of_launch {n : ℕ}
    (hl : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1)).2.2.2.1 n ≠ none) :
    n + 1 < (boundaryWalkSpec b₁ J₁ θ true).2.2.length := by
  obtain ⟨hev, hlt⟩ := GW1W.even_of_launches_walk hl
  have := GW1WalkFinish.boundaryWalk_length b₁ J₁ θ true
  omega

/-- **`R` lies on the start piece off a zero root.** -/
theorem memR_of_not_zeroRoot (hb : IsPiecewiseConstantBoundaryData b₁ J₁) (hX : RunExitData κ b₁ J₁ θ D₁)
    (hP : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hW : WalkChainFacts κ b₁ J₁ θ D₁)
    (hlm : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hallow : ∀ n, 1 ≤ n → AllowedSt κ b₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n))
    (hdone : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁
      (boundaryWalkSpec b₁ J₁ θ true).2.2.length) = stDone)
    (hR : (R : ℂ) ∈ ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hZ : ¬ ZeroRoot κ θ b₁ J₁ R D₁) :
    (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (relOff κ θ b₁ J₁ R D₁ + 1)).2.2.2.1
        (relOff κ θ b₁ J₁ R D₁) ≠ none ∧
      ((R : ℂ) ∈ statePhysicalSet 0
          (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (relOff κ θ b₁ J₁ R D₁)) →
        stPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (relOff κ θ b₁ J₁ R D₁)) = R) ∧
      (R : ℂ) ∈ (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (relOff κ θ b₁ J₁ R D₁))
          (D₁ (relOff κ θ b₁ J₁ R D₁))).1.tipSet
        (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (relOff κ θ b₁ J₁ R D₁))
          (D₁ (relOff κ θ b₁ J₁ R D₁))).2.1
        (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (relOff κ θ b₁ J₁ R D₁))
          (D₁ (relOff κ θ b₁ J₁ R D₁))).2.2 := by
  set o := relOff κ θ b₁ J₁ R D₁ with ho
  obtain ⟨hl, hseed⟩ := launch_seed_of_not_zeroRoot hb hX hP hW hlm hlh hallow hdone hR hZ
  refine ⟨hl, hseed, ?_⟩
  obtain ⟨⟨c₁, θ₁⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hmem := mem_succ_of_not_zeroRoot hR hZ
  have hsucc := prefixPhysSet_succ_of_launch hl'
  change (R : ℂ) ∈ SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1) at hmem
  rw [hsucc] at hmem
  rcases hmem with hold | htip
  · have hpt := hseed hold
    by_cases h0 : (D₁ o).2 = 0
    · rw [tipSet_zero_launch hP hW hl h0, hpt]
      exact mem_singleton _
    · obtain ⟨_, -, -, -, htip⟩ := tipSet_newPc_launch hP hl
      rw [htip]
      exact ⟨0, by simp, by rw [pcPt_zero_launch hP hW hl h0, hpt]⟩
  · exact htip


/-- A launching state is at its record. -/
theorem pt_eq_recR_of_launch (hP : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hlm : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j) {n : ℕ}
    (hl : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1)).2.2.2.1 n ≠ none) :
    stPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) =
      stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) := by
  obtain ⟨⟨c₁, θ₁⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd := Lx.stStatus_ne_done_of_launches _ D₁ hl'
  have hnone := launches_run_of_le (κ := κ) (b := b₁) (jumps := J₁) (boundaryWalkSpec b₁ J₁ θ true) D₁ (le_refl n)
  have hev := GW1W.even_of_launches_walk hl
  have hstep := GW1W.run_succ_walk_flow (κ := κ) (D := D₁) hev.2 hev.1
  rcases (recInv_ptRec_upto_launch hP hlm hlh hnd n le_rfl).2 with h | h | h
  · exact absurd h hnd
  · rw [hstep, flowStep_of_dead h] at hl; exact absurd hnone hl
  · exact h

/-- The relative root's tip set is its trace (identity chart). -/
theorem tipSet_init_eq (hP₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂)
    (hpr : GW1P.PieceRegular (D₂ 0).1 (D₂ 0).2) (hfin : (D₂ 0).2 ≠ ⊤) :
    (newPc (ExplState.init 0) (D₂ 0)).1.tipSet (newPc (ExplState.init 0) (D₂ 0)).2.1
      (newPc (ExplState.init 0) (D₂ 0)).2.2 = trOf (D₂ 0) '' Icc 0 (D₂ 0).2.toNNReal := by
  have hl : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (0 + 1)).2.2.2.1 0 ≠ none := by
    rw [GW1.launches_run_one_boundaryWalkSpec]; exact Option.some_ne_none _
  obtain ⟨_, -, -, -, htip⟩ := tipSet_newPc_launch hP₂ hl
  have htip' : (newPc (ExplState.init 0) (D₂ 0)).1.tipSet (newPc (ExplState.init 0) (D₂ 0)).2.1
      (newPc (ExplState.init 0) (D₂ 0)).2.2 = pcPt (ExplState.init 0) (D₂ 0) '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D₂ 0).2} :=
    htip
  rw [htip']
  have hT : ((D₂ 0).2.toNNReal : ℝ≥0∞) = (D₂ 0).2 := ENNReal.coe_toNNReal hfin
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D₂ 0).2} = Icc 0 (D₂ 0).2.toNNReal := by
    ext t
    constructor
    · intro h
      exact ⟨zero_le, by rw [← ENNReal.coe_le_coe, hT]; exact h⟩
    · intro h
      show (t : ℝ≥0∞) ≤ (D₂ 0).2
      rw [← hT]
      exact ENNReal.coe_le_coe.2 h.2
  rw [hset]
  have hαg := isGeneratingTrace_trOf hpr
  have hWlt : ContinuousOn (D₂ 0).1 {t | (t : ℝ≥0∞) < (D₂ 0).2} :=
    hpr.2.1.mono fun _ (hs : _ < (D₂ 0).2) => (le_of_lt hs : _ ≤ (D₂ 0).2)
  have hid : (stChart (ExplState.init 0)).2.1 = id := funext fun z => by
    simp [stChart, ExplState.init, Chart.recenter, Chart.id]
  refine image_congr fun t ht => ?_
  have hH := Sec7.IsGeneratingTrace.mem_Hbar hαg hWlt hpr.1 (hT ▸ ENNReal.coe_le_coe.2 ht.2)
  unfold pcPt
  refine LuM.bdVal_eq_of_tendsto hH ?_
  rw [hid]
  exact tendsto_id.mono_left nhdsWithin_le_nhds

/-- **The piece start at `relOff`** off a zero root, at a positive shifted lifetime. -/
theorem pieceStartV_of (hb : IsPiecewiseConstantBoundaryData b₁ J₁) (hX : RunExitData κ b₁ J₁ θ D₁)
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hW₁ : WalkChainFacts κ b₁ J₁ θ D₁)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hposW : ∀ n, 0 < n → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1)).2.2.2.1 n ≠ none →
      (D₁ n).2 ≠ 0)
    (hallow : ∀ n, 1 ≤ n → AllowedSt κ b₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n))
    (hdone : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁
      (boundaryWalkSpec b₁ J₁ θ true).2.2.length) = stDone)
    (hRH : ∀ n, (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1)).2.2.2.1 n ≠ none →
      (D₁ n).2 ≠ ⊤ → (D₁ n).2 ≠ 0 → ∃ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) < x ∧
        lHit (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n)) ⊤ (D₁ n) x)
    (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hD : LiftCurveData β₀ γ tL R ι) (hγ : IsTailLiftCurve c R m β₀ tL γ)
    (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hU : UpperChartOK c)
    (hK : β₀ '' Icc 0 tL ⊆ hullK A) (hDom : c.2.1 '' H = H \ fillH A)
    (hhead : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R) (hZ : ¬ ZeroRoot κ θ b₁ J₁ R D₁)
    (hL0 : (D₁ (relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0 ≠ 0)
    (hP₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂) (hreg₂ : IsRegularDriver (D₂ 0))
    (hRF : RootFactsAt κ θ b₁ J₁ b₂ J₂ R c m D₁ D₂) (hPL : PiecesLift2 κ θ b₁ J₁ b₂ J₂ R D₁ D₂ β₀ γ tL) :
    PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL (relOff κ θ b₁ J₁ R D₁) := by
  set o := relOff κ θ b₁ J₁ R D₁ with ho
  set s₁ := ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o with hs₁
  have hR : (R : ℂ) ∈ ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ := by
    rw [← hβr]; exact ⟨tL, hγ.1⟩
  obtain ⟨hl, hseed, hRtip⟩ := memR_of_not_zeroRoot hb hX hP₁ hW₁ hlm₁ hlh₁ hallow hdone hR hZ
  obtain ⟨⟨c₁, θ₁⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hlaunch := GW1W.launch_walk hl
  have hnd : stStatus s₁ ≠ stDone := Lx.stStatus_ne_done_of_launches _ D₁ hl'
  have hrp := recInv_ptRec_upto_launch hP₁ hlm₁ hlh₁ hnd
  have hlen := succ_lt_length_of_launch hl
  have hhd : statePhysicalSet 0 s₁ ⊆ β₀ '' Iic tL :=
    head_of_pieceStart hW₁.1 hW₁.2 le_rfl hdone hβ hβ0 hβr hγ.1 (by omega) hlaunch hRtip
  have hptmem : (stPt s₁ : ℂ) ∈ statePhysicalSet 0 s₁ := (prefix_facts hW₁.1 hW₁.2 o).2 hnd
  have hptR : stPt s₁ ≤ R := by
    obtain ⟨t, ht, e⟩ := hhd hptmem
    exact hhead t ht _ e
  obtain ⟨htipne, hrecLe⟩ := piece_fields_of_launch hl
    (by rcases Nat.eq_zero_or_pos o with h | h; exacts [Or.inl h, Or.inr (hallow o h)]) (hrp o le_rfl).2 hptR
  have hpos₁ : (D₁ o).2 ≠ 0 := fun h => hL0 (by rw [h]; exact zero_tsub _)
  have hsh : shiftD κ θ b₁ J₁ R D₁ 0 = visitTime s₁ (D₁ o) R := by simp only [shiftD, ↓reduceIte]; rfl
  obtain ⟨_, -, -, -, htip₁⟩ := tipSet_newPc_launch hP₁ hl
  have hRex : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D₁ o).2 ∧ pcPt s₁ (D₁ o) t = (R : ℂ) := by
    rw [htip₁] at hRtip
    obtain ⟨t, ht, e⟩ := hRtip
    exact ⟨t, ht, e⟩
  obtain ⟨ht₀le, hpR, -⟩ := visitTime_spec hP₁ hl hRex
  obtain ⟨-, hposF, hgood⟩ := hRF
  obtain ⟨hpos₂, hF⟩ := hposF hZ hL0
  rw [hsh] at hF hL0
  have hRmem := mem_succ_of_not_zeroRoot hR hZ
  obtain ⟨hPc, -, -, htl, -⟩ := rootInputs hP₁ hW₁ hl hpos₁ hβ hβr hK hDom hγ.1 hRmem hseed
    hF.2.2.2.2.1 hL0
  have hpt₁ : stPt s₁ ≤ stRecR s₁ := (pt_eq_recR_of_launch hP₁ hlm₁ hlh₁ hl).le
  have hpr₂ : GW1P.PieceRegular (D₂ 0).1 (D₂ 0).2 := hF.2.2.2.2.2.2
  have hf := rootFields (θ := θ) hι hD hγ hβ hU hβr hP₁ hW₁ (fun k hk => (hrp k hk).1) hlm₁ hl hlen.le hpt₁
    (hRH o hl) hpR hL0 hPc htl hreg₂ hF hgood hpos₂ (hPL.2 hZ hl) (tipSet_init_eq hP₂ hpr₂)
  refine ⟨relOff_even κ θ b₁ J₁ R D₁, hlaunch, htipne, hptR, hrecLe, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1,
    hf.2.2.2.2, hPL.2 hZ hl, hRtip, fun hfin => ?_, fun k hk hlk => ?_,
    ⟨hlen, one_lt_length_boundaryWalkSpec b₂ J₂ θ true⟩, hhd⟩
  · -- the new record is the end point, beyond `R`
    obtain ⟨x, hx, hhit⟩ := hRH o hl hfin hpos₁
    have hpre : SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1) ⊆ range β₀ := by
      rw [hβr]; exact prefix_subset_physSet D₁ hlen.le
    have hPH : SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1) ⊆ Hbar := by
      intro w hw
      obtain ⟨t, rfl⟩ := hpre hw
      exact hβ.2.2.1 t
    have hsucc := prefixPhysSet_succ_of_launch hl'
    have hH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D₁ o).2 → pcPt s₁ (D₁ o) t ∈ Hbar := fun t ht =>
      hPH (by rw [hsucc]; exact Or.inr (by rw [htip₁]; exact ⟨t, ht, rfl⟩))
    obtain ⟨hbef, z, hz, hxz, hmax⟩ :=
      actual_end hP₁ hW₁ (fun k hk => (hrp k hk).1) hlm₁ hl hfin hpos₁ hpt₁ hH hPH hx hhit
    have ht₀e : ((visitTime s₁ (D₁ o) R : ℝ≥0) : ℝ≥0∞) < (D₁ o).2 := by
      by_contra h
      push Not at h
      exact hL0 (tsub_eq_zero_of_le h)
    have hRz : R < z := lt_of_lt_of_le (hbef _ ht₀e R hpR) hxz
    have hzmem : (z : ℂ) ∈ SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1) := by
      rw [hsucc, htip₁, ← hz]
      exact Or.inr ⟨(D₁ o).2.toNNReal,
        show ((D₁ o).2.toNNReal : ℝ≥0∞) ≤ (D₁ o).2 from ENNReal.coe_toNNReal_le_self, rfl⟩
    have hzcl := mem_closure_prefix_succ_of_mem hP₁ hl' hfin (fun k hk => (hrp k hk).1) hlm₁ hnd
      (lt_of_lt_of_le hx hxz) hzmem
    have hrec := lRecR_eq_end hP₁ (fun k hk => (hrp k hk).1) hl hfin hPH (lt_of_lt_of_le hx hxz) hzcl hmax
    obtain ⟨-, -, hrecL, -, -, -⟩ := launch_eq_of_ne_top s₁ o (D₁ o) θ ⊤ (min_top_ne_top hfin)
    rw [hlaunch, hrecL, hrec]
    exact hRz.le
  · rcases eq_or_lt_of_le hk with rfl | h
    · exact hpos₁
    · exact hposW k (by omega) hlk

/-- **The arc start at a zero root**, with its head inclusion. -/
theorem arcStart_of_zeroRoot (hb : IsPiecewiseConstantBoundaryData b₁ J₁) (hX : RunExitData κ b₁ J₁ θ D₁)
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hW₁ : WalkChainFacts κ b₁ J₁ θ D₁)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hposW : ∀ n, 0 < n → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1)).2.2.2.1 n ≠ none →
      (D₁ n).2 ≠ 0)
    (hallow : ∀ n, 1 ≤ n → AllowedSt κ b₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n))
    (hdone : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁
      (boundaryWalkSpec b₁ J₁ θ true).2.2.length) = stDone)
    (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hβL : β₀ tL = R)
    (hZ : ZeroRoot κ θ b₁ J₁ R D₁) (hreg₂ : IsRegularDriver (D₂ 0)) (hz : D₂ 0 = zeroDrv) :
    ArcStart κ θ b₁ J₁ R D₁ D₂ β₀ tL (relOff κ θ b₁ J₁ R D₁) := by
  have hR : (R : ℂ) ∈ ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ := by
    rw [← hβr]; exact ⟨tL, hβL⟩
  have hA := arcStartData_of_zeroRoot_ae hb hX hP₁ hlm₁ hlh₁ hposW hallow (exists_mem_statePhysicalSet_succ hR) hZ
    hreg₂ hz
  exact { hA with
    head := head_of_arcStart hW₁.1 hW₁.2 le_rfl hdone hβ hβ0 hβr hβL hA.len.le hA.len
      (by have := hA.even; omega) hA.move hA.pt hA.gap }

/-- **The arc start at a corner** (off a zero root at a zero shifted lifetime): after the start piece the walk stands
at `R` on an outward right threshold. -/
theorem arcStart_of_corner (hb : IsPiecewiseConstantBoundaryData b₁ J₁) (hX : RunExitData κ b₁ J₁ θ D₁)
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hW₁ : WalkChainFacts κ b₁ J₁ θ D₁)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hposW : ∀ n, 0 < n → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1)).2.2.2.1 n ≠ none →
      (D₁ n).2 ≠ 0)
    (hallow : ∀ n, 1 ≤ n → AllowedSt κ b₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n))
    (hdone : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁
      (boundaryWalkSpec b₁ J₁ θ true).2.2.length) = stDone)
    (hRH : ∀ n, (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1)).2.2.2.1 n ≠ none →
      (D₁ n).2 ≠ ⊤ → (D₁ n).2 ≠ 0 → ∃ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) < x ∧
        lHit (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n)) ⊤ (D₁ n) x)
    (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hβL : β₀ tL = R)
    (hZ : ¬ ZeroRoot κ θ b₁ J₁ R D₁)
    (hL0 : (D₁ (relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0 = 0)
    (hreg₂ : IsRegularDriver (D₂ 0)) (hz : D₂ 0 = zeroDrv) :
    ArcStart κ θ b₁ J₁ R D₁ D₂ β₀ tL (relOff κ θ b₁ J₁ R D₁) := by
  set o := relOff κ θ b₁ J₁ R D₁ with ho
  set s₁ := ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o with hs₁
  have hR : (R : ℂ) ∈ ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ := by
    rw [← hβr]; exact ⟨tL, hβL⟩
  obtain ⟨hl, hseed, hRtip⟩ := memR_of_not_zeroRoot hb hX hP₁ hW₁ hlm₁ hlh₁ hallow hdone hR hZ
  obtain ⟨⟨c₁, θ₁⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hlaunch := GW1W.launch_walk hl
  have hnd : stStatus s₁ ≠ stDone := Lx.stStatus_ne_done_of_launches _ D₁ hl'
  have hrp := recInv_ptRec_upto_launch hP₁ hlm₁ hlh₁ hnd
  have hlen := succ_lt_length_of_launch hl
  have ho2 : o % 2 = 0 := relOff_even κ θ b₁ J₁ R D₁
  have hsh : shiftD κ θ b₁ J₁ R D₁ 0 = visitTime s₁ (D₁ o) R := by simp only [shiftD, ↓reduceIte]; rfl
  rw [hsh] at hL0
  obtain ⟨_, -, -, -, htip₁⟩ := tipSet_newPc_launch hP₁ hl
  have hRex : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D₁ o).2 ∧ pcPt s₁ (D₁ o) t = (R : ℂ) := by
    rw [htip₁] at hRtip
    obtain ⟨t, ht, e⟩ := hRtip
    exact ⟨t, ht, e⟩
  obtain ⟨ht₀le, hpR, -⟩ := visitTime_spec hP₁ hl hRex
  have he : (D₁ o).2 = (visitTime s₁ (D₁ o) R : ℝ≥0∞) := le_antisymm (tsub_eq_zero_iff_le.1 hL0) ht₀le
  have hfin : (D₁ o).2 ≠ ⊤ := by rw [he]; exact ENNReal.coe_ne_top
  set s := ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1) with hs
  obtain ⟨-, -, hrecL, -, hstL, hptL⟩ := launch_eq_of_ne_top s₁ o (D₁ o) θ ⊤ (min_top_ne_top hfin)
  have hnlt : ¬ (⊤ : ℝ≥0∞) < (D₁ o).2 := not_lt.2 le_top
  -- after the start piece the walk stands at `R` on an outward right threshold
  have hkey : stPt s = R ∧ GW1WalkFinish.OutwardThreshold κ b₁ true s := by
    by_cases h0 : (D₁ o).2 = 0
    · have hptR : stPt s₁ = R := by
        have := stPt_eq_of_zero_life hP₁ hW₁ hposW hR hZ hl h0
        exact_mod_cast this
      obtain ⟨htipne, -⟩ := piece_fields_of_launch hl
        (by rcases Nat.eq_zero_or_pos o with h | h; exacts [Or.inl h, Or.inr (hallow o h)])
        (hrp o le_rfl).2 hptR.le
      have hst : stStatus s = stThr none := by
        rw [hlaunch, hstL]
        unfold lStatus
        simp only [h0, ↓reduceIte]
        revert htipne
        rcases stStatus s₁ with u | u | u | u | u | u <;> intro htipne <;> first | rfl | exact absurd rfl htipne
      have hpts : stPt s = R := by
        rw [hlaunch, hptL]
        unfold lPt
        simp only [h0, ↓reduceIte]
        exact hptR
      refine ⟨hpts, ?_⟩
      rcases hallow (o + 1) (by omega) with h | h | h | h
      · rw [hst] at h; cases h
      · rw [hst] at h; cases h
      · rw [hst] at h; cases h
      · exact h
    · obtain ⟨x, hx, hhit⟩ := hRH o hl hfin h0
      have hpre : SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1) ⊆ range β₀ := by
        rw [hβr]; exact prefix_subset_physSet D₁ hlen.le
      have hPH : SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1) ⊆ Hbar := by
        intro w hw
        obtain ⟨t, rfl⟩ := hpre hw
        exact hβ.2.2.1 t
      have hsucc := prefixPhysSet_succ_of_launch hl'
      have hH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D₁ o).2 → pcPt s₁ (D₁ o) t ∈ Hbar := fun t ht =>
        hPH (by rw [hsucc]; exact Or.inr (by rw [htip₁]; exact ⟨t, ht, rfl⟩))
      have hpt₁ : stPt s₁ ≤ stRecR s₁ := (pt_eq_recR_of_launch hP₁ hlm₁ hlh₁ hl).le
      obtain ⟨-, z, hz, hxz, hmax⟩ :=
        actual_end hP₁ hW₁ (fun k hk => (hrp k hk).1) hlm₁ hl hfin h0 hpt₁ hH hPH hx hhit
      have hzR : z = R := by
        have hvt : (D₁ o).2.toNNReal = visitTime s₁ (D₁ o) R := by rw [he]; rfl
        rw [hvt, hpR] at hz
        exact_mod_cast hz.symm
      have hzmem : (z : ℂ) ∈ SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1) := by
        rw [hsucc, hzR]
        exact Or.inr hRtip
      have hzcl := mem_closure_prefix_succ_of_mem hP₁ hl' hfin (fun k hk => (hrp k hk).1) hlm₁ hnd
        (lt_of_lt_of_le hx hxz) hzmem
      have hrec := lRecR_eq_end hP₁ (fun k hk => (hrp k hk).1) hl hfin hPH (lt_of_lt_of_le hx hxz) hzcl hmax
      have hex : ∃ x : ℝ, stRecR s₁ < x ∧ lHit (stChart s₁) ⊤ (D₁ o) x := ⟨x, hx, hhit⟩
      refine ⟨?_, Or.inl ?_⟩
      · rw [hlaunch, hptL]
        unfold lPt
        simp only [hnlt, h0, hex, ↓reduceIte]
        rw [hrec, hzR]
      · rw [hlaunch, hstL]
        unfold lStatus
        simp only [hnlt, h0, hex, ↓reduceIte]
  obtain ⟨hpts, hout⟩ := hkey
  have hthr : stStatus s = stThr (some true) ∨
      (stStatus s = stThr none ∧ rightLim b₁ (stPt s) + stAngle s * chiC κ ≤ -sleLambda κ) := by
    rcases hout with h | ⟨h, hlow⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, by simpa using hlow⟩
  have hmove : ExplState.contStep κ b₁ J₁ s none true =
      if hC : (restartSet κ b₁ J₁ s).Nonempty then
        ExplState.moveAlong s true ((restartSet κ b₁ J₁ s).min' hC) true else ExplState.moveToEnd s true := by
    rcases hthr with h | ⟨h, hlow⟩
    · exact contStep_thr_true' b₁ J₁ s h
    · exact contStep_thr_none_right b₁ J₁ s h hlow
  have hgap : ∀ y ∈ restartSet κ b₁ J₁ s, R < y := fun y hy => by
    rw [← hpts]; exact (Finset.mem_filter.1 hy).2.1
  have hnd1 : stStatus s ≠ stDone := by
    rcases hthr with h | ⟨h, -⟩ <;> rw [h] <;> intro e <;> cases e
  have hrecs : stRecR s ≤ R := by
    rcases (recInv_ptRec_upto_launch hP₁ hlm₁ hlh₁ hnd1 (o + 1) le_rfl).2 with h | h | h
    · exact absurd h hnd1
    · rcases hthr with h' | ⟨h', -⟩ <;> rw [h'] at h <;> cases h
    · rw [← h, hpts]
  have hlow := low_at_threshold' hX ho2 (by omega) hthr
  rw [hpts] at hlow
  have hzero : (D₂ 0).2 = 0 := by rw [hz]; rfl
  exact ⟨ho2, hlen, hmove, stAngle_run_walk (o + 1) (by omega), hpts.le, hrecs, hgap, hlow, hreg₂, hzero,
    fun k hk hlk => hposW k (by omega) hlk,
    head_of_arcStart hW₁.1 hW₁.2 le_rfl hdone hβ hβ0 hβr hβL hlen.le hlen (by omega) hmove hpts.le hgap⟩

end InteractingSLE.Theorem14.SB.Lk
