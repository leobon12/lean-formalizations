/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2YaStart

/-!
# The piece start at `relOff` from the stage-`0` facts only

Packet PROVE-T14-SB2LIFT (round 32; decision D40). `pieceStartV_of` (`SB2YaStart`) takes the relative walk's regular
launches and LIFTSET's piece lifts `PiecesLift2` at all stages, but reads them only at the relative root. Here:
* `regLaunches_const`: the constant family of a regular piece has regular launches;
* **`pieceStartV_of0`**: `PieceStartV` at `relOff` from the actual walk's facts, the root facts `RootFactsAt` and the
  root lift relation alone (the same proof, the root tip set read through the constant family).
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

/-- The constant family of a regular piece has regular launches (every launch of a boundary walk is uncapped). -/
theorem regLaunches_const {e : Drv} (he : GW1P.PieceRegular e.1 e.2) :
    RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) (fun _ => e) := by
  intro k c' θ' hl
  have hl' : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) (fun _ => e) (k + 1)).2.2.2.1 k ≠ none := by
    rw [hl]; exact Option.some_ne_none _
  rw [GW1W.instrTime_walk hl', min_eq_right le_top]
  exact he

/-- **The piece start at `relOff` from the stage-`0` facts only** (`pieceStartV_of` with the root lift relation and the
root regularity in place of the relative walk's launches and the piece lifts at all stages). -/
theorem pieceStartV_of0 (hb : IsPiecewiseConstantBoundaryData b₁ J₁) (hX : RunExitData κ b₁ J₁ θ D₁)
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
    (hreg₂ : IsRegularDriver (D₂ 0)) (hRF : RootFactsAt κ θ b₁ J₁ b₂ J₂ R c m D₁ D₂)
    (hPL0 : ¬ ZeroRoot κ θ b₁ J₁ R D₁ →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (relOff κ θ b₁ J₁ R D₁ + 1)).2.2.2.1
        (relOff κ θ b₁ J₁ R D₁) ≠ none →
      LiftRel β₀ tL γ (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (relOff κ θ b₁ J₁ R D₁))
        (D₁ (relOff κ θ b₁ J₁ R D₁))) (newPc (ExplState.init 0) (D₂ 0))) :
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
    (hRH o hl) hpR hL0 hPc htl hreg₂ hF hgood hpos₂ (hPL0 hZ hl)
    (tipSet_init_eq (κ := κ) (θ := θ) (b₂ := b₂) (J₂ := J₂) (D₂ := fun _ => D₂ 0) (regLaunches_const hpr₂) hpr₂)
  refine ⟨relOff_even κ θ b₁ J₁ R D₁, hlaunch, htipne, hptR, hrecLe, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1,
    hf.2.2.2.2, hPL0 hZ hl, hRtip, fun hfin => ?_, fun k hk hlk => ?_,
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

end InteractingSLE.Theorem14.SB.Lk
