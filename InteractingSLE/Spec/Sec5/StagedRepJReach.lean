/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedRepJPieces
import InteractingSLE.Spec.Sec5.StagedNodeReach

/-!
# Prop 5.9's tree candidates: a reached list is alive

Packet PROVE-STAGED-REPJ. PROVE-STAGED-NODE's `alive_of_mem_canonR` (node experiments) for a tree family itself
(PIECES' root tree, or REP2's tree `gamData` on `Gam`): for tree data with the admissible lists `IsValid`, on the
canonical reached event of a list `t` of positive length the candidate `t` is alive (in particular `t` is admissible),
and
the start driver is outside the band of its depth. The proof is NODE's, without the node dilation.

* **`TreeData.reach`**.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CrossCond.StagedRepJ

open WangWu WangWu.ImgWord Prop59System Prop59Stage Prop59Pieces StagedCand StagedAdapt StagedNode
open Sec7.Lemma71C (capClock)
open CrossRestart (physTime physTime_nonneg physTime_lt_one)

section Reach

variable {Ω : Type*} [MeasurableSpace Ω] {nL₀ nR₀ : ℕ} {D : TreeData Ω nL₀ nR₀} (hnL : 0 < nL₀) (hnR : 0 < nR₀)

/-- The root start of a tree: the driver at `0` and the root marks. -/
abbrev treeY0 (D : TreeData Ω nL₀ nR₀) (ω : Ω) : Start (nL₀ + 0) (nR₀ + 0) := ((0 : ℝ), D.xL0 ω, D.xR0 ω)

theorem measurable_treeY0 (hD : D.IsReg) : Measurable (treeY0 D) :=
  measurable_const.prodMk (hD.xL0.prodMk hD.xR0)

/-- **A reached list of positive length is alive**, and the start driver is outside the band of its depth. -/
theorem TreeData.reach (hD : D.IsReg) (hT : D.IsTree) (hval : ∀ j t, D.valid j t ↔ IsValid j t) {R₀ : Set Ω} :
    ∀ (j : ℕ) (t : Fin j → ℝ≥0) (ω : Ω), ω ∈ canonR D.cand ratGrid hnL hnR (treeY0 D) R₀ j t →
      (canonY D.cand (treeY0 D) j t ω).1 ∉ band j ∧ (0 < j → ω ∈ D.alive j t)
  | 0, t, ω, _ => by
    refine ⟨?_, fun h => absurd h (lt_irrefl 0)⟩
    show (0 : ℝ) ∉ band 0
    rw [band_even (⟨0, rfl⟩ : Even 0)]
    intro h0
    linarith [h0.2]
  | j + 1, t, ω, hR => by
    simp only [canonR, mem_inter_iff, mem_iUnion] at hR
    obtain ⟨hR', n', m', hgrid, hsw⟩ := hR
    obtain ⟨hband', -⟩ := TreeData.reach hD hT hval j (Fin.init t) ω hR'
    have hreg := isRegStage_candStage (hnL := hnL) (hnR := hnR) hD.isRegFam (measurable_treeY0 hD) j (Fin.init t)
    obtain ⟨hsucc, hidx⟩ := hsw
    have hss := (swIdx_spec hreg hsucc).1
    rw [hidx, hgrid] at hss
    obtain ⟨hhit, hlt, hbandS, -⟩ := hss
    have hclk := clk_clkInv hhit
    set s := clkInv (candStage D.cand (canonY D.cand (treeY0 D)) j (Fin.init t)) (t (Fin.last j)) ω with hs
    have hγ := (hD.isKilledFamily j (Fin.init t)).arc ω
    have hlt' : ((s : ℝ≥0) : ℝ≥0∞) < (D.cand j (Fin.init t)).ζ ω := hlt
    obtain ⟨hA', hlife⟩ := lt_arcζ_iff.1 hlt'
    -- the switch is at a positive piece time
    have hspos : 0 < s := by
      rcases eq_zero_or_pos s with h0 | h0
      · exfalso
        have hb0 := hbandS
        change (canonY D.cand (treeY0 D) j (Fin.init t) ω).1 + (D.cand j (Fin.init t)).W s ω ∈ band j at hb0
        rw [h0] at hb0
        have hw0 : (D.cand j (Fin.init t)).W 0 ω = 0 := arcW_zero' ω
        rw [hw0, add_zero] at hb0
        exact hband' hb0
      · exact h0
    -- the clock at the switch
    have hclk' : (D.cand j (Fin.init t)).clk ω s = t (Fin.last j) := hclk
    rw [TreeData.clk_cand, arcClk_of_mem hA'] at hclk'
    have hclk'' : absClock (D.img j (Fin.init t) ω) (D.pre j (Fin.init t) ω) (D.startCap j (Fin.init t) ω + s) =
        t (Fin.last j) := hclk'
    rw [absClock_of_lt hlife] at hclk''
    obtain ⟨huP, hucap⟩ := hγ.kInv_spec hlife
    set u := WangWu.ImgWord.kInv (D.img j (Fin.init t) ω) (D.pre j (Fin.init t) ω)
      (D.startCap j (Fin.init t) ω + s) with hu
    have hvp : IsValid j (Fin.init t) := (hval _ _).1 hA'.1.1
    have hq0 : 0 ≤ qLast j (Fin.init t) := hT.qnonneg j (Fin.init t) hA'.1.1
    -- the switch is after the last switch of the parent
    have hqu : qLast j (Fin.init t) < u := by
      by_contra hle
      push Not at hle
      have h1 := hγ.strictMonoOn_capClock.monotoneOn huP hA'.2 hle
      have h2 : (D.startCap j (Fin.init t) ω : ℝ) = capClock (D.img j (Fin.init t) ω) (qLast j (Fin.init t)) :=
        Prop59NodeTree.TreeData.startCap_coe hD hA'
      rw [hucap, NNReal.coe_add, ← h2] at h1
      have : (0 : ℝ) < ((s : ℝ≥0) : ℝ) := NNReal.coe_pos.2 hspos
      linarith
    have hu0 : 0 ≤ u := hq0.trans hqu.le
    have hlast : (physTime u).toNNReal = t (Fin.last j) := hclk''
    -- the list is admissible
    have hvalid : IsValid (j + 1) t := by
      refine isValid_of_init hvp (fun i => ?_) ?_ ?_ ?_
      · rw [← hlast]
        have hi := (decode_le_qLast hvp i).trans_lt hqu
        have h1 : Fin.init t i < 1 := (hvp.2 i).2.1
        have e : (physTime (decode (Fin.init t i))).toNNReal = Fin.init t i := by
          rw [physTime_decode h1, Real.toNNReal_coe]
        rw [← e]
        exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg (physTime_nonneg (decode_nonneg h1))).2
          (physTime_lt_physTime (decode_nonneg h1) hi)
      · rw [← hlast]
        refine Real.toNNReal_pos.2 ?_
        unfold physTime
        exact div_pos (hq0.trans_lt hqu) (by linarith)
      · rw [← hlast]
        exact (Real.toNNReal_lt_iff_lt_coe (physTime_nonneg hu0)).2 (by simpa using physTime_lt_one hu0)
      · rw [← hgrid]
        exact ratGrid_isRat n' m'
    have hvc : D.valid (j + 1) t := (hval _ _).2 hvalid
    have hqc : qLast (j + 1) t = u := by
      show decode (t (Fin.last j)) = u
      rw [← hlast, decode_physTime hu0]
    have hpre : qLast (j + 1) t ∈ D.pre (j + 1) t ω := by
      rw [hT.mem_pre_iff hvc hA'.1.2 le_rfl, hqc]
      exact huP
    have hy : (canonY D.cand (treeY0 D) (j + 1) t ω).1 ∈ band j := hbandS
    exact ⟨band_disjoint j hy, fun _ => ⟨⟨hvc, hA'.1.2⟩, hpre⟩⟩

end Reach

end InteractingSLE.Sec5.CrossCond.StagedRepJ
