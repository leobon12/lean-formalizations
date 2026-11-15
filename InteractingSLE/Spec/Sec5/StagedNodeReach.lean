/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedNodeOrder

/-!
# Proposition 5.9's node experiments: a reached stage has an alive tree candidate

Packet PROVE-STAGED-NODE. On the reached event `canonR … j t` of a node experiment, the tree candidate of the full list
`nodePre s ++ t` (depth `m + j`) is alive (admissible, good, last switch before its first new contact), and the absolute
driver of the start is outside the switching band of depth `j` (it is `0` at the node tip, and in the band of depth
`j − 1` after a switch; consecutive bands are disjoint). The band invariant makes every realized switch happen at a
positive piece time, so the new list is strictly increasing.

* `decode_physTime`, `physTime_lt_physTime`, `ratGrid_isRat`, `decode_le_qLast`, `isValid_of_init`: clock helpers;
* **`alive_of_mem_canonR`**.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CrossCond.StagedNode

open Sec4 (IsStripGFF IsStripCounterflowDriver)
open Prop513TreeExtract Prop513Schedule Prop513Target Exist.StagedLaw Exist.Staged Sec7.AdmCode Restart
open Prop59System Prop59Stage Prop59Pieces Prop59Nodes Prop59Sched StagedKCand StagedKill StagedRep StagedRepLater
open Wire.Night LawUnique WangWu GlueCond Word49 Prop59NodeTree StagedS4 StagedCand StagedAdapt
open Sec7.Lemma71C (capClock)
open CrossRestart (physTime physTime_nonneg physTime_lt_one)

/-! ### Clock helpers -/

theorem decode_physTime {u : ℝ} (hu : 0 ≤ u) : decode (physTime u).toNNReal = u := by
  rw [decode, Real.coe_toNNReal _ (physTime_nonneg hu), physTime]
  have h1 : (1 + u) ≠ 0 := by linarith
  have h2 : 1 - u / (1 + u) = 1 / (1 + u) := by field_simp; ring
  rw [h2]
  field_simp

theorem physTime_lt_physTime {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : physTime a < physTime b := by
  unfold physTime
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem ratGrid_isRat (n k : ℕ) : ∃ q : ℚ, ((ratGrid n k : ℝ≥0) : ℝ) = q :=
  ⟨((k : ℚ) + 1) / ((n : ℚ) + 1), by
    rw [ratGrid, Real.coe_toNNReal _ (Rat.cast_nonneg.2 (by positivity))]⟩

theorem decode_le_qLast {k : ℕ} {tt : Fin k → ℝ≥0} (hv : IsValid k tt) (i : Fin k) : decode (tt i) ≤ qLast k tt := by
  cases k with
  | zero => exact i.elim0
  | succ k =>
    rcases (Fin.le_last i).eq_or_lt with hi | hi
    · rw [hi]; exact le_rfl
    · exact (decode_strictMono (hv.2 _).2.1 (hv.1 hi)).le

/-- A list is admissible if its parent is and its last value is a later rational value in `(0, 1)`. -/
theorem isValid_of_init {k : ℕ} {tt : Fin (k + 1) → ℝ≥0} (hv : IsValid k (Fin.init tt))
    (hlt : ∀ i : Fin k, Fin.init tt i < tt (Fin.last k)) (h0 : 0 < tt (Fin.last k)) (h1 : tt (Fin.last k) < 1)
    (hq : ∃ q : ℚ, (tt (Fin.last k) : ℝ) = q) : IsValid (k + 1) tt := by
  refine ⟨fun i i' hii => ?_, fun i => ?_⟩
  · induction i' using Fin.lastCases with
    | last =>
      induction i using Fin.lastCases with
      | last => exact absurd hii (lt_irrefl _)
      | cast i => exact hlt i
    | cast i' =>
      induction i using Fin.lastCases with
      | last => exact absurd hii (not_lt.2 (Fin.le_last _))
      | cast i => exact hv.1 (Fin.castSucc_lt_castSucc_iff.1 hii)
  · induction i using Fin.lastCases with
    | last => exact ⟨h0, h1, hq⟩
    | cast i => exact hv.2 i

theorem band_disjoint (j : ℕ) {x : ℝ} (hx : x ∈ band j) : x ∉ band (j + 1) := by
  rcases Nat.even_or_odd j with hj | hj
  · have hj' : ¬ Even (j + 1) := Nat.not_even_iff_odd.2 hj.add_one
    rw [band_even hj] at hx
    rw [band_odd hj']
    intro h
    linarith [hx.2, h.1]
  · have hj' : Even (j + 1) := hj.add_one
    rw [band_odd (Nat.not_even_iff_odd.2 hj)] at hx
    rw [band_even hj']
    intro h
    linarith [hx.1, h.2]

/-! ### A reached node stage has an alive tree candidate -/

section Reach

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω Ωa : Type} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ωa]
  (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
  (noise : ℕ → ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ)

theorem isRegFam_nodeCand (hhm : Measurable h) (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (n : ℕ) (q : ℚ) : IsRegFam (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q) :=
  isRegFam_liftFam (IsRegFam.scaleFam (measurable_nodeScale x₀ h44 hκ hκ4 hb P h W ζ noise hhm hcf n q)
    (nodeScale_pos x₀ h44 hκ hκ4 hb P h W ζ noise n q)
    (Prop59Nodes.IsRegFam.subFam (isReg_nodeD x₀ h44 hκ hκ4 hb P h W ζ noise hhm hcf n q).isRegFam _ _))

theorem measurable_nodeStart (hhm : Measurable h)
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (n : ℕ) (q : ℚ) :
    Measurable (nodeStart (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q) := by
  obtain ⟨hL, hR⟩ := measurable_nodeMarks x₀ h44 hκ hκ4 hb P h W ζ noise hhm hcf n q
  have hc := measurable_coe_nnreal_real.comp (measurable_nodeScale x₀ h44 hκ hκ4 hb P h W ζ noise hhm hcf n q)
  refine measurable_const.prodMk (Measurable.prodMk ?_ ?_)
  · exact measurable_pi_iff.2 fun i => (hc.mul ((measurable_pi_apply i).comp hL)).comp measurable_fst
  · exact measurable_pi_iff.2 fun k => (hc.mul ((measurable_pi_apply k).comp hR)).comp measurable_fst

/-- **A reached node stage has an alive tree candidate**, and its start driver is outside the band of its depth. -/
theorem alive_of_mem_canonR (hhm : Measurable h)
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (n : ℕ) (q : ℚ) :
    ∀ (j : ℕ) (t : Fin j → ℝ≥0) (ω' : Ω × Ωa),
      ω' ∈ canonR (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q) ratGrid (nodeNL_pos x₀ hκ hb n)
        (nodeNR_pos x₀ hκ hb n) (nodeStart x₀ h44 hκ hκ4 hb P h W ζ noise n q)
        (nodeR0 x₀ h44 hκ hκ4 hb P h W ζ noise n q) j t →
      ω'.1 ∈ (nodeD x₀ h44 hκ hκ4 hb P h W ζ noise n q).alive (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t) ∧
      (canonY (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q)
        (nodeStart x₀ h44 hκ hκ4 hb P h W ζ noise n q) j t ω').1 ∉ band j
  | 0, t, ω', hR => by
    have ht : t = Fin.elim0 := funext fun i => i.elim0
    subst ht
    refine ⟨?_, ?_⟩
    · have e := append_elim0 (nodePre (scheduleAt n))
      rw [e]
      exact hR.1
    · show (0 : ℝ) ∉ band 0
      rw [band_even (⟨0, rfl⟩ : Even 0)]
      intro h0
      linarith [h0.2]
  | j + 1, t, ω', hR => by
    simp only [canonR, mem_inter_iff, mem_iUnion] at hR
    obtain ⟨hR', n', m', hgrid, hsw⟩ := hR
    obtain ⟨hA', hband'⟩ := alive_of_mem_canonR hhm hcf n q j (Fin.init t) ω' hR'
    have hreg := isRegStage_candStage (hnL := nodeNL_pos x₀ hκ hb n) (hnR := nodeNR_pos x₀ hκ hb n)
      (isRegFam_nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise hhm hcf n q)
      (measurable_nodeStart (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise hhm hcf n q) j (Fin.init t)
    obtain ⟨hsucc, hidx⟩ := hsw
    have hss := (swIdx_spec hreg hsucc).1
    rw [hidx, hgrid] at hss
    obtain ⟨hhit, hlt, hbandS, -⟩ := hss
    have hclk := clk_clkInv hhit
    set D := nodeD x₀ h44 hκ hκ4 hb P h W ζ noise n q with hD
    set C := nodeScale x₀ h44 hκ hκ4 hb P h W ζ noise n q with hC
    have hDr := isReg_nodeD x₀ h44 hκ hκ4 hb P h W ζ noise hhm hcf n q
    have hDt := isTree_nodeD x₀ h44 hκ hκ4 hb P h W ζ noise n q
    have hCpos : 0 < C ω'.1 := nodeScale_pos x₀ h44 hκ hκ4 hb P h W ζ noise n q ω'.1
    set s := clkInv (candStage (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q)
      (canonY (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q)
        (nodeStart x₀ h44 hκ hκ4 hb P h W ζ noise n q)) j (Fin.init t)) (t (Fin.last j)) ω' with hs
    set k₀ := nodeLen (scheduleAt n) + j with hk₀
    set tt₀ := Fin.append (nodePre (scheduleAt n)) (Fin.init t) with htt₀
    have hγ := (hDr.isKilledFamily k₀ tt₀).arc ω'.1
    -- the dilated lifetime
    have hlt' : ((s / C ω'.1 ^ 2 : ℝ≥0) : ℝ≥0∞) < (D.cand k₀ tt₀).ζ ω'.1 :=
      (coe_lt_scale_iff hCpos).1 hlt
    obtain ⟨-, hlife⟩ := lt_arcζ_iff.1 hlt'
    -- the switch is at a positive piece time
    have hspos : 0 < s := by
      rcases eq_zero_or_pos s with h0 | h0
      · exfalso
        have hb0 := hbandS
        change (canonY (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q)
            (nodeStart x₀ h44 hκ hκ4 hb P h W ζ noise n q) j (Fin.init t) ω').1 +
            (C ω'.1 : ℝ) * (D.cand k₀ tt₀).W (s / C ω'.1 ^ 2) ω'.1 ∈ band j at hb0
        rw [h0, zero_div] at hb0
        have hw0 : (D.cand k₀ tt₀).W 0 ω'.1 = 0 := arcW_zero' ω'.1
        rw [hw0, mul_zero, add_zero] at hb0
        exact hband' hb0
      · exact h0
    have hs'pos : 0 < s / C ω'.1 ^ 2 := div_pos hspos (pow_pos hCpos 2)
    -- the clock at the switch
    have hclk' : (D.cand k₀ tt₀).clk ω'.1 (s / C ω'.1 ^ 2) = t (Fin.last j) := hclk
    rw [TreeData.clk_cand, arcClk_of_mem hA'] at hclk'
    have hclk'' : absClock (D.img k₀ tt₀ ω'.1) (D.pre k₀ tt₀ ω'.1) (D.startCap k₀ tt₀ ω'.1 + s / C ω'.1 ^ 2) =
        t (Fin.last j) := hclk'
    rw [absClock_of_lt hlife] at hclk''
    obtain ⟨huP, hucap⟩ := hγ.kInv_spec hlife
    set u := WangWu.ImgWord.kInv (D.img k₀ tt₀ ω'.1) (D.pre k₀ tt₀ ω'.1) (D.startCap k₀ tt₀ ω'.1 + s / C ω'.1 ^ 2)
        with hu
    have hvp : IsValid k₀ tt₀ := hA'.1.1.1
    have hq0 : 0 ≤ qLast k₀ tt₀ := hDt.qnonneg k₀ tt₀ hA'.1.1
    -- the switch is after the last switch of the parent
    have hqu : qLast k₀ tt₀ < u := by
      by_contra hle
      push Not at hle
      have h1 := hγ.strictMonoOn_capClock.monotoneOn huP hA'.2 hle
      have h2 : (D.startCap k₀ tt₀ ω'.1 : ℝ) = capClock (D.img k₀ tt₀ ω'.1) (qLast k₀ tt₀) :=
        TreeData.startCap_coe hDr hA'
      rw [hucap, NNReal.coe_add, ← h2] at h1
      have : (0 : ℝ) < ((s / C ω'.1 ^ 2 : ℝ≥0) : ℝ) := NNReal.coe_pos.2 hs'pos
      linarith
    have hu0 : 0 ≤ u := hq0.trans hqu.le
    have hlast : (physTime u).toNNReal = t (Fin.last j) := hclk''
    -- the extended list is admissible
    have hinit := init_append (nodePre (scheduleAt n)) t
    have hlastA := append_last (nodePre (scheduleAt n)) t
    have hvalid : IsValid (k₀ + 1) (Fin.append (nodePre (scheduleAt n)) t : Fin (nodeLen (scheduleAt n) + (j + 1)) →
        ℝ≥0) := by
      refine isValid_of_init ?_ (fun i => ?_) ?_ ?_ ?_
      · rw [hinit]; exact hvp
      · rw [hinit, hlastA, ← hlast]
        have hi := (decode_le_qLast hvp i).trans_lt hqu
        have h1 : tt₀ i < 1 := (hvp.2 i).2.1
        have e : (physTime (decode (tt₀ i))).toNNReal = tt₀ i := by rw [physTime_decode h1, Real.toNNReal_coe]
        show tt₀ i < _
        rw [← e]
        exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg (physTime_nonneg (decode_nonneg h1))).2
          (physTime_lt_physTime (decode_nonneg h1) hi)
      · rw [hlastA, ← hlast]
        refine Real.toNNReal_pos.2 ?_
        unfold physTime
        exact div_pos (hq0.trans_lt hqu) (by linarith)
      · rw [hlastA, ← hlast]
        exact (Real.toNNReal_lt_iff_lt_coe (physTime_nonneg hu0)).2 (by simpa using physTime_lt_one hu0)
      · rw [hlastA, ← hgrid]
        exact ratGrid_isRat n' m'
    have hvc : D.valid (k₀ + 1) (Fin.append (nodePre (scheduleAt n)) t : Fin (nodeLen (scheduleAt n) + (j + 1)) →
        ℝ≥0) := nodeValid_append hvalid
    -- the extended list is alive
    have hqc : qLast (k₀ + 1) (Fin.append (nodePre (scheduleAt n)) t : Fin (nodeLen (scheduleAt n) + (j + 1)) → ℝ≥0)
        = u := by
      show decode ((Fin.append (nodePre (scheduleAt n)) t : Fin (nodeLen (scheduleAt n) + (j + 1)) → ℝ≥0) (Fin.last
          k₀)) = u
      rw [hlastA, ← hlast, decode_physTime hu0]
    have hpre : qLast (k₀ + 1) (Fin.append (nodePre (scheduleAt n)) t : Fin (nodeLen (scheduleAt n) + (j + 1)) → ℝ≥0) ∈
        D.pre (k₀ + 1) (Fin.append (nodePre (scheduleAt n)) t : Fin (nodeLen (scheduleAt n) + (j + 1)) → ℝ≥0) ω'.1 := by
      rw [hDt.mem_pre_iff hvc hA'.1.2 le_rfl, hinit, hqc]
      exact huP
    refine ⟨⟨⟨hvc, hA'.1.2⟩, hpre⟩, ?_⟩
    -- the start driver after the switch is in the band of depth `j`
    have hy : (canonY (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q)
        (nodeStart x₀ h44 hκ hκ4 hb P h W ζ noise n q) (j + 1) t ω').1 ∈ band j := hbandS
    exact band_disjoint j hy

end Reach

end InteractingSLE.Sec5.CrossCond.StagedNode
