/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CmStop
import InteractingSLE.Spec.Supplement.SB2MzOffM
import InteractingSLE.Spec.Supplement.SBTail2SideTips

/-!
# The entrance time read through countable codes (deterministic core)

Packet PROVE-SB2-CONDFIN (round 6; root route, step 1). Two countable readings, so that `{entrTime ≤ s}` and the seed
`R = max (A ∩ ℝ)` become measurable functions of countably many measurable coordinates:

* `closure_range_inter_nonempty_iff`: the closure of a code meets a compact set `K` iff the code comes within distance
  `0` of `K`;
* **`measurable_realMax_of_hit`**: the largest real point `realMax (X ω)` is measurable as soon as every event
  "`X ω` meets the compact `K`" is (no compactness of `X ω`: off the event "`X ω ∩ ℝ` is nonempty and bounded above"
  both sides read `0`);
* `measurableSet_hit_codes`: for `X ω = C ∪ ⋃_{j < k} closure (range (G ω j))` these events are measurable;
* **`limUnder_tipApprox_eq_pcPt`**: for a launched regular piece of the boundary walk, the tip approximations at own
  time `t ≤ ζ` converge to the piece's point `Lk.pcPt` at `t`;
* **`entrTime_le_iff_code`**: `entrTime ≤ s` iff `ζ ≤ s` or the seed is within distance `0` of the tip limits at the
  times `m / (N + 1) ≤ min s ζ`.

Deterministic (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Cn

open Exist Exist.Staged Exist.StagedLaw Lk GW1W LuM WalkLaw

/-! ### Codes meeting compact sets; the largest real point -/

/-- **The closure of a code meets a compact set iff the code comes within distance `0` of it.** -/
theorem closure_range_inter_nonempty_iff {ι : Type*} (f : ι → ℂ) {K : Set ℂ} (hK : IsCompact K) :
    (closure (range f) ∩ K).Nonempty ↔ ⨅ i, infEDist (f i) K = 0 := by
  constructor
  · rintro ⟨z, hz, hzK⟩
    refine le_antisymm ?_ zero_le
    rw [← (Mz.mem_closure_range_iff z f).1 hz]
    exact iInf_mono fun i => by rw [edist_comm]; exact infEDist_le_edist_of_mem hzK
  · intro h
    by_contra hne
    rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at hne
    obtain ⟨r, hr, hrK⟩ := exists_pos_forall_lt_edist hK isClosed_closure hne.symm
    have hle : (r : ℝ≥0∞) ≤ ⨅ i, infEDist (f i) K := le_iInf fun i => le_infEDist.2 fun y hy => by
      rw [edist_comm]
      exact (hrK y hy (f i) (subset_closure (mem_range_self i))).le
    rw [h] at hle
    exact absurd hle (not_le.2 (by exact_mod_cast hr))

/-- The real segment `[a, m]` in `ℂ`. -/
def seg (a m : ℝ) : Set ℂ := ((↑) : ℝ → ℂ) '' Icc a m

theorem isCompact_seg (a m : ℝ) : IsCompact (seg a m) :=
  isCompact_Icc.image Complex.continuous_ofReal

theorem inter_seg_nonempty_iff (X : Set ℂ) (a m : ℝ) :
    (X ∩ seg a m).Nonempty ↔ ∃ x : ℝ, x ∈ Icc a m ∧ (x : ℂ) ∈ X := by
  constructor
  · rintro ⟨_, hX, x, hx, rfl⟩
    exact ⟨x, hx, hX⟩
  · rintro ⟨x, hx, hX⟩
    exact ⟨x, hX, x, hx, rfl⟩

/-- **The largest real point is measurable** as soon as every event "`X ω` meets the compact `K`" is. -/
theorem measurable_realMax_of_hit {Ω : Type*} [MeasurableSpace Ω] {X : Ω → Set ℂ}
    (hhit : ∀ K : Set ℂ, IsCompact K → MeasurableSet {ω | (X ω ∩ K).Nonempty}) :
    Measurable fun ω => realMax (X ω) := by
  classical
  set Y : Ω → Set ℝ := fun ω => {x : ℝ | (x : ℂ) ∈ X ω} with hY
  have hreal : ∀ ω, realMax (X ω) = sSup (Y ω) := fun ω => rfl
  set Hit : ℝ → ℝ → Set Ω := fun a m => {ω | (X ω ∩ seg a m).Nonempty} with hHit
  have hHitm : ∀ a m, MeasurableSet (Hit a m) := fun a m => hhit _ (isCompact_seg a m)
  have hHit_iff : ∀ a m ω, ω ∈ Hit a m ↔ ∃ x ∈ Y ω, x ∈ Icc a m := fun a m ω => by
    rw [show ω ∈ Hit a m ↔ (X ω ∩ seg a m).Nonempty from Iff.rfl, inter_seg_nonempty_iff]
    exact ⟨fun ⟨x, hx, hX⟩ => ⟨x, hX, hx⟩, fun ⟨x, hX, hx⟩ => ⟨x, hx, hX⟩⟩
  -- the good event: nonempty and bounded above
  set Good : Set Ω := (⋃ m : ℕ, Hit (-(m : ℝ)) m) ∩ ⋃ n : ℕ, ⋂ m : ℕ, (Hit n m)ᶜ with hGood
  have hGoodm : MeasurableSet Good :=
    (MeasurableSet.iUnion fun m => hHitm _ _).inter
      (MeasurableSet.iUnion fun n => MeasurableSet.iInter fun m => (hHitm _ _).compl)
  have hGood_iff : ∀ ω, ω ∈ Good ↔ (Y ω).Nonempty ∧ BddAbove (Y ω) := by
    intro ω
    simp only [hGood, mem_inter_iff, mem_iUnion, mem_iInter, mem_compl_iff]
    refine and_congr ⟨fun ⟨m, hm⟩ => ?_, fun ⟨x, hx⟩ => ?_⟩ ⟨fun ⟨n, hn⟩ => ?_, fun ⟨B, hB⟩ => ?_⟩
    · obtain ⟨x, hx, -⟩ := (hHit_iff _ _ ω).1 hm
      exact ⟨x, hx⟩
    · obtain ⟨m, hm⟩ := exists_nat_ge |x|
      exact ⟨m, (hHit_iff _ _ ω).2 ⟨x, hx, (abs_le.1 hm).1, (abs_le.1 hm).2⟩⟩
    · refine ⟨n, fun x hx => ?_⟩
      by_contra hxn
      push Not at hxn
      obtain ⟨m, hm⟩ := exists_nat_ge x
      exact hn m ((hHit_iff _ _ ω).2 ⟨x, hx, hxn.le, hm⟩)
    · obtain ⟨n, hn⟩ := exists_nat_gt B
      refine ⟨n, fun m hm => ?_⟩
      obtain ⟨x, hx, hxI⟩ := (hHit_iff _ _ ω).1 hm
      exact absurd (hB hx) (not_le.2 (hn.trans_le hxI.1))
  refine measurable_of_Ioi fun q => ?_
  have e : (fun ω => realMax (X ω)) ⁻¹' Ioi q =
      (Good ∩ ⋃ q' : ℚ, ⋃ m : ℕ, ({_ω | q < (q' : ℝ)} ∩ Hit q' m)) ∪ (Goodᶜ ∩ {_ω | q < 0}) := by
    ext ω
    simp only [mem_preimage, mem_Ioi, mem_union, mem_inter_iff, mem_iUnion, mem_compl_iff, mem_ofPred_eq]
    rw [hreal]
    by_cases hg : ω ∈ Good
    · obtain ⟨hne, hbdd⟩ := (hGood_iff ω).1 hg
      simp only [hg, true_and, not_true_eq_false, false_and, or_false]
      rw [lt_csSup_iff hbdd hne]
      constructor
      · rintro ⟨y, hy, hqy⟩
        obtain ⟨q', hq1, hq2⟩ := exists_rat_btwn hqy
        obtain ⟨m, hm⟩ := exists_nat_ge y
        exact ⟨q', m, hq1, (hHit_iff _ _ ω).2 ⟨y, hy, hq2.le, hm⟩⟩
      · rintro ⟨q', m, hq, hm⟩
        obtain ⟨x, hx, hxI⟩ := (hHit_iff _ _ ω).1 hm
        exact ⟨x, hx, hq.trans_le hxI.1⟩
    · have h0 : sSup (Y ω) = 0 := by
        rcases not_and_or.1 (fun h => hg ((hGood_iff ω).2 h)) with h | h
        · rw [not_nonempty_iff_eq_empty.1 h, Real.sSup_empty]
        · exact Real.sSup_of_not_bddAbove h
      simp only [hg, false_and, false_or, not_false_eq_true, true_and, h0]
  rw [e]
  refine (hGoodm.inter (MeasurableSet.iUnion fun q' => MeasurableSet.iUnion fun m =>
    (MeasurableSet.const _).inter (hHitm _ _))).union (hGoodm.compl.inter (MeasurableSet.const _))

/-- **Hitting events of a fixed set together with finitely many code closures are measurable.** -/
theorem measurableSet_hit_codes {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {G : Ω → ℕ → ι → ℂ}
    (hG : ∀ j i, Measurable fun ω => G ω j i) (C : Set ℂ) (k : ℕ) {K : Set ℂ} (hK : IsCompact K) :
    MeasurableSet {ω | ((C ∪ ⋃ j ∈ Finset.range k, closure (range (G ω j))) ∩ K).Nonempty} := by
  classical
  have e : {ω | ((C ∪ ⋃ j ∈ Finset.range k, closure (range (G ω j))) ∩ K).Nonempty} =
      {_ω | (C ∩ K).Nonempty} ∪ ⋃ j ∈ Finset.range k, {ω | ⨅ i, infEDist (G ω j i) K = 0} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_iUnion, exists_prop, union_inter_distrib_right,
      union_nonempty, iUnion₂_inter, nonempty_iUnion]
    refine or_congr Iff.rfl (exists_congr fun j => and_congr Iff.rfl ?_)
    exact closure_range_inter_nonempty_iff _ hK
  rw [e]
  exact (MeasurableSet.const _).union (Finset.measurableSet_biUnion _ fun j _ =>
    (Measurable.iInf fun i => measurable_infEDist.comp (hG j i)) (measurableSet_singleton 0))

/-! ### The tip limits and the entrance time -/

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → Drv}

/-- **The tip approximations converge to the piece's point**: for a launched regular piece of the boundary walk and an
own time `t ≤ ζ`, the approximations `tipApprox … t n` converge to `pcPt t`. -/
theorem tendsto_tipApprox_pcPt {θ : ℝ} (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) ≤ (D n).2) :
    Tendsto (fun m => tipApprox κ b jumps (boundaryWalkSpec b jumps θ true) D n t m) atTop
      (𝓝 (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t)) := by
  have hPR := pieceRegular_of_launch hP hl
  have hα := isGeneratingTrace_trOf hPR
  have hcc := isConformal_runChart_of_reg (boundaryWalkSpec b jumps θ true) hP n
  have hcb := (GW1P.isClosed_pieces_run (boundaryWalkSpec b jumps θ true) D hP n).1
  obtain ⟨g, -, -, -, hgt⟩ := Lw.exists_bdryMap_of_hasProperBdryExt hcc hcb
  have hαH : 0 ≤ (trOf (D n) t).im := im_nonneg_of_isGeneratingTrace_le hα hPR.2.1 hPR.1 ht
  have hpc : pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t = g (trOf (D n) t) :=
    bdVal_eq_of_tendsto hαH (hgt _ hαH)
  rw [hpc]
  have hlim := CounterflowRange.tendsto_tip_stopped_of_tendsto hα hPR.2.1 hPR.1 ht (hgt _ hαH)
  have hy : Tendsto (fun m : ℕ => (1 / ((m : ℝ) + 1) : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun m => (by positivity : (0 : ℝ) < 1 / ((m : ℝ) + 1))⟩
  have htime : min (instrTime (boundaryWalkSpec b jumps θ true) n) (D n).2 = (D n).2 := by
    rw [GW1W.instrTime_walk hl, min_eq_right le_top]
  have e : (fun m => tipApprox κ b jumps (boundaryWalkSpec b jumps θ true) D n t m) =
      (fun y : ℝ => (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)).2.1
        (QuantumZipper.fwdMapInv (fun r : ℝ => (D n).1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (D n).2).toNNReal)
          (t : ℝ) (y * Complex.I))) ∘ fun m : ℕ => (1 / ((m : ℝ) + 1) : ℝ) := by
    funext m
    simp only [tipApprox, Function.comp, htime]
  rw [e]
  exact hlim.comp hy

/-- The limit of the tip approximations is the piece's point (`limUnder` form). -/
theorem limUnder_tipApprox_eq_pcPt {θ : ℝ} (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    {n : ℕ} (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ (D n).2) :
    limUnder atTop (fun m => tipApprox κ b jumps (boundaryWalkSpec b jumps θ true) D n t m) =
      pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t :=
  (tendsto_tipApprox_pcPt hP hl ht).limUnder_eq

open Classical in
/-- **The tip code at cap `s`**: the distance from `R` to the tip limits at the times `m / (N + 1) ≤ min s ζ` (other
indices contribute `⊤`). -/
def tipCode (V : ℕ × ℕ → ℂ) (ζ : ℝ≥0∞) (s : ℝ≥0) (R : ℝ) : ℝ≥0∞ :=
  ⨅ p : ℕ × ℕ, if (qTime p.1 p.2 : ℝ≥0∞) ≤ min (s : ℝ≥0∞) ζ then edist (R : ℂ) (V p) else ⊤

/-- **The entrance time through the tip code**: for a launched regular piece of the boundary walk, `entrTime ≤ s` iff
`ζ ≤ s` or `R` is within distance `0` of the tip limits at the rational times `≤ min s ζ`. -/
theorem entrTime_le_iff_code {θ : ℝ} (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none) (R : ℝ)
    (s : ℝ≥0) :
    Ck.entrTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R ≤ s ↔
      (D n).2 ≤ s ∨ tipCode (fun p => limUnder atTop
        (fun m => tipApprox κ b jumps (boundaryWalkSpec b jumps θ true) D n (qTime p.1 p.2) m)) (D n).2 s R = 0 := by
  classical
  set st := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n with hst
  rw [Ck.entrTime_le_iff hP hl R s]
  by_cases hζ : (D n).2 ≤ s
  · exact iff_of_true (Or.inr hζ) (Or.inl hζ)
  push Not at hζ
  have hmin : min (s : ℝ≥0∞) (D n).2 = s := min_eq_left hζ.le
  simp only [hζ.not_ge, or_false, false_or]
  have hV : ∀ p : ℕ × ℕ, (qTime p.1 p.2 : ℝ≥0∞) ≤ min (s : ℝ≥0∞) (D n).2 →
      limUnder atTop (fun m => tipApprox κ b jumps (boundaryWalkSpec b jumps θ true) D n (qTime p.1 p.2) m) =
        pcPt st (D n) (qTime p.1 p.2) := fun p hp =>
    limUnder_tipApprox_eq_pcPt hP hl (hp.trans (min_le_right _ _))
  have hc := continuousOn_pcPt_launch hP hl
  have hsub : Icc (0 : ℝ≥0) s ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2} := fun t ht =>
    (ENNReal.coe_le_coe.2 ht.2).trans hζ.le
  unfold tipCode
  rw [hmin]
  constructor
  · rintro ⟨t, ht, htR⟩
    have hts : t ≤ s := ENNReal.coe_le_coe.1 ht
    obtain ⟨m, hm, hmt⟩ := exists_qTime_tendsto t
    have hcont : Tendsto (fun N => pcPt st (D n) (qTime (m N) N)) atTop (𝓝 (pcPt st (D n) t)) :=
      ((hc.mono hsub) t ⟨zero_le, hts⟩).tendsto.comp (tendsto_nhdsWithin_iff.2
        ⟨hmt, Eventually.of_forall fun N => ⟨zero_le, (hm N).trans hts⟩⟩)
    have hed : Tendsto (fun N => edist (R : ℂ) (pcPt st (D n) (qTime (m N) N))) atTop (𝓝 0) := by
      rw [show pcPt st (D n) t = (R : ℂ) from htR] at hcont
      have := (tendsto_iff_edist_tendsto_0.1 hcont)
      exact this.congr fun N => edist_comm _ _
    refine le_antisymm (ge_of_tendsto hed (Eventually.of_forall fun N => ?_)) zero_le
    have hq : (qTime (m N) N : ℝ≥0∞) ≤ s := ENNReal.coe_le_coe.2 ((hm N).trans hts)
    refine (iInf_le _ (m N, N)).trans ?_
    simp only [hq, ↓reduceIte]
    rw [hV (m N, N) (by rw [hmin]; exact hq)]
  · intro h0
    set K : Set ℂ := pcPt st (D n) '' Icc (0 : ℝ≥0) s with hK
    have hKc : IsCompact K := isCompact_Icc.image_of_continuousOn (hc.mono hsub)
    have hle : infEDist (R : ℂ) K ≤ ⨅ p : ℕ × ℕ, if (qTime p.1 p.2 : ℝ≥0∞) ≤ (s : ℝ≥0∞) then
        edist (R : ℂ) (limUnder atTop
          (fun m => tipApprox κ b jumps (boundaryWalkSpec b jumps θ true) D n (qTime p.1 p.2) m)) else ⊤ := by
      refine le_iInf fun p => ?_
      split_ifs with hp
      · rw [hV p (by rw [hmin]; exact hp)]
        exact infEDist_le_edist_of_mem ⟨qTime p.1 p.2, ⟨zero_le, ENNReal.coe_le_coe.1 hp⟩, rfl⟩
      · exact le_top
    rw [h0, nonpos_iff_eq_zero, ← mem_closure_iff_infEDist_zero, hKc.isClosed.closure_eq] at hle
    obtain ⟨t, ht, htR⟩ := hle
    exact ⟨t, ENNReal.coe_le_coe.2 ht.2, htR⟩

end InteractingSLE.Theorem14.SB.Cn
