/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmQGate

/-!
# The retained gate is J32's gate, almost surely

Packet PROVE-GW2-GEOM2 (round 5). **`ae_mem_nextGate_iff`**: almost surely, for every time-ordered history `l`,
candidate `a` and `q ≤ q'`, the retained gate `nextGate c r l a q q'` is J32's observation gate `S < q < F`.

The proof reads each conjunct of the gate on the next history:
* the candidate piece's record life past `q − T` (`life_iff_nextLast`: the same canonical piece, cut at `cap` and at
  `q' − T`);
* the separation buffer past `q − T` (the separation gauges of the two pairs agree on `[0, q − T]`: the joined drivers
  agree on `[0, q]`, so do their traces, `lt_localStop_congr`);
* the first passage before `capInc(q − T)` (`switchedEntry_lt_iff`, and the stage drivers of the two pairs agree at
  levels reached by `q`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip RootC24 RootJ32 Sec5.Prop513TreeExtract
  Sec5.Prop513Schedule

/-- The life comparison of a piece cut at `C` read from the same piece cut at `Q' ≥ d`. -/
theorem lt_life_iff {d C Q' ζ : ℝ≥0∞} (hdQ : d ≤ Q') :
    d < min C ζ ↔ d < C ∧ (decide (ζ ≤ Q') = false ∨ d < min Q' ζ) := by
  rw [lt_min_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · intro hζ
    by_cases hζQ : ζ ≤ Q'
    · right; rw [min_eq_right hζQ]; exact hζ
    · left; simp [hζQ]
  · rintro (h | h)
    · have hζQ : ¬ ζ ≤ Q' := by simpa using h
      exact hdQ.trans_lt (not_le.1 hζQ)
    · exact h.trans_le (min_le_right _ _)

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

omit [StandardBorelSpace Ω] in
/-- **The candidate piece's life, read from the next history's last record**: for `τ ≤ q' − T`, the piece survives
past `τ` before its cap exactly when `τ < cap` and the next history's record of the same piece (cut at `q' − T`) is
either alive at its cut or died after `τ`. -/
theorem life_iff_nextLast (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a : ℕ) (q' : c.Q) (ω : Ω) {τ : ℝ≥0}
    (hτ : τ ≤ (q' : ℝ≥0) - RootJ31.historyTime c r l) :
    τ < (RootJ31.nextRecord c r l a ω).2.1.toNNReal ↔
      τ < RootJ31.candidateCap c r a ∧ ((nextLast c r l a q' ω).2.2 = false ∨
        (τ : ℝ≥0∞) < (nextLast c r l a q' ω).2.1) := by
  set x := rootPt r.1
  set θ : ℝ := (RootJ31.candidateAngle c r a : ℝ)
  set T := RootJ31.historyTime c r l with hT
  set Lh := RootJ31.historyProgram c r l with hLh
  set m := Lh.length with hm
  set Lf := RootJ31.futureProgram c r l a with hLf
  set L' := Lh ++ [(θ, (q' : ℝ≥0))] with hL'
  have hDm : canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x Lf) m ω =
      canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x L') m ω :=
    RootH29.canonical_next_independent_time c.hκ c.h12p c.βA c.c₀ c.h x θ Lh
      (T + RootJ31.candidateCap c r a) q' ω
  have hΔfm : specDelta (schedSpec x Lf) m = (RootJ31.candidateCap c r a : ℝ≥0∞) :=
    RootJ31.futureProgram_delta c r l a
  have hΔ'm : specDelta (schedSpec x L') m = (((q' : ℝ≥0) - T : ℝ≥0) : ℝ≥0∞) :=
    RootH29.specDelta_last x θ Lh q'
  have h1 : (RootJ31.nextRecord c r l a ω).2.1 = min (specDelta (schedSpec x Lf) m)
      (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x Lf) m ω).2 := rfl
  have hnl : nextLast c r l a q' ω = stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x L') m ω := by
    unfold nextLast
    rw [RootJ31.historyProgram_cons]
  have h2 : (nextLast c r l a q' ω).2.1 = min (specDelta (schedSpec x L') m)
      (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x L') m ω).2 := by
    rw [hnl]; rfl
  have h3 : (nextLast c r l a q' ω).2.2 = decide
      ((canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x L') m ω).2 ≤
        specDelta (schedSpec x L') m) := by
    rw [hnl]; rfl
  have hfin : min (specDelta (schedSpec x Lf) m)
      (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x Lf) m ω).2 ≠ ⊤ := by
    rw [hΔfm]; exact ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  rw [h2, h3, h1, ← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hfin, hΔfm, hDm, hΔ'm,
    lt_life_iff (ENNReal.coe_le_coe.2 hτ), ENNReal.coe_lt_coe]

/-- **The retained gate is J32's observation gate**, almost surely: for every time-ordered history `l`, candidate
`a` and `q ≤ q'`, `nextGate c r l a q q'` is the event `S < q < F`. -/
theorem ae_mem_nextGate_iff (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q q' : c.Q),
      TimeOrdered 0 (RootJ31.historyProgram c r l) → q ≤ q' →
      (ω ∈ nextGate c r l a q q' ↔
        ((RootJ32.experiment c r).data.S l a ω < (q : ℝ≥0) ∧
          ((q : ℝ≥0) : ℝ) < (RootJ32.experiment c r).data.F l a ω)) := by
  filter_upwards [ae_clock_of_buffer_pos h13 c r, ae_futureJoined_eq_nextJoined' h13 c r,
    ae_futureJoined_trace h13 c r, ae_nextJoined_trace h13 c r]
    with ω hclock hnext hjoin hntr l a q q' hord hqq'
  classical
  have hS : (RootJ32.experiment c r).data.S l a ω = ((RootJ31.historyTime c r l +
      RootJ32.switchedEntry (2 ^ r.2) ((-1) ^ l.length) (rootPt r.1) c.s
        (RootJ31.historyTime c r l + RootJ31.candidateCap c r a) (rootEntry r.1).2
        (RootJ31.historyTime c r l) (RootJ31.sourceBuffer c r l a ω)
        (RootJ31.futurePair c r l a ω) : ℝ≥0) : ℝ) := rfl
  have hF : (RootJ32.experiment c r).data.F l a ω =
      ((RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ω : ℝ≥0) : ℝ) := rfl
  rw [hS, hF]
  unfold nextGate
  by_cases hTq : RootJ31.historyTime c r l < (q : ℝ≥0)
  swap
  · rw [ite_eq_right hTq]
    simp only [mem_empty_iff_false, false_iff, not_and]
    intro hSq
    exact absurd (le_self_add.trans_lt (NNReal.coe_lt_coe.1 hSq)) hTq
  rw [ite_eq_left hTq]
  set T := RootJ31.historyTime c r l with hT
  set cap := RootJ31.candidateCap c r a with hcap
  set Fb := RootJ31.sourceBuffer c r l a ω with hFb
  set k : ℝ≥0 := 2 ^ r.2 with hk
  set τ := (q : ℝ≥0) - T with hτ
  have hk0 : 0 < k := pow_pos (by norm_num) _
  have hv₀T : (rootEntry r.1).2 ≤ T := rootTime_le_historyTime c r l hord
  have hqq'' : (q : ℝ≥0) ≤ (q' : ℝ≥0) := hqq'
  have hTτ : T + τ = (q : ℝ≥0) := add_tsub_cancel_of_le hTq.le
  have hτq' : τ ≤ (q' : ℝ≥0) - T := tsub_le_tsub_right hqq'' T
  have hqF_iff : ((q : ℝ≥0) : ℝ) < ((T + Fb : ℝ≥0) : ℝ) ↔ τ < Fb := by
    rw [NNReal.coe_lt_coe, ← hTτ, add_lt_add_iff_left]
  have hSq_iff : ∀ se : ℝ≥0, ((T + se : ℝ≥0) : ℝ) < ((q : ℝ≥0) : ℝ) ↔ se < τ := by
    intro se
    rw [NNReal.coe_lt_coe, ← hTτ, add_lt_add_iff_left]
  have hτFb_iff : τ < Fb ↔ (ω ∈ RootCv.coverEvent c r ∧ RootJ31.oldSuccess c r l ω) ∧
      τ < (RootJ31.nextRecord c r l a ω).2.1.toNNReal ∧
      τ < RootJ31.switchedBuffer (rootPt r.1) c.s (T + cap) T cap (RootJ31.candidateBuffer a)
        (RootJ31.futurePair c r l a ω) := by
    have hFbdef : Fb = if ω ∈ RootCv.coverEvent c r ∧ RootJ31.oldSuccess c r l ω then
        min (RootJ31.nextRecord c r l a ω).2.1.toNNReal
          (RootJ31.switchedBuffer (rootPt r.1) c.s (T + cap) T cap (RootJ31.candidateBuffer a)
            (RootJ31.futurePair c r l a ω)) else 0 := rfl
    rw [hFbdef]
    split_ifs with hco
    · simp only [hco, true_and, lt_min_iff]
    · simp only [hco, false_and, iff_false, not_lt, zero_le]
  -- the two joined drivers
  have hpe := futurePair_eq_recOfDriver c r l a ω
  set J' := RootJ31.joinedRead
    (RootJ31.historyProgram c r ((RootJ31.candidateAngle c r a, q') :: l))
    (RootJ31.programRecords c (rootPt r.1)
      (RootJ31.historyProgram c r ((RootJ31.candidateAngle c r a, q') :: l)) ω) with hJ'def
  have hnp : nextPair c r l a q' ω =
      (cfRec c.s c.W c.ζ ω, StagedEntrance.Strip.recOfDriver (q' : ℝ≥0) J') := by
    show (cfRec c.s c.W c.ζ ω, StagedEntrance.Strip.recOfDriver (Sec5.Prop513Schedule.lastTime 0
      (RootJ31.historyProgram c r ((RootJ31.candidateAngle c r a, q') :: l))) J') = _
    rw [lastTime_next]
  obtain ⟨hJ, hJ0⟩ := continuous_futureJoined c r l a ω
  obtain ⟨hJ', hJ'0⟩ := RootJ31.continuous_joinedRead
    (RootJ31.historyProgram c r ((RootJ31.candidateAngle c r a, q') :: l))
    (RootJ31.programRecords c (rootPt r.1)
      (RootJ31.historyProgram c r ((RootJ31.candidateAngle c r a, q') :: l)) ω)
  have hqL : ∀ _ : τ < cap, (q : ℝ≥0) ≤ T + cap := fun hτc => by
    rw [← hTτ]; exact (add_le_add_iff_left T).2 hτc.le
  have hagree : RootJ31.oldSuccess c r l ω → τ < cap →
      ∀ y ≤ (q : ℝ≥0), futureJoined c r l a ω y = J' y := by
    intro hold hτc y hy
    refine hnext l a q' hold y (hy.trans ?_)
    rw [← hTτ]
    exact (add_le_add_iff_left T).2 (le_min hτc.le hτq')
  -- the separation buffer
  have hsw : RootJ31.oldSuccess c r l ω → τ < cap →
      (τ < RootJ31.switchedBuffer (rootPt r.1) c.s (T + cap) T cap (RootJ31.candidateBuffer a)
          (RootJ31.futurePair c r l a ω) ↔
        τ < RootJ31.switchedBuffer (rootPt r.1) c.s q' T cap (RootJ31.candidateBuffer a)
          (nextPair c r l a q' ω)) := by
    intro hold hτc
    have hJJ := hagree hold hτc
    obtain ⟨-, γJ, hγJ⟩ := hjoin l a hold
    obtain ⟨γ', hγ'⟩ := hntr l a q' hold
    unfold RootJ31.switchedBuffer
    rw [lt_min_iff, lt_min_iff]
    refine and_congr_right fun _ => ?_
    refine lt_localStop_congr
      ((RootJ31.continuous_separationRead _ _ _ _).comp (continuous_const.add continuous_id))
      ((RootJ31.continuous_separationRead _ _ _ _).comp (continuous_const.add continuous_id))
      (fun u hu => ?_) _
    show RootJ31.separationRead (rootPt r.1) c.s (T + cap) (T + u) (RootJ31.futurePair c r l a ω) =
      RootJ31.separationRead (rootPt r.1) c.s q' (T + u) (nextPair c r l a q' ω)
    rw [hpe, hnp]
    refine separationRead_congr rfl fun τ' hτ' => ?_
    rw [frozenTraceRead_recOfDriver hJ hJ0 hγJ, frozenTraceRead_recOfDriver hJ' hJ'0 hγ']
    have hτ'q : τ' ≤ (q : ℝ≥0) := hτ'.trans (by rw [← hTτ]; exact (add_le_add_iff_left T).2 hu)
    show γJ (min τ' (T + cap)) = γ' (min τ' (q' : ℝ≥0))
    rw [min_eq_left (hτ'q.trans (hqL hτc)), min_eq_left (hτ'q.trans hqq''),
      ← LP.traceAt_eq_of_isGeneratingTrace hγJ hJ.continuousOn hJ0 ENNReal.coe_lt_top,
      ← LP.traceAt_eq_of_isGeneratingTrace hγ' hJ'.continuousOn hJ'0 ENNReal.coe_lt_top]
    exact LP.traceAt_congr fun y hy => hJJ y (hy.trans hτ'q)
  -- the first passage
  have hent : τ < Fb →
      (RootJ32.switchedEntry k ((-1) ^ l.length) (rootPt r.1) c.s (T + cap) (rootEntry r.1).2 T Fb
          (RootJ31.futurePair c r l a ω) < τ ↔
        ∃ u : ℚ≥0, ((u : ℝ≥0)) < RootJ31.capacityIncrement k (rootPt r.1) c.s T τ
            (nextPair c r l a q' ω) ∧
          2 < stageDriverRead k ((-1) ^ l.length) (rootPt r.1) c.s q' (rootEntry r.1).2 T u
            (nextPair c r l a q' ω)) := by
    intro hτFb
    have hpos : 0 < Fb := lt_of_le_of_lt zero_le hτFb
    obtain ⟨-, -, -, hm, hc⟩ := hclock l a hpos
    obtain ⟨-, hold, -, -⟩ := (RootK32.sourceBuffer_pos_iff c r l a ω).1 hpos
    rw [switchedEntry_lt_iff hk0 _ _ _ _ _ hm hc hτFb]
    have hτc : τ < cap := hτFb.trans_le (RootJ31.sourceBuffer_le c r l a ω)
    have hJJ := hagree hold hτc
    rw [hpe] at hm hc
    have hqTF : (q : ℝ≥0) ≤ T + Fb := by rw [← hTτ]; exact (add_le_add_iff_left T).2 hτFb.le
    have hm' := (hm.mono (Icc_subset_Icc le_rfl hqTF)).monotoneOn
    have hc' := hc.mono (Icc_subset_Icc le_rfl hqTF)
    have hdrv := rdrv_recOfDriver_congr hJ hJ0 hJ' hJ'0 (hqL hτc) hqq'' hJJ
    rw [hpe, hnp]
    have hinc : RootJ31.capacityIncrement k (rootPt r.1) c.s T τ
        (cfRec c.s c.W c.ζ ω, StagedEntrance.Strip.recOfDriver (T + cap) (futureJoined c r l a ω)) =
        RootJ31.capacityIncrement k (rootPt r.1) c.s T τ
          (cfRec c.s c.W c.ζ ω, StagedEntrance.Strip.recOfDriver (q' : ℝ≥0) J') := by
      unfold RootJ31.capacityIncrement
      rw [forwardCapacity_congr_le hdrv (le_of_eq hTτ), forwardCapacity_congr_le hdrv hTq.le]
    rw [← hinc]
    have hA0 : ∀ t, 0 ≤ RootH29.forwardCapacity (rootPt r.1) c.s t
        (cfRec c.s c.W c.ζ ω, StagedEntrance.Strip.recOfDriver (T + cap) (futureJoined c r l a ω)) :=
      fun t => forwardCapacity_nonneg _ _ _ _
    have hTmem : T ∈ Icc 0 (q : ℝ≥0) := ⟨zero_le, hTq.le⟩
    have hqmem : (q : ℝ≥0) ∈ Icc 0 (q : ℝ≥0) := ⟨zero_le, le_rfl⟩
    have hlevq := level_capacityIncrement (x := rootPt r.1) (s := c.s) hk0 hTq.le (hA0 T)
      (hm' hTmem hqmem hTq.le)
    refine exists_congr fun u => and_congr_right fun hu => ?_
    have hlev : ((((RootH29.forwardCapacity (rootPt r.1) c.s T
        (cfRec c.s c.W c.ζ ω, StagedEntrance.Strip.recOfDriver (T + cap)
          (futureJoined c r l a ω))).toNNReal + (u : ℝ≥0) / k ^ 2 : ℝ≥0)) : ℝ) ≤
        RootH29.forwardCapacity (rootPt r.1) c.s (q : ℝ≥0)
          (cfRec c.s c.W c.ζ ω, StagedEntrance.Strip.recOfDriver (T + cap)
            (futureJoined c r l a ω)) := by
      rw [← hlevq]
      exact NNReal.coe_le_coe.2 ((add_le_add_iff_left _).2
        (div_le_div_of_nonneg_right hu.le zero_le))
    rw [stageDriverRead_congr_le hdrv (by rw [recOfDriver_life]; exact ENNReal.coe_le_coe.2 (hqL hτc))
      (by rw [recOfDriver_life]; exact ENNReal.coe_le_coe.2 hqq'')
      (by rw [recOfDriver_life]; exact ENNReal.coe_pos.2 (lt_of_le_of_lt zero_le hTq |>.trans_le
        (hqL hτc)))
      (by rw [recOfDriver_life]; exact ENNReal.coe_pos.2 (lt_of_le_of_lt zero_le hTq |>.trans_le hqq''))
      (hqL hτc) hqq'' k ((-1) ^ l.length) (hv₀T.trans hTq.le) hTq.le
      (level_le_runMax_of_clock hm' hc' le_rfl hlev)
      (level_le_runMax_of_clock hm' hc' (hv₀T.trans hTq.le) (Real.coe_toNNReal _ (hA0 _)).le)]
  constructor
  · rintro ⟨⟨⟨⟨hcov, hold⟩, hτc, hlast⟩, hsep'⟩, hent'⟩
    have hlife := (life_iff_nextLast c r l a q' ω hτq').2 ⟨hτc, hlast⟩
    have hswf := (hsw hold hτc).2 hsep'
    have hτFb : τ < Fb := hτFb_iff.2 ⟨⟨hcov, hold⟩, hlife, hswf⟩
    exact ⟨(hSq_iff _).2 ((hent hτFb).2 hent'), hqF_iff.2 hτFb⟩
  · rintro ⟨hSq, hqF⟩
    have hτFb := hqF_iff.1 hqF
    obtain ⟨⟨hcov, hold⟩, hlife, hswf⟩ := hτFb_iff.1 hτFb
    obtain ⟨hτc, hlast⟩ := (life_iff_nextLast c r l a q' ω hτq').1 hlife
    exact ⟨⟨⟨⟨hcov, hold⟩, hτc, hlast⟩, (hsw hold hτc).1 hswf⟩, (hent hτFb).1 ((hSq_iff _).1 hSq)⟩

end InteractingSLE.Theorem14.GW2TipSystem.Gm
