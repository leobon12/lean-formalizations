/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NvTools

/-!
# SB2(2)'s v6 measurability: the actual walk's bookkeeping

Packet PROVE-GW2-GEOM2, round 10 (D28, item (A)). For a measurable driver family `Ê` that is regular at every sample
and has regular launches at every sample (the actual walk read through a regularized family), the quantities of the
v4/v6 rule that only depend on the actual run are measurable:

* `isClosed_pcPt_image`, `mem_pcPt_image_iff` (deterministic): the points of a launched piece form a closed set, and a
  point lies on it iff rational readings of the piece come arbitrarily close;
* `pcPt_zero_eq_pfam`, `pcPt_rat_eq_pfam`: those readings are values of `LuM.pfam`;
* `measurableSet_mem_newPiece`, **`measurableSet_mem_physSet`**: membership of a fixed point in a launched piece and in
  the physical set after `n` instructions;
* **`measurableSet_entryStage_eq`**, `measurableSet_arcEntry`, **`measurableSet_markEntry`**,
  **`measurableSet_zeroRoot`**, **`measurableSet_relOff_eq`**: the offset bookkeeping;
* **`measurableSet_launch_relOff`**, **`measurable_life_relOff`**: the launch and the lifetime at instruction
  `j + relOff`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Nv

open Lk Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal LuM GW1W GW1Bookkeep

/-! ### The points of a launched piece (deterministic) -/

section Det

variable {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {D : ℕ → Drv}

/-- **The points of a launched piece form a closed set** (the piece's tip set, `GW1P.isClosed_pieces_run`). -/
theorem isClosed_pcPt_image (hP : RegLaunches κ b J (boundaryWalkSpec b J θ true) D) {n : ℕ}
    (hl : (wRun κ θ b J D (n + 1)).2.2.2.1 n ≠ none) :
    IsClosed (pcPt (wRun κ θ b J D n) (D n) '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2}) := by
  obtain ⟨g, -, -, -, htip⟩ := tipSet_newPc_launch hP hl
  rw [← htip]
  refine (GW1P.isClosed_pieces_run (κ := κ) (b := b) (jumps := J) (boundaryWalkSpec b J θ true) D hP (n + 1)).2
    _ ?_
  rw [pieces_run_succ_of_launch hl]
  exact List.mem_append_right _ (List.mem_singleton.2 rfl)

/-- **A point lies on a launched piece iff rational readings come arbitrarily close.** -/
theorem mem_pcPt_image_iff (hP : RegLaunches κ b J (boundaryWalkSpec b J θ true) D) {n : ℕ}
    (hl : (wRun κ θ b J D (n + 1)).2.2.2.1 n ≠ none) (z : ℂ) :
    z ∈ pcPt (wRun κ θ b J D n) (D n) '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2} ↔
      ∀ k : ℕ, dist (pcPt (wRun κ θ b J D n) (D n) 0) z < 1 / ((k : ℝ) + 1) ∨
        ∃ q : ℚ, 0 < q ∧ (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < (D n).2 ∧
          dist (pcPt (wRun κ θ b J D n) (D n) (q : ℝ).toNNReal) z < 1 / ((k : ℝ) + 1) := by
  have hc := continuousOn_pcPt_launch hP hl
  constructor
  · rintro ⟨t, ht, rfl⟩ k
    by_cases ht0 : t = 0
    · left
      rw [ht0, dist_self]
      positivity
    · right
      have htpos : (0 : ℝ) < t := NNReal.coe_pos.2 (pos_iff_ne_zero.2 ht0)
      have hcw := hc t ht
      rw [Metric.continuousWithinAt_iff] at hcw
      obtain ⟨δ, hδ, hδc⟩ := hcw (1 / ((k : ℝ) + 1)) (by positivity)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max 0 ((t : ℝ) - δ) < t from max_lt htpos (by linarith))
      have hq0 : (0 : ℝ) < q := lt_of_le_of_lt (le_max_left _ _) hq1
      have hqt : ((q : ℝ).toNNReal : ℝ≥0) < t := by
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0.le]; exact hq2
      refine ⟨q, by exact_mod_cast hq0, lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hqt) ht, ?_⟩
      have hmem : ((q : ℝ).toNNReal) ∈ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2} :=
        le_trans (ENNReal.coe_le_coe.2 hqt.le) ht
      have hd : dist ((q : ℝ).toNNReal) t < δ := by
        rw [NNReal.dist_eq, Real.coe_toNNReal _ hq0.le, abs_lt]
        constructor <;> linarith [le_max_right 0 ((t : ℝ) - δ)]
      exact hδc hmem hd
  · intro h
    refine (isClosed_pcPt_image hP hl).closure_subset (Metric.mem_closure_iff.2 fun ε hε => ?_)
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    rcases h k with h0 | ⟨q, -, hqL, hq⟩
    · exact ⟨_, ⟨0, by simp, rfl⟩, by rw [dist_comm]; linarith⟩
    · exact ⟨_, ⟨_, hqL.le, rfl⟩, by rw [dist_comm]; linarith⟩

/-- The reading at time `0` is a value of `pfam`. -/
theorem pcPt_zero_eq_pfam (hP : RegLaunches κ b J (boundaryWalkSpec b J θ true) D) {n : ℕ}
    (hl : (wRun κ θ b J D (n + 1)).2.2.2.1 n ≠ none) :
    pcPt (wRun κ θ b J D n) (D n) 0 = pfam κ b J θ true D (n + 1) (Sum.inl (Sum.inl n)) := by
  classical
  have hα := isGeneratingTrace_trOf (pieceRegular_of_launch hP hl)
  simp only [pfam]
  split_ifs with hc
  · unfold pcPt
    rw [hα.1]
  · exact absurd ⟨Nat.lt_succ_self n, hl⟩ hc

/-- The reading at a rational time before the lifetime is a value of `pfam`. -/
theorem pcPt_rat_eq_pfam (hP : RegLaunches κ b J (boundaryWalkSpec b J θ true) D)
    (hreg : ∀ j, IsRegularDriver (D j)) {n : ℕ} (hl : (wRun κ θ b J D (n + 1)).2.2.2.1 n ≠ none) {q : ℚ}
    (hq0 : 0 < q) (hqL : (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < (D n).2) :
    pcPt (wRun κ θ b J D n) (D n) (q : ℝ).toNNReal = pfam κ b J θ true D (n + 1) (Sum.inl (Sum.inr (n, q))) := by
  classical
  have hPR := pieceRegular_of_launch hP hl
  simp only [pfam]
  split_ifs with hc
  · unfold pcPt
    rw [traceAt_eq_trOf (hreg n) hPR hqL]
  · exact absurd ⟨Nat.lt_succ_self n, hl, hq0, hqL⟩ hc

end Det

/-! ### Measurability of the bookkeeping -/

section Meas

variable {Ω : Type*} [MeasurableSpace Ω] {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
  (hb : IsPiecewiseConstantBoundaryData b J) {Ê : ℕ → Ω → Drv} (hÊm : ∀ j, Measurable (Ê j))
  (hÊreg : ∀ j ω, IsRegularDriver (Ê j ω))
  (hÊP : ∀ ω, RegLaunches κ b J (boundaryWalkSpec b J θ true) fun j => Ê j ω)

include hb hÊm hÊreg in
/-- The launch events. -/
theorem measurableSet_launch (n : ℕ) :
    MeasurableSet {ω | (wRun κ θ b J (fun j => Ê j ω) (n + 1)).2.2.2.1 n ≠ none} :=
  (runMeasStatement κ b J hb _ Ê hÊm hÊreg n).1

include hb hÊm hÊreg hÊP in
/-- **Membership of a fixed point in a launched piece.** -/
theorem measurableSet_mem_newPiece (z : ℂ) (n : ℕ) :
    MeasurableSet {ω | z ∈ newPiece κ b J θ true (fun j => Ê j ω) n} := by
  have hpf := fun i => measurable_pfam (κ := κ) (θ := θ) (right := true) hb hÊm hÊreg hÊP (n + 1) i
  have e : {ω | z ∈ newPiece κ b J θ true (fun j => Ê j ω) n} =
      {ω | (wRun κ θ b J (fun j => Ê j ω) (n + 1)).2.2.2.1 n ≠ none} ∩ ⋂ k : ℕ,
        ({ω | dist (pfam κ b J θ true (fun j => Ê j ω) (n + 1) (Sum.inl (Sum.inl n))) z < 1 / ((k : ℝ) + 1)} ∪
          ⋃ q : ℚ, {ω | 0 < q ∧ (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < (Ê n ω).2 ∧
            dist (pfam κ b J θ true (fun j => Ê j ω) (n + 1) (Sum.inl (Sum.inr (n, q)))) z <
              1 / ((k : ℝ) + 1)}) := by
    ext ω
    simp only [mem_inter_iff, mem_iInter, mem_union, mem_iUnion, mem_ofPred_eq]
    constructor
    · rintro ⟨hl, hz⟩
      refine ⟨hl, fun k => ?_⟩
      rcases (mem_pcPt_image_iff (hÊP ω) hl z).1 hz k with h | ⟨q, hq0, hqL, h⟩
      · left; rwa [pcPt_zero_eq_pfam (hÊP ω) hl] at h
      · right; exact ⟨q, hq0, hqL, by rwa [pcPt_rat_eq_pfam (hÊP ω) (fun j => hÊreg j ω) hl hq0 hqL] at h⟩
    · rintro ⟨hl, hk⟩
      refine ⟨hl, (mem_pcPt_image_iff (hÊP ω) hl z).2 fun k => ?_⟩
      rcases hk k with h | ⟨q, hq0, hqL, h⟩
      · left; rwa [pcPt_zero_eq_pfam (hÊP ω) hl]
      · right; exact ⟨q, hq0, hqL, by rwa [pcPt_rat_eq_pfam (hÊP ω) (fun j => hÊreg j ω) hl hq0 hqL]⟩
  rw [e]
  refine (measurableSet_launch hb hÊm hÊreg n).inter (MeasurableSet.iInter fun k =>
    (measurableSet_lt ((hpf _).dist measurable_const) measurable_const).union
      (MeasurableSet.iUnion fun q => ?_))
  exact (MeasurableSet.const _).inter ((measurableSet_lt measurable_const (measurable_snd.comp (hÊm n))).inter
    (measurableSet_lt ((hpf _).dist measurable_const) measurable_const))

include hb hÊm hÊreg in
/-- Membership of a fixed point in the connector of an instruction. -/
theorem measurableSet_mem_arc (z : ℂ) (n : ℕ) :
    MeasurableSet {ω | z ∈ ((↑) : ℝ → ℂ) '' GW2aCont.arcAt κ b J (boundaryWalkSpec b J θ true)
      (fun j => Ê j ω) n} := by
  by_cases hz : z.im = 0
  · have e : {ω | z ∈ ((↑) : ℝ → ℂ) '' GW2aCont.arcAt κ b J (boundaryWalkSpec b J θ true) (fun j => Ê j ω) n} =
        {ω | z.re ∈ GW2aCont.arcAt κ b J (boundaryWalkSpec b J θ true) (fun j => Ê j ω) n} := by
      ext ω
      simp only [mem_ofPred_eq, mem_image]
      constructor
      · rintro ⟨y, hy, rfl⟩; simpa using hy
      · intro h; exact ⟨z.re, h, Complex.ext (by simp) (by simp [hz])⟩
    rw [e]
    exact GW2aCont.measurableSet_mem_arcAt hb _ hÊm hÊreg n z.re
  · have e : {ω | z ∈ ((↑) : ℝ → ℂ) '' GW2aCont.arcAt κ b J (boundaryWalkSpec b J θ true) (fun j => Ê j ω) n} =
        ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_image, mem_empty_iff_false, iff_false, not_exists, not_and]
      intro y _ hy
      exact hz (by rw [← hy]; simp)
    rw [e]
    exact MeasurableSet.empty

include hb hÊm hÊreg hÊP in
/-- **Membership of a fixed point in the physical set after `n` instructions.** -/
theorem measurableSet_mem_physSet (z : ℂ) (n : ℕ) :
    MeasurableSet {ω | z ∈ statePhysicalSet 0 (wRun κ θ b J (fun j => Ê j ω) n)} := by
  have e : {ω | z ∈ statePhysicalSet 0 (wRun κ θ b J (fun j => Ê j ω) n)} =
      {_ω | z = 0} ∪ ⋃ j ∈ Finset.range n, ({ω | z ∈ newPiece κ b J θ true (fun j => Ê j ω) j} ∪
        {ω | z ∈ ((↑) : ℝ → ℂ) '' GW2aCont.arcAt κ b J (boundaryWalkSpec b J θ true) (fun j => Ê j ω) j}) := by
    ext ω
    have h := prefixPhysSet_eq_walk (hÊP ω) n
    change z ∈ SB.prefixPhysSet κ b J (boundaryWalkSpec b J θ true) (fun j => Ê j ω) n ↔ _
    rw [h]
    simp only [mem_union, mem_singleton_iff, mem_iUnion, mem_ofPred_eq, exists_prop]
  rw [e]
  exact (MeasurableSet.const _).union (MeasurableSet.biUnion (Finset.range n).countable_toSet fun j _ =>
    (measurableSet_mem_newPiece hb hÊm hÊreg hÊP z j).union (measurableSet_mem_arc hb hÊm hÊreg z j))

include hb hÊm hÊreg hÊP in
/-- **The entry stage of `R` is measurable.** -/
theorem measurableSet_entryStage_eq (R : ℝ) (r : ℕ) :
    MeasurableSet {ω | entryStage κ θ b J R (fun j => Ê j ω) = r} := by
  classical
  set A : ℕ → Set Ω := fun n => {ω | (R : ℂ) ∈ statePhysicalSet 0 (wRun κ θ b J (fun j => Ê j ω) (n + 1))}
    with hA
  have hAm : ∀ n, MeasurableSet (A n) := fun n => measurableSet_mem_physSet hb hÊm hÊreg hÊP _ _
  have e : {ω | entryStage κ θ b J R (fun j => Ê j ω) = r} =
      (A r ∩ ⋂ n ∈ Finset.range r, (A n)ᶜ) ∪ ({_ω | r = 0} ∩ ⋂ n, (A n)ᶜ) := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_iInter, mem_compl_iff, Finset.mem_range]
    unfold entryStage
    split_ifs with hex
    · constructor
      · intro h
        left
        refine ⟨?_, fun n hn => ?_⟩
        · rw [← h]; exact Nat.find_spec hex
        · exact Nat.find_min hex (h ▸ hn)
      · rintro (⟨h1, h2⟩ | ⟨-, h2⟩)
        · exact le_antisymm (Nat.find_min' hex h1) (not_lt.1 fun hlt => h2 _ hlt (Nat.find_spec hex))
        · exact absurd (Nat.find_spec hex) (h2 _)
    · simp only [not_exists] at hex
      constructor
      · intro h; right; exact ⟨h.symm, fun n => hex n⟩
      · rintro (⟨h1, -⟩ | ⟨h1, -⟩)
        · exact absurd h1 (hex r)
        · exact h1.symm
  rw [e]
  exact ((hAm r).inter (MeasurableSet.biInter (Finset.range r).countable_toSet fun n _ => (hAm n).compl)).union
    ((MeasurableSet.const _).inter (MeasurableSet.iInter fun n => (hAm n).compl))

include hb hÊm hÊreg hÊP in
/-- An event read through the entry stage. -/
theorem measurableSet_of_entryStage (R : ℝ) {P : ℕ → Prop} :
    MeasurableSet {ω | P (entryStage κ θ b J R (fun j => Ê j ω))} := by
  have e : {ω | P (entryStage κ θ b J R (fun j => Ê j ω))} =
      ⋃ r, {ω | entryStage κ θ b J R (fun j => Ê j ω) = r} ∩ {_ω | P r} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨r, hr, h⟩ => hr ▸ h⟩
  rw [e]
  exact MeasurableSet.iUnion fun r => (measurableSet_entryStage_eq hb hÊm hÊreg hÊP R r).inter (MeasurableSet.const _)

include hb hÊm hÊreg hÊP in
/-- The arc entry. -/
theorem measurableSet_arcEntry (R : ℝ) : MeasurableSet {ω | ArcEntry κ θ b J R (fun j => Ê j ω)} :=
  measurableSet_of_entryStage hb hÊm hÊreg hÊP R (P := fun e => e % 2 = 1)

include hb hÊm hÊreg hÊP in
/-- The start offset's fibres. -/
theorem measurableSet_startOff_eq (R : ℝ) (r : ℕ) :
    MeasurableSet {ω | startOff κ θ b J R (fun j => Ê j ω) = r} :=
  measurableSet_of_entryStage hb hÊm hÊreg hÊP R (P := fun e => 2 * (e / 2) = r)

include hb hÊm hÊreg in
/-- Membership of a fixed point in the restart set after `n` instructions. -/
theorem measurableSet_mem_restartSet (R : ℝ) (n : ℕ) :
    MeasurableSet {ω | R ∈ restartSet κ b J (wRun κ θ b J (fun j => Ê j ω) n)} := by
  have hS := isMeasState_run (κ := κ) hb (boundaryWalkSpec b J θ true) hÊm hÊreg n
  have e : {ω | R ∈ restartSet κ b J (wRun κ θ b J (fun j => Ê j ω) n)} =
      {_ω | R ∈ PiecewiseConstantBoundaryData.jumpSet b J} ∩
        ({ω | stPt (wRun κ θ b J (fun j => Ê j ω) n) < R} ∩
          {ω | -sleLambda κ < PiecewiseConstantBoundaryData.rightLim b R +
            stAngle (wRun κ θ b J (fun j => Ê j ω) n) * QuantumZipper.chiC κ}) := by
    ext ω
    simp only [restartSet, Finset.mem_filter, mem_ofPred_eq, mem_inter_iff]
  rw [e]
  exact (MeasurableSet.const _).inter ((measurableSet_lt hS.2.1 measurable_const).inter
    (measurableSet_lt measurable_const (measurable_const.add (hS.2.2.1.mul measurable_const))))

include hb hÊm hÊreg hÊP in
/-- **The mark entry.** -/
theorem measurableSet_markEntry (R : ℝ) : MeasurableSet {ω | MarkEntry κ θ b J R (fun j => Ê j ω)} := by
  refine (measurableSet_arcEntry hb hÊm hÊreg hÊP R).inter ?_
  exact measurableSet_natIdx (x := fun ω => startOff κ θ b J R (fun j => Ê j ω) + 1)
    (fun r => by
      have e : {ω | startOff κ θ b J R (fun j => Ê j ω) + 1 = r} =
          ⋃ s ∈ ({r - 1} : Set ℕ), {ω | startOff κ θ b J R (fun j => Ê j ω) = s} ∩ {_ω | s + 1 = r} := by
        ext ω
        simp only [mem_ofPred_eq, mem_iUnion, mem_singleton_iff, mem_inter_iff, exists_prop]
        constructor
        · intro h; exact ⟨r - 1, by omega, by omega, by omega⟩
        · rintro ⟨s, -, hs, h⟩; omega
      rw [e]
      exact MeasurableSet.biUnion (countable_singleton _) fun s _ =>
        (measurableSet_startOff_eq hb hÊm hÊreg hÊP R s).inter (MeasurableSet.const _))
    (A := fun n => {ω | R ∈ restartSet κ b J (wRun κ θ b J (fun j => Ê j ω) n)})
    (fun n => measurableSet_mem_restartSet hb hÊm hÊreg R n)

include hb hÊm hÊreg hÊP in
/-- **The zero root.** -/
theorem measurableSet_zeroRoot (R : ℝ) : MeasurableSet {ω | ZeroRoot κ θ b J R (fun j => Ê j ω)} :=
  (measurableSet_arcEntry hb hÊm hÊreg hÊP R).inter (measurableSet_markEntry hb hÊm hÊreg hÊP R).compl

include hb hÊm hÊreg hÊP in
/-- **The relative offset's fibres.** -/
theorem measurableSet_relOff_eq (R : ℝ) (r : ℕ) : MeasurableSet {ω | relOff κ θ b J R (fun j => Ê j ω) = r} := by
  classical
  have e : {ω | relOff κ θ b J R (fun j => Ê j ω) = r} =
      ({ω | MarkEntry κ θ b J R (fun j => Ê j ω)} ∩ {ω | startOff κ θ b J R (fun j => Ê j ω) + 2 = r}) ∪
        ({ω | MarkEntry κ θ b J R (fun j => Ê j ω)}ᶜ ∩ {ω | startOff κ θ b J R (fun j => Ê j ω) = r}) := by
    ext ω
    simp only [relOff, mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff]
    by_cases h : MarkEntry κ θ b J R (fun j => Ê j ω) <;> simp [h]
  rw [e]
  refine ((measurableSet_markEntry hb hÊm hÊreg hÊP R).inter ?_).union
    ((measurableSet_markEntry hb hÊm hÊreg hÊP R).compl.inter (measurableSet_startOff_eq hb hÊm hÊreg hÊP R r))
  exact measurableSet_of_entryStage hb hÊm hÊreg hÊP R (P := fun e => 2 * (e / 2) + 2 = r)

include hb hÊm hÊreg hÊP in
/-- **The launch at instruction `j + relOff`.** -/
theorem measurableSet_launch_relOff (R : ℝ) (j : ℕ) :
    MeasurableSet {ω | (wRun κ θ b J (fun i => Ê i ω) (j + relOff κ θ b J R (fun i => Ê i ω) + 1)).2.2.2.1
      (j + relOff κ θ b J R (fun i => Ê i ω)) ≠ none} := by
  refine measurableSet_natIdx (x := fun ω => j + relOff κ θ b J R (fun i => Ê i ω)) (fun r => ?_)
    (A := fun n => {ω | (wRun κ θ b J (fun i => Ê i ω) (n + 1)).2.2.2.1 n ≠ none})
    (fun n => measurableSet_launch hb hÊm hÊreg n)
  have e : {ω | j + relOff κ θ b J R (fun i => Ê i ω) = r} =
      ⋃ s ∈ ({r - j} : Set ℕ), {ω | relOff κ θ b J R (fun i => Ê i ω) = s} ∩ {_ω | j + s = r} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_singleton_iff, mem_inter_iff, exists_prop]
    constructor
    · intro h; exact ⟨r - j, rfl, by omega, by omega⟩
    · rintro ⟨s, -, hs, h⟩; omega
  rw [e]
  exact MeasurableSet.biUnion (countable_singleton _) fun s _ =>
    (measurableSet_relOff_eq hb hÊm hÊreg hÊP R s).inter (MeasurableSet.const _)

include hb hÊm hÊreg hÊP in
/-- A measurable family read at instruction `j + relOff`. -/
theorem measurable_at_relOff {β : Type*} [MeasurableSpace β] (R : ℝ) (j : ℕ) {g : ℕ → Ω → β}
    (hg : ∀ r, Measurable (g r)) : Measurable fun ω => g (j + relOff κ θ b J R (fun i => Ê i ω)) ω := by
  refine measurable_natIdx (x := fun ω => j + relOff κ θ b J R (fun i => Ê i ω)) (fun r => ?_) hg
  have e : {ω | j + relOff κ θ b J R (fun i => Ê i ω) = r} =
      ⋃ s ∈ ({r - j} : Set ℕ), {ω | relOff κ θ b J R (fun i => Ê i ω) = s} ∩ {_ω | j + s = r} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_singleton_iff, mem_inter_iff, exists_prop]
    constructor
    · intro h; exact ⟨r - j, rfl, by omega, by omega⟩
    · rintro ⟨s, -, hs, h⟩; omega
  rw [e]
  exact MeasurableSet.biUnion (countable_singleton _) fun s _ =>
    (measurableSet_relOff_eq hb hÊm hÊreg hÊP R s).inter (MeasurableSet.const _)

include hb hÊm hÊreg hÊP in
/-- **The lifetime at instruction `j + relOff`.** -/
theorem measurable_life_relOff (R : ℝ) (j : ℕ) :
    Measurable fun ω => (Ê (j + relOff κ θ b J R (fun i => Ê i ω)) ω).2 :=
  measurable_at_relOff hb hÊm hÊreg hÊP R j (g := fun r ω => (Ê r ω).2) fun r => measurable_snd.comp (hÊm r)

end Meas

end InteractingSLE.Theorem14.SB.Nv
