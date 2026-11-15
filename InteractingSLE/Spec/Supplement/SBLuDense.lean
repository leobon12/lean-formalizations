/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLuChart
import InteractingSLE.Spec.Supplement.SBLxSucc
import InteractingSLE.Spec.Supplement.GW2aContArc

/-!
# A measurable dense family of a walk's retained prefix

Packet PROVE-T14-SBLEAVES6. For a boundary walk whose launched pieces are regular at every sample, the physical set
after `n` instructions is the root, the launched pieces read through the boundary values of their launch charts, and
the connectors (`prefixPhysSet_succ_walk`, `prefixPhysSet_eq_walk`). Hence it has a countable dense family
`pfam`: the boundary values at time `0` and at rational times before each lifetime (`LP.traceAt` reads the trace
there), and the rational points of the connectors (`pfam_mem`, `subset_closure_range_pfam`). For random drivers the
family is measurable (`measurable_pfam`): the launch events and connectors by PROVE-STAGEDLAW2/GW2AC, the boundary
values by `SBLuChart`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMapInv)

namespace InteractingSLE.Theorem14.SB.LuM

open Exist.Staged Exist.StagedLaw

/-! ### The chosen trace of a driver -/

open Classical in
/-- A continuous generating trace through the lifetime, transient when the lifetime is infinite, chosen when one
exists (`0` otherwise; `GW2aSingle.chosenTrace` at one sample). -/
def trOf (e : (ℝ≥0 → ℝ) × ℝ≥0∞) : ℝ≥0 → ℂ :=
  if hex : ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace e.1 e.2 η ∧ (e.2 = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) then
    hex.choose else 0

theorem chosenTrace_eq_trOf {Ω : Type*} (E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) :
    GW2aSingle.chosenTrace (fun t ω => (E ω).1 t) (fun ω => (E ω).2) ω = trOf (E ω) := rfl

theorem isGeneratingTrace_trOf {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (h : GW1P.PieceRegular e.1 e.2) :
    IsGeneratingTrace e.1 e.2 (trOf e) := by
  obtain ⟨-, -, α, hα, htr⟩ := h
  have hex : ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace e.1 e.2 η ∧ (e.2 = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) :=
    ⟨α, hα, htr⟩
  unfold trOf
  split_ifs
  exact hex.choose_spec.1

/-- A generating trace on `[0, S]` stays in `ℍ̄` up to `S`. -/
theorem im_nonneg_of_isGeneratingTrace_le {W : ℝ≥0 → ℝ} {S : ℝ≥0∞} {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace W S α)
    (hW : ContinuousOn W {t | (t : ℝ≥0∞) ≤ S}) (hW0 : W 0 = 0) {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ S) :
    0 ≤ (α t).im := by
  have hlim := CounterflowRange.tendsto_tip_stopped_of_tendsto (c := Chart.id) (f := id) hα hW hW0 ht
    ((continuous_id.tendsto (α t)).mono_left nhdsWithin_le_nhds)
  have hU : Continuous fun r : ℝ => W (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal :=
    (CounterflowRange.continuous_stopped hW).comp continuous_real_toNNReal
  have hU0 : (fun r : ℝ => W (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal) 0 = 0 := by
    simp only [Real.toNNReal_zero, ENNReal.coe_zero, zero_le, min_eq_left, ENNReal.toNNReal_zero]
    exact hW0
  have hmem : (α t) ∈ Hbar := by
    refine QuantumZipper.isClosed_Hbar.mem_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hyH : (y : ℂ) * Complex.I ∈ H := by
      show 0 < ((y : ℂ) * Complex.I).im
      simpa using hy
    exact le_of_lt (show 0 < (fwdMapInv _ _ _).im from
      QuantumZipper.RS.fwdMapInv_mem_H hU hU0 (NNReal.coe_nonneg t) hyH)
  exact hmem

/-! ### The physical set of a walk with regular launches -/

section Walk

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool}

/-- The physical points added by instruction `n` of a walk when it launches: the boundary values of the launch chart
along the chosen trace of the piece through its lifetime. -/
def newPiece (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ) :
    Set ℂ :=
  {z | (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1)).2.2.2.1 n ≠ none ∧
    ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 ∧
      bdVal (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)) (trOf (D n) t) = z}

/-- At a launch of a walk with regular launches, the launched piece is regular through its lifetime. -/
theorem pieceRegular_of_launch {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ right) D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1)).2.2.2.1 n ≠ none) :
    GW1P.PieceRegular (D n).1 (D n).2 := by
  obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  have h := hP n c θ' hcθ
  rwa [Lx.instrTime_boundaryWalk_of_launch hcθ, min_top_left] at h

/-- **One step of a walk with regular launches**: the physical set grows by the launched piece (read through the
boundary values of the launch chart) and by the connector recorded by the step. -/
theorem prefixPhysSet_succ_walk {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ right) D) (n : ℕ) :
    SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1) =
      SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D n ∪ newPiece κ b jumps θ right D n ∪
        ((↑) : ℝ → ℂ) '' GW2aCont.arcAt κ b jumps (boundaryWalkSpec b jumps θ right) D n := by
  by_cases hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1)).2.2.2.1 n ≠ none
  · have hPR := pieceRegular_of_launch hP hl
    have hα := isGeneratingTrace_trOf hPR
    have hcc := isConformal_runChart_of_reg (boundaryWalkSpec b jumps θ right) hP n
    have hcb := (GW1P.isClosed_pieces_run (boundaryWalkSpec b jumps θ right) D hP n).1
    obtain ⟨g, hgc, hgi, -, hgt⟩ := Lw.exists_bdryMap_of_hasProperBdryExt hcc hcb
    have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 → 0 ≤ (trOf (D n) t).im := fun t ht =>
      im_nonneg_of_isGeneratingTrace_le hα hPR.2.1 hPR.1 ht
    have harc : GW2aCont.arcAt κ b jumps (boundaryWalkSpec b jumps θ right) D n = ∅ := by
      rw [GW2aCont.arcAt_eq_newArc, GW1W.launch_walk hl]
      exact GW2aCont.newArc_of_arcs_eq (GW2aCont.arcs_launch _ _ _ _ _)
    rw [Lx.prefixPhysSet_succ_eq_image D hl hgc hgi hα hPR.2.1 hPR.1 hαH, harc, image_empty, union_empty]
    congr 1
    ext z
    simp only [newPiece, mem_ofPred_eq, mem_image]
    constructor
    · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨hl, t, ht, bdVal_eq_of_tendsto (hαH t ht) (hgt _ (hαH t ht))⟩
    · rintro ⟨-, t, ht, rfl⟩
      exact ⟨_, ⟨t, ht, rfl⟩, (bdVal_eq_of_tendsto (hαH t ht) (hgt _ (hαH t ht))).symm⟩
  · have hnone : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1)).2.2.2.1 n = none := by
      simpa using hl
    have hnp : newPiece κ b jumps θ right D n = ∅ := by
      ext z
      simp only [newPiece, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      exact fun h => absurd hnone h
    have hpc := GW1P.pieces_run_succ_of_noLaunch (κ := κ) (b := b) (jumps := jumps)
      (boundaryWalkSpec b jumps θ right) D hnone
    rw [hnp, union_empty]
    rcases GW2aCont.arcs_run_succ (κ := κ) (b := b) (jumps := jumps) (boundaryWalkSpec b jumps θ right) D n
      with e | ⟨a, e⟩
    · rw [GW2aCont.arcAt_of_arcs_eq e, image_empty, union_empty]
      simp only [SB.prefixPhysSet, hpc, e]
    · rw [GW2aCont.arcAt_eq_newArc, GW2aCont.newArc_of_arcs_eq_append e]
      simp only [SB.prefixPhysSet, hpc, e, List.mem_append, List.mem_singleton, iUnion_or, iUnion_union_distrib,
        iUnion_iUnion_eq_left, union_assoc]

/-- **The physical set of a walk with regular launches**: the root, and the launched pieces and recorded connectors
of the first `n` instructions. -/
theorem prefixPhysSet_eq_walk {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ right) D) :
    ∀ n, SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D n =
      {0} ∪ ⋃ j ∈ Finset.range n, (newPiece κ b jumps θ right D j ∪
        ((↑) : ℝ → ℂ) '' GW2aCont.arcAt κ b jumps (boundaryWalkSpec b jumps θ right) D j)
  | 0 => by
    simp [SB.prefixPhysSet, ExplState.run, ExplState.init, boundaryWalkSpec]
  | n + 1 => by
    rw [prefixPhysSet_succ_walk hP n, prefixPhysSet_eq_walk hP n, Finset.range_add_one,
      Finset.set_biUnion_insert]
    ext z
    simp only [mem_union]
    tauto

end Walk

/-- **Rational approximation from below**: a point `φ t`, `t > 0`, of a path continuous within `S` at `t` (with
`[0, t) ⊆ S`) is in the closure of the path's values at positive rational times before `t`. -/
theorem mem_closure_of_rat {φ : ℝ≥0 → ℂ} {S : Set ℝ≥0} {t : ℝ≥0} (hφ : ContinuousWithinAt φ S t) (ht0 : t ≠ 0)
    (hS : ∀ s, s < t → s ∈ S) {F : Set ℂ}
    (hF : ∀ q : ℚ, 0 < q → (q : ℝ).toNNReal < t → φ (q : ℝ).toNNReal ∈ F) : φ t ∈ closure F := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousWithinAt_iff.1 hφ ε hε
  have htpos : (0 : ℝ) < t := lt_of_le_of_ne t.coe_nonneg (fun h => ht0 (NNReal.coe_eq_zero.1 h.symm))
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max ((t : ℝ) - δ) 0 < t from max_lt (by linarith) htpos)
  have hq0 : (0 : ℝ) < q := lt_of_le_of_lt (le_max_right _ _) hq1
  have hqδ : (t : ℝ) - δ < q := lt_of_le_of_lt (le_max_left _ _) hq1
  have hsr : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq0.le
  have hst : (q : ℝ).toNNReal < t := by rw [← NNReal.coe_lt_coe, hsr]; exact hq2
  refine ⟨_, hF q (Rat.cast_pos.1 hq0) hst, ?_⟩
  rw [dist_comm]
  refine hδε (hS _ hst) ?_
  rw [NNReal.dist_eq, hsr, abs_sub_lt_iff]
  constructor <;> linarith

/-! ### The dense family -/

section Fam

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool}

/-- The index set of the dense family: time-`0` points of the pieces, rational-time points of the pieces, rational
points of the connectors. -/
abbrev PIdx : Type := (ℕ ⊕ (ℕ × ℚ)) ⊕ (ℕ × ℚ)

open Classical in
/-- **The dense family of a walk's physical set after `n` instructions** (`0`, the root, where a condition fails). -/
def pfam (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ) :
    PIdx → ℂ
  | Sum.inl (Sum.inl j) =>
    if j < n ∧ (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (j + 1)).2.2.2.1 j ≠ none then
      bdVal (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D j)) 0 else 0
  | Sum.inl (Sum.inr (j, q)) =>
    if j < n ∧ (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (j + 1)).2.2.2.1 j ≠ none ∧
        0 < q ∧ (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < (D j).2 then
      bdVal (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D j))
        (LP.traceAt (q : ℝ).toNNReal (D j).1) else 0
  | Sum.inr (j, q) =>
    if j < n ∧ (q : ℝ) ∈ GW2aCont.arcAt κ b jumps (boundaryWalkSpec b jumps θ right) D j then (q : ℂ) else 0

/-- The trace point at a time before the lifetime is the one read by `LP.traceAt`. -/
theorem traceAt_eq_trOf {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) (hP : GW1P.PieceRegular e.1 e.2) {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) < e.2) : LP.traceAt s e.1 = trOf e s :=
  LP.traceAt_eq_of_isGeneratingTrace (isGeneratingTrace_trOf hP) he.1 he.2.1 hs

/-- **Every point of the family lies in the physical set.** -/
theorem pfam_mem {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ right) D)
    (hreg : ∀ j, IsRegularDriver (D j)) (n : ℕ) (i : PIdx) :
    pfam κ b jumps θ right D n i ∈ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D n := by
  classical
  rw [prefixPhysSet_eq_walk hP n]
  have hpiece : ∀ j, j < n → ∀ z, z ∈ newPiece κ b jumps θ right D j →
      z ∈ ({0} ∪ ⋃ j ∈ Finset.range n, (newPiece κ b jumps θ right D j ∪
        ((↑) : ℝ → ℂ) '' GW2aCont.arcAt κ b jumps (boundaryWalkSpec b jumps θ right) D j) : Set ℂ) :=
    fun j hj z hz => Or.inr (mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 hj)) (Or.inl hz))
  have hzero : (0 : ℂ) ∈ ({0} ∪ ⋃ j ∈ Finset.range n, (newPiece κ b jumps θ right D j ∪
      ((↑) : ℝ → ℂ) '' GW2aCont.arcAt κ b jumps (boundaryWalkSpec b jumps θ right) D j) : Set ℂ) :=
    Or.inl rfl
  rcases i with (j | ⟨j, q⟩) | ⟨j, q⟩
  · simp only [pfam]
    split_ifs with h
    · refine hpiece j h.1 _ ⟨h.2, 0, by simp, ?_⟩
      rw [(isGeneratingTrace_trOf (pieceRegular_of_launch hP h.2)).1]
    · exact hzero
  · simp only [pfam]
    split_ifs with h
    · obtain ⟨hj, hl, -, hq⟩ := h
      refine hpiece j hj _ ⟨hl, _, hq.le, ?_⟩
      rw [traceAt_eq_trOf (hreg j) (pieceRegular_of_launch hP hl) hq]
    · exact hzero
  · simp only [pfam]
    split_ifs with h
    · exact Or.inr (mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 h.1)) (Or.inr ⟨_, h.2, rfl⟩))
    · exact hzero

/-- **The physical set lies in the closure of the family.** -/
theorem subset_closure_range_pfam {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ right) D) (hreg : ∀ j, IsRegularDriver (D j))
    (n : ℕ) : SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D n ⊆
      closure (range (pfam κ b jumps θ right D n)) := by
  classical
  rw [prefixPhysSet_eq_walk hP n]
  rintro z (hz | hz)
  · rw [mem_singleton_iff.1 hz]
    refine subset_closure ⟨Sum.inr (n, 0), ?_⟩
    simp [pfam]
  obtain ⟨j, hj, hz⟩ := mem_iUnion₂.1 hz
  have hjn : j < n := Finset.mem_range.1 (Finset.mem_coe.1 hj)
  rcases hz with ⟨hl, t, ht, rfl⟩ | ⟨x, hx, rfl⟩
  · have hPR := pieceRegular_of_launch hP hl
    have hα := isGeneratingTrace_trOf hPR
    have hcc := isConformal_runChart_of_reg (boundaryWalkSpec b jumps θ right) hP j
    have hcb := (GW1P.isClosed_pieces_run (boundaryWalkSpec b jumps θ right) D hP j).1
    obtain ⟨g, hgc, -, -, hgt⟩ := Lw.exists_bdryMap_of_hasProperBdryExt hcc hcb
    set c := stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D j) with hc
    have hαH : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ (D j).2 → 0 ≤ (trOf (D j) s).im := fun s hs =>
      im_nonneg_of_isGeneratingTrace_le hα hPR.2.1 hPR.1 hs
    have hφ : ContinuousOn (fun s => bdVal c (trOf (D j) s)) {s : ℝ≥0 | (s : ℝ≥0∞) ≤ (D j).2} := by
      refine (hgc.comp hα.2.1 fun s hs => hαH s hs).congr fun s hs => ?_
      exact bdVal_eq_of_tendsto (hαH s hs) (hgt _ (hαH s hs))
    rcases eq_or_ne t 0 with rfl | ht0
    · refine subset_closure ⟨Sum.inl (Sum.inl j), ?_⟩
      simp only [pfam, hjn, hl, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
      rw [hα.1]
    · refine mem_closure_of_rat (hφ t ht) ht0 (fun s hs => (ENNReal.coe_lt_coe.2 hs).le.trans ht) ?_
      intro q hq0 hst
      have hsζ : (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < (D j).2 := lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hst) ht
      refine ⟨Sum.inl (Sum.inr (j, q)), ?_⟩
      simp only [pfam]
      split_ifs with h
      · rw [traceAt_eq_trOf (hreg j) hPR hsζ]
      · exact absurd ⟨hjn, hl, hq0, hsζ⟩ h
  · have hxr : x ∈ closure (GW2aCont.arcAt κ b jumps (boundaryWalkSpec b jumps θ right) D j ∩
        range ((↑) : ℚ → ℝ)) := GW2aCont.arcAt_subset_closure_rat _ D j hx
    have himg := image_closure_subset_closure_image Complex.continuous_ofReal ⟨x, hxr, rfl⟩
    refine closure_mono ?_ himg
    rintro _ ⟨y, ⟨hy, q, rfl⟩, rfl⟩
    refine ⟨Sum.inr (j, q), ?_⟩
    simp only [pfam, hjn, hy, and_self, ↓reduceIte, Complex.ofReal_ratCast]

end Fam

/-! ### Measurability of the family -/

section Meas

variable {Ω : Type*} [MeasurableSpace Ω] {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool}

/-- **The dense family is measurable** for measurable drivers regular at every sample with regular launches. -/
theorem measurable_pfam (hb : IsPiecewiseConstantBoundaryData b jumps) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hP : ∀ ω, RegLaunches κ b jumps (boundaryWalkSpec b jumps θ right) fun j => E j ω) (n : ℕ) (i : PIdx) :
    Measurable fun ω => pfam κ b jumps θ right (fun j => E j ω) n i := by
  classical
  have hL : ∀ j, MeasurableSet {ω | (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) (fun j => E j ω)
      (j + 1)).2.2.2.1 j ≠ none} := fun j => (runMeasStatement κ b jumps hb _ E hE hreg j).1
  have hbd : ∀ j {Z : Ω → ℂ}, Measurable Z → Measurable fun ω =>
      bdVal (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) (fun j => E j ω) j)) (Z ω) :=
    fun j _ hZ => measurable_bdVal (measurable_runChart_inv hb _ hE hreg hP j)
      (fun ω => (isConformal_runChart_of_reg _ (hP ω) j).1.continuousOn) hZ
  rcases i with (j | ⟨j, q⟩) | ⟨j, q⟩
  · simp only [pfam]
    exact Measurable.ite ((MeasurableSet.const (j < n)).inter (hL j)) (hbd j measurable_const) measurable_const
  · simp only [pfam]
    refine Measurable.ite ?_ (hbd j ((LP.measurable_traceAt _).comp (measurable_fst.comp (hE j))))
      measurable_const
    exact (MeasurableSet.const _).inter ((hL j).inter ((MeasurableSet.const _).inter
      (measurableSet_lt measurable_const (measurable_snd.comp (hE j)))))
  · simp only [pfam]
    exact Measurable.ite ((MeasurableSet.const _).inter (GW2aCont.measurableSet_mem_arcAt hb _ hE hreg j q))
      measurable_const measurable_const

end Meas

/-! ### The truncated new piece -/

section Trunc

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool}

/-- The new piece of instruction `k` truncated at own time `d` (`Lx.PieceTrunc` at one sample). -/
def ptSet (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ)
    (d : ℝ≥0) : Set ℂ :=
  (fun z => limUnder (𝓝[H] z) (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k)).2.1) ''
    (trOf (D k) '' Icc 0 d)

theorem pieceTrunc_eq_ptSet {Ω : Type*} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (d : ℝ≥0) (ω : Ω) :
    Lx.PieceTrunc κ b jumps E k d ω = ptSet κ b jumps (-(Real.pi / 2)) true
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) k d := rfl

open Classical in
/-- **The dense family of the truncated new piece** (boundary values at time `0` and at rational times before `d`). -/
def tfam (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ)
    (d : ℝ≥0) : Option ℚ → ℂ
  | none => bdVal (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k)) 0
  | some q => if 0 < q ∧ (q : ℝ).toNNReal < d then
      bdVal (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k))
        (LP.traceAt (q : ℝ).toNNReal (D k).1)
    else bdVal (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k)) 0

/-- At a launch, the truncated piece is the path `t ↦ bdVal c (α t)` on `[0, d]`, which is continuous on `[0, ζ]`. -/
theorem ptSet_eq_and_continuousOn {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ right) D) {k : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k ≠ none) {d : ℝ≥0}
    (hd : (d : ℝ≥0∞) ≤ (D k).2) :
    ptSet κ b jumps θ right D k d = (fun t => bdVal (stChart (ExplState.run κ b jumps
        (boundaryWalkSpec b jumps θ right) D k)) (trOf (D k) t)) '' Icc 0 d ∧
      ContinuousOn (fun t => bdVal (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k))
        (trOf (D k) t)) {s : ℝ≥0 | (s : ℝ≥0∞) ≤ (D k).2} := by
  have hPR := pieceRegular_of_launch hP hl
  have hα := isGeneratingTrace_trOf hPR
  have hcc := isConformal_runChart_of_reg (boundaryWalkSpec b jumps θ right) hP k
  have hcb := (GW1P.isClosed_pieces_run (boundaryWalkSpec b jumps θ right) D hP k).1
  obtain ⟨g, hgc, -, -, hgt⟩ := Lw.exists_bdryMap_of_hasProperBdryExt hcc hcb
  have hαH : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ (D k).2 → 0 ≤ (trOf (D k) s).im := fun s hs =>
    im_nonneg_of_isGeneratingTrace_le hα hPR.2.1 hPR.1 hs
  refine ⟨?_, (hgc.comp hα.2.1 fun s hs => hαH s hs).congr fun s hs =>
    bdVal_eq_of_tendsto (hαH s hs) (hgt _ (hαH s hs))⟩
  simp only [ptSet, image_image]
  refine image_congr fun t ht => ?_
  have htζ : (t : ℝ≥0∞) ≤ (D k).2 := (ENNReal.coe_le_coe.2 ht.2).trans hd
  have := GW1P.neBot_nhdsWithin_H (hαH t htζ)
  rw [(hgt _ (hαH t htζ)).limUnder_eq, bdVal_eq_of_tendsto (hαH t htζ) (hgt _ (hαH t htζ))]

/-- **Every point of the truncation family lies in the truncated piece.** -/
theorem tfam_mem {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ right) D)
    (hreg : ∀ j, IsRegularDriver (D j)) {k : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k ≠ none) {d : ℝ≥0}
    (hd : (d : ℝ≥0∞) ≤ (D k).2) (i : Option ℚ) : tfam κ b jumps θ right D k d i ∈ ptSet κ b jumps θ right D k d := by
  have hPR := pieceRegular_of_launch hP hl
  have hα := isGeneratingTrace_trOf hPR
  rw [(ptSet_eq_and_continuousOn hP hl hd).1]
  have h0 : bdVal (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k)) 0 ∈
      (fun t => bdVal (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k))
        (trOf (D k) t)) '' Icc 0 d := ⟨0, ⟨le_rfl, zero_le⟩, by simp only [hα.1]⟩
  rcases i with _ | q
  · exact h0
  · simp only [tfam]
    split_ifs with h
    · have hsζ : (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < (D k).2 := (ENNReal.coe_lt_coe.2 h.2).trans_le hd
      refine ⟨_, ⟨zero_le, h.2.le⟩, ?_⟩
      rw [traceAt_eq_trOf (hreg k) hPR hsζ]
    · exact h0

/-- **The truncated piece lies in the closure of its family.** -/
theorem ptSet_subset_closure {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ right) D) (hreg : ∀ j, IsRegularDriver (D j)) {k : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k ≠ none) {d : ℝ≥0}
    (hd : (d : ℝ≥0∞) ≤ (D k).2) :
    ptSet κ b jumps θ right D k d ⊆ closure (range (tfam κ b jumps θ right D k d)) := by
  have hPR := pieceRegular_of_launch hP hl
  have hα := isGeneratingTrace_trOf hPR
  obtain ⟨he, hφ⟩ := ptSet_eq_and_continuousOn hP hl hd
  rw [he]
  rintro _ ⟨t, ht, rfl⟩
  have htζ : (t : ℝ≥0∞) ≤ (D k).2 := (ENNReal.coe_le_coe.2 ht.2).trans hd
  rcases eq_or_ne t 0 with rfl | ht0
  · exact subset_closure ⟨none, by simp only [tfam]; rw [hα.1]⟩
  · refine mem_closure_of_rat (hφ t htζ) ht0 (fun s hs => (ENNReal.coe_lt_coe.2 hs).le.trans htζ) ?_
    intro q hq0 hst
    have hsd : (q : ℝ).toNNReal < d := lt_of_lt_of_le hst ht.2
    have hsζ : (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < (D k).2 := (ENNReal.coe_lt_coe.2 hsd).trans_le hd
    refine ⟨some q, ?_⟩
    simp only [tfam]
    split_ifs with h
    · rw [traceAt_eq_trOf (hreg k) hPR hsζ]
    · exact absurd ⟨hq0, hsd⟩ h

/-- **The truncation family is measurable** (measurable truncation time). -/
theorem measurable_tfam {Ω : Type*} [MeasurableSpace Ω] (hb : IsPiecewiseConstantBoundaryData b jumps)
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hP : ∀ ω, RegLaunches κ b jumps (boundaryWalkSpec b jumps θ right) fun j => E j ω) (k : ℕ) {d : Ω → ℝ≥0}
    (hd : Measurable d) (i : Option ℚ) :
    Measurable fun ω => tfam κ b jumps θ right (fun j => E j ω) k (d ω) i := by
  classical
  have hbd : ∀ {Z : Ω → ℂ}, Measurable Z → Measurable fun ω =>
      bdVal (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) (fun j => E j ω) k)) (Z ω) :=
    fun hZ => measurable_bdVal (measurable_runChart_inv hb _ hE hreg hP k)
      (fun ω => (isConformal_runChart_of_reg _ (hP ω) k).1.continuousOn) hZ
  rcases i with _ | q
  · exact hbd measurable_const
  · simp only [tfam]
    exact Measurable.ite ((MeasurableSet.const _).inter (measurableSet_lt (by fun_prop) (by fun_prop)))
      (hbd ((LP.measurable_traceAt _).comp (measurable_fst.comp (hE k)))) (hbd measurable_const)

end Trunc

end InteractingSLE.Theorem14.SB.LuM
