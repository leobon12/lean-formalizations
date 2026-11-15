/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JyConc
import InteractingSLE.Spec.Supplement.SB2FinConfig
import InteractingSLE.Spec.Supplement.SB2LkS3

/-!
# SB2(2): the density of an actual piece's good times (option-independent part of D6)

Packet PROVE-SB2-LIFTSET (round 15). The last actual-piece fact of `StageFactsV2`: the times before the lifetime at
which the piece is in `D = c⁻¹ '' ℍ = ℍ \ fillH A` are dense — **for every launched piece whose launch state already
holds `R`** (all relative stages `≥ 2`, and the start piece of a mark entry; not the start piece of a pure piece
entry, §R14.2). Deterministic here, from:

* GW1's chain facts (`WalkChainFacts`: piece simplicity — a piece meets the earlier physical part only at its real
  seed; and the prefixes are preconnected, `prefix_facts`);
* Lemma S2 reflected (`s2HullRight`: the tail's points of `ℍ` off `A` are in `D`);
* the trace spending no time interval on `ℝ` (`FinRel.interior_real_times_eq_empty`, in the `ℝ≥0` form
  `interior_real_times_nn`);
* **Lemma S3 for the lower pieces** (`hS3`, the form of `SB2LowerNoCommonArcStatement`): no piece maps a time interval
  into `A`.

Results: `interior_real_times_nn`, `head_subset_of_preconnected`, `tip_inter_old_real` (piece simplicity in tip-set
form), **`hgd_of_launch`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep

/-- **A generating trace spends no time interval on `ℝ`** (`ℝ≥0` form, on an interval below the lifetime). -/
theorem interior_real_times_nn {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w T η)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) {a d : ℝ≥0} (hdT : (d : ℝ≥0∞) < T) :
    interior {t : ℝ≥0 | t ∈ Ioo a d ∧ (η t).im = 0} = ∅ := by
  have hd0 : (0 : ℝ) ≤ d := d.2
  have hT : ENNReal.ofReal (d : ℝ) < T := by rwa [ENNReal.ofReal_coe_nnreal]
  have hI := FinRel.interior_real_times_eq_empty (hη.isLoewnerTraceLT hT) (continuous_frozenDrive_of_lt hw hT)
    (by rw [frozenDrive_zero hd0, hw0])
  by_contra hne
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 hne
  have hxI := (interior_subset hx).1
  have hx0 : 0 < x := lt_of_le_of_lt (zero_le) hxI.1
  obtain ⟨l, r, ⟨hlx, hxr⟩, hsub⟩ :=
    (mem_nhds_iff_exists_Ioo_subset' ⟨0, hx0⟩ ⟨x + 1, lt_add_one x⟩).1 (isOpen_interior.mem_nhds hx)
  have hJ : Ioo (max (l : ℝ) 0) (min (r : ℝ) (d : ℝ)) ⊆
      {y ∈ Ioo (0 : ℝ) d | ((fun s : ℝ => η s.toNNReal) y).im = 0} := by
    intro y hy
    have hy0 : 0 < y := lt_of_le_of_lt (le_max_right _ _) hy.1
    have hyl : (l : ℝ) < y := lt_of_le_of_lt (le_max_left _ _) hy.1
    have hyr : y < r := lt_of_lt_of_le hy.2 (min_le_left _ _)
    have hyd : y < d := lt_of_lt_of_le hy.2 (min_le_right _ _)
    have hmem : y.toNNReal ∈ Ioo l r := by
      constructor
      · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hy0.le]; exact hyl
      · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hy0.le]; exact hyr
    exact ⟨⟨hy0, hyd⟩, (interior_subset (hsub hmem)).2⟩
  have hJo := interior_maximal hJ isOpen_Ioo
  rw [hI] at hJo
  have hxJ : (x : ℝ) ∈ Ioo (max (l : ℝ) 0) (min (r : ℝ) (d : ℝ)) :=
    ⟨max_lt (by exact_mod_cast hlx) (by exact_mod_cast hx0), lt_min (by exact_mod_cast hxr) (by exact_mod_cast hxI.2)⟩
  exact hJo hxJ

/-- **The head lies in a preconnected part of the range holding `β₀ 0` and `β₀ t_L`** (`β₀` a closed embedding). -/
theorem head_subset_of_preconnected {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀) {P : Set ℂ} (hP : P ⊆ range β₀)
    (hPc : IsPreconnected P) {tL : ℝ≥0} (h0 : β₀ 0 ∈ P) (hR : β₀ tL ∈ P) : β₀ '' Icc 0 tL ⊆ P := by
  have he := isClosedEmbedding_of_isProperCurve hβ
  have hT : IsPreconnected (β₀ ⁻¹' P) := by
    rw [← he.isInducing.isPreconnected_image, image_preimage_eq_of_subset hP]
    exact hPc
  exact image_subset_iff.2 (hT.Icc_subset h0 hR)

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → Drv}

/-- **Piece simplicity in tip-set form**: a launched piece meets the earlier physical part only at real points. -/
theorem tip_inter_old_real (hW : WalkChainFacts κ b jumps θ D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none) :
    (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).1.tipSet
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.1
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.2 ∩
      statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ⊆ {z : ℂ | z.im = 0} := by
  obtain ⟨⟨c, θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd := stStatus_ne_done_of_launches _ D hl'
  have hpt := (prefix_facts hW.1 hW.2 n).2 hnd
  obtain ⟨f, α, C, -, -, -, -, -, -, -, -, hq₀, -, hcap⟩ := hW.1 n c θ' hl' hpt
  have hti := Lx.instrTime_boundaryWalk_of_launch hl'
  have hc : c = stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) :=
    (eq_launch_of_launches _ D hl').2.2
  rw [hti, hc, hq₀] at hcap
  intro z hz
  have hz' : z ∈ ({((stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) : ℝ) : ℂ)} :
      Set ℂ) := by
    rw [← hcap]
    exact hz
  rw [mem_singleton_iff.1 hz']
  show (((stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) : ℝ) : ℂ)).im = 0
  simp

/-- **The good times of a launched piece are dense before its lifetime**, if its launch state holds the head. -/
theorem hgd_of_launch (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hW : WalkChainFacts κ b jumps θ D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    {c : Chart} {A : Set ℂ} (hA : IsClosed A) (hDom : c.2.1 '' H = H \ fillH A) {β₀ : ℝ≥0 → ℂ}
    (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D) {tL : ℝ≥0}
    (hhead : β₀ '' Icc 0 tL ⊆ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    (hright : ∀ t : ℝ≥0, tL < t → β₀ t ∈ H → β₀ t ∉ A → β₀ t ∈ H \ fillH A)
    (hS3 : ∀ s₁ s₂ : ℝ≥0, s₁ < s₂ → (s₂ : ℝ≥0∞) ≤ (D n).2 →
      ¬ pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) '' Ioo s₁ s₂ ⊆ A) :
    {t : ℝ≥0 | (t : ℝ≥0∞) < (D n).2} ⊆
      closure (goodT c (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)) := by
  set s₁ := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n with hs₁
  have hPR := pieceRegular_of_launch hP hl
  have hα := isGeneratingTrace_trOf hPR
  have hpc := continuousOn_pcPt_launch hP hl
  obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hP hl
  have hcc := isConformal_runChart_of_reg (boundaryWalkSpec b jumps θ true) hP n
  have hsimp := tip_inter_old_real hW hl
  intro t₀ ht₀
  by_contra hcl
  obtain ⟨U, hU, hUg⟩ : ∃ U ∈ 𝓝 t₀, U ∩ goodT c s₁ (D n) = ∅ := by
    rw [mem_closure_iff_nhds] at hcl
    push Not at hcl
    obtain ⟨U, hU, hUe⟩ := hcl
    exact ⟨U, hU, hUe⟩
  obtain ⟨u, htu, hIcoU⟩ := exists_Ico_subset_of_mem_nhds hU ⟨t₀ + 1, lt_add_one t₀⟩
  obtain ⟨d', htd', hd'T⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (show (t₀ : ℝ≥0∞) < (D n).2 from ht₀)
  set d := min u d' with hd
  have htd : t₀ < d := lt_min htu (by exact_mod_cast htd')
  have hdT : (d : ℝ≥0∞) < (D n).2 := lt_of_le_of_lt (by exact_mod_cast min_le_right u d') hd'T
  -- every time of `(t₀, d)` is bad
  have hIK : ∀ t ∈ Ioo t₀ d, (t : ℝ≥0∞) ≤ (D n).2 := fun t ht =>
    le_of_lt (lt_of_lt_of_le (ENNReal.coe_lt_coe.2 ht.2) hdT.le)
  have hbad : ∀ t ∈ Ioo t₀ d, pcPt s₁ (D n) t ∉ H \ fillH A := by
    intro t ht hgood
    have htU : t ∈ U := hIcoU ⟨le_of_lt ht.1, lt_of_lt_of_le ht.2 (min_le_left u d')⟩
    have : t ∈ U ∩ goodT c s₁ (D n) := ⟨htU, hIK t ht, by rw [hDom]; exact hgood⟩
    rw [hUg] at this
    exact this
  -- the interior lemma on `(t₀, d)`
  have hint := interior_setOf_notMem_domain_eq_empty (p := pcPt s₁ (D n)) (α := trOf (D n)) hA isOpen_Ioo
    (hpc.mono fun t ht => hIK t ht)
    (fun t ht => im_nonneg_of_isGeneratingTrace_le hα hPR.2.1 hPR.1 (hIK t ht))
    (fun t ht hH => by
      have he : pcPt s₁ (D n) t = (stChart s₁).2.1 (trOf (D n) t) := bdVal_eq_of_mem_H hcc.1.continuousOn hH
      rw [he]
      exact hcc.2.1 hH)
    (fun t ht hH hA' => by
      have hmem : pcPt s₁ (D n) t ∈ (newPc s₁ (D n)).1.tipSet (newPc s₁ (D n)).2.1 (newPc s₁ (D n)).2.2 := by
        rw [htip]; exact ⟨t, hIK t ht, rfl⟩
      obtain ⟨t', ht'⟩ := (hβr ▸ tipSet_subset_physSet_launch hl hmem : pcPt s₁ (D n) t ∈ range β₀)
      by_cases htl : t' ≤ tL
      · exfalso
        have hold := hhead ⟨t', ⟨zero_le, htl⟩, ht'⟩
        have hre := hsimp ⟨hmem, hold⟩
        have hpos : (0 : ℝ) < (pcPt s₁ (D n) t).im := hH
        rw [show (pcPt s₁ (D n) t).im = 0 from hre] at hpos
        exact lt_irrefl _ hpos
      · push Not at htl
        rw [← ht'] at hH hA' ⊢
        exact hright t' htl hH hA')
    (interior_real_times_nn hα (hPR.2.1.mono fun s hs => le_of_lt (show (s : ℝ≥0∞) < (D n).2 from hs)) hPR.1
      hdT)
    (fun a e hae hsub' => by
      have hed : e ≤ d := by
        by_contra hle
        push Not at hle
        obtain ⟨y, hy1, hy2⟩ := exists_between (max_lt hae hle)
        have hyI := hsub' ⟨lt_of_le_of_lt (le_max_left a d) hy1, hy2⟩
        exact absurd hyI.2 (not_lt.2 (le_of_lt (lt_of_le_of_lt (le_max_right a d) hy1)))
      exact hS3 a e hae (le_trans (ENNReal.coe_le_coe.2 hed) hdT.le))
  have hfull : {t : ℝ≥0 | t ∈ Ioo t₀ d ∧ pcPt s₁ (D n) t ∉ H \ fillH A} = Ioo t₀ d := by
    ext t
    exact ⟨fun h => h.1, fun h => ⟨h, hbad t h⟩⟩
  rw [hfull, isOpen_Ioo.interior_eq] at hint
  obtain ⟨y, hy⟩ := exists_between htd
  exact (hint ▸ (⟨hy.1, hy.2⟩ : y ∈ Ioo t₀ d) : y ∈ (∅ : Set ℝ≥0))

end InteractingSLE.Theorem14.SB.Lk
