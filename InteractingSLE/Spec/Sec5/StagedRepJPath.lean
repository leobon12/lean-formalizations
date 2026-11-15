/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedRepJWire
import InteractingSLE.Spec.Sec5.StagedNodeClause
import InteractingSLE.Spec.Sec5.StagedNCompArc
import InteractingSLE.Spec.Sec5.StagedS4Objects

/-!
# Prop 5.9's later root stages: the path clause

Packet PROVE-STAGED-REPJ. Clause 1 of `Wire.Night.RootLaw … (j + 1) t` for the stage objects `s4Objects` (whose root
noise is PROVE-STAGED-REP2's recovered noise `rootNoise`): on the reached event, the canonical start of PIECES' root
candidate is an ordered strict word and the candidate's processes with the recovered noise are Definition 2.1's local
integrated path up to the candidate's lifetime. This is PROVE-STAGED-NODE's `nodePath_of_mem` for the root tree itself:

* `canonY_rootCand_snd`: the canonical marks are the tree marks;
* **`rootPath_of_mem`**: the path clause at a reached sample with a good counterflow history (reached ⇒ alive by
  `TreeData.reach`, strict tree marks by NODE's `TreeData.marks_strict` with NODECOMP's `arcKilledWordStatement`, the
  one-point killed word and `IsKilledWord.isSLEPathUpTo_recNoise`);
* **`rootPathLaterOn_s4Objects`**: `RootPathLaterOn h44 (s4Objects h44)` from the clearance form of Part A;
* **`rootLaterOn_s4Objects_of_glue`**: `RootLaterOn h44 (s4Objects h44)` from the two glued identifications.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real
open LQGMetric (DistOn)

namespace InteractingSLE.Sec5.CrossCond.StagedRepJ

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord Restart Exist.StagedLaw Exist.Staged Wire.Night GlueCond Word49
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target Prop59Pieces Prop59Stage Prop59System Prop59Sched
open StagedRepLater StagedKCand StagedKill StagedRep StagedCand StagedS4 StagedNode
open Sec4 (IsStripGFF IsStripCounterflowDriver)

section Path

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω Ωa : Type} [mΩ : MeasurableSpace Ω]
  (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)

/-- PIECES' root candidates agree at a sample with the tree candidates at its first coordinate. -/
theorem pieceAt_rootCand (noise : ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) (q : ℚ) (ω' : Ω × Ωa) (j : ℕ)
    (t : Fin j → ℝ≥0) :
    PieceAt (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise
      (Ωa := Ωa) q j t) ((rootData x₀ h44 hκ hκ4 hb P h W ζ (q : ℝ).toNNReal (canonLam W ζ q) (canonXL x₀ hκ hb W ζ q)
      (canonXR x₀ hκ hb W ζ q) (noise q)).cand j t) ω' ω'.1 :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

/-- **The canonical marks of PIECES' root candidates are the tree marks.** -/
theorem canonY_rootCand_snd (noise : ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) (q : ℚ) (ω' : Ω × Ωa) (j : ℕ)
    (t : Fin (j + 1) → ℝ≥0) :
    (canonY (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise
      (Ωa := Ωa) q) (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) (j + 1) t ω').2 =
      (rootData x₀ h44 hκ hκ4 hb P h W ζ (q : ℝ).toNNReal (canonLam W ζ q) (canonXL x₀ hκ hb W ζ q)
        (canonXR x₀ hκ hb W ζ q) (noise q)).marks (j + 1) t ω'.1 := by
  rw [canonY_congr (fun j t => pieceAt_rootCand x₀ h44 hκ hκ4 hb P h W ζ noise q ω' j t)
    (y₀' := treeY0 (rootData x₀ h44 hκ hκ4 hb P h W ζ (q : ℝ).toNNReal (canonLam W ζ q) (canonXL x₀ hκ hb W ζ q)
      (canonXR x₀ hκ hb W ζ q) (noise q))) rfl (j + 1) t, TreeData.marks_succ]
  rfl

/-- **The path clause of PIECES' root candidate at depth `j + 1`** at a reached sample with a good counterflow history
(recovered root noise `rootNoise`). -/
theorem rootPath_of_mem (hhm : Measurable h) (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (q : ℚ) (j : ℕ) (t : Fin (j + 1) → ℝ≥0) (ω' : Ω × Ωa)
    (hgood : Cond44Ref.cfHistory W ζ ω'.1 ∈ goodSet49 (q : ℝ).toNNReal)
    (hR : ω' ∈ canonR (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
      (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (Ωa := Ωa) q) ratGrid (rootNL_pos _) (rootNR_pos _)
      (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) univ (j + 1) t) :
    IsOrderedForceWord (canonY (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
        (canonXR x₀ hκ hb W ζ) (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (Ωa := Ωa) q)
        (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) (j + 1) t ω').2.1
      (canonY (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
        (canonXR x₀ hκ hb W ζ) (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (Ωa := Ωa) q)
        (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) (j + 1) t ω').2.2 ∧
    StrictAnti (canonY (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
        (canonXR x₀ hκ hb W ζ) (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (Ωa := Ωa) q)
        (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) (j + 1) t ω').2.1 ∧
    StrictMono (canonY (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
        (canonXR x₀ hκ hb W ζ) (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (Ωa := Ωa) q)
        (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) (j + 1) t ω').2.2 ∧
    Sec2.IsSLEPathUpTo κ (canonY (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
        (canonXR x₀ hκ hb W ζ) (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (Ωa := Ωa) q)
        (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) (j + 1) t ω').2.1
      (canonY (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
        (canonXR x₀ hκ hb W ζ) (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (Ωa := Ωa) q)
        (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) (j + 1) t ω').2.2
      (stageρL κ (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) (j + 1))
      (stageρR κ (rootρR κ (sourceWord (x₀ := x₀) hκ hb)) (j + 1))
      ((rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
        (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (Ωa := Ωa) q (j + 1) t).W · ω')
      (fun i u => (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
        (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (Ωa := Ωa) q (j + 1) t).VL i u ω')
      (fun k u => (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
        (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (Ωa := Ωa) q (j + 1) t).VR k u ω')
      ((rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
        (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (Ωa := Ωa) q (j + 1) t).B · ω')
      ((rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
        (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (Ωa := Ωa) q (j + 1) t).ζ ω') := by
  set r : ℝ≥0 := (q : ℝ).toNNReal with hr
  set D := rootData x₀ h44 hκ hκ4 hb P h W ζ r (canonLam W ζ q) (canonXL x₀ hκ hb W ζ q)
    (canonXR x₀ hκ hb W ζ q) (rootNoise x₀ h44 hκ hκ4 hb P h W ζ q) with hD
  have hcfm := measurable_cfHistory_of_strip hcf
  have hlamm : Measurable (canonLam W ζ q) := (measurable_rootLam _).comp hcfm
  have hxLm : Measurable (canonXL x₀ hκ hb W ζ q) := measurable_pi_iff.2 fun i =>
    ((measurable_rootLam _).comp hcfm).mul ((measurable_pi_apply i).comp ((measurable_rootXL hκ hb _).comp hcfm))
  have hxRm : Measurable (canonXR x₀ hκ hb W ζ q) := measurable_pi_iff.2 fun k =>
    ((measurable_rootLam _).comp hcfm).mul ((measurable_pi_apply k).comp ((measurable_rootXR hκ hb _).comp hcfm))
  have hDr : D.IsReg := isReg_rootData x₀ h44 hκ hκ4 hb hhm hcf hlamm (fun _ => rootLam_pos _ _) hxLm hxRm
  have hDt : D.IsTree := isTree_rootData x₀ h44 hκ hκ4 hb
  -- reached ⇒ alive
  have hR1 : ω'.1 ∈ canonR D.cand ratGrid (rootNL_pos _) (rootNR_pos _) (treeY0 D) univ (j + 1) t :=
    (mem_canonR_congr ratGrid (rootNL_pos _) (rootNR_pos _)
      (fun j t => pieceAt_rootCand x₀ h44 hκ hκ4 hb P h W ζ (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) q ω' j t)
      (y₀' := treeY0 D) rfl (R₀' := univ) Iff.rfl (j + 1) t).1 hR
  have hA := (TreeData.reach (rootNL_pos _) (rootNR_pos _) hDr hDt (fun _ _ => Iff.rfl) (j + 1) t ω'.1 hR1).2
    (Nat.succ_pos j)
  -- the root marks are strictly ordered
  have hlam : 0 < canonLam W ζ q ω'.1 := rootLam_pos _ _
  have h0 : MarksStrict (D.xL0 ω'.1) (D.xR0 ω'.1) := by
    have hF := Theorem15.isOrderedForceWord_flowLine (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps 0
    have hxLs : StrictAnti (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) :=
      fun i i' hii => Theorem14.GW0.flowLineXL_lt _ _ 0 hii
    have hxRs : StrictMono (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) :=
      fun i i' hii => Theorem14.GW0.flowLineXR_lt _ _ 0 hii
    obtain ⟨-, o2, -, o4⟩ := histStart_ordered_dil hlam hF hgood (s := r)
    obtain ⟨s1, s2⟩ := histStart_strict_dil hlam hF hxLs hxRs hgood (s := r)
    exact ⟨o2, s1, o4, s2⟩
  have hq' : ∀ (k' : ℕ) (t' : Fin (k' + 1) → ℝ≥0), D.valid (k' + 1) t' →
      qLast k' (Fin.init t') < qLast (k' + 1) t' := by
    intro k' t' hv
    have hv' : IsValid (k' + 1) t' := hv
    cases k' with
    | zero => exact decode_pos (hv'.2 _).1 (hv'.2 _).2.1
    | succ k' => exact decode_strictMono (hv'.2 _).2.1 (hv'.1 (Fin.castSucc_lt_last (Fin.last k')))
  obtain ⟨hL0, hLs, hR0, hRs⟩ := TreeData.marks_strict hDr hDt StagedNComp.arcKilledWordStatement hq' ω'.1 h0 _ _ hA
  have hY := canonY_rootCand_snd x₀ h44 hκ hκ4 hb P h W ζ (Ωa := Ωa) (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) q ω' j t
  rw [hY]
  refine ⟨⟨hLs.antitone, hL0, hRs.monotone, hR0⟩, hLs, hRs, ?_⟩
  -- the killed word of the tree candidate's arc piece at this sample
  have hγ := (hDr.isKilledFamily (j + 1) t).arc ω'.1
  have hSlt := Prop59NodeTree.TreeData.startCap_lt_kLife hDr hA
  have hK := StagedNComp.arcKilledWordStatement (Ω := Unit) (γ := fun _ => D.img (j + 1) t ω'.1)
    (P := fun _ => D.pre (j + 1) t ω'.1) (S₀ := fun _ => D.startCap (j + 1) t ω'.1) (fun _ => hγ)
    (xL := fun _ => (D.marks (j + 1) t ω'.1).1) (xR := fun _ => (D.marks (j + 1) t ω'.1).2) (fun _ => hL0)
    (fun _ => hR0) (fun _ => hLs.antitone) (fun _ => hRs.monotone)
  have hζ0 : (0 : ℝ≥0∞) < arcζ (fun _ : Unit => D.img (j + 1) t ω'.1) (fun _ => D.pre (j + 1) t ω'.1)
      (fun _ => D.startCap (j + 1) t ω'.1) univ () := by
    have h1 := (lt_arcζ_iff (γ := D.img (j + 1) t) (P := D.pre (j + 1) t) (S₀ := D.startCap (j + 1) t)
      (A := D.alive (j + 1) t) (u := 0) (ω := ω'.1)).2 ⟨hA, by rwa [add_zero]⟩
    rw [arcζ_onePt hA, ENNReal.coe_zero] at h1
    exact h1
  have hVL0 : ∀ i, arcVL (fun _ : Unit => D.img (j + 1) t ω'.1) (fun _ => D.pre (j + 1) t ω'.1)
      (fun _ => D.startCap (j + 1) t ω'.1) univ (fun _ => (D.marks (j + 1) t ω'.1).1) i 0 () =
      (D.marks (j + 1) t ω'.1).1 i := fun i =>
    arcVL_zero_eq (A := univ) (ω := ()) hγ (mem_univ _) (hL0 i) hSlt
  have hVR0 : ∀ k, arcVR (fun _ : Unit => D.img (j + 1) t ω'.1) (fun _ => D.pre (j + 1) t ω'.1)
      (fun _ => D.startCap (j + 1) t ω'.1) univ (fun _ => (D.marks (j + 1) t ω'.1).2) k 0 () =
      (D.marks (j + 1) t ω'.1).2 k := fun k =>
    arcVR_zero_eq (A := univ) (ω := ()) hγ (mem_univ _) (hR0 k) hSlt
  have hnL : 0 < rootNL (sourceWord (x₀ := x₀) hκ hb) + (j + 1) :=
    Nat.lt_of_lt_of_le (rootNL_pos _) (Nat.le_add_right _ _)
  have hnR : 0 < rootNR (sourceWord (x₀ := x₀) hκ hb) + (j + 1) :=
    Nat.lt_of_lt_of_le (rootNR_pos _) (Nat.le_add_right _ _)
  have hthr0 : ¬ ForceWord.ThresholdCondition (stageρL κ (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) (j + 1))
      (stageρR κ (rootρR κ (sourceWord (x₀ := x₀) hκ hb)) (j + 1))
      (arcW (fun _ : Unit => D.img (j + 1) t ω'.1) (fun _ => D.pre (j + 1) t ω'.1)
        (fun _ => D.startCap (j + 1) t ω'.1) univ 0 ())
      (fun i => arcVL (fun _ : Unit => D.img (j + 1) t ω'.1) (fun _ => D.pre (j + 1) t ω'.1)
        (fun _ => D.startCap (j + 1) t ω'.1) univ (fun _ => (D.marks (j + 1) t ω'.1).1) i 0 ())
      (fun k => arcVR (fun _ : Unit => D.img (j + 1) t ω'.1) (fun _ => D.pre (j + 1) t ω'.1)
        (fun _ => D.startCap (j + 1) t ω'.1) univ (fun _ => (D.marks (j + 1) t ω'.1).2) k 0 ()) := by
    rw [arcW_zero']
    simp only [hVL0, hVR0]
    have eL : stageρL κ (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) (j + 1) ⟨0, hnL⟩ = newL κ j :=
      consAlt_zero_idx (newL κ) _ (Nat.succ_pos j)
    have eR : stageρR κ (rootρR κ (sourceWord (x₀ := x₀) hκ hb)) (j + 1) ⟨0, hnR⟩ = newR κ j :=
      consAlt_zero_idx (newR κ) _ (Nat.succ_pos j)
    refine not_threshold_of_unique ⟨0, hnL⟩ (fun i hi => ?_) (by rw [eL]; exact neg_two_lt_newL hκ hκ4 j)
      ⟨0, hnR⟩ (fun k hk => ?_) (by rw [eR]; exact neg_two_lt_newR hκ hκ4 j)
    · have hlt : (⟨0, hnL⟩ : Fin _) < i := by
        rw [Fin.lt_def]; exact Nat.pos_of_ne_zero fun h' => hi (Fin.ext h')
      exact ((hLs hlt).trans_le (hL0 _)).ne
    · have hlt : (⟨0, hnR⟩ : Fin _) < k := by
        rw [Fin.lt_def]; exact Nat.pos_of_ne_zero fun h' => hk (Fin.ext h')
      exact ((hR0 _).trans_lt (hRs hlt)).ne'
  have hp := hK.isSLEPathUpTo_recNoise (fun _ => hζ0) hκ (stageρL κ (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) (j + 1))
    (stageρR κ (rootρR κ (sourceWord (x₀ := x₀) hκ hb)) (j + 1)) () hthr0
  simp only [hVL0, hVR0] at hp
  simp only [← arcW_onePt (γ := D.img (j + 1) t) (P := D.pre (j + 1) t) (S₀ := D.startCap (j + 1) t) hA,
    ← arcVL_onePt (γ := D.img (j + 1) t) (P := D.pre (j + 1) t) (S₀ := D.startCap (j + 1) t) hA
      (fun ω => (D.marks (j + 1) t ω).1),
    ← arcVR_onePt (γ := D.img (j + 1) t) (P := D.pre (j + 1) t) (S₀ := D.startCap (j + 1) t) hA
      (fun ω => (D.marks (j + 1) t ω).2),
    ← arcζ_onePt (γ := D.img (j + 1) t) (P := D.pre (j + 1) t) (S₀ := D.startCap (j + 1) t) hA] at hp
  -- the noise of the candidate is the recovered noise of its own processes
  have hB : (fun u => (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
      (canonXR x₀ hκ hb W ζ) (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (Ωa := Ωa) q (j + 1) t).B u ω') =
      recNoise κ (stageρL κ (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) (j + 1))
        (stageρR κ (rootρR κ (sourceWord (x₀ := x₀) hκ hb)) (j + 1)) (D.marks (j + 1) t ω'.1).1
        (D.marks (j + 1) t ω'.1).2 (fun s => (D.cand (j + 1) t).W s ω'.1)
        (fun i s => (D.cand (j + 1) t).VL i s ω'.1) (fun k s => (D.cand (j + 1) t).VR k s ω'.1) := by
    have hag : (rootData0 x₀ h44 hκ hκ4 hb P h W ζ q).AgreeAt D ω'.1 ω'.1 :=
      ⟨rfl, rfl, rfl, Iff.rfl, fun _ _ => rfl, fun _ _ => Iff.rfl, rfl, rfl⟩
    have hm := hag.marks (j + 1) t
    have hc := hag.cand (j + 1) t
    funext u
    show rootNoise x₀ h44 hκ hκ4 hb P h W ζ q (j + 1) t u ω'.1 = _
    unfold rootNoise
    rw [hm]
    simp only [hc.W, hc.VL, hc.VR]
  rw [hB]
  exact hp

end Path

/-- **The later root path leaf for the concrete stage objects** (clearance form of Part A, as
`rootPathOn_s4Objects`). -/
theorem rootPathLaterOn_s4Objects (h44 : Theorem12ParamCond44Statement.{0}) (hA : PartAInputsSixteenDivOfClearance) :
    RootPathLaterOn h44 (s4Objects h44) := by
  intro κ x₀ a b a' b' hκ hκ4 hb Ω _ _ P _ h W ζ γ hG hcf htr d q hq j t
  have hr : 0 < (q : ℝ).toNNReal := Real.toNNReal_pos.2 (by exact_mod_cast hq)
  have h2 := Sec7.StripMarks.ae_cfHistory_mem_goodSet49_of_clearance hκ hκ4 hb hA hG hcf hr
  have h2' : ∀ᵐ ω' ∂(P.prod (Measure.dirac (0 : ℝ))), Cond44Ref.cfHistory W ζ ω'.1 ∈ goodSet49 (q : ℝ).toNNReal :=
    Measure.quasiMeasurePreserving_fst.ae h2
  show ∀ᵐ ω' ∂(P.prod (Measure.dirac (0 : ℝ))), _
  filter_upwards [h2'] with ω' hω hR
  exact rootPath_of_mem x₀ h44 hκ hκ4 hb P h W ζ hG.1 hcf q j t ω' hω hR

/-- **Theorem 1.2's leaf `hRootLater` for the concrete stage objects** from the two glued identifications. -/
theorem rootLaterOn_s4Objects_of_glue (h44 : Theorem12ParamCond44Statement.{0})
    (hA : PartAInputsSixteenDivOfClearance) (hpast : GluePastStatement h44) (hobs : GlueObsStatement h44) :
    RootLaterOn h44 (s4Objects h44) :=
  rootLaterOn_of_leaves h44 hA (s4Objects h44) (rootPathLaterOn_s4Objects h44 hA) hpast hobs

end InteractingSLE.Sec5.CrossCond.StagedRepJ
