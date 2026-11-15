/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59PiecesQPath
import InteractingSLE.Spec.Sec5.Prop513TargetInputs
import InteractingSLE.Spec.Sec7.StripWallVersion

/-!
# The candidate paths are simple proper arcs, and their positions are nodes of the tree

Packet PROVE-PROP59-PIECES. Deterministic part (every sample) of the identification of the candidate paths with
PROVE-PROP513C's tree (Astra's follow-up 5, §2.1–§2.2, ruling R73: each fixed canonical finite schedule is a
measurable function of the field; the realized adaptive prefix is the canonical path of its realized schedule):

* `exists_simple_trace_catPath_of`, **`continuedDriver_trace_transient`**: a continued driver of pieces with simple
  transient traces has a simple transient generating trace on `[0, ∞)` (PROVE-PROP513C's `continuedDriver_trace` with
  transience, `StripWall.tendsto_joinedTrace`);
* **`isProperArc_qPath_of`**: if the code pieces of the candidate's schedule are good paths, the candidate path is a
  simple proper arc, the Loewner trace of its continued driver;
* **`driverTree_mkSched_eq_qPath`**: if moreover the actual staged prefix driver of the truncated schedule
  `mkSched j t u` (`u` rational after the last switch) is the joined code driver, the node of the tree with that
  schedule is the candidate's position at `u`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Function
open QuantumZipper (H)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Prop59Pieces

open Prop513TreeExtract Prop513Schedule Prop513Target Exist.StagedLaw Exist.Staged LQGMetric Sec7.AdmCode Restart
open Sec7.StripSideHeightProb (catPath catPath_of_le)
open Sec7.StripWall (goodPathSet mem_goodPathSet continuous_of_isRegularDriver exists_simple_trace_of_goodPath)

/-! ### Simple transient traces of continued drivers -/

section Trace

variable {w₀ w₁ : ℝ≥0 → ℝ} {η₀ η₁ : ℝ≥0 → ℂ}

/-- A simple transient trace of a concatenated driver (PROVE-PROP513C's `exists_simple_trace_catPath`, with the
continuation's trace given). -/
theorem exists_simple_trace_catPath_of (h₀ : Continuous w₀) (h00 : w₀ 0 = 0) (h₁ : Continuous w₁) (h10 : w₁ 0 = 0)
    (hη₀ : IsGeneratingTrace w₀ ⊤ η₀) (hinj₀ : Injective η₀) (hH₀ : ∀ t, 0 < t → η₀ t ∈ H)
    (hη₁ : IsGeneratingTrace w₁ ⊤ η₁) (hinj₁ : Injective η₁) (hH₁ : ∀ t, 0 < t → η₁ t ∈ H)
    (ht₁ : Tendsto (fun t => ‖η₁ t‖) atTop atTop) (a : ℝ≥0) :
    ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (catPath w₀ a w₁) ⊤ η ∧ Injective η ∧ (∀ t, 0 < t → η t ∈ H) ∧
      Tendsto (fun t => ‖η t‖) atTop atTop := by
  obtain ⟨hinj, hH⟩ := Sec7.StripWall.joinedTrace_simple (a := a) h₀ h00 hη₀ hinj₀ hH₀ hinj₁ hH₁
  exact ⟨LoewnerConcat.joinedTrace w₀ η₀ a η₁, LoewnerConcat.isGeneratingTrace_catPath h₀ h00 h₁ h10
    (IsGeneratingTrace.mono_horizon hη₀ le_top) hη₁ hH₁, hinj, hH,
    Sec7.StripWall.tendsto_joinedTrace h₀ h00 hH₁ ht₁⟩

/-- The pieces of a continued driver with simple transient traces. -/
def GoodPieces {Ω : Type*} (E : ℕ → Ω → Driver) (ω : Ω) (i : ℕ) : Prop :=
  Continuous (E i ω).1 ∧ (E i ω).1 0 = 0 ∧ ∃ η, IsGeneratingTrace (E i ω).1 ⊤ η ∧ Injective η ∧
    (∀ t, 0 < t → η t ∈ H) ∧ Tendsto (fun t => ‖η t‖) atTop atTop

/-- **A continued driver of pieces with simple transient traces has a simple transient trace.** -/
theorem continuedDriver_trace_transient {Ω : Type*} (E : ℕ → Ω → Driver) (ω : Ω) :
    ∀ (j : ℕ) (a : ℝ≥0) (l : List (ℝ × ℝ≥0)), l ≠ [] → (∀ i, j ≤ i → i < j + l.length → GoodPieces E ω i) →
      Continuous (continuedDriver E j a l ω) ∧ continuedDriver E j a l ω 0 = 0 ∧
        ∃ η, IsGeneratingTrace (continuedDriver E j a l ω) ⊤ η ∧ Injective η ∧ (∀ t, 0 < t → η t ∈ H) ∧
          Tendsto (fun t => ‖η t‖) atTop atTop
  | _, _, [], hl, _ => absurd rfl hl
  | j, _, [_], _, he => he j le_rfl (by simp)
  | j, a, p :: q :: l, _, he => by
    obtain ⟨hc0, hz0, η0, hη0, hi0, hH0, -⟩ := he j le_rfl (by simp)
    obtain ⟨hc1, hz1, η1, hη1, hi1, hH1, ht1⟩ := continuedDriver_trace_transient E ω (j + 1) p.2 (q :: l)
      (List.cons_ne_nil _ _) fun i hji hi => he i (by omega) (by simp only [List.length_cons] at hi ⊢; omega)
    exact ⟨Sec7.StripSideHeightProb.continuous_catPath hc0 hc1 hz1, Sec7.StripSideHeightProb.catPath_zero hz0,
      exists_simple_trace_catPath_of hc0 hz0 hc1 hz1 hη0 hi0 hH0 hη1 hi1 hH1 ht1 (p.2 - a)⟩

/-- A good path gives a piece with a simple transient trace. -/
theorem goodPieces_of_mem {Ω : Type*} {E : ℕ → Ω → Driver} {ω : Ω} {i : ℕ} (hr : IsRegularDriver (E i ω))
    (hg : E i ω ∈ goodPathSet) : GoodPieces E ω i := by
  have htop := (mem_goodPathSet.1 hg).1
  have hcont := continuous_of_isRegularDriver hr htop
  have hg' : WangWu.ImgDrv.GoodPath (E i ω).1 ⊤ := by simpa only [htop] using mem_goodPathSet.1 hg
  obtain ⟨η, hη, hinj, hH, ht⟩ := exists_simple_trace_of_goodPath hcont hr.2.1 hg'
  exact ⟨hcont, hr.2.1, η, hη, hinj, hH, ht⟩

end Trace

/-! ### The candidate paths -/

section QPath

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (c : BoundaryWord)
  {Ω : Type*} (F : Ω → DistOn upperHalfPlaneOpens)

/-- **The candidate path is a simple proper arc** when the code pieces of its schedule are good paths: it is the
reparametrized Loewner trace of its continued code driver. -/
theorem isProperArc_qPath_of {j : ℕ} {t : Fin j → ℝ≥0} {ω : Ω}
    (hg : ∀ k < (scheduleList (candSched j t)).length, codeFam h44 hκ hκ4 c F (candSched j t) k ω ∈ goodPathSet) :
    WangWu.IsProperArc (qPath h44 hκ hκ4 c F j t ω) ∧
      ∃ η, IsGeneratingTrace (qDrv h44 hκ hκ4 c F j t ω) ⊤ η ∧ Continuous (qDrv h44 hκ hκ4 c F j t ω) ∧
        qDrv h44 hκ hκ4 c F j t ω 0 = 0 ∧ ∀ u : ℝ, qPath h44 hκ hκ4 c F j t ω u = η u.toNNReal := by
  have hne : scheduleList (candSched j t) ≠ [] := fun h => (candSched j t).2.1 (List.map_eq_nil_iff.1 h)
  obtain ⟨hc, h0, η, hη, hinj, hH, ht⟩ := continuedDriver_trace_transient _ ω 0 0 _ hne fun i _ hi =>
    goodPieces_of_mem (codeDriver_regular h44 hκ hκ4 c _ i (F ω)) (hg i (by omega))
  have hηc : Continuous η := continuousOn_univ.1 (hη.2.1.mono fun s _ => show (s : ℝ≥0∞) ≤ ⊤ from le_top)
  have he : ∀ u : ℝ, qPath h44 hκ hκ4 c F j t ω u = η u.toNNReal := fun u =>
    LP.traceAt_eq_of_isGeneratingTrace hη hc.continuousOn h0 ENNReal.coe_lt_top
  have hfun : qPath h44 hκ hκ4 c F j t ω = fun u => η u.toNNReal := funext he
  refine ⟨?_, η, hη, hc, h0, he⟩
  rw [hfun]
  exact WangWu.isProperArc_of_injective hηc hη.1 hinj hH ht

/-- **The node of the truncated schedule is the candidate's position.** Let `t` be admissible, `u` rational after its
last switch, the code pieces of the candidate's schedule good paths, and the actual prefix driver of `mkSched j t u`
equal (before its terminal time) to the joined code driver of `mkSched j t u`. Then the tree node with the schedule
`mkSched j t u` is the candidate's position at `u`. -/
theorem driverTree_mkSched_eq_qPath {E : Schedule → ℕ → Ω → Driver} {j : ℕ} {t : Fin j → ℝ≥0} (hv : IsValid j t)
    {u : ℚ} (hu : lastO j t < u) {ω : Ω}
    (hg : ∀ k < (scheduleList (candSched j t)).length, codeFam h44 hκ hκ4 c F (candSched j t) k ω ∈ goodPathSet)
    (hE : ∀ s : ℝ≥0, (s : ℝ≥0∞) < terminal (mkSched j t u) →
      prefixDriver E (mkSched j t u) ω s =
        joinedDriver (codeFam h44 hκ hκ4 c F (mkSched j t u)) 0 0 (scheduleList (mkSched j t u)) ω s) :
    driverTree E (scheduleIndex (mkSched j t u)) ω (treeTime (scheduleIndex (mkSched j t u))) =
      qPath h44 hκ hκ4 c F j t ω u := by
  obtain ⟨-, η, hη, hc, h0, he⟩ := isProperArc_qPath_of h44 hκ hκ4 c F hg
  set s := mkSched j t u with hs
  have hu0 : (0 : ℝ) < u := by exact_mod_cast (lastO_nonneg hv).trans_lt hu
  have hT : terminal s = (u : ℝ).toNNReal := terminal_mkSched hv hu
  -- the joined code driver of `s` is the continued code driver of the candidate on `[0, u]`
  have hlt' : lastO j t < lastO j t + 1 := lt_add_one _
  have hlenA : ((entries j t).map gmap).length = j := by rw [List.length_map, length_entries]
  have hcode : ∀ i, 0 ≤ i → i ≤ 0 + ((entries j t).map gmap).length →
      codeFam h44 hκ hκ4 c F s i ω = codeFam h44 hκ hκ4 c F (candSched j t) i ω := by
    intro i _ hi
    simp only [codeFam]
    refine codeDriver_eq_of_program h44 hκ hκ4 c (F ω) (fun i' hi' => ?_) ?_
    · exact instr_lt_mkSched hv hu hlt' (by omega)
    · rcases (show i < j ∨ i = j by omega) with hi' | rfl
      · unfold instrAngle; rw [instr_lt_mkSched hv hu hlt' hi']; rfl
      · exact instrAngle_mkSched hv hu hlt'
  have hto : TimeOrdered 0 ((entries j t).map gmap ++ [gmap (stageFlag j, u)]) := by
    have h := timeOrdered_scheduleList s
    rwa [hs, scheduleList_mkSched' hv hu] at h
  have hF0 : ∀ k, (codeFam h44 hκ hκ4 c F (candSched j t) k ω).1 0 = 0 := fun k =>
    (codeDriver_regular h44 hκ hκ4 c _ k (F ω)).2.1
  have hagree : ∀ r : ℝ≥0, r ≤ (u : ℝ).toNNReal →
      joinedDriver (codeFam h44 hκ hκ4 c F s) 0 0 (scheduleList s) ω r = qDrv h44 hκ hκ4 c F j t ω r := by
    intro r hr
    unfold qDrv candSched
    rw [hs, scheduleList_mkSched' hv hu, scheduleList_mkSched' hv hlt']
    exact joinedDriver_append_eq_continued ω hF0 _ 0 0 _ _ hto hcode (by rw [tsub_zero]; exact hr)
  -- a generating trace of the actual prefix driver on `[0, terminal]`
  have hgen : IsGeneratingTrace (prefixDriver E s ω) (terminal s) η := by
    refine Sec7.IsGeneratingTrace.congr_lt (IsGeneratingTrace.mono_horizon hη le_top) fun r hr => ?_
    rw [hE r hr, hagree r (by rw [← hT]; exact (ENNReal.coe_lt_coe.1 hr).le)]
  have hcont : ContinuousOn (prefixDriver E s ω) {r | (r : ℝ≥0∞) < terminal s} :=
    hc.continuousOn.congr fun r hr => by
      rw [hE r hr, hagree r (by rw [← hT]; exact (ENNReal.coe_lt_coe.1 hr).le)]
  have hpos : (0 : ℝ≥0∞) < terminal s := by rw [hT]; exact_mod_cast Real.toNNReal_pos.2 hu0
  have hz : prefixDriver E s ω 0 = 0 := by
    rw [hE 0 hpos, hagree 0 (zero_le), h0]
  have hidx : scheduleAt (scheduleIndex s) = s := scheduleAt_index s
  have htt : treeTime (scheduleIndex s) = u := by
    rw [treeTime, hidx, hT, Real.coe_toNNReal _ hu0.le]
  rw [driverTree, htt, hidx, prefixTrace_eq hcont hz (fun r _ => rfl) hgen
    ⟨hu0.le, by rw [hT, Real.coe_toNNReal _ hu0.le]⟩, he]

end QPath

end InteractingSLE.Sec5.Prop59Pieces
