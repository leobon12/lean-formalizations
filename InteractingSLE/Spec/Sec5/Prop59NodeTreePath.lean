/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59NodeTreeSched
import InteractingSLE.Spec.Sec5.Prop59PiecesTrace

/-!
# The candidate paths of a node tree and their identification with Proposition 5.13's tree

Packet PROVE-PROP59-NODETREE. PROVE-PROP59-PIECES' candidate paths (`qPath`, the Loewner traces of the continued code
drivers of PROVE-PROP513C) with arbitrary angle flags `fl` (`Prop59NodeTreeSched`):

* `qDrvF`, **`qPathF`**, `measurable_qPathF`;
* **`qPathF_pfx`**: an admissible path agrees with its parent's path up to its last switch (every sample);
* `isProperArc_qPathF_of`: a simple proper arc when the code pieces of its schedule are good paths;
* **`prefixTrace_mkSchedF_eq_qPathF`**: the actual staged trace of a truncated schedule `mkSchedF fl j t u` is the
  candidate path on `[0, u]`, when the actual prefix driver is the joined code driver;
* **`prefixTrace_node_eq_qPathF`**: the actual staged trace of a schedule `s` is, on `[0, terminal s]`, the candidate
  path of the node prefix `nodePre s` with the node flags (which continues `s` at the angle `+π/2`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Function
open QuantumZipper (H)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Prop59NodeTree

open Prop513TreeExtract Prop513Schedule Prop513Target Exist.StagedLaw Exist.Staged LQGMetric Sec7.AdmCode Restart
open Prop59Pieces
open Sec7.StripSideHeightProb (catPath catPath_of_le)
open Sec7.StripWall (goodPathSet)

section QPath

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (c : BoundaryWord)
  {Ω : Type*} (F : Ω → DistOn upperHalfPlaneOpens) (fl : ℕ → Bool)

/-- **The continued code driver of the candidate `(j, t)` with the flags `fl`.** -/
def qDrvF (j : ℕ) (t : Fin j → ℝ≥0) : Ω → ℝ≥0 → ℝ :=
  continuedDriver (codeFam h44 hκ hκ4 c F (candSchedF fl j t)) 0 0 (scheduleList (candSchedF fl j t))

/-- **The candidate path of the list `t` with the flags `fl`** (chart `Q`). -/
def qPathF (j : ℕ) (t : Fin j → ℝ≥0) (ω : Ω) (u : ℝ) : ℂ := LP.traceAt u.toNNReal (qDrvF h44 hκ hκ4 c F fl j t ω)

theorem measurable_qPathF [MeasurableSpace Ω] (hF : Measurable F) (j : ℕ) (t : Fin j → ℝ≥0) (u : ℝ) :
    Measurable fun ω => qPathF h44 hκ hκ4 c F fl j t ω u :=
  (LP.measurable_traceAt _).comp (measurable_continuedDriver
    (fun k => (measurable_codeDriver h44 hκ hκ4 c _ k).comp hF) _ _ _)

variable {fl}

/-- **The continued code driver of an admissible list agrees with its parent's up to its last switch.** -/
theorem qDrvF_pfx {j : ℕ} {t : Fin (j + 1) → ℝ≥0} (hv : IsValid (j + 1) t) (ω : Ω) {s : ℝ≥0}
    (hs : s ≤ ((oTime (t (Fin.last j)) : ℚ) : ℝ).toNNReal) :
    qDrvF h44 hκ hκ4 c F fl (j + 1) t ω s = qDrvF h44 hκ hκ4 c F fl j (Fin.init t) ω s := by
  have hv' := hv.init
  have hltP : lastO (j + 1) t < lastO (j + 1) t + 1 := lt_add_one _
  have hlt' : lastO j (Fin.init t) < lastO j (Fin.init t) + 1 := lt_add_one _
  set A := (entriesF fl j (Fin.init t)).map gmap with hA
  set x := gmap (fl j, oTime (t (Fin.last j))) with hx
  set y := gmap (fl (j + 1), lastO (j + 1) t + 1) with hy
  set x'' := gmap (fl j, lastO j (Fin.init t) + 1) with hx''
  have hLP : scheduleList (candSchedF fl (j + 1) t) = A ++ x :: [y] := by
    rw [candSchedF, scheduleList_mkSchedF hv hltP, entriesF_succ, List.map_append]
    simp [hA, hx, hy]
  have hL' : scheduleList (candSchedF fl j (Fin.init t)) = A ++ x'' :: [] := by
    rw [candSchedF, scheduleList_mkSchedF hv' hlt']
  obtain ⟨hpre, hang⟩ := program_agree A [y] [] x x'' rfl
  have hcode : ∀ i, 0 ≤ i → i ≤ 0 + A.length →
      codeFam h44 hκ hκ4 c F (candSchedF fl (j + 1) t) i ω =
        codeFam h44 hκ hκ4 c F (candSchedF fl j (Fin.init t)) i ω := by
    intro i _ hi
    simp only [codeFam]
    refine codeDriver_eq_of_program h44 hκ hκ4 c (F ω) (fun i' hi' => ?_) ?_
    · simp only [scheduleSpec, hLP, hL']
      exact hpre i' (by omega)
    · rcases (show i < A.length ∨ i = A.length by omega) with hi' | rfl
      · unfold instrAngle; simp only [scheduleSpec, hLP, hL']; rw [hpre i hi']
      · simpa only [scheduleSpec, hLP, hL'] using hang
  have hto : TimeOrdered 0 (A ++ [x]) := by
    have h := timeOrdered_scheduleList (candSchedF fl (j + 1) t)
    rw [hLP] at h
    refine ⟨?_, fun p hp => h.2 p (by simp only [List.mem_append, List.mem_cons] at hp ⊢; tauto)⟩
    have h1 := h.1
    rw [show A ++ x :: [y] = (A ++ [x]) ++ [y] by simp] at h1
    exact (List.pairwise_append.1 h1).1
  have hlast : lastTime 0 (A ++ [x]) = x.2 := by
    rw [lastTime_eq_getLast _ _ (by simp)]; simp
  have hx2 : x.2 = ((oTime (t (Fin.last j)) : ℚ) : ℝ).toNNReal := rfl
  have hF0 : ∀ k, (codeFam h44 hκ hκ4 c F (candSchedF fl j (Fin.init t)) k ω).1 0 = 0 := fun k =>
    (codeDriver_regular h44 hκ hκ4 c _ k (F ω)).2.1
  have hF0' : ∀ k, (codeFam h44 hκ hκ4 c F (candSchedF fl (j + 1) t) k ω).1 0 = 0 := fun k =>
    (codeDriver_regular h44 hκ hκ4 c _ k (F ω)).2.1
  have hsx : s ≤ x.2 - 0 := by rw [tsub_zero, hx2]; exact hs
  unfold qDrvF
  rw [hLP, hL']
  have h1 : continuedDriver (codeFam h44 hκ hκ4 c F (candSchedF fl (j + 1) t)) 0 0 (A ++ x :: [y]) ω s =
      joinedDriver (codeFam h44 hκ hκ4 c F (candSchedF fl (j + 1) t)) 0 0 (A ++ [x]) ω s := by
    have htoP : TimeOrdered 0 (A ++ x :: [y]) := by
      have h := timeOrdered_scheduleList (candSchedF fl (j + 1) t); rwa [hLP] at h
    have hxy : x.2 ≤ y.2 := by
      have h := (List.pairwise_append.1 htoP.1).2.1
      exact List.rel_of_pairwise_cons h (List.mem_singleton_self y)
    have hlastP : lastTime 0 (A ++ x :: [y]) = y.2 := by
      rw [lastTime_eq_getLast _ _ (by simp)]; simp
    rw [← joinedDriver_eq_continued _ ω 0 0 _ htoP (by
      rw [hlastP, tsub_zero]; rw [tsub_zero] at hsx; exact hsx.trans hxy)]
    rw [show A ++ x :: [y] = (A ++ [x]) ++ [y] by simp]
    exact (joinedDriver_prefix ω hF0' 0 0 (A ++ [x]) [y] hto (fun _ _ _ => rfl) (by rw [hlast]; exact hsx)).symm
  rw [h1]
  exact joinedDriver_append_eq_continued ω hF0 A 0 0 x'' x hto hcode hsx

/-- **An admissible path agrees with its parent's up to its last switch** (every sample). -/
theorem qPathF_pfx {j : ℕ} {t : Fin (j + 1) → ℝ≥0} (hv : IsValid (j + 1) t) (ω : Ω) {u : ℝ}
    (hu : u ≤ qLast (j + 1) t) :
    qPathF h44 hκ hκ4 c F fl (j + 1) t ω u = qPathF h44 hκ hκ4 c F fl j (Fin.init t) ω u := by
  unfold qPathF
  refine LP.traceAt_congr fun r hr => qDrvF_pfx h44 hκ hκ4 c F hv ω (hr.trans ?_)
  rw [← lastO_eq hv] at hu
  exact Real.toNNReal_le_toNNReal hu

/-- **The candidate path is a simple proper arc** when the code pieces of its schedule are good paths. -/
theorem isProperArc_qPathF_of {j : ℕ} {t : Fin j → ℝ≥0} {ω : Ω}
    (hg : ∀ k < (scheduleList (candSchedF fl j t)).length,
      codeFam h44 hκ hκ4 c F (candSchedF fl j t) k ω ∈ goodPathSet) :
    WangWu.IsProperArc (qPathF h44 hκ hκ4 c F fl j t ω) ∧
      ∃ η, IsGeneratingTrace (qDrvF h44 hκ hκ4 c F fl j t ω) ⊤ η ∧ Continuous (qDrvF h44 hκ hκ4 c F fl j t ω) ∧
        qDrvF h44 hκ hκ4 c F fl j t ω 0 = 0 ∧ ∀ u : ℝ, qPathF h44 hκ hκ4 c F fl j t ω u = η u.toNNReal := by
  have hne : scheduleList (candSchedF fl j t) ≠ [] := fun h =>
    (candSchedF fl j t).2.1 (List.map_eq_nil_iff.1 h)
  obtain ⟨hc, h0, η, hη, hinj, hH, ht⟩ := continuedDriver_trace_transient _ ω 0 0 _ hne fun i _ hi =>
    goodPieces_of_mem (codeDriver_regular h44 hκ hκ4 c _ i (F ω)) (hg i (by omega))
  have hηc : Continuous η := continuousOn_univ.1 (hη.2.1.mono fun s _ => show (s : ℝ≥0∞) ≤ ⊤ from le_top)
  have he : ∀ u : ℝ, qPathF h44 hκ hκ4 c F fl j t ω u = η u.toNNReal := fun u =>
    LP.traceAt_eq_of_isGeneratingTrace hη hc.continuousOn h0 ENNReal.coe_lt_top
  have hfun : qPathF h44 hκ hκ4 c F fl j t ω = fun u => η u.toNNReal := funext he
  refine ⟨?_, η, hη, hc, h0, he⟩
  rw [hfun]
  exact WangWu.isProperArc_of_injective hηc hη.1 hinj hH ht

/-- The actual staged trace of a schedule whose prefix driver agrees, before its terminal time, with a continuous
driver started at `0` having a generating trace `η` on `[0, ∞)`, is `η` on `[0, terminal]`. -/
theorem prefixTrace_eq_of_agree {E : Schedule → ℕ → Ω → Driver} {s : Schedule} {ω : Ω} {d : ℝ≥0 → ℝ}
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace d ⊤ η) (hc : Continuous d) (h0 : d 0 = 0)
    (hag : ∀ r : ℝ≥0, (r : ℝ≥0∞) < terminal s → prefixDriver E s ω r = d r) {u' : ℝ}
    (hu' : u' ∈ Icc 0 (terminal s : ℝ)) : prefixTrace (prefixDriver E) s ω u' = η u'.toNNReal := by
  have hgen : IsGeneratingTrace (prefixDriver E s ω) (terminal s) η :=
    Sec7.IsGeneratingTrace.congr_lt (IsGeneratingTrace.mono_horizon hη le_top) fun r hr => hag r hr
  have hcont : ContinuousOn (prefixDriver E s ω) {r | (r : ℝ≥0∞) < terminal s} :=
    hc.continuousOn.congr fun r hr => hag r hr
  have hpos : (0 : ℝ≥0∞) < terminal s := by exact_mod_cast terminal_pos s
  have hz : prefixDriver E s ω 0 = 0 := by rw [hag 0 hpos, h0]
  exact prefixTrace_eq hcont hz (fun r _ => rfl) hgen hu'

/-- **The actual staged trace of a truncated schedule is the candidate path** on `[0, u]`. -/
theorem prefixTrace_mkSchedF_eq_qPathF {E : Schedule → ℕ → Ω → Driver} {j : ℕ} {t : Fin j → ℝ≥0}
    (hv : IsValid j t) {u : ℚ} (hu : lastO j t < u) {ω : Ω}
    (hg : ∀ k < (scheduleList (candSchedF fl j t)).length,
      codeFam h44 hκ hκ4 c F (candSchedF fl j t) k ω ∈ goodPathSet)
    (hE : ∀ s : ℝ≥0, (s : ℝ≥0∞) < terminal (mkSchedF fl j t u) →
      prefixDriver E (mkSchedF fl j t u) ω s =
        joinedDriver (codeFam h44 hκ hκ4 c F (mkSchedF fl j t u)) 0 0 (scheduleList (mkSchedF fl j t u)) ω s)
    {u' : ℝ} (hu' : u' ∈ Icc 0 (terminal (mkSchedF fl j t u) : ℝ)) :
    prefixTrace (prefixDriver E) (mkSchedF fl j t u) ω u' = qPathF h44 hκ hκ4 c F fl j t ω u' := by
  obtain ⟨-, η, hη, hc, h0, he⟩ := isProperArc_qPathF_of h44 hκ hκ4 c F hg
  set s := mkSchedF fl j t u with hs
  have hT : terminal s = (u : ℝ).toNNReal := terminal_mkSchedF hv hu
  have hlt' : lastO j t < lastO j t + 1 := lt_add_one _
  have hcode : ∀ i, 0 ≤ i → i ≤ 0 + ((entriesF fl j t).map gmap).length →
      codeFam h44 hκ hκ4 c F s i ω = codeFam h44 hκ hκ4 c F (candSchedF fl j t) i ω := by
    intro i _ hi
    have hlenA : ((entriesF fl j t).map gmap).length = j := by rw [List.length_map, length_entriesF]
    simp only [codeFam]
    refine codeDriver_eq_of_program h44 hκ hκ4 c (F ω) (fun i' hi' => ?_) ?_
    · exact instr_lt_mkSchedF hv hu hlt' (by omega)
    · rcases (show i < j ∨ i = j by omega) with hi' | rfl
      · unfold instrAngle; rw [instr_lt_mkSchedF hv hu hlt' hi']; rfl
      · exact instrAngle_mkSchedF hv hu hlt'
  have hto : TimeOrdered 0 ((entriesF fl j t).map gmap ++ [gmap (fl j, u)]) := by
    have h := timeOrdered_scheduleList s
    rwa [hs, scheduleList_mkSchedF hv hu] at h
  have hF0 : ∀ k, (codeFam h44 hκ hκ4 c F (candSchedF fl j t) k ω).1 0 = 0 := fun k =>
    (codeDriver_regular h44 hκ hκ4 c _ k (F ω)).2.1
  have hagree : ∀ r : ℝ≥0, (r : ℝ≥0∞) < terminal s → prefixDriver E s ω r = qDrvF h44 hκ hκ4 c F fl j t ω r := by
    intro r hr
    rw [hE r hr]
    unfold qDrvF candSchedF
    rw [hs, scheduleList_mkSchedF hv hu, scheduleList_mkSchedF hv hlt']
    refine joinedDriver_append_eq_continued ω hF0 _ 0 0 _ _ hto hcode ?_
    rw [tsub_zero]
    have := (ENNReal.coe_lt_coe.1 hr).le
    rw [hT] at this
    exact this
  rw [prefixTrace_eq_of_agree hη hc h0 hagree hu', he]

/-- **The node of the truncated schedule is the candidate's position.** -/
theorem driverTree_mkSchedF_eq_qPathF {E : Schedule → ℕ → Ω → Driver} {j : ℕ} {t : Fin j → ℝ≥0}
    (hv : IsValid j t) {u : ℚ} (hu : lastO j t < u) {ω : Ω}
    (hg : ∀ k < (scheduleList (candSchedF fl j t)).length,
      codeFam h44 hκ hκ4 c F (candSchedF fl j t) k ω ∈ goodPathSet)
    (hE : ∀ s : ℝ≥0, (s : ℝ≥0∞) < terminal (mkSchedF fl j t u) →
      prefixDriver E (mkSchedF fl j t u) ω s =
        joinedDriver (codeFam h44 hκ hκ4 c F (mkSchedF fl j t u)) 0 0 (scheduleList (mkSchedF fl j t u)) ω s) :
    driverTree E (scheduleIndex (mkSchedF fl j t u)) ω (treeTime (scheduleIndex (mkSchedF fl j t u))) =
      qPathF h44 hκ hκ4 c F fl j t ω u := by
  have hu0 : (0 : ℝ) < u := by exact_mod_cast (lastO_nonneg hv).trans_lt hu
  have hT : terminal (mkSchedF fl j t u) = (u : ℝ).toNNReal := terminal_mkSchedF hv hu
  have hidx : scheduleAt (scheduleIndex (mkSchedF fl j t u)) = mkSchedF fl j t u := scheduleAt_index _
  have htt : treeTime (scheduleIndex (mkSchedF fl j t u)) = u := by
    rw [treeTime, hidx, hT, Real.coe_toNNReal _ hu0.le]
  rw [driverTree, htt, hidx]
  exact prefixTrace_mkSchedF_eq_qPathF h44 hκ hκ4 c F hv hu hg hE
    ⟨hu0.le, by rw [hT, Real.coe_toNNReal _ hu0.le]⟩

/-- **The actual staged trace of a schedule `s` is the candidate path of its node prefix** on `[0, terminal s]`
(the node path follows `s` and then continues at the angle `+π/2`). -/
theorem prefixTrace_node_eq_qPathF {E : Schedule → ℕ → Ω → Driver} {s : Schedule} {ω : Ω}
    (hg : ∀ k < (scheduleList (candSchedF (nodeFlag s) (nodeLen s) (nodePre s))).length,
      codeFam h44 hκ hκ4 c F (candSchedF (nodeFlag s) (nodeLen s) (nodePre s)) k ω ∈ goodPathSet)
    (hE : ∀ r : ℝ≥0, (r : ℝ≥0∞) < terminal s →
      prefixDriver E s ω r = joinedDriver (codeFam h44 hκ hκ4 c F s) 0 0 (scheduleList s) ω r)
    {u' : ℝ} (hu' : u' ∈ Icc 0 (terminal s : ℝ)) :
    prefixTrace (prefixDriver E) s ω u' = qPathF h44 hκ hκ4 c F (nodeFlag s) (nodeLen s) (nodePre s) ω u' := by
  obtain ⟨-, η, hη, hc, h0, he⟩ := isProperArc_qPathF_of h44 hκ hκ4 c F hg
  set m := nodeLen s
  set cs := candSchedF (nodeFlag s) m (nodePre s) with hcs
  have hlt : lastO m (nodePre s) < lastO m (nodePre s) + 1 := lt_add_one _
  set y := gmap (nodeFlag s m, lastO m (nodePre s) + 1) with hy
  have hL : scheduleList cs = scheduleList s ++ [y] := by
    rw [hcs, candSchedF, scheduleList_mkSchedF isValid_nodePre hlt, entriesF_nodePre]
    rfl
  have hlen : (scheduleList s).length = m := by simp [scheduleList, m, nodeLen]
  have hcode : ∀ i, 0 ≤ i → i < 0 + (scheduleList s).length →
      codeFam h44 hκ hκ4 c F s i ω = codeFam h44 hκ hκ4 c F cs i ω := by
    intro i _ hi
    have hp : ∀ k < (scheduleList s).length,
        (scheduleSpec s).2.2[k]? = (scheduleSpec cs).2.2[k]? := by
      intro k hk
      have hk' : k < (scheduleProgram 0 (scheduleList s)).length := by rw [length_scheduleProgram]; exact hk
      simp only [scheduleSpec, hL, scheduleProgram_append]
      rw [List.getElem?_append_left hk']
    simp only [codeFam]
    refine codeDriver_eq_of_program h44 hκ hκ4 c (F ω) (fun i' hi' => hp i' (by omega)) ?_
    unfold instrAngle
    rw [hp i (by omega)]
  have hto : TimeOrdered 0 (scheduleList s) := timeOrdered_scheduleList s
  have htoP : TimeOrdered 0 (scheduleList cs) := timeOrdered_scheduleList cs
  have hF0 : ∀ k, (codeFam h44 hκ hκ4 c F cs k ω).1 0 = 0 := fun k =>
    (codeDriver_regular h44 hκ hκ4 c _ k (F ω)).2.1
  have hagree : ∀ r : ℝ≥0, (r : ℝ≥0∞) < terminal s →
      prefixDriver E s ω r = qDrvF h44 hκ hκ4 c F (nodeFlag s) m (nodePre s) ω r := by
    intro r hr
    have hr' : r ≤ lastTime 0 (scheduleList s) - 0 := by
      rw [tsub_zero, ← terminal_eq_lastTime]; exact (ENNReal.coe_lt_coe.1 hr).le
    rw [hE r hr, joinedDriver_prefix ω hF0 0 0 (scheduleList s) [y] hto hcode hr', ← hL]
    unfold qDrvF
    refine joinedDriver_eq_continued _ ω 0 0 _ htoP ?_
    rw [tsub_zero, ← terminal_eq_lastTime]
    have h1 : r ≤ terminal s := (ENNReal.coe_lt_coe.1 hr).le
    refine h1.trans ?_
    rw [hcs, candSchedF, terminal_mkSchedF isValid_nodePre hlt, terminal, ← lastO_nodePre]
    exact Real.toNNReal_le_toNNReal (by push_cast; linarith)
  rw [prefixTrace_eq_of_agree hη hc h0 hagree hu', he]

end QPath

end InteractingSLE.Sec5.Prop59NodeTree
