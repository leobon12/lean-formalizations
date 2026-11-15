/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59PiecesSched

/-!
# The candidate paths of Proposition 5.13's tree from the code drivers

Packet PROVE-PROP59-PIECES. PROVE-PROP513C's code drivers `codeDriver c spec k f` (the Borel recursion of the
Section 4.2 determination maps along a schedule, deterministic in the field `f`) give every extreme-angle tree path
as a function of the field at **every** sample. The candidate path of a list `t` is the Loewner trace (LP11's
measurable reconstruction `LP.traceAt`) of the continued driver of its schedule `candSched j t`:

* `codeContext_eq_of_program`, `codeDriver_eq_of_program`: the code driver of piece `k` only depends on the
  instructions before `k` and the angle of `k`;
* `joinedDriver_append_eq_continued`: a joined driver ending with a piece of end time `u` agrees on `[0, u]` with
  the continued driver ending with the same piece continued (equal drivers on the pieces);
* `measurable_continuedDriver`;
* `qDrv`, **`qPath`**: the continued code driver and the candidate path; `measurable_qPath`;
* **`qPath_pfx`**: an admissible path agrees with its parent's path up to its last switch (every sample).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Prop59Pieces

open Prop513TreeExtract Prop513Schedule Exist.StagedLaw Exist.Staged LQGMetric Sec7.AdmCode Restart
open Sec7.StripSideHeightProb (catPath catPath_of_le)

/-! ### Code drivers only see earlier instructions -/

section Code

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)

theorem codeContext_eq_of_program (c : BoundaryWord) {spec spec' : ExplSpec} (f : DistOn upperHalfPlaneOpens) :
    ∀ k, (∀ i < k, spec.2.2[i]? = spec'.2.2[i]?) →
      codeContext h44 hκ hκ4 c spec k f = codeContext h44 hκ hκ4 c spec' k f
  | 0, _ => rfl
  | k + 1, h => by
    have ha : instrAngle spec k = instrAngle spec' k := by unfold instrAngle; rw [h k (Nat.lt_succ_self k)]
    have ht : instrTime spec k = instrTime spec' k := by unfold instrTime; rw [h k (Nat.lt_succ_self k)]
    simp only [codeContext, ha, ht,
      codeContext_eq_of_program c f k fun i hi => h i (Nat.lt_succ_of_lt hi)]

theorem codeDriver_eq_of_program (c : BoundaryWord) {spec spec' : ExplSpec} (f : DistOn upperHalfPlaneOpens)
    {k : ℕ} (h : ∀ i < k, spec.2.2[i]? = spec'.2.2[i]?) (ha : instrAngle spec k = instrAngle spec' k) :
    codeDriver h44 hκ hκ4 c spec k f = codeDriver h44 hκ hκ4 c spec' k f := by
  simp only [codeDriver, ha, codeContext_eq_of_program h44 hκ hκ4 c f k h]

end Code

/-! ### Joined and continued drivers -/

section Drivers

variable {Ω : Type*}

/-- **A joined driver ending with a piece of end time `u` agrees on `[0, u]` with the continued driver ending with
the same piece continued**, when the pieces' drivers agree. -/
theorem joinedDriver_append_eq_continued {E F : ℕ → Ω → Driver} (ω : Ω) (hF : ∀ k, (F k ω).1 0 = 0) :
    ∀ (A : List (ℝ × ℝ≥0)) (j : ℕ) (a : ℝ≥0) (x x' : ℝ × ℝ≥0), TimeOrdered a (A ++ [x']) →
      (∀ i, j ≤ i → i ≤ j + A.length → E i ω = F i ω) → ∀ {t : ℝ≥0}, t ≤ x'.2 - a →
      joinedDriver E j a (A ++ [x']) ω t = continuedDriver F j a (A ++ [x]) ω t
  | [], j, a, x, x', _, he, t, ht => by
    change catPath (E j ω).1 (x'.2 - a) (joinedDriver E (j + 1) x'.2 [] ω) t = (F j ω).1 t
    rw [catPath_of_le ht, he j le_rfl (by simp)]
  | p :: A, j, a, x, x', hl, he, t, ht => by
    have hA : A ++ [x] ≠ [] := by simp
    obtain ⟨q, l, hql⟩ := List.exists_cons_of_ne_nil hA
    change catPath (E j ω).1 (p.2 - a) (joinedDriver E (j + 1) p.2 (A ++ [x']) ω) t =
      continuedDriver F j a (p :: (A ++ [x])) ω t
    rw [hql]
    change _ = catPath (F j ω).1 (p.2 - a) (continuedDriver F (j + 1) p.2 (q :: l) ω) t
    rw [← hql, he j le_rfl (by omega)]
    have hl' : TimeOrdered p.2 (A ++ [x']) := timeOrdered_tail hl
    by_cases htp : t ≤ p.2 - a
    · simp only [catPath, htp, ↓reduceIte]
    · simp only [catPath, htp, ↓reduceIte]
      congr 1
      refine joinedDriver_append_eq_continued ω hF A (j + 1) p.2 x x' hl'
        (fun i hji hi => he i (by omega) (by simp only [List.length_cons]; omega)) ?_
      have hpa := hl.2 p List.mem_cons_self
      have hpx : p.2 ≤ x'.2 := hl'.2 x' (by simp)
      have htt : p.2 - a ≤ t := (lt_of_not_ge htp).le
      rw [← NNReal.coe_le_coe, NNReal.coe_sub htt, NNReal.coe_sub hpx, NNReal.coe_sub hpa]
      have h1 := NNReal.coe_le_coe.2 ht
      rw [NNReal.coe_sub (hpa.trans hpx)] at h1
      linarith

theorem measurable_continuedDriver [MeasurableSpace Ω] {E : ℕ → Ω → Driver} (hE : ∀ j, Measurable (E j)) :
    ∀ (l : List (ℝ × ℝ≥0)) (j : ℕ) (a : ℝ≥0), Measurable (continuedDriver E j a l)
  | [], _, _ => measurable_const
  | [_], j, _ => measurable_fst.comp (hE j)
  | p :: q :: l, j, a =>
    (Sec7.StripDet.measurable_catPath (p.2 - a)).comp
      ((measurable_fst.comp (hE j)).prodMk (measurable_continuedDriver hE (q :: l) (j + 1) p.2))

end Drivers

/-! ### The candidate paths -/

section QPath

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (c : BoundaryWord)
  {Ω : Type*} (F : Ω → DistOn upperHalfPlaneOpens)

/-- The code drivers of a schedule at the field `F ω`. -/
def codeFam (s : Schedule) : ℕ → Ω → Driver := fun k ω => codeDriver h44 hκ hκ4 c (scheduleSpec s) k (F ω)

/-- **The continued code driver of the candidate `(j, t)`.** -/
def qDrv (j : ℕ) (t : Fin j → ℝ≥0) : Ω → ℝ≥0 → ℝ :=
  continuedDriver (codeFam h44 hκ hκ4 c F (candSched j t)) 0 0 (scheduleList (candSched j t))

/-- **The candidate path of the list `t`** (chart `Q`): the Loewner trace of its continued code driver. -/
def qPath (j : ℕ) (t : Fin j → ℝ≥0) (ω : Ω) (u : ℝ) : ℂ := LP.traceAt u.toNNReal (qDrv h44 hκ hκ4 c F j t ω)

theorem measurable_qPath [MeasurableSpace Ω] (hF : Measurable F) (j : ℕ) (t : Fin j → ℝ≥0) (u : ℝ) :
    Measurable fun ω => qPath h44 hκ hκ4 c F j t ω u :=
  (LP.measurable_traceAt _).comp (measurable_continuedDriver
    (fun k => (measurable_codeDriver h44 hκ hκ4 c _ k).comp hF) _ _ _)

end QPath


/-! ### Prefix agreement along the tree -/

section Pfx

/-- The real-angle form of a schedule entry. -/
def gmap (p : Bool × ℚ) : ℝ × ℝ≥0 := (if p.1 then Real.pi / 2 else -(Real.pi / 2), (p.2 : ℝ).toNNReal)

theorem entries_succ (j : ℕ) (t : Fin (j + 1) → ℝ≥0) :
    entries (j + 1) t = entries j (Fin.init t) ++ [(stageFlag j, oTime (t (Fin.last j)))] := by
  simp only [entries, List.ofFn_succ', List.concat_eq_append, Fin.val_castSucc, Fin.val_last, Fin.init]

theorem scheduleList_mkSched' {j : ℕ} {t : Fin j → ℝ≥0} {v : ℚ} (hv : IsValid j t) (hlt : lastO j t < v) :
    scheduleList (mkSched j t v) = (entries j t).map gmap ++ [gmap (stageFlag j, v)] :=
  scheduleList_mkSched hv hlt

/-- Two programs with a common prefix `A` followed by pieces with the same first angle agree before the prefix's end
and have the same angle at it. -/
theorem program_agree (A B B' : List (ℝ × ℝ≥0)) (x x' : ℝ × ℝ≥0) (hx : x.1 = x'.1) :
    (∀ i < A.length, (scheduleProgram 0 (A ++ x :: B))[i]? = (scheduleProgram 0 (A ++ x' :: B'))[i]?) ∧
      instrAngle ⟨0, true, scheduleProgram 0 (A ++ x :: B)⟩ A.length =
        instrAngle ⟨0, true, scheduleProgram 0 (A ++ x' :: B')⟩ A.length := by
  have hlen : (scheduleProgram 0 A).length = A.length := length_scheduleProgram 0 A
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [scheduleProgram_append, scheduleProgram_append, List.getElem?_append_left (hlen ▸ hi),
      List.getElem?_append_left (hlen ▸ hi)]
  · simp only [instrAngle]
    rw [scheduleProgram_append, scheduleProgram_append, List.getElem?_append_right hlen.le,
      List.getElem?_append_right hlen.le, hlen, Nat.sub_self]
    simp only [scheduleProgram, List.getElem?_cons_zero, hx]

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (c : BoundaryWord)
  {Ω : Type*} (F : Ω → DistOn upperHalfPlaneOpens)

/-- **The continued code driver of an admissible list agrees with its parent's up to its last switch.** -/
theorem qDrv_pfx {j : ℕ} {t : Fin (j + 1) → ℝ≥0} (hv : IsValid (j + 1) t) (ω : Ω) {s : ℝ≥0}
    (hs : s ≤ ((oTime (t (Fin.last j)) : ℚ) : ℝ).toNNReal) :
    qDrv h44 hκ hκ4 c F (j + 1) t ω s = qDrv h44 hκ hκ4 c F j (Fin.init t) ω s := by
  have hv' := hv.init
  have hltP : lastO (j + 1) t < lastO (j + 1) t + 1 := lt_add_one _
  have hlt' : lastO j (Fin.init t) < lastO j (Fin.init t) + 1 := lt_add_one _
  set A := (entries j (Fin.init t)).map gmap with hA
  set x := gmap (stageFlag j, oTime (t (Fin.last j))) with hx
  set y := gmap (stageFlag (j + 1), lastO (j + 1) t + 1) with hy
  set x'' := gmap (stageFlag j, lastO j (Fin.init t) + 1) with hx''
  have hLP : scheduleList (candSched (j + 1) t) = A ++ x :: [y] := by
    rw [candSched, scheduleList_mkSched' hv hltP, entries_succ, List.map_append]
    simp [hA, hx, hy]
  have hL' : scheduleList (candSched j (Fin.init t)) = A ++ x'' :: [] := by
    rw [candSched, scheduleList_mkSched' hv' hlt']
  have hlenA : A.length = j := by rw [hA, List.length_map, length_entries]
  obtain ⟨hpre, hang⟩ := program_agree A [y] [] x x'' rfl
  have hcode : ∀ i, 0 ≤ i → i ≤ 0 + A.length →
      codeFam h44 hκ hκ4 c F (candSched (j + 1) t) i ω = codeFam h44 hκ hκ4 c F (candSched j (Fin.init t)) i ω := by
    intro i _ hi
    simp only [codeFam]
    refine codeDriver_eq_of_program h44 hκ hκ4 c (F ω) (fun i' hi' => ?_) ?_
    · simp only [scheduleSpec, hLP, hL']
      exact hpre i' (by omega)
    · rcases (show i < A.length ∨ i = A.length by omega) with hi' | rfl
      · unfold instrAngle; simp only [scheduleSpec, hLP, hL']; rw [hpre i hi']
      · simpa only [scheduleSpec, hLP, hL'] using hang
  have hto : TimeOrdered 0 (A ++ [x]) := by
    have h := timeOrdered_scheduleList (candSched (j + 1) t)
    rw [hLP] at h
    refine ⟨?_, fun p hp => h.2 p (by simp only [List.mem_append, List.mem_cons] at hp ⊢; tauto)⟩
    have h1 := h.1
    rw [show A ++ x :: [y] = (A ++ [x]) ++ [y] by simp] at h1
    exact (List.pairwise_append.1 h1).1
  have hlast : lastTime 0 (A ++ [x]) = x.2 := by
    rw [lastTime_eq_getLast _ _ (by simp)]; simp
  have hx2 : x.2 = ((oTime (t (Fin.last j)) : ℚ) : ℝ).toNNReal := rfl
  have hF0 : ∀ k, (codeFam h44 hκ hκ4 c F (candSched j (Fin.init t)) k ω).1 0 = 0 := fun k =>
    (codeDriver_regular h44 hκ hκ4 c _ k (F ω)).2.1
  have hF0' : ∀ k, (codeFam h44 hκ hκ4 c F (candSched (j + 1) t) k ω).1 0 = 0 := fun k =>
    (codeDriver_regular h44 hκ hκ4 c _ k (F ω)).2.1
  have hsx : s ≤ x.2 - 0 := by rw [tsub_zero, hx2]; exact hs
  unfold qDrv
  rw [hLP, hL']
  have h1 : continuedDriver (codeFam h44 hκ hκ4 c F (candSched (j + 1) t)) 0 0 (A ++ x :: [y]) ω s =
      joinedDriver (codeFam h44 hκ hκ4 c F (candSched (j + 1) t)) 0 0 (A ++ [x]) ω s := by
    have htoP : TimeOrdered 0 (A ++ x :: [y]) := by
      have h := timeOrdered_scheduleList (candSched (j + 1) t); rwa [hLP] at h
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
theorem qPath_pfx {j : ℕ} {t : Fin (j + 1) → ℝ≥0} (hv : IsValid (j + 1) t) (ω : Ω) {u : ℝ}
    (hu : u ≤ qLast (j + 1) t) :
    qPath h44 hκ hκ4 c F (j + 1) t ω u = qPath h44 hκ hκ4 c F j (Fin.init t) ω u := by
  unfold qPath
  refine LP.traceAt_congr fun r hr => qDrv_pfx h44 hκ hκ4 c F hv ω (hr.trans ?_)
  rw [← lastO_eq hv] at hu
  exact Real.toNNReal_le_toNNReal hu

end Pfx

end InteractingSLE.Sec5.Prop59Pieces
