/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59PiecesImage
import InteractingSLE.Spec.Sec5.Prop59PiecesChain

/-!
# The candidate pieces of Proposition 5.9's construction along a tree of paths

Packet PROVE-PROP59-PIECES. Specification §5.2, proof of Proposition 5.9 (pp. 143–146); PROVE-PROP59T4 §5.1.
Given, for every depth `j` and every list `t` of switching clock values, a path `α j t` of the chart `Q` (the
flow line with the alternating extreme angles switched at the original times decoded from `t`, continued at its last
angle), this file builds PROVE-PROP59T4's candidate family:

* the candidate `(j, t)` is **alive** (`alive`) when `t` is an admissible list (`valid`), the sample is good (`G`) and
  the last switch `qLast j t` happens before the first new contact of `α j t` with the revealed counterflow;
* its piece is the piece of the dilated joint-chart image `tImg` after the chart capacity `startCap` of its last
  switch (`arcPiece`, `Prop59PiecesArc`), killed at its first new contact ("the trajectory is used only before its
  first new contact with the conditional domain boundary", p. 144; Astra's follow-up 4, §3.4, ruling R71);
* its initial marks (`marks`) are defined along the tree exactly as PROVE-PROP59T2's `nextStart`: the marks of the
  parent candidate at the switch, relative to the driver, with one new mark on each side at the driver (the two seed
  marks of the switch, Astra's (SW6)).

The clock values of a list are compressed original times (`Prop59PiecesClock`): `decode x = x/(1 − x)` is the
original time of the clock value `x < 1`.

## Main results

* **`TreeData.IsReg.isRegFam`**: the candidate family is regular (`Prop59System.IsRegFam`);
* `TreeData.IsTree.alive_init`, **`TreeData.recStart_eq`**: along the tree (paths agreeing with their parents up to
  the last switch), the recursive start of PROVE-PROP59-PIECES' `recStart` is the chart capacity of the last switch;
* `TreeData.mem_closure_image`: pre-contact image points lie in the closure of the node images when the positions of
  the paths at positive rational times are nodes;
* **`TreeData.isChainFamEx`**: the per-switch chain data `IsChainFamEx` (so `isStageSystem_histSys_ex` applies).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric Complex
open QuantumZipper (H fwdHull fwdMap)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Prop59Pieces

open WangWu WangWu.ImgWord GlueCond CrossCond.Word49 LawUnique CrossRestart Prop59System Prop59Stage
open Sec7.Lemma71C (capClock)

/-! ### Decoding clock values -/

/-- The original time `x/(1 − x)` of a compressed clock value `x`. -/
def decode (x : ℝ≥0) : ℝ := (x : ℝ) / (1 - x)

theorem physTime_decode {x : ℝ≥0} (hx : x < 1) : physTime (decode x) = x :=
  physTime_div_one_sub (by exact_mod_cast hx)

theorem decode_nonneg {x : ℝ≥0} (hx : x < 1) : 0 ≤ decode x :=
  div_nonneg x.coe_nonneg (sub_nonneg.2 (by exact_mod_cast hx.le))

/-- The original time of the last switch of a list (`0` for the empty list). -/
def qLast : (j : ℕ) → (Fin j → ℝ≥0) → ℝ
  | 0, _ => 0
  | j + 1, t => decode (t (Fin.last j))

/-! ### The candidate family -/

section Cand

variable {Ω : Type*} {nL₀ nR₀ : ℕ}

/-- The data of a tree of paths: the counterflow time `r`, the counterflow history `y`, the dilation `lam`, the good
set `G`, the paths `α`, the admissible lists `valid`, the root marks and the noises. -/
structure TreeData (Ω : Type*) (nL₀ nR₀ : ℕ) where
  r : ℝ≥0
  y : Ω → HistorySpace 0 0
  lam : Ω → ℝ
  G : Set Ω
  α : (j : ℕ) → (Fin j → ℝ≥0) → Ω → ℝ → ℂ
  valid : (j : ℕ) → (Fin j → ℝ≥0) → Prop
  xL0 : Ω → Fin nL₀ → ℝ
  xR0 : Ω → Fin nR₀ → ℝ
  noise : (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ

variable (D : TreeData Ω nL₀ nR₀)

/-- The good samples of an admissible list. -/
def TreeData.Gc (j : ℕ) (t : Fin j → ℝ≥0) : Set Ω := {ω | D.valid j t ∧ ω ∈ D.G}

/-- The image curve of the candidate `(j, t)`. -/
def TreeData.img (j : ℕ) (t : Fin j → ℝ≥0) : Ω → ℝ → ℂ := tImg D.r D.y D.lam (D.Gc j t) (D.α j t)

/-- The pre-contact times of the candidate `(j, t)`. -/
def TreeData.pre (j : ℕ) (t : Fin j → ℝ≥0) : Ω → Set ℝ := tPre D.r D.y (D.Gc j t) (D.α j t)

/-- **The candidate `(j, t)` is alive**: admissible, good, and its last switch precedes its first new contact. -/
def TreeData.alive (j : ℕ) (t : Fin j → ℝ≥0) : Set Ω := {ω | ω ∈ D.Gc j t ∧ qLast j t ∈ D.pre j t ω}

open scoped Classical in
/-- **The chart capacity of the last switch** (`0` off the alive event). -/
def TreeData.startCap (j : ℕ) (t : Fin j → ℝ≥0) (ω : Ω) : ℝ≥0 :=
  if ω ∈ D.alive j t then (capClock (D.img j t ω) (qLast j t)).toNNReal else 0

/-- The clock of the candidate `(j, t)` as stage data (for its inverse). -/
def TreeData.clkStage (j : ℕ) (t : Fin j → ℝ≥0) : StageData Ω (nL₀ + j) (nR₀ + j) :=
  ⟨⊥, ∅, fun _ => 0, fun _ _ => 0, fun _ _ _ => 0, fun _ _ _ => 0, fun _ _ => 0, fun _ => 0,
    arcClk (D.img j t) (D.pre j t) (D.startCap j t) (D.alive j t)⟩

/-- **The initial marks along the tree** (relative to the driver): the root marks, and at a switch the parent's
marks at the switch relative to the driver with one new mark on each side at the driver (PROVE-PROP59T2's
`nextStart`). -/
def TreeData.marks : (j : ℕ) → (Fin j → ℝ≥0) → Ω → (Fin (nL₀ + j) → ℝ) × (Fin (nR₀ + j) → ℝ)
  | 0, _ => fun ω => (D.xL0 ω, D.xR0 ω)
  | j + 1, t => fun ω =>
    (Fin.cons 0 fun i => arcVL (D.img j (Fin.init t)) (D.pre j (Fin.init t)) (D.startCap j (Fin.init t))
          (D.alive j (Fin.init t)) (fun ω => (TreeData.marks j (Fin.init t) ω).1) i
          (clkInv (D.clkStage j (Fin.init t)) (t (Fin.last j)) ω) ω -
        arcW (D.img j (Fin.init t)) (D.pre j (Fin.init t)) (D.startCap j (Fin.init t)) (D.alive j (Fin.init t))
          (clkInv (D.clkStage j (Fin.init t)) (t (Fin.last j)) ω) ω,
      Fin.cons 0 fun k => arcVR (D.img j (Fin.init t)) (D.pre j (Fin.init t)) (D.startCap j (Fin.init t))
          (D.alive j (Fin.init t)) (fun ω => (TreeData.marks j (Fin.init t) ω).2) k
          (clkInv (D.clkStage j (Fin.init t)) (t (Fin.last j)) ω) ω -
        arcW (D.img j (Fin.init t)) (D.pre j (Fin.init t)) (D.startCap j (Fin.init t)) (D.alive j (Fin.init t))
          (clkInv (D.clkStage j (Fin.init t)) (t (Fin.last j)) ω) ω)

/-- **The candidate family**: the piece of the image curve after the last switch, with the marks along the tree. -/
def TreeData.cand : CandFam Ω nL₀ nR₀ := fun j t =>
  arcPiece (D.img j t) (D.pre j t) (D.startCap j t) (D.alive j t) (fun ω => (D.marks j t ω).1)
    (fun ω => (D.marks j t ω).2) (D.noise j t)

theorem TreeData.clk_cand (j : ℕ) (t : Fin j → ℝ≥0) :
    (D.cand j t).clk = arcClk (D.img j t) (D.pre j t) (D.startCap j t) (D.alive j t) := rfl

theorem TreeData.candInv_eq (j : ℕ) (t : Fin j → ℝ≥0) (q : ℝ≥0) (ω : Ω) :
    candInv D.cand j t q ω = clkInv (D.clkStage j t) q ω := rfl

end Cand

/-! ### Regularity -/

section Reg

variable {Ω : Type*} [MeasurableSpace Ω] {nL₀ nR₀ : ℕ} {D : TreeData Ω nL₀ nR₀}

/-- **The hypotheses on a tree of paths**: measurable history, dilation, good set, paths and root marks; on the good
set the counterflow is good and every admissible path is a simple proper arc; the last switch of an admissible list
is at a rational original time. -/
structure TreeData.IsReg (D : TreeData Ω nL₀ nR₀) : Prop where
  y : Measurable D.y
  lam : Measurable D.lam
  lam_pos : ∀ ω, 0 < D.lam ω
  G : MeasurableSet D.G
  good : ∀ ω ∈ D.G, CfGood D.r (D.y ω) ∧ ∀ j t, D.valid j t → IsProperArc (D.α j t ω)
  α : ∀ j t u, Measurable fun ω => D.α j t ω u
  xL0 : Measurable D.xL0
  xR0 : Measurable D.xR0
  qrat : ∀ j t, D.valid j t → ∃ x : ℚ, qLast j t = x

variable (hD : D.IsReg)
include hD

theorem TreeData.IsReg.measurableSet_Gc (j : ℕ) (t : Fin j → ℝ≥0) : MeasurableSet (D.Gc j t) := by
  by_cases hv : D.valid j t
  · have e : D.Gc j t = D.G := by ext ω; simp only [TreeData.Gc, mem_ofPred_eq, hv, true_and]
    rw [e]; exact hD.G
  · have e : D.Gc j t = ∅ := by ext ω; simp only [TreeData.Gc, mem_ofPred_eq, hv, false_and, mem_empty_iff_false]
    rw [e]; exact MeasurableSet.empty

theorem TreeData.IsReg.good_Gc (j : ℕ) (t : Fin j → ℝ≥0) :
    ∀ ω ∈ D.Gc j t, CfGood D.r (D.y ω) ∧ IsProperArc (D.α j t ω) :=
  fun ω hω => ⟨(hD.good ω hω.2).1, (hD.good ω hω.2).2 j t hω.1⟩

theorem TreeData.IsReg.isKilledFamily (j : ℕ) (t : Fin j → ℝ≥0) : IsKilledFamily (D.img j t) (D.pre j t) :=
  isKilledFamily_tImg hD.y hD.lam hD.lam_pos (hD.measurableSet_Gc j t) (hD.good_Gc j t) (hD.α j t)

theorem TreeData.IsReg.measurableSet_alive (j : ℕ) (t : Fin j → ℝ≥0) : MeasurableSet (D.alive j t) := by
  by_cases hv : D.valid j t
  · obtain ⟨x, hx⟩ := hD.qrat j t hv
    have e : D.alive j t = D.Gc j t ∩ {ω | (x : ℝ) ∈ D.pre j t ω} := by
      ext ω; simp only [TreeData.alive, mem_ofPred_eq, mem_inter_iff, hx]
    rw [e]
    exact (hD.measurableSet_Gc j t).inter ((hD.isKilledFamily j t).pre x)
  · have e : D.alive j t = ∅ := by
      ext ω; simp only [TreeData.alive, TreeData.Gc, mem_ofPred_eq, hv, false_and, mem_empty_iff_false]
    rw [e]; exact MeasurableSet.empty

theorem TreeData.IsReg.measurable_startCap (j : ℕ) (t : Fin j → ℝ≥0) : Measurable (D.startCap j t) := by
  classical
  by_cases hv : D.valid j t
  · obtain ⟨x, hx⟩ := hD.qrat j t hv
    have hc := (hD.isKilledFamily j t).cap x
    have e : D.startCap j t = fun ω => if ω ∈ D.alive j t then
        (({ω | (x : ℝ) ∈ D.pre j t ω}.indicator fun ω => capClock (D.img j t ω) x) ω).toNNReal else 0 := by
      funext ω
      by_cases hω : ω ∈ D.alive j t
      · have hmem : ω ∈ {ω | (x : ℝ) ∈ D.pre j t ω} := by
          show (x : ℝ) ∈ D.pre j t ω; rw [← hx]; exact hω.2
        simp only [TreeData.startCap, hω, ↓reduceIte, indicator_of_mem hmem, hx]
      · simp only [TreeData.startCap, hω, ↓reduceIte]
    rw [e]
    exact Measurable.ite (hD.measurableSet_alive j t) (measurable_real_toNNReal.comp hc) measurable_const
  · have e : D.startCap j t = fun _ => 0 := by
      funext ω
      have hω : ω ∉ D.alive j t := fun h => hv h.1.1
      simp only [TreeData.startCap, hω, ↓reduceIte]
    rw [e]; exact measurable_const

theorem TreeData.IsReg.clk_props (j : ℕ) (t : Fin j → ℝ≥0) :
    (∀ ω, Continuous ((D.clkStage j t).clk ω) ∧ StrictMono ((D.clkStage j t).clk ω)) ∧
      ∀ s, Measurable fun ω => (D.clkStage j t).clk ω s :=
  ⟨fun ω => ⟨continuous_arcClk (hD.isKilledFamily j t).arc ω, strictMono_arcClk (hD.isKilledFamily j t).arc ω⟩,
    measurable_arcClk (hD.isKilledFamily j t) (hD.measurable_startCap j t) (hD.measurableSet_alive j t)⟩

theorem TreeData.IsReg.measurable_marks : ∀ (j : ℕ) (t : Fin j → ℝ≥0),
    (Measurable fun ω => (D.marks j t ω).1) ∧ Measurable fun ω => (D.marks j t ω).2
  | 0, _ => ⟨hD.xL0, hD.xR0⟩
  | j + 1, t => by
    obtain ⟨ihL, ihR⟩ := TreeData.IsReg.measurable_marks j (Fin.init t)
    have hF := hD.isKilledFamily j (Fin.init t)
    have hS := hD.measurable_startCap j (Fin.init t)
    have hA := hD.measurableSet_alive j (Fin.init t)
    have hs : Measurable (clkInv (D.clkStage j (Fin.init t)) (t (Fin.last j))) :=
      measurable_clkInv (hD.clk_props j (Fin.init t)).1 (hD.clk_props j (Fin.init t)).2 _
    have hW := (measurable_uncurry_arcW hF hS hA).comp (hs.prodMk measurable_id)
    refine ⟨measurable_pi_iff.2 fun i => ?_, measurable_pi_iff.2 fun k => ?_⟩
    · refine Fin.cases ?_ (fun i' => ?_) i
      · simp only [TreeData.marks, Fin.cons_zero]
        exact measurable_const
      · simp only [TreeData.marks, Fin.cons_succ]
        exact ((measurable_uncurry_arcVL hF hS hA ihL i').comp (hs.prodMk measurable_id)).sub hW
    · refine Fin.cases ?_ (fun k' => ?_) k
      · simp only [TreeData.marks, Fin.cons_zero]
        exact measurable_const
      · simp only [TreeData.marks, Fin.cons_succ]
        exact ((measurable_uncurry_arcVR hF hS hA ihR k').comp (hs.prodMk measurable_id)).sub hW

/-- **The candidate family is regular.** -/
theorem TreeData.IsReg.isRegFam : IsRegFam D.cand := fun j t =>
  isRegPiece_arcPiece (hD.isKilledFamily j t) (hD.measurable_startCap j t) (hD.measurableSet_alive j t)
    (hD.measurable_marks j t).1 (hD.measurable_marks j t).2 (D.noise j t)

end Reg


/-! ### The tree link -/

section Link

variable {Ω : Type*} {nL₀ nR₀ : ℕ} {D : TreeData Ω nL₀ nR₀}

/-- **Tree hypotheses for the link**: the parent of an admissible list is admissible, switches later, and the last
clock value is below `1`; an admissible path agrees with its parent's path up to its last switch. -/
structure TreeData.IsTree (D : TreeData Ω nL₀ nR₀) : Prop where
  init : ∀ j (t : Fin (j + 1) → ℝ≥0), D.valid (j + 1) t →
    D.valid j (Fin.init t) ∧ qLast j (Fin.init t) ≤ qLast (j + 1) t ∧ t (Fin.last j) < 1
  pfx : ∀ j (t : Fin (j + 1) → ℝ≥0), D.valid (j + 1) t → ∀ ω u, 0 ≤ u → u ≤ qLast (j + 1) t →
    D.α (j + 1) t ω u = D.α j (Fin.init t) ω u
  qnonneg : ∀ j t, D.valid j t → 0 ≤ qLast j t

/-- The capacity clock at `u` depends only on the curve on `[0, u]`. -/
theorem capClock_congr {γ γ' : ℝ → ℂ} {u : ℝ} (h : EqOn γ γ' (Icc 0 u)) : capClock γ u = capClock γ' u := by
  simp only [capClock, image_congr h]

theorem preContact_congr {α α' : ℝ → ℂ} {K : Set ℂ} {u v : ℝ} (h : EqOn α α' (Icc 0 v)) (huv : u ≤ v) :
    u ∈ preContact α K ↔ u ∈ preContact α' K := by
  constructor
  · rintro ⟨hu, hK⟩
    exact ⟨hu, fun w hw => by rw [← h ⟨hw.1, hw.2.trans huv⟩]; exact hK w hw⟩
  · rintro ⟨hu, hK⟩
    exact ⟨hu, fun w hw => by rw [h ⟨hw.1, hw.2.trans huv⟩]; exact hK w hw⟩

variable (hT : D.IsTree)
include hT

/-- An admissible path agrees with its parent's on `[0, qLast]`, and so do the images and the pre-contact times. -/
theorem TreeData.IsTree.img_eqOn {j : ℕ} {t : Fin (j + 1) → ℝ≥0} (hv : D.valid (j + 1) t) {ω : Ω} (hω : ω ∈ D.G) :
    EqOn (D.img (j + 1) t ω) (D.img j (Fin.init t) ω) (Icc 0 (qLast (j + 1) t)) := by
  intro u hu
  have h1 : ω ∈ D.Gc (j + 1) t := ⟨hv, hω⟩
  have h2 : ω ∈ D.Gc j (Fin.init t) := ⟨(hT.init j t hv).1, hω⟩
  simp only [TreeData.img, tImg_of_mem h1, tImg_of_mem h2, imgCurve, hT.pfx j t hv ω u hu.1 hu.2]

theorem TreeData.IsTree.mem_pre_iff {j : ℕ} {t : Fin (j + 1) → ℝ≥0} (hv : D.valid (j + 1) t) {ω : Ω}
    (hω : ω ∈ D.G) {u : ℝ} (hu : u ≤ qLast (j + 1) t) :
    u ∈ D.pre (j + 1) t ω ↔ u ∈ D.pre j (Fin.init t) ω := by
  have h1 : ω ∈ D.Gc (j + 1) t := ⟨hv, hω⟩
  have h2 : ω ∈ D.Gc j (Fin.init t) := ⟨(hT.init j t hv).1, hω⟩
  simp only [TreeData.pre, tPre_of_mem h1, tPre_of_mem h2]
  exact preContact_congr (fun w hw => hT.pfx j t hv ω w hw.1 hw.2) hu

/-- The parent of an alive candidate is alive. -/
theorem TreeData.IsTree.alive_init {j : ℕ} {t : Fin (j + 1) → ℝ≥0} {ω : Ω} (h : ω ∈ D.alive (j + 1) t)
    (hγ : IsKilledArc (D.img j (Fin.init t) ω) (D.pre j (Fin.init t) ω)) : ω ∈ D.alive j (Fin.init t) := by
  obtain ⟨⟨hv, hω⟩, hq⟩ := h
  obtain ⟨hv', hle, -⟩ := hT.init j t hv
  refine ⟨⟨hv', hω⟩, ?_⟩
  have hq' := (hT.mem_pre_iff hv hω le_rfl).1 hq
  exact hγ.icc _ hq' ⟨hT.qnonneg j _ hv', hle⟩

end Link

section RecStart

variable {Ω : Type*} [MeasurableSpace Ω] {nL₀ nR₀ : ℕ} {D : TreeData Ω nL₀ nR₀}

/-- **The recursive start is the chart capacity of the last switch** on the alive events. -/
theorem TreeData.recStart_eq (hD : D.IsReg) (hT : D.IsTree) :
    ∀ (j : ℕ) (t : Fin j → ℝ≥0) (ω : Ω), ω ∈ D.alive j t → recStart D.cand j t ω = D.startCap j t ω
  | 0, t, ω, hω => by
    have hγ := (hD.isKilledFamily 0 t).arc ω
    simp only [recStart, TreeData.startCap, hω, ↓reduceIte, qLast, hγ.capClock_zero, Real.toNNReal_zero,
      NNReal.coe_zero]
  | j + 1, t, ω, hω => by
    have hγ' := (hD.isKilledFamily j (Fin.init t)).arc ω
    have hγ := (hD.isKilledFamily (j + 1) t).arc ω
    have hω' := hT.alive_init hω hγ'
    obtain ⟨⟨hv, hG⟩, hq⟩ := hω
    obtain ⟨hv', hle, hlt⟩ := hT.init j t hv
    have hqP' : qLast (j + 1) t ∈ D.pre j (Fin.init t) ω := (hT.mem_pre_iff hv hG le_rfl).1 hq
    set Q := qLast (j + 1) t with hQ
    set S₀ := D.startCap j (Fin.init t) ω with hS₀
    have hS₀e : (S₀ : ℝ) = capClock (D.img j (Fin.init t) ω) (qLast j (Fin.init t)) := by
      simp only [hS₀, TreeData.startCap, hω', ↓reduceIte]
      exact Real.coe_toNNReal _ (hγ'.capClock_nonneg hω'.2)
    have hmono : (S₀ : ℝ) ≤ capClock (D.img j (Fin.init t) ω) Q := by
      rw [hS₀e]
      exact hγ'.strictMonoOn_capClock.monotoneOn hω'.2 hqP' hle
    set s : ℝ≥0 := (capClock (D.img j (Fin.init t) ω) Q).toNNReal - S₀ with hs
    have hsum : S₀ + s = (capClock (D.img j (Fin.init t) ω) Q).toNNReal := by
      rw [hs, add_tsub_cancel_of_le]
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (hγ'.capClock_nonneg hqP')]
      exact hmono
    have hclk : (D.cand j (Fin.init t)).clk ω s = t (Fin.last j) := by
      rw [TreeData.clk_cand, arcClk_of_mem hω']
      show absClock _ _ (S₀ + s) = _
      rw [hsum, absClock_capClock hγ' hqP', hQ, qLast, physTime_decode hlt, Real.toNNReal_coe]
    have hinv : candInv D.cand j (Fin.init t) (t (Fin.last j)) ω = s :=
      (eq_clkInv (d := (D.cand j (Fin.init t)).toStage ⊥ ∅ fun _ => 0)
        (strictMono_arcClk (hD.isKilledFamily j (Fin.init t)).arc ω) hclk).symm
    have hcap : capClock (D.img (j + 1) t ω) Q = capClock (D.img j (Fin.init t) ω) Q :=
      capClock_congr (hT.img_eqOn hv hG)
    have halive : ω ∈ D.alive (j + 1) t := ⟨⟨hv, hG⟩, hq⟩
    have hst : (D.startCap (j + 1) t ω : ℝ) = capClock (D.img (j + 1) t ω) Q := by
      simp only [TreeData.startCap, halive, ↓reduceIte]
      exact Real.coe_toNNReal _ (hγ.capClock_nonneg hq)
    rw [recStart, TreeData.recStart_eq hD hT j (Fin.init t) ω hω', hinv, hst, hcap, ← hS₀, ← NNReal.coe_add, hsum,
      Real.coe_toNNReal _ (hγ'.capClock_nonneg hqP')]

end RecStart

section Chain

variable {Ω : Type*} [MeasurableSpace Ω] {nL₀ nR₀ : ℕ} {D : TreeData Ω nL₀ nR₀}

/-- **The node images in the dilated joint chart**: `λ Ψ(z)` for the nodes `z ∈ Z ω` of the chart `Q` off the
revealed counterflow. -/
def TreeData.image (D : TreeData Ω nL₀ nR₀) (Z : Ω → Set ℂ) (ω : Ω) : Set ℂ :=
  {w | ∃ z ∈ Z ω, z ∈ H ∧ z ∉ cfHullQ D.r (D.y ω) ∧ w = (D.lam ω : ℂ) * revChart (cfDrv0 D.r (D.y ω)) D.r z}

/-- Pre-contact points of an admissible image curve lie in the closure of the node images, when its positions at
positive rational times are nodes. -/
theorem TreeData.mem_closure_image (hD : D.IsReg) {Z : Ω → Set ℂ} {j : ℕ} {t : Fin j → ℝ≥0} {ω : Ω}
    (hω : ω ∈ D.Gc j t) (hZ : ∀ q : ℚ, 0 < (q : ℝ) → D.α j t ω q ∈ Z ω) {u : ℝ} (hu : u ∈ D.pre j t ω) :
    D.img j t ω u ∈ closure (D.image Z ω) := by
  have hγ := (hD.isKilledFamily j t).arc ω
  set S : Set ℝ := Ioo 0 (Classical.choose (hγ.exists_gt u hu)) with hSdef
  obtain ⟨hS'P, huS'⟩ := Classical.choose_spec (hγ.exists_gt u hu)
  set S' := Classical.choose (hγ.exists_gt u hu)
  have hSP : S ⊆ D.pre j t ω := fun v hv => hγ.icc S' hS'P ⟨hv.1.le, hv.2.le⟩
  have hrat : D.img j t ω '' (S ∩ range ((↑) : ℚ → ℝ)) ⊆ D.image Z ω := by
    rintro _ ⟨v, ⟨hvS, q, rfl⟩, rfl⟩
    have hpre := hSP hvS
    rw [TreeData.pre, tPre_of_mem hω] at hpre
    refine ⟨D.α j t ω q, hZ q hvS.1, ((hD.good_Gc j t) ω hω).2.mem_H _ hvS.1, hpre.2 q ⟨hpre.1, le_rfl⟩, ?_⟩
    rw [TreeData.img, tImg_of_mem hω]
    beta_reduce
    rw [imgCurve_of_pos hvS.1]
  have hucl : u ∈ closure (S ∩ range ((↑) : ℚ → ℝ)) := by
    have h1 : u ∈ closure S := by
      rw [hSdef, closure_Ioo (hγ.nonneg u hu |>.trans_lt huS').ne]
      exact ⟨hγ.nonneg u hu, huS'.le⟩
    have h2 : closure S ⊆ closure (S ∩ range ((↑) : ℚ → ℝ)) :=
      closure_minimal (Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo) isClosed_closure
    exact h2 h1
  have hc : ContinuousWithinAt (D.img j t ω) (S ∩ range ((↑) : ℚ → ℝ)) u :=
    (hγ.cont u hu).mono fun v hv => hSP hv.1
  exact closure_mono hrat (hc.mem_closure_image hucl)


/-- **The per-switch chain data of the candidate family** (`IsChainFamEx`, with the recursive start): almost surely,
for every alive candidate and every piece time `s` before its first new contact, the Loewner trace of the image
curve (a continuous driver agreeing with the glued driver on a pre-contact prefix, WangWu's `exists_traceDriver`)
covers the chart capacities `[0, start + s]` inside the closure of the node images — provided the positions of the
admissible paths at positive rational times are nodes. -/
theorem TreeData.isChainFamEx (hD : D.IsReg) (hT : D.IsTree) {P : Measure Ω} {hnL : 0 < nL₀} {hnR : 0 < nR₀}
    {Z : Ω → Set ℂ} (hnode : ∀ᵐ ω ∂P, ∀ j t, D.valid j t → ∀ q : ℚ, 0 < (q : ℝ) → D.α j t ω q ∈ Z ω) :
    IsChainFamEx P D.cand hnL hnR (D.image Z) (recStart D.cand) := by
  refine isChainFamEx_of_trace (fun j t ω => strictMono_arcClk (hD.isKilledFamily j t).arc ω) fun j t => ?_
  filter_upwards [hnode] with ω hZ s hs _
  obtain ⟨hA, hlt⟩ := lt_arcζ_iff.1 hs
  have hγ := (hD.isKilledFamily j t).arc ω
  rw [D.recStart_eq hD hT j t ω hA]
  obtain ⟨S, hSP, hSlt⟩ := lt_kLife_iff.1 hlt
  rw [NNReal.coe_add] at hSlt
  have hS0 : 0 < S := by
    rcases (hγ.nonneg S hSP).eq_or_lt with h | h
    · rw [← h, hγ.capClock_zero] at hSlt
      exact absurd hSlt (not_lt.2 (add_nonneg (D.startCap j t ω).coe_nonneg s.coe_nonneg))
    · exact h
  obtain ⟨w, hw, hw0, -, η, hηL, -, hηγ⟩ := hγ.exists_traceDriver hSP hS0
  refine ⟨w, η, (D.startCap j t ω : ℝ) + s + 1, hw, hw0,
    ⟨hηL.1, hηL.2.1.mono Ico_subset_Ici_self, fun t' ht' _ => hηL.2.2 t' ht'⟩, by linarith, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hτle : x.toNNReal ≤ D.startCap j t ω + s := by
    rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_add]; exact hx.2
  have hτ : ((x.toNNReal : ℝ≥0) : WithTop ℝ≥0) < kLife (D.img j t ω) (D.pre j t ω) :=
    lt_of_le_of_lt (WithTop.coe_le_coe.2 hτle) hlt
  obtain ⟨hm, he⟩ := hγ.kInv_spec hτ
  have hle : kInv (D.img j t ω) (D.pre j t ω) x.toNNReal ≤ S :=
    hγ.kInv_le hSP hτ (by rw [Real.coe_toNNReal _ hx.1]; linarith [hx.2])
  have hxe : x = capClock (D.img j t ω) (kInv (D.img j t ω) (D.pre j t ω) x.toNNReal) := by
    rw [he, Real.coe_toNNReal _ hx.1]
  rw [hxe, hηγ _ ⟨hγ.nonneg _ hm, hle⟩]
  exact D.mem_closure_image hD hA.1 (hZ j t hA.1.1) hm

end Chain

end InteractingSLE.Sec5.Prop59Pieces
