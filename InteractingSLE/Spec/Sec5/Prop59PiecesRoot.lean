/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59PiecesTrace
import InteractingSLE.Spec.Sec5.Prop513WireCounterflow
import InteractingSLE.Spec.Sec5.CrossRestartMeas

/-!
# The concrete candidate pieces of Proposition 5.9 along Proposition 5.13's tree: regularity and chain data

Packet PROVE-PROP59-PIECES. In the setting of PROVE-PROP513C's assembly
(`Prop513Wire.prop513_path_of_partA_reverseVisit`:
the Figure 5.1 field `h`, its counterflow `W` with trace `γ`, the actual staged histories `E` of every extreme-angle
schedule), for a counterflow time `r`, this file builds the **root experiment's candidate family**: the candidate
`(j, t)` is the dilated joint-chart image of the canonical tree path `qPath` (the flow line of the source word, with
switches at the original times of `t`, PROVE-PROP513C's code drivers), read after its last switch and killed at its
first new contact (`TreeData`, `Prop59PiecesCand`). Astra's follow-up 5, §2 (ruling R73): each fixed canonical finite
schedule is a function of the field (§2.1–§2.2); the realized adaptive prefix of PROVE-PROP59T4's `histSys` is the
candidate at its realized (countably valued) index, the identification (2.2).

## Almost sure facts (countably many schedules)

* `ae_codeGood`: the code pieces of every schedule are good paths (simple transient traces);
* `ae_prefixDriver_eq_joined`: every actual staged prefix driver is the joined code driver;
* `ae_node`: the positions of every admissible candidate path at positive rational times are nodes of the tree
  (`driverTree E n ω (treeTime n)`);
* `ae_cfHistory_mem_goodHitSet`, `cfGood_of_mem_goodHitSet`: the counterflow history is good;
* `rootGood`, `ae_mem_rootGood`: a measurable good set of full measure.

## Main results

* `rootData`: the tree data of the root experiment (any measurable positive dilation, root marks and noises);
* **`isRegFam_rootData`**: the candidate family is regular (`Prop59System.IsRegFam`);
* **`isChainFamEx_rootData`**: its per-switch chain data (`IsChainFamEx`) with the dilated joint-chart images of the
  tree nodes, so that `isStageSystem_histSys_ex` applies.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Function
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.Prop59Pieces

open Prop513TreeExtract Prop513Schedule Prop513Target Exist.StagedLaw Exist.Staged LQGMetric Sec7.AdmCode Restart
open Sec4 Theorem14.StagedReg GlueCond CrossCond.Word49 WangWu LawUnique
open Sec7.StripWall (goodPathSet)

/-! ### Countably many admissible lists -/

instance countable_valid (j : ℕ) : Countable {t : Fin j → ℝ≥0 // IsValid j t} := by
  refine Function.Injective.countable (f := fun t => fun i => ratVal (t.1 i)) ?_
  intro t t' h
  apply Subtype.ext
  funext i
  have h1 := ratVal_spec (t.2.2 i).2.2
  have h2 := ratVal_spec (t'.2.2 i).2.2
  have := congrFun h i
  apply NNReal.coe_injective
  rw [← h1, ← h2]
  exact congrArg _ this

theorem ae_all_valid {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : (j : ℕ) → (Fin j → ℝ≥0) → Ω → Prop}
    (h : ∀ j t, IsValid j t → ∀ᵐ ω ∂P, p j t ω) : ∀ᵐ ω ∂P, ∀ j t, IsValid j t → p j t ω := by
  have h' : ∀ j, ∀ᵐ ω ∂P, ∀ tt : {t : Fin j → ℝ≥0 // IsValid j t}, p j tt.1 ω := fun j =>
    ae_all_iff.2 fun tt => h j tt.1 tt.2
  filter_upwards [ae_all_iff.2 h'] with ω hω j t hv
  exact hω j ⟨t, hv⟩

/-! ### The counterflow -/

/-- On a good hitting history the counterflow obstacle is closed and equals GLUECOND's hull. -/
theorem cfGood_of_mem_goodHitSet {y : HistorySpace 0 0} (hy : y ∈ goodHitSet) (r : ℝ≥0) : CfGood r y := by
  have hg : y ∈ CfRegQ.goodCfSet := hy.1
  have hc := (CfRegQ.reg_of_mem_goodCfSet hg).2.1
  have e : fwdHull (cfDrv0 r y) r = fwdHull (Prop411Q.cfDrv y) r :=
    YuanCorollary13.fwdHull_eq_of_eqOn_Icc (continuous_cfDrv0 r y) hc r.coe_nonneg fun s hs => cfDrv0_eq_cfDrv hg hs
  refine ⟨?_, ?_⟩
  · rw [e]; exact (isClosed_negInv_fwdHull_of_mem_goodHitSet hy r.coe_nonneg).1
  · rw [cfHullQ_eq_of_mem_goodCfSet hg, e]

section Setting

variable (h44 : Theorem12ParamCond44Statement.{u}) (hA : PartAInputsSixteenDiv)
  {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
  {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}
  {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
  {E : Schedule → ℕ → Ω → Driver}

/-- The field in the chart `Q` (PROVE-PROP513C's `targetField`). -/
def qField (x₀ κ : ℝ) (h : Ω → DistOn upperHalfPlaneOpens) : Ω → DistOn upperHalfPlaneOpens :=
  fun ω => targetField κ (Real.exp (π * x₀)) (Real.exp_pos _) (h ω)

omit [StandardBorelSpace Ω] in
include hA hκ hκ4 hb in
/-- **The counterflow history is a good hitting history** almost surely. -/
theorem ae_cfHistory_mem_goodHitSet (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)) :
    ∀ᵐ ω ∂P, Cond44Ref.cfHistory W ζ ω ∈ goodHitSet ∧ ζ ω = ⊤ ∧ Continuous (fun t => W t ω) := by
  have hreg := Prop513Wire.fig51_trace_mem_H_of_partA hA hκ hκ4 hb hG hcf
  have hcont := CrossRestart.ae_continuousOn_of_isStripCounterflowDriver hcf
  filter_upwards [hreg, hcont, htr] with ω hω hc' hγ
  have hζ := hω.1
  rw [hζ] at hγ hc'
  have hw : Continuous fun t => W t ω :=
    continuousOn_univ.1 (by simpa only [ENNReal.coe_lt_top, ofPred_true] using hc'.1)
  refine ⟨cfHistory_mem_goodHitSet hζ hw hc'.2 hγ fun t ht x _ he => ?_, hζ, hw⟩
  have hH := hω.2 _ hγ t ht
  rw [he] at hH
  exact lt_irrefl _ (show (0 : ℝ) < ((x : ℂ)).im from hH) |>.elim

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem measurable_cfHistory_of_strip (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) :
    Measurable (Cond44Ref.cfHistory W ζ) := by
  obtain ⟨_, _, _, _, _, _, 𝓕, VL, VR, B, _, hcpl⟩ := hcf
  exact Cond44Ref.measurable_cfHistory (Cond44Ref.isMeasurableKilledDriving_elim0 hcpl.2.2.2.1)

/-! ### The code pieces and the staged prefixes -/

variable (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
  (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
    (qField x₀ κ h) (scheduleSpec s) (E s))
  (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
    (scheduleSpec s) (E s))
include hG hE hR

/-- **The code pieces of every schedule are good paths** almost surely. -/
theorem ae_codeGood (s : Schedule) :
    ∀ᵐ ω ∂P, ∀ k < (scheduleList s).length,
      codeFam h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (qField x₀ κ h) s k ω ∈ goodPathSet := by
  set c := sourceWord (x₀ := x₀) hκ hb
  have hc : ExtremeHeights κ c := sourceWord_extreme hκ hb
  have hhQ := sourceWord_gff hκ hb hG
  have hF' := isStagedHistory_regHist c.isPiecewiseConstantBoundaryData (hE s) (hR s)
  have hr : ∀ j ω, IsRegularDriver (regHist (scheduleSpec s) (E s) j ω) := fun _ _ => isRegularDriver_regHist _ _
  filter_upwards [ae_schedule_goodPath h44 hκ hκ4 c hc hhQ s hF' hr,
    ae_schedule_drivers h44 hκ hκ4 c hc hhQ s hF' hr] with ω hg hd k hk
  have hk' : k < (scheduleSpec s).2.2.length := by
    simpa only [scheduleSpec, length_scheduleProgram] using hk
  have e : codeFam h44 hκ hκ4 c (qField x₀ κ h) s k ω = regHist (scheduleSpec s) (E s) k ω :=
    (hd k hk').2.symm
  rw [e]
  exact hg k hk'

/-- **Every actual staged prefix driver is the joined code driver** before its terminal time, almost surely. -/
theorem ae_prefixDriver_eq_joined :
    ∀ᵐ ω ∂P, ∀ s : Schedule, ∀ r : ℝ≥0, (r : ℝ≥0∞) < terminal s →
      prefixDriver E s ω r = joinedDriver (codeFam h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (qField x₀ κ h) s)
        0 0 (scheduleList s) ω r := by
  set c := sourceWord (x₀ := x₀) hκ hb
  have hc : ExtremeHeights κ c := sourceWord_extreme hκ hb
  have hhQ := sourceWord_gff hκ hb hG
  have hD : ∀ s, ∀ᵐ ω ∂P, ∀ j < (scheduleSpec s).2.2.length, (regHist (scheduleSpec s) (E s) j ω).2 = ⊤ ∧
      regHist (scheduleSpec s) (E s) j ω = codeDriver h44 hκ hκ4 c (scheduleSpec s) j (qField x₀ κ h ω) :=
    fun s => ae_schedule_drivers h44 hκ hκ4 c hc hhQ s
      (isStagedHistory_regHist c.isPiecewiseConstantBoundaryData (hE s) (hR s)) fun _ _ => isRegularDriver_regHist _ _
  filter_upwards [ae_all_iff.2 hD, ae_prefixDriver_regHist h44 hκ hκ4 c hc hhQ hE hR] with ω hd hpre s r hr
  rw [← congrFun (hpre s) r]
  have hF0 : ∀ k, (codeFam h44 hκ hκ4 c (qField x₀ κ h) s k ω).1 0 = 0 := fun k =>
    (codeDriver_regular h44 hκ hκ4 c _ k (qField x₀ κ h ω)).2.1
  have hr' : r ≤ lastTime 0 (scheduleList s) - 0 := by
    rw [tsub_zero, ← terminal_eq_lastTime]; exact (ENNReal.coe_lt_coe.1 hr).le
  have h1 := joinedDriver_prefix (E := fun j ω => regHist (scheduleSpec s) (E s) j ω)
    (F := codeFam h44 hκ hκ4 c (qField x₀ κ h) s) ω hF0 0 0 (scheduleList s) [] (timeOrdered_scheduleList s)
    (fun i _ hi => (hd s i (by simpa only [scheduleSpec, length_scheduleProgram, zero_add] using hi)).2) hr'
  rw [List.append_nil] at h1
  exact h1

/-- **The positions of the admissible candidate paths at rational times after their last switch are nodes.** -/
theorem ae_node_last :
    ∀ᵐ ω ∂P, ∀ j t, IsValid j t → ∀ u : ℚ, lastO j t < u →
      driverTree E (scheduleIndex (mkSched j t u)) ω (treeTime (scheduleIndex (mkSched j t u))) =
        qPath h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (qField x₀ κ h) j t ω u := by
  have hg := ae_all_valid (P := P) fun j t (_ : IsValid j t) =>
    ae_codeGood h44 hκ hκ4 hb hG hE hR (candSched j t)
  filter_upwards [hg, ae_prefixDriver_eq_joined h44 hκ hκ4 hb hG hE hR] with ω hgω hpω j t hv u hu
  exact driverTree_mkSched_eq_qPath h44 hκ hκ4 _ _ hv hu (hgω j t hv) (hpω (mkSched j t u))

/-- The node set of the tree in the chart `Q`. -/
def nodeSet (E : Schedule → ℕ → Ω → Driver) (ω : Ω) : Set ℂ := range fun n => driverTree E n ω (treeTime n)

/-- **The positions of the admissible candidate paths at positive rational times are nodes** (earlier times reduce
to ancestors by the prefix agreement `qPath_pfx`). -/
theorem ae_node :
    ∀ᵐ ω ∂P, ∀ j t, IsValid j t → ∀ q : ℚ, 0 < (q : ℝ) →
      qPath h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (qField x₀ κ h) j t ω q ∈ nodeSet E ω := by
  filter_upwards [ae_node_last h44 hκ hκ4 hb hG hE hR] with ω hω
  intro j
  induction j with
  | zero =>
    intro t hv q hq
    exact ⟨_, hω 0 t hv q (by exact_mod_cast hq)⟩
  | succ j ih =>
    intro t hv q hq
    by_cases hql : lastO (j + 1) t < q
    · exact ⟨_, hω (j + 1) t hv q hql⟩
    · have hle : (q : ℝ) ≤ qLast (j + 1) t := by
        rw [← lastO_eq hv]; exact_mod_cast not_lt.1 hql
      rw [qPath_pfx h44 hκ hκ4 _ _ hv ω hle]
      exact ih (Fin.init t) hv.init q hq

end Setting


/-! ### The root experiment -/

section Data

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{u}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens)
  (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) {nL₀ nR₀ : ℕ}

/-- **The good samples of the root experiment** at counterflow time `r`: the counterflow is good and every
admissible candidate path is a simple proper arc (the counterflow history is a good hitting history, the
counterflow lives forever with a continuous driver; the condition does not depend on the counterflow time). -/
def RootGood (_r : ℝ≥0) (ω : Ω) : Prop :=
  (Cond44Ref.cfHistory W ζ ω ∈ goodHitSet ∧ ζ ω = ⊤ ∧ Continuous (fun t => W t ω)) ∧ ∀ j t, IsValid j t →
    IsProperArc (qPath h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (qField x₀ κ h) j t ω)

/-- A measurable set of good samples (of full measure, `ae_mem_rootGood`). -/
def rootGood (r : ℝ≥0) : Set Ω := (toMeasurable P {ω | ¬ RootGood x₀ h44 hκ hκ4 hb h W ζ r ω})ᶜ

/-- **The tree data of the root experiment** at counterflow time `r`, with a dilation `lam`, root marks
`xL0`, `xR0` and noises: the canonical tree paths of the source word in the chart `Q` (`qPath`), the counterflow
history, and the admissible lists. -/
def rootData (r : ℝ≥0) (lam : Ω → ℝ) (xL0 : Ω → Fin nL₀ → ℝ) (xR0 : Ω → Fin nR₀ → ℝ)
    (noise : (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) : TreeData Ω nL₀ nR₀ where
  r := r
  y := Cond44Ref.cfHistory W ζ
  lam := lam
  G := rootGood x₀ h44 hκ hκ4 hb P h W ζ r
  α := fun j t => qPath h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (qField x₀ κ h) j t
  valid := IsValid
  xL0 := xL0
  xR0 := xR0
  noise := noise

variable {P h W ζ} {r : ℝ≥0} {lam : Ω → ℝ} {xL0 : Ω → Fin nL₀ → ℝ} {xR0 : Ω → Fin nR₀ → ℝ}
  {noise : (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ}

theorem rootGood_spec {ω : Ω} (hω : ω ∈ rootGood x₀ h44 hκ hκ4 hb P h W ζ r) :
    RootGood x₀ h44 hκ hκ4 hb h W ζ r ω := by
  by_contra hn
  exact hω (subset_toMeasurable _ _ hn)

/-- **The root tree data are regular.** -/
theorem isReg_rootData (hhm : Measurable h) (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (hlam : Measurable lam) (hpos : ∀ ω, 0 < lam ω) (hxL : Measurable xL0) (hxR : Measurable xR0) :
    (rootData x₀ h44 hκ hκ4 hb P h W ζ r lam xL0 xR0 noise).IsReg where
  y := measurable_cfHistory_of_strip hcf
  lam := hlam
  lam_pos := hpos
  G := (measurableSet_toMeasurable _ _).compl
  good _ hω := ⟨cfGood_of_mem_goodHitSet (rootGood_spec x₀ h44 hκ hκ4 hb hω).1.1 r,
    (rootGood_spec x₀ h44 hκ hκ4 hb hω).2⟩
  α j t u := measurable_qPath h44 hκ hκ4 _ _
    ((measurable_targetField κ (Real.exp (π * x₀)) (Real.exp_pos _)).comp hhm) j t u
  xL0 := hxL
  xR0 := hxR
  qrat j t hv := ⟨lastO j t, (lastO_eq hv).symm⟩

/-- **The root tree data form a tree**: admissible parents, later switches, and prefix agreement (`qPath_pfx`). -/
theorem isTree_rootData : (rootData x₀ h44 hκ hκ4 hb P h W ζ r lam xL0 xR0 noise).IsTree where
  init j t hv := ⟨hv.init, qLast_init_le hv, (hv.2 _).2.1⟩
  pfx j t hv ω u _ hu := qPath_pfx h44 hκ hκ4 _ _ hv ω hu
  qnonneg j t hv := by
    show 0 ≤ qLast j t
    rw [← lastO_eq hv]; exact_mod_cast lastO_nonneg hv

variable [StandardBorelSpace Ω] [IsProbabilityMeasure P] {γ : Ω → ℝ≥0 → ℂ} {E : Schedule → ℕ → Ω → Driver}

/-- **The good set has full measure.** -/
theorem ae_mem_rootGood (hA : PartAInputsSixteenDiv)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (qField x₀ κ h) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s)) :
    ∀ᵐ ω ∂P, ω ∈ rootGood x₀ h44 hκ hκ4 hb P h W ζ r := by
  have hg := ae_all_valid (P := P) fun j t (_ : IsValid j t) =>
    ae_codeGood h44 hκ hκ4 hb hG hE hR (candSched j t)
  have hae : ∀ᵐ ω ∂P, RootGood x₀ h44 hκ hκ4 hb h W ζ r ω := by
    filter_upwards [hg, ae_cfHistory_mem_goodHitSet hA hκ hκ4 hb hG hcf htr] with ω hgω hcω
    exact ⟨hcω, fun j t hv => (isProperArc_qPath_of h44 hκ hκ4 _ _ (hgω j t hv)).1⟩
  rw [ae_iff]
  have e : {ω | ¬ ω ∈ rootGood x₀ h44 hκ hκ4 hb P h W ζ r} =
      toMeasurable P {ω | ¬ RootGood x₀ h44 hκ hκ4 hb h W ζ r ω} := by
    ext ω; simp [rootGood]
  rw [e, measure_toMeasurable]
  exact ae_iff.1 hae

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **The concrete candidate pieces of the root experiment are regular** (`Prop59System.IsRegFam`). -/
theorem isRegFam_rootData (hhm : Measurable h) (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (hlam : Measurable lam) (hpos : ∀ ω, 0 < lam ω) (hxL : Measurable xL0) (hxR : Measurable xR0) :
    Prop59System.IsRegFam (rootData x₀ h44 hκ hκ4 hb P h W ζ r lam xL0 xR0 noise).cand :=
  (isReg_rootData x₀ h44 hκ hκ4 hb hhm hcf hlam hpos hxL hxR).isRegFam

/-- **The per-switch chain data of the concrete candidate pieces of the root experiment** (`IsChainFamEx`) with the
dilated joint-chart images of the tree nodes, for the recursive start. -/
theorem isChainFamEx_rootData (hhm : Measurable h)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (qField x₀ κ h) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s))
    (hlam : Measurable lam) (hpos : ∀ ω, 0 < lam ω) (hxL : Measurable xL0) (hxR : Measurable xR0)
    (hnL : 0 < nL₀) (hnR : 0 < nR₀) :
    IsChainFamEx P (rootData x₀ h44 hκ hκ4 hb P h W ζ r lam xL0 xR0 noise).cand hnL hnR
      ((rootData x₀ h44 hκ hκ4 hb P h W ζ r lam xL0 xR0 noise).image (nodeSet E))
      (recStart (rootData x₀ h44 hκ hκ4 hb P h W ζ r lam xL0 xR0 noise).cand) :=
  TreeData.isChainFamEx (isReg_rootData x₀ h44 hκ hκ4 hb hhm hcf hlam hpos hxL hxR) (isTree_rootData x₀ h44 hκ hκ4 hb)
    (ae_node h44 hκ hκ4 hb hG hE hR)

end Data

end InteractingSLE.Sec5.Prop59Pieces
