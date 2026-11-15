/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61MarksCode

/-!
# The aliveness events of the code in the completed rule marks (the other half of `code_le`)

Packet PROVE-AUX61-MARKS. For the selected-access restart code whose chart is read from the time-`0` record, whose
restarted path is the record's trace before the contact time `T`, and whose absolute contact time `t₀ + T` is a
measurable Galmarino rule `Ta` of the records (a first hit), the **aliveness event `{r' < life}` at every capacity time
`r' ≤ r` is, on the event `E`, almost surely the record event `AliveRec … r' r` of the record stopped at the glued stop
`capacityRule c t₀ r`**:

* `AliveRec c t₀ Ta V r' r p`: the rule at `r'` is at most the rule at `r`, finite and before the contact, and the
  record's chart path stays in a closed `δ`-interior of the window up to the rule at `r'` (countably many dyadic
  conditions); a measurable event of the record (`measurableSet_aliveRec`);
* alive at `r'` ⟹ `AliveRec` (`aliveRec_of_alive`: compactness of the chart path up to the code time inside the open
  window); `AliveRec` on the exit event ⟹ alive (`alive_of_aliveRec`: the window exit is after the rule at `r'`, while a
  code dead at `r'` has its rule after the exit, `exitNN_le_capacityRule_of_dead`);
* `AliveRec` only reads the record stopped at the glued stop of `r` (`aliveRec_stopRec`; Galmarino's property of the
  capacity rule and of the contact rule);
* hence the aliveness events are in the completed rule marks (`measurableSet_alive_nullRuleMarks`), and with the driver
  half (`Aux61MarksCode`) **`code_le` holds for the completed rule marks**
  (`codeFiltration_le_nullRuleMarks_of_record`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Marks

open Aux61ULoc LawUnique Restart.FlowStopIdentG Aux61FibData Aux61GInst Aux61Fib
open Aux61SlitW (prefixPoint capacityRule fullRecord readChart accessTime)

universe u

/-! ### The closed inner set of the window -/

/-- The points whose `δ`-ball lies in `V`. -/
def innerSet (V : Set ℂ) (δ : ℝ) : Set ℂ := {z | ball z δ ⊆ V}

theorem isClosed_innerSet (V : Set ℂ) (δ : ℝ) : IsClosed (innerSet V δ) := by
  refine isClosed_of_closure_subset fun z hz w hw => ?_
  have hε : 0 < δ - dist w z := sub_pos.2 hw
  obtain ⟨z', hz', hzz'⟩ := Metric.mem_closure_iff.1 hz _ hε
  refine hz' ?_
  calc dist w z' ≤ dist w z + dist z z' := dist_triangle _ _ _
    _ < dist w z + (δ - dist w z) := by linarith
    _ = δ := by ring

theorem innerSet_subset {V : Set ℂ} {δ : ℝ} (hδ : 0 < δ) : innerSet V δ ⊆ V := fun _ hz => hz (mem_ball_self hδ)

/-! ### The record aliveness event -/

section Record

variable {𝒴 : Type*} [MeasurableSpace 𝒴] {nL nR : ℕ}

/-- **The record aliveness event** at capacity time `r'` before the glued stop of `r`: the rule at `r'` is at most the
rule at `r`, before the contact rule `Ta`, finite, and the record's chart path stays in a closed inner set of the window
up to it. -/
def AliveRec (c : 𝒴 × HistorySpace nL nR → Chart) (t₀ : ℝ≥0) (Ta : 𝒴 × HistorySpace nL nR → ℝ≥0∞) (V : Set ℂ)
    (r' r : ℝ≥0) (p : 𝒴 × HistorySpace nL nR) : Prop :=
  capacityRule c t₀ r' p ≤ capacityRule c t₀ r p ∧ capacityRule c t₀ r' p < Ta p ∧ capacityRule c t₀ r' p < ⊤ ∧
    ∃ δ : ℚ, 0 < δ ∧ ∀ q : ℕ × ℕ, dyadicTime q ≤ recTime c t₀ r' p →
      prefixPoint c t₀ p.1 (fullRecord p.2) (dyadicTime q) ∈ innerSet V δ

theorem measurableSet_aliveRec {c : 𝒴 × HistorySpace nL nR → Chart} (hc : IsMeasChart c) (t₀ : ℝ≥0)
    {Ta : 𝒴 × HistorySpace nL nR → ℝ≥0∞} (hTa : Measurable Ta) (V : Set ℂ) (r' r : ℝ≥0) :
    MeasurableSet {p | AliveRec c t₀ Ta V r' r p} := by
  have h1 := Aux61SlitW.measurable_capacityRule hc t₀ r'
  have h2 := Aux61SlitW.measurable_capacityRule hc t₀ r
  have hD : MeasurableSet {p : 𝒴 × HistorySpace nL nR | ∃ δ : ℚ, 0 < δ ∧ ∀ q : ℕ × ℕ,
      dyadicTime q ≤ recTime c t₀ r' p → prefixPoint c t₀ p.1 (fullRecord p.2) (dyadicTime q) ∈ innerSet V δ} := by
    rw [ofPred_exists]
    refine MeasurableSet.iUnion fun δ => ?_
    rw [ofPred_and]
    refine (MeasurableSet.const _).inter ?_
    rw [ofPred_forall]
    refine MeasurableSet.iInter fun q => ?_
    have he : {p : 𝒴 × HistorySpace nL nR | dyadicTime q ≤ recTime c t₀ r' p →
        prefixPoint c t₀ p.1 (fullRecord p.2) (dyadicTime q) ∈ innerSet V δ} =
        {p | dyadicTime q ≤ recTime c t₀ r' p}ᶜ ∪
          {p | prefixPoint c t₀ p.1 (fullRecord p.2) (dyadicTime q) ∈ innerSet V δ} := by
      ext p
      simp only [mem_ofPred_eq, mem_union, mem_compl_iff]
      tauto
    rw [he]
    exact (measurableSet_le measurable_const (measurable_recTime hc t₀ r')).compl.union
      ((measurable_prefixPoint hc t₀ _) (isClosed_innerSet V δ).measurableSet)
  have he : {p | AliveRec c t₀ Ta V r' r p} =
      {p | capacityRule c t₀ r' p ≤ capacityRule c t₀ r p} ∩ ({p | capacityRule c t₀ r' p < Ta p} ∩
        ({p | capacityRule c t₀ r' p < ⊤} ∩ {p : 𝒴 × HistorySpace nL nR | ∃ δ : ℚ, 0 < δ ∧ ∀ q : ℕ × ℕ,
          dyadicTime q ≤ recTime c t₀ r' p →
            prefixPoint c t₀ p.1 (fullRecord p.2) (dyadicTime q) ∈ innerSet V δ})) := by
    ext p
    simp only [AliveRec, mem_ofPred_eq, mem_inter_iff]
  rw [he]
  exact (measurableSet_le h1 h2).inter ((measurableSet_lt h1 hTa).inter
    ((measurableSet_lt h1 measurable_const).inter hD))

omit [MeasurableSpace 𝒴] in
/-- A Galmarino rule is after a time `s ≤ t` for the record stopped at `t` iff it is for the record. -/
theorem lt_galmarino_stopRec_iff {Ta : 𝒴 × HistorySpace nL nR → ℝ≥0∞} (hG : IsGalmarinoRule stopRec Ta)
    {y : 𝒴} {g : HistorySpace nL nR} {t : ℝ≥0} {s : ℝ≥0∞} (hs : s ≤ t) :
    s < Ta (y, stopRec t g) ↔ s < Ta (y, g) := by
  constructor
  · intro h
    by_cases h' : Ta (y, stopRec t g) ≤ t
    · rwa [← hG y g t (Or.inl h')]
    · by_contra h''
      have hle : Ta (y, g) ≤ t := (not_lt.1 h'').trans hs
      exact h' (by rw [hG y g t (Or.inr hle)]; exact hle)
  · intro h
    by_cases h' : Ta (y, g) ≤ t
    · rwa [hG y g t (Or.inr h')]
    · by_contra h''
      have hle : Ta (y, stopRec t g) ≤ t := (not_lt.1 h'').trans hs
      exact h' (by rw [← hG y g t (Or.inl hle)]; exact hle)

/-- **The record aliveness event only reads the record stopped at the glued stop of `r`.** -/
theorem aliveRec_stopRec {c : 𝒴 × HistorySpace nL nR → Chart} {t₀ : ℝ≥0} {Ta : 𝒴 × HistorySpace nL nR → ℝ≥0∞}
    (hTaG : IsGalmarinoRule stopRec Ta) {V : Set ℂ} {r' r : ℝ≥0} {y : 𝒴} {g : HistorySpace nL nR}
    (htop : capacityRule c t₀ r (y, g) < ⊤) :
    AliveRec c t₀ Ta V r' r (y, stopRec (capacityRule c t₀ r (y, g)).toNNReal g) ↔ AliveRec c t₀ Ta V r' r (y, g) := by
  set t := (capacityRule c t₀ r (y, g)).toNNReal with htdef
  have ht : capacityRule c t₀ r (y, g) = t := (ENNReal.coe_toNNReal htop.ne).symm
  have hr : capacityRule c t₀ r (y, stopRec t g) = capacityRule c t₀ r (y, g) :=
    Aux61SlitW.isGalmarinoRule_capacityRule c t₀ r y g t (Or.inr ht.le)
  -- under the ordering, the rule at `r'` agrees and so do the path conditions
  have key : ∀ (_ : capacityRule c t₀ r' (y, g) ≤ t),
      capacityRule c t₀ r' (y, stopRec t g) = capacityRule c t₀ r' (y, g) → (AliveRec c t₀ Ta V r' r (y, stopRec t g) ↔
        AliveRec c t₀ Ta V r' r (y, g)) := by
    intro hle he
    have hT : recTime c t₀ r' (y, stopRec t g) = recTime c t₀ r' (y, g) := by
      simp only [recTime, he]
    have hfin : capacityRule c t₀ r' (y, g) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hle
    have hst : (t₀ : ℝ≥0∞) ≤ capacityRule c t₀ r' (y, g) := Aux61SlitW.start_le_capacityRule c t₀ r' (y, g)
    have hpt : ∀ q : ℕ × ℕ, dyadicTime q ≤ recTime c t₀ r' (y, g) →
        prefixPoint c t₀ y (fullRecord (stopRec t g)) (dyadicTime q) =
          prefixPoint c t₀ y (fullRecord g) (dyadicTime q) := by
      intro q hq
      refine prefixPoint_stopRec ?_
      have hle' : (capacityRule c t₀ r' (y, g)).toNNReal ≤ t := by
        rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfin]
        exact hle
      have ht₀ : t₀ ≤ (capacityRule c t₀ r' (y, g)).toNNReal := by
        rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfin]
        exact hst
      unfold recTime at hq
      calc t₀ + dyadicTime q ≤ t₀ + ((capacityRule c t₀ r' (y, g)).toNNReal - t₀) := (add_le_add_iff_left t₀).2 hq
        _ = (capacityRule c t₀ r' (y, g)).toNNReal := add_tsub_cancel_of_le ht₀
        _ ≤ t := hle'
    have hTa : capacityRule c t₀ r' (y, g) < Ta (y, stopRec t g) ↔ capacityRule c t₀ r' (y, g) < Ta (y, g) :=
      lt_galmarino_stopRec_iff hTaG hle
    simp only [AliveRec, he, hr, hT, hTa]
    refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (exists_congr fun δ => and_congr Iff.rfl
      (forall_congr' fun q => imp_congr_right fun hq => ?_))))
    rw [hpt q hq]
  constructor
  · intro hA
    have hle : capacityRule c t₀ r' (y, stopRec t g) ≤ t := by
      rw [← ht, ← hr]
      exact hA.1
    have he : capacityRule c t₀ r' (y, stopRec t g) = capacityRule c t₀ r' (y, g) :=
      Aux61SlitW.isGalmarinoRule_capacityRule c t₀ r' y g t (Or.inl hle)
    exact (key (he ▸ hle) he).1 hA
  · intro hA
    have hle : capacityRule c t₀ r' (y, g) ≤ t := ht ▸ hA.1
    have he : capacityRule c t₀ r' (y, stopRec t g) = capacityRule c t₀ r' (y, g) :=
      Aux61SlitW.isGalmarinoRule_capacityRule c t₀ r' y g t (Or.inr hle)
    exact (key hle he).2 hA

end Record

/-! ### Aliveness of the code and the record aliveness event -/

section Access

variable {X : Type*} [MeasurableSpace X] {E : Set X} {cc : X → Chart}
  {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ}
  (hs : IsRestartSpec E cc ρ T) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
  (hland : HasAccessLanding E cc ρ T V)
  (hinj : ∀ x ∈ E, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x})
  {a k : ℝ} {h : X → LQGMetric.DistOn upperHalfPlaneOpens}
  {𝒴 : Type*} [MeasurableSpace 𝒴] {nL nR : ℕ}
  {c : 𝒴 × HistorySpace nL nR → Chart} {t₀ : ℝ≥0} {Ta : 𝒴 × HistorySpace nL nR → ℝ≥0∞} {y : 𝒴}
  {g : HistorySpace nL nR} {x : X} (hchart : cc x = c (y, stopRec t₀ g))
  (hρ : ∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < T x → ρ x u = histTrace 0 g (t₀ + u))
  (hTa : Ta (y, g) = (t₀ : ℝ≥0∞) + T x)
include hs hV hV0 hland hinj hchart hρ

omit [MeasurableSpace 𝒴] hV hV0 hland hinj in
/-- Before the contact time the record's chart point is the chart image of the restarted path. -/
theorem prefixPoint_eq_inPath (hxE : x ∈ E) (hT0 : 0 < T x) {u : ℝ≥0} (huT : (u : ℝ≥0∞) < T x) :
    prefixPoint c t₀ y (fullRecord g) u = inPath E cc ρ T x u := by
  rcases eq_or_ne u 0 with rfl | hu0
  · rw [hs.inPath_zero hxE hT0]
    simp only [prefixPoint, ↓reduceIte]
  · have hu : 0 < u := pos_iff_ne_zero.2 hu0
    rw [prefixPoint, ite_eq_right hu0, Aux61SlitW.stopRec_fullRecord, Aux61SlitW.histTrace_fullRecord, ← hchart,
      ← hρ u hu huT, Aux61SlitW.readChart_eq (hs.conf x hxE) (hs.inside x hxE u hu huT),
      hs.inPath_eq_fwd hxE hu huT]

omit [MeasurableSpace X] hs hV hV0 hland hinj [MeasurableSpace 𝒴] hchart in
/-- SLITW's path clause (before the exit) from the path clause before the contact. -/
theorem hρ_exit (hx : x ∈ exitEv E cc ρ T V) :
    ∀ u : ℝ≥0, 0 < u → u < exitNN E cc ρ T V x → ρ x u = histTrace 0 g (t₀ + u) := by
  intro u hu hue
  refine hρ u hu (lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hue) ?_)
  rw [IsRestartSpec.coe_exitNN hx]
  exact IsRestartSpec.exitTime_le x

/-- **Alive at `r'` ⟹ the record aliveness event.** -/
theorem aliveRec_of_alive (hTa : Ta (y, g) = (t₀ : ℝ≥0∞) + T x) {r' r : ℝ≥0}
    (hr' : (r' : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life) (hrr : r' ≤ r) :
    AliveRec c t₀ Ta V r' r (y, g) := by
  have hx := mem_exitEv_of_lt_accessLife hr'
  have hρe := hρ_exit hρ hx
  set A := accessTime (E := E) (c := cc) (ρ := ρ) (T := T) (V := V) x r' with hAdef
  have hAe : A < exitNN E cc ρ T V x := (Aux61SlitW.accessTime_spec hs hV hV0 hland hinj hr').1
  have heT : ((exitNN E cc ρ T V x : ℝ≥0) : ℝ≥0∞) ≤ T x := by
    rw [IsRestartSpec.coe_exitNN hx]
    exact IsRestartSpec.exitTime_le x
  have hcap : capacityRule c t₀ r' (y, g) = ((t₀ + A : ℝ≥0) : ℝ≥0∞) := by
    rcases eq_or_ne r' 0 with rfl | hr0
    · rw [Aux61SlitW.capacityRule_zero, hAdef, Aux61SlitW.accessTime_zero hs hV hV0 hland hinj hr', add_zero]
    · exact Aux61SlitW.capacityRule_eq_accessTime hs hV hV0 hland hinj hchart hρe (pos_iff_ne_zero.2 hr0) hr'
  refine ⟨le_capacityRule_of_alive hs hV hV0 hland hinj hchart hρe hr' hrr le_rfl, ?_, ?_, ?_⟩
  · rw [hcap, hTa, ENNReal.coe_add]
    exact ENNReal.add_lt_add_left ENNReal.coe_ne_top (lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hAe) heT)
  · rw [hcap]
    exact ENNReal.coe_lt_top
  · -- the chart path up to the code time is a compact subset of the open window
    have hxE : x ∈ E := hx.1.1
    have hsub : Icc (0 : ℝ≥0) A ⊆ {u : ℝ≥0 | (u : ℝ≥0∞) < T x} := fun u hu =>
      lt_of_lt_of_le (ENNReal.coe_lt_coe.2 (lt_of_le_of_lt hu.2 hAe)) heT
    have hK : IsCompact (inPath E cc ρ T x '' Icc 0 A) :=
      isCompact_Icc.image_of_continuousOn ((hs.continuousOn_inPath hxE).mono hsub)
    have hKV : inPath E cc ρ T x '' Icc 0 A ⊆ V := by
      rintro _ ⟨u, hu, rfl⟩
      refine (IsRestartSpec.lt_exitTime ?_).2
      rw [← IsRestartSpec.coe_exitNN hx]
      exact ENNReal.coe_lt_coe.2 (lt_of_le_of_lt hu.2 hAe)
    obtain ⟨δ₀, hδ₀, hthick⟩ := hK.exists_thickening_subset_open hV hKV
    obtain ⟨δ, hδ, hδδ⟩ := exists_rat_btwn hδ₀
    refine ⟨δ, by exact_mod_cast hδ, fun q hq => ?_⟩
    rw [recTime_eq_accessTime hs hV hV0 hland hinj hchart hρe hr'] at hq
    have hqe : dyadicTime q < exitNN E cc ρ T V x := lt_of_le_of_lt hq hAe
    rw [Aux61SlitW.prefixPoint_eq_accessPath hs hV hV0 hland hx hchart hρe hqe]
    have hpath : accessExitPath E cc ρ T V x (dyadicTime q) = inPath E cc ρ T x (dyadicTime q) := by
      simp only [accessExitPath, hx, ↓reduceIte, hqe]
    rw [hpath]
    intro w hw
    refine hthick (Metric.ball_subset_thickening (mem_image_of_mem _
      (show dyadicTime q ∈ Icc (0 : ℝ≥0) A from ⟨zero_le, hq⟩)) δ₀ ?_)
    exact Metric.ball_subset_ball hδδ.le hw

/-- **The record aliveness event on the exit event ⟹ alive at `r'`.** -/
theorem alive_of_aliveRec (hTa : Ta (y, g) = (t₀ : ℝ≥0∞) + T x) {r' r : ℝ≥0}
    (hx : x ∈ exitEv E cc ρ T V) (hA : AliveRec c t₀ Ta V r' r (y, g)) :
    (r' : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life := by
  have hρe := hρ_exit hρ hx
  have hxE : x ∈ E := hx.1.1
  have hT0 : 0 < T x := hx.1.2
  obtain ⟨-, hTa', htop, δ, hδ, hpath⟩ := hA
  set s := capacityRule c t₀ r' (y, g) with hsdef
  set τ := recTime c t₀ r' (y, g) with hτdef
  have hst : (t₀ : ℝ≥0∞) ≤ s := Aux61SlitW.start_le_capacityRule c t₀ r' (y, g)
  have hs' : s = ((t₀ + τ : ℝ≥0) : ℝ≥0∞) := by
    rw [hτdef, recTime, ← hsdef, add_tsub_cancel_of_le, ENNReal.coe_toNNReal htop.ne]
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal htop.ne]
    exact hst
  have hτT : (τ : ℝ≥0∞) < T x := by
    rw [hs', hTa, ENNReal.coe_add] at hTa'
    exact (ENNReal.add_lt_add_iff_left ENNReal.coe_ne_top).1 hTa'
  -- the chart path stays in the inner set up to `τ`
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hin : ∀ v : ℝ≥0, v ≤ τ → inPath E cc ρ T x v ∈ innerSet V δ := by
    intro v hv
    have hvT : (v : ℝ≥0∞) < T x := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hv) hτT
    have hcont : ContinuousAt (inPath E cc ρ T x) v :=
      (hs.continuousOn_inPath hxE).continuousAt
        ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds hvT)
    refine (isClosed_innerSet V δ).mem_of_tendsto (hcont.tendsto.comp (tendsto_dyadicTime_lowerDyadic v))
      (Eventually.of_forall fun n => ?_)
    have hd : dyadicTime (lowerDyadic v n) ≤ τ := (dyadicTime_lowerDyadic_le v n).trans hv
    have hdT : (dyadicTime (lowerDyadic v n) : ℝ≥0∞) < T x :=
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 hd) hτT
    show inPath E cc ρ T x (dyadicTime (lowerDyadic v n)) ∈ innerSet V δ
    rw [← prefixPoint_eq_inPath hs hchart hρ hxE hT0 hdT]
    exact hpath _ hd
  have hlt : (τ : ℝ≥0∞) < Aux61FibData.exitTime E cc ρ T V x := by
    refine IsRestartSpec.lt_exitTime_of hxE (fun v hv => innerSet_subset hδ' (hin v hv.le)) ?_
    exact hs.eventually_mem_of_lt hxE hV hτT (innerSet_subset hδ' (hin τ le_rfl))
  by_contra hdead
  have hd := exitNN_le_capacityRule_of_dead hs hV hV0 hland hinj hchart hρe hx (not_lt.1 hdead)
  rw [← hsdef, hs'] at hd
  have hd' : exitNN E cc ρ T V x ≤ τ := by
    have := ENNReal.coe_le_coe.1 hd
    exact (add_le_add_iff_left t₀).1 this
  rw [← IsRestartSpec.coe_exitNN hx] at hlt
  exact absurd (ENNReal.coe_lt_coe.1 hlt) (not_lt.2 hd')

end Access

/-! ### The aliveness events and `code_le` in the completed rule marks -/

section Marks

/-- Before the window exit (as a finite time) the path is before the contact time. -/
theorem lt_T_of_lt_exitNN {X : Type*} {E : Set X} {cc : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞}
    {V : Set ℂ} {x : X} {u : ℝ≥0} (hu : u < exitNN E cc ρ T V x) : (u : ℝ≥0∞) < T x := by
  have hle : Aux61FibData.exitTime E cc ρ T V x ≤ T x := IsRestartSpec.exitTime_le x
  by_cases htop : Aux61FibData.exitTime E cc ρ T V x = ⊤
  · have h0 : exitNN E cc ρ T V x = 0 := by simp only [exitNN, htop, ENNReal.toNNReal_top]
    exact absurd hu (by rw [h0]; exact not_lt.2 zero_le)
  · refine lt_of_lt_of_le ?_ hle
    rw [← ENNReal.coe_toNNReal htop]
    exact ENNReal.coe_lt_coe.2 hu

variable {X : Type u} [mX : MeasurableSpace X] {E : Set X} {cc : X → Chart}
  {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ}
  (hs : IsRestartSpec E cc ρ T) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
  (hland : HasAccessLanding E cc ρ T V)
  (hinj : ∀ x ∈ E, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x})
  {a k : ℝ} {h : X → LQGMetric.DistOn upperHalfPlaneOpens}
  {𝒴 : Type*} [MeasurableSpace 𝒴] {nL nR : ℕ}
  {c : 𝒴 × HistorySpace nL nR → Chart} {t₀ : ℝ≥0} {Ta : 𝒴 × HistorySpace nL nR → ℝ≥0∞}
  {Y₀ : X → 𝒴} {R₀ : X → HistorySpace nL nR} {μ : Measure X}
include hs hV hV0 hland hinj

/-- **The aliveness events are in the completed rule marks.** When the chart is read from the time-`0` record, the
restarted path is the record's trace before the contact, the absolute contact time is a measurable Galmarino rule `Ta`
of the records, the event is in the completed marks and almost surely exits on it: for every `r' ≤ r`,
`{r' < life}` is in the null completion of the rule marks of the glued stop `capacityRule c t₀ r`. -/
theorem measurableSet_alive_nullRuleMarks (hc : IsMeasChart c) (hTam : Measurable Ta)
    (hTaG : IsGalmarinoRule stopRec Ta) (hliftc : ∀ x ∈ E, ContinuousOn (cc x).2.2 (cc x).dom)
    (hh : Measurable h) {r r' : ℝ≥0} (hrr : r' ≤ r)
    (hE : MeasurableSet[nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ] E)
    (hrec : ∀ᵐ x ∂μ, cc x = c (Y₀ x, stopRec t₀ (R₀ x)) ∧
      (∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < T x → ρ x u = histTrace 0 (R₀ x) (t₀ + u)) ∧
      Ta (Y₀ x, R₀ x) = (t₀ : ℝ≥0∞) + T x)
    (hexit : ∀ᵐ x ∂μ, x ∈ E → x ∈ exitEv E cc ρ T V) :
    MeasurableSet[nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ]
      {x | ((r' : ℝ≥0) : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life} := by
  have hY := measurable_accessExitCode hs hV hV0 hland hinj hliftc hh (a := a) (k := k)
  obtain ⟨-, E', hE', hEe⟩ := hE
  have hA : MeasurableSet[ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀]
      {x | AliveRec c t₀ Ta V r' r (Y₀ x, stopAt stopRec (capacityRule c t₀ r (Y₀ x, R₀ x)) (R₀ x))} :=
    (measurable_ruleMarks_of_factor (stop := stopRec) (ρ := capacityRule c t₀ r) (Y₀ := Y₀) (R₀ := R₀)
      measurable_id) (measurableSet_aliveRec hc t₀ hTam V r' r)
  refine measurableSet_nullMarks_of_ae_eq
    (measurableSet_lt measurable_const (FibCode.measurable_life.comp hY)) (hE'.inter hA) ?_
  filter_upwards [hEe, hrec, hexit] with x hxE' hx hexx
  obtain ⟨hch, hρx, hTax⟩ := hx
  have hxE : (x ∈ E) = (x ∈ E') := hxE'
  -- stopping at the glued stop does not change the record aliveness event
  have hstop : AliveRec c t₀ Ta V r' r (Y₀ x, stopAt stopRec (capacityRule c t₀ r (Y₀ x, R₀ x)) (R₀ x)) ↔
      AliveRec c t₀ Ta V r' r (Y₀ x, R₀ x) := by
    by_cases htop : capacityRule c t₀ r (Y₀ x, R₀ x) < ⊤
    · simp only [stopAt, htop, ↓reduceIte]
      exact aliveRec_stopRec hTaG htop
    · simp only [stopAt, htop, ↓reduceIte]
  refine propext ⟨fun halive => ⟨?_, ?_⟩, fun hJ => ?_⟩
  · have hxe := mem_exitEv_of_lt_accessLife halive
    exact hxE ▸ hxe.1.1
  · exact hstop.2 (aliveRec_of_alive hs hV hV0 hland hinj hch hρx hTax halive hrr)
  · have hxe : x ∈ E := hxE ▸ hJ.1
    exact alive_of_aliveRec hs hV hV0 hland hinj hch hρx hTax (hexx hxe) (hstop.1 hJ.2)

/-- **`code_le` for the completed rule marks** (the field `code_le` of `Aux61Marks.MarksFacts` for
`baseMarks i r := nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ`): from the record reading of the chart,
the restarted path and the contact time, the event in the completed marks, and the a.s. exit on the event. -/
theorem codeFiltration_le_nullRuleMarks_of_record (hc : IsMeasChart c) (hTam : Measurable Ta)
    (hTaG : IsGalmarinoRule stopRec Ta) (hliftc : ∀ x ∈ E, ContinuousOn (cc x).2.2 (cc x).dom)
    (hh : Measurable h) (d : FibData) (hdV : d.V = V) (hℓ : d.ℓ = clr V) (r : ℝ≥0)
    (hE : MeasurableSet[nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ] E)
    (hrec : ∀ᵐ x ∂μ, cc x = c (Y₀ x, stopRec t₀ (R₀ x)) ∧
      (∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < T x → ρ x u = histTrace 0 (R₀ x) (t₀ + u)) ∧
      Ta (Y₀ x, R₀ x) = (t₀ : ℝ≥0∞) + T x)
    (hexit : ∀ᵐ x ∂μ, x ∈ E → x ∈ exitEv E cc ρ T V) :
    (Aux61FibK.codeFiltration.{u} r).comap (fun x => ULift.up.{u} (accessExitCode E cc ρ T V a k h x)) ≤
      nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ := by
  have hrec' : ∀ᵐ x ∂μ, cc x = c (Y₀ x, stopRec t₀ (R₀ x)) ∧
      ∀ u : ℝ≥0, 0 < u → u < exitNN E cc ρ T V x → ρ x u = histTrace 0 (R₀ x) (t₀ + u) := by
    filter_upwards [hrec] with x hx
    exact ⟨hx.1, fun u hu hue => hx.2.1 u hu (lt_T_of_lt_exitNN hue)⟩
  exact codeFiltration_le_nullRuleMarks hs hV hV0 hland hinj hc d hdV hℓ hliftc hh r hrec'
    fun r' hr' => measurableSet_alive_nullRuleMarks hs hV hV0 hland hinj hc hTam hTaG hliftc hh hr' hE hrec hexit

end Marks

end InteractingSLE.Sec5.Aux61Marks
