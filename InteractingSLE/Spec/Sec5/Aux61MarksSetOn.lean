/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61MarksSet
import InteractingSLE.Spec.Sec5.Aux61MarksCodeOn
import InteractingSLE.Spec.Sec5.Aux61RestartMarkChart
import InteractingSLE.Spec.Sec5.Aux61RestartPrepDist

/-!
# `baseSets_marks` with the path reading almost surely, and R1's record chart

Packet PROVE-AUX61-MARKS. The `baseSets_marks` theorem of `Aux61MarksSet` takes the record reading of the restarted
path at every live sample. The concrete restarted path is the record's trace only almost surely, so:

* `measurable_nullMarks_of_ae_eq_nullMarks`: an ambient-measurable function almost everywhere equal to a function
  measurable for a null completion is measurable for it;
* `measurableSet_mem_chartHull`, `exists_slitAvoid_ambient`, **`measurable_markedSet_ambient`**: the marked set is
  hitting-measurable for the ambient σ-algebra (no record reading needed);
* **`measurable_markedSet_nullRuleMarks_on`**: `baseSets_marks` with the path reading almost surely on the live set;
* R1's chart (`Aux61Restart.HasOriginalTargetRestartChart`): **its domain is the component of its retained domain**
  and it is a measurable chart (`exists_isMeasChart_of_hasOriginalTargetRestartChart`); **the counterflow history hull
  of the records is hitting-measurable** (`measurable_historyHull_fst`);
* **`measurable_liveSet_nullRuleMarks_of_source`**: `baseSets_marks` for the concrete source form (the live set of the
  time-`0` record event at the alive code, the chart read from the time-`0` record with domain the component of a
  retained domain of a hitting-measurable record obstacle and the record's own prefix).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Marks

open Aux61ULoc LawUnique Restart.FlowStopIdentG Aux61FibData Aux61GInst Aux61Fib LocalSets
open Aux61UnionK (chartHull)
open Aux61SlitW (accessTime capacityRule)

/-! ### Null completions and almost-everywhere equality -/

/-- An ambient-measurable function almost everywhere equal to a function measurable for a null completion is
measurable for the null completion. -/
theorem measurable_nullMarks_of_ae_eq_nullMarks {X β : Type*} {ℋ : MeasurableSpace X} [mX : MeasurableSpace X]
    {μ : Measure X} (mβ : MeasurableSpace β) {f g : X → β} (hf : Measurable[mX, mβ] f)
    (hg : Measurable[nullMarks ℋ μ, mβ] g) (hfg : f =ᵐ[μ] g) : Measurable[nullMarks ℋ μ, mβ] f := by
  intro S hS
  obtain ⟨-, J, hJ, hgJ⟩ := hg hS
  exact ⟨hf hS, J, hJ, (hfg.preimage S).trans hgJ⟩

/-! ### The marked set for the ambient σ-algebra -/

section Ambient

variable {X : Type*} [mX : MeasurableSpace X] {E : Set X} {cc : X → Chart}
  {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ}
  (hs : IsRestartSpec E cc ρ T) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
  (hland : HasAccessLanding E cc ρ T V)
  (hinj : ∀ x ∈ E, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x})
  {a k : ℝ} {h : X → LQGMetric.DistOn upperHalfPlaneOpens}
include hs hV hV0 hland hinj

/-- Membership of a measurable random point in the chart hull of the code is measurable. -/
theorem measurableSet_mem_chartHull (hliftc : ∀ x ∈ E, ContinuousOn (cc x).2.2 (cc x).dom) (hh : Measurable h)
    (r : ℝ≥0) {w : X → ℂ} (hw : Measurable w) :
    MeasurableSet {x | w x ∈ chartHull (accessExitCode E cc ρ T V a k h) r x} := by
  have hY := measurable_accessExitCode hs hV hV0 hland hinj hliftc hh (a := a) (k := k)
  have hZ := QuantumZipper.NonSwallow.measurableSet_fwdHull_prod
    (B := fun t x => FibCode.driver (min t r) (accessExitCode E cc ρ T V a k h x))
    (fun t => (FibCode.measurable_driver _).comp hY)
    (fun x => (FibCode.continuous_driver _).comp (continuous_id.min continuous_const)) 1 (NNReal.coe_nonneg r)
  have hhull : ∀ x, fwdHull (QuantumZipper.drive 1
      (fun t x => FibCode.driver (min t r) (accessExitCode E cc ρ T V a k h x)) x) (r : ℝ) =
      chartHull (accessExitCode E cc ρ T V a k h) r x := by
    intro x
    unfold chartHull
    refine YuanCorollary13.fwdHull_eq_of_eqOn_Icc ?_ ?_ (NNReal.coe_nonneg r) fun t ht => ?_
    · exact continuous_const.mul (((FibCode.continuous_driver _).comp
        (continuous_id.min continuous_const)).comp continuous_real_toNNReal)
    · exact (FibCode.continuous_driver _).comp continuous_real_toNNReal
    · simp only [QuantumZipper.drive, Real.sqrt_one, one_mul]
      congr 1
      exact min_eq_left (Real.toNNReal_le_iff_le_coe.2 ht.2)
  have e : {x | w x ∈ chartHull (accessExitCode E cc ρ T V a k h) r x} = (fun x => (w x, x)) ⁻¹'
      {p : ℂ × X | p.1 ∈ fwdHull (QuantumZipper.drive 1
        (fun t x => FibCode.driver (min t r) (accessExitCode E cc ρ T V a k h x)) p.2) r} := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, hhull]
  rw [e]
  exact (hw.prodMk measurable_id) hZ

omit hinj in
/-- The slit-avoidance events for the ambient σ-algebra. -/
theorem exists_slitAvoid_ambient (r : ℝ≥0) {G : Set X}
    (hG : ∀ x ∈ G, (r : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life) (p : ℚ × ℚ × ℚ) :
    ∃ S' : Set X, MeasurableSet S' ∧ ∀ x ∈ G,
      (Disjoint (ratBall p) (ρ x '' Ioc 0 (accessTime (E := E) (c := cc) (ρ := ρ) (T := T) (V := V) x r)) ↔
        x ∈ S') := by
  have hA : Measurable fun x => accessTime (E := E) (c := cc) (ρ := ρ) (T := T) (V := V) x r :=
    (isPathSpec_accessExitPath hs hV hV0 hland).measurable_invClock r
  refine ⟨⋂ q : ℕ × ℕ, {x | 0 < dyadicTime q ∧
      dyadicTime q < accessTime (E := E) (c := cc) (ρ := ρ) (T := T) (V := V) x r}ᶜ ∪
      {x | ρ x (dyadicTime q) ∉ ratBall p}, ?_, fun x hx => ?_⟩
  · refine MeasurableSet.iInter fun q => (((MeasurableSet.const _).inter
      (measurableSet_lt measurable_const hA)).compl).union ?_
    exact ((hs.measρ _) (isOpen_ratBall p).measurableSet).compl
  · have hxE : x ∈ E := (mem_exitEv_of_lt_accessLife (hG x hx)).1.1
    rw [disjoint_image_Ioc_iff (hs.contρ x hxE) (isOpen_ratBall p)]
    simp only [mem_iInter, mem_union, mem_compl_iff, mem_ofPred_eq]
    refine forall_congr' fun q => ⟨fun hq => ?_, fun hq hq0 hqA => ?_⟩
    · by_cases hc' : 0 < dyadicTime q ∧
          dyadicTime q < accessTime (E := E) (c := cc) (ρ := ρ) (T := T) (V := V) x r
      · exact Or.inr (hq hc'.1 hc'.2)
      · exact Or.inl hc'
    · rcases hq with hq | hq
      · exact absurd ⟨hq0, hqA⟩ hq
      · exact hq

open scoped Classical in
/-- **The marked set is hitting-measurable for the ambient σ-algebra**, on a measurable set of samples alive at `r`
with R1's chart (domain a component of `R x`), once the events "a rational ball lies in `R x`" are measurable on it. -/
theorem measurable_markedSet_ambient (d : FibData) (hdV : d.V = V) (hℓ : d.ℓ = clr V)
    (hliftc : ∀ x ∈ E, ContinuousOn (cc x).2.2 (cc x).dom) (hh : Measurable h) {r : ℝ≥0}
    {G : Set X} (hGm : MeasurableSet G) {R : X → Set ℂ} {b : X → ℂ}
    (hG : ∀ x ∈ G, (r : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life ∧
      ((cc x).dom : Set ℂ) = connectedComponentIn (R x) (b x))
    (hR : ∀ p : ℚ × ℚ × ℚ, ∃ R' : Set X, MeasurableSet R' ∧ ∀ x ∈ G, (ratBall p ⊆ R x ↔ x ∈ R')) :
    Measurable[mX, hittingSigma]
      (G.piecewise (fun x => chartSet (cc x) (chartHull (accessExitCode E cc ρ T V a k h) r x)) fun _ => H) :=
  measurable_markedSet hs hV hV0 hland hinj d hdV hℓ hGm hG hs.chart
    (fun _ hw => ⟨_, measurableSet_mem_chartHull hs hV hV0 hland hinj hliftc hh r hw, fun _ _ => Iff.rfl⟩) hR
    (exists_slitAvoid_ambient hs hV hV0 hland r fun x hx => (hG x hx).1)

end Ambient

/-! ### `baseSets_marks` with the path reading almost surely -/

section AE

variable {X : Type*} [mX : MeasurableSpace X] {E : Set X} {cc : X → Chart}
  {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ}
  (hs : IsRestartSpec E cc ρ T) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
  (hland : HasAccessLanding E cc ρ T V)
  (hinj : ∀ x ∈ E, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x})
  {a k : ℝ} {h : X → LQGMetric.DistOn upperHalfPlaneOpens}
  {𝒴 : Type*} [MeasurableSpace 𝒴] {nL nR : ℕ}
  {c : 𝒴 × HistorySpace nL nR → Chart} {t₀ : ℝ≥0} {Y₀ : X → 𝒴} {R₀ : X → HistorySpace nL nR}
  {μ : Measure X}
include hs hV hV0 hland hinj

open scoped Classical in
/-- **`baseSets_marks` for the completed rule marks, with the record reading of the restarted path almost surely on
the live set**: as `measurable_markedSet_nullRuleMarks`, the path clause being required only almost surely. -/
theorem measurable_markedSet_nullRuleMarks_on (d : FibData) (hdV : d.V = V) (hℓ : d.ℓ = clr V)
    (hc : IsMeasChart c) (hliftc : ∀ x ∈ E, ContinuousOn (cc x).2.2 (cc x).dom) (hh : Measurable h)
    (hY₀ : Measurable Y₀) (hR₀ : Measurable R₀) {r : ℝ≥0} {G : Set X}
    (hGm : MeasurableSet[nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ] G) {R : X → Set ℂ} {b : X → ℂ}
    (hG : ∀ x ∈ G, (r : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life ∧ cc x = c (Y₀ x, stopRec t₀ (R₀ x)) ∧
      ((cc x).dom : Set ℂ) = connectedComponentIn (R x) (b x))
    (hpath : ∀ᵐ x ∂μ, x ∈ G →
      ∀ u : ℝ≥0, 0 < u → u < exitNN E cc ρ T V x → ρ x u = histTrace 0 (R₀ x) (t₀ + u))
    (hcm : @IsMeasChart X (nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ) cc)
    (hR : ∀ p : ℚ × ℚ × ℚ, ∃ R' : Set X, MeasurableSet[nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ] R' ∧
      ∀ x ∈ G, (ratBall p ⊆ R x ↔ x ∈ R')) :
    Measurable[nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ, hittingSigma]
      (G.piecewise (fun x => chartSet (cc x) (chartHull (accessExitCode E cc ρ T V a k h) r x)) fun _ => H) := by
  -- the null set where the path reading fails
  set N := toMeasurable μ {x | ¬ (x ∈ G →
    ∀ u : ℝ≥0, 0 < u → u < exitNN E cc ρ T V x → ρ x u = histTrace 0 (R₀ x) (t₀ + u))} with hN
  have hN0 : μ N = 0 := by
    rw [hN, measure_toMeasurable]
    exact ae_iff.1 hpath
  have hNae : ∀ᵐ x ∂μ, x ∉ N := by
    rw [ae_iff]
    simpa only [not_not, ofPred_mem_eq] using hN0
  have hNm : MeasurableSet N := measurableSet_toMeasurable μ _
  -- the live set without the null set
  have hG'm : MeasurableSet[nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ] (G \ N) := by
    obtain ⟨hGa, J, hJ, hGJ⟩ := hGm
    refine ⟨hGa.diff hNm, J, hJ, EventuallyEq.trans ?_ hGJ⟩
    filter_upwards [hNae] with x hx
    exact propext ⟨fun h => h.1, fun h => ⟨h, hx⟩⟩
  have hG' : ∀ x ∈ G \ N, (r : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life ∧
      cc x = c (Y₀ x, stopRec t₀ (R₀ x)) ∧
      (∀ u : ℝ≥0, 0 < u → u < exitNN E cc ρ T V x → ρ x u = histTrace 0 (R₀ x) (t₀ + u)) ∧
      ((cc x).dom : Set ℂ) = connectedComponentIn (R x) (b x) := by
    intro x hx
    have hp : x ∈ G → ∀ u : ℝ≥0, 0 < u → u < exitNN E cc ρ T V x → ρ x u = histTrace 0 (R₀ x) (t₀ + u) := by
      by_contra hn
      exact hx.2 (subset_toMeasurable μ _ hn)
    exact ⟨(hG x hx.1).1, (hG x hx.1).2.1, hp hx.1, (hG x hx.1).2.2⟩
  have hR' : ∀ p : ℚ × ℚ × ℚ, ∃ R' : Set X,
      MeasurableSet[nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ] R' ∧
      ∀ x ∈ G \ N, (ratBall p ⊆ R x ↔ x ∈ R') := fun p => by
    obtain ⟨R', hR'm, hR'e⟩ := hR p
    exact ⟨R', hR'm, fun x hx => hR'e x hx.1⟩
  have hmeas' := measurable_markedSet_nullRuleMarks hs hV hV0 hland hinj d hdV hℓ hc hY₀ hR₀ hG'm hG' hcm hR'
  -- the ambient measurability of the exact live set
  have hamb := measurable_markedSet_ambient hs hV hV0 hland hinj d hdV hℓ hliftc hh (nullMarks_le _ hGm)
    (fun x hx => ⟨(hG x hx).1, (hG x hx).2.2⟩) fun p => by
      obtain ⟨R', hR'm, hR'e⟩ := hR p
      exact ⟨R', nullMarks_le _ hR'm, hR'e⟩
  refine measurable_nullMarks_of_ae_eq_nullMarks hittingSigma hamb hmeas' ?_
  filter_upwards [hNae] with x hx
  by_cases hxG : x ∈ G
  · have hx' : x ∈ G \ N := ⟨hxG, hx⟩
    simp only [Set.piecewise, hxG, hx', ↓reduceIte]
  · have hx' : x ∉ G \ N := fun h => hxG h.1
    simp only [Set.piecewise, hxG, hx', ↓reduceIte]

end AE

/-! ### R1's chart: the component of the retained domain, and the counterflow history hull -/

section R1

/-- **R1's chart domain is the component of its retained domain**: R1's chart (`HasOriginalTargetRestartChart`) is a
measurable conformal chart with continuous lift whose domain is the connected component of the retained domain
`ℍ ∖ (K_s ∪ η[0, q])` at a measurable base point. -/
theorem exists_isMeasChart_of_hasOriginalTargetRestartChart {Ω : Type*} [MeasurableSpace Ω] {s r : ℝ≥0} {q : ℚ}
    {Y : Ω → HistorySpace 0 0} {η : Ω → ℝ → ℂ} {U : ℝ≥0 → Ω → ℝ} {e : ℕ → ℂ}
    (hR1 : Aux61Restart.HasOriginalTargetRestartChart s r q Y η U e) :
    ∃ b : Ω → ℂ, Measurable b ∧
      (∀ ω, b ω ∈ Aux61Restart.retainedDomain (Aux61Restart.historyHull s Y ω) (η ω) q) ∧
      ∃ c : Ω → Chart, IsMeasChart c ∧ (∀ ω, (c ω).IsConformal) ∧
        (∀ ω, ((c ω).dom : Set ℂ) =
          connectedComponentIn (Aux61Restart.retainedDomain (Aux61Restart.historyHull s Y ω) (η ω) q) (b ω)) ∧
        ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom := by
  obtain ⟨N, hN, hmem, -, c, hconf, hdom, -, hd, hf, hl, hcont, -⟩ := hR1
  have hb : Measurable fun ω => e (N ω) := measurable_from_nat.comp hN
  have hm : IsMeasChart c := ⟨hd, hf, hl⟩
  refine ⟨fun ω => e (N ω), hb, hmem, c, hm, hconf, fun ω => ?_, hcont⟩
  rw [hdom ω]
  rfl

/-- **The counterflow history hull of the records is hitting-measurable.** -/
theorem measurable_historyHull_fst {β : Type*} [MeasurableSpace β] (s : ℝ≥0) :
    Measurable[_, hittingSigma] (Aux61Restart.historyHull s (fun p : HistorySpace 0 0 × β => p.1)) :=
  Aux61Restart.measurable_historyHull ((GlueCond.measurable_cfStop s).comp measurable_fst)

/-! #### R1's contact obstacle -/

open scoped Classical in
/-- The distance to the complement of a set as a countable supremum of closed-ball tests. -/
theorem infDist_compl_eq_iSup {U : Set ℂ} (hU : Uᶜ.Nonempty) (z : ℂ) :
    infDist z Uᶜ = ⨆ q : ℚ, if 0 ≤ (q : ℝ) ∧ closedBall z q ⊆ U then (q : ℝ) else 0 := by
  have hterm : ∀ q : ℚ, (if 0 ≤ (q : ℝ) ∧ closedBall z q ⊆ U then (q : ℝ) else 0) ≤ infDist z Uᶜ := by
    intro q
    by_cases hq : 0 ≤ (q : ℝ) ∧ closedBall z q ⊆ U
    · rw [ite_eq_left hq]
      refine (le_infDist hU).2 fun w hw => le_of_not_gt fun hlt => hw (hq.2 ?_)
      rw [mem_closedBall, dist_comm]
      exact hlt.le
    · rw [ite_eq_right hq]
      exact infDist_nonneg
  have hbdd : BddAbove (range fun q : ℚ => if 0 ≤ (q : ℝ) ∧ closedBall z q ⊆ U then (q : ℝ) else 0) :=
    ⟨infDist z Uᶜ, by rintro _ ⟨q, rfl⟩; exact hterm q⟩
  refine le_antisymm (le_of_forall_lt fun c hc => ?_) (ciSup_le hterm)
  rcases lt_or_ge c 0 with hc0 | hc0
  · refine lt_of_lt_of_le hc0 (le_ciSup_of_le hbdd 0 ?_)
    by_cases h0 : 0 ≤ ((0 : ℚ) : ℝ) ∧ closedBall z ((0 : ℚ) : ℝ) ⊆ U
    · rw [ite_eq_left h0, Rat.cast_zero]
    · rw [ite_eq_right h0]
  · obtain ⟨q, hcq, hqd⟩ := exists_rat_btwn hc
    have hq0 : 0 ≤ (q : ℝ) := hc0.trans hcq.le
    have hsub : closedBall z q ⊆ U := fun w hw => by
      by_contra hwU
      have h1 := infDist_le_dist_of_mem (x := z) (show w ∈ Uᶜ from hwU)
      rw [mem_closedBall, dist_comm] at hw
      linarith
    refine lt_of_lt_of_le hcq (le_ciSup_of_le hbdd q ?_)
    rw [ite_eq_left ⟨hq0, hsub⟩]

/-- **R1's contact obstacle**: the complement of `ℍ ∖ K_s` for the counterflow history hull of the records (the
first hit of it after the restart time is the first contact with the hull or the real line). -/
def retObs (s : ℝ≥0) {β : Type*} (p : HistorySpace 0 0 × β) : Set ℂ :=
  (H \ Aux61Restart.historyHull s (fun p : HistorySpace 0 0 × β => p.1) p)ᶜ

theorem isClosed_retObs (s : ℝ≥0) {β : Type*} (p : HistorySpace 0 0 × β) : IsClosed (retObs s p) :=
  (Aux61Restart.historyHull_properties s _ p).1.isClosed_compl

theorem retObs_nonempty (s : ℝ≥0) {β : Type*} (p : HistorySpace 0 0 × β) : (retObs s p).Nonempty :=
  ⟨0, fun h => by
    have h0 := h.1
    simp only [QuantumZipper.H, mem_ofPred_eq, Complex.zero_im, lt_self_iff_false] at h0⟩

open CrossCond.Word49 in
open scoped Classical in
/-- **The distances to R1's contact obstacle are measurable in the records.** -/
theorem measurable_infDist_retObs (s : ℝ≥0) {β : Type*} [MeasurableSpace β] (z : ℂ) :
    Measurable fun p : HistorySpace 0 0 × β => infDist z (retObs s p) := by
  have hm : ∀ (c : ℂ) (ρ : ℝ), MeasurableSet {p : HistorySpace 0 0 × β |
      closedBall c ρ ⊆ H \ Aux61Restart.historyHull s (fun p : HistorySpace 0 0 × β => p.1) p} := by
    intro c ρ
    have h := measurableSet_comp_of_stopSigma (𝓜 := inferInstance) (Y := fun p : HistorySpace 0 0 × β => p.1)
      (measurableSet_closedBall_subset_dom_cfChart (s := s) c ρ) ((GlueCond.measurable_cfStop s).comp measurable_fst)
    simpa only [preimage_ofPred_eq, coe_dom_cfChart, Aux61Restart.historyHull] using h
  have e : (fun p : HistorySpace 0 0 × β => infDist z (retObs s p)) = fun p => ⨆ q : ℚ,
      if 0 ≤ (q : ℝ) ∧ closedBall z q ⊆ H \ Aux61Restart.historyHull s (fun p : HistorySpace 0 0 × β => p.1) p
      then (q : ℝ) else 0 :=
    funext fun p => infDist_compl_eq_iSup (retObs_nonempty s p) z
  rw [e]
  exact Measurable.iSup fun q => Measurable.ite ((MeasurableSet.const _).inter (hm z q)) measurable_const
    measurable_const

/-- **R1's absolute contact time is a measurable Galmarino rule of the records**: the contact rule of R1's obstacle. -/
theorem measurable_isGalmarinoRule_contactRule_retObs (s t₀ : ℝ≥0) {nL nR : ℕ} :
    Measurable (contactRule (retObs s (β := HistorySpace nL nR)) t₀) ∧
      IsGalmarinoRule stopRec (contactRule (retObs s (β := HistorySpace nL nR)) t₀) :=
  ⟨measurable_contactRule (measurable_infDist_retObs s) t₀, isGalmarinoRule_contactRule _ t₀⟩

end R1

/-! ### `baseSets_marks` for the concrete source form -/

section Source

variable {X : Type*} [mX : MeasurableSpace X] {E : Set X} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ}
  {a k : ℝ} {h : X → LQGMetric.DistOn upperHalfPlaneOpens}
  {𝒴 : Type*} [MeasurableSpace 𝒴] {nL nR : ℕ}
  {c : 𝒴 × HistorySpace nL nR → Chart} {t₀ : ℝ≥0} {Y₀ : X → 𝒴} {R₀ : X → HistorySpace nL nR} {μ : Measure X}

/-- **`baseSets_marks` for the concrete source form.** The live set of the time-`0` record event `{record ∈ B}` (read
through any `Z`, `B'`) at the alive code: the chart is read from the time-`0` record and, on `B`, its domain is the
component of the retained domain of a hitting-measurable record obstacle `K` and the record's own prefix (continuous on
`[0, t₀]`); the restart data are as in `codeFiltration_le_nullRuleMarks_of_source`. Then the live marked set is
hitting-measurable for the null completion of the rule marks of SLITW's glued stop `capacityRule c t₀ r`. -/
theorem measurable_liveSet_nullRuleMarks_of_source
    (hs : IsRestartSpec E (fun x => c (Y₀ x, stopRec t₀ (R₀ x))) ρ T) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
    (hland : HasAccessLanding E (fun x => c (Y₀ x, stopRec t₀ (R₀ x))) ρ T V)
    (hinj : ∀ x ∈ E, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x}) (hc : IsMeasChart c)
    (hliftc : ∀ x ∈ E, ContinuousOn (c (Y₀ x, stopRec t₀ (R₀ x))).2.2 (c (Y₀ x, stopRec t₀ (R₀ x))).dom)
    (hh : Measurable h) (d : FibData) (hdV : d.V = V) (hℓ : d.ℓ = clr V) (hY₀ : Measurable Y₀)
    (hR₀ : Measurable R₀) (r : ℝ≥0)
    {B : Set (𝒴 × HistorySpace nL nR)} (hB : MeasurableSet B)
    (hEv : E =ᵐ[μ] (fun x => (Y₀ x, stopRec t₀ (R₀ x))) ⁻¹' B)
    (hstop : ∀ᵐ x ∂μ, (Y₀ x, stopRec t₀ (R₀ x)) ∈ B → x ∈ E ∧ 0 < T x ∧
      (T x < ⊤ ∨ ∃ v : ℝ≥0, (v : ℝ≥0∞) < T x ∧
        inPath E (fun x => c (Y₀ x, stopRec t₀ (R₀ x))) ρ T x v ∉ V))
    (hpath : ∀ᵐ x ∂μ, x ∈ E → ∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < T x → ρ x u = histTrace 0 (R₀ x) (t₀ + u))
    (htr : ∀ᵐ x ∂μ, x ∈ E → Continuous (histTrace 0 (R₀ x)))
    {C : 𝒴 × HistorySpace nL nR → Set ℂ} (hC : ∀ p, IsClosed (C p)) (hCne : ∀ p, (C p).Nonempty)
    (hCm : ∀ z : ℂ, Measurable fun p : 𝒴 × HistorySpace nL nR => infDist z (C p))
    (hT : ∀ᵐ x ∂μ, x ∈ E → T x = hitTime ρ (fun x => C (Y₀ x, stopRec t₀ (R₀ x))) x ∧
      ρ x 0 ∉ C (Y₀ x, stopRec t₀ (R₀ x)))
    {K : 𝒴 × HistorySpace nL nR → Set ℂ} (hK : Measurable[_, hittingSigma] K) {b : 𝒴 × HistorySpace nL nR → ℂ}
    (hdom : ∀ p ∈ B, ((c p).dom : Set ℂ) = connectedComponentIn
      (Aux61Restart.retainedDomain (K p) (fun t : ℝ => histTrace 0 p.2 t.toNNReal) t₀) (b p))
    (hcont : ∀ p ∈ B, ContinuousOn (fun t : ℝ => histTrace 0 p.2 t.toNNReal) (Icc 0 (t₀ : ℝ)))
    {β : Type*} (Z : X → β) (B' : Set β) (hZ : ∀ x, Z x ∈ B' ↔ (Y₀ x, stopRec t₀ (R₀ x)) ∈ B) :
    Measurable[nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ, hittingSigma]
      (Aux61ChLoc.liveSet (Aux61ChLoc.liveEv Z B'
        (accessExitCode E (fun x => c (Y₀ x, stopRec t₀ (R₀ x))) ρ T V a k h) r)
        fun x => chartSet (c (Y₀ x, stopRec t₀ (R₀ x)))
          (chartHull (accessExitCode E (fun x => c (Y₀ x, stopRec t₀ (R₀ x))) ρ T V a k h) r x)) := by
  have hle : ∀ p, (t₀ : ℝ≥0∞) ≤ capacityRule c t₀ r p := Aux61SlitW.start_le_capacityRule c t₀ r
  have hℋle : ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀ ≤ mX :=
    ruleMarks_le isRecordStop_stopRec (Aux61SlitW.measurable_capacityRule hc t₀ r) hY₀ hR₀
  have hrec0 : Measurable[ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀] fun x => (Y₀ x, stopRec t₀ (R₀ x)) :=
    measurable_ruleMarks_of_time0 (F := id) measurable_id isRecordStop_stopRec hle
  have hrecN : Measurable[nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ]
      fun x => (Y₀ x, stopRec t₀ (R₀ x)) :=
    hrec0.mono (le_nullMarks hℋle) le_rfl
  -- the live event is in the completed marks
  have hTa := ae_contactRule_eq hC hCne hs.contρ htr hT hpath
  have hrec : ∀ᵐ x ∂μ, x ∈ E → c (Y₀ x, stopRec t₀ (R₀ x)) = c (Y₀ x, stopRec t₀ (R₀ x)) ∧
      (∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < T x → ρ x u = histTrace 0 (R₀ x) (t₀ + u)) ∧
      contactRule C t₀ (Y₀ x, R₀ x) = (t₀ : ℝ≥0∞) + T x := by
    filter_upwards [hpath, hTa] with x hx hxT hxE
    exact ⟨rfl, hx hxE, hxT hxE⟩
  have halive := measurableSet_alive_nullRuleMarks_on (a := a) (k := k) hs hV hV0 hland hinj hc
    (measurable_contactRule hCm t₀) (isGalmarinoRule_contactRule C t₀) hliftc hh (le_refl r)
    (measurableSet_nullRuleMarks_of_version hle hs.measurableSet hB hEv) hrec (ae_mem_exitEv_of_stop hEv hstop)
  have hZm : MeasurableSet[nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ] {x | Z x ∈ B'} := by
    have e : {x | Z x ∈ B'} = (fun x => (Y₀ x, stopRec t₀ (R₀ x))) ⁻¹' B := by
      ext x
      exact hZ x
    rw [e]
    exact hrecN hB
  have hGm : MeasurableSet[nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ] (Aux61ChLoc.liveEv Z B'
      (accessExitCode E (fun x => c (Y₀ x, stopRec t₀ (R₀ x))) ρ T V a k h) r) := hZm.inter halive
  -- the retained-domain events
  have hK₀ : Measurable[nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ, hittingSigma]
      fun x => K (Y₀ x, stopRec t₀ (R₀ x)) := hK.comp hrecN
  have hηm : ∀ v : ℝ, Measurable[nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ] fun x =>
      histTrace 0 (stopRec t₀ (R₀ x)) v.toNNReal := by
    intro v
    have h1 : Measurable fun p : 𝒴 × HistorySpace nL nR => histTrace 0 p.2 v.toNNReal :=
      (measurable_histTrace 0 v.toNNReal).comp measurable_snd
    have h2 := h1.comp hrecN
    exact h2
  unfold Aux61ChLoc.liveSet
  refine measurable_markedSet_nullRuleMarks_on hs hV hV0 hland hinj d hdV hℓ hc hliftc hh hY₀ hR₀ hGm
    (R := fun x => Aux61Restart.retainedDomain (K (Y₀ x, stopRec t₀ (R₀ x)))
      (fun t : ℝ => histTrace 0 (stopRec t₀ (R₀ x)) t.toNNReal) t₀)
    (b := fun x => b (Y₀ x, stopRec t₀ (R₀ x)))
    (fun x hx => ⟨hx.2, rfl, hdom _ ((hZ x).1 hx.1)⟩) ?_
    (isMeasChart_nullRuleMarks_of_time0_ae hs.chart hc isRecordStop_stopRec hle (ae_of_all _ fun _ => rfl))
    fun p => exists_retained_event hK₀ (NNReal.coe_nonneg t₀) (fun x hx => hcont _ ((hZ x).1 hx.1)) hηm p
  filter_upwards [hpath] with x hx hxG u hu hue
  exact hx (mem_exitEv_of_lt_accessLife hxG.2).1.1 u hu (lt_T_of_lt_exitNN hue)

end Source

end InteractingSLE.Sec5.Aux61Marks
