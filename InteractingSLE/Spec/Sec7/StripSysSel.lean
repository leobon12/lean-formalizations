/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux130
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Aux. lemma 130: the deterministic rational change time and its positive-probability events

Packet PROVE-STRIPSYS. Specification §7.4.1, Aux. lemma 130 and its proof (`source/spec/p385-432.md` L401–L489,
pp. 408–413).

PROVE-AUX119-130 proved the point-set steps of Aux. lemma 130 for one realization (`Sec7/Aux130.lean`). This file adds
the probabilistic step that turns them into a *deterministic* rational change time, and the measurability of the
events involved:

> "By (RS13.2), and by the preceding no-terminal-arc conclusion, almost surely there is a rational `r > 0` such that
> `E_r := {β(r) ∉ α([0, ∞]), T(β(r)) < T(p)}` (RS13.4) occurs. […] The events are measurable: first visits to a point
> are measurable functions of a continuous path and the point, since membership in each compact initial range is
> measurable. Their countable union has probability one. Fix one deterministic rational `r` with `ℙ(E_r) > 0`."

and the inclusion `E_r ⊆ F_r` after the angle change at `r` ((RS13.5): the first subsequent common contact is strictly
after the first change along the first path).

The paths live in a metric space `X` (the source's "fixed conformal compactification in which the strip is a Jordan
domain and all three complete paths are continuous"); the complete range `α([0, ∞])` of a path converging to its
terminal point is `closure (range α)`.

## Main results

* `mem_image_Icc_iff`, `notMem_closure_range_iff`: countable descriptions of the compact initial ranges and of the
  complement of the complete range of a continuous path, through rational times.
* `measurableSet_inter_firstVisit_le`, `measurableSet_inter_firstVisit_lt`,
  `measurableSet_inter_notMem_closure_range`: on a measurable set of realizations where the paths are continuous,
  the first-visit events are measurable for every σ-algebra making the rational-time values measurable.
* `IsSelectionConfig`: the pathwise hypotheses of (RS13.2)–(RS13.4) for one realization.
* **`exists_rat_selEvent`**: pathwise (RS13.2) + (RS13.4).
* **`exists_rat_measure_selEvent_pos`**: Aux. lemma 130's choice of one deterministic rational `r > 0` with
  `ℙ(E_r) > 0`, `E_r` measurable on the good set.
* **`notMem_image_Icc_of_firstVisit_lt`**, **`IsSelPoint.isContactPoint`** and `selEvent_subset_contactEvent`:
  `E_r ⊆ F_r` ((RS13.5) and the first subsequent contact) for the path `β^{(r)}` with the same point at `r`, where
  `F_r` (`IsContactPoint`, `contactEvent`) is the event of the final labelled incoming paths alone.
* `contactBy_iff`, `isBadContact_iff`: countable descriptions of "a contact by time `t`" and of "the first contact is
  on `α([0, 1])`" through rational times.
* **`measurableSet_inter_contactEvent`**: `F_r` is measurable for every σ-algebra making the rational-time values of
  the two incoming paths measurable ("Compact contact sets and continuous inverse path parametrizations make this a
  measurable event").
* **`exists_rat_measure_contactEvent_pos`**, **`exists_rat_contactEvent`**: Aux. lemma 130's conclusion on the event
  level: a deterministic rational `r > 0` with `ℙ(F_r) > 0`, `F_r` measurable from the incoming paths alone.
* **`exists_isContactGap_upper_notMem`**: on `F_r`, in Aux. lemma 33's disc-crosscut parametrization, the contact gap
  of the second path containing its change point has its upper contact `y₀` strictly after the first change along
  the first path (its pocket is a Jordan pocket by `WangWu.pocket_props`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace StripSys

open Aux130

/-- The rational time `q⁺` as an element of `ℝ≥0` (the indexing of rational times used by `Aux130`). -/
def rt (q : ℚ) : ℝ≥0 := (q : ℝ).toNNReal

theorem rt_one : rt 1 = 1 := by simp [rt]

theorem coe_rt {q : ℚ} (hq : 0 ≤ q) : (rt q : ℝ) = q := by
  simp only [rt, Real.coe_toNNReal _ (Rat.cast_nonneg.2 hq)]

/-- Every point of `[0, t]` is approximated by rational points of `[0, t]`. -/
theorem exists_rat_near {s t : ℝ≥0} (hst : s ≤ t) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : ℚ, 0 ≤ q ∧ (q : ℝ) ≤ t ∧ dist (rt q) s < δ := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with hs | hs
  · refine ⟨0, le_rfl, by simp, ?_⟩
    rw [← hs]
    simp [rt, hδ]
  · have hs' : (0 : ℝ) < s := hs
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt (sub_lt_self (s : ℝ) hδ) hs')
    have hq0 : (0 : ℝ) < q := lt_of_le_of_lt (le_max_right _ _) hq1
    have hq0' : (0 : ℚ) ≤ q := by exact_mod_cast hq0.le
    refine ⟨q, hq0', hq2.le.trans (by exact_mod_cast hst), ?_⟩
    rw [NNReal.dist_eq, coe_rt hq0', abs_sub_lt_iff]
    have := lt_of_le_of_lt (le_max_left _ _) hq1
    constructor <;> linarith

section Deterministic

variable {X : Type*} [MetricSpace X]

/-- **The compact initial range through rational times**: for a continuous path, `z ∈ γ([0, t])` iff `z` is a limit
of values of `γ` at rational times in `[0, t]`. -/
theorem mem_image_Icc_iff {γ : ℝ≥0 → X} (hγ : Continuous γ) (t : ℝ≥0) (z : X) :
    z ∈ γ '' Icc 0 t ↔
      ∀ n : ℕ, ∃ q : ℚ, 0 ≤ q ∧ (q : ℝ) ≤ t ∧ dist z (γ (rt q)) < 1 / (n + 1) := by
  constructor
  · rintro ⟨s, hs, rfl⟩ n
    have hε : (0 : ℝ) < 1 / (n + 1) := Nat.one_div_pos_of_nat
    obtain ⟨δ, hδ, hcont⟩ := Metric.continuous_iff.1 hγ s _ hε
    obtain ⟨q, hq0, hqt, hqs⟩ := exists_rat_near hs.2 hδ
    exact ⟨q, hq0, hqt, by rw [dist_comm]; exact hcont _ hqs⟩
  · intro h
    have hcl : IsClosed (γ '' Icc 0 t) := (isCompact_Icc.image hγ).isClosed
    refine hcl.closure_subset_iff.2 subset_rfl (Metric.mem_closure_iff.2 fun ε hε => ?_)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨q, hq0, hqt, hd⟩ := h n
    refine ⟨γ (rt q), ⟨rt q, ⟨zero_le, ?_⟩, rfl⟩, hd.trans hn⟩
    exact Real.toNNReal_le_iff_le_coe.2 hqt

/-- **The complement of the complete range through rational times**: for a continuous path, `z ∉ closure (range α)`
iff `z` keeps a positive distance from all rational-time values of `α`. -/
theorem notMem_closure_range_iff {α : ℝ≥0 → X} (hα : Continuous α) (z : X) :
    z ∉ closure (range α) ↔ ∃ n : ℕ, ∀ q : ℚ, 0 ≤ q → 1 / (n + 1) ≤ dist z (α (rt q)) := by
  constructor
  · intro hz
    rw [Metric.mem_closure_iff] at hz
    push Not at hz
    obtain ⟨ε, hε, hfar⟩ := hz
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    exact ⟨n, fun q _ => hn.le.trans (hfar _ ⟨_, rfl⟩)⟩
  · rintro ⟨n, hn⟩ hz
    have hε : (0 : ℝ) < 1 / (n + 1) / 2 := half_pos Nat.one_div_pos_of_nat
    obtain ⟨_, ⟨s, rfl⟩, hzs⟩ := Metric.mem_closure_iff.1 hz _ hε
    obtain ⟨δ, hδ, hcont⟩ := Metric.continuous_iff.1 hα s _ hε
    obtain ⟨q, hq0, -, hqs⟩ := exists_rat_near (le_refl s) hδ
    have h1 := hcont _ hqs
    have h2 := hn q hq0
    have h3 := dist_triangle z (α s) (α (rt q))
    rw [dist_comm (α (rt q))] at h1
    linarith

end Deterministic

section Random

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The event `{T(z) ≤ t}` on a measurable set of realizations where the counterflow path is continuous is measurable,
for every σ-algebra making `z` and the rational-time values of the path measurable ("membership in each compact
initial range is measurable"). -/
theorem measurableSet_inter_firstVisit_le {G : Set Ω} (hG : MeasurableSet G) {γ : Ω → ℝ≥0 → X}
    (hγc : ∀ ω ∈ G, Continuous (γ ω)) (hγm : ∀ q : ℚ, Measurable fun ω => γ ω (rt q)) {z : Ω → X}
    (hz : Measurable z) (t : ℝ≥0) :
    MeasurableSet (G ∩ {ω | firstVisit (γ ω) (z ω) ≤ t}) := by
  have hS : MeasurableSet (⋂ n : ℕ, ⋃ q : ℚ, ⋃ (_ : 0 ≤ q ∧ (q : ℝ) ≤ t),
      {ω | dist (z ω) (γ ω (rt q)) < 1 / (n + 1)}) :=
    MeasurableSet.iInter fun n => MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
      measurableSet_lt (hz.dist (hγm q)) measurable_const
  convert hG.inter hS using 1
  ext ω
  simp only [mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_iUnion, exists_prop, and_assoc]
  refine and_congr_right fun hω => ?_
  have h := Set.ext_iff.1 (setOf_firstVisit_le (hγc ω hω) t) (z ω)
  rw [mem_ofPred_eq] at h
  rw [h, mem_image_Icc_iff (hγc ω hω)]

/-- `a < b` in `ℝ≥0∞` through a rational time strictly between them. -/
theorem lt_iff_exists_rt {a b : ℝ≥0∞} : a < b ↔ ∃ q : ℚ, a ≤ rt q ∧ ¬ b ≤ rt q := by
  constructor
  · intro h
    obtain ⟨q, -, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 h
    exact ⟨q, hq1.le, not_le.2 hq2⟩
  · rintro ⟨q, h1, h2⟩
    exact lt_of_le_of_lt h1 (not_le.1 h2)

/-- The event `{T(z₁) < T(z₂)}` comparing two random first visits is measurable on the good set. -/
theorem measurableSet_inter_firstVisit_lt {G : Set Ω} (hG : MeasurableSet G) {γ : Ω → ℝ≥0 → X}
    (hγc : ∀ ω ∈ G, Continuous (γ ω)) (hγm : ∀ q : ℚ, Measurable fun ω => γ ω (rt q)) {z₁ z₂ : Ω → X}
    (hz₁ : Measurable z₁) (hz₂ : Measurable z₂) :
    MeasurableSet (G ∩ {ω | firstVisit (γ ω) (z₁ ω) < firstVisit (γ ω) (z₂ ω)}) := by
  have hU : MeasurableSet (⋃ q : ℚ, (G ∩ {ω | firstVisit (γ ω) (z₁ ω) ≤ rt q}) \
      (G ∩ {ω | firstVisit (γ ω) (z₂ ω) ≤ rt q})) :=
    MeasurableSet.iUnion fun q => (measurableSet_inter_firstVisit_le hG hγc hγm hz₁ _).diff
      (measurableSet_inter_firstVisit_le hG hγc hγm hz₂ _)
  convert hU using 1
  ext ω
  simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion, Set.mem_sdiff, not_and]
  constructor
  · rintro ⟨hω, h⟩
    obtain ⟨q, h1, h2⟩ := lt_iff_exists_rt.1 h
    exact ⟨q, ⟨hω, h1⟩, fun _ => h2⟩
  · rintro ⟨q, ⟨hω, h1⟩, h2⟩
    exact ⟨hω, lt_iff_exists_rt.2 ⟨q, h1, h2 hω⟩⟩

/-- The event that a random point is off the complete range of a random continuous path is measurable on the good
set ("the nonmembership condition … the complete range is compact in the chosen compactification"). -/
theorem measurableSet_inter_notMem_closure_range {G : Set Ω} (hG : MeasurableSet G) {α : Ω → ℝ≥0 → X}
    (hαc : ∀ ω ∈ G, Continuous (α ω)) (hαm : ∀ q : ℚ, Measurable fun ω => α ω (rt q)) {z : Ω → X}
    (hz : Measurable z) :
    MeasurableSet (G ∩ {ω | z ω ∉ closure (range (α ω))}) := by
  have hS : MeasurableSet (⋃ n : ℕ, ⋂ q : ℚ, ⋂ (_ : 0 ≤ q),
      {ω | 1 / ((n : ℝ) + 1) ≤ dist (z ω) (α ω (rt q))}) :=
    MeasurableSet.iUnion fun n => MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ =>
      measurableSet_le measurable_const (hz.dist (hαm q))
  convert hG.inter hS using 1
  ext ω
  simp only [mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_iUnion]
  exact and_congr_right fun hω => notMem_closure_range_iff (hαc ω hω) (z ω)

end Random

/-! ### (RS13.2)–(RS13.4): the deterministic rational change time -/

section Selection

variable {X : Type*} [MetricSpace X]

/-- **The pathwise hypotheses of (RS13.2)–(RS13.4)** for one realization of the counterflow `γ` (in the fixed
compactification), the first incoming path `α` and the unchanged extremal path `β = η_{π/2}`, with common terminal
point `y` (the counterflow seed):
* the three paths are continuous;
* `β` is visited by `γ` in reverse order (Lemma 5.7's reverse containment), with finite first visits at positive
  times ("finite for `t > 0`");
* `β(t) → y` and `γ` visits `y` only at time `0` (the nonhit property on the original boundary);
* `β` has points outside the complete range of `α` at arbitrarily late times (the no-terminal-arc conclusion of
  (RS13.3));
* `T(p) > 0` for `p = α(1)` ("every other interior incoming point has `0 < T(z) < ∞`"). -/
structure IsSelectionConfig (γ α β : ℝ≥0 → X) (y : X) : Prop where
  continuous_γ : Continuous γ
  continuous_α : Continuous α
  continuous_β : Continuous β
  antitone_β : Antitone fun t => firstVisit γ (β t)
  firstVisit_lt_top : ∀ t, 0 < t → firstVisit γ (β t) < ⊤
  tendsto_β : Tendsto β atTop (𝓝 y)
  nonhit : ∀ t : ℝ≥0, 0 < t → γ t ≠ y
  late : ∀ N : ℝ≥0, ∃ t, N ≤ t ∧ β t ∉ closure (range α)
  firstVisit_pos : 0 < firstVisit γ (α 1)

/-- The event `E_r` of (RS13.4) for one realization: `β(r) ∉ α([0, ∞])` and `T(β(r)) < T(α(1))`. -/
def IsSelPoint (γ α β : ℝ≥0 → X) (r : ℚ) : Prop :=
  β (rt r) ∉ closure (range α) ∧ firstVisit γ (β (rt r)) < firstVisit γ (α 1)

/-- **(RS13.2) and (RS13.4), pathwise**: some positive rational `r` realizes `E_r`. -/
theorem IsSelectionConfig.exists_rat {γ α β : ℝ≥0 → X} {y : X} (h : IsSelectionConfig γ α β y) :
    ∃ r : ℚ, 0 < r ∧ IsSelPoint γ α β r :=
  exists_rat_notMem_firstVisit_lt h.continuous_β isClosed_closure h.late
    (tendsto_firstVisit_zero h.continuous_γ h.antitone_β h.firstVisit_lt_top h.tendsto_β h.nonhit)
    h.firstVisit_pos

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The event `E_r` of (RS13.4). -/
def selEvent (γ α β : Ω → ℝ≥0 → X) (r : ℚ) : Set Ω := {ω | IsSelPoint (γ ω) (α ω) (β ω) r}

/-- `E_r` is measurable on the good set of realizations where the three paths are continuous. -/
theorem measurableSet_inter_selEvent {G : Set Ω} (hG : MeasurableSet G) {γ α β : Ω → ℝ≥0 → X}
    (hc : ∀ ω ∈ G, Continuous (γ ω) ∧ Continuous (α ω) ∧ Continuous (β ω))
    (hm : ∀ q : ℚ, Measurable (fun ω => γ ω (rt q)) ∧ Measurable (fun ω => α ω (rt q)) ∧
      Measurable (fun ω => β ω (rt q))) (r : ℚ) :
    MeasurableSet (G ∩ selEvent γ α β r) := by
  have hα1 : Measurable fun ω => α ω 1 := by simpa only [rt_one] using (hm 1).2.1
  have h1 := measurableSet_inter_notMem_closure_range hG (fun ω hω => (hc ω hω).2.1) (fun q => (hm q).2.1)
    (hm r).2.2
  have h2 := measurableSet_inter_firstVisit_lt hG (fun ω hω => (hc ω hω).1) (fun q => (hm q).1) (hm r).2.2 hα1
  convert h1.inter h2 using 1
  ext ω
  simp only [selEvent, IsSelPoint, mem_inter_iff, mem_ofPred_eq]
  tauto

/-- **Aux. lemma 130, the deterministic rational change time** ("Their countable union has probability one. Fix one
deterministic rational `r` with `ℙ(E_r) > 0`"): if almost every realization satisfies the hypotheses of
(RS13.2)–(RS13.4), there is a deterministic rational `r > 0` whose event `E_r` (intersected with the measurable good
set) is measurable and has positive probability. -/
theorem exists_rat_measure_selEvent_pos {P : Measure Ω} [NeZero P] {G : Set Ω} (hG : MeasurableSet G)
    {γ α β : Ω → ℝ≥0 → X} (hc : ∀ ω ∈ G, Continuous (γ ω) ∧ Continuous (α ω) ∧ Continuous (β ω))
    (hm : ∀ q : ℚ, Measurable (fun ω => γ ω (rt q)) ∧ Measurable (fun ω => α ω (rt q)) ∧
      Measurable (fun ω => β ω (rt q)))
    (hGae : ∀ᵐ ω ∂P, ω ∈ G) {y : X} (hconf : ∀ᵐ ω ∂P, IsSelectionConfig (γ ω) (α ω) (β ω) y) :
    ∃ r : ℚ, 0 < r ∧ MeasurableSet (G ∩ selEvent γ α β r) ∧ 0 < P (G ∩ selEvent γ α β r) := by
  by_contra hcon
  push Not at hcon
  have hnull : ∀ r : ℚ, ∀ᵐ ω ∂P, ¬(0 < r ∧ ω ∈ G ∩ selEvent γ α β r) := by
    intro r
    by_cases hr : 0 < r
    · have h0 : P (G ∩ selEvent γ α β r) = 0 :=
        nonpos_iff_eq_zero.1 (hcon r hr (measurableSet_inter_selEvent hG hc hm r))
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ω hω
      exact fun h => hω h.2
    · exact Eventually.of_forall fun ω h => hr h.1
  have hfalse : ∀ᵐ ω ∂P, False := by
    filter_upwards [ae_all_iff.2 hnull, hGae, hconf] with ω hω hGω hcω
    obtain ⟨r, hr, hE⟩ := hcω.exists_rat
    exact hω r ⟨hr, hGω, hE⟩
  exact NeZero.ne P (ae_eq_bot.1 (eventually_false_iff_eq_bot.1 hfalse))

end Selection

/-! ### (RS13.5): `E_r ⊆ F_r` after the angle change at `r` -/

section Contact

variable {X : Type*} [MetricSpace X]

omit [MetricSpace X] in
/-- **(RS13.5), the contact is after the first change**: if `α` is visited in reverse order, a point first visited
strictly before `α(1)` is not on the first prefix `α([0, 1])`. -/
theorem notMem_image_Icc_of_firstVisit_lt {γ α : ℝ≥0 → X} (hrev : Antitone fun t => firstVisit γ (α t)) {z : X}
    (hz : firstVisit γ z < firstVisit γ (α 1)) : z ∉ α '' Icc 0 1 := by
  rintro ⟨u, hu, rfl⟩
  exact absurd (hrev hu.2) (not_le.2 hz)

/-- **The event `F_r` for one realization** of the final labelled incoming paths `α` and `βr = β^{(r)}` ("the second
change point is off the first path and its first subsequent common contact is strictly after the first change along
that first path"): `βr(r) ∉ α([0, ∞])`, and every visit of the first prefix `α([0, 1])` by `βr` after `r` is preceded
by a visit of the complete range of `α`, i.e. the first contact after `r` (finite, or the terminal point) is not on
`α([0, 1])`. -/
def IsContactPoint (α βr : ℝ≥0 → X) (r : ℚ) : Prop :=
  βr (rt r) ∉ closure (range α) ∧
    ∀ s, rt r ≤ s → βr s ∈ α '' Icc 0 1 → ∃ u, rt r ≤ u ∧ u < s ∧ βr u ∈ closure (range α)

/-- **`E_r ⊆ F_r`, pathwise** ((RS13.5) and the first subsequent contact): replace the future of `β` after the own
time `r` by a continuous path `βr` with the same point at `r` (the prefix is unchanged), still visited by `γ` in
reverse order. On `E_r` the first contact of `βr` after `r` with the complete range of `α` is not on `α([0, 1])`:
it is first visited no later than `βr(r) = β(r)`, hence strictly before `α(1)`. -/
theorem IsSelPoint.isContactPoint {γ α β βr : ℝ≥0 → X} {r : ℚ} (hE : IsSelPoint γ α β r)
    (hβr : Continuous βr) (hpre : βr (rt r) = β (rt r)) (hrevr : Antitone fun t => firstVisit γ (βr t))
    (hrevα : Antitone fun t => firstVisit γ (α t)) : IsContactPoint α βr r := by
  refine ⟨hpre ▸ hE.1, fun s hrs hs => ?_⟩
  have hK : βr s ∈ closure (range α) := by
    obtain ⟨u, -, hu⟩ := hs
    exact subset_closure ⟨u, hu⟩
  obtain ⟨b, hrb, hbs, hbK, hbefore⟩ := exists_firstContact hβr isClosed_closure (hpre ▸ hE.1) hrs hK
  rcases eq_or_lt_of_le hbs with rfl | hlt
  · refine absurd hs (notMem_image_Icc_of_firstVisit_lt hrevα ?_)
    exact lt_of_le_of_lt (hpre ▸ hrevr hrb.le) hE.2
  · exact ⟨b, hrb.le, hlt, hbK⟩

variable {Ω : Type*}

/-- The event `F_r` of the final labelled incoming paths. -/
def contactEvent (α βr : Ω → ℝ≥0 → X) (r : ℚ) : Set Ω := {ω | IsContactPoint (α ω) (βr ω) r}

/-- **`E_r ⊆ F_r`** on the realizations where the changed path is continuous, has the same prefix point at `r`, and
both incoming paths are visited in reverse order. -/
theorem selEvent_subset_contactEvent {γ α β βr : Ω → ℝ≥0 → X} {r : ℚ} {G : Set Ω}
    (hG : ∀ ω ∈ G, Continuous (βr ω) ∧ βr ω (rt r) = β ω (rt r) ∧
      (Antitone fun t => firstVisit (γ ω) (βr ω t)) ∧ Antitone fun t => firstVisit (γ ω) (α ω t)) :
    G ∩ {ω | IsSelPoint (γ ω) (α ω) (β ω) r} ⊆ contactEvent α βr r := fun ω hω =>
  hω.2.isContactPoint (hG ω hω.1).1 (hG ω hω.1).2.1 (hG ω hω.1).2.2.1 (hG ω hω.1).2.2.2

end Contact

/-! ### Measurability of `F_r` from the incoming paths alone -/

section ContactMeas

variable {X : Type*} [MetricSpace X]

/-- Every point of `[r, t]` (`r ≥ 0` rational) is approximated by rational points of `[r, t]`. -/
theorem exists_rat_near_Icc {r : ℚ} (hr : 0 ≤ r) {s : ℝ≥0} {t : ℝ} (hrs : rt r ≤ s) (hst : (s : ℝ) ≤ t)
    {δ : ℝ} (hδ : 0 < δ) : ∃ q : ℚ, r ≤ q ∧ (q : ℝ) ≤ t ∧ dist (rt q) s < δ := by
  have hrs' : (r : ℝ) ≤ s := by rw [← coe_rt hr]; exact_mod_cast hrs
  rcases eq_or_lt_of_le hrs' with heq | hlt
  · refine ⟨r, le_rfl, heq ▸ hst, ?_⟩
    have : rt r = s := NNReal.eq (by rw [coe_rt hr, heq])
    rw [this, dist_self]
    exact hδ
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt (sub_lt_self (s : ℝ) hδ) hlt)
    have hrq : r ≤ q := by exact_mod_cast (lt_of_le_of_lt (le_max_right _ _) hq1).le
    refine ⟨q, hrq, hq2.le.trans hst, ?_⟩
    rw [NNReal.dist_eq, coe_rt (hr.trans hrq), abs_sub_lt_iff]
    have := lt_of_le_of_lt (le_max_left _ _) hq1
    constructor <;> linarith

/-- `βr` meets the complete range of `α` at some own time in `[r, t]`. -/
def ContactBy (α βr : ℝ≥0 → X) (r : ℚ) (t : ℝ) : Prop :=
  ∃ u : ℝ≥0, rt r ≤ u ∧ (u : ℝ) ≤ t ∧ βr u ∈ closure (range α)

/-- **A contact by time `t`, through rational times** ("compact contact sets … obtainable from rational interval
tests"). -/
theorem contactBy_iff {α βr : ℝ≥0 → X} (hα : Continuous α) (hβ : Continuous βr) {r : ℚ} (hr : 0 ≤ r) (t : ℝ) :
    ContactBy α βr r t ↔ ∀ n : ℕ, ∃ q : ℚ, r ≤ q ∧ (q : ℝ) ≤ t ∧
      ∃ q' : ℚ, 0 ≤ q' ∧ dist (βr (rt q)) (α (rt q')) < 1 / (n + 1) := by
  constructor
  · rintro ⟨u, hru, hut, huK⟩ n
    have hε : (0 : ℝ) < 1 / (n + 1) / 3 := div_pos Nat.one_div_pos_of_nat (by norm_num)
    obtain ⟨δ, hδ, hcont⟩ := Metric.continuous_iff.1 hβ u _ hε
    obtain ⟨q, hrq, hqt, hqu⟩ := exists_rat_near_Icc hr hru hut hδ
    obtain ⟨_, ⟨s, rfl⟩, hus⟩ := Metric.mem_closure_iff.1 huK _ hε
    obtain ⟨δ', hδ', hcont'⟩ := Metric.continuous_iff.1 hα s _ hε
    obtain ⟨q', hq'0, -, hq's⟩ := exists_rat_near (le_refl s) hδ'
    refine ⟨q, hrq, hqt, q', hq'0, ?_⟩
    have h1 := hcont _ hqu
    have h2 := hcont' _ hq's
    have h3 := dist_triangle4 (βr (rt q)) (βr u) (α s) (α (rt q'))
    rw [dist_comm (α s)] at h3
    linarith
  · intro h
    obtain ⟨q₀, hrq₀, hq₀t, -⟩ := h 0
    have hrt : (r : ℝ) ≤ t := (Rat.cast_le.2 hrq₀).trans hq₀t
    have ht0 : (0 : ℝ) ≤ t := (Rat.cast_nonneg.2 hr).trans hrt
    set f : ℝ≥0 → ℝ := fun u => Metric.infDist (βr u) (closure (range α)) with hf
    have hfc : Continuous f := (Metric.continuous_infDist_pt _).comp hβ
    have hab : rt r ≤ t.toNNReal := by
      rw [← NNReal.coe_le_coe, coe_rt hr, Real.coe_toNNReal _ ht0]; exact hrt
    obtain ⟨u, hu, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab) hfc.continuousOn
    have hfu : f u = 0 := by
      refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) Metric.infDist_nonneg
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      obtain ⟨q, hrq, hqt, q', -, hd⟩ := h n
      have hqI : rt q ∈ Icc (rt r) t.toNNReal := by
        refine ⟨Real.toNNReal_le_toNNReal (Rat.cast_le.2 hrq), Real.toNNReal_le_toNNReal hqt⟩
      have h1 : f (rt q) ≤ dist (βr (rt q)) (α (rt q')) :=
        Metric.infDist_le_dist_of_mem (subset_closure ⟨_, rfl⟩)
      have h2 := hmin hqI
      simp only [mem_ofPred_eq] at h2
      linarith
    refine ⟨u, hu.1, ?_, ?_⟩
    · have := hu.2
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ht0] at this
      exact this
    · have hne : (closure (range α)).Nonempty := ⟨α 0, subset_closure ⟨0, rfl⟩⟩
      have hmem := (Metric.mem_closure_iff_infDist_zero hne).2 hfu
      rwa [closure_closure] at hmem

/-- The failure of `F_r`'s contact clause: after `r`, `βr` reaches the first prefix `α([0, 1])` without an earlier
visit of the complete range of `α`. -/
def IsBadContact (α βr : ℝ≥0 → X) (r : ℚ) : Prop :=
  ∃ s, rt r ≤ s ∧ βr s ∈ α '' Icc 0 1 ∧ ∀ u, rt r ≤ u → u < s → βr u ∉ closure (range α)

theorem isContactPoint_iff (α βr : ℝ≥0 → X) (r : ℚ) :
    IsContactPoint α βr r ↔ βr (rt r) ∉ closure (range α) ∧ ¬ IsBadContact α βr r := by
  simp only [IsContactPoint, IsBadContact, not_exists, not_and, not_forall, not_not, exists_prop]

/-- **The bad first contact through rational times**: `βr` first meets the complete range of `α` after `r` on
`α([0, 1])` iff, for every `n`, some rational time `q ≥ r` is within `1/(n+1)` after the first contact time and
`βr(q)` is within `1/(n+1)` of a rational-time point of `α([0, 1])`. -/
theorem isBadContact_iff {α βr : ℝ≥0 → X} (hα : Continuous α) (hβ : Continuous βr) {r : ℚ} (hr : 0 ≤ r) :
    IsBadContact α βr r ↔ ∀ n : ℕ, ∃ q : ℚ, r ≤ q ∧ ContactBy α βr r q ∧ ¬ ContactBy α βr r (q - 1 / (n + 1)) ∧
      ∃ q' : ℚ, 0 ≤ q' ∧ (q' : ℝ) ≤ 1 ∧ dist (βr (rt q)) (α (rt q')) < 1 / (n + 1) := by
  constructor
  · rintro ⟨s, hrs, ⟨v, hv, hsv⟩, hbefore⟩ n
    have hε : (0 : ℝ) < 1 / (n + 1) / 2 := half_pos Nat.one_div_pos_of_nat
    obtain ⟨δ, hδ, hcont⟩ := Metric.continuous_iff.1 hβ s _ hε
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_add_of_pos_right (s : ℝ)
      (lt_min hδ (Nat.one_div_pos_of_nat (n := n))))
    have hr' : (r : ℝ) ≤ s := by rw [← coe_rt hr]; exact_mod_cast hrs
    have hrq : r ≤ q := by exact_mod_cast (hr'.trans hq1.le)
    have hq0 : 0 ≤ q := hr.trans hrq
    have hqs : dist (rt q) s < δ := by
      rw [NNReal.dist_eq, coe_rt hq0, abs_sub_lt_iff]
      constructor <;> linarith [min_le_left δ (1 / ((n : ℝ) + 1))]
    obtain ⟨δ', hδ', hcont'⟩ := Metric.continuous_iff.1 hα v _ hε
    obtain ⟨q', hq'0, hq'1, hq'v⟩ := exists_rat_near hv.2 hδ'
    have hsK : βr s ∈ closure (range α) := subset_closure ⟨v, hsv⟩
    refine ⟨q, hrq, ⟨s, hrs, hq1.le, hsK⟩, ?_, q', hq'0, hq'1, ?_⟩
    · rintro ⟨u, hru, huq, huK⟩
      have hus : u < s := by
        have : (u : ℝ) < s := by linarith [min_le_right δ (1 / ((n : ℝ) + 1))]
        exact_mod_cast this
      exact hbefore u hru hus huK
    · have h1 := hcont _ hqs
      have h2 := hcont' _ hq'v
      have h3 := dist_triangle (βr (rt q)) (βr s) (α (rt q'))
      rw [← hsv] at h1 h3
      rw [dist_comm (α v) (α (rt q'))] at h3
      linarith
  · intro h
    set C : Set ℝ≥0 := {u | rt r ≤ u ∧ βr u ∈ closure (range α)} with hC
    have hCc : IsClosed C := isClosed_Ici.inter (isClosed_closure.preimage hβ)
    obtain ⟨q₀, -, ⟨u₀, hru₀, -, hu₀⟩, -⟩ := h 0
    have hCne : C.Nonempty := ⟨u₀, hru₀, hu₀⟩
    set τ := sInf C with hτ
    have hτC : τ ∈ C := hCc.csInf_mem hCne (OrderBot.bddBelow C)
    -- `τ` lies within `1/(n+1)` before each rational time of the hypothesis
    have hclose : ∀ n : ℕ, ∃ q : ℚ, 0 ≤ q ∧ dist (rt q) τ < 1 / (n + 1) ∧
        Metric.infDist (βr (rt q)) (α '' Icc 0 1) < 1 / (n + 1) := by
      intro n
      obtain ⟨q, hrq, ⟨u, hru, huq, huK⟩, hnot, q', hq'0, hq'1, hd⟩ := h n
      have hq0 : 0 ≤ q := hr.trans hrq
      have hτu : τ ≤ u := csInf_le (OrderBot.bddBelow C) ⟨hru, huK⟩
      have hτq : (τ : ℝ) ≤ q := (NNReal.coe_le_coe.2 hτu).trans huq
      have hqτ : (q : ℝ) - 1 / (n + 1) < τ := by
        by_contra hle
        exact hnot ⟨τ, hτC.1, not_lt.1 hle, hτC.2⟩
      refine ⟨q, hq0, ?_, ?_⟩
      · rw [NNReal.dist_eq, coe_rt hq0, abs_sub_lt_iff]
        constructor <;> linarith [Nat.one_div_pos_of_nat (α := ℝ) (n := n)]
      · refine lt_of_le_of_lt (Metric.infDist_le_dist_of_mem ⟨rt q', ⟨zero_le, ?_⟩, rfl⟩) hd
        exact Real.toNNReal_le_iff_le_coe.2 (by simpa using hq'1)
    have hzero : Metric.infDist (βr τ) (α '' Icc 0 1) = 0 := by
      refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) Metric.infDist_nonneg
      obtain ⟨δ, hδ, hcont⟩ := Metric.continuous_iff.1 hβ τ _ (half_pos hε)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min hδ (half_pos hε))
      obtain ⟨q, -, hqτ, hinf⟩ := hclose n
      have h1 := hcont _ (hqτ.trans (hn.trans_le (min_le_left _ _)))
      have h2 := Metric.infDist_le_infDist_add_dist (x := βr τ) (y := βr (rt q)) (s := α '' Icc 0 1)
      rw [dist_comm] at h1
      linarith [min_le_right δ (ε / 2)]
    have hcl : IsClosed (α '' Icc 0 1) := (isCompact_Icc.image hα).isClosed
    have hne : (α '' Icc 0 1).Nonempty := ⟨α 0, 0, ⟨le_rfl, zero_le⟩, rfl⟩
    have hmem : βr τ ∈ α '' Icc 0 1 := by
      rw [← hcl.closure_eq]
      exact (Metric.mem_closure_iff_infDist_zero hne).2 hzero
    refine ⟨τ, hτC.1, hmem, fun u hru hu huK => ?_⟩
    exact not_le.2 hu (csInf_le (OrderBot.bddBelow C) ⟨hru, huK⟩)

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The event `{ContactBy t}` is given by a countable formula on the good set. -/
theorem measurableSet_contactByFormula {α βr : Ω → ℝ≥0 → X}
    (hm : ∀ q : ℚ, Measurable (fun ω => α ω (rt q)) ∧ Measurable (fun ω => βr ω (rt q))) (r : ℚ) (t : ℝ) :
    MeasurableSet {ω | ∀ n : ℕ, ∃ q : ℚ, r ≤ q ∧ (q : ℝ) ≤ t ∧
      ∃ q' : ℚ, 0 ≤ q' ∧ dist (βr ω (rt q)) (α ω (rt q')) < 1 / (n + 1)} := by
  have : {ω | ∀ n : ℕ, ∃ q : ℚ, r ≤ q ∧ (q : ℝ) ≤ t ∧
      ∃ q' : ℚ, 0 ≤ q' ∧ dist (βr ω (rt q)) (α ω (rt q')) < 1 / (n + 1)} =
      ⋂ n : ℕ, ⋃ q : ℚ, ⋃ (_ : r ≤ q ∧ (q : ℝ) ≤ t), ⋃ q' : ℚ, ⋃ (_ : 0 ≤ q'),
        {ω | dist (βr ω (rt q)) (α ω (rt q')) < 1 / (n + 1)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, exists_prop, and_assoc]
  rw [this]
  exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
    MeasurableSet.iUnion fun q' => MeasurableSet.iUnion fun _ =>
      measurableSet_lt ((hm q).2.dist (hm q').1) measurable_const

/-- **`F_r` is measurable from the final labelled incoming paths alone** ("Compact contact sets and continuous inverse
path parametrizations make this a measurable event"), on a measurable set of realizations where both paths are
continuous, for every σ-algebra making their rational-time values measurable. -/
theorem measurableSet_inter_contactEvent {G : Set Ω} (hG : MeasurableSet G) {α βr : Ω → ℝ≥0 → X}
    (hc : ∀ ω ∈ G, Continuous (α ω) ∧ Continuous (βr ω))
    (hm : ∀ q : ℚ, Measurable (fun ω => α ω (rt q)) ∧ Measurable (fun ω => βr ω (rt q))) {r : ℚ} (hr : 0 ≤ r) :
    MeasurableSet (G ∩ contactEvent α βr r) := by
  set CB : ℝ → Set Ω := fun t => {ω | ∀ n : ℕ, ∃ q : ℚ, r ≤ q ∧ (q : ℝ) ≤ t ∧
      ∃ q' : ℚ, 0 ≤ q' ∧ dist (βr ω (rt q)) (α ω (rt q')) < 1 / (n + 1)} with hCB
  set Bad : Set Ω := ⋂ n : ℕ, ⋃ q : ℚ, ⋃ (_ : r ≤ q), (CB q ∩ (CB (q - 1 / (n + 1)))ᶜ ∩
      ⋃ q' : ℚ, ⋃ (_ : 0 ≤ q' ∧ (q' : ℝ) ≤ 1), {ω | dist (βr ω (rt q)) (α ω (rt q')) < 1 / (n + 1)})
    with hBad
  have hBadm : MeasurableSet Bad :=
    MeasurableSet.iInter fun n => MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
      ((measurableSet_contactByFormula hm r _).inter (measurableSet_contactByFormula hm r _).compl).inter
        (MeasurableSet.iUnion fun q' => MeasurableSet.iUnion fun _ =>
          measurableSet_lt ((hm q).2.dist (hm q').1) measurable_const)
  have h1 := measurableSet_inter_notMem_closure_range hG (fun ω hω => (hc ω hω).1) (fun q => (hm q).1) (hm r).2
  convert h1.diff hBadm using 1
  ext ω
  simp only [mem_inter_iff, Set.mem_sdiff, mem_ofPred_eq, contactEvent]
  constructor
  · rintro ⟨hω, hcp⟩
    rw [isContactPoint_iff] at hcp
    refine ⟨⟨hω, hcp.1⟩, fun hB => hcp.2 ?_⟩
    rw [isBadContact_iff (hc ω hω).1 (hc ω hω).2 hr]
    intro n
    simp only [hBad, hCB, mem_iInter, mem_iUnion, mem_inter_iff, mem_compl_iff, mem_ofPred_eq,
      exists_prop] at hB
    obtain ⟨q, hrq, ⟨h1, h2⟩, q', hq', hd⟩ := hB n
    refine ⟨q, hrq, (contactBy_iff (hc ω hω).1 (hc ω hω).2 hr _).2 h1, fun h3 => h2 ?_, q', hq'.1, hq'.2, hd⟩
    exact (contactBy_iff (hc ω hω).1 (hc ω hω).2 hr _).1 h3
  · rintro ⟨⟨hω, hK⟩, hB⟩
    refine ⟨hω, (isContactPoint_iff _ _ _).2 ⟨hK, fun hbad => hB ?_⟩⟩
    rw [isBadContact_iff (hc ω hω).1 (hc ω hω).2 hr] at hbad
    simp only [hBad, hCB, mem_iInter, mem_iUnion, mem_inter_iff, mem_compl_iff, mem_ofPred_eq, exists_prop]
    intro n
    obtain ⟨q, hrq, h1, h2, q', hq'0, hq'1, hd⟩ := hbad n
    refine ⟨q, hrq, ⟨(contactBy_iff (hc ω hω).1 (hc ω hω).2 hr _).1 h1, fun h3 => h2 ?_⟩, q', ⟨hq'0, hq'1⟩, hd⟩
    exact (contactBy_iff (hc ω hω).1 (hc ω hω).2 hr _).2 h3

end ContactMeas

/-! ### Aux. lemma 130's reference event -/

section Reference

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **Aux. lemma 130, the positive-probability reference event** (pp. 411–412: "Fix one deterministic rational `r`
with `ℙ(E_r) > 0`. Now replace the future of `β` after this fixed own time `r` by the angle-`θ₂` continuation,
obtaining `β^{(r)}` […] We proved `E_r ⊆ F_r`, so `ℙ(F_r) > 0`"): if almost every realization satisfies the
hypotheses of (RS13.2)–(RS13.4), and for every rational `r > 0` the changed path `βr r = β^{(r)}` is almost surely
continuous, has the prefix point `β(r)` at `r` and, like `α`, is visited by the counterflow in reverse order, then
some deterministic rational `r > 0` has `ℙ(F_r) > 0`. -/
theorem exists_rat_measure_contactEvent_pos {P : Measure Ω} [NeZero P] {G : Set Ω} (hG : MeasurableSet G)
    {γ α β : Ω → ℝ≥0 → X} {βr : ℚ → Ω → ℝ≥0 → X}
    (hc : ∀ ω ∈ G, Continuous (γ ω) ∧ Continuous (α ω) ∧ Continuous (β ω))
    (hm : ∀ q : ℚ, Measurable (fun ω => γ ω (rt q)) ∧ Measurable (fun ω => α ω (rt q)) ∧
      Measurable (fun ω => β ω (rt q)))
    (hGae : ∀ᵐ ω ∂P, ω ∈ G) {y : X} (hconf : ∀ᵐ ω ∂P, IsSelectionConfig (γ ω) (α ω) (β ω) y)
    (hchange : ∀ r : ℚ, 0 < r → ∀ᵐ ω ∂P, Continuous (βr r ω) ∧ βr r ω (rt r) = β ω (rt r) ∧
      (Antitone fun t => firstVisit (γ ω) (βr r ω t)) ∧ Antitone fun t => firstVisit (γ ω) (α ω t)) :
    ∃ r : ℚ, 0 < r ∧ 0 < P (contactEvent α (βr r) r) := by
  obtain ⟨r, hr, -, hpos⟩ := exists_rat_measure_selEvent_pos hG hc hm hGae hconf
  refine ⟨r, hr, lt_of_lt_of_le hpos (measure_mono_ae ?_)⟩
  filter_upwards [hchange r hr] with ω hω hmem
  exact hmem.2.isContactPoint hω.1 hω.2.1 hω.2.2.1 hω.2.2.2

/-- **Aux. lemma 130's event `F_r`, measurable from the incoming paths and of positive probability**: in addition,
for any σ-algebra `𝓔` (the complete labelled incoming paths) making the rational-time values of `α` and of every
`β^{(r)}` measurable, and an `𝓔`-measurable almost sure set `G'` on which these paths are continuous, the event
`G' ∩ F_r` is `𝓔`-measurable and has positive probability ("The event and the selected component are measurable from
their complete labeled incoming paths alone"). -/
theorem exists_rat_contactEvent {P : Measure Ω} [NeZero P] {G : Set Ω} (hG : MeasurableSet G)
    {γ α β : Ω → ℝ≥0 → X} {βr : ℚ → Ω → ℝ≥0 → X}
    (hc : ∀ ω ∈ G, Continuous (γ ω) ∧ Continuous (α ω) ∧ Continuous (β ω))
    (hm : ∀ q : ℚ, Measurable (fun ω => γ ω (rt q)) ∧ Measurable (fun ω => α ω (rt q)) ∧
      Measurable (fun ω => β ω (rt q)))
    (hGae : ∀ᵐ ω ∂P, ω ∈ G) {y : X} (hconf : ∀ᵐ ω ∂P, IsSelectionConfig (γ ω) (α ω) (β ω) y)
    (hchange : ∀ r : ℚ, 0 < r → ∀ᵐ ω ∂P, Continuous (βr r ω) ∧ βr r ω (rt r) = β ω (rt r) ∧
      (Antitone fun t => firstVisit (γ ω) (βr r ω t)) ∧ Antitone fun t => firstVisit (γ ω) (α ω t))
    (𝓔 : MeasurableSpace Ω) {G' : Set Ω} (hG' : MeasurableSet[𝓔] G') (hG'ae : ∀ᵐ ω ∂P, ω ∈ G')
    (hc' : ∀ ω ∈ G', Continuous (α ω) ∧ ∀ r : ℚ, Continuous (βr r ω))
    (hm' : ∀ q : ℚ, Measurable[𝓔] (fun ω => α ω (rt q)) ∧ ∀ r : ℚ, Measurable[𝓔] (fun ω => βr r ω (rt q))) :
    ∃ r : ℚ, 0 < r ∧ MeasurableSet[𝓔] (G' ∩ contactEvent α (βr r) r) ∧
      0 < P (G' ∩ contactEvent α (βr r) r) := by
  obtain ⟨r, hr, hpos⟩ := exists_rat_measure_contactEvent_pos (mΩ := mΩ) hG hc hm hGae hconf hchange
  refine ⟨r, hr, measurableSet_inter_contactEvent (mΩ := 𝓔) hG' (fun ω hω => ⟨(hc' ω hω).1, (hc' ω hω).2 r⟩)
    (fun q => ⟨(hm' q).1, (hm' q).2 r⟩) hr.le, lt_of_lt_of_le hpos (measure_mono_ae ?_)⟩
  filter_upwards [hG'ae] with ω hω hmem
  exact ⟨hω, hmem⟩

end Reference

/-! ### The selected Jordan pocket (Aux. lemma 33 on `F_r`) -/

section Pocket

/-- **The pocket selected on `F_r`, in Aux. lemma 33's crosscut parametrization** (p. 412: "Parametrize the two
completed simple paths on `[0, 1]` to apply Aux. lemma 33. […] The gap in the second path's contact set containing
its change point has `y₀` as its upper endpoint. Its lower endpoint `x₀` and the corresponding gap of the first path
give exactly the Jordan pocket asserted there. In particular the second change lies strictly inside its selected open
arc"): for disc crosscuts `α̃` (first path) and `β̃` (second path), a change parameter `c` of `β̃` whose point is off
the first path, and the crosscut form of `F_r` (every visit of the first prefix `α̃([0, p])` after `c` is preceded by
a visit of `α̃`), the contact gap `(a, b)` of `β̃` containing `c` has its upper contact `β̃(b)` off `α̃([0, p])`, i.e.
strictly after the first change `p` along the first path. Its pocket is a Jordan pocket by `WangWu.pocket_props`. -/
theorem exists_isContactGap_upper_notMem {α β : ℝ → ℂ} (hα : WangWu.IsDiscCrosscut α) (hβ : WangWu.IsDiscCrosscut β)
    {c p : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (hcα : β c ∉ α '' Icc 0 1)
    (hF : ∀ s ∈ Icc c 1, β s ∈ α '' Icc 0 p → ∃ u ∈ Ico c s, β u ∈ α '' Icc 0 1) :
    ∃ a b, WangWu.IsContactGap β α a b ∧ c ∈ Ioo a b ∧ β b ∉ α '' Icc 0 p := by
  have hcS : c ∉ pocketContactSet β α := fun h => hcα h.2
  obtain ⟨a, b, hgap, hcab⟩ := Aux130.exists_isContactGap_of_notMem hβ hα hc hcS
  refine ⟨a, b, hgap, hcab, fun hbp => ?_⟩
  have hb1 : b ∈ Icc c 1 := ⟨hcab.2.le, hgap.2.1.1.2⟩
  obtain ⟨u, hu, huα⟩ := hF b hb1 hbp
  rcases eq_or_lt_of_le hu.1 with rfl | hcu
  · exact hcα huα
  · exact hgap.2.2.2 u ⟨hcab.1.trans hcu, hu.2⟩ ⟨⟨hgap.1.1.1.trans hcab.1.le |>.trans hcu.le, hu.2.le.trans
      hgap.2.1.1.2⟩, huα⟩

end Pocket

end StripSys

end Sec7

end InteractingSLE
