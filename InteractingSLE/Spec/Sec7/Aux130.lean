/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ChamberPocket
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# §7.4, Aux. lemma 130: the point-set steps of the nondegenerate two-angle reference

Packet PROVE-AUX119-130. Specification §7.4.1, Aux. lemma 130 and its proof (`source/spec/p385-432.md` L401–L489,
pp. 408–413).

The proof of Aux. lemma 130 combines probabilistic inputs about the non-boundary centred strip coupling (continuity,
simplicity and determination of the angle-varying incoming paths; Lemma 5.7's reverse containment in the counterflow
range; non-boundary duality; the local-set boundary comparison behind (RS13.3)) with elementary point-set arguments
about one realization. This file proves the point-set arguments, for an arbitrary continuous curve `γ` (the
counterflow, in a fixed compactification) in a Hausdorff space `X` and paths `α`, `β` in `X`:

* **First visits** (`firstVisit γ z = inf {t : γ t = z}`, `⊤` if `z` is never visited): "For a point in the completed
  counterflow range let `T(z)` be its first counterflow visit time". A finite first visit is attained
  (`apply_firstVisit`); the sublevel sets are the compact initial ranges (`setOf_firstVisit_le`), so `T` is lower
  semicontinuous and Borel (`lowerSemicontinuous_firstVisit`, `measurable_firstVisit`: "first visits to a point are
  measurable functions of a continuous path and the point, since membership in each compact initial range is
  measurable").
* **Strict decrease along an incoming path** (`firstVisit_lt_of_lt`): "Distinct points of an incoming path have
  strictly decreasing `T` in its incoming order: reverse containment gives weak decrease, and equality at a finite
  time would make a continuous curve occupy two distinct points at that time."
* **(RS13.2)** (`tendsto_firstVisit_zero`): along an incoming path visited in reverse order, with finite first visits
  at positive times and limit `y` visited by `γ` only at time `0`, the first visits tend to `0`.
* **(RS13.4), the rational choice** (`exists_rat_notMem_firstVisit_lt`): if the path has points outside a closed set
  `K` (the complete range of `α`) at arbitrarily late times and its first visits tend to `0`, then for every point
  `p` with `0 < T(p)` some positive rational `r` has `β r ∉ K` and `T(β r) < T(p)`.
* **The first subsequent contact** (`exists_firstContact`): from a time `r` with `β r ∉ K` and a later contact, there
  is a first contact time `b > r`.
* **(RS13.5)** (`one_lt_of_firstVisit_lt`): a contact `α b` with `T(α b) < T(α 1)` on a path visited in reverse order
  has `b > 1`.
* **(RS13.3)** (`sub_half_pi_ne_two_pi_mul_int`): `θ₁ − π/2 = 2πn` has no integer solution for `θ₁ ∈ (−π/2, π/2)`.
* **The gap of a contact set containing a non-contact parameter** (`exists_isContactGap_of_notMem`): with the
  crosscut parametrization of Aux. lemma 33 (`WangWu.IsContactGap`), every parameter in `[0, 1]` off the closed
  contact set lies in a contact gap, whose pocket is a Jordan pocket by `WangWu.pocket_props` ("The gap in the second
  path's contact set containing its change point … give exactly the Jordan pocket asserted there").
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal Real

namespace InteractingSLE

namespace Sec7

namespace Aux130

variable {X : Type*}

/-! ### First visits -/

/-- The first visit time of `z` by the curve `γ`: `inf {t : γ t = z}` in `ℝ≥0∞`, and `⊤` if `γ` never visits `z`
("For a point in the completed counterflow range let `T(z)` be its first counterflow visit time"). -/
def firstVisit (γ : ℝ≥0 → X) (z : X) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : γ t = z), (t : ℝ≥0∞)

theorem firstVisit_le {γ : ℝ≥0 → X} {z : X} {t : ℝ≥0} (h : γ t = z) : firstVisit γ z ≤ t :=
  iInf₂_le t h

theorem le_firstVisit_iff {γ : ℝ≥0 → X} {z : X} {c : ℝ≥0∞} :
    c ≤ firstVisit γ z ↔ ∀ t : ℝ≥0, γ t = z → c ≤ t := by
  simp only [firstVisit, le_iInf_iff]

theorem firstVisit_eq_top_iff {γ : ℝ≥0 → X} {z : X} : firstVisit γ z = ⊤ ↔ ∀ t, γ t ≠ z := by
  refine ⟨fun h t ht => ?_, fun h => ?_⟩
  · have := firstVisit_le ht
    rw [h] at this
    exact ENNReal.coe_ne_top (top_le_iff.1 this)
  · exact top_le_iff.1 (le_firstVisit_iff.2 fun t ht => absurd ht (h t))

theorem firstVisit_lt_top_iff {γ : ℝ≥0 → X} {z : X} : firstVisit γ z < ⊤ ↔ ∃ t, γ t = z := by
  rw [lt_top_iff_ne_top, Ne, firstVisit_eq_top_iff]
  push Not
  rfl

/-- The first visit is the infimum, in `ℝ≥0`, of the (nonempty) visit set. -/
theorem firstVisit_eq_coe_sInf {γ : ℝ≥0 → X} {z : X} (hne : ∃ t, γ t = z) :
    firstVisit γ z = ((sInf {t | γ t = z} : ℝ≥0) : ℝ≥0∞) := by
  rw [ENNReal.coe_sInf (s := {t : ℝ≥0 | γ t = z}) hne]
  rfl

variable [TopologicalSpace X] [T2Space X]

/-- **A finite first visit is attained**: the visit set of a point is closed. -/
theorem apply_firstVisit {γ : ℝ≥0 → X} (hγ : Continuous γ) {z : X} (hT : firstVisit γ z < ⊤) :
    γ (firstVisit γ z).toNNReal = z := by
  have hne := firstVisit_lt_top_iff.1 hT
  rw [firstVisit_eq_coe_sInf hne, ENNReal.toNNReal_coe]
  exact (isClosed_singleton.preimage hγ).csInf_mem hne (OrderBot.bddBelow _)

/-- The first visit time is attained: `γ (T z) = z` when `T z = t` is finite. -/
theorem apply_of_firstVisit_eq {γ : ℝ≥0 → X} (hγ : Continuous γ) {z : X} {t : ℝ≥0}
    (hT : firstVisit γ z = t) : γ t = z := by
  have h := apply_firstVisit hγ (z := z) (by rw [hT]; exact ENNReal.coe_lt_top)
  rwa [hT, ENNReal.toNNReal_coe] at h

/-- **The sublevel sets of the first visit are the initial ranges.** -/
theorem setOf_firstVisit_le {γ : ℝ≥0 → X} (hγ : Continuous γ) (t : ℝ≥0) :
    {z | firstVisit γ z ≤ t} = γ '' Icc 0 t := by
  ext z
  refine ⟨fun h => ?_, ?_⟩
  · have hlt : firstVisit γ z < ⊤ := lt_of_le_of_lt h ENNReal.coe_lt_top
    refine ⟨(firstVisit γ z).toNNReal, ⟨bot_le, ?_⟩, apply_firstVisit hγ hlt⟩
    have := (ENNReal.toNNReal_le_toNNReal hlt.ne ENNReal.coe_ne_top).2 h
    rwa [ENNReal.toNNReal_coe] at this
  · rintro ⟨s, hs, rfl⟩
    exact (firstVisit_le rfl).trans (ENNReal.coe_le_coe.2 hs.2)

/-- The sublevel sets of the first visit are compact. -/
theorem isCompact_setOf_firstVisit_le {γ : ℝ≥0 → X} (hγ : Continuous γ) (t : ℝ≥0) :
    IsCompact {z | firstVisit γ z ≤ t} := by
  rw [setOf_firstVisit_le hγ]
  exact isCompact_Icc.image hγ

/-- **The first visit is lower semicontinuous** (its sublevel sets are compact initial ranges). -/
theorem lowerSemicontinuous_firstVisit {γ : ℝ≥0 → X} (hγ : Continuous γ) :
    LowerSemicontinuous (firstVisit γ) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro c
  rcases eq_or_ne c ⊤ with rfl | hc
  · rw [Iic_top, preimage_univ]
    exact isClosed_univ
  · have : firstVisit γ ⁻¹' Iic c = {z | firstVisit γ z ≤ c.toNNReal} := by
      ext z
      show firstVisit γ z ≤ c ↔ firstVisit γ z ≤ (c.toNNReal : ℝ≥0∞)
      rw [ENNReal.coe_toNNReal hc]
    rw [this]
    exact (isCompact_setOf_firstVisit_le hγ _).isClosed

/-- **First visits are Borel functions of the point** ("first visits to a point are measurable functions of a
continuous path and the point, since membership in each compact initial range is measurable"). -/
theorem measurable_firstVisit [MeasurableSpace X] [OpensMeasurableSpace X] {γ : ℝ≥0 → X}
    (hγ : Continuous γ) : Measurable (firstVisit γ) :=
  (lowerSemicontinuous_firstVisit hγ).measurable

/-! ### Strict decrease along an incoming path -/

/-- **Strict decrease of first visits along an injective incoming path** (proof of Aux. lemma 130, p. 410): if the
first visits along `β` are weakly decreasing (reverse containment) and `β` is injective, then `s < t` and a finite
first visit of `β t` give `T(β t) < T(β s)`. -/
theorem firstVisit_lt_of_lt {γ : ℝ≥0 → X} (hγ : Continuous γ) {β : ℝ≥0 → X} (hβ : Function.Injective β)
    (hrev : Antitone fun t => firstVisit γ (β t)) {s t : ℝ≥0} (hst : s < t)
    (hfin : firstVisit γ (β t) < ⊤) : firstVisit γ (β t) < firstVisit γ (β s) := by
  refine lt_of_le_of_ne (hrev hst.le) fun heq => hst.ne ?_
  have h1 := apply_firstVisit hγ hfin
  have h2 := apply_firstVisit hγ (heq ▸ hfin)
  rw [heq] at h1
  exact hβ (h2.symm.trans h1)

/-! ### (RS13.2) -/

/-- **(RS13.2)**: first visits along an incoming path tend to `0`. Let the first visits along `β` be weakly
decreasing and finite at positive times, let `β t → y`, and let `γ` visit `y` only at time `0` (the counterflow's
non-hit property on the original boundary; `y` is its seed). Then `T(β t) → 0`: "the left side is nonincreasing, is
finite for `t > 0`, and therefore has a finite limit `ℓ ≥ 0`. If `ℓ > 0`, continuity of the counterflow and
`β(t) → y` imply that the counterflow visits `y` again at time `ℓ`." -/
theorem tendsto_firstVisit_zero {γ : ℝ≥0 → X} (hγ : Continuous γ) {β : ℝ≥0 → X}
    (hrev : Antitone fun t => firstVisit γ (β t)) (hfin : ∀ t, 0 < t → firstVisit γ (β t) < ⊤) {y : X}
    (hβy : Tendsto β atTop (𝓝 y)) (hy : ∀ t : ℝ≥0, 0 < t → γ t ≠ y) :
    Tendsto (fun t => firstVisit γ (β t)) atTop (𝓝 0) := by
  set L := ⨅ t, firstVisit γ (β t) with hL
  have hlim : Tendsto (fun t => firstVisit γ (β t)) atTop (𝓝 L) := tendsto_atTop_iInf hrev
  have hLtop : L ≠ ⊤ := ne_top_of_le_ne_top (hfin 1 one_pos).ne (iInf_le _ 1)
  -- the curve visits `y` at time `L`
  have hlim' : Tendsto (fun t => (firstVisit γ (β t)).toNNReal) atTop (𝓝 L.toNNReal) :=
    (ENNReal.tendsto_toNNReal hLtop).comp hlim
  have hγL : γ L.toNNReal = y := by
    have h1 : Tendsto (fun t => γ (firstVisit γ (β t)).toNNReal) atTop (𝓝 (γ L.toNNReal)) :=
      (hγ.tendsto _).comp hlim'
    have h2 : Tendsto (fun t => γ (firstVisit γ (β t)).toNNReal) atTop (𝓝 y) := by
      refine hβy.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      exact (apply_firstVisit hγ (hfin t ht)).symm
    exact tendsto_nhds_unique h1 h2
  have hL0 : L = 0 := by
    by_contra hne
    have hpos : 0 < L.toNNReal := ENNReal.toNNReal_pos hne hLtop
    exact hy _ hpos hγL
  rwa [hL0] at hlim

/-! ### (RS13.4): the rational choice -/

omit [T2Space X] in
/-- **(RS13.4), the rational choice** (proof of Aux. lemma 130, p. 411): "By (RS13.2), and by the preceding
no-terminal-arc conclusion, almost surely there is a rational `r > 0` such that `β(r) ∉ α([0, ∞])` and
`T(β(r)) < T(p)` … The nonmembership condition is open in the finite parameter of `β`, since that complete range is
compact … Once the second inequality holds at a sufficiently late time, its monotonicity makes it hold at every later
time." Pathwise: if `β` is continuous, `K` is closed, `β` leaves `K` at arbitrarily late times, the first visits along
`β` tend to `0`, and `0 < T(p)`, then some positive rational time works. -/
theorem exists_rat_notMem_firstVisit_lt {γ β : ℝ≥0 → X} (hβ : Continuous β) {K : Set X} (hK : IsClosed K)
    (hlate : ∀ N : ℝ≥0, ∃ t, N ≤ t ∧ β t ∉ K)
    (hT : Tendsto (fun t => firstVisit γ (β t)) atTop (𝓝 0)) {p : X} (hp : 0 < firstVisit γ p) :
    ∃ r : ℚ, 0 < r ∧ β (r : ℝ).toNNReal ∉ K ∧ firstVisit γ (β (r : ℝ).toNNReal) < firstVisit γ p := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hT.eventually (gt_mem_nhds hp))
  obtain ⟨t, hNt, htK⟩ := hlate N
  have hU : IsOpen {s : ℝ≥0 | β s ∉ K} := hK.isOpen_compl.preimage hβ
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU t htK
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show (t : ℝ) < t + ε by linarith)
  have hr0 : (0 : ℝ) < r := lt_of_le_of_lt t.2 hr1
  have htr : t ≤ (r : ℝ).toNNReal := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0.le]
    exact hr1.le
  refine ⟨r, by exact_mod_cast hr0, ?_, hN _ (hNt.trans htr)⟩
  apply hball
  rw [Metric.mem_ball, NNReal.dist_eq, Real.coe_toNNReal _ hr0.le, abs_lt]
  constructor <;> linarith

/-! ### The first subsequent contact -/

omit [T2Space X] in
/-- **The first subsequent common contact** (proof of Aux. lemma 130, p. 412): "let `y₀` be the first point of
`β^{(r)}([r, ∞])` in the complete range of `α`. It exists because both completed paths end at `y`. It occurs
strictly after `r`, because the starting point `β(r)` has positive distance from that compact range." For a
continuous path `β`, a closed set `K`, `β r ∉ K` and a contact `β t ∈ K` at a time `t ≥ r`, there is a first contact
time `b ∈ (r, t]`. -/
theorem exists_firstContact {β : ℝ≥0 → X} (hβ : Continuous β) {K : Set X} (hK : IsClosed K) {r t : ℝ≥0}
    (hr : β r ∉ K) (hrt : r ≤ t) (ht : β t ∈ K) :
    ∃ b, r < b ∧ b ≤ t ∧ β b ∈ K ∧ ∀ s, r ≤ s → s < b → β s ∉ K := by
  set S : Set ℝ≥0 := Ici r ∩ β ⁻¹' K with hS
  have hSc : IsClosed S := isClosed_Ici.inter (hK.preimage hβ)
  have hSne : S.Nonempty := ⟨t, hrt, ht⟩
  have hbS : sInf S ∈ S := hSc.csInf_mem hSne (OrderBot.bddBelow _)
  refine ⟨sInf S, lt_of_le_of_ne hbS.1 fun h => hr (h ▸ hbS.2),
    csInf_le (OrderBot.bddBelow S) (show t ∈ S from ⟨hrt, ht⟩), hbS.2, fun s hrs hsb hsK => ?_⟩
  exact absurd (csInf_le (OrderBot.bddBelow S) (show s ∈ S from ⟨hrs, hsK⟩)) (not_le.2 hsb)

/-! ### (RS13.5) and (RS13.3) -/

omit [TopologicalSpace X] [T2Space X] in
/-- **(RS13.5)** (proof of Aux. lemma 130, p. 412): "If `y₀ = α(b)`, reverse first-visit order gives
`T(α(b)) ≤ T(β(r)) < T(α(1))`, hence `b > 1`." On a path visited in reverse order, a strictly earlier first visit
than at `α c` comes from a strictly later parameter. -/
theorem lt_of_firstVisit_lt {γ α : ℝ≥0 → X} (hrev : Antitone fun t => firstVisit γ (α t)) {b c : ℝ≥0}
    (h : firstVisit γ (α b) < firstVisit γ (α c)) : c < b :=
  lt_of_not_ge fun hbc => absurd (hrev hbc) (not_le.2 h)

/-- **(RS13.3) has no solution** (proof of Aux. lemma 130, p. 411): "`θ₁ − π/2 = 2πn` … is impossible because
`−π < θ₁ − π/2 < 0`." -/
theorem sub_half_pi_ne_two_pi_mul_int {θ : ℝ} (h1 : -(π / 2) < θ) (h2 : θ < π / 2) (n : ℤ) :
    θ - π / 2 ≠ 2 * π * n := by
  intro h
  have hn1 : (n : ℝ) < 0 := by nlinarith [Real.pi_pos]
  have hn2 : (-1 : ℝ) < n := by nlinarith [Real.pi_pos]
  have a : n < 0 := by exact_mod_cast hn1
  have b : -1 < n := by exact_mod_cast hn2
  omega

/-! ### The contact gap containing a non-contact parameter -/

/-- **A closed set has a gap around each of its non-points**: for a closed `S ⊆ ℝ` and `c ∉ S` between two points
`a₀ ≤ c ≤ b₀` of `S`, the largest point of `S` below `c` and the smallest above bound an open interval around `c`
avoiding `S` ("the endpoints are the infimum and supremum of their closed contact-parameter sets"). -/
theorem exists_gap_of_notMem {S : Set ℝ} (hS : IsClosed S) {a₀ b₀ c : ℝ} (ha₀ : a₀ ∈ S) (hb₀ : b₀ ∈ S)
    (hac : a₀ ≤ c) (hcb : c ≤ b₀) (hc : c ∉ S) :
    ∃ a b, a ∈ S ∧ b ∈ S ∧ a < c ∧ c < b ∧ ∀ s ∈ Ioo a b, s ∉ S := by
  set SL := S ∩ Icc a₀ c with hSL
  set SR := S ∩ Icc c b₀ with hSR
  have hSLc : IsClosed SL := hS.inter isClosed_Icc
  have hSRc : IsClosed SR := hS.inter isClosed_Icc
  have hSLne : SL.Nonempty := ⟨a₀, ha₀, le_rfl, hac⟩
  have hSRne : SR.Nonempty := ⟨b₀, hb₀, hcb, le_rfl⟩
  have hSLb : BddAbove SL := ⟨c, fun x hx => hx.2.2⟩
  have hSRb : BddBelow SR := ⟨c, fun x hx => hx.2.1⟩
  have haS : sSup SL ∈ SL := hSLc.csSup_mem hSLne hSLb
  have hbS : sInf SR ∈ SR := hSRc.csInf_mem hSRne hSRb
  have hac' : sSup SL < c := lt_of_le_of_ne haS.2.2 fun h => hc (h ▸ haS.1)
  have hcb' : c < sInf SR := lt_of_le_of_ne hbS.2.1 fun h => hc (h ▸ hbS.1)
  refine ⟨sSup SL, sInf SR, haS.1, hbS.1, hac', hcb', fun s hs hsS => ?_⟩
  rcases le_total s c with hsc | hcs
  · have : s ≤ sSup SL := le_csSup hSLb ⟨hsS, haS.2.1.trans hs.1.le, hsc⟩
    exact absurd hs.1 (not_lt.2 this)
  · have : sInf SR ≤ s := csInf_le hSRb ⟨hsS, hcs, hs.2.le.trans hbS.2.2⟩
    exact absurd hs.2 (not_lt.2 this)

/-- **The contact gap containing a non-contact parameter** (proof of Aux. lemma 130, p. 412, with Aux. lemma 33):
for two disc crosscuts, every parameter `c ∈ [0, 1]` off the contact set lies in a contact gap; with the ordering
hypothesis of `WangWu.pocket_props`, the pocket of that gap is a Jordan pocket bounded by the two open selected
arcs. -/
theorem exists_isContactGap_of_notMem {α β : ℝ → ℂ} (hα : WangWu.IsDiscCrosscut α)
    (hβ : WangWu.IsDiscCrosscut β) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (hcS : c ∉ pocketContactSet α β) :
    ∃ a b, WangWu.IsContactGap α β a b ∧ c ∈ Ioo a b := by
  obtain ⟨a, b, ha, hb, hac, hcb, hgap⟩ :=
    exists_gap_of_notMem (WangWu.isClosed_pocketContactSet hα hβ) (WangWu.zero_mem_pocketContactSet hα hβ)
      (WangWu.one_mem_pocketContactSet hα hβ) hc.1 hc.2 hcS
  exact ⟨a, b, ⟨ha, hb, hac.trans hcb, hgap⟩, hac, hcb⟩

end Aux130

end Sec7

end InteractingSLE
