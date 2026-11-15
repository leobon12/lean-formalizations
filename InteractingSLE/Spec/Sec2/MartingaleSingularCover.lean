import InteractingSLE.Spec.Sec2.MartingaleSingular
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Theorem 2.4, converse implication: the singular force-point motions vanish

Packet PROVE-SEC2-MART2 (step R1 of `planning/handoffs/PROVE-SEC2-MART.md`). Specification, proof of
Theorem 2.4 (`source/spec/p001-048.md`, anchor `thm-2.4-proof`, L900–L925; graph node
`SPEC.thm-2.4#no-singular-motion`): "A countable cover of the collision times by the local
intervals just used, together with the absence of atoms at merging times, proves `Iʲ ≡ 0` for every
force point."

The local statements of `MartingaleSingular` (`ae_forceDefect_const_of_group`) hold simultaneously
for all groups `S`, rational starting times and integer horizons, outside one null set. Pathwise,
the defect `I^{i₀}` of the left point nearest to the driver is then locally constant at every time
before the continuation threshold except the finitely many first merging times
(`forceDefect_eq_zero_of_forall_group`); a continuous function with zero derivative off a
countable set is constant (Mathlib's `integral_eq_of_hasDerivAt_off_countable_of_le`). The other
left points share the defect of `V^{i₀}` after merging with it and have none before
(`forceDefect_eq_zero_of_nearest`). The right side follows by reflection `x ↦ −x`.

## Main results

* `ae_forceDefect_left_eq_zero`, `ae_forceDefect_right_eq_zero`: almost surely, every defect
  vanishes up to every time `T` before which the continuation threshold is not met.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace MartChar

/-! ### Local constancy gives a zero derivative -/

lemma hasDerivAt_toNNReal_of_const {φ : ℝ≥0 → ℝ} {x ε : ℝ} (hx : 0 < x) (hε : 0 < ε)
    (h : ∀ a b : ℝ≥0, a ≤ b → |(a : ℝ) - x| < ε → |(b : ℝ) - x| < ε → φ a = φ b) :
    HasDerivAt (fun y : ℝ => φ y.toNNReal) 0 x := by
  have hev : (fun y : ℝ => φ y.toNNReal) =ᶠ[𝓝 x] fun _ => φ x.toNNReal := by
    have hball : ∀ᶠ y in 𝓝 x, |y - x| < ε := by
      filter_upwards [Metric.ball_mem_nhds x hε] with y hy
      rwa [Metric.mem_ball, Real.dist_eq] at hy
    filter_upwards [hball] with y hy
    have h1 : |((y.toNNReal : ℝ)) - x| < ε := by
      rcases le_or_gt 0 y with hy0 | hy0
      · rwa [Real.coe_toNNReal _ hy0]
      · rw [Real.toNNReal_of_nonpos hy0.le, NNReal.coe_zero, zero_sub, abs_neg, abs_of_pos hx]
        have := (abs_lt.1 hy).1
        linarith
    have h2 : |((x.toNNReal : ℝ)) - x| < ε := by
      rw [Real.coe_toNNReal _ hx.le, sub_self, abs_zero]; exact hε
    rcases le_total y.toNNReal x.toNNReal with hle | hle
    · exact h _ _ hle h1 h2
    · exact (h _ _ hle h2 h1).symm
  exact (hasDerivAt_const x (φ x.toNNReal)).congr_of_eventuallyEq hev

lemma abs_sub_lt_of_mem_Icc {a b r x ε : ℝ} (ha : |a - x| < ε) (hb : |b - x| < ε) (har : a ≤ r)
    (hrb : r ≤ b) : |r - x| < ε := by
  rw [abs_lt] at ha hb ⊢
  constructor <;> linarith [ha.1, hb.2]

/-- A property that holds near `x` at the times `y.toNNReal` holds at the nearby times. -/
lemma exists_pos_forall_of_eventually {p : ℝ≥0 → Prop} {x : ℝ}
    (h : ∀ᶠ y in 𝓝 x, p y.toNNReal) : ∃ ε > 0, ∀ r : ℝ≥0, |(r : ℝ) - x| < ε → p r := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨ε, hε, fun r hr => ?_⟩
  have := hball (y := (r : ℝ)) (by rwa [Real.dist_eq])
  rwa [Real.toNNReal_coe] at this

/-! ### The covering argument for the nearest left point -/

section Cover

variable {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ}
  {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}

/-- The pathwise conclusion of the local Tanaka steps, for all groups, rational starting times
and all later times. -/
def GroupConst (ρL : Fin nL → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (i₀ : Fin nL) : Prop :=
  ∀ S : Finset (Fin nL), 1 + (1 / 2) * ∑ i ∈ S, ρL i ≠ 0 → ∀ q : ℚ, 0 ≤ q →
    (∀ i, vL i (q : ℝ).toNNReal = vL i₀ (q : ℝ).toNNReal ↔ i ∈ S) → ∀ u, (q : ℝ).toNNReal ≤ u →
    (∀ r, (q : ℝ).toNNReal ≤ r → r ≤ u → (∀ i ∉ S, vL i r ≠ vL i₀ r) ∧ ∀ j, vR j r ≠ w r) →
    forceDefect w (vL i₀) u = forceDefect w (vL i₀) (q : ℝ).toNNReal

/-- **The nearest left point has no singular motion before the threshold** (pathwise). -/
theorem forceDefect_eq_zero_of_groupConst (hwc : Continuous w)
    (hpL : ∀ i, IsForcePath w (vL i)) (hpR : ∀ j, IsForcePath w (vR j))
    (hmerge : ∀ i j s t, s ≤ t → vL i s = vL j s → vL i t = vL j t) {i₀ : Fin nL}
    (hsep : ∀ t, 0 < t → vL i₀ t = w t → ∀ j, vR j t ≠ w t)
    (hgood : GroupConst ρL w vL vR i₀) {T : ℝ≥0}
    (hT : ∀ u ≤ T, ¬ ForceWord.ThresholdCondition ρL ρR (w u) (fun i => vL i u)
      (fun j => vR j u)) :
    forceDefect w (vL i₀) T = 0 := by
  have hcL : ∀ i, Continuous (vL i) := fun i => (hpL i).1
  have hcR : ∀ j, Continuous (vR j) := fun j => (hpR j).1
  set f : ℝ → ℝ := fun y => forceDefect w (vL i₀) y.toNNReal with hf
  set m : Fin nL → ℝ := fun i => ((sInf {r : ℝ≥0 | vL i r = vL i₀ r} : ℝ≥0) : ℝ) with hm
  have hFc : (insert (0 : ℝ) (range m)).Countable := (countable_range m).insert 0
  have hfc : Continuous f := (hpL i₀).continuous_forceDefect.comp continuous_real_toNNReal
  have hd : ∀ x ∈ Ioo (0 : ℝ) T \ insert (0 : ℝ) (range m), HasDerivAt f 0 x := by
    rintro x ⟨⟨hx0, hxT⟩, hxF⟩
    have hxm : ∀ i, m i ≠ x := fun i h => hxF (Or.inr ⟨i, h⟩)
    set u := x.toNNReal with hu
    have hux : (u : ℝ) = x := Real.coe_toNNReal _ hx0.le
    have huT : u ≤ T := Real.toNNReal_le_iff_le_coe.2 hxT.le
    have hu0 : 0 < u := Real.toNNReal_pos.2 hx0
    have hcont : ∀ g : ℝ≥0 → ℝ, Continuous g → ContinuousAt (fun y : ℝ => g y.toNNReal) x :=
      fun g hg => (hg.comp continuous_real_toNNReal).continuousAt
    have hne2 : ∀ g₁ g₂ : ℝ≥0 → ℝ, Continuous g₁ → Continuous g₂ → g₁ u ≠ g₂ u →
        ∀ᶠ y in 𝓝 x, g₁ y.toNNReal ≠ g₂ y.toNNReal := fun g₁ g₂ h1 h2 h =>
      (((hcont _ h1).sub (hcont _ h2)).eventually_ne
        (sub_ne_zero.2 h : g₁ x.toNNReal - g₂ x.toNNReal ≠ 0)).mono fun y hy => sub_ne_zero.1 hy
    by_cases hcol : vL i₀ u = w u
    · -- a collision: use the local Tanaka step on a group interval
      set S := Finset.univ.filter fun i => vL i u = vL i₀ u with hSdef
      have hSw : (Finset.univ.filter fun i => vL i u = w u) = S :=
        Finset.filter_congr fun i _ => by rw [hcol]
      have hc : 1 + (1 / 2) * ∑ i ∈ S, ρL i ≠ 0 := by
        have h := hT u huT
        simp only [ForceWord.ThresholdCondition, not_or, not_le] at h
        rw [hSw] at h
        linarith [h.1]
      have hsepu := hsep u hu0 hcol
      have hE1 : ∀ᶠ y in 𝓝 x, ∀ j, vR j y.toNNReal ≠ w y.toNNReal :=
        Filter.eventually_all.2 fun j => hne2 _ _ (hcR j) hwc (hsepu j)
      have hE2 : ∀ᶠ y in 𝓝 x, ∀ i ∉ S, vL i y.toNNReal ≠ vL i₀ y.toNNReal := by
        refine Filter.eventually_all.2 fun i => ?_
        by_cases hi : i ∈ S
        · exact Eventually.of_forall fun y h => absurd hi h
        · have hne : vL i u ≠ vL i₀ u := by simpa [hSdef] using hi
          exact (hne2 _ _ (hcL i) (hcL i₀) hne).mono fun y hy _ => hy
      have hE3 : ∀ᶠ y in 𝓝 x, ∀ i ∈ S, vL i y.toNNReal = vL i₀ y.toNNReal := by
        refine Filter.eventually_all.2 fun i => ?_
        by_cases hi : i ∈ S
        · have hiu : vL i u = vL i₀ u := by simpa [hSdef] using hi
          have hle : sInf {r : ℝ≥0 | vL i r = vL i₀ r} ≤ u := csInf_le (OrderBot.bddBelow _) hiu
          have hlt : sInf {r : ℝ≥0 | vL i r = vL i₀ r} < u := by
            refine lt_of_le_of_ne hle fun h => hxm i ?_
            simp only [hm, h, hux]
          obtain ⟨r, hr, hru⟩ := exists_lt_of_csInf_lt ⟨u, hiu⟩ hlt
          have hrx : (r : ℝ) < x := by rw [← hux]; exact_mod_cast hru
          filter_upwards [Ioi_mem_nhds hrx] with y hy _
          exact hmerge i i₀ r _ ((Real.le_toNNReal_iff_coe_le
            ((NNReal.coe_nonneg r).trans hy.le)).2 hy.le) hr
        · exact Eventually.of_forall fun y h => absurd h hi
      obtain ⟨ε, hε, hP⟩ := exists_pos_forall_of_eventually
        (p := fun r => (∀ j, vR j r ≠ w r) ∧ (∀ i ∉ S, vL i r ≠ vL i₀ r) ∧
          ∀ i ∈ S, vL i r = vL i₀ r) (hE1.and (hE2.and hE3))
      refine hasDerivAt_toNNReal_of_const (ε := min ε x) hx0 (lt_min hε hx0)
        fun a b hab ha hb => ?_
      have ha' : x - min ε x < a := by linarith [(abs_lt.1 ha).1]
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn ha'
      have hq0 : (0 : ℝ) ≤ q := by linarith [min_le_right ε x]
      set s := (q : ℝ).toNNReal with hsdef
      have hqs : (s : ℝ) = q := Real.coe_toNNReal _ hq0
      have hPr : ∀ r : ℝ≥0, s ≤ r → r ≤ b → (∀ j, vR j r ≠ w r) ∧ (∀ i ∉ S, vL i r ≠ vL i₀ r) ∧
          ∀ i ∈ S, vL i r = vL i₀ r := fun r h1 h2 => by
        refine hP r (abs_lt.2 ⟨?_, ?_⟩)
        · have : (q : ℝ) ≤ r := hqs ▸ NNReal.coe_le_coe.2 h1
          linarith [min_le_left ε x]
        · have : (r : ℝ) ≤ b := h2
          linarith [(abs_lt.1 hb).2, min_le_left ε x]
      have hsa : s ≤ a := NNReal.coe_le_coe.1 (hqs ▸ hq2.le)
      have hgrp : ∀ i, vL i s = vL i₀ s ↔ i ∈ S := fun i => by
        obtain ⟨-, h2, h3⟩ := hPr s le_rfl (hsa.trans hab)
        refine ⟨fun h => ?_, h3 i⟩
        by_contra hi
        exact h2 i hi h
      have hq0' : (0 : ℚ) ≤ q := by exact_mod_cast hq0
      have hb' := hgood S hc q hq0' hgrp b (hsa.trans hab)
        fun r h1 h2 => ⟨(hPr r h1 h2).2.1, (hPr r h1 h2).1⟩
      have ha'' := hgood S hc q hq0' hgrp a hsa
        fun r h1 h2 => ⟨(hPr r h1 (h2.trans hab)).2.1, (hPr r h1 (h2.trans hab)).1⟩
      exact ha''.trans hb'.symm
    · -- no collision: the defect is locally constant
      have hev := hne2 _ _ (hcL i₀) hwc hcol
      obtain ⟨ε, hε, hP⟩ := exists_pos_forall_of_eventually (p := fun r => vL i₀ r ≠ w r) hev
      refine hasDerivAt_toNNReal_of_const hx0 hε fun a b hab ha hb => ?_
      exact ((hpL i₀).forceDefect_eq_of_forall_ne hab fun r hr =>
        hP r (abs_sub_lt_of_mem_Icc ha hb hr.1 hr.2)).symm
  have hint := integral_eq_of_hasDerivAt_off_countable_of_le f (fun _ => (0 : ℝ))
    (NNReal.coe_nonneg T) hFc hfc.continuousOn hd intervalIntegrable_const
  simp only [intervalIntegral.integral_zero, hf, Real.toNNReal_coe, Real.toNNReal_zero] at hint
  have h0 : forceDefect w (vL i₀) 0 = 0 := by simp [forceDefect]
  linarith

/-- **The other left points.** A left point has no defect before it merges with the nearest one
and shares its defect afterwards. -/
theorem forceDefect_eq_zero_of_nearest (hpL : ∀ i, IsForcePath w (vL i))
    (hordL : ∀ t i, vL i t ≤ w t) (hmerge : ∀ i j s t, s ≤ t → vL i s = vL j s → vL i t = vL j t)
    {i₀ : Fin nL} (hi₀ : ∀ t i, vL i t ≤ vL i₀ t) {T : ℝ≥0}
    (h0 : ∀ u ≤ T, forceDefect w (vL i₀) u = 0) (i : Fin nL) : forceDefect w (vL i) T = 0 := by
  have hz : forceDefect w (vL i) 0 = 0 := by simp [forceDefect]
  have hcolm : ∀ r, vL i r = w r → vL i r = vL i₀ r := fun r hcol =>
    le_antisymm (hi₀ r i) (by rw [hcol]; exact hordL r i₀)
  by_cases hm : ∃ r ≤ T, vL i r = vL i₀ r
  · obtain ⟨r, hrT, hr⟩ := hm
    set M : Set ℝ≥0 := {r : ℝ≥0 | vL i r = vL i₀ r} with hM
    have hMc : IsClosed M := isClosed_eq (hpL i).1 (hpL i₀).1
    have hmM : sInf M ∈ M := hMc.csInf_mem ⟨r, hr⟩ (OrderBot.bddBelow _)
    have hmT : sInf M ≤ T := (csInf_le (OrderBot.bddBelow M) (show r ∈ M from hr)).trans hrT
    have h1 : forceDefect w (vL i) (sInf M) = forceDefect w (vL i) 0 :=
      (hpL i).forceDefect_eq_of_forall_ne_Ico (zero_le : (0 : ℝ≥0) ≤ sInf M)
        fun r _ hrm hcol => notMem_of_lt_csInf hrm (OrderBot.bddBelow M) (hcolm r hcol)
    have h2 : forceDefect w (vL i) T - forceDefect w (vL i) (sInf M)
        = forceDefect w (vL i₀) T - forceDefect w (vL i₀) (sInf M) :=
      (hpL i₀).forceDefect_sub_eq_of_eqOn (hpL i) hmT fun r hmr _ => hmerge i i₀ _ r hmr hmM
    have h3 := h0 T le_rfl
    have h4 := h0 _ hmT
    linarith
  · push Not at hm
    rw [(hpL i).forceDefect_eq_of_forall_ne (zero_le : (0 : ℝ≥0) ≤ T)
      fun r hr hcol => hm r hr.2 (hcolm r hcol), hz]

end Cover

/-! ### Almost surely, no singular motion before the threshold -/

section AlmostSure

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsProbabilityMeasure P] {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {β W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ}

/-- **Theorem 2.4, the singular motions vanish: left side.** -/
theorem ae_forceDefect_left_eq_zero {a : ℝ} (ha : a ≠ 0) (hβ : IsFilteredPreBrownian β 𝓕 P)
    (hβc : ∀ ω, Continuous fun t => β t ω)
    (hW : ∀ t ω, W t ω = a * β t ω
      - (1 / 2) * ((∑ i, ρL i * (VL i t ω - xL i)) + ∑ j, ρR j * (VR j t ω - xR j)))
    (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓕 W)
    (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i)) (hVRa : ∀ j, StronglyAdapted 𝓕 (VR j))
    (hpL : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VL i t ω))
    (hpR : ∀ ω j, IsForcePath (fun t => W t ω) (fun t => VR j t ω))
    (hordL : ∀ ω t i, VL i t ω ≤ W t ω) (hantiL : ∀ ω i, Antitone fun t => VL i t ω)
    (hmonoR : ∀ ω j, Monotone fun t => VR j t ω)
    (hmerge : ∀ ω i j s t, s ≤ t → VL i s ω = VL j s ω → VL i t ω = VL j t ω)
    (hidxL : ∀ ω t, Antitone fun i => VL i t ω)
    (hsep : ∀ ω t, 0 < t → ∀ i j, VL i t ω = W t ω → VR j t ω ≠ W t ω) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, (∀ u ≤ T, ¬ ForceWord.ThresholdCondition ρL ρR (W u ω)
      (fun i => VL i u ω) (fun j => VR j u ω)) →
      ∀ i, forceDefect (fun t => W t ω) (fun t => VL i t ω) T = 0 := by
  rcases Nat.eq_zero_or_pos nL with hn | hn
  · subst hn
    exact Eventually.of_forall fun ω T _ i => i.elim0
  set i₀ : Fin nL := ⟨0, hn⟩ with hi₀def
  have hi₀ : ∀ ω t i, VL i t ω ≤ VL i₀ t ω := fun ω t i =>
    hidxL ω t (show i₀ ≤ i from Nat.zero_le _)
  have hloc : ∀ (S : Finset (Fin nL)) (q : ℚ) (t : ℕ), ∀ᵐ ω ∂P,
      1 + (1 / 2) * ∑ i ∈ S, ρL i ≠ 0 → 0 ≤ q →
      (∀ i, VL i (q : ℝ).toNNReal ω = VL i₀ (q : ℝ).toNNReal ω ↔ i ∈ S) →
      ∀ u, (q : ℝ).toNNReal ≤ u → u ≤ t →
      (∀ r, (q : ℝ).toNNReal ≤ r → r ≤ u →
        (∀ i ∉ S, VL i r ω ≠ VL i₀ r ω) ∧ ∀ j, VR j r ω ≠ W r ω) →
      forceDefect (fun t => W t ω) (fun t => VL i₀ t ω) u
        = forceDefect (fun t => W t ω) (fun t => VL i₀ t ω) (q : ℝ).toNNReal := by
    intro S q t
    by_cases hS : 1 + (1 / 2) * ∑ i ∈ S, ρL i ≠ 0
    · by_cases hst : (q : ℝ).toNNReal ≤ (t : ℝ≥0)
      · filter_upwards [ae_forceDefect_const_of_group ha hβ hβc hW hWc hWa hVLa hVRa hpL hpR
          hordL hantiL hmonoR hmerge hi₀ S hS hst] with ω hω _ _ hgrp u h1 h2 h3
        exact hω hgrp u h1 h2 h3
      · exact Eventually.of_forall fun ω _ _ _ u h1 h2 _ => absurd (h1.trans h2) hst
    · exact Eventually.of_forall fun ω h => absurd h hS
  have hall := ae_all_iff.2 fun S => ae_all_iff.2 fun q => ae_all_iff.2 fun t => hloc S q t
  filter_upwards [hall] with ω hω T hT i
  have hgood : GroupConst ρL (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) i₀ :=
    fun S hS q hq hgrp u hsu hcond => hω S q ⌈u⌉₊ hS hq hgrp u hsu (Nat.le_ceil u) hcond
  have h0 : ∀ u ≤ T, forceDefect (fun t => W t ω) (fun t => VL i₀ t ω) u = 0 := fun u hu =>
    forceDefect_eq_zero_of_groupConst (ρR := ρR) (hWc ω) (hpL ω) (hpR ω) (hmerge ω)
      (fun t ht hcol j => hsep ω t ht i₀ j hcol) hgood fun v hv => hT v (hv.trans hu)
  exact forceDefect_eq_zero_of_nearest (hpL ω) (hordL ω) (hmerge ω) (hi₀ ω) h0 i

end AlmostSure

/-! ### Reflection `x ↦ −x` -/

section Reflect

lemma IsForcePath.neg {w v : ℝ≥0 → ℝ} (hv : IsForcePath w v) :
    IsForcePath (fun t => -w t) (fun t => -v t) := by
  obtain ⟨hc, hm, hd, hz⟩ := hv
  refine ⟨hc.neg, (hm.imp Monotone.neg Antitone.neg).symm, fun u hu hne => ?_, ?_⟩
  · have hne' : v u.toNNReal ≠ w u.toNNReal := fun h => hne (by simp only [h])
    have hD := (hd u hu hne').neg
    have he : 2 / (-v u.toNNReal - -w u.toNNReal) = -(2 / (v u.toNNReal - w u.toNNReal)) := by
      rw [show -v u.toNNReal - -w u.toNNReal = -(v u.toNNReal - w u.toNNReal) by ring, div_neg]
    rw [he]
    exact hD
  · simpa only [neg_inj] using hz

lemma forceDefect_neg (w v : ℝ≥0 → ℝ) (t : ℝ≥0) :
    forceDefect (fun t => -w t) (fun t => -v t) t = -forceDefect w v t := by
  simp only [forceDefect]
  have h : ∀ s : ℝ, 2 / (-v s.toNNReal - -w s.toNNReal) = -(2 / (v s.toNNReal - w s.toNNReal)) :=
    fun s => by
      rw [show -v s.toNNReal - -w s.toNNReal = -(v s.toNNReal - w s.toNNReal) by ring, div_neg]
  simp only [h, intervalIntegral.integral_neg]
  ring

lemma thresholdCondition_neg_iff {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ)
    (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) :
    ForceWord.ThresholdCondition ρR ρL (-w) (fun j => -vR j) (fun i => -vL i) ↔
      ForceWord.ThresholdCondition ρL ρR w vL vR := by
  simp only [ForceWord.ThresholdCondition, neg_inj]
  exact or_comm

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsProbabilityMeasure P] {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {β W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ}

/-- **Theorem 2.4, the singular motions vanish: right side** (by reflection). -/
theorem ae_forceDefect_right_eq_zero {a : ℝ} (ha : a ≠ 0) (hβ : IsFilteredPreBrownian β 𝓕 P)
    (hβc : ∀ ω, Continuous fun t => β t ω)
    (hW : ∀ t ω, W t ω = a * β t ω
      - (1 / 2) * ((∑ i, ρL i * (VL i t ω - xL i)) + ∑ j, ρR j * (VR j t ω - xR j)))
    (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓕 W)
    (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i)) (hVRa : ∀ j, StronglyAdapted 𝓕 (VR j))
    (hpL : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VL i t ω))
    (hpR : ∀ ω j, IsForcePath (fun t => W t ω) (fun t => VR j t ω))
    (hordR : ∀ ω t j, W t ω ≤ VR j t ω) (hantiL : ∀ ω i, Antitone fun t => VL i t ω)
    (hmonoR : ∀ ω j, Monotone fun t => VR j t ω)
    (hmergeR : ∀ ω i j s t, s ≤ t → VR i s ω = VR j s ω → VR i t ω = VR j t ω)
    (hidxR : ∀ ω t, Monotone fun j => VR j t ω)
    (hsep : ∀ ω t, 0 < t → ∀ i j, VL i t ω = W t ω → VR j t ω ≠ W t ω) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, (∀ u ≤ T, ¬ ForceWord.ThresholdCondition ρL ρR (W u ω)
      (fun i => VL i u ω) (fun j => VR j u ω)) →
      ∀ j, forceDefect (fun t => W t ω) (fun t => VR j t ω) T = 0 := by
  have hW' : ∀ t ω, -W t ω = -a * β t ω
      - (1 / 2) * ((∑ j, ρR j * (-VR j t ω - -xR j)) + ∑ i, ρL i * (-VL i t ω - -xL i)) := by
    intro t ω
    have h1 : ∀ j, ρR j * (-VR j t ω - -xR j) = -(ρR j * (VR j t ω - xR j)) := fun j => by ring
    have h2 : ∀ i, ρL i * (-VL i t ω - -xL i) = -(ρL i * (VL i t ω - xL i)) := fun i => by ring
    rw [hW t ω]
    simp only [h1, h2, Finset.sum_neg_distrib]
    ring
  have h := ae_forceDefect_left_eq_zero (P := P) (a := -a) (neg_ne_zero.2 ha) (ρL := ρR) (ρR := ρL)
    (xL := fun j => -xR j) (xR := fun i => -xL i) (W := fun t ω => -W t ω)
    (VL := fun j t ω => -VR j t ω) (VR := fun i t ω => -VL i t ω) hβ hβc hW'
    (fun ω => (hWc ω).neg) (fun t => (hWa t).neg) (fun j t => (hVRa j t).neg)
    (fun i t => (hVLa i t).neg) (fun ω j => (hpR ω j).neg) (fun ω i => (hpL ω i).neg)
    (fun ω t j => neg_le_neg (hordR ω t j)) (fun ω j => (hmonoR ω j).neg)
    (fun ω i => (hantiL ω i).neg)
    (fun ω i j s t hst h => by rw [neg_inj] at h ⊢; exact hmergeR ω i j s t hst h)
    (fun ω t => (hidxR ω t).neg)
    (fun ω t ht j i h1 h2 => hsep ω t ht i j (neg_inj.1 h2) (neg_inj.1 h1))
  filter_upwards [h] with ω hω T hT j
  have := hω T (fun u hu => (thresholdCondition_neg_iff ρL ρR (W u ω) (fun i => VL i u ω)
    (fun j => VR j u ω)).not.2 (hT u hu)) j
  rw [forceDefect_neg] at this
  exact neg_eq_zero.1 this

end Reflect

end MartChar

end InteractingSLE
