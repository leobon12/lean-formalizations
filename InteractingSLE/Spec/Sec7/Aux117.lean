/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.MartingaleFinal

/-!
# §7.4, Aux. lemma 117: the martingale converse away from critical colliding weights

Packet PROVE-STRIPSYS4. Specification §7.4, Aux. lemma 117 and its proof (`source/spec/p337-384.md` L897–L939,
pp. 381–383): "If the canonical harmonic functions of Theorem 1.1, with parameter `k` and these weights, are continuous
local martingales at every fixed interior point until swallowing, then the integrated driving and force equations hold
on every compact interval in `[0, T)`. No assertion that a colliding weight is greater than `−2` is needed for this
implication."

The converse implication of Theorem 2.4 (`MartChar.isIntegratedSLEEvolution_of_couplingMean`, landed) stops at the
continuation threshold: a colliding group of total weight `≤ −2` ends the lifetime. Aux. lemma 117 needs only that
the colliding total is **different from** `−2` ("The assumed condition `r ≠ −2` is exactly what makes (NC9.5) imply
`dI = 0`; the sign of `1 + r/2` is immaterial"). This is what Aux. lemma 122 uses for the shifted words (PS9.2), whose
seed weights may be `< −2`.

The local Tanaka step `MartChar.ae_forceDefect_const_of_group` (landed) already needs only `1 + ρ_S/2 ≠ 0`; the
landed cover argument (`MartChar.forceDefect_eq_zero_of_groupConst`) used the threshold only to obtain that
inequality at the colliding group. Here the cover argument is rerun with the weaker hypothesis.

## Main definitions

* `ColliderNe ρL w vL u`: the total weight of the left marks at the driver at time `u` is not `−2`;
* `IsWordEntrance a xL xR ρL ρR w vL vR b T`: the integrated driving and force equations of a finite force word on
  `[0, T)` (the clauses of the frozen `IsIntegratedSLEPath` without the continuation-threshold clauses).

## Main results

* `forceDefect_eq_zero_of_groupConst_of_colliderNe`: the pathwise cover argument with `≠ −2`;
* `ae_forceDefect_left_eq_zero_of_colliderNe`, `ae_forceDefect_right_eq_zero_of_colliderNe`;
* `isWordEntrance_of_forceDefect_eq_zero`: pathwise assembly before `T`;
* **`ae_isWordEntrance_of_couplingMean`** (Aux. lemma 117, for globally defined coordinates): the Brownian motion
  `B = M/√k` and, almost surely, the integrated equations on `[0, T)` for every `T` before which every colliding
  group on either side has total weight `≠ −2`.

## Scope

The coordinates are continuous adapted processes on all of `ℝ≥0` with the deterministic properties of geometric force
images, and the coupling means are local martingales until swallowing at all times (the hypotheses of the landed
Theorem 2.4 converse). The source's lemma assumes the martingale property only before the stopping lifetime `T` of
the trace; that version also needs a Brownian motion continued after `T` (an enlargement of the probability space),
which is not done here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace Aux117

open MartChar

/-! ### The colliding-weight condition -/

section Collider

variable {nL nR : ℕ}

/-- The total weight of the marks of `v` that sit at the driver at time `u` is not `−2`. -/
def ColliderNe {n : ℕ} (ρ : Fin n → ℝ) (w : ℝ≥0 → ℝ) (v : Fin n → ℝ≥0 → ℝ) (u : ℝ≥0) : Prop :=
  (∑ i ∈ Finset.univ.filter (fun i => v i u = w u), ρ i) ≠ -2

theorem colliderNe_neg_iff {n : ℕ} (ρ : Fin n → ℝ) (w : ℝ≥0 → ℝ) (v : Fin n → ℝ≥0 → ℝ) (u : ℝ≥0) :
    ColliderNe ρ (fun t => -w t) (fun i t => -v i t) u ↔ ColliderNe ρ w v u := by
  simp only [ColliderNe, neg_inj]

/-- Before the continuation threshold every colliding group has total weight `> −2`, hence `≠ −2`. -/
theorem colliderNe_of_not_thresholdCondition {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {u : ℝ≥0}
    (h : ¬ ForceWord.ThresholdCondition ρL ρR (w u) (fun i => vL i u) (fun j => vR j u)) :
    ColliderNe ρL w vL u ∧ ColliderNe ρR w vR u := by
  simp only [ForceWord.ThresholdCondition, not_or, not_le] at h
  exact ⟨h.1.ne', h.2.ne'⟩

end Collider

/-! ### The cover argument with `≠ −2` -/

section Cover

variable {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ}
  {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}

/-- **The nearest left point has no singular motion while every colliding left group has total weight `≠ −2`**
(pathwise; the landed `MartChar.forceDefect_eq_zero_of_groupConst` with the threshold replaced by `≠ −2`). -/
theorem forceDefect_eq_zero_of_groupConst_of_colliderNe (hwc : Continuous w)
    (hpL : ∀ i, IsForcePath w (vL i)) (hpR : ∀ j, IsForcePath w (vR j))
    (hmerge : ∀ i j s t, s ≤ t → vL i s = vL j s → vL i t = vL j t) {i₀ : Fin nL}
    (hsep : ∀ t, 0 < t → vL i₀ t = w t → ∀ j, vR j t ≠ w t)
    (hgood : GroupConst ρL w vL vR i₀) {T : ℝ≥0}
    (hT : ∀ u, 0 < u → u ≤ T → ColliderNe ρL w vL u) :
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
        have h : (∑ i ∈ S, ρL i) ≠ -2 := by
          have := hT u hu0 huT
          rwa [ColliderNe, hSw] at this
        intro h0
        exact h (by linarith)
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

end Cover

/-! ### Almost surely, no singular motion while colliding totals are `≠ −2` -/

section AlmostSure

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsProbabilityMeasure P] {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {β W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ}

/-- **Aux. lemma 117, the singular motions vanish: left side** ((NC9.5) with `r ≠ −2`). -/
theorem ae_forceDefect_left_eq_zero_of_colliderNe {a : ℝ} (ha : a ≠ 0)
    (hβ : IsFilteredPreBrownian β 𝓕 P) (hβc : ∀ ω, Continuous fun t => β t ω)
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
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, (∀ u, 0 < u → u ≤ T → ColliderNe ρL (fun t => W t ω) (fun i t => VL i t ω) u) →
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
    forceDefect_eq_zero_of_groupConst_of_colliderNe (ρL := ρL) (hWc ω) (hpL ω) (hpR ω) (hmerge ω)
      (fun t ht hcol j => hsep ω t ht i₀ j hcol) hgood fun v hv0 hv => hT v hv0 (hv.trans hu)
  exact forceDefect_eq_zero_of_nearest (hpL ω) (hordL ω) (hmerge ω) (hi₀ ω) h0 i

/-- **Aux. lemma 117, the singular motions vanish: right side** (by reflection `x ↦ −x`). -/
theorem ae_forceDefect_right_eq_zero_of_colliderNe {a : ℝ} (ha : a ≠ 0)
    (hβ : IsFilteredPreBrownian β 𝓕 P) (hβc : ∀ ω, Continuous fun t => β t ω)
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
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, (∀ u, 0 < u → u ≤ T → ColliderNe ρR (fun t => W t ω) (fun j t => VR j t ω) u) →
      ∀ j, forceDefect (fun t => W t ω) (fun t => VR j t ω) T = 0 := by
  have hW' : ∀ t ω, -W t ω = -a * β t ω
      - (1 / 2) * ((∑ j, ρR j * (-VR j t ω - -xR j)) + ∑ i, ρL i * (-VL i t ω - -xL i)) := by
    intro t ω
    have h1 : ∀ j, ρR j * (-VR j t ω - -xR j) = -(ρR j * (VR j t ω - xR j)) := fun j => by ring
    have h2 : ∀ i, ρL i * (-VL i t ω - -xL i) = -(ρL i * (VL i t ω - xL i)) := fun i => by ring
    rw [hW t ω]
    simp only [h1, h2, Finset.sum_neg_distrib]
    ring
  have h := ae_forceDefect_left_eq_zero_of_colliderNe (P := P) (a := -a) (neg_ne_zero.2 ha) (ρL := ρR)
    (ρR := ρL) (xL := fun j => -xR j) (xR := fun i => -xL i) (W := fun t ω => -W t ω)
    (VL := fun j t ω => -VR j t ω) (VR := fun i t ω => -VL i t ω) hβ hβc hW'
    (fun ω => (hWc ω).neg) (fun t => (hWa t).neg) (fun j t => (hVRa j t).neg)
    (fun i t => (hVLa i t).neg) (fun ω j => (hpR ω j).neg) (fun ω i => (hpL ω i).neg)
    (fun ω t j => neg_le_neg (hordR ω t j)) (fun ω j => (hmonoR ω j).neg)
    (fun ω i => (hantiL ω i).neg)
    (fun ω i j s t hst h => by rw [neg_inj] at h ⊢; exact hmergeR ω i j s t hst h)
    (fun ω t => (hidxR ω t).neg)
    (fun ω t ht j i h1 h2 => hsep ω t ht i j (neg_inj.1 h2) (neg_inj.1 h1))
  filter_upwards [h] with ω hω T hT j
  have := hω T (fun u hu0 hu => (colliderNe_neg_iff ρR (fun t => W t ω) (fun j t => VR j t ω) u).2
    (hT u hu0 hu)) j
  rw [forceDefect_neg] at this
  exact neg_eq_zero.1 this

end AlmostSure

/-! ### The integrated equations before a time `T` -/

section Entrance

/-- **The integrated driving and force equations of a finite force word on `[0, T)`** (Definition 2.1's equations
without its continuation-threshold clauses): the clauses `w_zero` … `volume_collisionR` of the frozen
`IsIntegratedSLEPath`, with the lifetime `T` arbitrary. This is the conclusion of Aux. lemma 117 ("the integrated
driving and force equations hold on every compact interval in `[0, T)`") and the hypothesis of Aux. lemma 104. -/
structure IsWordEntrance (a : ℝ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (b : ℝ≥0 → ℝ)
    (T : ℝ≥0∞) : Prop where
  w_zero : w 0 = 0
  vL_zero : ∀ i, vL i 0 = xL i
  vR_zero : ∀ i, vR i 0 = xR i
  continuousOn_w : ContinuousOn w {t | (t : ℝ≥0∞) < T}
  continuousOn_vL : ∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < T}
  continuousOn_vR : ∀ i, ContinuousOn (vR i) {t | (t : ℝ≥0∞) < T}
  antitone_vL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → Antitone fun i => vL i t
  vL_le_w : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → ∀ i, vL i t ≤ w t
  w_le_vR : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → ∀ i, w t ≤ vR i t
  monotone_vR : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → Monotone fun i => vR i t
  integrable_gapL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → ∀ i,
    IntervalIntegrable (fun s : ℝ => (w s.toNNReal - vL i s.toNNReal)⁻¹) volume 0 t
  integrable_gapR : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → ∀ i,
    IntervalIntegrable (fun s : ℝ => (w s.toNNReal - vR i s.toNNReal)⁻¹) volume 0 t
  w_eq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T →
    w t = Real.sqrt a * b t
      + (∑ i, ∫ s in (0 : ℝ)..t, ρL i / (w s.toNNReal - vL i s.toNNReal))
      + (∑ i, ∫ s in (0 : ℝ)..t, ρR i / (w s.toNNReal - vR i s.toNNReal))
  vL_eq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → ∀ i,
    vL i t = xL i + ∫ s in (0 : ℝ)..t, 2 / (vL i s.toNNReal - w s.toNNReal)
  vR_eq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → ∀ i,
    vR i t = xR i + ∫ s in (0 : ℝ)..t, 2 / (vR i s.toNNReal - w s.toNNReal)
  volume_collisionL : ∀ i,
    volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < T ∧ w s.toNNReal = vL i s.toNNReal} = 0
  volume_collisionR : ∀ i,
    volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < T ∧ w s.toNNReal = vR i s.toNNReal} = 0

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w b : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {T T' : ℝ≥0∞}

/-- An integrated path of Definition 2.1 satisfies the integrated equations before its lifetime. -/
theorem isWordEntrance_of_isIntegratedSLEPath
    (h : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b T) : IsWordEntrance a xL xR ρL ρR w vL vR b T := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, -⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

/-- The integrated equations before `T` hold before every earlier time. -/
theorem IsWordEntrance.mono (h : IsWordEntrance a xL xR ρL ρR w vL vR b T) (hT : T' ≤ T) :
    IsWordEntrance a xL xR ρL ρR w vL vR b T' := by
  have hs : {t : ℝ≥0 | (t : ℝ≥0∞) < T'} ⊆ {t | (t : ℝ≥0∞) < T} := fun t ht => lt_of_lt_of_le ht hT
  refine ⟨h.w_zero, h.vL_zero, h.vR_zero, h.continuousOn_w.mono hs, fun i => (h.continuousOn_vL i).mono hs,
    fun i => (h.continuousOn_vR i).mono hs, fun t ht => h.antitone_vL t (hs ht),
    fun t ht => h.vL_le_w t (hs ht), fun t ht => h.w_le_vR t (hs ht), fun t ht => h.monotone_vR t (hs ht),
    fun t ht => h.integrable_gapL t (hs ht), fun t ht => h.integrable_gapR t (hs ht),
    fun t ht => h.w_eq t (hs ht), fun t ht => h.vL_eq t (hs ht), fun t ht => h.vR_eq t (hs ht),
    fun i => measure_mono_null ?_ (h.volume_collisionL i), fun i => measure_mono_null ?_ (h.volume_collisionR i)⟩
  · exact fun s hs => ⟨hs.1, lt_of_lt_of_le hs.2.1 hT, hs.2.2⟩
  · exact fun s hs => ⟨hs.1, lt_of_lt_of_le hs.2.1 hT, hs.2.2⟩

/-- **Pathwise assembly before `T`.** Force paths with the deterministic properties of geometric images, whose driver
is `√a b − ½ ∑ⱼ ρⱼ (Vʲ − xʲ)` and whose defects vanish before `T`, satisfy the integrated equations on `[0, T)`. -/
theorem isWordEntrance_of_forceDefect_eq_zero
    (hw0 : w 0 = 0) (hvL0 : ∀ i, vL i 0 = xL i) (hvR0 : ∀ j, vR j 0 = xR j)
    (hwc : Continuous w) (hpL : ∀ i, IsForcePath w (vL i)) (hpR : ∀ j, IsForcePath w (vR j))
    (hordL : ∀ t i, vL i t ≤ w t) (hordR : ∀ t j, w t ≤ vR j t)
    (hidxL : ∀ t, Antitone fun i => vL i t) (hidxR : ∀ t, Monotone fun j => vR j t)
    (hw : ∀ t, w t = Real.sqrt a * b t
      - (1 / 2) * ((∑ i, ρL i * (vL i t - xL i)) + ∑ j, ρR j * (vR j t - xR j)))
    (hdefL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → ∀ i, forceDefect w (vL i) t = 0)
    (hdefR : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → ∀ j, forceDefect w (vR j) t = 0) :
    IsWordEntrance a xL xR ρL ρR w vL vR b T := by
  have hvLc : ∀ i, Continuous (vL i) := fun i => (hpL i).1
  have hvRc : ∀ j, Continuous (vR j) := fun j => (hpR j).1
  refine ⟨hw0, hvL0, hvR0, hwc.continuousOn, fun i => (hvLc i).continuousOn,
    fun j => (hvRc j).continuousOn, fun t _ => hidxL t, fun t _ i => hordL t i,
    fun t _ j => hordR t j, fun t _ => hidxR t,
    fun t _ i => (hpL i).intervalIntegrable_inv_sub t,
    fun t _ j => (hpR j).intervalIntegrable_inv_sub t, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [Finset.sum_congr rfl fun i _ =>
        integral_weight_div_eq (ρL i) (xL i) (hvL0 i) (hdefL t ht i),
      Finset.sum_congr rfl fun j _ =>
        integral_weight_div_eq (ρR j) (xR j) (hvR0 j) (hdefR t ht j),
      ← Finset.mul_sum, ← Finset.mul_sum, hw t]
    ring
  · intro t ht i
    have h := hdefL t ht i
    simp only [forceDefect, hvL0] at h
    linarith
  · intro t ht j
    have h := hdefR t ht j
    simp only [forceDefect, hvR0] at h
    linarith
  · intro i
    refine measure_mono_null ?_ (hpL i).2.2.2
    intro s hs
    exact ⟨hs.1, hs.2.2.symm⟩
  · intro j
    refine measure_mono_null ?_ (hpR j).2.2.2
    intro s hs
    exact ⟨hs.1, hs.2.2.symm⟩

end Entrance

/-! ### Aux. lemma 117 -/

section Converse

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- **The driver's martingale part is Brownian** (the landed `MartChar.isFilteredBrownianReal_of_couplingMean`), from
the local-martingale property of the **explicit** coupling means `coupProc` only (the bounded harmonic extension
`meanExt`), not of every extension: the landed proof uses only this one. -/
theorem isFilteredBrownianReal_of_coupProc [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ)
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hW0 : ∀ ω, W 0 ω = 0) (hVL0 : ∀ i ω, VL i 0 ω = xL i) (hVR0 : ∀ i ω, VR i 0 ω = xR i)
    (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓕 W)
    (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i)) (hVRa : ∀ i, StronglyAdapted 𝓕 (VR i))
    (hordL : ∀ ω t i, VL i t ω ≤ W t ω) (hordR : ∀ ω t i, W t ω ≤ VR i t ω)
    (hpathL : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VL i t ω))
    (hpathR : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VR i t ω))
    (hmart : ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
      (fun ω => (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0)) (coupProc κ ρL ρR W VL VR z)) :
    IsFilteredBrownianReal 𝓕
      (fun t ω => martProc (jointρ ρL ρR) W (jointV VL VR) t ω / Real.sqrt κ) P := by
  have hVLc : ∀ i ω, Continuous fun t => VL i t ω := fun i ω => (hpathL ω i).1
  have hVRc : ∀ i ω, Continuous fun t => VR i t ω := fun i ω => (hpathR ω i).1
  have hV0 : ∀ j ω, jointV VL VR j 0 ω = jointV xL xR j := fun j ω => by
    cases j with
    | inl i => exact hVL0 i ω
    | inr i => exact hVR0 i ω
  have hVa : ∀ j, StronglyAdapted 𝓕 (jointV VL VR j) := fun j => by
    cases j with
    | inl i => exact hVLa i
    | inr i => exact hVRa i
  have hpath : ∀ ω j, IsForcePath (fun t => W t ω) (fun t => jointV VL VR j t ω) := fun ω j => by
    cases j with
    | inl i => exact hpathL ω i
    | inr i => exact hpathR ω i
  have hNQ := martingale_driftProc_quadProc_of_couplingMean hκ hW0 hVL0 hVR0 hWc hVLc hVRc hWa
    hVLa hVRa hordL hordR hmart
  exact isFilteredBrownianReal_martProc_div_sqrt hκ hW0 hV0 hWc hWa hVa hpath
    (fun T N => (hNQ T N).1) (fun T N => (hNQ T N).2)

/-- The local-martingale hypothesis of the landed Theorem 2.4 converse (every bounded harmonic extension) gives the
one for the explicit coupling means `coupProc`. -/
theorem coupProc_isLocalMartingaleBefore {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hmart : ∀ u : Ω → ℝ≥0 → ℂ → ℝ,
      (∀ ω t, IsBoundedHarmonicExtension
        (forceBoundaryData κ ρL ρR (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω))
        (forceJumpSet (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω)) (u ω t)) →
      ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
        (fun ω => (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z : WithTop ℝ≥0))
        (fun t ω => couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u ω t) z)) :
    ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
      (fun ω => (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0)) (coupProc κ ρL ρR W VL VR z) :=
  fun z hz => hmart (fun ω t => meanExt κ ρL ρR (W t ω) (fun i => VL i t ω) (fun i => VR i t ω))
    (fun ω t => isBoundedHarmonicExtension_meanExt κ ρL ρR (W t ω) _ _) z hz

/-- **Aux. lemma 117 (the martingale converse away from critical colliding weights), for globally defined
coordinates.** Let the driver `W` and the force coordinates `V^{i,q}` be continuous adapted processes started at
`(0; xL; xR)` with the deterministic properties of geometric force images (the hypotheses of the landed Theorem 2.4
converse `MartChar.isIntegratedSLEEvolution_of_couplingMean`; the weights are arbitrary reals). If every explicit
coupling mean `𝔥_t(z)` (`coupProc`, implied by the landed hypothesis through `coupProc_isLocalMartingaleBefore`) is a
local martingale before `z` is swallowed, then `B = M/√k` is a Brownian motion in `𝓕` and, almost surely,
the integrated driving and force equations hold on `[0, T)` for every `T` before which every group of marks meeting
the driver at a positive time has total weight different from `−2` (on each side). -/
theorem ae_isWordEntrance_of_couplingMean [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ)
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hW0 : ∀ ω, W 0 ω = 0) (hVL0 : ∀ i ω, VL i 0 ω = xL i) (hVR0 : ∀ i ω, VR i 0 ω = xR i)
    (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓕 W)
    (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i)) (hVRa : ∀ i, StronglyAdapted 𝓕 (VR i))
    (hordL : ∀ ω t i, VL i t ω ≤ W t ω) (hordR : ∀ ω t i, W t ω ≤ VR i t ω)
    (hpathL : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VL i t ω))
    (hpathR : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VR i t ω))
    (hantiL : ∀ ω i, Antitone fun t => VL i t ω) (hmonoR : ∀ ω j, Monotone fun t => VR j t ω)
    (hidxL : ∀ ω t, Antitone fun i => VL i t ω) (hidxR : ∀ ω t, Monotone fun j => VR j t ω)
    (hmergeL : ∀ ω i j s t, s ≤ t → VL i s ω = VL j s ω → VL i t ω = VL j t ω)
    (hmergeR : ∀ ω i j s t, s ≤ t → VR i s ω = VR j s ω → VR i t ω = VR j t ω)
    (hsep : ∀ ω t, 0 < t → ∀ i j, VL i t ω = W t ω → VR j t ω ≠ W t ω)
    (hmart : ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
      (fun ω => (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0)) (coupProc κ ρL ρR W VL VR z)) :
    IsFilteredBrownianReal 𝓕 (fun t ω => martProc (jointρ ρL ρR) W (jointV VL VR) t ω / Real.sqrt κ) P ∧
      ∀ᵐ ω ∂P, ∀ T : ℝ≥0∞, (∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < T →
          ColliderNe ρL (fun t => W t ω) (fun i t => VL i t ω) u ∧
            ColliderNe ρR (fun t => W t ω) (fun j t => VR j t ω) u) →
        IsWordEntrance κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
          (fun t => martProc (jointρ ρL ρR) W (jointV VL VR) t ω / Real.sqrt κ) T := by
  have hVLc : ∀ i ω, Continuous fun t => VL i t ω := fun i ω => (hpathL ω i).1
  have hVRc : ∀ i ω, Continuous fun t => VR i t ω := fun i ω => (hpathR ω i).1
  have hVc : ∀ j ω, Continuous fun t => jointV VL VR j t ω := fun j ω => by
    cases j with
    | inl i => exact hVLc i ω
    | inr i => exact hVRc i ω
  have hB := isFilteredBrownianReal_of_coupProc hκ hW0 hVL0 hVR0 hWc hWa hVLa hVRa hordL
    hordR hpathL hpathR hmart
  have hBpre := LocalTime.isFilteredPreBrownian_of_isFilteredBrownianReal hB
  have hBc : ∀ ω, Continuous fun t =>
      martProc (jointρ ρL ρR) W (jointV VL VR) t ω / Real.sqrt κ := fun ω =>
    (continuous_martProc hWc hVc ω).div_const _
  have hdec := fun t ω => driver_eq_sqrt_mul_sub (ρL := ρL) (ρR := ρR) hκ hW0 hVL0 hVR0 t ω
  have hsk : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  have hL := ae_forceDefect_left_eq_zero_of_colliderNe hsk hBpre hBc hdec hWc hWa hVLa hVRa hpathL
    hpathR hordL hantiL hmonoR hmergeL hidxL hsep
  have hR := ae_forceDefect_right_eq_zero_of_colliderNe hsk hBpre hBc hdec hWc hWa hVLa hVRa hpathL
    hpathR hordR hantiL hmonoR hmergeR hidxR hsep
  refine ⟨hB, ?_⟩
  filter_upwards [hL, hR] with ω hLω hRω T hT
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → ∀ u : ℝ≥0, 0 < u → u ≤ t → (u : ℝ≥0∞) < T :=
    fun t ht u _ hu => lt_of_le_of_lt (ENNReal.coe_le_coe.2 hu) ht
  exact isWordEntrance_of_forceDefect_eq_zero (hW0 ω) (fun i => hVL0 i ω) (fun j => hVR0 j ω) (hWc ω)
    (hpathL ω) (hpathR ω) (hordL ω) (hordR ω) (hidxL ω) (hidxR ω) (fun t => hdec t ω)
    (fun t ht i => hLω t (fun u hu0 hu => (hT u hu0 (hlt t ht u hu0 hu)).1) i)
    (fun t ht j => hRω t (fun u hu0 hu => (hT u hu0 (hlt t ht u hu0 hu)).2) j)

/-- **The landed Theorem 2.4 converse** (`MartChar.isIntegratedSLEEvolution_of_couplingMean`) from the local-martingale
property of the explicit coupling means `coupProc` only. Same proof, with `isFilteredBrownianReal_of_coupProc`. -/
theorem isIntegratedSLEEvolution_of_coupProc [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ)
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hW0 : ∀ ω, W 0 ω = 0) (hVL0 : ∀ i ω, VL i 0 ω = xL i) (hVR0 : ∀ i ω, VR i 0 ω = xR i)
    (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓕 W)
    (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i)) (hVRa : ∀ i, StronglyAdapted 𝓕 (VR i))
    (hordL : ∀ ω t i, VL i t ω ≤ W t ω) (hordR : ∀ ω t i, W t ω ≤ VR i t ω)
    (hpathL : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VL i t ω))
    (hpathR : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VR i t ω))
    (hantiL : ∀ ω i, Antitone fun t => VL i t ω) (hmonoR : ∀ ω j, Monotone fun t => VR j t ω)
    (hidxL : ∀ ω t, Antitone fun i => VL i t ω) (hidxR : ∀ ω t, Monotone fun j => VR j t ω)
    (hmergeL : ∀ ω i j s t, s ≤ t → VL i s ω = VL j s ω → VL i t ω = VL j t ω)
    (hmergeR : ∀ ω i j s t, s ≤ t → VR i s ω = VR j s ω → VR i t ω = VR j t ω)
    (hsep : ∀ ω t, 0 < t → ∀ i j, VL i t ω = W t ω → VR j t ω ≠ W t ω)
    (hmart : ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
      (fun ω => (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0)) (coupProc κ ρL ρR W VL VR z)) :
    IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR
      (fun t ω => martProc (jointρ ρL ρR) W (jointV VL VR) t ω / Real.sqrt κ)
      (fun ω => thresholdTime ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)) := by
  have hVLc : ∀ i ω, Continuous fun t => VL i t ω := fun i ω => (hpathL ω i).1
  have hVRc : ∀ i ω, Continuous fun t => VR i t ω := fun i ω => (hpathR ω i).1
  have hVc : ∀ j ω, Continuous fun t => jointV VL VR j t ω := fun j ω => by
    cases j with
    | inl i => exact hVLc i ω
    | inr i => exact hVRc i ω
  have hB := isFilteredBrownianReal_of_coupProc hκ hW0 hVL0 hVR0 hWc hWa hVLa hVRa hordL hordR hpathL hpathR
    hmart
  have hBpre := LocalTime.isFilteredPreBrownian_of_isFilteredBrownianReal hB
  have hBc : ∀ ω, Continuous fun t =>
      martProc (jointρ ρL ρR) W (jointV VL VR) t ω / Real.sqrt κ := fun ω =>
    (continuous_martProc hWc hVc ω).div_const _
  have hdec := fun t ω => driver_eq_sqrt_mul_sub (ρL := ρL) (ρR := ρR) hκ hW0 hVL0 hVR0 t ω
  have hsk : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  have hL := ae_forceDefect_left_eq_zero hsk hBpre hBc hdec hWc hWa hVLa hVRa hpathL hpathR
    hordL hantiL hmonoR hmergeL hidxL hsep
  have hR := ae_forceDefect_right_eq_zero hsk hBpre hBc hdec hWc hWa hVLa hVRa hpathL hpathR
    hordR hantiL hmonoR hmergeR hidxR hsep
  have hζ := measurableSet_thresholdTime_le (ρL := ρL) (ρR := ρR) hWc hVLc hVRc hWa hVLa hVRa
    hmergeL hmergeR
  refine ⟨hB, adaptedBefore_of_stronglyAdapted hζ hWa,
    fun i => adaptedBefore_of_stronglyAdapted hζ (hVLa i),
    fun j => adaptedBefore_of_stronglyAdapted hζ (hVRa j), ?_⟩
  filter_upwards [hL, hR] with ω hLω hRω
  have hnot : ∀ t : ℝ≥0, (t : ℝ≥0∞) < thresholdTime ρL ρR (fun t => W t ω)
      (fun i t => VL i t ω) (fun j t => VR j t ω) → ∀ u ≤ t,
      ¬ ForceWord.ThresholdCondition ρL ρR (W u ω) (fun i => VL i u ω) (fun j => VR j u ω) :=
    fun t ht u hu => notMem_thresholdSet_of_lt ((ENNReal.coe_le_coe.2 hu).trans_lt ht)
  exact isIntegratedSLEPath_of_forceDefect_eq_zero (hW0 ω) (fun i => hVL0 i ω)
    (fun j => hVR0 j ω) (hWc ω) (hpathL ω) (hpathR ω) (hordL ω) (hordR ω) (hidxL ω) (hidxR ω)
    (hmergeL ω) (hmergeR ω) (fun t => hdec t ω) (fun t ht i => hLω t (hnot t ht) i)
    (fun t ht j => hRω t (hnot t ht) j)

end Converse

end Aux117

end Sec7

end InteractingSLE
