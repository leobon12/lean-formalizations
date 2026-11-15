/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkNormLift
import InteractingSLE.Spec.ZhanGT4.RealTip
import InteractingSLE.Spec.Supplement.WalkSideWord
import InteractingSLE.Spec.Sec7.LocalExtGChart

/-!
# Side points of a simple trace point in a Loewner chart

Packet PROVE-T14-WALKNORM. Let `η` be a continuous Loewner trace of a continuous driver `W` (`W 0 = 0`), injective on
`[0, τ]`, and let `t₀ < τ` with `η([t₀, τ]) ⊆ ℍ`. In the chart of time `τ`, with `F̄_τ` the continuous extension to
`ℍ̄` of the centred inverse map, the point `η(t₀)` is the boundary value of a point `y_l < 0` of the **open left side**
and of a point `y_r > 0` of the **open right side** of the hull image: `F̄_τ(y_l) = F̄_τ(y_r) = η(t₀)`, and every real
point alive at `τ` whose image is negative (positive) is mapped a positive distance left of `y_l` (right of `y_r`)
(Lemma GW3's "ordinary selected subarc", read in the prefix chart: `WalkBdry.IsLeftSidePt`, `IsRightSidePt`).
Moreover the open sides `(y_l, 0)` and `(0, y_r)` between the side points and the tip coordinate carry **later** trace
points: `F̄_τ(y') = η(s)` with `t₀ < s ≤ τ` (time orientation).

**Proof (connectedness).** On `ℝ` the boundary values of `F̄_τ` are real or points of `η([0, τ])`
(`ZhanGT4.extendFrom_mem_fwdHull`, `ZhanGT4.mem_image_of_mem_fwdHull_of_mem_closure`). The arc `η([t₀, τ])` lies in
`ℍ` and meets `ℝ ∪ η([0, t₀])` only at `η(t₀)`, so the image under `F̄_τ` of a real interval from a point with a real
value to the tip coordinate `0` (`F̄_τ(0) = η(τ)`) — a connected set covered by the two closed sets `ℝ ∪ η([0, t₀])` and
`η([t₀, τ])` and meeting both — contains `η(t₀)` (`exists_eq_of_cut`). Take `y_l` the largest such coordinate in
`(−∞, 0]` (`y_r` the smallest in `[0, ∞)`). An alive point `X` with `x = f_τ(X) ∈ (y_l, 0)` has the real value
`F̄_τ(x) = X`, and the interval `[x, 0]` would give a larger coordinate; near `y_l` the values of `F̄_τ` stay in `ℍ`
(continuity at `y_l`, `η(t₀) ∈ ℍ`), whence the margin. Likewise a coordinate `y' ∈ (y_l, 0)` whose value is real or
in `η([0, t₀])` would give a larger coordinate, whence the time orientation.

## Main results

* `exists_eq_of_cut`: the connectedness step;
* **`exists_leftSide_of_cut`**, **`exists_rightSide_of_cut`**;
* in the vocabulary of PROVE-T14-WALKBDRY's recorded pieces: **`exists_isLeftSidePt_of_cut`**,
  **`exists_isRightSidePt_of_cut`** (`WalkBdry.IsLeftSidePt pc τ y` for a piece whose driver agrees with `W` on
  `[0, τ]`) and **`tendsto_prefixChart_inv_of_eq`** (the prefix chart's inverse lands at `c.2.1 (η t₀)`).

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Complex Metric
open scoped NNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull IsForwardSol)

namespace InteractingSLE.Theorem14.WalkNorm

section Cut

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- The extension of the inverse map is continuous on the real line. -/
theorem continuous_extendFrom_real (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {τ : ℝ}
    (hτ : 0 ≤ τ) : Continuous fun y : ℝ => extendFrom H (fwdMapInv W τ) (y : ℂ) :=
  (hη.hasBdryLimits hW hW0 hτ).continuousOn.comp_continuous Complex.continuous_ofReal fun y =>
    show (0 : ℝ) ≤ ((y : ℂ)).im by simp

/-- On the real line the boundary values are real or points of the trace. -/
theorem extendFrom_real_cases (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {τ : ℝ} (hτ : 0 ≤ τ)
    (v : ℝ) : (extendFrom H (fwdMapInv W τ) v).im = 0 ∨ extendFrom H (fwdMapInv W τ) v ∈ η '' Icc 0 τ := by
  by_cases hH : extendFrom H (fwdMapInv W τ) v ∈ H
  · right
    obtain ⟨h1, h2⟩ := ZhanGT4.extendFrom_mem_fwdHull hη hW hW0 hτ hH
    exact ZhanGT4.mem_image_of_mem_fwdHull_of_mem_closure hη hτ h1 h2
  · left
    have hlim := (hη.hasBdryLimits hW hW0 hτ).tendsto (show ((v : ℂ)) ∈ Hbar by
      show (0 : ℝ) ≤ ((v : ℂ)).im; simp)
    have := FiniteEndpoint.neBot_nhdsWithin_H (z := (v : ℂ)) (by simp)
    have hcl : extendFrom H (fwdMapInv W τ) v ∈ closure H := mem_closure_of_tendsto hlim
      (eventually_nhdsWithin_of_forall fun w hw => QuantumZipper.RS.fwdMapInv_mem_H hW hW0 hτ hw)
    rw [closure_H] at hcl
    have h0 : (0 : ℝ) ≤ (extendFrom H (fwdMapInv W τ) v).im := hcl
    have h1 : ¬ (0 : ℝ) < (extendFrom H (fwdMapInv W τ) v).im := hH
    linarith [not_lt.1 h1]

/-- **The connectedness step**: if `F̄_τ(a)` is real or a point of `η([0, t₀])`, and `F̄_τ(c) = η(τ)`, some coordinate
between `a` and `c` is mapped to `η(t₀)`. -/
theorem exists_eq_of_cut (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {t₀ τ : ℝ} (ht₀ : 0 ≤ t₀)
    (hτ : t₀ ≤ τ) (hinj : InjOn η (Icc 0 τ)) (hH : ∀ s ∈ Icc t₀ τ, η s ∈ H) {a c : ℝ}
    (ha : (extendFrom H (fwdMapInv W τ) a).im = 0 ∨ extendFrom H (fwdMapInv W τ) a ∈ η '' Icc 0 t₀)
    (hc : extendFrom H (fwdMapInv W τ) c = η τ) :
    ∃ y ∈ uIcc a c, extendFrom H (fwdMapInv W τ) y = η t₀ := by
  have hτ0 : 0 ≤ τ := ht₀.trans hτ
  set Φ : ℝ → ℂ := fun y => extendFrom H (fwdMapInv W τ) (y : ℂ) with hΦ
  have hΦc : Continuous Φ := continuous_extendFrom_real hη hW hW0 hτ0
  set C : Set ℂ := Φ '' uIcc a c with hC
  have hCc : IsPreconnected C := isPreconnected_uIcc.image _ hΦc.continuousOn
  have hηc : ContinuousOn η (Icc 0 τ) := hη.2.1.mono fun s hs => hs.1
  set F₁ : Set ℂ := {z | z.im = 0} ∪ η '' Icc 0 t₀ with hF₁
  set F₂ : Set ℂ := η '' Icc t₀ τ with hF₂
  have hF₁c : IsClosed F₁ := (isClosed_eq Complex.continuous_im continuous_const).union
    ((isCompact_Icc.image_of_continuousOn (hηc.mono (Icc_subset_Icc_right hτ))).isClosed)
  have hF₂c : IsClosed F₂ :=
    (isCompact_Icc.image_of_continuousOn (hηc.mono (Icc_subset_Icc_left ht₀))).isClosed
  have hcover : C ⊆ F₁ ∪ F₂ := by
    rintro _ ⟨y, -, rfl⟩
    rcases extendFrom_real_cases hη hW hW0 hτ0 y with h | ⟨s, hs, hsy⟩
    · exact Or.inl (Or.inl h)
    · rcases le_total s t₀ with hst | hst
      · exact Or.inl (Or.inr ⟨s, ⟨hs.1, hst⟩, hsy⟩)
      · exact Or.inr ⟨s, ⟨hst, hs.2⟩, hsy⟩
  -- the only common point of `F₁` and `F₂` is `η t₀`
  have hcommon : ∀ z ∈ F₁, z ∈ F₂ → z = η t₀ := by
    rintro z hz1 ⟨s, hs, rfl⟩
    rcases hz1 with hz | ⟨s', hs', hs'z⟩
    · exact absurd (hH s hs) (by
        show ¬ (0 : ℝ) < (η s).im
        rw [show (η s).im = 0 from hz]; exact lt_irrefl 0)
    · have := hinj ⟨hs'.1, hs'.2.trans hτ⟩ ⟨ht₀.trans hs.1, hs.2⟩ hs'z
      have hss : s = t₀ := le_antisymm (this ▸ hs'.2) hs.1
      rw [hss]
  by_contra hno
  simp only [not_exists, not_and] at hno
  have h1 : (C ∩ F₁).Nonempty := ⟨Φ a, mem_image_of_mem _ left_mem_uIcc, ha⟩
  have h2 : (C ∩ F₂).Nonempty := ⟨Φ c, mem_image_of_mem _ right_mem_uIcc, by
    show extendFrom H (fwdMapInv W τ) c ∈ F₂
    rw [hc]; exact ⟨τ, ⟨hτ, le_rfl⟩, rfl⟩⟩
  obtain ⟨z, ⟨y, hy, rfl⟩, hz1, hz2⟩ := isPreconnected_closed_iff.1 hCc F₁ F₂ hF₁c hF₂c hcover h1 h2
  exact hno y hy (hcommon _ hz1 hz2)

/-- An alive real point has the real value `F̄_τ(f_τ(X)) = X`, and `f_τ(X)` is real. -/
theorem extendFrom_fwdMap_real (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {τ : ℝ}
    (hτ : 0 ≤ τ) {X : ℝ} {u : ℝ → ℂ} (hu : IsForwardSol W (X : ℂ) τ u) :
    extendFrom H (fwdMapInv W τ) (((fwdMap W τ X).re : ℝ) : ℂ) = X := by
  have hFc : ContinuousOn (extendFrom H (fwdMapInv W τ)) Hbar := (hη.hasBdryLimits hW hW0 hτ).continuousOn
  have hFeq : EqOn (extendFrom H (fwdMapInv W τ)) (fwdMapInv W τ) H := fun w hw =>
    ZhanGT4.extendFrom_eq_fwdMapInv hW hW0 hτ hw
  have h := ZhanGT4.extension_fwdMap_eq_of_isForwardSol hW hW0 hτ hFeq hFc hu
  rwa [fwdMap_eq_ofReal_re hW hu ⟨hτ, le_rfl⟩] at h

/-- **The left side point of a cut point.** -/
theorem exists_leftSide_of_cut (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {t₀ τ : ℝ}
    (ht₀ : 0 ≤ t₀) (hτ : t₀ < τ) (hinj : InjOn η (Icc 0 τ)) (hH : ∀ s ∈ Icc t₀ τ, η s ∈ H) :
    ∃ y : ℝ, y < 0 ∧ extendFrom H (fwdMapInv W τ) y = η t₀ ∧ (∃ ε > 0, ∀ X : ℝ,
      (∃ u, IsForwardSol W (X : ℂ) τ u) → (fwdMap W τ X).re < 0 → (fwdMap W τ X).re + ε < y) ∧
      ∀ y' ∈ Ioo y 0, ∃ s ∈ Ioc t₀ τ, extendFrom H (fwdMapInv W τ) y' = η s := by
  have hτ0 : 0 ≤ τ := ht₀.trans hτ.le
  have hτpos : 0 < τ := lt_of_le_of_lt ht₀ hτ
  set Φ : ℝ → ℂ := fun y => extendFrom H (fwdMapInv W τ) (y : ℂ) with hΦ
  have hΦc : Continuous Φ := continuous_extendFrom_real hη hW hW0 hτ0
  have hΦ0 : Φ 0 = η τ := by
    simp only [hΦ, Complex.ofReal_zero]; exact ZhanGT4.extendFrom_zero_eq hη hW hW0 hτ0
  have hne : η τ ≠ η t₀ := fun h => (ne_of_lt hτ).symm (hinj ⟨hτ0, le_rfl⟩ ⟨ht₀, hτ.le⟩ h)
  have hηt₀ : η t₀ ∈ H := hH t₀ ⟨le_rfl, hτ.le⟩
  have hcut : ∀ a : ℝ, a ≤ 0 → ((Φ a).im = 0 ∨ Φ a ∈ η '' Icc 0 t₀) → ∃ y ∈ Icc a 0, Φ y = η t₀ := by
    intro a ha hare
    obtain ⟨y, hy, hyη⟩ := exists_eq_of_cut hη hW hW0 ht₀ hτ.le hinj hH hare (c := 0)
      (by rw [Complex.ofReal_zero]; exact ZhanGT4.extendFrom_zero_eq hη hW hW0 hτ0)
    rw [uIcc_of_le ha] at hy
    exact ⟨y, hy, hyη⟩
  obtain ⟨⟨v, hv0, hvim, -⟩, -⟩ := ZhanGT4.exists_coord_far hW hW0 hη hτpos 0
  set Z : Set ℝ := {y | y ≤ 0 ∧ Φ y = η t₀} with hZ
  have hZne : Z.Nonempty := by
    obtain ⟨y, hy, hyη⟩ := hcut v hv0.le (Or.inl hvim)
    exact ⟨y, hy.2, hyη⟩
  have hZc : IsClosed Z := (isClosed_le continuous_id continuous_const).inter (isClosed_eq hΦc continuous_const)
  have hZb : BddAbove Z := ⟨0, fun y hy => hy.1⟩
  set y₀ := sSup Z with hy₀
  have hy₀Z : y₀ ∈ Z := hZc.csSup_mem hZne hZb
  have hy₀neg : y₀ < 0 := lt_of_le_of_ne hy₀Z.1 fun h => hne (by rw [← hΦ0, ← h]; exact hy₀Z.2)
  -- near `y₀` the boundary values stay in `ℍ`
  have hcontim : Continuous fun y => (Φ y).im := Complex.continuous_im.comp hΦc
  obtain ⟨ε, hε, hεim⟩ := Metric.isOpen_iff.1 ((isOpen_lt continuous_const hcontim)) y₀
    (show (0 : ℝ) < (Φ y₀).im by rw [hy₀Z.2]; exact hηt₀)
  refine ⟨y₀, hy₀neg, hy₀Z.2, ⟨ε / 2, half_pos hε, ?_⟩, fun y' hy' => ?_⟩
  swap
  · rcases extendFrom_real_cases hη hW hW0 hτ0 y' with h | ⟨s, hs, hsy⟩
    · obtain ⟨y, hy, hyη⟩ := hcut y' hy'.2.le (Or.inl h)
      have : y ≤ y₀ := le_csSup hZb ⟨hy.2, hyη⟩
      linarith [hy.1, hy'.1]
    · by_cases hst : s ≤ t₀
      · obtain ⟨y, hy, hyη⟩ := hcut y' hy'.2.le (Or.inr ⟨s, ⟨hs.1, hst⟩, hsy⟩)
        have : y ≤ y₀ := le_csSup hZb ⟨hy.2, hyη⟩
        linarith [hy.1, hy'.1]
      · exact ⟨s, ⟨lt_of_not_ge hst, hs.2⟩, hsy.symm⟩
  rintro X ⟨u, hu⟩ hX
  set x := (fwdMap W τ X).re with hx
  have hΦx : Φ x = X := extendFrom_fwdMap_real hη hW hW0 hτ0 hu
  have hΦxim : (Φ x).im = 0 := by rw [hΦx]; simp
  have hxle : x ≤ y₀ := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨y, hy, hyη⟩ := hcut x hX.le (Or.inl hΦxim)
    have : y ≤ y₀ := le_csSup hZb ⟨hy.2, hyη⟩
    linarith [hy.1]
  have hfar : ¬ dist x y₀ < ε := fun h => by
    have h' : (0 : ℝ) < (Φ x).im := hεim h
    linarith
  rw [Real.dist_eq, not_lt, abs_of_nonpos (by linarith)] at hfar
  linarith

/-- **The right side point of a cut point.** -/
theorem exists_rightSide_of_cut (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {t₀ τ : ℝ}
    (ht₀ : 0 ≤ t₀) (hτ : t₀ < τ) (hinj : InjOn η (Icc 0 τ)) (hH : ∀ s ∈ Icc t₀ τ, η s ∈ H) :
    ∃ y : ℝ, 0 < y ∧ extendFrom H (fwdMapInv W τ) y = η t₀ ∧ (∃ ε > 0, ∀ X : ℝ,
      (∃ u, IsForwardSol W (X : ℂ) τ u) → 0 < (fwdMap W τ X).re → y + ε < (fwdMap W τ X).re) ∧
      ∀ y' ∈ Ioo 0 y, ∃ s ∈ Ioc t₀ τ, extendFrom H (fwdMapInv W τ) y' = η s := by
  have hτ0 : 0 ≤ τ := ht₀.trans hτ.le
  have hτpos : 0 < τ := lt_of_le_of_lt ht₀ hτ
  set Φ : ℝ → ℂ := fun y => extendFrom H (fwdMapInv W τ) (y : ℂ) with hΦ
  have hΦc : Continuous Φ := continuous_extendFrom_real hη hW hW0 hτ0
  have hΦ0 : Φ 0 = η τ := by
    simp only [hΦ, Complex.ofReal_zero]; exact ZhanGT4.extendFrom_zero_eq hη hW hW0 hτ0
  have hne : η τ ≠ η t₀ := fun h => (ne_of_lt hτ).symm (hinj ⟨hτ0, le_rfl⟩ ⟨ht₀, hτ.le⟩ h)
  have hηt₀ : η t₀ ∈ H := hH t₀ ⟨le_rfl, hτ.le⟩
  have hcut : ∀ a : ℝ, 0 ≤ a → ((Φ a).im = 0 ∨ Φ a ∈ η '' Icc 0 t₀) → ∃ y ∈ Icc 0 a, Φ y = η t₀ := by
    intro a ha hare
    obtain ⟨y, hy, hyη⟩ := exists_eq_of_cut hη hW hW0 ht₀ hτ.le hinj hH hare (c := 0)
      (by rw [Complex.ofReal_zero]; exact ZhanGT4.extendFrom_zero_eq hη hW hW0 hτ0)
    rw [uIcc_of_ge ha] at hy
    exact ⟨y, hy, hyη⟩
  obtain ⟨-, ⟨v, hv0, hvim, -⟩⟩ := ZhanGT4.exists_coord_far hW hW0 hη hτpos 0
  set Z : Set ℝ := {y | 0 ≤ y ∧ Φ y = η t₀} with hZ
  have hZne : Z.Nonempty := by
    obtain ⟨y, hy, hyη⟩ := hcut v hv0.le (Or.inl hvim)
    exact ⟨y, hy.1, hyη⟩
  have hZc : IsClosed Z := (isClosed_le continuous_const continuous_id).inter (isClosed_eq hΦc continuous_const)
  have hZb : BddBelow Z := ⟨0, fun y hy => hy.1⟩
  set y₀ := sInf Z with hy₀
  have hy₀Z : y₀ ∈ Z := hZc.csInf_mem hZne hZb
  have hy₀pos : 0 < y₀ := lt_of_le_of_ne hy₀Z.1 fun h => hne (by rw [← hΦ0, h]; exact hy₀Z.2)
  have hcontim : Continuous fun y => (Φ y).im := Complex.continuous_im.comp hΦc
  obtain ⟨ε, hε, hεim⟩ := Metric.isOpen_iff.1 ((isOpen_lt continuous_const hcontim)) y₀
    (show (0 : ℝ) < (Φ y₀).im by rw [hy₀Z.2]; exact hηt₀)
  refine ⟨y₀, hy₀pos, hy₀Z.2, ⟨ε / 2, half_pos hε, ?_⟩, fun y' hy' => ?_⟩
  swap
  · rcases extendFrom_real_cases hη hW hW0 hτ0 y' with h | ⟨s, hs, hsy⟩
    · obtain ⟨y, hy, hyη⟩ := hcut y' hy'.1.le (Or.inl h)
      have : y₀ ≤ y := csInf_le hZb ⟨hy.1, hyη⟩
      linarith [hy.2, hy'.2]
    · by_cases hst : s ≤ t₀
      · obtain ⟨y, hy, hyη⟩ := hcut y' hy'.1.le (Or.inr ⟨s, ⟨hs.1, hst⟩, hsy⟩)
        have : y₀ ≤ y := csInf_le hZb ⟨hy.1, hyη⟩
        linarith [hy.2, hy'.2]
      · exact ⟨s, ⟨lt_of_not_ge hst, hs.2⟩, hsy.symm⟩
  rintro X ⟨u, hu⟩ hX
  set x := (fwdMap W τ X).re with hx
  have hΦx : Φ x = X := extendFrom_fwdMap_real hη hW hW0 hτ0 hu
  have hΦxim : (Φ x).im = 0 := by rw [hΦx]; simp
  have hxge : y₀ ≤ x := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨y, hy, hyη⟩ := hcut x hX.le (Or.inl hΦxim)
    have : y₀ ≤ y := csInf_le hZb ⟨hy.1, hyη⟩
    linarith [hy.2]
  have hfar : ¬ dist x y₀ < ε := fun h => by
    have h' : (0 : ℝ) < (Φ x).im := hεim h
    linarith
  rw [Real.dist_eq, not_lt, abs_of_nonneg (by linarith)] at hfar
  linarith

end Cut

/-! ### Recorded pieces -/

section Piece

open WalkBdry

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {pc : Piece} {τ : ℝ≥0}

/-- **A left side point of a recorded piece at a cut point** of a global model `(W, η)` of its driver on `[0, τ]`. -/
theorem exists_isLeftSidePt_of_cut (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hagree : EqOn (pieceDrv pc) W (Icc 0 (τ : ℝ))) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (hτ : t₀ < τ)
    (hinj : InjOn η (Icc 0 (τ : ℝ))) (hH : ∀ s ∈ Icc t₀ (τ : ℝ), η s ∈ H) :
    ∃ y : ℝ, IsLeftSidePt pc τ y ∧ extendFrom H (fwdMapInv W τ) y = η t₀ ∧
      ∀ y' ∈ Ioo y 0, ∃ s ∈ Ioc t₀ (τ : ℝ), extendFrom H (fwdMapInv W τ) y' = η s := by
  obtain ⟨y, hy0, hyη, ⟨ε, hε, hm⟩, hlater⟩ := exists_leftSide_of_cut hη hW hW0 ht₀ hτ hinj hH
  refine ⟨y, ⟨hy0, ε, hε, fun X ⟨u, hu⟩ hX => ?_⟩, hyη, hlater⟩
  have hu' : IsForwardSol W (X : ℂ) τ u := (WalkSide.isForwardSol_congr hagree _ _).1 hu
  have hf : fwdMap (pieceDrv pc) τ X = fwdMap W τ X := Ito.fwdMap_congr_of_eqOn_of_le hagree le_rfl
  rw [hf] at hX ⊢
  exact hm X ⟨u, hu'⟩ hX

/-- **A right side point of a recorded piece at a cut point.** -/
theorem exists_isRightSidePt_of_cut (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hagree : EqOn (pieceDrv pc) W (Icc 0 (τ : ℝ))) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (hτ : t₀ < τ)
    (hinj : InjOn η (Icc 0 (τ : ℝ))) (hH : ∀ s ∈ Icc t₀ (τ : ℝ), η s ∈ H) :
    ∃ y : ℝ, IsRightSidePt pc τ y ∧ extendFrom H (fwdMapInv W τ) y = η t₀ ∧
      ∀ y' ∈ Ioo 0 y, ∃ s ∈ Ioc t₀ (τ : ℝ), extendFrom H (fwdMapInv W τ) y' = η s := by
  obtain ⟨y, hy0, hyη, ⟨ε, hε, hm⟩, hlater⟩ := exists_rightSide_of_cut hη hW hW0 ht₀ hτ hinj hH
  refine ⟨y, ⟨hy0, ε, hε, fun X ⟨u, hu⟩ hX => ?_⟩, hyη, hlater⟩
  have hu' : IsForwardSol W (X : ℂ) τ u := (WalkSide.isForwardSol_congr hagree _ _).1 hu
  have hf : fwdMap (pieceDrv pc) τ X = fwdMap W τ X := Ito.fwdMap_congr_of_eqOn_of_le hagree le_rfl
  rw [hf] at hX ⊢
  exact hm X ⟨u, hu'⟩ hX

/-- **The prefix chart's inverse lands at the launch-chart image of an interior boundary value**: if the piece's
driver is continuous on `[0, τ']`, `τ < τ'`, and agrees with `W` on `[0, τ]`, and `F̄_τ(y) = q ∈ ℍ`, then
`(prefixChart pc τ).2.1 → pc.1.2.1 q` at `y`. -/
theorem tendsto_prefixChart_inv_of_eq (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hc : pc.1.IsConformal) {τ' : ℝ} (hτ' : (τ : ℝ) < τ') (hpc : ContinuousOn (pieceDrv pc) (Icc 0 τ'))
    (hagree : EqOn (pieceDrv pc) W (Icc 0 (τ : ℝ))) {y : ℝ} {q : ℂ} (hq : q ∈ H)
    (hy : extendFrom H (fwdMapInv W τ) y = q) :
    Tendsto (prefixChart pc τ).2.1 (𝓝[H] (y : ℂ)) (𝓝 (pc.1.2.1 q)) := by
  have hτ0 : (0 : ℝ) ≤ τ := τ.coe_nonneg
  have hinv : ∀ z, fwdMapInv (pieceDrv pc) τ z = fwdMapInv W τ z := fun z =>
    LocalExt.fwdMapInv_congr_of_continuousOn hpc hW.continuousOn hτ0 hτ' hagree z
  have hlim : Tendsto (fwdMapInv W τ) (𝓝[H] (y : ℂ)) (𝓝 q) := by
    rw [← hy]
    exact (hη.hasBdryLimits hW hW0 hτ0).tendsto (show ((y : ℂ)) ∈ Hbar by
      show (0 : ℝ) ≤ ((y : ℂ)).im; simp)
  have hcq : ContinuousAt pc.1.2.1 q :=
    (hc.1.differentiableAt (QuantumZipper.isOpen_H.mem_nhds hq)).continuousAt
  have := hcq.tendsto.comp hlim
  refine this.congr fun z => ?_
  change pc.1.2.1 (fwdMapInv W τ z) = pc.1.2.1 (fwdMapInv (pieceDrv pc) τ z)
  rw [hinv]

end Piece

end InteractingSLE.Theorem14.WalkNorm
