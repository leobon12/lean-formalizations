/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7StopInClip
import InteractingSLE.Spec.Sec7.PocketReverseFields
import InteractingSLE.Spec.Sec7.PocketMarks
import InteractingSLE.Spec.Sec7.Lemma71JPocket
import InteractingSLE.WangWu.ChamberArcs
import InteractingSLE.Spec.Supplement.GB10
import InteractingSLE.Spec.Supplement.SBFrontier

/-!
# Lemma R.3 and Consequence R.4 for the change pocket of an outer arm: clipping by the certified frontier

Packet PROVE-R7-STOPIN. Supplement §5.1 and §5.3 (`source/spec/p433-480.md` L930–L971, pp. 471–473):

> "**Lemma R.3.** Suppose `C` is bounded by an outer right arm `α_R` and a contained left arm `γ` of angle in
> `(−π/2, π/2]`. Its two endpoints belong to `β_R ∩ γ`. The portion of `β_R` between those endpoints lies in `C̄`. All
> counterflow points in `C` lie on the `γ` side of that portion. The analogous statement for two outer arms uses both
> `β_R` and `β_L`.
>
> *Proof.* An outer-arm point in the counterflow range is on the certified frontier: `α_R ⊂ Ē_R` and the counterflow
> avoids `E_R`. Both endpoints of `C` are on `γ`, hence in that range. The order of common contacts puts the intervening
> `β_R` arc between the same two endpoints. It cannot exit `C` through `α_R` or `γ` without violating their global
> closed-side order. Jordan separation gives the stated containment."

The selected pocket is the landed change pocket `changePocket R L r` of the right wall `R` and the left wall `L` (Aux.
lemma 33's Jordan component between consecutive contacts), read in the counterflow chart `m(z) = −1/z`
(`cfPocket R L r`, corners `x₀ = cfArcR 0`, `y₀ = cfArcR 1`). The certified frontier `M` (`β_R` for an outer right arm,
`β_L` for an outer left arm) lies between the walls (`WangWu.IsOrderedArcs R M L`) and shares no arc with either
(Lemma 6.13's (MD1) exclusion, `Lemma71I.NoCommonArc`). Then:

* **`exists_midTimes`** (R.3's clipping): by Wang–Wu's Lemma 4.22 (`WangWu.IsOrderedTriple.traverse`) the frontier
  `M` meets the closed pocket exactly on a disc-time interval `[σ_M, τ_M]` running from the opening corner to the
  closing corner, all of it in `C̄`;
* `midArc M σ_M τ_M` (the clipped frontier in the counterflow chart, from `x₀` to `y₀`): continuous, injective, in
  reverse first-visit order (from the wall's `IsWallReverseVisit`); **every point of `C̄ ∩ m(M)` in `ℍ` is on it**
  (`mem_midArc_of_mem_closure`);
* `negInv_mem_of_mem_frontier`: the frontier in `ℍ` of the forbidden side `m(E)` (`E = rightSideOf (range M)` or
  `leftSideOf (range M)`) lies on `m(M)` ("the certified frontier bounds the forbidden side");
* **`isErasurePocket_rightOuter`**: for an outer right wall (`range R ⊆ E_R ∪ range M`) and a counterflow avoiding
  `m(E_R)`, the erasure facts of the pocket (`IsErasurePocket`): Consequence R.4's `η⁻¹(C) ⊂ (τ, σ)` and the absence
  of a terminal gap are proved, with the barrier arcs `cfArcL` (the contained left side) and `midArc`; the inputs are
  the walls' reverse visit order, Aux. 42 (`GB10.NoSimpleArcInterval` for the counterflow), Aux. 37's attachment
  constancy along the contained side and §5.4's equal gap endpoints.

Conditional helpers with distinct names; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology Function
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R7StopIn

open WangWu Lemma71I PocketCoord PocketJordan Sec6

/-! ### The frontier of the forbidden side -/

section Forbidden

/-- **The certified frontier bounds the forbidden side**: if `E ⊆ ℍ` is open and a union of components of
`ℍ ∖ A` (`A` closed), every frontier point of `m(E)` in `ℍ` is the image of a point of `A`. -/
theorem negInv_mem_of_mem_frontier {A E : Set ℂ} (hA : IsClosed A) (hEH : E ⊆ H) (hEo : IsOpen E)
    (hEcc : ∀ e ∈ E, ∀ w ∈ connectedComponentIn (H \ A) e, w ∈ E) {z : ℂ}
    (hz : z ∈ frontier (negInv '' E)) (hzH : z ∈ H) : negInv z ∈ A := by
  by_contra hzA
  have hFo : IsOpen (negInv '' E) := isOpen_image_negInv' hEo hEH
  set w := negInv z with hw
  have hwH : w ∈ H := negInv_mem_H hzH
  have hUo : IsOpen (H \ A) := QuantumZipper.isOpen_H.sdiff hA
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hUo w ⟨hwH, hzA⟩
  -- `w` is a limit of points of `E`
  have hwcl : w ∈ closure E := by
    have hc : ContinuousWithinAt negInv (negInv '' E) z := by
      refine (continuousOn_negInv.continuousAt (QuantumZipper.isOpen_H.mem_nhds hzH)).continuousWithinAt
    have := hc.mem_closure_image (frontier_subset_closure hz)
    rwa [image_image, show (fun x => negInv (negInv x)) = id from funext negInv_negInv, image_id] at this
  obtain ⟨e, he, hed⟩ := Metric.mem_closure_iff.1 hwcl ε hε
  have hsub : ball w ε ⊆ connectedComponentIn (H \ A) w :=
    (convex_ball w ε).isPreconnected.subset_connectedComponentIn (mem_ball_self hε) hball
  have heC : e ∈ connectedComponentIn (H \ A) w := hsub (by rw [mem_ball, dist_comm]; exact hed)
  have hwC : w ∈ connectedComponentIn (H \ A) e := by
    rw [← connectedComponentIn_eq heC]
    exact mem_connectedComponentIn ⟨hwH, hzA⟩
  have hwE : w ∈ E := hEcc e he w hwC
  have hzF : z ∈ negInv '' E := ⟨w, hwE, by rw [hw, negInv_negInv]⟩
  have := hz.2
  rw [hFo.interior_eq] at this
  exact this hzF

/-- The right side of a closed set is a union of components of its complement in `ℍ`. -/
theorem rightSideOf_saturated {A : Set ℂ} :
    ∀ e ∈ rightSideOf A, ∀ w ∈ connectedComponentIn (H \ A) e, w ∈ rightSideOf A :=
  fun _ he _ hw => WangWu.mem_rightSideOf_of_mem_connectedComponentIn he hw

/-- The left side of a closed set is a union of components of its complement in `ℍ`. -/
theorem leftSideOf_saturated {A : Set ℂ} :
    ∀ e ∈ leftSideOf A, ∀ w ∈ connectedComponentIn (H \ A) e, w ∈ leftSideOf A :=
  fun _ he _ hw => WangWu.mem_leftSideOf_of_mem_connectedComponentIn he hw

/-- A counterflow avoiding `E` in the flow chart avoids `m(E)` in its own chart. -/
theorem notMem_image_negInv {E : Set ℂ} {z : ℂ} (hz : negInv z ∉ E) : z ∉ negInv '' E := by
  rintro ⟨e, he, rfl⟩
  rw [negInv_negInv] at hz
  exact hz he

end Forbidden

/-! ### The clipped certified frontier -/

section Mid

variable {R M L : ℝ≥0 → ℂ} {r : ℝ≥0}

/-- **Lemma R.3's clipping** (Wang–Wu Lemma 4.22 for the change pocket): a middle arc `M` between the walls, with no
common arc with either, meets the closed pocket (disc picture `cayley '' changePocket`) exactly on a disc-time interval
`[σ_M, τ_M]`, running from the opening corner `openPt` to the closing corner `closePt`. -/
theorem exists_midTimes (h : IsChangeConfigInc R L r)
    (hO : WangWu.IsOrderedArcs (realPath R) (realPath M) (realPath L)) (hcR : NoCommonArc M R)
    (hcL : NoCommonArc M L) :
    ∃ σM τM : ℝ, 0 ≤ σM ∧ σM < τM ∧ τM ≤ 1 ∧ toDisc (realPath M) σM = openPt R L r ∧
      toDisc (realPath M) τM = closePt R L r ∧
      (∀ t ∈ Icc σM τM, toDisc (realPath M) t ∈ closure (cayley '' changePocket R L r)) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, toDisc (realPath M) t ∈ closure (cayley '' changePocket R L r) → t ∈ Icc σM τM := by
  obtain ⟨hg, -, -, -, -, hC⟩ := h.changeCorners
  obtain ⟨σ, τ, h0σ, hστ, hτ1, hσa, hτb, hin, hout, -⟩ := hO.toTriple.traverse
    (interior_contact_toDisc hO.middle hO.right (interior_contact_eq_empty hcR))
    (interior_contact_toDisc hO.middle hO.left (interior_contact_eq_empty hcL)) hg
  refine ⟨σ, τ, h0σ, hστ, hτ1, hσa, hτb, fun t ht => hC ▸ hin t ht, fun t ht hcl => ?_⟩
  by_contra hn
  exact hout t ht hn (hC ▸ hcl)

/-- **The clipped certified frontier** in the counterflow chart, from `m(M̃(σ_M))` (`v = 0`) to `m(M̃(τ_M))`
(`v = 1`). -/
def midArc (M : ℝ≥0 → ℂ) (σM τM : ℝ) (v : ℝ) : ℂ := cfPt (toDisc (realPath M) (σM + v * (τM - σM)))

theorem midArc_image {σM τM : ℝ} (hστ : σM < τM) :
    midArc M σM τM '' Icc 0 1 = cfPt '' (toDisc (realPath M) '' Icc σM τM) := by
  rw [← image_affine_Icc_zero_one hστ.le, image_image, image_image]
  rfl

theorem midArc_zero (σM τM : ℝ) : midArc M σM τM 0 = cfPt (toDisc (realPath M) σM) := by
  simp only [midArc, zero_mul, add_zero]

theorem midArc_one (σM τM : ℝ) : midArc M σM τM 1 = cfPt (toDisc (realPath M) τM) := by
  simp only [midArc, one_mul, add_sub_cancel]

/-- The clipped frontier is a continuous injective arc (its disc times are positive). -/
theorem midArc_props (hM : IsSimpleProper M) {σM τM : ℝ} (hσ : 0 < σM) (hστ : σM < τM) (hτ : τM ≤ 1) :
    ContinuousOn (midArc M σM τM) (Icc 0 1) ∧ InjOn (midArc M σM τM) (Icc 0 1) := by
  have hαM := hM.isProperArc.isDiscCrosscut_toDisc
  have hI : Icc σM τM ⊆ Icc 0 1 := fun s hs => ⟨hσ.le.trans hs.1, hs.2.trans hτ⟩
  have hne : ∀ s ∈ Icc σM τM, toDisc (realPath M) s ≠ -1 := fun s hs he => by
    have := hαM.inj (hI hs) ⟨le_rfl, zero_le_one⟩ (he.trans hαM.zero.symm)
    linarith [hs.1]
  refine ⟨continuousOn_cfPt.comp
    (hαM.cont.comp (by fun_prop) fun s hs => hI ((PocketCoord.IsChangeConfigInc.affine_mem hστ).1 hs))
    fun s hs => hne _ ((PocketCoord.IsChangeConfigInc.affine_mem hστ).1 hs), fun s hs s' hs' he => ?_⟩
  have hm := (PocketCoord.IsChangeConfigInc.affine_mem hστ).1 hs
  have hm' := (PocketCoord.IsChangeConfigInc.affine_mem hστ).1 hs'
  exact PocketCoord.IsChangeConfigInc.affine_injective hστ
    (hαM.inj (hI hm) (hI hm') (injOn_cfPt (hne _ hm) (hne _ hm') he))

/-- **The clipped frontier is visited in reverse order** (Lemma 5.7 for `M` read along its disc times). -/
theorem midArc_rev (hM : IsSimpleProper M) {η : ℝ → ℂ} (hη0 : η 0 = 0) (hrev : IsWallReverseVisit M η)
    {σM τM : ℝ} (hσ : 0 < σM) (hστ : σM < τM) (hτ : τM ≤ 1) :
    R16.IsReverseVisitOrder (midArc M σM τM) fun t => η '' Icc 0 t := by
  intro t v₁ hv₁ v₂ hv₂ h12 hvis
  have hm₁ := (PocketCoord.IsChangeConfigInc.affine_mem hστ).1 hv₁
  have hm₂ := (PocketCoord.IsChangeConfigInc.affine_mem hστ).1 hv₂
  have hmono : σM + v₁ * (τM - σM) ≤ σM + v₂ * (τM - σM) := by
    have := mul_le_mul_of_nonneg_right h12 (sub_nonneg.2 hστ.le)
    linarith
  exact wall_rev hM hη0 hrev ⟨hσ.trans_le hm₁.1, hm₁.2.trans hτ⟩ ⟨hσ.trans_le hm₂.1, hm₂.2.trans hτ⟩ hmono hvis

/-- **Every point of `C̄ ∩ m(M)` in `ℍ` is on the clipped frontier** (Lemma R.3: "the order of common contacts puts
the intervening `β_R` arc between the same two endpoints"). -/
theorem mem_midArc_of_mem_closure (h : IsChangeConfigInc R L r) (hM : IsSimpleProper M) {σM τM : ℝ}
    (hστ : σM < τM)
    (hout : ∀ t ∈ Icc (0 : ℝ) 1, toDisc (realPath M) t ∈ closure (cayley '' changePocket R L r) → t ∈ Icc σM τM)
    {z : ℂ} (hzc : z ∈ closure (cfPocket R L r)) (hzH : z ∈ H) (hzM : negInv z ∈ range M) :
    z ∈ midArc M σM τM '' Icc 0 1 := by
  obtain ⟨t', ht'⟩ := hzM
  have hMH : M t' ∈ H := by rw [ht']; exact negInv_mem_H hzH
  have ht'0 : t' ≠ 0 := fun h0 => by
    rw [h0, hM.2.2.1] at hMH
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hMH)
  have hz : z = negInv (M t') := by rw [ht', negInv_negInv]
  have hcl := neg_cayley_mem_closure h.changePocket_subset_H hzc
  rw [hz, cayley_negInv (H_subset_Hbar' hMH) (WangWu.ne_zero_of_mem_H hMH), neg_neg,
    ← toDisc_realPath_discTime] at hcl
  have hmem := hout _ (discTime_mem_Icc t') hcl
  rw [midArc_image hστ]
  refine ⟨_, ⟨_, hmem, rfl⟩, ?_⟩
  rw [toDisc_realPath_discTime, cfPt_cayley (H_subset_Hbar' hMH) (WangWu.ne_zero_of_mem_H hMH), hz]

end Mid

/-! ### The two remaining pathwise inputs of the erasure -/

section Inputs

/-- **Aux. lemma 37 along one barrier** (§5.4: "On a contained strict-angle arm, the proof of Aux. 37 applies verbatim
to that one arm. The retained component field is constant during a no-`C` interval"; for a certified extremal arm
"the local confinement and Aux. 42 argument of Aux. 43 replaces this height mismatch"): the first-visit attachment of
the barrier `B` does not move on an interval `[a, b] ⊆ [τ, σ)` avoiding `C`. -/
def BarrierAttachConst (η : ℝ → ℂ) (C : Set ℂ) (B : ℝ → ℂ) (τ σ : ℝ) : Prop :=
  ∀ a b : ℝ, τ ≤ a → a ≤ b → b < σ → (∀ t ∈ Icc a b, η t ∉ C) →
    firstVisit (fun t => η '' Icc 0 t) B b = firstVisit (fun t => η '' Icc 0 t) B a

/-- **§5.4, "Closed gaps have identical endpoints"**: for a nondegenerate interval `[a, b] ⊆ [τ, σ)` avoiding `C`
whose right end is a limit of later visits and whose left end is `τ` or a limit of visits, `η(a) = η(b)`. -/
def PocketGapEq (η : ℝ → ℂ) (C : Set ℂ) (τ σ : ℝ) : Prop :=
  ∀ a b : ℝ, τ ≤ a → a < b → b < σ → (∀ t ∈ Icc a b, η t ∉ C) →
    b ∈ closure {t | a < t ∧ η t ∈ C} → (a = τ ∨ a ∈ closure {t | τ < t ∧ η t ∈ C}) → η a = η b

/-- **Aux. 42 for two compact simple arcs**: under GB10's pathwise conclusion for the counterflow (read on `[0, ∞)`),
no nontrivial time interval maps into the union of two compact simple arcs (Baire). -/
theorem not_image_subset_union_of_noSimpleArc {η : ℝ → ℂ} (hηc : ContinuousOn η (Ici 0))
    (h : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤) {A₁ A₂ : Set ℂ}
    (h₁ : Theorem14.GB10.IsSimpleArc A₁) (h₂ : Theorem14.GB10.IsSimpleArc A₂) :
    ∀ a b : ℝ, 0 ≤ a → a < b → ¬ η '' Icc a b ⊆ A₁ ∪ A₂ := by
  intro a b ha hab hsub
  set A : ℕ → Set ℂ := fun n => if n = 0 then A₁ else A₂ with hA
  have hAs : ∀ n, Theorem14.GB10.IsSimpleArc (A n) := fun n => by
    simp only [hA]; split_ifs; exacts [h₁, h₂]
  have hab' : a.toNNReal < b.toNNReal := (Real.toNNReal_lt_toNNReal_iff (ha.trans_lt hab)).2 hab
  refine h.not_image_subset_iUnion hab' ENNReal.coe_lt_top
    (hηc.comp continuous_subtype_val.continuousOn fun s _ => s.2) (A := A) hAs ?_
  rintro _ ⟨s, hs, rfl⟩
  have hs' : (s : ℝ) ∈ Icc a b := by
    constructor
    · have := NNReal.coe_le_coe.2 hs.1
      rwa [Real.coe_toNNReal _ ha] at this
    · have := NNReal.coe_le_coe.2 hs.2
      rwa [Real.coe_toNNReal _ (ha.trans hab.le)] at this
  rcases hsub ⟨_, hs', rfl⟩ with h | h
  · exact mem_iUnion.2 ⟨0, by simp only [hA, ↓reduceIte]; exact h⟩
  · exact mem_iUnion.2 ⟨1, by simp only [hA, one_ne_zero, ↓reduceIte]; exact h⟩

end Inputs

/-! ### The barriers of a change pocket -/

section Barrier

variable {R M L : ℝ≥0 → ℂ} {r : ℝ≥0}

/-- The left side of the change pocket is visited in reverse order when the left wall is (as in
`IsChangeConfigInc.isReversePocket_of_counterflow`). -/
theorem cfArcL_rev (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r)) {η : ℝ → ℂ}
    (hη0 : η 0 = 0) (hrevL : IsWallReverseVisit L η) :
    R16.IsReverseVisitOrder (cfArcL R L r) fun t => η '' Icc 0 t := by
  obtain ⟨-, -, -, ha, hb, hab, -⟩ := h.changeCorner_props
  have ha0 := h.leftLo_pos h0
  have hdL : ∀ s ∈ Icc (0 : ℝ) 1, leftLo R L r + s * (leftHi R L r - leftLo R L r) ∈ Ioc (0 : ℝ) 1 := fun s hs =>
    ⟨ha0.trans_le ((PocketCoord.IsChangeConfigInc.affine_mem hab).1 hs).1,
      ((PocketCoord.IsChangeConfigInc.affine_mem hab).1 hs).2.trans hb.2⟩
  intro t v₁ hv₁ v₂ hv₂ h12 hvis
  have hm : leftLo R L r + v₁ * (leftHi R L r - leftLo R L r) ≤ leftLo R L r + v₂ * (leftHi R L r - leftLo R L r) := by
    have := mul_le_mul_of_nonneg_right h12 (sub_nonneg.2 hab.le)
    linarith
  exact wall_rev h.left hη0 hrevL (hdL v₁ hv₁) (hdL v₂ hv₂) hm hvis

/-- The right side of the change pocket is visited in reverse order when the right wall is. -/
theorem cfArcR_rev (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r)) {η : ℝ → ℂ}
    (hη0 : η 0 = 0) (hrevR : IsWallReverseVisit R η) :
    R16.IsReverseVisitOrder (cfArcR R L r) fun t => η '' Icc 0 t := by
  obtain ⟨hu, hv, huv, -⟩ := h.changeCorner_props
  have hu0 := h.rightLo_pos h0
  have hdR : ∀ s ∈ Icc (0 : ℝ) 1, rightLo R L r + s * (rightHi R L r - rightLo R L r) ∈ Ioc (0 : ℝ) 1 := fun s hs =>
    ⟨hu0.trans_le ((PocketCoord.IsChangeConfigInc.affine_mem huv).1 hs).1,
      ((PocketCoord.IsChangeConfigInc.affine_mem huv).1 hs).2.trans hv.2⟩
  intro t v₁ hv₁ v₂ hv₂ h12 hvis
  have hm : rightLo R L r + v₁ * (rightHi R L r - rightLo R L r) ≤
      rightLo R L r + v₂ * (rightHi R L r - rightLo R L r) := by
    have := mul_le_mul_of_nonneg_right h12 (sub_nonneg.2 huv.le)
    linarith
  exact wall_rev h.right hη0 hrevR (hdR v₁ hv₁) (hdR v₂ hv₂) hm hvis

/-- **The clipped certified frontier as a barrier of the pocket** (Lemma R.3): for a middle arc `M` between the walls
of a pocket bounded in the counterflow chart, with no common arc with either wall and visited in reverse order, its
clipped part is a continuous injective arc from `x₀` to `y₀`, in reverse first-visit order, containing every point of
`C̄ ∩ m(M)` in `ℍ`, and with visited ends when `M` is entirely visited. -/
theorem exists_midArc (h : IsChangeConfigInc R L r) (hb : 0 < rightLo R L r) (hM : IsSimpleProper M)
    (hO : WangWu.IsOrderedArcs (realPath R) (realPath M) (realPath L)) (hcR : NoCommonArc M R)
    (hcL : NoCommonArc M L) {η : ℝ → ℂ} (hη0 : η 0 = 0) (hrevM : IsWallReverseVisit M η) :
    ∃ σM τM : ℝ, ContinuousOn (midArc M σM τM) (Icc 0 1) ∧ InjOn (midArc M σM τM) (Icc 0 1) ∧
      (R16.IsReverseVisitOrder (midArc M σM τM) fun t => η '' Icc 0 t) ∧
      midArc M σM τM 0 = cfArcR R L r 0 ∧ midArc M σM τM 1 = cfArcR R L r 1 ∧
      (∀ z ∈ closure (cfPocket R L r), z ∈ H → negInv z ∈ range M → z ∈ midArc M σM τM '' Icc 0 1) ∧
      (IsWallVisited M η → ∀ v ∈ Icc (0 : ℝ) 1, ∃ t, midArc M σM τM v ∈ η '' Icc 0 t) := by
  have h0 := PocketMarks.zero_notMem_closure_of_rightLo_pos h hb
  obtain ⟨σM, τM, h0σ, hστ, hτ1, hσa, hτb, -, hout⟩ := exists_midTimes h hO hcR hcL
  have hσpos : 0 < σM := by
    refine lt_of_le_of_ne h0σ fun he => h.openPt_ne_neg_one h0 ?_
    rw [← hσa, ← he]
    exact hM.isProperArc.isDiscCrosscut_toDisc.zero
  obtain ⟨hBc, hBi⟩ := midArc_props hM hσpos hστ hτ1
  refine ⟨σM, τM, hBc, hBi, midArc_rev hM hη0 hrevM hσpos hστ hτ1, ?_, ?_,
    fun z hzc hzH hzM => mem_midArc_of_mem_closure h hM hστ hout hzc hzH hzM, fun hvis v hv => ?_⟩
  · rw [midArc_zero, hσa, PocketCoord.IsChangeConfigInc.cfArcR_zero]
  · rw [midArc_one, hτb, PocketCoord.IsChangeConfigInc.cfArcR_one]
  · have hm := (PocketCoord.IsChangeConfigInc.affine_mem hστ).1 hv
    exact wall_visited hη0 hM hvis ⟨hσpos.trans_le hm.1, hm.2.trans hτ1⟩

/-- **An outer right side** (R.3: "An outer-arm point in the counterflow range is on the certified frontier"): if the
right wall lies in `E ∪ range M`, every point of the right side of the pocket is in the forbidden `m(E)` or on the
clipped frontier. -/
theorem cfArcR_mem_of_outer (h : IsChangeConfigInc R L r) (hb : 0 < rightLo R L r) {E : Set ℂ}
    (houter : range R ⊆ E ∪ range M) {B : ℝ → ℂ} (hB1 : B 1 = cfArcR R L r 1)
    (hBmem : ∀ z ∈ closure (cfPocket R L r), z ∈ H → negInv z ∈ range M → z ∈ B '' Icc 0 1) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : cfArcR R L r s ∈ negInv '' E ∪ B '' Icc 0 1 := by
  have h0 := PocketMarks.zero_notMem_closure_of_rightLo_pos h hb
  have hC := h.isCfPocket h0
  obtain ⟨hu, hv, huv, -⟩ := h.changeCorner_props
  have hu0 := h.rightLo_pos h0
  have hzcl : cfArcR R L r s ∈ closure (cfPocket R L r) :=
    frontier_subset_closure (by rw [hC.frontier_eq]; exact Or.inl ⟨s, hs, rfl⟩)
  rcases eq_or_lt_of_le hs.2 with hs1 | hs1
  · exact Or.inr ⟨1, ⟨zero_le_one, le_rfl⟩, by rw [hB1, hs1]⟩
  · have hd : rightLo R L r + s * (rightHi R L r - rightLo R L r) ∈ Ioo (0 : ℝ) 1 :=
      ⟨hu0.trans_le ((PocketCoord.IsChangeConfigInc.affine_mem huv).1 hs).1,
        ((PocketCoord.IsChangeConfigInc.affine_mem huv).2.2 ⟨hs.1, hs1⟩).2.trans_le hv.2⟩
    obtain ⟨e, hpos⟩ := cfPt_toDisc_of_mem h.right hd
    have hz : cfArcR R L r s =
        negInv (R (arcTime (rightLo R L r + s * (rightHi R L r - rightLo R L r))).toNNReal) := e
    rcases houter ⟨_, rfl⟩ with hE | hMr
    · exact Or.inl ⟨_, hE, hz.symm⟩
    · have hRH := h.right.2.2.2.1 _ hpos
      refine Or.inr (hBmem _ hzcl ?_ ?_)
      · rw [hz]; exact negInv_mem_H hRH
      · rw [hz, negInv_negInv]; exact hMr

/-- **An outer left side**: if the left wall lies in `E ∪ range M`, every point of the left side of the pocket is in
`m(E)` or on the clipped frontier. -/
theorem cfArcL_mem_of_outer (h : IsChangeConfigInc R L r) (hb : 0 < rightLo R L r) {E : Set ℂ}
    (houter : range L ⊆ E ∪ range M) {B : ℝ → ℂ} (hB1 : B 1 = cfArcR R L r 1)
    (hBmem : ∀ z ∈ closure (cfPocket R L r), z ∈ H → negInv z ∈ range M → z ∈ B '' Icc 0 1) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : cfArcL R L r s ∈ negInv '' E ∪ B '' Icc 0 1 := by
  have h0 := PocketMarks.zero_notMem_closure_of_rightLo_pos h hb
  have hC := h.isCfPocket h0
  obtain ⟨-, -, -, ha, hbb, hab, -⟩ := h.changeCorner_props
  have ha0 := h.leftLo_pos h0
  have hzcl : cfArcL R L r s ∈ closure (cfPocket R L r) :=
    frontier_subset_closure (by rw [hC.frontier_eq]; exact Or.inr ⟨s, hs, rfl⟩)
  rcases eq_or_lt_of_le hs.2 with hs1 | hs1
  · exact Or.inr ⟨1, ⟨zero_le_one, le_rfl⟩, by rw [hB1, hs1, hC.seed]⟩
  · have hd : leftLo R L r + s * (leftHi R L r - leftLo R L r) ∈ Ioo (0 : ℝ) 1 :=
      ⟨ha0.trans_le ((PocketCoord.IsChangeConfigInc.affine_mem hab).1 hs).1,
        ((PocketCoord.IsChangeConfigInc.affine_mem hab).2.2 ⟨hs.1, hs1⟩).2.trans_le hbb.2⟩
    obtain ⟨e, hpos⟩ := cfPt_toDisc_of_mem h.left hd
    have hz : cfArcL R L r s =
        negInv (L (arcTime (leftLo R L r + s * (leftHi R L r - leftLo R L r))).toNNReal) := e
    rcases houter ⟨_, rfl⟩ with hE | hMr
    · exact Or.inl ⟨_, hE, hz.symm⟩
    · have hLH := h.left.2.2.2.1 _ hpos
      refine Or.inr (hBmem _ hzcl ?_ ?_)
      · rw [hz]; exact negInv_mem_H hLH
      · rw [hz, negInv_negInv]; exact hMr

/-- The forbidden side `m(rightSideOf (range M))` is open and its frontier in `ℍ` lies on `m(M)`. -/
theorem forbidden_right (hM : IsSimpleProper M) :
    IsOpen (negInv '' rightSideOf (range M)) ∧
      ∀ z ∈ frontier (negInv '' rightSideOf (range M)), z ∈ H → negInv z ∈ range M := by
  have hMcl : IsClosed (range M) := Lemma71Pin.IsSimpleProper.isClosed_range hM
  have hEo : IsOpen (rightSideOf (range M)) :=
    Theorem14.SB.isOpen_rightSideOf (by rw [hMcl.closure_eq]; exact inter_subset_left)
  have hEH : rightSideOf (range M) ⊆ H := fun _ hz => hz.1.1
  exact ⟨isOpen_image_negInv' hEo hEH, fun z hz hzH =>
    negInv_mem_of_mem_frontier hMcl hEH hEo rightSideOf_saturated hz hzH⟩

/-- The forbidden side `m(leftSideOf (range M))` is open and its frontier in `ℍ` lies on `m(M)`. -/
theorem forbidden_left (hM : IsSimpleProper M) :
    IsOpen (negInv '' leftSideOf (range M)) ∧
      ∀ z ∈ frontier (negInv '' leftSideOf (range M)), z ∈ H → negInv z ∈ range M := by
  have hMcl : IsClosed (range M) := Lemma71Pin.IsSimpleProper.isClosed_range hM
  have hEo : IsOpen (leftSideOf (range M)) :=
    Theorem14.SB.isOpen_leftSideOf (by rw [hMcl.closure_eq]; exact inter_subset_left)
  have hEH : leftSideOf (range M) ⊆ H := fun _ hz => hz.1.1
  exact ⟨isOpen_image_negInv' hEo hEH, fun z hz hzH =>
    negInv_mem_of_mem_frontier hMcl hEH hEo leftSideOf_saturated hz hzH⟩

end Barrier

/-! ### The three mixed and outer pockets -/

section Assemble

variable {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- **The erasure facts of a mixed pocket with an outer right arm** (Lemma R.3, Consequence R.4, §5.4). Walls: the
outer right arm `R` (`range R ⊆ E_R ∪ range M`, `E_R = rightSideOf (range M)`) and the contained left arm `L`; `M` the
certified right frontier between them with no common arc with either; the pocket bounded in the counterflow chart.
Counterflow: a continuous Loewner trace avoiding `m(E_R)`, visiting `L` and `M` in reverse order and every point of
`M`, with Aux. 42 (`GB10.NoSimpleArcInterval`), Aux. 37 along the contained side `cfArcL` and §5.4's equal gap
endpoints. -/
theorem isErasurePocket_rightOuter (h : IsChangeConfigInc R L r) (hb : 0 < rightLo R L r) (hM : IsSimpleProper M)
    (hO : WangWu.IsOrderedArcs (realPath R) (realPath M) (realPath L)) (hcR : NoCommonArc M R)
    (hcL : NoCommonArc M L) (houter : range R ⊆ rightSideOf (range M) ∪ range M)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M)) (hrevL : IsWallReverseVisit L η)
    (hrevM : IsWallReverseVisit M η) (hvisM : IsWallVisited M η)
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤)
    (hAC : BarrierAttachConst η (cfPocket R L r) (cfArcL R L r) (firstHit η (cfArcR R L r 1))
      (firstHit η (cfArcR R L r 0)))
    (hgap : PocketGapEq η (cfPocket R L r) (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0))) :
    IsErasurePocket η (cfPocket R L r) (cfArcR R L r 0) (cfArcR R L r 1) (firstHit η (cfArcR R L r 1))
      (firstHit η (cfArcR R L r 0)) := by
  have h0 := PocketMarks.zero_notMem_closure_of_rightLo_pos h hb
  have hC := h.isCfPocket h0
  have hη0 : η 0 = 0 := hη.1
  obtain ⟨σM, τM, hBc, hBi, hBrev, hB0, hB1, hBmem, hBvis⟩ := exists_midArc h hb hM hO hcR hcL hη0 hrevM
  obtain ⟨hFo, hFfr⟩ := forbidden_right hM
  obtain ⟨hτ0, hτ, hτf⟩ := firstHit_spec hη.2.1 (hB1 ▸ hBvis hvisM 1 ⟨zero_le_one, le_rfl⟩)
  obtain ⟨hσ0, hσ, hσf⟩ := firstHit_spec hη.2.1 (hB0 ▸ hBvis hvisM 0 ⟨le_rfl, zero_le_one⟩)
  have hxy : cfArcR R L r 0 ≠ cfArcR R L r 1 := fun he =>
    zero_ne_one (hC.inj₁ ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ he)
  have hfr : frontier (cfPocket R L r) ⊆
      negInv '' rightSideOf (range M) ∪ (cfArcL R L r '' Icc 0 1 ∪ midArc M σM τM '' Icc 0 1) := by
    rw [hC.frontier_eq]
    rintro z (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · rcases cfArcR_mem_of_outer h hb houter hB1 hBmem hs with h' | h'
      exacts [Or.inl h', Or.inr (Or.inr h')]
    · exact Or.inr (Or.inl ⟨s, hs, rfl⟩)
  exact isErasurePocket_of_barriers hη hW hW0 hC.isOpen hC.isBounded
    (PocketJordan.image_negInv_subset_H h.changePocket_subset_H) hFo hC.cont₂ hC.inj₂ (cfArcL_rev h h0 hη0 hrevL)
    hBrev hC.junction hC.seed hB0 hB1 hfr (fun z hz => Or.inr (hBmem z hz.1.1 hz.2 (hFfr z hz.1.2 hz.2)))
    (fun t ht => notMem_image_negInv (havoid t ht))
    (not_image_subset_union_of_noSimpleArc hη.2.1 h42 ⟨_, hC.cont₂, hC.inj₂, rfl⟩ ⟨_, hBc, hBi, rfl⟩)
    hτ0 hτ hτf hσ0 hσ hσf hxy hAC hgap

/-- **The erasure facts of a mixed pocket with an outer left arm** (the reflected statement): the contained right arm
`R`, the outer left arm `L` (`range L ⊆ E_L ∪ range M`, `E_L = leftSideOf (range M)`), `M` the certified left frontier
between them; Aux. 37 along the contained side `cfArcR`. -/
theorem isErasurePocket_leftOuter (h : IsChangeConfigInc R L r) (hb : 0 < rightLo R L r) (hM : IsSimpleProper M)
    (hO : WangWu.IsOrderedArcs (realPath R) (realPath M) (realPath L)) (hcR : NoCommonArc M R)
    (hcL : NoCommonArc M L) (houter : range L ⊆ leftSideOf (range M) ∪ range M)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ leftSideOf (range M)) (hrevR : IsWallReverseVisit R η)
    (hrevM : IsWallReverseVisit M η) (hvisM : IsWallVisited M η)
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤)
    (hAC : BarrierAttachConst η (cfPocket R L r) (cfArcR R L r) (firstHit η (cfArcR R L r 1))
      (firstHit η (cfArcR R L r 0)))
    (hgap : PocketGapEq η (cfPocket R L r) (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0))) :
    IsErasurePocket η (cfPocket R L r) (cfArcR R L r 0) (cfArcR R L r 1) (firstHit η (cfArcR R L r 1))
      (firstHit η (cfArcR R L r 0)) := by
  have h0 := PocketMarks.zero_notMem_closure_of_rightLo_pos h hb
  have hC := h.isCfPocket h0
  have hη0 : η 0 = 0 := hη.1
  obtain ⟨σM, τM, hBc, hBi, hBrev, hB0, hB1, hBmem, hBvis⟩ := exists_midArc h hb hM hO hcR hcL hη0 hrevM
  obtain ⟨hFo, hFfr⟩ := forbidden_left hM
  obtain ⟨hτ0, hτ, hτf⟩ := firstHit_spec hη.2.1 (hB1 ▸ hBvis hvisM 1 ⟨zero_le_one, le_rfl⟩)
  obtain ⟨hσ0, hσ, hσf⟩ := firstHit_spec hη.2.1 (hB0 ▸ hBvis hvisM 0 ⟨le_rfl, zero_le_one⟩)
  have hxy : cfArcR R L r 0 ≠ cfArcR R L r 1 := fun he =>
    zero_ne_one (hC.inj₁ ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ he)
  have hfr : frontier (cfPocket R L r) ⊆
      negInv '' leftSideOf (range M) ∪ (cfArcR R L r '' Icc 0 1 ∪ midArc M σM τM '' Icc 0 1) := by
    rw [hC.frontier_eq]
    rintro z (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · exact Or.inr (Or.inl ⟨s, hs, rfl⟩)
    · rcases cfArcL_mem_of_outer h hb houter hB1 hBmem hs with h' | h'
      exacts [Or.inl h', Or.inr (Or.inr h')]
  exact isErasurePocket_of_barriers hη hW hW0 hC.isOpen hC.isBounded
    (PocketJordan.image_negInv_subset_H h.changePocket_subset_H) hFo hC.cont₁ hC.inj₁ (cfArcR_rev h h0 hη0 hrevR)
    hBrev rfl rfl hB0 hB1 hfr (fun z hz => Or.inr (hBmem z hz.1.1 hz.2 (hFfr z hz.1.2 hz.2)))
    (fun t ht => notMem_image_negInv (havoid t ht))
    (not_image_subset_union_of_noSimpleArc hη.2.1 h42 ⟨_, hC.cont₁, hC.inj₁, rfl⟩ ⟨_, hBc, hBi, rfl⟩)
    hτ0 hτ hτf hσ0 hσ hσf hxy hAC hgap

/-- **The erasure facts of a pocket with two outer arms** (Lemma R.3: "The analogous statement for two outer arms
uses both `β_R` and `β_L`"): `range R ⊆ E_R ∪ range M₁`, `range L ⊆ E_L ∪ range M₂` with the certified frontiers
`M₁ = β_R`, `M₂ = β_L` between the walls; the counterflow avoids `m(E_R ∪ E_L)`; the two clipped frontiers are the
barriers, Aux. 37 (Aux. 43 for an extremal arm) along the clipped `β_R`. -/
theorem isErasurePocket_outerOuter (h : IsChangeConfigInc R L r) (hb : 0 < rightLo R L r) {M₁ M₂ : ℝ≥0 → ℂ}
    (hM₁ : IsSimpleProper M₁) (hM₂ : IsSimpleProper M₂)
    (hO₁ : WangWu.IsOrderedArcs (realPath R) (realPath M₁) (realPath L))
    (hO₂ : WangWu.IsOrderedArcs (realPath R) (realPath M₂) (realPath L)) (hc₁R : NoCommonArc M₁ R)
    (hc₁L : NoCommonArc M₁ L) (hc₂R : NoCommonArc M₂ R) (hc₂L : NoCommonArc M₂ L)
    (houterR : range R ⊆ rightSideOf (range M₁) ∪ range M₁) (houterL : range L ⊆ leftSideOf (range M₂) ∪ range M₂)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M₁) ∪ leftSideOf (range M₂))
    (hrev₁ : IsWallReverseVisit M₁ η) (hrev₂ : IsWallReverseVisit M₂ η) (hvis₁ : IsWallVisited M₁ η)
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤)
    (hAC : ∀ σ₁ τ₁ : ℝ, midArc M₁ σ₁ τ₁ 0 = cfArcR R L r 0 → midArc M₁ σ₁ τ₁ 1 = cfArcR R L r 1 →
      BarrierAttachConst η (cfPocket R L r) (midArc M₁ σ₁ τ₁) (firstHit η (cfArcR R L r 1))
        (firstHit η (cfArcR R L r 0)))
    (hgap : PocketGapEq η (cfPocket R L r) (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0))) :
    IsErasurePocket η (cfPocket R L r) (cfArcR R L r 0) (cfArcR R L r 1) (firstHit η (cfArcR R L r 1))
      (firstHit η (cfArcR R L r 0)) := by
  have h0 := PocketMarks.zero_notMem_closure_of_rightLo_pos h hb
  have hC := h.isCfPocket h0
  have hη0 : η 0 = 0 := hη.1
  obtain ⟨σ₁, τ₁, hB₁c, hB₁i, hB₁rev, hB₁0, hB₁1, hB₁mem, hB₁vis⟩ := exists_midArc h hb hM₁ hO₁ hc₁R hc₁L hη0 hrev₁
  obtain ⟨σ₂, τ₂, hB₂c, hB₂i, hB₂rev, hB₂0, hB₂1, hB₂mem, -⟩ := exists_midArc h hb hM₂ hO₂ hc₂R hc₂L hη0 hrev₂
  obtain ⟨hF₁o, hF₁fr⟩ := forbidden_right hM₁
  obtain ⟨hF₂o, hF₂fr⟩ := forbidden_left hM₂
  obtain ⟨hτ0, hτ, hτf⟩ := firstHit_spec hη.2.1 (hB₁1 ▸ hB₁vis hvis₁ 1 ⟨zero_le_one, le_rfl⟩)
  obtain ⟨hσ0, hσ, hσf⟩ := firstHit_spec hη.2.1 (hB₁0 ▸ hB₁vis hvis₁ 0 ⟨le_rfl, zero_le_one⟩)
  have hxy : cfArcR R L r 0 ≠ cfArcR R L r 1 := fun he =>
    zero_ne_one (hC.inj₁ ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ he)
  have hfr : frontier (cfPocket R L r) ⊆ (negInv '' rightSideOf (range M₁) ∪ negInv '' leftSideOf (range M₂)) ∪
      (midArc M₁ σ₁ τ₁ '' Icc 0 1 ∪ midArc M₂ σ₂ τ₂ '' Icc 0 1) := by
    rw [hC.frontier_eq]
    rintro z (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · rcases cfArcR_mem_of_outer h hb houterR hB₁1 hB₁mem hs with h' | h'
      exacts [Or.inl (Or.inl h'), Or.inr (Or.inl h')]
    · rcases cfArcL_mem_of_outer h hb houterL hB₂1 hB₂mem hs with h' | h'
      exacts [Or.inl (Or.inr h'), Or.inr (Or.inr h')]
  have hFfr : closure (cfPocket R L r) ∩ frontier (negInv '' rightSideOf (range M₁) ∪
      negInv '' leftSideOf (range M₂)) ∩ H ⊆ midArc M₁ σ₁ τ₁ '' Icc 0 1 ∪ midArc M₂ σ₂ τ₂ '' Icc 0 1 := by
    rintro z ⟨⟨hzc, hzf⟩, hzH⟩
    rcases frontier_union_subset _ _ hzf with ⟨hz1, -⟩ | ⟨-, hz2⟩
    · exact Or.inl (hB₁mem z hzc hzH (hF₁fr z hz1 hzH))
    · exact Or.inr (hB₂mem z hzc hzH (hF₂fr z hz2 hzH))
  have havoid' : ∀ t, 0 ≤ t → η t ∉ negInv '' rightSideOf (range M₁) ∪ negInv '' leftSideOf (range M₂) :=
    fun t ht hm => by
      rcases hm with hm | hm
      · exact notMem_image_negInv (fun h' => havoid t ht (Or.inl h')) hm
      · exact notMem_image_negInv (fun h' => havoid t ht (Or.inr h')) hm
  exact isErasurePocket_of_barriers hη hW hW0 hC.isOpen hC.isBounded
    (PocketJordan.image_negInv_subset_H h.changePocket_subset_H) (hF₁o.union hF₂o) hB₁c hB₁i hB₁rev hB₂rev
    hB₁0 hB₁1 hB₂0 hB₂1 hfr hFfr havoid'
    (not_image_subset_union_of_noSimpleArc hη.2.1 h42 ⟨_, hB₁c, hB₁i, rfl⟩ ⟨_, hB₂c, hB₂i, rfl⟩)
    hτ0 hτ hτf hσ0 hσ hσf hxy (hAC σ₁ τ₁ hB₁0 hB₁1) hgap

end Assemble

end InteractingSLE.Sec7.R7StopIn
