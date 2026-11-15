/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux36FaceArm

/-!
# The central face of a fixed chart from the physical pocket (Aux. lemma 36, chart-face geometry)

Specification §6.2, **Aux.** lemma 36 (`source/spec/p193-240.md` L36–L78, pp. 195–196) and ruling
R41's note (`source/external/AstraIG1/ig1_ztip_elimination.txt` §1.1, (1.1)–(1.2), and
Propositions 1.5–1.6). The physical pocket `C` (open, bounded: its junction `x_C` is an interior
point) is bounded by two incoming subarcs `α₁([c₁, e₁])`, `α₂([c₂, e₂])` from
`x_C = α₁(c₁) = α₂(c₂)`.
At the chart time `r` the prefixes `α_i([c_i, u_i))` are unvisited and lie in `D_r = ℍ \ K_r`,
while the suffixes `α_i([u_i, e_i])` are not in `D_r` (they are visited). By `exists_arm` the
prefixes lift to arms `a_i` in the `g_r` chart from the gates `q_i` to `z = g_r(x_C)`.

"These faces are exactly the image of `E_T`. Indeed, inside `D_T` the only portions of `∂C` are the
two incoming arcs." This file proves that the face `F_r` (the inner side of
`Γ = A₁ ∪ A₂ ∪ [q₁, q₂]`, or of `A₁ ∪ A₂` when `q₁ = q₂`) satisfies, for `w ∈ ℍ`,
`f̄_r(w) ∈ C ↔ w ∈ F_r` — this is (1.1) together with `f̄_r(F_r) ⊆ C` — and derives the gap
equality of Propositions 1.5–1.6 (old start) from the physical pocket data.

## Main results

* `trMap_mem_iff_of_arms`: the face identification for any Jordan curve `Γ` whose part in `ℍ` is
  the two open arms and whose real points are `[q₁, q₂]`;
* `trMap_mem_iff_innerSide`, `trMap_mem_iff_innerSide_eq`: the distinct-gate and equal-gate faces;
* `ownFuture_gap_eq_of_face_eq`: the gap equality for equal gates;
* `ownFuture_gap_eq_of_pocket`: **Propositions 1.5 (old start) and 1.6 (`p ∈ R_s`) from the
  physical pocket data** (finite junction): `δ_s(a) = δ_s(b)` for `s ≤ r` and `η(a) = η(b)`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec6

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- **The face identification in a fixed chart** (generic form). The pocket `C` is open and
bounded, `∂C = α₁([c₁, e₁]) ∪ α₂([c₂, e₂])`, the prefixes `α_i([c_i, u_i))` lie in `D_r` and the
suffixes `α_i([u_i, e_i])` do not; `a_i((0, 1]) = g_r(α_i([c_i, u_i)))`. If `Γ ⊆ ℍ̄` is a Jordan
curve with real points `[q₁, q₂]` whose part in `ℍ` is exactly `a₁((0, 1]) ∪ a₂((0, 1])`, then
`f̄_r(w) ∈ C ↔ w ∈ innerSide Γ` for `w ∈ ℍ`. -/
theorem trMap_mem_iff_of_arms (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {r : ℝ} (hr : 0 ≤ r) {C : Set ℂ} (hC : IsOpen C) (hCb : IsBounded C) {α₁ α₂ : ℝ → ℂ}
    {c₁ u₁ e₁ c₂ u₂ e₂ : ℝ} (hcu₁ : c₁ < u₁) (hue₁ : u₁ ≤ e₁) (hue₂ : u₂ ≤ e₂)
    (hfrC : frontier C = α₁ '' Icc c₁ e₁ ∪ α₂ '' Icc c₂ e₂)
    (hα₁D : ∀ v ∈ Ico c₁ u₁, α₁ v ∈ H \ fwdHull W r)
    (hα₂D : ∀ v ∈ Ico c₂ u₂, α₂ v ∈ H \ fwdHull W r)
    (hα₁K : ∀ v ∈ Icc u₁ e₁, α₁ v ∉ H \ fwdHull W r)
    (hα₂K : ∀ v ∈ Icc u₂ e₂, α₂ v ∉ H \ fwdHull W r) {a₁ a₂ : ℝ → ℂ}
    (ha₁img : a₁ '' Ioc 0 1 = fwdMap W r '' (α₁ '' Ico c₁ u₁))
    (ha₂img : a₂ '' Ioc 0 1 = fwdMap W r '' (α₂ '' Ico c₂ u₂)) {Γ : Set ℂ} {q₁ q₂ : ℝ}
    (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) (hΓH : Γ ⊆ Hbar)
    (hΓR : ∀ x : ℝ, (x : ℂ) ∈ Γ ↔ x ∈ Icc q₁ q₂)
    (hΓA : ∀ w ∈ Γ, w ∈ H → w ∈ a₁ '' Ioc 0 1 ∪ a₂ '' Ioc 0 1)
    (hAΓ : a₁ '' Ioc 0 1 ∪ a₂ '' Ioc 0 1 ⊆ Γ) {w : ℂ} (hw : w ∈ H) :
    trMap W 0 r w ∈ C ↔ w ∈ innerSide Γ := by
  obtain ⟨K, hK⟩ := exists_norm_trMap_zero_sub_le hW hW0 hr
  have hF : ContinuousOn (trMap W 0 r) H :=
    (YuanSimpleApprox.trMap_continuousOn hη hW hW0 le_rfl hr).mono H_subset_Hbar
  -- the arms map onto the unvisited prefixes, which lie on `∂C`
  have harm : ∀ y ∈ a₁ '' Ioc 0 1 ∪ a₂ '' Ioc 0 1, trMap W 0 r y ∈ frontier C := by
    rintro y (hy | hy)
    · rw [ha₁img] at hy
      obtain ⟨_, ⟨v, hv, rfl⟩, rfl⟩ := hy
      rw [trMap_zero_fwdMap hW hW0 hr (hα₁D v hv), hfrC]
      exact Or.inl ⟨v, ⟨hv.1, hv.2.le.trans hue₁⟩, rfl⟩
    · rw [ha₂img] at hy
      obtain ⟨_, ⟨v, hv, rfl⟩, rfl⟩ := hy
      rw [trMap_zero_fwdMap hW hW0 hr (hα₂D v hv), hfrC]
      exact Or.inr ⟨v, ⟨hv.1, hv.2.le.trans hue₂⟩, rfl⟩
  have hJC : ∀ y ∈ Γ, y ∈ H → trMap W 0 r y ∉ C := by
    intro y hyΓ hyH hyC
    have h1 := harm y (hΓA y hyΓ hyH)
    rw [hC.frontier_eq] at h1
    exact h1.2 hyC
  have hfr : ∀ y ∈ H, trMap W 0 r y ∈ frontier C → y ∈ Γ := by
    intro y hyH hyC
    have hD := trMap_zero_mem_domain hW hW0 hr hyH
    have hy : y = fwdMap W r (trMap W 0 r y) := (fwdMap_trMap_zero hW hW0 hr hyH).symm
    rw [hfrC] at hyC
    rcases hyC with ⟨v, hv, hvy⟩ | ⟨v, hv, hvy⟩
    · have hvu : v < u₁ := by
        by_contra h
        push Not at h
        exact hα₁K v ⟨h, hv.2⟩ (hvy ▸ hD)
      refine hAΓ (Or.inl ?_)
      rw [ha₁img, hy, ← hvy]
      exact ⟨α₁ v, ⟨v, ⟨hv.1, hvu⟩, rfl⟩, rfl⟩
    · have hvu : v < u₂ := by
        by_contra h
        push Not at h
        exact hα₂K v ⟨h, hv.2⟩ (hvy ▸ hD)
      refine hAΓ (Or.inr ?_)
      rw [ha₂img, hy, ← hvy]
      exact ⟨α₂ v, ⟨v, ⟨hv.1, hvu⟩, rfl⟩, rfl⟩
  -- `C` meets `D_r` near the junction
  have hCF : ∃ p ∈ H, trMap W 0 r p ∈ C := by
    have hx₀D := hα₁D c₁ ⟨le_rfl, hcu₁⟩
    have hx₀fr : α₁ c₁ ∈ frontier C := by
      rw [hfrC]; exact Or.inl ⟨c₁, ⟨le_rfl, hcu₁.le.trans hue₁⟩, rfl⟩
    obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.1
      (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hr) _ hx₀D
    obtain ⟨y, hyb, hyC⟩ := mem_closure_iff.1 (frontier_subset_closure hx₀fr) _ isOpen_ball
      (mem_ball_self hε)
    have hyD := hεD hyb
    exact ⟨fwdMap W r y, QuantumZipper.FwdHolo.mapsTo_fwdMap hW hr hyD,
      by rw [trMap_zero_fwdMap hW hW0 hr hyD]; exact hyC⟩
  exact mem_innerSide_iff hΓ hΓH hΓR hC hCb hF hK hJC hfr hCF hw

/-- An arm `a : [0, 1] → ℍ̄` with `a 0 = q`, open in `ℍ`, lies in `ℍ̄`. -/
theorem image_arm_subset_Hbar {a : ℝ → ℂ} {q : ℝ} (ha0 : a 0 = q)
    (haH : ∀ t ∈ Ioc (0 : ℝ) 1, a t ∈ H) : a '' Icc 0 1 ⊆ Hbar := by
  rintro _ ⟨t, ht, rfl⟩
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h, ha0]; exact ofReal_mem_Hbar q
  · exact H_subset_Hbar (haH t ⟨h, ht.2⟩)

/-- A point of an arm is its gate or a point of the open arm. -/
theorem eq_or_mem_open_arm {a : ℝ → ℂ} {q : ℝ} (ha0 : a 0 = q) {w : ℂ} (hw : w ∈ a '' Icc 0 1) :
    w = q ∨ w ∈ a '' Ioc 0 1 := by
  obtain ⟨t, ht, rfl⟩ := hw
  rcases eq_or_lt_of_le ht.1 with h | h
  · left; rw [← h, ha0]
  · exact Or.inr ⟨t, ⟨h, ht.2⟩, rfl⟩

/-- **The distinct-gate face** `F_r = innerSide (A₁ ∪ A₂ ∪ [q₁, q₂])`: (1.1) and `f̄_r(F_r) ⊆ C`
in one statement. -/
theorem trMap_mem_iff_innerSide (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {r : ℝ} (hr : 0 ≤ r) {C : Set ℂ} (hC : IsOpen C) (hCb : IsBounded C) {α₁ α₂ : ℝ → ℂ}
    {c₁ u₁ e₁ c₂ u₂ e₂ : ℝ} (hcu₁ : c₁ < u₁) (hue₁ : u₁ ≤ e₁) (hue₂ : u₂ ≤ e₂)
    (hfrC : frontier C = α₁ '' Icc c₁ e₁ ∪ α₂ '' Icc c₂ e₂)
    (hα₁D : ∀ v ∈ Ico c₁ u₁, α₁ v ∈ H \ fwdHull W r)
    (hα₂D : ∀ v ∈ Ico c₂ u₂, α₂ v ∈ H \ fwdHull W r)
    (hα₁K : ∀ v ∈ Icc u₁ e₁, α₁ v ∉ H \ fwdHull W r)
    (hα₂K : ∀ v ∈ Icc u₂ e₂, α₂ v ∉ H \ fwdHull W r) {q₁ q₂ : ℝ} {z : ℂ} {a₁ a₂ : ℝ → ℂ}
    (hq : q₁ < q₂) (ha₁ : ContinuousOn a₁ (Icc 0 1)) (ha₂ : ContinuousOn a₂ (Icc 0 1))
    (ha₁i : InjOn a₁ (Icc 0 1)) (ha₂i : InjOn a₂ (Icc 0 1)) (ha₁0 : a₁ 0 = q₁)
    (ha₂0 : a₂ 0 = q₂) (ha₁1 : a₁ 1 = z) (ha₂1 : a₂ 1 = z) (ha₁H : ∀ t ∈ Ioc (0 : ℝ) 1, a₁ t ∈ H)
    (ha₂H : ∀ t ∈ Ioc (0 : ℝ) 1, a₂ t ∈ H) (h12 : a₁ '' Icc 0 1 ∩ a₂ '' Icc 0 1 ⊆ {z})
    (ha₁img : a₁ '' Ioc 0 1 = fwdMap W r '' (α₁ '' Ico c₁ u₁))
    (ha₂img : a₂ '' Ioc 0 1 = fwdMap W r '' (α₂ '' Ico c₂ u₂)) {w : ℂ} (hw : w ∈ H) :
    trMap W 0 r w ∈ C ↔ w ∈ innerSide (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂) := by
  obtain ⟨hΓJ, hΓH⟩ := isJordanCurve_faceBoundary hq ha₁ ha₂ ha₁i ha₂i ha₁0 ha₂0 ha₁1 ha₂1 ha₁H
    ha₂H h12
  refine trMap_mem_iff_of_arms hη hW hW0 hr hC hCb hcu₁ hue₁ hue₂ hfrC hα₁D hα₂D hα₁K hα₂K
    ha₁img ha₂img hΓJ hΓH (q₁ := q₁) (q₂ := q₂) ?_ ?_ ?_ hw
  · intro x
    constructor
    · rintro ((h | h) | ⟨y, hy, hyx⟩)
      · have := ofReal_injective (arm_real ha₁0 ha₁H h (by simp))
        rw [this]; exact ⟨le_rfl, hq.le⟩
      · have := ofReal_injective (arm_real ha₂0 ha₂H h (by simp))
        rw [this]; exact ⟨hq.le, le_rfl⟩
      · rw [← ofReal_injective hyx]; exact hy
    · intro hx; exact Or.inr ⟨x, hx, rfl⟩
  · rintro y ((hy | hy) | ⟨x, -, rfl⟩) hyH
    · rcases eq_or_mem_open_arm ha₁0 hy with h | h
      · exact absurd (h ▸ hyH) (not_mem_H_ofReal q₁)
      · exact Or.inl h
    · rcases eq_or_mem_open_arm ha₂0 hy with h | h
      · exact absurd (h ▸ hyH) (not_mem_H_ofReal q₂)
      · exact Or.inr h
    · exact absurd hyH (not_mem_H_ofReal x)
  · rintro y (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact Or.inl (Or.inl ⟨t, Ioc_subset_Icc_self ht, rfl⟩)
    · exact Or.inl (Or.inr ⟨t, Ioc_subset_Icc_self ht, rfl⟩)

/-- **The equal-gate face** `F_r = innerSide (A₁ ∪ A₂)` (`q₁ = q₂ = q`). -/
theorem trMap_mem_iff_innerSide_eq (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {r : ℝ} (hr : 0 ≤ r) {C : Set ℂ} (hC : IsOpen C) (hCb : IsBounded C) {α₁ α₂ : ℝ → ℂ}
    {c₁ u₁ e₁ c₂ u₂ e₂ : ℝ} (hcu₁ : c₁ < u₁) (hue₁ : u₁ ≤ e₁) (hue₂ : u₂ ≤ e₂)
    (hfrC : frontier C = α₁ '' Icc c₁ e₁ ∪ α₂ '' Icc c₂ e₂)
    (hα₁D : ∀ v ∈ Ico c₁ u₁, α₁ v ∈ H \ fwdHull W r)
    (hα₂D : ∀ v ∈ Ico c₂ u₂, α₂ v ∈ H \ fwdHull W r)
    (hα₁K : ∀ v ∈ Icc u₁ e₁, α₁ v ∉ H \ fwdHull W r)
    (hα₂K : ∀ v ∈ Icc u₂ e₂, α₂ v ∉ H \ fwdHull W r) {q : ℝ} {z : ℂ} {a₁ a₂ : ℝ → ℂ}
    (ha₁ : ContinuousOn a₁ (Icc 0 1)) (ha₂ : ContinuousOn a₂ (Icc 0 1))
    (ha₁i : InjOn a₁ (Icc 0 1)) (ha₂i : InjOn a₂ (Icc 0 1)) (ha₁0 : a₁ 0 = q)
    (ha₂0 : a₂ 0 = q) (ha₁1 : a₁ 1 = z) (ha₂1 : a₂ 1 = z) (ha₁H : ∀ t ∈ Ioc (0 : ℝ) 1, a₁ t ∈ H)
    (ha₂H : ∀ t ∈ Ioc (0 : ℝ) 1, a₂ t ∈ H) (h12 : a₁ '' Icc 0 1 ∩ a₂ '' Icc 0 1 ⊆ {(q : ℂ), z})
    (ha₁img : a₁ '' Ioc 0 1 = fwdMap W r '' (α₁ '' Ico c₁ u₁))
    (ha₂img : a₂ '' Ioc 0 1 = fwdMap W r '' (α₂ '' Ico c₂ u₂)) {w : ℂ} (hw : w ∈ H) :
    trMap W 0 r w ∈ C ↔ w ∈ innerSide (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1) := by
  have hΓJ := Sec7.isJordanCurve_image_union ha₁ ha₂ ha₁i ha₂i (by rw [ha₁0, ha₂0])
    (by rw [ha₁1, ha₂1]) (by rw [ha₁0, ha₁1]; exact h12)
  have hΓH : a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ⊆ Hbar :=
    union_subset (image_arm_subset_Hbar ha₁0 ha₁H) (image_arm_subset_Hbar ha₂0 ha₂H)
  refine trMap_mem_iff_of_arms hη hW hW0 hr hC hCb hcu₁ hue₁ hue₂ hfrC hα₁D hα₂D hα₁K hα₂K
    ha₁img ha₂img hΓJ hΓH (q₁ := q) (q₂ := q) ?_ ?_ ?_ hw
  · intro x
    constructor
    · rintro (h | h)
      · rw [ofReal_injective (arm_real ha₁0 ha₁H h (by simp))]; exact ⟨le_rfl, le_rfl⟩
      · rw [ofReal_injective (arm_real ha₂0 ha₂H h (by simp))]; exact ⟨le_rfl, le_rfl⟩
    · intro hx
      rw [le_antisymm hx.2 hx.1]
      exact Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, ha₁0⟩
  · rintro y (hy | hy) hyH
    · rcases eq_or_mem_open_arm ha₁0 hy with h | h
      · exact absurd (h ▸ hyH) (not_mem_H_ofReal q)
      · exact Or.inl h
    · rcases eq_or_mem_open_arm ha₂0 hy with h | h
      · exact absurd (h ▸ hyH) (not_mem_H_ofReal q)
      · exact Or.inr h
  · rintro y (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact Or.inl ⟨t, Ioc_subset_Icc_self ht, rfl⟩
    · exact Or.inr ⟨t, Ioc_subset_Icc_self ht, rfl⟩

/-- Equal mapped values in the chart at `r` give equal mapped values in every earlier chart and
equal physical values (Lemma 1.2 (2) and `f̄_r(δ_r(t)) = η(t)`). -/
theorem ownFuture_and_trace_eq (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {s r a b : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) (hra : r ≤ a) (hrb : r ≤ b)
    (heq : trMap W r a 0 = trMap W r b 0) : trMap W s a 0 = trMap W s b 0 ∧ η a = η b := by
  have hr : 0 ≤ r := hs.trans hsr
  refine ⟨?_, ?_⟩
  · rw [ownFuture_trans hη hW hW0 hs hsr hra, ownFuture_trans hη hW hW0 hs hsr hrb]
    exact congrArg (trMap W s r) heq
  · rw [← traceMapOut_trMap_zero hη hW hW0 hr hra, ← traceMapOut_trMap_zero hη hW hW0 hr hrb]
    exact congrArg (trMap W 0 r) heq

/-- **The gap equality for equal gates** (the case `q₁ = q₂` of Lemma 1.3 in a fixed chart): the
endpoint values of `δ_r` on a gap avoiding `C` and the open arms, approached by `C`-visits, are
both the common gate. -/
theorem ownFuture_gap_eq_of_face_eq (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {C : Set ℂ} (hC : IsOpen C) {q : ℝ} {a₁ a₂ : ℝ → ℂ}
    (hJc : IsClosed (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1)) (ha₁0 : a₁ 0 = q) (ha₂0 : a₂ 0 = q)
    {s r a b : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) (hra : r ≤ a) (hrb : r ≤ b)
    (h11 : ∀ t, r ≤ t → η t ∈ C → trMap W r t 0 ∈ H →
      trMap W r t 0 ∈ innerSide (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1))
    (hFC : trMap W 0 r '' innerSide (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1) ⊆ C)
    (hgapa : η a ∉ C) (hgapb : η b ∉ C)
    (htree : ∀ t ∈ ({a, b} : Set ℝ), trMap W r t 0 ∉ a₁ '' Ioc 0 1 ∪ a₂ '' Ioc 0 1)
    (ha : a ∈ closure {t | r < t ∧ η t ∈ C}) (hb : b ∈ closure {t | r < t ∧ η t ∈ C}) :
    trMap W s a 0 = trMap W s b 0 ∧ η a = η b := by
  have hr : 0 ≤ r := hs.trans hsr
  have hF : ∀ t, r ≤ t → η t ∉ C →
      trMap W r t 0 ∉ innerSide (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1) := by
    intro t hrt hηt hF
    have := hFC ⟨_, hF, rfl⟩
    rw [traceMapOut_trMap_zero hη hW hW0 hr hrt] at this
    exact hηt this
  have h := gate_lemma_eq (δ := fun t => trMap W r t 0) rfl hJc ha₁0 ha₂0 (hF a hra hgapa)
    (hF b hrb hgapb) (fun t ht h => htree t ht (Or.inl h)) (fun t ht h => htree t ht (Or.inr h))
    (ownFuture_mem_closure_face hη hW hW0 hC hr h11 ha)
    (ownFuture_mem_closure_face hη hW hW0 hC hr h11 hb)
  exact ownFuture_and_trace_eq hη hW hW0 hs hsr hra hrb (h.1.trans h.2.symm)

/-- **The third arm**: the lift `g_r ∘ β` of the earlier incoming prefix `β` from `x_C` to the
original target (a proper simple path in `D_r`) is a proper simple path in `ℍ`. -/
theorem thirdArm_props (hW : Continuous W) (hW0 : W 0 = 0) {r : ℝ} (hr : 0 ≤ r) {β : ℝ → ℂ}
    (hβ : ContinuousOn β (Ici 0)) (hβi : InjOn β (Ici 0))
    (hβD : ∀ τ ∈ Ici (0 : ℝ), β τ ∈ H \ fwdHull W r) (hβt : Tendsto (fun t => ‖β t‖) atTop atTop) :
    ContinuousOn (fun t => fwdMap W r (β t)) (Ici 0) ∧ InjOn (fun t => fwdMap W r (β t)) (Ici 0) ∧
      (∀ t ∈ Ici (0 : ℝ), fwdMap W r (β t) ∈ H) ∧
      Tendsto (fun t => ‖fwdMap W r (β t)‖) atTop atTop := by
  obtain ⟨K, hK⟩ := exists_norm_trMap_zero_sub_le hW hW0 hr
  refine ⟨(QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hr).continuousOn.comp hβ hβD,
    fun t ht t' ht' h => hβi ht ht' (QuantumZipper.FwdHolo.injOn_fwdMap hW hr (hβD t ht)
      (hβD t' ht') h), fun t ht => QuantumZipper.FwdHolo.mapsTo_fwdMap hW hr (hβD t ht), ?_⟩
  refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_right _ (-K) hβt)
  filter_upwards [eventually_ge_atTop 0] with t ht
  have hwH := QuantumZipper.FwdHolo.mapsTo_fwdMap hW hr (hβD t ht)
  have h1 := hK _ hwH
  rw [trMap_zero_fwdMap hW hW0 hr (hβD t ht)] at h1
  have h2 := norm_sub_norm_le (β t) (fwdMap W r (β t))
  linarith

/-- Two lifted pieces meet only over a common physical point. -/
theorem lift_inter_eq (hW : Continuous W) {r : ℝ} (hr : 0 ≤ r) {α β : ℝ → ℂ} {S T : Set ℝ}
    {x₀ : ℂ} (hαD : ∀ v ∈ S, α v ∈ H \ fwdHull W r) (hβD : ∀ v ∈ T, β v ∈ H \ fwdHull W r)
    (h : ∀ v ∈ S, ∀ v' ∈ T, α v = β v' → α v = x₀) {w : ℂ} (hwα : w ∈ fwdMap W r '' (α '' S))
    (hwβ : w ∈ fwdMap W r '' (β '' T)) : w = fwdMap W r x₀ := by
  obtain ⟨_, ⟨v, hv, rfl⟩, rfl⟩ := hwα
  obtain ⟨_, ⟨v', hv', rfl⟩, hvv⟩ := hwβ
  have := QuantumZipper.FwdHolo.injOn_fwdMap hW hr (hβD v' hv') (hαD v hv) hvv
  rw [h v hv v' hv' this.symm]

/-- The own-mapped future at an unvisited time avoids a lifted unvisited piece. -/
theorem ownFuture_notMem_lift (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) {α : ℝ → ℂ} {S : Set ℝ}
    (hαD : ∀ v ∈ S, α v ∈ H \ fwdHull W r) (hunv : ∀ v ∈ S, η t ≠ α v) :
    trMap W r t 0 ∉ fwdMap W r '' (α '' S) := by
  rintro ⟨_, ⟨v, hv, rfl⟩, hδ⟩
  have := traceMapOut_trMap_zero hη hW hW0 hr hrt
  rw [← hδ, trMap_zero_fwdMap hW hW0 hr (hαD v hv)] at this
  exact hunv v hv this.symm

/-- **Propositions 1.5 (old start) and 1.6 in a fixed chart, distinct gates `q₁ < q₂`**, with the
gate-lemma data and the face built from the physical pocket: the arms `a_i` are lifts of the
unvisited prefixes `α_i([c_i, u_i))` (junction `x_C = α₁(c₁)`), the third arm is the lift of the
earlier prefix `β` from `x_C` to the original target, and (1.1), `f̄_r(F_r) ⊆ C` are proved
(`trMap_mem_iff_innerSide`). -/
theorem ownFuture_gap_eq_of_arms_lt (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {C : Set ℂ} (hC : IsOpen C) (hCb : IsBounded C) {α₁ α₂ β : ℝ → ℂ}
    {c₁ u₁ e₁ c₂ u₂ e₂ : ℝ} (hcu₁ : c₁ < u₁) (hue₁ : u₁ ≤ e₁) (hue₂ : u₂ ≤ e₂)
    (hfrC : frontier C = α₁ '' Icc c₁ e₁ ∪ α₂ '' Icc c₂ e₂)
    (h12 : ∀ v ∈ Ico c₁ u₁, ∀ v' ∈ Ico c₂ u₂, α₁ v = α₂ v' → α₁ v = α₁ c₁)
    (h13 : ∀ v ∈ Ico c₁ u₁, ∀ τ ∈ Ici (0 : ℝ), α₁ v = β τ → α₁ v = α₁ c₁)
    (h23 : ∀ v ∈ Ico c₂ u₂, ∀ τ ∈ Ici (0 : ℝ), α₂ v = β τ → α₂ v = α₁ c₁)
    (hβ : ContinuousOn β (Ici 0)) (hβi : InjOn β (Ici 0)) (hβ0 : β 0 = α₁ c₁)
    (hβt : Tendsto (fun t => ‖β t‖) atTop atTop) {s r a b : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r)
    (hra : r < a) (hab : a < b) (hα₁D : ∀ v ∈ Ico c₁ u₁, α₁ v ∈ H \ fwdHull W r)
    (hα₂D : ∀ v ∈ Ico c₂ u₂, α₂ v ∈ H \ fwdHull W r)
    (hα₁K : ∀ v ∈ Icc u₁ e₁, α₁ v ∉ H \ fwdHull W r)
    (hα₂K : ∀ v ∈ Icc u₂ e₂, α₂ v ∉ H \ fwdHull W r)
    (hβD : ∀ τ ∈ Ici (0 : ℝ), β τ ∈ H \ fwdHull W r) {q₁ q₂ : ℝ} {a₁ a₂ : ℝ → ℂ} (hq : q₁ < q₂)
    (ha₁ : ContinuousOn a₁ (Icc 0 1)) (ha₂ : ContinuousOn a₂ (Icc 0 1))
    (ha₁i : InjOn a₁ (Icc 0 1)) (ha₂i : InjOn a₂ (Icc 0 1)) (ha₁0 : a₁ 0 = q₁)
    (ha₂0 : a₂ 0 = q₂) (ha₁1 : a₁ 1 = fwdMap W r (α₁ c₁)) (ha₂1 : a₂ 1 = fwdMap W r (α₁ c₁))
    (ha₁H : ∀ t ∈ Ioc (0 : ℝ) 1, a₁ t ∈ H) (ha₂H : ∀ t ∈ Ioc (0 : ℝ) 1, a₂ t ∈ H)
    (ha₁img : a₁ '' Ioc 0 1 = fwdMap W r '' (α₁ '' Ico c₁ u₁))
    (ha₂img : a₂ '' Ioc 0 1 = fwdMap W r '' (α₂ '' Ico c₂ u₂))
    (hgap : ∀ t ∈ Icc a b, η t ∉ C) (hunv₁ : ∀ t ∈ Icc a b, ∀ v ∈ Ico c₁ u₁, η t ≠ α₁ v)
    (hunv₂ : ∀ t ∈ Icc a b, ∀ v ∈ Ico c₂ u₂, η t ≠ α₂ v)
    (hunv₃ : ∀ t ∈ Icc a b, ∀ τ ∈ Ici (0 : ℝ), η t ≠ β τ)
    (ha : a ∈ closure {t | r < t ∧ η t ∈ C}) (hb : b ∈ closure {t | r < t ∧ η t ∈ C}) :
    trMap W s a 0 = trMap W s b 0 ∧ η a = η b := by
  have hr : 0 ≤ r := hs.trans hsr
  obtain ⟨ha₃, ha₃i, ha₃H, ha₃t⟩ := thirdArm_props hW hW0 hr hβ hβi hβD hβt
  set a₃ : ℝ → ℂ := fun t => fwdMap W r (β t) with ha₃def
  have ha₃img : a₃ '' Ici 0 = fwdMap W r '' (β '' Ici 0) := (image_image _ _ _).symm
  have ha₃0 : a₃ 0 = fwdMap W r (α₁ c₁) := by simp only [ha₃def, hβ0]
  have hopenH : ∀ {a : ℝ → ℂ}, (∀ t ∈ Ioc (0 : ℝ) 1, a t ∈ H) → ∀ w ∈ a '' Ioc 0 1, w ∈ H := by
    rintro a haH _ ⟨t, ht, rfl⟩; exact haH t ht
  have hq₁₂ : (q₁ : ℂ) ≠ q₂ := fun h => by have := ofReal_injective h; linarith
  have h12' : a₁ '' Icc 0 1 ∩ a₂ '' Icc 0 1 ⊆ {fwdMap W r (α₁ c₁)} := by
    rintro w ⟨hw₁, hw₂⟩
    rcases eq_or_mem_open_arm ha₁0 hw₁ with h | h
    · exact absurd (h.symm.trans (arm_real ha₂0 ha₂H hw₂ (by rw [h]; simp))) hq₁₂
    rcases eq_or_mem_open_arm ha₂0 hw₂ with h' | h'
    · exact absurd (h' ▸ hopenH ha₁H w h) (not_mem_H_ofReal q₂)
    rw [ha₁img] at h; rw [ha₂img] at h'
    exact lift_inter_eq hW hr hα₁D hα₂D h12 h h'
  have h13' : a₁ '' Icc 0 1 ∩ a₃ '' Ici 0 ⊆ {fwdMap W r (α₁ c₁)} := by
    rintro w ⟨hw₁, hw₃⟩
    have hw₃H : w ∈ H := by obtain ⟨t, ht, rfl⟩ := hw₃; exact ha₃H t ht
    rcases eq_or_mem_open_arm ha₁0 hw₁ with h | h
    · exact absurd (h ▸ hw₃H) (not_mem_H_ofReal q₁)
    rw [ha₁img] at h; rw [ha₃img] at hw₃
    exact lift_inter_eq hW hr hα₁D hβD h13 h hw₃
  have h23' : a₂ '' Icc 0 1 ∩ a₃ '' Ici 0 ⊆ {fwdMap W r (α₁ c₁)} := by
    rintro w ⟨hw₂, hw₃⟩
    have hw₃H : w ∈ H := by obtain ⟨t, ht, rfl⟩ := hw₃; exact ha₃H t ht
    rcases eq_or_mem_open_arm ha₂0 hw₂ with h | h
    · exact absurd (h ▸ hw₃H) (not_mem_H_ofReal q₂)
    rw [ha₂img] at h; rw [ha₃img] at hw₃
    exact lift_inter_eq hW hr hα₂D hβD h23 h hw₃
  obtain ⟨hΓJ, hΓH⟩ := isJordanCurve_faceBoundary hq ha₁ ha₂ ha₁i ha₂i ha₁0 ha₂0 ha₁1 ha₂1 ha₁H
    ha₂H h12'
  have hiff := fun w (hw : w ∈ H) => trMap_mem_iff_innerSide hη hW hW0 hr hC hCb hcu₁ hue₁ hue₂
    hfrC hα₁D hα₂D hα₁K hα₂K hq ha₁ ha₂ ha₁i ha₂i ha₁0 ha₂0 ha₁1 ha₂1 ha₁H ha₂H h12' ha₁img
    ha₂img hw
  refine ownFuture_gap_eq_of_face hη hW hW0 hC hq ha₁ ha₂ ha₁i ha₂i ha₁0 ha₂0 ha₁1 ha₂1 ha₁H ha₂H
    h12' ha₃ ha₃i ha₃0 ha₃H ha₃t h13' h23' hs hsr hra hab ?_ ?_ hgap ?_ ha hb
  · intro t hrt htC hδH
    exact (hiff _ hδH).1 (by rw [traceMapOut_trMap_zero hη hW hW0 hr hrt]; exact htC)
  · rintro _ ⟨w, hw, rfl⟩
    exact (hiff w (innerSide_subset_H hΓJ hΓH hw)).2 hw
  · rintro t ht ((h | h) | h)
    · rw [ha₁img] at h
      exact ownFuture_notMem_lift hη hW hW0 hr (hra.le.trans ht.1) hα₁D (hunv₁ t ht) h
    · rw [ha₂img] at h
      exact ownFuture_notMem_lift hη hW hW0 hr (hra.le.trans ht.1) hα₂D (hunv₂ t ht) h
    · rw [ha₃img] at h
      exact ownFuture_notMem_lift hη hW hW0 hr (hra.le.trans ht.1) hβD (hunv₃ t ht) h

/-- **Propositions 1.5 (old start) and 1.6 in a fixed chart, equal gates `q₁ = q₂ = q`**: the
face is the inner side of the Jordan loop `A₁ ∪ A₂` (no third arm is needed). -/
theorem ownFuture_gap_eq_of_arms_eq (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {C : Set ℂ} (hC : IsOpen C) (hCb : IsBounded C) {α₁ α₂ : ℝ → ℂ}
    {c₁ u₁ e₁ c₂ u₂ e₂ : ℝ} (hcu₁ : c₁ < u₁) (hue₁ : u₁ ≤ e₁) (hue₂ : u₂ ≤ e₂)
    (hfrC : frontier C = α₁ '' Icc c₁ e₁ ∪ α₂ '' Icc c₂ e₂)
    (h12 : ∀ v ∈ Ico c₁ u₁, ∀ v' ∈ Ico c₂ u₂, α₁ v = α₂ v' → α₁ v = α₁ c₁)
    {s r a b : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) (hra : r ≤ a) (hrb : r ≤ b)
    (hα₁D : ∀ v ∈ Ico c₁ u₁, α₁ v ∈ H \ fwdHull W r)
    (hα₂D : ∀ v ∈ Ico c₂ u₂, α₂ v ∈ H \ fwdHull W r)
    (hα₁K : ∀ v ∈ Icc u₁ e₁, α₁ v ∉ H \ fwdHull W r)
    (hα₂K : ∀ v ∈ Icc u₂ e₂, α₂ v ∉ H \ fwdHull W r) {q : ℝ} {a₁ a₂ : ℝ → ℂ}
    (ha₁ : ContinuousOn a₁ (Icc 0 1)) (ha₂ : ContinuousOn a₂ (Icc 0 1))
    (ha₁i : InjOn a₁ (Icc 0 1)) (ha₂i : InjOn a₂ (Icc 0 1)) (ha₁0 : a₁ 0 = q)
    (ha₂0 : a₂ 0 = q) (ha₁1 : a₁ 1 = fwdMap W r (α₁ c₁)) (ha₂1 : a₂ 1 = fwdMap W r (α₁ c₁))
    (ha₁H : ∀ t ∈ Ioc (0 : ℝ) 1, a₁ t ∈ H) (ha₂H : ∀ t ∈ Ioc (0 : ℝ) 1, a₂ t ∈ H)
    (ha₁img : a₁ '' Ioc 0 1 = fwdMap W r '' (α₁ '' Ico c₁ u₁))
    (ha₂img : a₂ '' Ioc 0 1 = fwdMap W r '' (α₂ '' Ico c₂ u₂))
    (hgapa : η a ∉ C) (hgapb : η b ∉ C)
    (hunv₁ : ∀ t ∈ ({a, b} : Set ℝ), ∀ v ∈ Ico c₁ u₁, η t ≠ α₁ v)
    (hunv₂ : ∀ t ∈ ({a, b} : Set ℝ), ∀ v ∈ Ico c₂ u₂, η t ≠ α₂ v)
    (ha : a ∈ closure {t | r < t ∧ η t ∈ C}) (hb : b ∈ closure {t | r < t ∧ η t ∈ C}) :
    trMap W s a 0 = trMap W s b 0 ∧ η a = η b := by
  have hr : 0 ≤ r := hs.trans hsr
  have h12' : a₁ '' Icc 0 1 ∩ a₂ '' Icc 0 1 ⊆ {(q : ℂ), fwdMap W r (α₁ c₁)} := by
    rintro w ⟨hw₁, hw₂⟩
    rcases eq_or_mem_open_arm ha₁0 hw₁ with h | h
    · exact Or.inl h
    rcases eq_or_mem_open_arm ha₂0 hw₂ with h' | h'
    · exact Or.inl h'
    rw [ha₁img] at h; rw [ha₂img] at h'
    exact Or.inr (lift_inter_eq hW hr hα₁D hα₂D h12 h h')
  have hΓJ := Sec7.isJordanCurve_image_union ha₁ ha₂ ha₁i ha₂i (by rw [ha₁0, ha₂0])
    (by rw [ha₁1, ha₂1]) (by rw [ha₁0, ha₁1]; exact h12')
  have hΓH : a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ⊆ Hbar :=
    union_subset (image_arm_subset_Hbar ha₁0 ha₁H) (image_arm_subset_Hbar ha₂0 ha₂H)
  have hiff := fun w (hw : w ∈ H) => trMap_mem_iff_innerSide_eq hη hW hW0 hr hC hCb hcu₁ hue₁
    hue₂ hfrC hα₁D hα₂D hα₁K hα₂K ha₁ ha₂ ha₁i ha₂i ha₁0 ha₂0 ha₁1 ha₂1 ha₁H ha₂H h12' ha₁img
    ha₂img hw
  refine ownFuture_gap_eq_of_face_eq hη hW hW0 hC (isCompact_of_isJordanCurve hΓJ).isClosed
    ha₁0 ha₂0 hs hsr hra hrb ?_ ?_ hgapa hgapb ?_ ha hb
  · intro t hrt htC hδH
    exact (hiff _ hδH).1 (by rw [traceMapOut_trMap_zero hη hW hW0 hr hrt]; exact htC)
  · rintro _ ⟨w, hw, rfl⟩
    exact (hiff w (innerSide_subset_H hΓJ hΓH hw)).2 hw
  · intro t ht h
    have hrt : r ≤ t := by rcases ht with rfl | rfl; exacts [hra, hrb]
    rcases h with h | h
    · rw [ha₁img] at h
      exact ownFuture_notMem_lift hη hW hW0 hr hrt hα₁D (hunv₁ t ht) h
    · rw [ha₂img] at h
      exact ownFuture_notMem_lift hη hW hW0 hr hrt hα₂D (hunv₂ t ht) h

/-- **Propositions 1.5 (old start) and 1.6 (`p ∈ R_s`) from the physical pocket** (finite
junction; ruling R41's note, the fixed-chart argument of pp. 4–6). The pocket `C` is open and
bounded with `∂C = α₁([c₁, e₁]) ∪ α₂([c₂, e₂])`, junction `x_C = α₁(c₁) = α₂(c₂)`. In the chart at
`r < a`: the prefixes `α_i([c_i, u_i))` are in `D_r` and meet only at `x_C`, the suffixes
`α_i([u_i, e_i])` are not in `D_r`, and the earlier prefix `β` (a proper simple path from `x_C` to
the original target) is in `D_r` and meets the prefixes only at `x_C`. If on the gap `[a, b]` the
trace avoids `C` and these unvisited pieces, and both endpoints are limits of `C`-visits after `r`,
then `δ_s(a) = δ_s(b)` for every `0 ≤ s ≤ r`, and `η(a) = η(b)`. No singleton-fibre assumption is
used; the two gates may have the same physical image. -/
theorem ownFuture_gap_eq_of_pocket (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {C : Set ℂ} (hC : IsOpen C) (hCb : IsBounded C) {α₁ α₂ β : ℝ → ℂ}
    {c₁ u₁ e₁ c₂ u₂ e₂ : ℝ} (hcu₁ : c₁ < u₁) (hcu₂ : c₂ < u₂) (hue₁ : u₁ ≤ e₁) (hue₂ : u₂ ≤ e₂)
    (hα₁ : ContinuousOn α₁ (Icc c₁ u₁)) (hα₂ : ContinuousOn α₂ (Icc c₂ u₂))
    (hα₁i : InjOn α₁ (Icc c₁ u₁)) (hα₂i : InjOn α₂ (Icc c₂ u₂)) (hx₀ : α₁ c₁ = α₂ c₂)
    (hfrC : frontier C = α₁ '' Icc c₁ e₁ ∪ α₂ '' Icc c₂ e₂)
    (h12 : ∀ v ∈ Ico c₁ u₁, ∀ v' ∈ Ico c₂ u₂, α₁ v = α₂ v' → α₁ v = α₁ c₁)
    (hβ : ContinuousOn β (Ici 0)) (hβi : InjOn β (Ici 0)) (hβ0 : β 0 = α₁ c₁)
    (hβt : Tendsto (fun t => ‖β t‖) atTop atTop)
    (h13 : ∀ v ∈ Ico c₁ u₁, ∀ τ ∈ Ici (0 : ℝ), α₁ v = β τ → α₁ v = α₁ c₁)
    (h23 : ∀ v ∈ Ico c₂ u₂, ∀ τ ∈ Ici (0 : ℝ), α₂ v = β τ → α₂ v = α₁ c₁)
    {s r a b : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) (hra : r < a) (hab : a < b)
    (hα₁D : ∀ v ∈ Ico c₁ u₁, α₁ v ∈ H \ fwdHull W r)
    (hα₂D : ∀ v ∈ Ico c₂ u₂, α₂ v ∈ H \ fwdHull W r)
    (hα₁K : ∀ v ∈ Icc u₁ e₁, α₁ v ∉ H \ fwdHull W r)
    (hα₂K : ∀ v ∈ Icc u₂ e₂, α₂ v ∉ H \ fwdHull W r)
    (hβD : ∀ τ ∈ Ici (0 : ℝ), β τ ∈ H \ fwdHull W r)
    (hgap : ∀ t ∈ Icc a b, η t ∉ C) (hunv₁ : ∀ t ∈ Icc a b, ∀ v ∈ Ico c₁ u₁, η t ≠ α₁ v)
    (hunv₂ : ∀ t ∈ Icc a b, ∀ v ∈ Ico c₂ u₂, η t ≠ α₂ v)
    (hunv₃ : ∀ t ∈ Icc a b, ∀ τ ∈ Ici (0 : ℝ), η t ≠ β τ)
    (ha : a ∈ closure {t | r < t ∧ η t ∈ C}) (hb : b ∈ closure {t | r < t ∧ η t ∈ C}) :
    trMap W s a 0 = trMap W s b 0 ∧ η a = η b := by
  have hr : 0 ≤ r := hs.trans hsr
  obtain ⟨q₁, a₁, ha₁, ha₁i, ha₁0, ha₁1, ha₁H, -, ha₁img⟩ :=
    exists_arm hη hW hW0 hr hcu₁ hα₁ hα₁i hα₁D (hα₁K u₁ ⟨le_rfl, hue₁⟩)
  obtain ⟨q₂, a₂, ha₂, ha₂i, ha₂0, ha₂1, ha₂H, -, ha₂img⟩ :=
    exists_arm hη hW hW0 hr hcu₂ hα₂ hα₂i hα₂D (hα₂K u₂ ⟨le_rfl, hue₂⟩)
  have ha₂1' : a₂ 1 = fwdMap W r (α₁ c₁) := by rw [ha₂1, hx₀]
  have hab' : ∀ t ∈ ({a, b} : Set ℝ), t ∈ Icc a b := by
    rintro t (rfl | rfl); exacts [⟨le_rfl, hab.le⟩, ⟨hab.le, le_rfl⟩]
  rcases lt_trichotomy q₁ q₂ with hq | hq | hq
  · exact ownFuture_gap_eq_of_arms_lt hη hW hW0 hC hCb hcu₁ hue₁ hue₂ hfrC h12 h13 h23 hβ hβi
      hβ0 hβt hs hsr hra hab hα₁D hα₂D hα₁K hα₂K hβD hq ha₁ ha₂ ha₁i ha₂i ha₁0 ha₂0 ha₁1 ha₂1'
      ha₁H ha₂H ha₁img ha₂img hgap hunv₁ hunv₂ hunv₃ ha hb
  · subst hq
    exact ownFuture_gap_eq_of_arms_eq hη hW hW0 hC hCb hcu₁ hue₁ hue₂ hfrC h12 hs hsr hra.le
      (hra.le.trans hab.le) hα₁D hα₂D hα₁K hα₂K ha₁ ha₂ ha₁i ha₂i ha₁0 ha₂0 ha₁1 ha₂1' ha₁H ha₂H
      ha₁img ha₂img (hgap a ⟨le_rfl, hab.le⟩) (hgap b ⟨hab.le, le_rfl⟩)
      (fun t ht => hunv₁ t (hab' t ht)) (fun t ht => hunv₂ t (hab' t ht)) ha hb
  · -- relabel the two arms
    have hx₀' : α₂ c₂ = α₁ c₁ := hx₀.symm
    refine ownFuture_gap_eq_of_arms_lt hη hW hW0 hC hCb hcu₂ hue₂ hue₁ (by rw [hfrC, union_comm])
      (fun v hv v' hv' h => by rw [hx₀']; exact h.trans (h12 v' hv' v hv h.symm))
      (fun v hv τ hτ h => by rw [hx₀']; exact h23 v hv τ hτ h)
      (fun v hv τ hτ h => by rw [hx₀']; exact h13 v hv τ hτ h) hβ hβi (hβ0.trans hx₀) hβt hs
      hsr hra hab hα₂D hα₁D hα₂K hα₁K hβD hq ha₂ ha₁ ha₂i ha₁i ha₂0 ha₁0 ha₂1 (by rw [ha₁1, hx₀])
      ha₂H ha₁H ha₂img ha₁img hgap hunv₂ hunv₁ hunv₃ ha hb

end InteractingSLE.Sec6
