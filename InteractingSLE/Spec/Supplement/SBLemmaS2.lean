/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLemmaS2Loop
import InteractingSLE.Spec.Supplement.SBLemmaSProofInside
import InteractingSLE.Foundations.Topology.JaniszewskiHalfPlane

/-!
# Lemma S2, the hull restriction

Packet PROVE-T14-SB4. **`s2HullStatement : S2HullStatement`**: Lemma S2's (S2.1) and the `D_A` membership of the
supplement (p. 577, `source/spec/p577-624.md` L19–L52), deterministic.

Setting: `A = p([0, 1])` (compact, from `0`), `γ` a proper curve from `0` with `A` on its closed right side,
`L = min (A ∩ ℝ) ≤ 0`, `R = max (A ∩ ℝ) ≥ 0`, `U_L`, `U_R` the two sides of `γ`. The left side misses `A`.

* **The visit to `L`.** For `L < 0`, the point `L` is a negative real point of `A`; off the curve it would be on the
  left side (S1: "every negative real point off `β̂` lies strictly on its left"). So `γ(t_L) = L`.
* **The left-component lemma** (`unbounded_or_gap`, the source's "left-collar incidence fact" without its record
  hypothesis): a component `C` of `U_L ∩ ℍ` is unbounded or has a negative real point off the curve in its closure.
  Otherwise its frontier would lie in a compact arc `γ([0, T])`, and `C` would be open and closed in the connected
  complement of that arc.
* **The closed walk** `Λ = γ([0, t_L])` + the lower semicircle `S⁻` over `[L, 0]` (`SBLemmaS2Loop`). Its winding
  number is `0` on `U_R` (which misses it), `1` in the lower half-disc, hence `1` just above every gap of
  `(L, 0) \ γ` — and `0` near every later point `γ(t)`, `t > t_L` (a ball off `Λ` meets `U_R`). So a later point can
  be no real point of `(L, 0)` ("a new real point inside the already filled real base could not be visited"), and
  the left component at a later point has no gap in `(L, 0)`: it is unbounded or reaches a gap below `L`, whose upper
  half-disc is in `D_A`. This is the second inclusion of (S2.1) and the `D_A` membership.
* **The first inclusion** (S2.2): for `z` on the left side with nonzero winding, the history loop `a_L + S⁻` (along `p`
  from `0` to a visit of `L`) winds about `z` as often as `Λ` — their difference `a_L − γ([0, t_L])` lies on the
  closed right side and misses the unbounded connected `U_L`. A loop in `A ∪ S⁻` winding about `z ∈ ℍ` traps `z`
  in `fill(A)`. Every interior point of the simple loop `Λ` is a limit of points about which it winds
  (`mem_closure_s2Wind_ne_zero`); those in `ℍ` are on the left side (not on `U_R`, not on a later point of `γ`).
  Hence `γ(s) ∈ fill(A)` for `γ(s) ∈ ℍ`, and a real `γ(s)` off `[L, 0]` is a limit of `fill(A)`, hence in `[L, R]`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped Real NNReal
open QuantumZipper (H)
open InteractingSLE.Supp9B (IsProperCurve leftSide rightSide closedRightSide lowerLeft lowerRight)
open InteractingSLE.HalfPlaneSep (IsFreeAt IsTrappedAt)
open InteractingSLE.Orientation (windNum)

namespace InteractingSLE

namespace Theorem14

namespace SB

/-! ### Sides of a proper curve from `0` -/

section Sides

variable {γ : ℝ≥0 → ℂ}

theorem isOpen_leftSide' (hγ : IsProperCurve γ) : IsOpen (leftSide γ) :=
  (Supp9B.isClosed_seedRayClosure hγ).isOpen_compl.connectedComponentIn

theorem isOpen_rightSide' (hγ : IsProperCurve γ) : IsOpen (rightSide γ) :=
  (Supp9B.isClosed_seedRayClosure hγ).isOpen_compl.connectedComponentIn

theorem notMem_range_of_mem_leftSide {z : ℂ} (hz : z ∈ leftSide γ) : z ∉ range γ := fun h =>
  connectedComponentIn_subset _ _ hz (Or.inl h)

theorem notMem_range_of_mem_rightSide {z : ℂ} (hz : z ∈ rightSide γ) : z ∉ range γ := fun h =>
  connectedComponentIn_subset _ _ hz (Or.inl h)

theorem not_isBounded_lowerLeft (x : ℝ) : ¬ IsBounded (lowerLeft x) := fun hb => by
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  set r : ℝ := |M| + |x| + 1 with hr
  have hmem : ((-r : ℝ) : ℂ) - I ∈ lowerLeft x :=
    ⟨by simp; linarith [neg_abs_le x, abs_nonneg M], by simp⟩
  have h := hM _ hmem
  have h2 : |(-r : ℝ)| ≤ ‖((-r : ℝ) : ℂ) - I‖ := by
    have := Complex.abs_re_le_norm (((-r : ℝ) : ℂ) - I)
    simpa using this
  rw [abs_neg, abs_of_pos (by positivity)] at h2
  linarith [le_abs_self M, abs_nonneg x]

theorem not_isBounded_lowerRight (x : ℝ) : ¬ IsBounded (lowerRight x) := fun hb => by
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  set r : ℝ := |M| + |x| + 1 with hr
  have hmem : ((r : ℝ) : ℂ) - I ∈ lowerRight x :=
    ⟨by simp; linarith [le_abs_self x, abs_nonneg M], by simp⟩
  have h := hM _ hmem
  have h2 : |r| ≤ ‖((r : ℝ) : ℂ) - I‖ := by
    have := Complex.abs_re_le_norm (((r : ℝ) : ℂ) - I)
    simpa using this
  rw [abs_of_pos (by positivity)] at h2
  linarith [le_abs_self M, abs_nonneg x]

theorem not_isBounded_leftSide (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) : ¬ IsBounded (leftSide γ) := fun hb =>
  not_isBounded_lowerLeft 0 (hb.subset (by
    have := Supp9B.lowerLeft_subset_leftSide hγ.2.2.1 (by rw [hγ0]; rfl)
    rwa [hγ0, zero_re] at this))

theorem not_isBounded_rightSide (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) : ¬ IsBounded (rightSide γ) := fun hb =>
  not_isBounded_lowerRight 0 (hb.subset (by
    have := Supp9B.lowerRight_subset_rightSide hγ.2.2.1 (by rw [hγ0]; rfl)
    rwa [hγ0, zero_re] at this))

theorem leftSide_inter_rightSide (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) {z : ℂ} (hl : z ∈ leftSide γ)
    (hr : z ∈ rightSide γ) : False :=
  Set.disjoint_left.1 (Supp9B.disjoint_leftSide_rightSide hγ (by rw [hγ0]; rfl)) hl hr

/-- A point off the closed curve is on one of the two sides. -/
theorem mem_leftSide_or_mem_rightSide (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) {z : ℂ}
    (hz : z ∉ seedRayClosure γ) : z ∈ leftSide γ ∨ z ∈ rightSide γ := by
  have := Supp9B.compl_seedRayClosure_eq hγ (by rw [hγ0]; rfl)
  have hz' : z ∈ (seedRayClosure γ)ᶜ := hz
  rw [this] at hz'
  exact hz'

/-- A point of `ℍ` off the curve is on one of the two sides. -/
theorem mem_leftSide_or_mem_rightSide_of_mem_H (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) {z : ℂ} (hz : z ∈ H)
    (hzγ : z ∉ range γ) : z ∈ leftSide γ ∨ z ∈ rightSide γ := by
  refine mem_leftSide_or_mem_rightSide hγ hγ0 fun h => ?_
  rcases h with h | h
  · exact hzγ h
  · have : z.im ≤ 0 := by have := h.2; rwa [hγ0, zero_im] at this
    exact absurd hz (not_lt.2 this)

/-- A positive real point off the curve is on the right side. -/
theorem ofReal_mem_rightSide (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) {x : ℝ} (hx : 0 < x)
    (hxγ : (x : ℂ) ∉ range γ) : (x : ℂ) ∈ rightSide γ := by
  have hxS : (x : ℂ) ∉ seedRayClosure γ := by
    rintro (h | h)
    · exact hxγ h
    · have := h.1
      rw [hγ0] at this
      simp at this
      linarith
  rcases mem_leftSide_or_mem_rightSide hγ hγ0 hxS with h | h
  · exfalso
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (isOpen_leftSide' hγ) _ h
    set δ' := min (δ / 2) (x / 2) with hδ'
    have hδ'0 : 0 < δ' := lt_min (by positivity) (by positivity)
    have hmem : (x : ℂ) - (δ' : ℂ) * I ∈ ball (x : ℂ) δ := by
      rw [mem_ball, dist_eq_norm, show (x : ℂ) - (δ' : ℂ) * I - x = ((-δ' : ℝ) : ℂ) * I by push_cast; ring,
        norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hδ'0]
      linarith [min_le_left (δ / 2) (x / 2)]
    have hR : (x : ℂ) - (δ' : ℂ) * I ∈ rightSide γ := by
      have hsub := Supp9B.lowerRight_subset_rightSide hγ.2.2.1 (by rw [hγ0]; rfl)
      rw [hγ0, zero_re] at hsub
      exact hsub ⟨by simp; linarith, by simp; linarith⟩
    exact leftSide_inter_rightSide hγ hγ0 (hball hmem) hR
  · exact h

/-- A negative real point off the curve is on the left side. -/
theorem ofReal_mem_leftSide' (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) {x : ℝ} (hx : x < 0)
    (hxγ : (x : ℂ) ∉ range γ) : (x : ℂ) ∈ leftSide γ := by
  refine Supp9B.ofReal_mem_leftSide hγ.2.2.1 (by rw [hγ0]; rfl) (by rw [hγ0]; simpa using hx) ?_
  rintro (h | h)
  · exact hxγ h
  · have := h.1
    rw [hγ0] at this
    simp at this
    linarith

/-- The left side misses the closed right side. -/
theorem notMem_closedRightSide_of_mem_leftSide (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) {z : ℂ}
    (hz : z ∈ leftSide γ) : z ∉ closedRightSide γ := by
  rintro (h | h)
  · exact leftSide_inter_rightSide hγ hγ0 hz h
  · exact connectedComponentIn_subset _ _ hz h

end Sides

/-! ### The left-component lemma -/

section Component

variable {γ : ℝ≥0 → ℂ}

theorem notMem_closure_of_isOpen {S U : Set ℂ} (hU : IsOpen U) (hSU : Disjoint S U) {z : ℂ} (hz : z ∈ U) :
    z ∉ closure S := fun h => Set.disjoint_left.1 (hSU.closure_left hU) h hz

/-- **The left-component lemma** (the source's "left-collar incidence fact", p. 578, without the record hypothesis):
a component of `U_L ∩ ℍ` is unbounded or has a negative real point off the curve in its closure. Otherwise its
frontier lies in a compact arc `γ([0, T])` and it is open and closed in the connected complement of that arc. -/
theorem unbounded_or_gap (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) {w : ℂ} (hw : w ∈ leftSide γ ∩ H) :
    ¬ IsBounded (connectedComponentIn (leftSide γ ∩ H) w) ∨
      ∃ x : ℝ, x < 0 ∧ (x : ℂ) ∉ range γ ∧ (x : ℂ) ∈ closure (connectedComponentIn (leftSide γ ∩ H) w) := by
  set C := connectedComponentIn (leftSide γ ∩ H) w with hC
  by_contra hcon
  have hCb : IsBounded C := by by_contra h; exact hcon (Or.inl h)
  have hgap : ∀ x : ℝ, x < 0 → (x : ℂ) ∉ range γ → (x : ℂ) ∉ closure C := fun x hx hxγ hxC =>
    hcon (Or.inr ⟨x, hx, hxγ, hxC⟩)
  have hopen : IsOpen (leftSide γ ∩ H) := (isOpen_leftSide' hγ).inter QuantumZipper.isOpen_H
  have hCo : IsOpen C := hopen.connectedComponentIn
  have hCsub : C ⊆ leftSide γ ∩ H := connectedComponentIn_subset _ _
  have hwC : w ∈ C := mem_connectedComponentIn hw
  obtain ⟨M, hM⟩ := hCb.closure.exists_norm_le
  -- a compact initial arc carrying every curve point of `closure C`
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 (tendsto_atTop.1 hγ.2.2.2 (M + 1))
  set T : ℝ≥0 := max T₀ 1 with hTdef
  have hT : ∀ t : ℝ≥0, T ≤ t → M < ‖γ t‖ := fun t ht => by
    have := hT₀ t ((le_max_left _ _).trans ht); linarith
  have hT0 : (0 : ℝ) < T := by
    have h1 : (1 : ℝ≥0) ≤ T := le_max_right _ _
    have h2 : (0 : ℝ≥0) < T := lt_of_lt_of_le one_pos h1
    exact_mod_cast h2
  set J := Supp9B.seedLine γ '' Icc 0 (T : ℝ) with hJdef
  have h0' : (γ 0).im = 0 := by rw [hγ0]; rfl
  obtain ⟨φ⟩ := Sec4.nonempty_homeomorph_unitInterval_image hT0
    (Supp9B.continuous_seedLine hγ.1).continuousOn (Supp9B.seedLine_injective hγ h0').injOn
  have hJc : IsConnected Jᶜ := Sec4.isConnected_compl_of_homeomorph_unitInterval φ
  have hJ : J ⊆ range γ := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨s.toNNReal, by simp [Supp9B.seedLine, hs.1]⟩
  have hJ' : ∀ t : ℝ≥0, t < T → γ t ∈ J := fun t ht =>
    ⟨t, ⟨t.2, le_of_lt ht⟩, Supp9B.seedLine_coe γ t⟩
  have hCJ : C ⊆ Jᶜ := fun z hz hzJ => notMem_range_of_mem_leftSide (hCsub hz).1 (hJ hzJ)
  have hCR : Disjoint C (rightSide γ) := Set.disjoint_left.2 fun z hz hzR =>
    leftSide_inter_rightSide hγ hγ0 (hCsub hz).1 hzR
  have hcl : ∀ z ∈ closure C, z ∉ J → z ∈ C := by
    intro z hz hzJ
    have hzM : ‖z‖ ≤ M := hM z hz
    have hzγ : z ∉ range γ := by
      rintro ⟨t, rfl⟩
      by_cases htT : t < T
      · exact hzJ (hJ' t htT)
      · exact absurd hzM (not_le.2 (hT t (not_lt.1 htT)))
    have him : 0 ≤ z.im :=
      closure_minimal (fun c hc => le_of_lt (hCsub hc).2) (isClosed_le continuous_const Complex.continuous_im) hz
    rcases lt_or_eq_of_le him with hpos | hzero
    · rcases mem_leftSide_or_mem_rightSide_of_mem_H hγ hγ0 hpos hzγ with hl | hr
      · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen z ⟨hl, hpos⟩
        obtain ⟨c, hc, hcz⟩ := Metric.mem_closure_iff.1 hz ε hε
        have hcball : c ∈ ball z ε := by rw [mem_ball, dist_comm]; exact hcz
        have hsub : ball z ε ⊆ C := by
          rw [hC, connectedComponentIn_eq hc]
          exact (convex_ball z ε).isPreconnected.subset_connectedComponentIn hcball hball
        exact hsub (mem_ball_self hε)
      · exact absurd hz (notMem_closure_of_isOpen (isOpen_rightSide' hγ) hCR hr)
    · have hz' : z = (z.re : ℂ) := Complex.ext rfl (by simp [← hzero])
      rcases lt_trichotomy z.re 0 with hneg | h0 | hposr
      · exact absurd (hz' ▸ hz) (hgap z.re hneg (hz' ▸ hzγ))
      · exact absurd ⟨0, by rw [hγ0, hz', h0]; simp⟩ hzγ
      · exact absurd hz (notMem_closure_of_isOpen (isOpen_rightSide' hγ) hCR
          (hz' ▸ ofReal_mem_rightSide hγ hγ0 hposr (hz' ▸ hzγ)))
  have hsub : Jᶜ ⊆ C := by
    have hcov : Jᶜ ⊆ C ∪ (closure C)ᶜ := fun z hz => by
      by_cases hzc : z ∈ closure C
      · exact Or.inl (hcl z hzc hz)
      · exact Or.inr hzc
    have hdis : Disjoint C (closure C)ᶜ := Set.disjoint_left.2 fun z hz hzc => hzc (subset_closure hz)
    exact hJc.isPreconnected.subset_left_of_subset_union hCo isClosed_closure.isOpen_compl hdis hcov
      ⟨w, hCJ hwC, hwC⟩
  have hJb : IsBounded J :=
    (isCompact_Icc.image_of_continuousOn (Supp9B.continuous_seedLine hγ.1).continuousOn).isBounded
  exact NormedSpace.unbounded_univ ℝ ℂ (by
    rw [← union_compl_self J]
    exact hJb.union (hCb.subset hsub))

end Component

/-! ### Free real points -/

section Free

variable {A : Set ℂ}

theorem not_isBounded_image_Iic (x : ℝ) : ¬ IsBounded (((↑) : ℝ → ℂ) '' Iic x) := fun hb => by
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  have h := hM _ (mem_image_of_mem _ (show min x 0 - |M| - 1 ∈ Iic x by
    show min x 0 - |M| - 1 ≤ x
    linarith [min_le_left x 0, abs_nonneg M]))
  rw [norm_real, Real.norm_eq_abs, abs_of_neg (by linarith [min_le_right x 0, abs_nonneg M])] at h
  linarith [min_le_right x 0, le_abs_self M]

theorem not_isBounded_image_Ici (x : ℝ) : ¬ IsBounded (((↑) : ℝ → ℂ) '' Ici x) := fun hb => by
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  have h := hM _ (mem_image_of_mem _ (show max x 0 + |M| + 1 ∈ Ici x by
    show x ≤ max x 0 + |M| + 1
    linarith [le_max_left x 0, abs_nonneg M]))
  rw [norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [le_max_right x 0, abs_nonneg M])] at h
  linarith [le_max_right x 0, le_abs_self M]

/-- Real points left of every real point of a compact set are free for it. -/
theorem isFreeAt_of_lt (hA : IsCompact A) {L : ℝ} (hL : ∀ y : ℝ, (y : ℂ) ∈ A → L ≤ y) {x : ℝ} (hx : x < L) :
    IsFreeAt A (x : ℂ) := by
  refine HalfPlaneSep.isFreeAt_of_not_isBounded hA.isClosed hA.isBounded
    (isPreconnected_Iic.image _ continuous_ofReal.continuousOn) (not_isBounded_image_Iic x) ?_ _
    ⟨x, mem_Iic.2 le_rfl, rfl⟩
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨by simp, fun h => by linarith [hL y h, mem_Iic.1 hy]⟩

/-- Real points right of every real point of a compact set are free for it. -/
theorem isFreeAt_of_gt (hA : IsCompact A) {R : ℝ} (hR : ∀ y : ℝ, (y : ℂ) ∈ A → y ≤ R) {x : ℝ} (hx : R < x) :
    IsFreeAt A (x : ℂ) := by
  refine HalfPlaneSep.isFreeAt_of_not_isBounded hA.isClosed hA.isBounded
    (isPreconnected_Ici.image _ continuous_ofReal.continuousOn) (not_isBounded_image_Ici x) ?_ _
    ⟨x, mem_Ici.2 le_rfl, rfl⟩
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨by simp, fun h => by linarith [hR y h, mem_Ici.1 hy]⟩

theorem mem_of_isFreeAt {z : ℂ} (hf : IsFreeAt A z) (hz : z ∈ H) : z ∈ H \ fillH A := by
  obtain ⟨ε, hε, h⟩ := hf
  exact h ⟨mem_ball_self hε, hz⟩

theorem isFreeAt_of_mem (hA : IsClosed A) {z : ℂ} (hz : z ∈ H \ fillH A) : IsFreeAt A z := by
  have hzA : z ∉ A := fun h => hz.2 ⟨hz.1, Or.inl (subset_closure h)⟩
  rcases HalfPlaneSep.isFreeAt_or_isTrappedAt hA hzA with h | h
  · exact h
  · exact absurd hz h.notMem

/-- The free label propagates along a preconnected set of `ℍ̄ \ A`. -/
theorem isFreeAt_of_isPreconnected (hA : IsClosed A) {X : Set ℂ} (hX : IsPreconnected X)
    (hXA : X ⊆ {w | 0 ≤ w.im} \ A) {z₀ z : ℂ} (hz₀ : z₀ ∈ X) (hf : IsFreeAt A z₀) (hz : z ∈ X) : IsFreeAt A z := by
  rcases HalfPlaneSep.isFreeAt_or_isTrappedAt_of_isPreconnected hA hX hXA with h | h
  · exact h z hz
  · exact absurd (h z₀ hz₀) (hf.not_isTrappedAt (hXA hz₀).1)

/-- The trapped label propagates along a preconnected set of `ℍ̄ \ A`. -/
theorem isTrappedAt_of_isPreconnected (hA : IsClosed A) {X : Set ℂ} (hX : IsPreconnected X)
    (hXA : X ⊆ {w | 0 ≤ w.im} \ A) {z₀ z : ℂ} (hz₀ : z₀ ∈ X) (ht : ¬ IsFreeAt A z₀) (hz : z ∈ X) :
    IsTrappedAt A z := by
  rcases HalfPlaneSep.isFreeAt_or_isTrappedAt_of_isPreconnected hA hX hXA with h | h
  · exact absurd (h z₀ hz₀) ht
  · exact h z hz

end Free

/-! ### The real base of the history -/

section Setting

variable {p : ℝ → ℂ} {γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

/-- `L = min (A ∩ ℝ)` and `R = max (A ∩ ℝ)` are attained, `L ≤ 0 ≤ R`. -/
theorem realBase_facts (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) :
    ((realMin (p '' Icc 0 1) : ℝ) : ℂ) ∈ p '' Icc 0 1 ∧ ((realMax (p '' Icc 0 1) : ℝ) : ℂ) ∈ p '' Icc 0 1 ∧
      (∀ y : ℝ, (y : ℂ) ∈ p '' Icc 0 1 → realMin (p '' Icc 0 1) ≤ y ∧ y ≤ realMax (p '' Icc 0 1)) ∧
      realMin (p '' Icc 0 1) ≤ 0 ∧ 0 ≤ realMax (p '' Icc 0 1) := by
  have hAc : IsCompact (p '' Icc 0 1) := isCompact_Icc.image_of_continuousOn hp
  set S := {x : ℝ | (x : ℂ) ∈ p '' Icc 0 1} with hS
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded (hAc.isClosed.preimage continuous_ofReal) ?_
    obtain ⟨M, hM⟩ := hAc.isBounded.exists_norm_le
    exact isBounded_iff_forall_norm_le.2 ⟨M, fun x hx => by simpa using hM _ hx⟩
  have h0 : (0 : ℝ) ∈ S := by
    show ((0 : ℝ) : ℂ) ∈ p '' Icc 0 1
    exact ⟨0, left_mem_Icc.2 zero_le_one, by rw [hp0]; simp⟩
  have hne : S.Nonempty := ⟨0, h0⟩
  have hmin : sInf S ∈ S := hSc.sInf_mem hne
  have hmax : sSup S ∈ S := hSc.sSup_mem hne
  have hle : ∀ y ∈ S, sInf S ≤ y ∧ y ≤ sSup S := fun y hy =>
    ⟨csInf_le hSc.bddBelow hy, le_csSup hSc.bddAbove hy⟩
  exact ⟨hmin, hmax, hle, (hle 0 h0).1, (hle 0 h0).2⟩

/-- **The visit to `L`** (S2: "The last observation in S1 forces `L ∈ β̂`"). -/
theorem exists_visit (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0)
    (hA : p '' Icc 0 1 ⊆ closedRightSide γ) :
    ∃ t : ℝ≥0, γ t = realMin (p '' Icc 0 1) ∧ (realMin (p '' Icc 0 1) = 0 → t = 0) := by
  obtain ⟨hLA, -, -, hL0, -⟩ := realBase_facts hp hp0
  rcases eq_or_lt_of_le hL0 with hL | hL
  · exact ⟨0, by rw [hγ0, hL]; simp, fun _ => rfl⟩
  · have hmem : ((realMin (p '' Icc 0 1) : ℝ) : ℂ) ∈ range γ := by
      by_contra h
      exact notMem_closedRightSide_of_mem_leftSide hγ hγ0 (ofReal_mem_leftSide' hγ hγ0 hL h) (hA hLA)
    obtain ⟨t, ht⟩ := hmem
    exact ⟨t, ht, fun h => absurd h hL.ne⟩

/-! ### Later points of the witness -/

theorem isClosed_s2Lower (L : ℝ) : IsClosed (s2Lower L) := by
  have : IsClosed (WangWu.semiArc 1) :=
    (isClosed_eq continuous_norm continuous_const).inter
      (isClosed_le continuous_const (continuous_const.mul Complex.continuous_im))
  exact this.preimage (continuous_s2Nrm L)

theorem rightSide_off (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) {L : ℝ} (hL : L < 0) (htL : γ tL = L) {z : ℂ}
    (hz : z ∈ rightSide γ) : z ∉ γ '' Icc 0 tL ∧ z ∉ s2Lower L := by
  refine ⟨fun ⟨s, _, hs⟩ => notMem_range_of_mem_rightSide hz ⟨s, hs⟩, fun hl => ?_⟩
  rcases lt_or_eq_of_le (im_nonpos_of_mem_s2Lower hL hl) with him | him
  · have hsub := Supp9B.lowerLeft_subset_leftSide hγ.2.2.1 (by rw [hγ0]; rfl)
    rw [hγ0, zero_re] at hsub
    exact leftSide_inter_rightSide hγ hγ0 (hsub ⟨re_neg_of_mem_s2Lower hL hl him, him⟩) hz
  · rcases eq_or_eq_of_mem_s2Lower hL hl him with h | h
    · exact notMem_range_of_mem_rightSide hz ⟨0, by rw [hγ0, h]⟩
    · exact notMem_range_of_mem_rightSide hz ⟨tL, by rw [htL, h]⟩

theorem leftSide_inter_H_off {L : ℝ} (hL : L < 0) {z : ℂ} (hz : z ∈ leftSide γ ∩ H) :
    z ∉ γ '' Icc 0 tL ∧ z ∉ s2Lower L :=
  ⟨fun ⟨s, _, hs⟩ => notMem_range_of_mem_leftSide hz.1 ⟨s, hs⟩,
    fun hl => absurd hz.2 (not_lt.2 (im_nonpos_of_mem_s2Lower hL hl))⟩

/-- The winding number vanishes on the right side. -/
theorem s2Wind_eq_zero_of_mem_rightSide (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) {L : ℝ} (hL : L < 0)
    (htL : γ tL = L) {z : ℂ} (hz : z ∈ rightSide γ) : s2Wind L γ tL z = 0 :=
  s2Wind_eq_zero_of_isPreconnected hγ hγ0 hL htL isPreconnected_connectedComponentIn
    (not_isBounded_rightSide hγ hγ0) (fun _ hw => rightSide_off hγ hγ0 hL htL hw) hz

/-- **Near a later point `γ(t)`, `t > t_L`, the loop `γ([0, t_L])` + `S⁻` is absent and winds `0` times.** -/
theorem later_ball (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) {L : ℝ} (hL : L < 0) (htL : γ tL = L) {t : ℝ≥0}
    (ht : tL < t) : ∃ ε > 0, ∀ z ∈ ball (γ t) ε, z ∉ γ '' Icc 0 tL ∧ z ∉ s2Lower L ∧ s2Wind L γ tL z = 0 := by
  have hΓc : IsClosed (γ '' Icc 0 tL ∪ s2Lower L) :=
    (isCompact_Icc.image hγ.1).isClosed.union (isClosed_s2Lower L)
  have hγt : γ t ∉ γ '' Icc 0 tL ∪ s2Lower L := by
    rintro (⟨s, hs, he⟩ | hl)
    · exact absurd (hγ.2.1 he) (ne_of_lt (lt_of_le_of_lt hs.2 ht))
    · have him : (γ t).im = 0 := le_antisymm (im_nonpos_of_mem_s2Lower hL hl) (hγ.2.2.1 t)
      rcases eq_or_eq_of_mem_s2Lower hL hl him with h | h
      · rw [← hγ0] at h
        exact absurd (hγ.2.1 h) (ne_of_gt (lt_of_le_of_lt zero_le ht))
      · rw [← htL] at h
        exact absurd (hγ.2.1 h) (ne_of_gt ht)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΓc.isOpen_compl _ hγt
  have hoff : ∀ z ∈ ball (γ t) ε, z ∉ γ '' Icc 0 tL ∧ z ∉ s2Lower L := fun z hz =>
    ⟨fun h => hball hz (Or.inl h), fun h => hball hz (Or.inr h)⟩
  obtain ⟨r, hr, hrb⟩ := Metric.mem_closure_iff.1
    (Supp9B.seedRayClosure_subset_closure_rightSide hγ (by rw [hγ0]; rfl) (Or.inl ⟨t, rfl⟩)) ε hε
  have hrball : r ∈ ball (γ t) ε := by rw [mem_ball, dist_comm]; exact hrb
  refine ⟨ε, hε, fun z hz => ⟨(hoff z hz).1, (hoff z hz).2, ?_⟩⟩
  rw [s2Wind_eq_of_isPreconnected hγ hγ0 hL htL (convex_ball _ _).isPreconnected hoff hz hrball]
  exact s2Wind_eq_zero_of_mem_rightSide hγ hγ0 hL htL hr

/-- **Winding `1` just above a gap of `(L, 0)`.** -/
theorem gap_ball (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) {L : ℝ} (hL : L < 0) (htL : γ tL = L) {x : ℝ}
    (hx : x ∈ Ioo L 0) (hxγ : (x : ℂ) ∉ γ '' Icc 0 tL) : ∃ ρ > 0, ∀ z ∈ ball (x : ℂ) ρ, s2Wind L γ tL z = 1 := by
  have hΓc : IsClosed (γ '' Icc 0 tL ∪ s2Lower L) :=
    (isCompact_Icc.image hγ.1).isClosed.union (isClosed_s2Lower L)
  have hxΓ : (x : ℂ) ∉ γ '' Icc 0 tL ∪ s2Lower L := by
    rintro (h | hl)
    · exact hxγ h
    · rcases eq_or_eq_of_mem_s2Lower hL hl (by simp) with h | h
      · exact absurd (ofReal_eq_zero.1 h) hx.2.ne
      · exact absurd (ofReal_injective h) hx.1.ne'
  have hO : IsOpen ((γ '' Icc 0 tL ∪ s2Lower L)ᶜ ∩ {z | ‖s2Nrm L z‖ < 1}) :=
    hΓc.isOpen_compl.inter (isOpen_lt (continuous_norm.comp (continuous_s2Nrm L)) continuous_const)
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hO _ ⟨hxΓ, norm_s2Nrm_ofReal_lt_one hL hx⟩
  have hoff : ∀ z ∈ ball (x : ℂ) ρ, z ∉ γ '' Icc 0 tL ∧ z ∉ s2Lower L := fun z hz =>
    ⟨fun h => (hball hz).1 (Or.inl h), fun h => (hball hz).1 (Or.inr h)⟩
  set z₀ : ℂ := (x : ℂ) - ((ρ / 2 : ℝ) : ℂ) * I with hz₀
  have hz₀b : z₀ ∈ ball (x : ℂ) ρ := by
    rw [mem_ball, dist_eq_norm, hz₀, show (x : ℂ) - ((ρ / 2 : ℝ) : ℂ) * I - x = ((-(ρ / 2) : ℝ) : ℂ) * I by
      push_cast; ring, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
    linarith
  have hz₀1 : s2Wind L γ tL z₀ = 1 :=
    s2Wind_eq_one hγ hγ0 hL htL (by rw [hz₀]; simp; positivity) (hball hz₀b).2
  refine ⟨ρ, hρ, fun z hz => ?_⟩
  rw [s2Wind_eq_of_isPreconnected hγ hγ0 hL htL (convex_ball _ _).isPreconnected hoff hz hz₀b, hz₀1]

/-- **No return into `(L, 0)`** ("a new real point inside the already filled real base could not be visited"): a
real point of the witness after `t_L` is left of `L` or positive. -/
theorem later_real (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) {L : ℝ} (htL : γ tL = L) {t : ℝ≥0}
    (ht : tL < t) (him : (γ t).im = 0) : (γ t).re < L ∨ 0 < (γ t).re := by
  have hγt : γ t = ((γ t).re : ℂ) := Complex.ext rfl (by simp [him])
  have h0 : (γ t).re ≠ 0 := fun h => by
    rw [h, ofReal_zero, ← hγ0] at hγt
    exact absurd (hγ.2.1 hγt) (ne_of_gt (lt_of_le_of_lt zero_le ht))
  have hL' : (γ t).re ≠ L := fun h => by
    rw [h, ← htL] at hγt
    exact absurd (hγ.2.1 hγt) (ne_of_gt ht)
  by_contra hcon
  have hx : (γ t).re ∈ Ioo L 0 := ⟨lt_of_le_of_ne (not_lt.1 fun h => hcon (Or.inl h)) hL'.symm,
    lt_of_le_of_ne (not_lt.1 fun h => hcon (Or.inr h)) h0⟩
  have hLn : L < 0 := hx.1.trans hx.2
  obtain ⟨ε, hε, hb⟩ := later_ball hγ hγ0 hLn htL ht
  obtain ⟨ρ, hρ, hg⟩ := gap_ball hγ hγ0 hLn htL hx (by
    rw [← hγt]
    rintro ⟨s, hs, he⟩
    exact absurd (hγ.2.1 he) (ne_of_lt (lt_of_le_of_lt hs.2 ht)))
  have h1 := hg (γ t) (by rw [← hγt]; exact mem_ball_self hρ)
  rw [(hb (γ t) (mem_ball_self hε)).2.2] at h1
  exact zero_ne_one h1

end Setting

/-! ### The two inclusions of (S2.1) -/

section Main

variable {p : ℝ → ℂ} {γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

theorem lowerRight_zero_subset (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) : lowerRight 0 ⊆ rightSide γ := by
  have := Supp9B.lowerRight_subset_rightSide hγ.2.2.1 (by rw [hγ0]; rfl)
  rwa [hγ0, zero_re] at this

theorem im_pos_of_dist_lt {z w : ℂ} (h : dist z w < z.im) : 0 < w.im := by
  have h1 : |z.im - w.im| ≤ dist z w := by
    rw [dist_eq_norm, ← sub_im]
    exact abs_im_le_norm _
  have := (abs_lt.1 (lt_of_le_of_lt h1 h)).2
  linarith

theorem re_pos_of_dist_lt {z w : ℂ} (h : dist z w < z.re) : 0 < w.re := by
  have h1 : |z.re - w.re| ≤ dist z w := by
    rw [dist_eq_norm, ← sub_re]
    exact abs_re_le_norm _
  have := (abs_lt.1 (lt_of_le_of_lt h1 h)).2
  linarith

/-- **The left collar of a later point is in `D_A`** (S2, "No second swallowed portion"): near `γ(t)`, `t > t_L`, every
left-side point of `ℍ` is in the unbounded domain of `A`. -/
theorem later_leftSide_free (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) (hγ : IsProperCurve γ)
    (hγ0 : γ 0 = 0) (hA : p '' Icc 0 1 ⊆ closedRightSide γ) (htL : γ tL = realMin (p '' Icc 0 1)) {t : ℝ≥0}
    (ht : tL < t) : ∃ ε > 0, ∀ w ∈ ball (γ t) ε, w ∈ leftSide γ → w ∈ H → w ∈ H \ fillH (p '' Icc 0 1) := by
  have hAc : IsCompact (p '' Icc 0 1) := isCompact_Icc.image_of_continuousOn hp
  obtain ⟨-, -, hLR, hL0, -⟩ := realBase_facts hp hp0
  obtain ⟨ε, hε, hεb⟩ : ∃ ε > 0, realMin (p '' Icc 0 1) < 0 → ∀ z ∈ ball (γ t) ε,
      s2Wind (realMin (p '' Icc 0 1)) γ tL z = 0 := by
    rcases eq_or_lt_of_le hL0 with hL | hL
    · exact ⟨1, one_pos, fun h => absurd hL h.ne⟩
    · obtain ⟨ε, hε, hb⟩ := later_ball hγ hγ0 hL htL ht
      exact ⟨ε, hε, fun _ z hz => (hb z hz).2.2⟩
  refine ⟨ε, hε, fun w hw hwL hwH => ?_⟩
  have hCA : connectedComponentIn (leftSide γ ∩ H) w ⊆ {z | 0 ≤ z.im} \ p '' Icc 0 1 := fun z hz => by
    have hz' := connectedComponentIn_subset _ _ hz
    exact ⟨show (0 : ℝ) ≤ z.im from le_of_lt (show (0 : ℝ) < z.im from hz'.2),
      fun h => notMem_closedRightSide_of_mem_leftSide hγ hγ0 hz'.1 (hA h)⟩
  have hwC : w ∈ connectedComponentIn (leftSide γ ∩ H) w := mem_connectedComponentIn ⟨hwL, hwH⟩
  refine mem_of_isFreeAt ?_ hwH
  rcases unbounded_or_gap hγ hγ0 ⟨hwL, hwH⟩ with hu | ⟨x, hx0, hxγ, hxC⟩
  · exact HalfPlaneSep.isFreeAt_of_not_isBounded hAc.isClosed hAc.isBounded isPreconnected_connectedComponentIn
      hu hCA w hwC
  · rcases lt_trichotomy x (realMin (p '' Icc 0 1)) with hxL | hxL | hxL
    · obtain ⟨δ, hδ, hfree⟩ := isFreeAt_of_lt hAc (fun y hy => (hLR y hy).1) hxL
      obtain ⟨c, hc, hcx⟩ := Metric.mem_closure_iff.1 hxC δ hδ
      have hcH : c ∈ H := (connectedComponentIn_subset _ _ hc).2
      have hcD : c ∈ H \ fillH (p '' Icc 0 1) := hfree ⟨by rw [mem_ball, dist_comm]; exact hcx, hcH⟩
      exact isFreeAt_of_isPreconnected hAc.isClosed isPreconnected_connectedComponentIn hCA hc
        (isFreeAt_of_mem hAc.isClosed hcD) hwC
    · exact absurd ⟨tL, by rw [htL, hxL]⟩ hxγ
    · exfalso
      have hLn : realMin (p '' Icc 0 1) < 0 := hxL.trans hx0
      obtain ⟨ρ, hρ, hg⟩ := gap_ball hγ hγ0 hLn htL ⟨hxL, hx0⟩ (fun ⟨s, _, he⟩ => hxγ ⟨s, he⟩)
      obtain ⟨c, hc, hcx⟩ := Metric.mem_closure_iff.1 hxC ρ hρ
      have h1 := hg c (by rw [mem_ball, dist_comm]; exact hcx)
      rw [s2Wind_eq_of_isPreconnected hγ hγ0 hLn htL isPreconnected_connectedComponentIn
        (fun z hz => leftSide_inter_H_off hLn (connectedComponentIn_subset _ _ hz)) hc hwC, hεb hLn w hw] at h1
      exact zero_ne_one h1

/-- **(S2.1), the second inclusion, and the `D_A` membership.** -/
theorem later_mem (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0)
    (hA : p '' Icc 0 1 ⊆ closedRightSide γ) (htL : γ tL = realMin (p '' Icc 0 1)) {t : ℝ≥0} (ht : tL < t) :
    γ t ∈ closure (H \ fillH (p '' Icc 0 1)) ∧
      (γ t ∈ H → γ t ∉ p '' Icc 0 1 → γ t ∈ H \ fillH (p '' Icc 0 1)) := by
  have hAc : IsCompact (p '' Icc 0 1) := isCompact_Icc.image_of_continuousOn hp
  obtain ⟨-, -, hLR, -, -⟩ := realBase_facts hp hp0
  obtain ⟨ε, hε, hfree⟩ := later_leftSide_free hp hp0 hγ hγ0 hA htL ht
  have hcl := Supp9B.seedRayClosure_subset_closure_leftSide hγ (by rw [hγ0]; rfl) (Or.inl ⟨t, rfl⟩)
  refine ⟨?_, fun hH hnA => ?_⟩
  · rcases lt_or_eq_of_le (hγ.2.2.1 t) with hH | him
    · refine Metric.mem_closure_iff.2 fun δ hδ => ?_
      obtain ⟨w, hwL, hwd⟩ := Metric.mem_closure_iff.1 hcl (min δ (min ε (γ t).im)) (lt_min hδ (lt_min hε hH))
      have hwH : w ∈ H := im_pos_of_dist_lt (lt_of_lt_of_le hwd ((min_le_right _ _).trans (min_le_right _ _)))
      refine ⟨w, hfree w ?_ hwL hwH, lt_of_lt_of_le hwd (min_le_left _ _)⟩
      rw [mem_ball, dist_comm]
      exact lt_of_lt_of_le hwd ((min_le_right _ _).trans (min_le_left _ _))
    · have hγt : γ t = ((γ t).re : ℂ) := Complex.ext rfl (by simp [← him])
      rcases later_real hγ hγ0 htL ht him.symm with hy | hy
      · obtain ⟨δ₀, hδ₀, hf⟩ := isFreeAt_of_lt hAc (fun y hy => (hLR y hy).1) hy
        rw [hγt]
        refine Metric.mem_closure_iff.2 fun δ hδ => ?_
        set r : ℝ := min δ δ₀ / 2 with hr
        have hr0 : 0 < r := by positivity
        have hd : dist ((γ t).re : ℂ) ((γ t).re + (r : ℂ) * I) = r := by
          rw [dist_eq_norm, show ((γ t).re : ℂ) - ((γ t).re + (r : ℂ) * I) = ((-r : ℝ) : ℂ) * I by push_cast; ring,
            norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hr0]
        refine ⟨(γ t).re + (r : ℂ) * I, hf ⟨?_, ?_⟩, ?_⟩
        · rw [mem_ball, dist_comm, hd]
          linarith [min_le_right δ δ₀]
        · show 0 < ((γ t).re + (r : ℂ) * I).im
          simp [hr0]
        · rw [hd]
          linarith [min_le_left δ δ₀]
      · refine Metric.mem_closure_iff.2 fun δ hδ => ?_
        have hy' : 0 < (γ t).re := hy
        obtain ⟨w, hwL, hwd⟩ := Metric.mem_closure_iff.1 hcl (min δ (min ε (γ t).re)) (lt_min hδ (lt_min hε hy'))
        have hre : 0 < w.re := re_pos_of_dist_lt (lt_of_lt_of_le hwd ((min_le_right _ _).trans (min_le_right _ _)))
        have hwH : w ∈ H := by
          by_contra hn
          rcases lt_or_eq_of_le (not_lt.1 (show ¬ (0 : ℝ) < w.im from hn)) with hneg | hzero
          · exact leftSide_inter_rightSide hγ hγ0 hwL (lowerRight_zero_subset hγ hγ0 ⟨hre, hneg⟩)
          · have hw' : w = (w.re : ℂ) := Complex.ext rfl (by simp [hzero])
            have hwγ : (w.re : ℂ) ∉ range γ := hw' ▸ notMem_range_of_mem_leftSide hwL
            exact leftSide_inter_rightSide hγ hγ0 hwL (hw' ▸ ofReal_mem_rightSide hγ hγ0 hre hwγ)
        refine ⟨w, hfree w ?_ hwL hwH, lt_of_lt_of_le hwd (min_le_left _ _)⟩
        rw [mem_ball, dist_comm]
        exact lt_of_lt_of_le hwd ((min_le_right _ _).trans (min_le_left _ _))
  · obtain ⟨ρ, hρ, hρb⟩ := Metric.isOpen_iff.1 (QuantumZipper.isOpen_H.inter hAc.isClosed.isOpen_compl) _
      (show γ t ∈ H ∩ (p '' Icc 0 1)ᶜ from ⟨hH, hnA⟩)
    obtain ⟨w, hwL, hwd⟩ := Metric.mem_closure_iff.1 hcl (min ρ ε) (lt_min hρ hε)
    have hwb : w ∈ ball (γ t) ρ := by
      rw [mem_ball, dist_comm]; exact lt_of_lt_of_le hwd (min_le_left _ _)
    have hwD := hfree w (by rw [mem_ball, dist_comm]; exact lt_of_lt_of_le hwd (min_le_right _ _)) hwL (hρb hwb).1
    have hball : ball (γ t) ρ ⊆ {z | 0 ≤ z.im} \ p '' Icc 0 1 := fun z hz =>
      ⟨show (0 : ℝ) ≤ z.im from le_of_lt (show (0 : ℝ) < z.im from (hρb hz).1), (hρb hz).2⟩
    exact mem_of_isFreeAt (isFreeAt_of_isPreconnected hAc.isClosed (convex_ball _ _).isPreconnected hball hwb
      (isFreeAt_of_mem hAc.isClosed hwD) (mem_ball_self hρ)) hH

/-- **Left points with nonzero winding are in `fill(A)`** (S2: "these left-collar points have nonzero winding around
a closed walk in `A ∪ ℝ`. They cannot be connected to infinity inside `ℍ \ A`"). A point `q ∈ ℍ` about which
`γ([0, t_L])` + `S⁻` winds is on the left side; by (S2.2) the history loop `a_L` + `S⁻` winds about it as well, so
its component in `ℍ \ A` is bounded. -/
theorem mem_fillH_of_s2Wind_ne_zero (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) (hγ : IsProperCurve γ)
    (hγ0 : γ 0 = 0) (hA : p '' Icc 0 1 ⊆ closedRightSide γ) (htL : γ tL = realMin (p '' Icc 0 1))
    (hL : realMin (p '' Icc 0 1) < 0) (htL0 : 0 < tL) {q : ℂ} (hqH : q ∈ H)
    (hq : s2Wind (realMin (p '' Icc 0 1)) γ tL q ≠ 0) : q ∈ fillH (p '' Icc 0 1) := by
  obtain ⟨hLA, -, -, -, -⟩ := realBase_facts hp hp0
  obtain ⟨σ, hσ, hpσ⟩ := hLA
  obtain ⟨hqΓ, hql⟩ := notMem_of_s2Wind_ne_zero hL htL htL0 hq
  have hqγ : q ∉ range γ := by
    rintro ⟨t, rfl⟩
    by_cases ht : t ≤ tL
    · exact hqΓ ⟨t, ⟨zero_le, ht⟩, rfl⟩
    · obtain ⟨ε, hε, hb⟩ := later_ball hγ hγ0 hL htL (not_le.1 ht)
      exact hq (hb _ (mem_ball_self hε)).2.2
  have hqL : q ∈ leftSide γ := by
    rcases mem_leftSide_or_mem_rightSide_of_mem_H hγ hγ0 hqH hqγ with h | h
    · exact h
    · exact absurd (s2Wind_eq_zero_of_mem_rightSide hγ hγ0 hL htL h) hq
  have hqA : q ∉ p '' Icc 0 1 := fun h => notMem_closedRightSide_of_mem_leftSide hγ hγ0 hqL (hA h)
  have hadd := windNum_s2ALoop_eq_add hγ hγ0 hL htL hp hp0 hσ hpσ hqA hqΓ hql
  have hD : windNum (s2DLoop (realMin (p '' Icc 0 1)) p σ γ tL) (s2Nrm (realMin (p '' Icc 0 1)) q) = 0 :=
    windNum_s2DLoop_eq_zero hγ hγ0 hL htL hp hp0 hσ hpσ isPreconnected_connectedComponentIn
      (not_isBounded_leftSide hγ hγ0)
      (fun z hz => ⟨fun h => notMem_closedRightSide_of_mem_leftSide hγ hγ0 hz (hA h),
        fun ⟨u, _, hu⟩ => notMem_range_of_mem_leftSide hz ⟨u, hu⟩⟩) hqL
  rw [hD, zero_add] at hadd
  by_contra hqf
  have hnb : ¬ (q ∈ closure (p '' Icc 0 1) ∨
      IsBounded (connectedComponentIn (H \ closure (p '' Icc 0 1)) q)) := fun h => hqf ⟨hqH, h⟩
  rw [not_or] at hnb
  have hQ : ∀ z ∈ connectedComponentIn (H \ closure (p '' Icc 0 1)) q,
      z ∉ p '' Icc 0 1 ∧ z ∉ s2Lower (realMin (p '' Icc 0 1)) := fun z hz => by
    have hz' := connectedComponentIn_subset _ _ hz
    exact ⟨fun h => hz'.2 (subset_closure h),
      fun h => absurd (show (0 : ℝ) < z.im from hz'.1) (not_lt.2 (im_nonpos_of_mem_s2Lower hL h))⟩
  have h0 := windNum_s2ALoop_eq_zero hL hp hp0 hσ hpσ isPreconnected_connectedComponentIn hnb.2 hQ
    (mem_connectedComponentIn ⟨hqH, hnb.1⟩)
  rw [h0] at hadd
  exact hq hadd.symm

/-- **(S2.1), the first inclusion** (`L < 0`): `γ([0, t_L]) ⊆ K_A`. -/
theorem pre_mem_hullK (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0)
    (hA : p '' Icc 0 1 ⊆ closedRightSide γ) (htL : γ tL = realMin (p '' Icc 0 1))
    (hL : realMin (p '' Icc 0 1) < 0) {s : ℝ≥0} (hs : s ≤ tL) : γ s ∈ hullK (p '' Icc 0 1) := by
  have hAc : IsCompact (p '' Icc 0 1) := isCompact_Icc.image_of_continuousOn hp
  obtain ⟨-, -, hLR, hL0, hR0⟩ := realBase_facts hp hp0
  have htL0 : 0 < tL := by
    refine lt_of_le_of_ne zero_le fun h => ?_
    rw [← h, hγ0] at htL
    exact hL.ne (ofReal_eq_zero.1 htL.symm)
  unfold hullK
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with hs0 | hs0
  · rw [← hs0, hγ0]
    exact mem_union_right _ ⟨0, ⟨hL0, hR0⟩, by simp⟩
  rcases eq_or_lt_of_le hs with hstL | hstL
  · rw [hstL, htL]
    exact mem_union_right _ ⟨_, ⟨le_rfl, hL0.trans hR0⟩, rfl⟩
  have hcl := mem_closure_s2Wind_ne_zero hγ hγ0 hL htL hs0 hstL
  have claim1 := fun q (hqH : q ∈ H) hq => mem_fillH_of_s2Wind_ne_zero hp hp0 hγ hγ0 hA htL hL htL0 hqH hq
  rcases lt_or_eq_of_le (hγ.2.2.1 s) with hH | him
  · refine mem_union_left _ ?_
    by_cases hsA : γ s ∈ p '' Icc 0 1
    · exact ⟨hH, Or.inl (subset_closure hsA)⟩
    obtain ⟨ρ, hρ, hρb⟩ := Metric.isOpen_iff.1 (QuantumZipper.isOpen_H.inter hAc.isClosed.isOpen_compl) _
      (show γ s ∈ H ∩ (p '' Icc 0 1)ᶜ from ⟨hH, hsA⟩)
    obtain ⟨q, hq, hqd⟩ := Metric.mem_closure_iff.1 hcl ρ hρ
    have hqb : q ∈ ball (γ s) ρ := by rw [mem_ball, dist_comm]; exact hqd
    have hqf := claim1 q (hρb hqb).1 hq
    have hqnf : ¬ IsFreeAt (p '' Icc 0 1) q := fun h => (mem_of_isFreeAt h (hρb hqb).1).2 hqf
    have hball : ball (γ s) ρ ⊆ {z | 0 ≤ z.im} \ p '' Icc 0 1 := fun z hz =>
      ⟨show (0 : ℝ) ≤ z.im from le_of_lt (show (0 : ℝ) < z.im from (hρb hz).1), (hρb hz).2⟩
    have htr := isTrappedAt_of_isPreconnected hAc.isClosed (convex_ball _ _).isPreconnected hball hqb hqnf
      (mem_ball_self hρ)
    by_contra hn
    exact htr.notMem ⟨hH, hn⟩
  · refine mem_union_right _ ?_
    have hγs : γ s = ((γ s).re : ℂ) := Complex.ext rfl (by simp [← him])
    refine ⟨(γ s).re, ?_, hγs.symm⟩
    by_cases hy : realMin (p '' Icc 0 1) ≤ (γ s).re ∧ (γ s).re ≤ 0
    · exact ⟨hy.1, hy.2.trans hR0⟩
    have hy' : (γ s).re < realMin (p '' Icc 0 1) ∨ 0 < (γ s).re := by
      rcases not_and_or.1 hy with h | h
      · exact Or.inl (not_le.1 h)
      · exact Or.inr (not_le.1 h)
    have hO : IsOpen {z | 1 < ‖s2Nrm (realMin (p '' Icc 0 1)) z‖} :=
      isOpen_lt continuous_const (continuous_norm.comp (continuous_s2Nrm _))
    obtain ⟨ρ₀, hρ₀, hρ₀b⟩ := Metric.isOpen_iff.1 hO _
      (show γ s ∈ {z | 1 < ‖s2Nrm (realMin (p '' Icc 0 1)) z‖} by
        show 1 < ‖s2Nrm (realMin (p '' Icc 0 1)) (γ s)‖
        rw [hγs]
        exact one_lt_norm_s2Nrm_ofReal hL hy')
    have hΓc : IsClosed (γ '' Icc 0 tL ∪ s2Lower (realMin (p '' Icc 0 1))) :=
      (isCompact_Icc.image hγ.1).isClosed.union (isClosed_s2Lower _)
    have hnearH : ∀ q ∈ ball (γ s) ρ₀, s2Wind (realMin (p '' Icc 0 1)) γ tL q ≠ 0 → q ∈ H := by
      intro q hqb hq
      rcases lt_trichotomy q.im 0 with hneg | hzero | hpos
      · exact absurd (s2Wind_eq_zero_of_outer hγ hγ0 hL htL hneg (hρ₀b hqb)) hq
      · exfalso
        obtain ⟨hqΓ, hql⟩ := notMem_of_s2Wind_ne_zero hL htL htL0 hq
        obtain ⟨r, hr, hrb⟩ := Metric.isOpen_iff.1 (hΓc.isOpen_compl.inter isOpen_ball) q
          (show q ∈ (γ '' Icc 0 tL ∪ s2Lower _)ᶜ ∩ ball (γ s) ρ₀ from ⟨fun h => h.elim hqΓ hql, hqb⟩)
        set q' : ℂ := q - ((r / 2 : ℝ) : ℂ) * I with hq'
        have hq'b : q' ∈ ball q r := by
          rw [mem_ball, dist_eq_norm, hq', show q - ((r / 2 : ℝ) : ℂ) * I - q = ((-(r / 2) : ℝ) : ℂ) * I by
            push_cast; ring, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_neg,
            abs_of_pos (by positivity)]
          linarith
        have hoff : ∀ z ∈ ball q r, z ∉ γ '' Icc 0 tL ∧ z ∉ s2Lower (realMin (p '' Icc 0 1)) := fun z hz =>
          ⟨fun h => (hrb hz).1 (Or.inl h), fun h => (hrb hz).1 (Or.inr h)⟩
        have h1 := s2Wind_eq_of_isPreconnected hγ hγ0 hL htL (convex_ball _ _).isPreconnected hoff
          (mem_ball_self hr) hq'b
        have hq'im : q'.im < 0 := by
          rw [hq']
          simp
          linarith
        rw [s2Wind_eq_zero_of_outer hγ hγ0 hL htL hq'im (hρ₀b (hrb hq'b).2)] at h1
        exact hq h1
      · exact hpos
    have key : ∀ x : ℝ, IsFreeAt (p '' Icc 0 1) (x : ℂ) → (x : ℂ) = γ s → False := fun x hx hxs => by
      obtain ⟨δ, hδ, hf⟩ := hx
      obtain ⟨q, hq, hqd⟩ := Metric.mem_closure_iff.1 hcl (min δ ρ₀) (lt_min hδ hρ₀)
      have hqb : q ∈ ball (γ s) ρ₀ := by
        rw [mem_ball, dist_comm]; exact lt_of_lt_of_le hqd (min_le_right _ _)
      have hqH := hnearH q hqb hq
      have hqD := hf ⟨by rw [mem_ball, dist_comm, hxs]; exact lt_of_lt_of_le hqd (min_le_left _ _), hqH⟩
      exact hqD.2 (claim1 q hqH hq)
    rcases hy' with hy' | hy'
    · exact (key _ (isFreeAt_of_lt hAc (fun z hz => (hLR z hz).1) hy') hγs.symm).elim
    · refine ⟨hL0.trans hy'.le, ?_⟩
      by_contra hyR
      exact key _ (isFreeAt_of_gt hAc (fun z hz => (hLR z hz).2) (not_le.1 hyR)) hγs.symm

/-- **Lemma S2, the hull restriction** (supplement p. 577, (S2.1) and the `D_A` membership). -/
theorem s2HullStatement : S2HullStatement := by
  intro p β' hp hp0 _ hγ hγ0 hA
  obtain ⟨-, -, -, hL0, hR0⟩ := realBase_facts hp hp0
  obtain ⟨tL, htL, htL0⟩ := exists_visit hp hp0 hγ hγ0 hA
  refine ⟨hL0, tL, htL, htL0, ?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    rcases eq_or_lt_of_le hL0 with hL | hL
    · have hs0 : s = 0 := le_antisymm (htL0 hL ▸ hs.2) zero_le
      rw [hs0, hγ0]
      unfold hullK
      exact mem_union_right _ ⟨0, ⟨hL0, hR0⟩, by simp⟩
    · exact pre_mem_hullK hp hp0 hγ hγ0 hA htL hL hs.2
  · rintro _ ⟨t, ht, rfl⟩
    exact (later_mem hp hp0 hγ hγ0 hA htL ht).1
  · intro t ht hH hnA
    exact (later_mem hp hp0 hγ hγ0 hA htL ht).2 hH hnA

/-- **Lemma S5's inside clause, repaired (R49), unconditionally**: from the repaired clause's reduction to S2
(`s5InsideNoVisitStatement_of_s2Hull`, PROVE-T14-SB3) and `s2HullStatement`. -/
theorem s5InsideNoVisitStatement : S5InsideNoVisitStatement :=
  s5InsideNoVisitStatement_of_s2Hull s2HullStatement

end Main

end SB

end Theorem14

end InteractingSLE
