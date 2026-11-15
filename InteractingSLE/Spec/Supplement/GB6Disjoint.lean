/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6Contact
import InteractingSLE.Spec.Supplement.GB6LawTrace
import InteractingSLE.Spec.Sec5.CrossRestartLawTopo
import InteractingSLE.Spec.Sec7.ContinuityProb2Join

/-!
# Proposition GB6: disjoint closed hulls before the first contact

Packet PROVE-GB6C, item (a) of `planning/handoffs/PROVE-GB6B.md` §5. Supplement §8.6, proof of Proposition GB6
(`source/spec/p481-528.md` L935–L975, p. 519): "Before `T`, every compact pair of retained histories is physically
separated. The counterflow lies in `Ū`: entering an open component cut off by the flow prefix would first require a
contact with its flow boundary. […] Their intersection is the connected set `Ĉ \ D` […] This is the disjoint-set core
of G13 and applies also when the counterflow prefix is nonsimple."

In the original flow chart `(ℍ, 0, ∞)` the flow prefix is `A = α([0, s])` (hull `K_s`, the filling of `A`) and the
counterflow prefix, read in its own chart `R(z) = −1/z`, is `B = γ([0, T])` (hull `K'_T`, the filling of `B`); the
physical counterflow prefix is `R(B)`. Both paths may touch `ℝ`, also at several points. If the physical paths are
disjoint (`A ∩ R(B \ {0}) = ∅`, i.e. `T` is before the first contact), the closures of the two hulls in the original
chart are disjoint:

  `closure K_s ∩ closure R(K'_T) = ∅`,

which is the hypothesis `hd` of GB6's fixed-hull restriction (`exists_loewner_relMap`).

## Proof

* (**No entry into flow pockets.**) Each point of `R(B \ {0})` lies on an unbounded preconnected subset of
  `R(B \ {0}) ⊆ ℍ̄ \ A` (the inversion of a piece of `γ` between two visits of `0`), hence is free for `A`
  (`HalfPlaneSep.isFreeAt_of_not_isBounded`), hence not in the closure of the filling of `A`. Symmetrically
  `R(A \ {0})` misses the closure of the filling of `B`.
* (**No common pocket.**) A common point `v` of the two closures is then off `A` and off `R(B)`, so it is trapped for
  both; a nearby `w ∈ ℍ` lies in a bounded component `O₁` of `ℍ \ A` and `R(w)` in a bounded component `O₂` of
  `ℍ \ B`. By the first step `O₁ = R(O₂)`. The highest point of `closure O₁` is then a frontier point in `ℍ` of both
  `O₁` and `R(O₂)`, so it lies on `A` and on `R(B)`, contradicting `A ∩ R(B \ {0}) = ∅`.

## Main results

* `notMem_closure_fillH_of_isFreeAt`, `disjoint_closure_fillH_of_unbounded`;
* `exists_unbounded_inv_image`, `rangeData_of_isGeneratingTrace`: the inversion of a path through `0` is a union of
  unbounded preconnected sets;
* **`disjoint_closure_fillH_inv_image`** (sets) and **`disjoint_closure_fwdHull_inv_image`** (hulls of generating
  traces);
* **`disjoint_closure_fwdHull_of_lt_firstContactTime`**: GB6's `hd` at every counterflow time before the first
  contact of `η = R̂ ∘ γ` with `α([0, s])`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology Bornology Complex
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE

namespace Supp8

namespace GB6

open HalfPlaneSep

/-! ### The inversion `R(z) = −1/z` on the closed upper half-plane -/

theorem neg_inv_neg_inv (z : ℂ) : -(-z⁻¹)⁻¹ = z := by
  rw [inv_neg, inv_inv, neg_neg]

theorem neg_inv_ne_zero {z : ℂ} (hz : z ≠ 0) : -z⁻¹ ≠ 0 :=
  neg_ne_zero.2 (inv_ne_zero hz)

theorem im_neg_inv (z : ℂ) : (-z⁻¹).im = z.im / normSq z := by
  rw [neg_im, inv_im, neg_div, neg_neg]

theorem im_neg_inv_nonneg {z : ℂ} (hz : 0 ≤ z.im) : 0 ≤ (-z⁻¹).im := by
  rw [im_neg_inv]
  exact div_nonneg hz (normSq_nonneg z)

theorem neg_inv_mem_H {z : ℂ} (hz : z ∈ H) : -z⁻¹ ∈ H := by
  have hz' : 0 < z.im := hz
  have hz0 : z ≠ 0 := fun h => by rw [h, zero_im] at hz'; exact lt_irrefl 0 hz'
  show 0 < (-z⁻¹).im
  rw [im_neg_inv]
  exact div_pos hz' (normSq_pos.2 hz0)

/-- Symmetry of the disjointness condition `A ∩ R(B \ {0}) = ∅`. -/
theorem disjoint_neg_inv_image_comm {A B : Set ℂ} (h : Disjoint A ((fun w : ℂ => -w⁻¹) '' (B \ {0}))) :
    Disjoint B ((fun w : ℂ => -w⁻¹) '' (A \ {0})) := by
  refine Set.disjoint_left.2 fun b hb ⟨a, ⟨ha, ha0⟩, hab⟩ => ?_
  have hb0 : b ≠ 0 := by
    rw [← hab]; exact neg_inv_ne_zero ha0
  refine Set.disjoint_left.1 h ha ⟨b, ⟨hb, hb0⟩, ?_⟩
  rw [← hab]
  exact neg_inv_neg_inv a

/-! ### No entry into the pockets of a filling -/

/-- A free point is not in the closure of the filling. -/
theorem notMem_closure_fillH_of_isFreeAt {F : Set ℂ} {z : ℂ} (hf : IsFreeAt F z) : z ∉ closure (fillH F) := by
  intro hz
  obtain ⟨ε, hε, h⟩ := hf
  obtain ⟨y, hy, hyz⟩ := Metric.mem_closure_iff.1 hz ε hε
  have hyH : y ∈ H := fillH_subset_H F hy
  exact (h ⟨by rw [mem_ball, dist_comm]; exact hyz, hyH⟩).2 hy

/-- **No entry into the pockets of a filling.** If every point of `C ⊆ ℍ̄ \ A` lies on an unbounded preconnected
subset of `C`, then `C` misses the closure of the filling of the compact set `A`. -/
theorem disjoint_closure_fillH_of_unbounded {A C : Set ℂ} (hA : IsCompact A)
    (hCA : C ⊆ {w | 0 ≤ w.im} \ A)
    (hC : ∀ c ∈ C, ∃ P ⊆ C, IsPreconnected P ∧ c ∈ P ∧ ¬ IsBounded P) :
    Disjoint (closure (fillH A)) C := by
  refine Set.disjoint_right.2 fun c hc => ?_
  obtain ⟨P, hPC, hP, hcP, hPu⟩ := hC c hc
  exact notMem_closure_fillH_of_isFreeAt
    (isFreeAt_of_not_isBounded hA.isClosed hA.isBounded hP hPu (hPC.trans hCA) c hcP)

/-! ### The inversion of a path through `0` -/

/-- **The inversion of a path through `0` is a union of unbounded preconnected sets.** If `γ` is continuous on
`[0, T]` with `γ(0) = 0` and `γ(t) ≠ 0`, the inversion of `γ` on `(t₀, t]`, `t₀` the last visit of `0` before `t`,
is a preconnected unbounded subset of `R(γ([0, T]) \ {0})` containing `R(γ(t))`. -/
theorem exists_unbounded_inv_image {γ : ℝ≥0 → ℂ} {T : ℝ≥0} (hγ : ContinuousOn γ (Icc 0 T)) (hγ0 : γ 0 = 0)
    {t : ℝ≥0} (ht : t ∈ Icc 0 T) (hγt : γ t ≠ 0) :
    ∃ P ⊆ (fun w : ℂ => -w⁻¹) '' (γ '' Icc 0 T \ {0}), IsPreconnected P ∧ -(γ t)⁻¹ ∈ P ∧
      ¬ IsBounded P := by
  set Z : Set ℝ≥0 := Icc 0 t ∩ γ ⁻¹' {0} with hZ
  have hγt' : ContinuousOn γ (Icc 0 t) := hγ.mono (Icc_subset_Icc_right ht.2)
  have hZc : IsClosed Z := hγt'.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hZk : IsCompact Z := isCompact_Icc.of_isClosed_subset hZc inter_subset_left
  have hZne : Z.Nonempty := ⟨0, ⟨le_rfl, zero_le⟩, hγ0⟩
  set t₀ := sSup Z with ht₀
  have ht₀Z : t₀ ∈ Z := hZk.sSup_mem hZne
  have hZbdd : BddAbove Z := hZk.isBounded.bddAbove
  have ht₀t : t₀ < t := by
    refine lt_of_le_of_ne ht₀Z.1.2 fun h => hγt ?_
    rw [← h]; exact ht₀Z.2
  have hne : ∀ u ∈ Ioc t₀ t, γ u ≠ 0 := by
    intro u hu h0
    exact absurd (le_csSup hZbdd ⟨⟨zero_le, hu.2⟩, h0⟩) (not_le.2 hu.1)
  have hsub : Ioc t₀ t ⊆ Icc 0 T := fun u hu => ⟨zero_le, hu.2.trans ht.2⟩
  refine ⟨(fun u => -(γ u)⁻¹) '' Ioc t₀ t, ?_, ?_, ⟨t, ⟨ht₀t, le_rfl⟩, rfl⟩, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨γ u, ⟨⟨u, hsub hu, rfl⟩, hne u hu⟩, rfl⟩
  · refine isPreconnected_Ioc.image _ ?_
    intro u hu
    exact ((hγ.mono hsub u hu).inv₀ (hne u hu)).neg
  · intro hb
    obtain ⟨M, hM⟩ := hb.subset_closedBall 0
    have hM0 : 0 ≤ M := by
      have := mem_closedBall_zero_iff.1 (hM ⟨t, ⟨ht₀t, le_rfl⟩, rfl⟩)
      exact (norm_nonneg _).trans this
    -- `γ(u) → 0` as `u ↓ t₀`
    have hcont : Tendsto γ (𝓝[Ioc t₀ t] t₀) (𝓝 0) := by
      have h1 : ContinuousWithinAt γ (Icc 0 T) t₀ := hγ t₀ ⟨zero_le, ht₀Z.1.2.trans ht.2⟩
      have h2 := h1.mono hsub
      rw [ContinuousWithinAt, ht₀Z.2] at h2
      exact h2
    have hev : ∀ᶠ u in 𝓝[Ioc t₀ t] t₀, ‖γ u‖ < 1 / (M + 1) :=
      (tendsto_norm_zero.comp hcont).eventually (gt_mem_nhds (by positivity))
    have : (𝓝[Ioc t₀ t] t₀).NeBot := left_nhdsWithin_Ioc_neBot ht₀t
    obtain ⟨u, hu, hut⟩ := (hev.and self_mem_nhdsWithin).exists
    have hγu := hne u hut
    have hpos : 0 < ‖γ u‖ := norm_pos_iff.2 hγu
    have h1 := mem_closedBall_zero_iff.1 (hM ⟨u, hut, rfl⟩)
    rw [norm_neg, norm_inv] at h1
    -- `‖γ u‖⁻¹ ≤ M` and `‖γ u‖ < 1/(M+1)` are incompatible
    have h2 : 1 ≤ M * ‖γ u‖ := by
      have := mul_le_mul_of_nonneg_right h1 hpos.le
      rwa [inv_mul_cancel₀ hpos.ne'] at this
    have h3 : M * ‖γ u‖ < M * (1 / (M + 1)) + 1 / (M + 1) := by
      nlinarith [mul_le_mul_of_nonneg_left hu.le hM0]
    have h4 : M * (1 / (M + 1)) + 1 / (M + 1) = 1 := by
      field_simp
    linarith

/-! ### Components of `ℍ \ A` -/

/-- Inside `ℍ`, the frontier of a component of `ℍ \ A` lies on `A`. -/
theorem mem_connectedComponentIn_of_mem_closure {A : Set ℂ} (hA : IsClosed A) {w z : ℂ}
    (hz : z ∈ closure (connectedComponentIn (H \ A) w)) (hzH : z ∈ H) (hzA : z ∉ A) :
    z ∈ connectedComponentIn (H \ A) w := by
  have hU : IsOpen (H \ A) := QuantumZipper.isOpen_H.sdiff hA
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU z ⟨hzH, hzA⟩
  obtain ⟨y, hy, hyz⟩ := Metric.mem_closure_iff.1 hz ε hε
  have hyb : y ∈ ball z ε := by rw [mem_ball, dist_comm]; exact hyz
  have h1 : ball z ε ⊆ connectedComponentIn (H \ A) y :=
    (convex_ball z ε).isPreconnected.subset_connectedComponentIn hyb hball
  rw [← connectedComponentIn_eq hy] at h1
  exact h1 (mem_ball_self hε)

/-- A bounded component of `ℍ \ A` lies in the filling of the closed set `A`. -/
theorem connectedComponentIn_subset_fillH {A : Set ℂ} (hA : IsClosed A) {w : ℂ}
    (hb : IsBounded (connectedComponentIn (H \ A) w)) : connectedComponentIn (H \ A) w ⊆ fillH A := by
  intro z hz
  refine ⟨(connectedComponentIn_subset _ _ hz).1, Or.inr ?_⟩
  rw [hA.closure_eq, ← connectedComponentIn_eq hz]
  exact hb

/-- A point of the filling off the closed set `A` has a bounded component in `ℍ \ A`. -/
theorem isBounded_connectedComponentIn_of_mem_fillH {A : Set ℂ} (hA : IsClosed A) {w : ℂ}
    (hw : w ∈ fillH A) (hwA : w ∉ A) : IsBounded (connectedComponentIn (H \ A) w) := by
  rcases hw.2 with h | h
  · rw [hA.closure_eq] at h; exact absurd h hwA
  · rwa [hA.closure_eq] at h

/-- A trapped point of `ℍ̄` is in the closure of the filling. -/
theorem IsTrappedAt.exists_mem_fillH {F : Set ℂ} {v : ℂ} (h : IsTrappedAt F v) :
    ∃ ε > 0, ∀ w ∈ ball v ε, w ∈ H → w ∈ fillH F := by
  obtain ⟨ε, hε, hd⟩ := h
  refine ⟨ε, hε, fun w hw hwH => ?_⟩
  by_contra hwf
  exact Set.disjoint_left.1 hd hw ⟨hwH, hwf⟩

/-- A point of the closure of the filling off `F` is trapped. -/
theorem isTrappedAt_of_mem_closure_fillH {F : Set ℂ} (hF : IsClosed F) {v : ℂ} (hv : v ∈ closure (fillH F))
    (hvF : v ∉ F) : IsTrappedAt F v :=
  (isFreeAt_or_isTrappedAt hF hvF).resolve_left fun hf => notMem_closure_fillH_of_isFreeAt hf hv

/-! ### Disjoint closed hulls -/

/-- **Disjoint closed hulls** (GB6, p. 519, "the disjoint-set core of G13"). Let `A, B ⊆ ℍ̄` be compact, and let
the inversions `R(A \ {0})`, `R(B \ {0})` (`R(z) = −1/z`) be unions of unbounded preconnected subsets (paths from
`0`). If `A` misses `R(B \ {0})`, then the closure of the filling of `A` misses the closure of the inversion of the
filling of `B`. -/
theorem disjoint_closure_fillH_inv_image {A B : Set ℂ} (hA : IsCompact A) (hB : IsCompact B)
    (hAH : A ⊆ {w | 0 ≤ w.im}) (hBH : B ⊆ {w | 0 ≤ w.im})
    (hAu : ∀ c ∈ (fun w : ℂ => -w⁻¹) '' (A \ {0}), ∃ P ⊆ (fun w : ℂ => -w⁻¹) '' (A \ {0}),
      IsPreconnected P ∧ c ∈ P ∧ ¬ IsBounded P)
    (hBu : ∀ c ∈ (fun w : ℂ => -w⁻¹) '' (B \ {0}), ∃ P ⊆ (fun w : ℂ => -w⁻¹) '' (B \ {0}),
      IsPreconnected P ∧ c ∈ P ∧ ¬ IsBounded P)
    (hAB : Disjoint A ((fun w : ℂ => -w⁻¹) '' (B \ {0}))) :
    Disjoint (closure (fillH A)) (closure ((fun w : ℂ => -w⁻¹) '' fillH B)) := by
  set R : ℂ → ℂ := fun w => -w⁻¹ with hR
  have hRR : ∀ z : ℂ, R (R z) = z := neg_inv_neg_inv
  have hBA : Disjoint B (R '' (A \ {0})) := disjoint_neg_inv_image_comm hAB
  have hCH : ∀ {S : Set ℂ}, S ⊆ {w | 0 ≤ w.im} → R '' (S \ {0}) ⊆ {w | 0 ≤ w.im} := by
    rintro S hS _ ⟨a, ⟨ha, -⟩, rfl⟩
    exact im_neg_inv_nonneg (hS ha)
  have hRc : ∀ {z : ℂ}, z ≠ 0 → ContinuousAt R z := fun hz => (continuousAt_inv₀ hz).neg
  -- step 1: no entry into the pockets
  have h1 : Disjoint (closure (fillH A)) (R '' (B \ {0})) :=
    disjoint_closure_fillH_of_unbounded hA
      (fun c hc => ⟨hCH hBH hc, fun hcA => Set.disjoint_left.1 hAB hcA hc⟩) hBu
  have h2 : Disjoint (closure (fillH B)) (R '' (A \ {0})) :=
    disjoint_closure_fillH_of_unbounded hB
      (fun c hc => ⟨hCH hAH hc, fun hcB => Set.disjoint_left.1 hBA hcB hc⟩) hAu
  have hRB : ∀ {z : ℂ}, z ∈ fillH A → R z ∉ B := fun {z} hz hzB => by
    have hz0 : z ≠ 0 := fun h => by
      have : (0 : ℝ) < z.im := fillH_subset_H A hz
      rw [h, zero_im] at this; exact lt_irrefl 0 this
    refine Set.disjoint_left.1 h1 (subset_closure hz) ⟨R z, ⟨hzB, neg_inv_ne_zero hz0⟩, hRR z⟩
  have hRA : ∀ {z : ℂ}, z ∈ fillH B → R z ∉ A := fun {z} hz hzA => by
    have hz0 : z ≠ 0 := fun h => by
      have : (0 : ℝ) < z.im := fillH_subset_H B hz
      rw [h, zero_im] at this; exact lt_irrefl 0 this
    refine Set.disjoint_left.1 h2 (subset_closure hz) ⟨R z, ⟨hzA, neg_inv_ne_zero hz0⟩, hRR z⟩
  -- step 2: a common point of the closures
  refine Set.disjoint_left.2 fun v hvA hvB => ?_
  obtain ⟨MB, hMB, hBMB⟩ := exists_closure_subset_ball hB.isBounded
  have hfB : fillH B ⊆ ball 0 MB := fillH_subset_ball hMB hBMB
  have hv0 : v ≠ 0 := by
    have hsub : R '' fillH B ⊆ {z | MB⁻¹ ≤ ‖z‖} := by
      rintro _ ⟨z, hz, rfl⟩
      have hz0 : z ≠ 0 := fun h => by
        have : (0 : ℝ) < z.im := fillH_subset_H B hz
        rw [h, zero_im] at this; exact lt_irrefl 0 this
      have hzM : ‖z‖ < MB := mem_ball_zero_iff.1 (hfB hz)
      show MB⁻¹ ≤ ‖-z⁻¹‖
      rw [norm_neg, norm_inv]
      exact (inv_le_inv₀ hMB (norm_pos_iff.2 hz0)).2 hzM.le
    have hcl := closure_minimal hsub (isClosed_le continuous_const continuous_norm) hvB
    intro h
    rw [h] at hcl
    have hcl' : MB⁻¹ ≤ ‖(0 : ℂ)‖ := hcl
    rw [norm_zero] at hcl'
    exact absurd hcl' (not_le.2 (inv_pos.2 hMB))
  have hRv : R v ∈ closure (fillH B) := by
    have := mem_closure_image (hRc hv0) hvB
    rwa [image_image, show (fun z => R (R z)) = id from funext hRR, image_id] at this
  have hvA' : v ∉ A := fun h =>
    Set.disjoint_left.1 h2 hRv ⟨v, ⟨h, hv0⟩, rfl⟩
  have hRvB : R v ∉ B := fun h =>
    Set.disjoint_left.1 h1 hvA ⟨R v, ⟨h, neg_inv_ne_zero hv0⟩, hRR v⟩
  obtain ⟨ε₁, hε₁, hb₁⟩ := IsTrappedAt.exists_mem_fillH (isTrappedAt_of_mem_closure_fillH hA.isClosed hvA hvA')
  obtain ⟨ε₂, hε₂, hb₂⟩ := IsTrappedAt.exists_mem_fillH (isTrappedAt_of_mem_closure_fillH hB.isClosed hRv hRvB)
  obtain ⟨ε₃, hε₃, hb₃⟩ := Metric.isOpen_iff.1 hA.isClosed.isOpen_compl v hvA'
  obtain ⟨ε₄, hε₄, hb₄⟩ := Metric.isOpen_iff.1 hB.isClosed.isOpen_compl (R v) hRvB
  obtain ⟨δ, hδ, hRδ⟩ := Metric.continuousAt_iff.1 (hRc hv0) (min ε₂ ε₄) (lt_min hε₂ hε₄)
  set δ' : ℝ := min δ (min ε₁ ε₃) / 2 with hδ'
  have hδ'0 : 0 < δ' := by positivity
  have hvim : 0 ≤ v.im := by
    have : closure (fillH A) ⊆ {z : ℂ | 0 ≤ z.im} :=
      closure_minimal (fun z hz => show (0 : ℝ) ≤ z.im from le_of_lt (fillH_subset_H A hz))
        (isClosed_le continuous_const continuous_im)
    exact this hvA
  set w : ℂ := v + (δ' : ℂ) * I with hw
  have hwv : dist w v = δ' := by
    rw [dist_eq_norm, hw, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hδ'0]
  have hwH : w ∈ H := by
    show 0 < w.im
    simp only [hw, add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    linarith
  have hlt : ∀ {x : ℝ}, 0 < x → min δ (min ε₁ ε₃) ≤ x → δ' < x := fun hx h => by
    rw [hδ']; linarith [lt_min hδ (lt_min hε₁ hε₃)]
  have hwδ : dist w v < δ := by
    rw [hwv]; exact hlt hδ (min_le_left _ _)
  have hwε₁ : w ∈ ball v ε₁ := by
    rw [mem_ball, hwv]; exact hlt hε₁ ((min_le_right _ _).trans (min_le_left _ _))
  have hwε₃ : w ∈ ball v ε₃ := by
    rw [mem_ball, hwv]; exact hlt hε₃ ((min_le_right _ _).trans (min_le_right _ _))
  have hRw := hRδ hwδ
  have hRwH : R w ∈ H := neg_inv_mem_H hwH
  have hwfA : w ∈ fillH A := hb₁ w hwε₁ hwH
  have hwA : w ∉ A := hb₃ hwε₃
  have hRwfB : R w ∈ fillH B := hb₂ (R w) (lt_of_lt_of_le hRw (min_le_left _ _)) hRwH
  have hRwB : R w ∉ B := hb₄ (lt_of_lt_of_le hRw (min_le_right _ _))
  -- the two components
  set O₁ := connectedComponentIn (H \ A) w with hO₁
  set O₂ := connectedComponentIn (H \ B) (R w) with hO₂
  have hO₁b : IsBounded O₁ := isBounded_connectedComponentIn_of_mem_fillH hA.isClosed hwfA hwA
  have hO₁f : O₁ ⊆ fillH A := connectedComponentIn_subset_fillH hA.isClosed hO₁b
  have hO₂f : O₂ ⊆ fillH B :=
    connectedComponentIn_subset_fillH hB.isClosed
      (isBounded_connectedComponentIn_of_mem_fillH hB.isClosed hRwfB hRwB)
  have hRcon : ∀ {S : Set ℂ}, S ⊆ H → ContinuousOn R S := fun hS z hz =>
    (hRc fun h => by
      have : (0 : ℝ) < z.im := hS hz
      rw [h, zero_im] at this; exact lt_irrefl 0 this).continuousWithinAt
  have hRO₁ : R '' O₁ ⊆ O₂ := by
    have hsub : O₁ ⊆ H := fun z hz => (connectedComponentIn_subset _ _ hz).1
    refine (isPreconnected_connectedComponentIn.image R (hRcon hsub)).subset_connectedComponentIn
      ⟨w, mem_connectedComponentIn ⟨hwH, hwA⟩, rfl⟩ ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨neg_inv_mem_H (hsub hz), hRB (hO₁f hz)⟩
  have hRO₂ : R '' O₂ ⊆ O₁ := by
    have hsub : O₂ ⊆ H := fun z hz => (connectedComponentIn_subset _ _ hz).1
    refine (isPreconnected_connectedComponentIn.image R (hRcon hsub)).subset_connectedComponentIn
      ⟨R w, mem_connectedComponentIn ⟨hRwH, hRwB⟩, hRR w⟩ ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨neg_inv_mem_H (hsub hz), hRA (hO₂f hz)⟩
  -- step 3: the highest point of `closure O₁`
  have hO₁ne : (closure O₁).Nonempty := ⟨w, subset_closure (mem_connectedComponentIn ⟨hwH, hwA⟩)⟩
  obtain ⟨z, hzc, hzmax⟩ := hO₁b.isCompact_closure.exists_isMaxOn hO₁ne continuous_im.continuousOn
  have hzH : z ∈ H := by
    show 0 < z.im
    exact lt_of_lt_of_le hwH (hzmax (subset_closure (mem_connectedComponentIn ⟨hwH, hwA⟩)))
  have hO₁o : IsOpen O₁ := (QuantumZipper.isOpen_H.sdiff hA.isClosed).connectedComponentIn
  have hzO₁ : z ∉ O₁ := by
    intro hz
    obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 hO₁o z hz
    have hmem : z + ((ε / 2 : ℝ) : ℂ) * I ∈ O₁ := by
      refine hεO ?_
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      exact half_lt_self hε
    have := hzmax (subset_closure hmem)
    simp only [mem_ofPred_eq, add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
      add_zero] at this
    linarith
  have hzA : z ∈ A := by
    by_contra h
    exact hzO₁ (mem_connectedComponentIn_of_mem_closure hA.isClosed hzc hzH h)
  have hz0 : z ≠ 0 := fun h => by
    have : (0 : ℝ) < z.im := hzH
    rw [h, zero_im] at this; exact lt_irrefl 0 this
  have hRzc : R z ∈ closure O₂ := closure_mono hRO₁ (mem_closure_image (hRc hz0) hzc)
  have hRzB : R z ∈ B := by
    by_contra h
    exact hzO₁ (hRO₂ ⟨R z, mem_connectedComponentIn_of_mem_closure hB.isClosed hRzc (neg_inv_mem_H hzH) h,
      hRR z⟩)
  exact Set.disjoint_left.1 hAB hzA ⟨R z, ⟨hRzB, neg_inv_ne_zero hz0⟩, hRR z⟩

/-! ### Hulls of generating traces before the first contact -/

/-- The data of a generating trace on `[0, s]` used by the disjointness theorem: the range is compact, in `ℍ̄`, its
inversion is a union of unbounded preconnected sets, and the hull is its filling. -/
theorem rangeData_of_isGeneratingTrace {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w T η)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < T}) (hw0 : w 0 = 0) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < T) :
    IsCompact (η '' Icc 0 s) ∧ η '' Icc 0 s ⊆ {z | 0 ≤ z.im} ∧
      (∀ c ∈ (fun w : ℂ => -w⁻¹) '' (η '' Icc 0 s \ {0}), ∃ P ⊆ (fun w : ℂ => -w⁻¹) '' (η '' Icc 0 s \ {0}),
        IsPreconnected P ∧ c ∈ P ∧ ¬ IsBounded P) ∧
      QuantumZipper.fwdHull (fun r : ℝ => w r.toNNReal) s = fillH (η '' Icc 0 s) := by
  have hc : ContinuousOn η (Icc 0 s) :=
    hη.2.1.mono fun t ht => le_trans (by exact_mod_cast ht.2) hs.le
  have hk : IsCompact (η '' Icc 0 s) := isCompact_Icc.image_of_continuousOn hc
  refine ⟨hk, ?_, ?_, Sec5.CrossRestart.fwdHull_eq_fillH_of_isFilling hk (hη.2.2 s hs)⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact Sec7.IsGeneratingTrace.mem_Hbar hη hw hw0 (le_trans (by exact_mod_cast ht.2) hs.le)
  · rintro _ ⟨_, ⟨⟨t, ht, rfl⟩, ht0⟩, rfl⟩
    exact exists_unbounded_inv_image hc hη.1 ht ht0

/-- **Disjoint closed hulls of two generating traces** (hull form of `disjoint_closure_fillH_inv_image`): if the
flow trace `α` on `[0, s]` misses the inversion of the counterflow trace `γ` on `[0, T]` (away from `γ = 0`), the
closures of the flow hull `K_s` and of the inverted counterflow hull `R(K'_T)` are disjoint. -/
theorem disjoint_closure_fwdHull_inv_image {wα w : ℝ≥0 → ℝ} {Tα Tγ : ℝ≥0∞} {α γ : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace wα Tα α) (hwα : ContinuousOn wα {t | (t : ℝ≥0∞) < Tα}) (hwα0 : wα 0 = 0)
    (hγ : IsGeneratingTrace w Tγ γ) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < Tγ}) (hw0 : w 0 = 0)
    {s T : ℝ≥0} (hs : (s : ℝ≥0∞) < Tα) (hT : (T : ℝ≥0∞) < Tγ)
    (hsep : ∀ t ∈ Icc 0 T, γ t ≠ 0 → -(γ t)⁻¹ ∉ α '' Icc 0 s) :
    Disjoint (closure (QuantumZipper.fwdHull (fun r : ℝ => wα r.toNNReal) s))
      (closure ((fun w : ℂ => -w⁻¹) '' QuantumZipper.fwdHull (fun r : ℝ => w r.toNNReal) T)) := by
  obtain ⟨hAk, hAH, hAu, hKA⟩ := rangeData_of_isGeneratingTrace hα hwα hwα0 hs
  obtain ⟨hBk, hBH, hBu, hKB⟩ := rangeData_of_isGeneratingTrace hγ hw hw0 hT
  rw [hKA, hKB]
  refine disjoint_closure_fillH_inv_image hAk hBk hAH hBH hAu hBu ?_
  rintro X hXA hXB x hx
  obtain ⟨b, ⟨⟨t, ht, rfl⟩, hb0⟩, hbx⟩ := hXB hx
  have := hXA hx
  rw [← hbx] at this
  exact hsep t ht hb0 this

/-- **GB6's `hd` before the first contact** (p. 519: "Before `T`, every compact pair of retained histories is
physically separated"). With `η = R̂ ∘ γ` the physical counterflow, at every counterflow time `T` before the first
contact of `η` with `α([0, s])`, the closure of the flow hull `K_s` misses the closure of the physical counterflow
hull `R(K'_T)`. This is the hypothesis `hd` of `exists_loewner_relMap`. -/
theorem disjoint_closure_fwdHull_of_lt_firstContactTime {wα w : ℝ≥0 → ℝ} {Tα Tγ : ℝ≥0∞} {α γ : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace wα Tα α) (hwα : ContinuousOn wα {t | (t : ℝ≥0∞) < Tα}) (hwα0 : wα 0 = 0)
    (hγ : IsGeneratingTrace w Tγ γ) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < Tγ}) (hw0 : w 0 = 0)
    {s T : ℝ≥0} (hs : (s : ℝ≥0∞) < Tα) (hT : (T : ℝ≥0∞) < Tγ)
    (hTc : (T : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
      ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)) :
    Disjoint (closure (QuantumZipper.fwdHull (fun r : ℝ => wα r.toNNReal) s))
      (closure ((fun w : ℂ => -w⁻¹) '' QuantumZipper.fwdHull (fun r : ℝ => w r.toNNReal) T)) := by
  refine disjoint_closure_fwdHull_inv_image hα hwα hwα0 hγ hw hw0 hs hT fun t ht ht0 hmem => ?_
  have hlt : (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
      ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s) := lt_of_le_of_lt (by exact_mod_cast ht.2) hTc
  refine notMem_of_lt_firstContactTime hlt ?_
  obtain ⟨u, hu, hux⟩ := hmem
  refine ⟨u, hu, ?_⟩
  simp only [sphereInv_coe_of_ne ht0, hux]

end GB6

end Supp8

end InteractingSLE
