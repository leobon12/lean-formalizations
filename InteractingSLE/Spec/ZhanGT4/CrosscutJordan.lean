/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.CollarBoundary
import InteractingSLE.Spec.Sec7.InteractionLens
import InteractingSLE.Foundations.Topology.Jordan.Complex

/-!
# Domains bounded by a crosscut: Jordan separation and boundary injectivity

Packet PROVE-ZHAN-GT4-A2 ("crosscut boundary injectivity"). Source: Astra, *Follow-up proofs and dependency
audit*, Part A.4.2 (`source/external/AstraIG1/ig1_followup_proofs.txt` L743–L777, ruling R38): "The original
continued process stopped when the deterministic point `−n` is first swallowed has a simple crosscut boundary, by
§A.3 … The right side is therefore the restriction of a simple interior boundary arc". This file proves the
deterministic fact behind that sentence: if the frontier in `ℍ` of a domain `D = ℍ \ K` is the open part of a
simple crosscut `γ` from `γ 0 < γ 1`, then a conformal map `F : ℍ → D` that extends continuously to `ℍ̄`, with
real boundary values off `D`, is injective on the real line.

## Main definitions

* `crosscutSeg γ`: the real segment from `γ 0` to `γ 1`; `crosscutCurve γ = γ([0, 1]) ∪ [γ 0, γ 1]`, a Jordan
  curve (`isJordanCurve_crosscutCurve`).
* `IsCrosscutDomain D γ`: `D ⊆ ℍ` open, connected, containing every point of `ℍ` far enough out, with
  `frontier D ∩ ℍ = γ((0, 1))` for a simple crosscut `γ` with `(γ 0).re < (γ 1).re`.

## Main results

* `IsCrosscutDomain.exists_inside`: the bounded component `V` of the complement of `crosscutCurve γ` lies in
  `ℍ \ D`, `ℍ \ D ⊆ V ∪ γ((0, 1))`, and `frontier V = crosscutCurve γ`.
* `IsCrosscutDomain.exists_ball_inter_H_subset_compl`: real points strictly between the crosscut's endpoints have
  a relative half-disc neighbourhood outside `D`;
* `IsCrosscutDomain.exists_ball_inter_H_subset`: real points outside `[γ 0, γ 1]` have one inside `D`;
* `IsCrosscutDomain.false_of_eq`: **boundary injectivity** — if `F` is continuous on `ℍ̄`, holomorphic and injective
  on `ℍ` with `F(ℍ) = D`, moves points by a bounded amount, and its real boundary values lie off `D`, then
  `F v₁ = F v₂` with `v₁ < v₂` is impossible: `F` is injective on `ℝ`.

## Proof of the boundary injectivity

Let `p = F v₁ = F v₂` (a point of `closure D \ D`) and let `α` be the image under `F` of the upper semicircle over
`[v₁, v₂]`: a Jordan curve through `p`, otherwise inside `D`. Its bounded complementary component `J` lies in `ℍ`. It cannot meet `ℍ \ D`:
that set is in `V ∪ γ((0, 1))`, so `J` would meet `V`, then contain the connected set `V`, and the whole real
segment `(γ 0, γ 1) ⊆ closure V` would lie in `closure J ∩ ℝ ⊆ {p}`. So `J ⊆ D`. The image under `F` of the open
half-disc over `[v₁, v₂]` lies in `J` (it is connected and misses `α`; a point of `J` has a preimage, and if that
preimage were outside the half-disc, `F` of the vertical ray above it would be a connected unbounded subset of
`J`). Hence every boundary value of `F` on `(v₁, v₂)` lies in `closure J \ D ⊆ α \ D = {p}`, and Schwarz
reflection and the identity theorem make `F` constant on the half-disc, contradicting injectivity.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Bornology
open scoped ComplexConjugate

namespace InteractingSLE.ZhanGT4

open QuantumZipper

/-! ### The closed curve of a crosscut -/

/-- The real segment from `γ 0` to `γ 1`, parametrized by `[0, 1]`. -/
def crosscutSeg (γ : ℝ → ℂ) (s : ℝ) : ℂ := γ 0 + (s : ℂ) * (γ 1 - γ 0)

/-- The closed curve formed by a crosscut and the real segment between its endpoints. -/
def crosscutCurve (γ : ℝ → ℂ) : Set ℂ := γ '' Icc 0 1 ∪ crosscutSeg γ '' Icc 0 1

theorem continuous_crosscutSeg (γ : ℝ → ℂ) : Continuous (crosscutSeg γ) := by
  unfold crosscutSeg; fun_prop

theorem crosscutSeg_im {γ : ℝ → ℂ} (hγ : IsRealCrosscut γ) (s : ℝ) : (crosscutSeg γ s).im = 0 := by
  simp [crosscutSeg, hγ.2.2.2.1, hγ.2.2.2.2]

theorem crosscutSeg_re (γ : ℝ → ℂ) (s : ℝ) :
    (crosscutSeg γ s).re = (γ 0).re + s * ((γ 1).re - (γ 0).re) := by
  simp [crosscutSeg]

theorem crosscutSeg_zero (γ : ℝ → ℂ) : crosscutSeg γ 0 = γ 0 := by simp [crosscutSeg]

theorem crosscutSeg_one (γ : ℝ → ℂ) : crosscutSeg γ 1 = γ 1 := by simp [crosscutSeg]

theorem eq_ofReal_re_of_im_eq_zero {z : ℂ} (h : z.im = 0) : z = (z.re : ℂ) :=
  Complex.ext (by simp) (by simp [h])

/-- The points of the crosscut on the real line are its two endpoints. -/
theorem IsRealCrosscut.eq_of_im_eq_zero {γ : ℝ → ℂ} (hγ : IsRealCrosscut γ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (him : (γ s).im = 0) : s = 0 ∨ s = 1 := by
  rcases eq_or_lt_of_le hs.1 with h | h
  · exact Or.inl h.symm
  rcases eq_or_lt_of_le hs.2 with h' | h'
  · exact Or.inr h'
  have := hγ.2.2.1 (mem_image_of_mem γ ⟨h, h'⟩)
  exact absurd him (ne_of_gt this)

theorem IsRealCrosscut.im_nonneg {γ : ℝ → ℂ} (hγ : IsRealCrosscut γ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    0 ≤ (γ s).im := by
  rcases eq_or_lt_of_le hs.1 with h | h
  · rw [← h, hγ.2.2.2.1]
  rcases eq_or_lt_of_le hs.2 with h' | h'
  · rw [h', hγ.2.2.2.2]
  exact (hγ.2.2.1 (mem_image_of_mem γ ⟨h, h'⟩)).le

/-- **The crosscut closed by its real base is a Jordan curve.** -/
theorem isJordanCurve_crosscutCurve {γ : ℝ → ℂ} (hγ : IsRealCrosscut γ) (hlt : (γ 0).re < (γ 1).re) :
    LQGMetric.JordanMap.IsJordanCurve (crosscutCurve γ) := by
  have hne : (γ 1).re - (γ 0).re ≠ 0 := by linarith
  refine Sec7.isJordanCurve_image_union hγ.1 (continuous_crosscutSeg γ).continuousOn hγ.2.1 ?_
    (crosscutSeg_zero γ).symm (crosscutSeg_one γ).symm ?_
  · intro s _ t _ hst
    have h := congrArg Complex.re hst
    rw [crosscutSeg_re, crosscutSeg_re] at h
    have : (s - t) * ((γ 1).re - (γ 0).re) = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · exact absurd h1 hne
  · rintro z ⟨⟨s, hs, rfl⟩, ⟨t, -, ht⟩⟩
    have him : (γ s).im = 0 := by rw [← ht, crosscutSeg_im hγ]
    rcases hγ.eq_of_im_eq_zero hs him with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem isCompact_crosscutCurve {γ : ℝ → ℂ} (hγ : IsRealCrosscut γ) : IsCompact (crosscutCurve γ) :=
  (isCompact_Icc.image_of_continuousOn hγ.1).union
    (isCompact_Icc.image_of_continuousOn (continuous_crosscutSeg γ).continuousOn)

/-- Every point of the closed curve has nonnegative imaginary part. -/
theorem crosscutCurve_im_nonneg {γ : ℝ → ℂ} (hγ : IsRealCrosscut γ) {z : ℂ} (hz : z ∈ crosscutCurve γ) :
    0 ≤ z.im := by
  rcases hz with ⟨s, hs, rfl⟩ | ⟨s, -, rfl⟩
  · exact hγ.im_nonneg hs
  · rw [crosscutSeg_im hγ]

/-- The real points of the closed curve are the points of the segment `[γ 0, γ 1]`. -/
theorem mem_crosscutCurve_of_real {γ : ℝ → ℂ} (hγ : IsRealCrosscut γ) (hlt : (γ 0).re < (γ 1).re) {x : ℝ}
    (hx : x ∈ Icc (γ 0).re (γ 1).re) : (x : ℂ) ∈ crosscutCurve γ := by
  refine Or.inr ⟨(x - (γ 0).re) / ((γ 1).re - (γ 0).re), ⟨div_nonneg (by linarith [hx.1]) (by linarith),
    (div_le_one (by linarith)).2 (by linarith [hx.2])⟩, ?_⟩
  apply Complex.ext
  · have hne : (γ 1).re - (γ 0).re ≠ 0 := by linarith
    rw [crosscutSeg_re, Complex.ofReal_re]; field_simp; ring
  · rw [crosscutSeg_im hγ]; simp

theorem re_mem_Icc_of_mem_crosscutCurve {γ : ℝ → ℂ} (hγ : IsRealCrosscut γ) (hlt : (γ 0).re < (γ 1).re)
    {z : ℂ} (hz : z ∈ crosscutCurve γ) (him : z.im = 0) : z.re ∈ Icc (γ 0).re (γ 1).re := by
  rcases hz with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
  · rcases hγ.eq_of_im_eq_zero hs him with rfl | rfl
    · exact ⟨le_rfl, hlt.le⟩
    · exact ⟨hlt.le, le_rfl⟩
  · rw [crosscutSeg_re]
    constructor <;> nlinarith [hs.1, hs.2]

/-! ### Domains bounded by a crosscut -/

/-- The open lower half-plane. -/
def lowerHalf : Set ℂ := {z : ℂ | z.im < 0}

theorem isPreconnected_lowerHalf : IsPreconnected lowerHalf :=
  (convex_halfSpace_lt (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0).isPreconnected

theorem isOpen_lowerHalf : IsOpen lowerHalf := isOpen_lt continuous_im continuous_const


/-- **A domain of `ℍ` bounded by a crosscut**: `D ⊆ ℍ` is open and connected, contains all points of `ℍ` far
enough from the origin, and its frontier inside `ℍ` is the open part of the simple crosscut `γ`, whose endpoints
satisfy `γ 0 < γ 1`. -/
structure IsCrosscutDomain (D : Set ℂ) (γ : ℝ → ℂ) : Prop where
  isOpen : IsOpen D
  subset_H : D ⊆ H
  isPreconnected : IsPreconnected D
  far : ∃ R : ℝ, ∀ z ∈ H, R < ‖z‖ → z ∈ D
  crosscut : IsRealCrosscut γ
  re_lt : (γ 0).re < (γ 1).re
  frontier_inter : frontier D ∩ H = γ '' Ioo 0 1

namespace IsCrosscutDomain

variable {D : Set ℂ} {γ : ℝ → ℂ}

theorem disjoint_crosscut (hD : IsCrosscutDomain D γ) : Disjoint D (γ '' Ioo 0 1) := by
  rw [← hD.frontier_inter]
  refine Set.disjoint_left.2 fun z hz hz' => ?_
  have := hD.isOpen.inter_frontier_eq
  exact (Set.eq_empty_iff_forall_notMem.1 this) z ⟨hz, hz'.1⟩

theorem disjoint_curve (hD : IsCrosscutDomain D γ) : Disjoint D (crosscutCurve γ) := by
  refine Set.disjoint_left.2 fun z hz hz' => ?_
  have hzH : 0 < z.im := hD.subset_H hz
  rcases hz' with ⟨s, hs, rfl⟩ | ⟨s, -, rfl⟩
  · rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h, hD.crosscut.2.2.2.1] at hzH; exact lt_irrefl _ hzH
    rcases eq_or_lt_of_le hs.2 with h' | h'
    · rw [h', hD.crosscut.2.2.2.2] at hzH; exact lt_irrefl _ hzH
    exact Set.disjoint_left.1 hD.disjoint_crosscut hz (mem_image_of_mem γ ⟨h, h'⟩)
  · rw [crosscutSeg_im hD.crosscut] at hzH; exact lt_irrefl _ hzH

/-- A connected subset of `ℍ` that misses the crosscut and meets `D` lies in `D`. -/
theorem subset_of_isPreconnected (hD : IsCrosscutDomain D γ) {C : Set ℂ} (hC : IsPreconnected C)
    (hCH : C ⊆ H) (hCγ : Disjoint C (γ '' Ioo 0 1)) (hCD : (C ∩ D).Nonempty) : C ⊆ D := by
  refine hC.subset_left_of_subset_union hD.isOpen isClosed_closure.isOpen_compl
    (Set.disjoint_left.2 fun z hz hz' => hz' (subset_closure hz)) (fun z hz => ?_) hCD
  by_cases hzD : z ∈ D
  · exact Or.inl hzD
  refine Or.inr fun hzc => Set.disjoint_left.1 hCγ hz ?_
  rw [← hD.frontier_inter]
  exact ⟨⟨hzc, by rwa [hD.isOpen.interior_eq]⟩, hCH hz⟩

/-- A point of `ℍ` of large modulus above a given real point lies in `D`. -/
theorem exists_far_mem (hD : IsCrosscutDomain D γ) : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ H, R < ‖z‖ → z ∈ D := by
  obtain ⟨R, hR⟩ := hD.far
  exact ⟨max R 1, by positivity, fun z hz hzR => hR z hz (lt_of_le_of_lt (le_max_left _ _) hzR)⟩

/-- **Real points beyond the crosscut's ends have half-disc neighbourhoods in `D`.** If a closed convex set `S` of
real points misses the closed curve and is unbounded, then a uniform relative neighbourhood of `S` in `ℍ` lies in
`D`. -/
theorem exists_thickening_inter_H_subset (hD : IsCrosscutDomain D γ) {S : Set ℂ} (hSc : IsClosed S)
    (hSv : Convex ℝ S) (hSr : ∀ z ∈ S, z.im = 0) (hSΓ : Disjoint S (crosscutCurve γ))
    (hSu : ∀ M : ℝ, ∃ z ∈ S, M < ‖z‖) :
    ∃ δ > (0 : ℝ), thickening δ S ∩ H ⊆ D := by
  obtain ⟨z₁, hz₁S, -⟩ := hSu 0
  have hSne : S.Nonempty := ⟨z₁, hz₁S⟩
  have hΓc := isCompact_crosscutCurve hD.crosscut
  have hΓne : (crosscutCurve γ).Nonempty := ⟨γ 0, Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩⟩
  obtain ⟨z₀, hz₀, hmin⟩ := hΓc.exists_isMinOn hΓne (continuous_infDist_pt S).continuousOn
  have hδ : 0 < infDist z₀ S :=
    (hSc.notMem_iff_infDist_pos hSne).1 fun h => Set.disjoint_left.1 hSΓ h hz₀
  set δ := infDist z₀ S with hδdef
  refine ⟨δ, hδ, ?_⟩
  have hconv : Convex ℝ (thickening δ S ∩ H) := (hSv.thickening δ).inter (convex_halfSpace_gt
    (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0)
  refine hD.subset_of_isPreconnected hconv.isPreconnected inter_subset_right ?_ ?_
  · refine Set.disjoint_left.2 fun z hz hzγ => ?_
    obtain ⟨w, hwS, hwd⟩ := mem_thickening_iff.1 hz.1
    have hzΓ : z ∈ crosscutCurve γ := Or.inl (image_mono Ioo_subset_Icc_self hzγ)
    have h1 : δ ≤ infDist z S := hmin hzΓ
    have h2 : infDist z S ≤ dist z w := infDist_le_dist_of_mem hwS
    linarith
  · obtain ⟨R, hR0, hR⟩ := hD.exists_far_mem
    obtain ⟨w, hwS, hwR⟩ := hSu (R + δ)
    set z : ℂ := w + ((δ / 2 : ℝ) : ℂ) * I with hz
    have hzim : z.im = δ / 2 := by simp [hz, hSr w hwS]
    have hzH : z ∈ H := by show 0 < z.im; rw [hzim]; linarith
    have hzw : dist z w = δ / 2 := by
      rw [dist_eq_norm, hz, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith)]
    refine ⟨z, ⟨mem_thickening_iff.2 ⟨w, hwS, by rw [hzw]; linarith⟩, hzH⟩, hR z hzH ?_⟩
    have := norm_sub_norm_le w z
    rw [← dist_eq_norm, dist_comm, hzw] at this
    linarith

theorem disjoint_Iic_crosscutCurve (hD : IsCrosscutDomain D γ) {x : ℝ} (hx : x < (γ 0).re) :
    Disjoint (((↑) : ℝ → ℂ) '' Iic x) (crosscutCurve γ) := by
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨y, hy, rfl⟩ hyΓ
  have := re_mem_Icc_of_mem_crosscutCurve hD.crosscut hD.re_lt hyΓ (by simp)
  rw [Complex.ofReal_re] at this
  exact absurd (lt_of_le_of_lt hy hx) (not_lt.2 this.1)

theorem disjoint_Ici_crosscutCurve (hD : IsCrosscutDomain D γ) {x : ℝ} (hx : (γ 1).re < x) :
    Disjoint (((↑) : ℝ → ℂ) '' Ici x) (crosscutCurve γ) := by
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨y, hy, rfl⟩ hyΓ
  have := re_mem_Icc_of_mem_crosscutCurve hD.crosscut hD.re_lt hyΓ (by simp)
  rw [Complex.ofReal_re] at this
  exact absurd (lt_of_lt_of_le hx hy) (not_lt.2 this.2)

theorem isClosed_ofReal_image {s : Set ℝ} (hs : IsClosed s) : IsClosed (((↑) : ℝ → ℂ) '' s) :=
  Complex.isometry_ofReal.isClosedEmbedding.isClosedMap s hs

theorem convex_ofReal_image {s : Set ℝ} (hs : Convex ℝ s) : Convex ℝ (((↑) : ℝ → ℂ) '' s) :=
  hs.linear_image Complex.ofRealLI.toLinearMap

/-- **Half-disc neighbourhoods in `D`** of the real points outside `[γ 0, γ 1]`. -/
theorem exists_ball_inter_H_subset (hD : IsCrosscutDomain D γ) {x : ℝ}
    (hx : x < (γ 0).re ∨ (γ 1).re < x) : ∃ δ > (0 : ℝ), ball (x : ℂ) δ ∩ H ⊆ D := by
  rcases hx with hx | hx
  · obtain ⟨δ, hδ, h⟩ := hD.exists_thickening_inter_H_subset (isClosed_ofReal_image isClosed_Iic)
      (convex_ofReal_image (convex_Iic x)) (by rintro _ ⟨y, -, rfl⟩; simp)
      (hD.disjoint_Iic_crosscutCurve hx) fun M => ⟨((min x (-|M| - 1) : ℝ) : ℂ),
        mem_image_of_mem _ (show min x (-|M| - 1) ∈ Iic x from mem_Iic.2 (min_le_left _ _)), by
          rw [Complex.norm_real, Real.norm_eq_abs]
          have h1 := min_le_right x (-|M| - 1)
          have h0 := abs_nonneg M
          have h2 : -min x (-|M| - 1) ≤ |min x (-|M| - 1)| := neg_le_abs _
          linarith [le_abs_self M]⟩
    refine ⟨δ, hδ, fun z hz => h ⟨mem_thickening_iff.2 ⟨x, ⟨x, mem_Iic.2 le_rfl, rfl⟩, hz.1⟩, hz.2⟩⟩
  · obtain ⟨δ, hδ, h⟩ := hD.exists_thickening_inter_H_subset (isClosed_ofReal_image isClosed_Ici)
      (convex_ofReal_image (convex_Ici x)) (by rintro _ ⟨y, -, rfl⟩; simp)
      (hD.disjoint_Ici_crosscutCurve hx) fun M => ⟨((max x (|M| + 1) : ℝ) : ℂ),
        mem_image_of_mem _ (show max x (|M| + 1) ∈ Ici x from mem_Ici.2 (le_max_left _ _)), by
          rw [Complex.norm_real, Real.norm_eq_abs]
          have h1 := le_max_right x (|M| + 1)
          have h2 := le_abs_self (max x (|M| + 1))
          linarith [le_abs_self M]⟩
    refine ⟨δ, hδ, fun z hz => h ⟨mem_thickening_iff.2 ⟨x, ⟨x, mem_Ici.2 le_rfl, rfl⟩, hz.1⟩, hz.2⟩⟩

/-- **The inside of the crosscut** (Jordan separation): the bounded component `V` of the complement of the closed
curve `γ([0, 1]) ∪ [γ 0, γ 1]` lies in `ℍ \ D`, every point of `ℍ \ D` off the crosscut lies in `V`, and the
frontier of `V` is the whole closed curve. -/
theorem exists_inside (hD : IsCrosscutDomain D γ) :
    ∃ V : Set ℂ, IsOpen V ∧ IsPreconnected V ∧ V ⊆ H ∧ Disjoint V D ∧
      H \ D ⊆ V ∪ γ '' Ioo 0 1 ∧ frontier V = crosscutCurve γ ∧ Disjoint V (crosscutCurve γ) := by
  set Γ := crosscutCurve γ with hΓ
  have hΓc : IsCompact Γ := isCompact_crosscutCurve hD.crosscut
  have hΓo : IsOpen Γᶜ := hΓc.isClosed.isOpen_compl
  obtain ⟨x₁, -, x₀, -, hb, -, hdisj, hunion, hfr₁, -⟩ :=
    jordan_curve_components (isJordanCurve_crosscutCurve hD.crosscut hD.re_lt)
  set V := connectedComponentIn Γᶜ x₁ with hV
  set U := connectedComponentIn Γᶜ x₀ with hU
  have hVo : IsOpen V := hΓo.connectedComponentIn
  have hUo : IsOpen U := hΓo.connectedComponentIn
  have hVΓ : V ⊆ Γᶜ := connectedComponentIn_subset _ _
  -- far points are in `U`
  obtain ⟨R₁, hR₁⟩ := (hb.union hΓc.isBounded).subset_ball (0 : ℂ)
  have hfarU : ∀ z : ℂ, R₁ ≤ ‖z‖ → z ∈ U := by
    intro z hz
    have hzV : z ∉ V := fun h => by
      have := hR₁ (Or.inl h); rw [mem_ball_zero_iff] at this; linarith
    have hzΓ : z ∉ Γ := fun h => by
      have := hR₁ (Or.inr h); rw [mem_ball_zero_iff] at this; linarith
    have : z ∈ Γᶜ := hzΓ
    rw [hunion] at this
    exact this.resolve_left hzV
  have hsubU : ∀ {C : Set ℂ} {z : ℂ}, IsPreconnected C → z ∈ C → C ⊆ Γᶜ → R₁ ≤ ‖z‖ → C ⊆ U := by
    intro C z hC hz hCΓ hzR
    have h := hC.subset_connectedComponentIn hz hCΓ
    rwa [← connectedComponentIn_eq (hfarU z hzR)] at h
  -- the lower half-plane is in `U`
  have hLΓ : lowerHalf ⊆ Γᶜ := fun z hz hzΓ => by
    have := crosscutCurve_im_nonneg hD.crosscut hzΓ
    exact absurd hz (not_lt.2 this)
  have hR₁0 : 0 ≤ R₁ := by
    have := hR₁ (Or.inr (Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩) : γ 0 ∈ V ∪ Γ)
    rw [mem_ball_zero_iff] at this; linarith [norm_nonneg (γ 0)]
  have hzL : (-(R₁ + 1 : ℝ) : ℂ) * I ∈ lowerHalf := by
    show (_ : ℂ).im < 0; simp; linarith
  have hzLn : R₁ ≤ ‖(-(R₁ + 1 : ℝ) : ℂ) * I‖ := by
    rw [norm_mul, Complex.norm_I, mul_one, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
  have hLU : lowerHalf ⊆ U := hsubU isPreconnected_lowerHalf hzL hLΓ hzLn
  -- `V ⊆ ℍ`
  have hVH : V ⊆ H := by
    intro z hz
    show 0 < z.im
    rcases lt_trichotomy z.im 0 with h | h | h
    · exact absurd (hLU h) (Set.disjoint_left.1 hdisj hz)
    · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΓo z (hVΓ hz)
      have hballV : ball z r ⊆ V := by
        have h' := (convex_ball z r).isPreconnected.subset_connectedComponentIn (mem_ball_self hr) hball
        rwa [← connectedComponentIn_eq hz] at h'
      set w : ℂ := z - ((r / 2 : ℝ) : ℂ) * I with hw
      have hwb : w ∈ ball z r := by
        rw [mem_ball, dist_eq_norm, hw, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I,
          mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
      have hwL : w ∈ lowerHalf := by show w.im < 0; simp [hw, h]; linarith
      exact absurd (hLU hwL) (Set.disjoint_left.1 hdisj (hballV hwb))
    · exact h
  -- `D ⊆ U`
  obtain ⟨R₂, hR₂0, hR₂⟩ := hD.exists_far_mem
  have hzD : (((max R₁ R₂) + 1 : ℝ) : ℂ) * I ∈ D := by
    refine hR₂ _ (by show 0 < (_ : ℂ).im; simp; positivity) ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    linarith [le_max_right R₁ R₂]
  have hDU : D ⊆ U := hsubU hD.isPreconnected hzD
    (fun z hz hzΓ => Set.disjoint_left.1 hD.disjoint_curve hz hzΓ) (by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith [le_max_left R₁ R₂])
  have hVD : Disjoint V D :=
    Set.disjoint_left.2 fun z hz hzD => Set.disjoint_left.1 hdisj hz (hDU hzD)
  -- `ℍ \ closure D` does not meet `U`
  have hclH : ∀ z ∈ H, z ∈ closure D → z ∈ D ∨ z ∈ γ '' Ioo 0 1 := by
    intro z hzH hzc
    by_cases hzD : z ∈ D
    · exact Or.inl hzD
    right
    rw [← hD.frontier_inter]
    exact ⟨⟨hzc, by rwa [hD.isOpen.interior_eq]⟩, hzH⟩
  set O := H \ closure D with hO
  have hOo : IsOpen O := isOpen_H.sdiff isClosed_closure
  have hUO : U ∩ O = ∅ := by
    have hsub : U ⊆ (closure O)ᶜ := by
      refine isPreconnected_connectedComponentIn.subset_left_of_subset_union
        isClosed_closure.isOpen_compl hOo
        (Set.disjoint_left.2 fun z hz hz' => hz (subset_closure hz')) (fun y hy => ?_) ?_
      · by_cases hyO : y ∈ closure O
        swap
        · exact Or.inl hyO
        right
        have hyim : 0 ≤ y.im := by
          have : closure O ⊆ closure H := closure_mono (fun z hz => hz.1)
          rw [closure_H] at this
          exact this hyO
        rcases eq_or_lt_of_le hyim with h | h
        · -- a real point of `U` lies outside `[γ 0, γ 1]`, hence has a half-disc in `D`
          have hyΓ : y ∉ Γ := connectedComponentIn_subset _ _ hy
          have hyre : y.re < (γ 0).re ∨ (γ 1).re < y.re := by
            by_contra hc
            push Not at hc
            exact hyΓ (by
              rw [eq_ofReal_re_of_im_eq_zero h.symm]
              exact mem_crosscutCurve_of_real hD.crosscut hD.re_lt hc)
          obtain ⟨δ, hδ, hball⟩ := hD.exists_ball_inter_H_subset hyre
          exfalso
          have hy' : (y.re : ℂ) = y := (eq_ofReal_re_of_im_eq_zero h.symm).symm
          rw [hy'] at hball
          obtain ⟨w, hwO, hwb⟩ := Metric.mem_closure_iff.1 hyO δ hδ
          rw [dist_comm] at hwb
          exact hwO.2 (subset_closure (hball ⟨hwb, hwO.1⟩))
        · have hyH : y ∈ H := h
          have hyD : y ∉ D := by
            have : closure O ⊆ closure Dᶜ := closure_mono fun z hz hzD => hz.2 (subset_closure hzD)
            rw [hD.isOpen.isClosed_compl.closure_eq] at this
            exact this hyO
          refine ⟨hyH, fun hyc => ?_⟩
          rcases hclH y hyH hyc with h' | h'
          · exact hyD h'
          · exact (connectedComponentIn_subset _ _ hy) (Or.inl (image_mono Ioo_subset_Icc_self h'))
      · refine ⟨_, hLU hzL, fun hzO => ?_⟩
        have : closure O ⊆ closure H := closure_mono (fun z hz => hz.1)
        rw [closure_H] at this
        have h1 : 0 ≤ ((-(R₁ + 1 : ℝ) : ℂ) * I).im := this hzO
        have h2 : ((-(R₁ + 1 : ℝ) : ℂ) * I).im < 0 := hzL
        linarith
    exact Set.eq_empty_iff_forall_notMem.2 fun z hz => hsub hz.1 (subset_closure hz.2)
  refine ⟨V, hVo, isPreconnected_connectedComponentIn, hVH, hVD, ?_, hfr₁,
    Set.disjoint_left.2 fun z hz => hVΓ hz⟩
  intro z hz
  by_cases hzγ : z ∈ γ '' Ioo 0 1
  · exact Or.inr hzγ
  left
  have hzO : z ∈ O := ⟨hz.1, fun hzc => (hclH z hz.1 hzc).elim hz.2 hzγ⟩
  have hzΓ : z ∈ Γᶜ := by
    rintro (⟨s, hs, rfl⟩ | ⟨s, -, rfl⟩)
    · have hzH : 0 < (γ s).im := hz.1
      rcases eq_or_lt_of_le hs.1 with h | h
      · rw [← h, hD.crosscut.2.2.2.1] at hzH; exact lt_irrefl _ hzH
      rcases eq_or_lt_of_le hs.2 with h' | h'
      · rw [h', hD.crosscut.2.2.2.2] at hzH; exact lt_irrefl _ hzH
      exact hzγ (mem_image_of_mem γ ⟨h, h'⟩)
    · have hzH : 0 < (crosscutSeg γ s).im := hz.1
      rw [crosscutSeg_im hD.crosscut] at hzH
      exact lt_irrefl _ hzH
  rw [hunion] at hzΓ
  exact hzΓ.resolve_right fun hzU => (Set.eq_empty_iff_forall_notMem.1 hUO) z ⟨hzU, hzO⟩

/-- **Half-disc neighbourhoods in the inside** of the real points strictly between the crosscut's ends. -/
theorem exists_ball_inter_H_subset_inside (hD : IsCrosscutDomain D γ) {V : Set ℂ} (hVo : IsOpen V)
    (hVH : V ⊆ H) (hfr : frontier V = crosscutCurve γ) {x : ℝ} (hx : x ∈ Ioo (γ 0).re (γ 1).re) :
    ∃ r > (0 : ℝ), ball (x : ℂ) r ∩ H ⊆ V := by
  have hK : IsClosed (γ '' Icc 0 1) := (isCompact_Icc.image_of_continuousOn hD.crosscut.1).isClosed
  have hxK : (x : ℂ) ∉ γ '' Icc 0 1 := by
    rintro ⟨s, hs, hsx⟩
    have him : (γ s).im = 0 := by rw [hsx]; simp
    have hre : (γ s).re = x := by rw [hsx]; simp
    rcases hD.crosscut.eq_of_im_eq_zero hs him with rfl | rfl
    · linarith [hx.1]
    · linarith [hx.2]
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hK.isOpen_compl _ hxK
  refine ⟨r, hr, ?_⟩
  have hconv : Convex ℝ (ball (x : ℂ) r ∩ H) :=
    (convex_ball _ r).inter (convex_halfSpace_gt (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0)
  have hxV : (x : ℂ) ∈ closure V := by
    have : (x : ℂ) ∈ frontier V := by
      rw [hfr]; exact mem_crosscutCurve_of_real hD.crosscut hD.re_lt (Ioo_subset_Icc_self hx)
    exact this.1
  obtain ⟨v, hvV, hvd⟩ := Metric.mem_closure_iff.1 hxV r hr
  refine hconv.isPreconnected.subset_left_of_subset_union hVo isClosed_closure.isOpen_compl
    (Set.disjoint_left.2 fun z hz hz' => hz' (subset_closure hz)) (fun z hz => ?_)
    ⟨v, ⟨by rw [mem_ball, dist_comm]; exact hvd, hVH hvV⟩, hvV⟩
  by_cases hzV : z ∈ V
  · exact Or.inl hzV
  refine Or.inr fun hzc => ?_
  have hzf : z ∈ frontier V := ⟨hzc, by rwa [hVo.interior_eq]⟩
  rw [hfr] at hzf
  rcases hzf with hzγ | ⟨s, -, rfl⟩
  · exact hball hz.1 hzγ
  · have : 0 < (crosscutSeg γ s).im := hz.2
    rw [crosscutSeg_im hD.crosscut] at this
    exact lt_irrefl _ this

end IsCrosscutDomain

/-! ### Jordan curves in the closed upper half-plane -/

/-- **A Jordan curve in `ℍ̄` has its inside in `ℍ`.** -/
theorem exists_inside_of_subset_Hbar {Γ : Set ℂ} (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ)
    (hΓH : ∀ z ∈ Γ, 0 ≤ z.im) :
    ∃ J E : Set ℂ, IsOpen J ∧ IsOpen E ∧ IsPreconnected J ∧ IsPreconnected E ∧ J.Nonempty ∧ IsBounded J ∧
      J ⊆ H ∧ Disjoint J E ∧ Γᶜ = J ∪ E ∧ frontier J = Γ ∧ ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → z ∈ E := by
  have hΓc : IsCompact Γ := Foundations.Schoenflies.isCompact_of_isJordanCurve hΓ
  have hΓo : IsOpen Γᶜ := hΓc.isClosed.isOpen_compl
  obtain ⟨x₁, hx₁, x₀, -, hb, -, hdisj, hunion, hfr₁, -⟩ := jordan_curve_components hΓ
  set J := connectedComponentIn Γᶜ x₁ with hJ
  set E := connectedComponentIn Γᶜ x₀ with hE
  obtain ⟨R₁, hR₁⟩ := (hb.union hΓc.isBounded).subset_ball (0 : ℂ)
  have hfarE : ∀ z : ℂ, R₁ ≤ ‖z‖ → z ∈ E := by
    intro z hz
    have hzJ : z ∉ J := fun h => by
      have := hR₁ (Or.inl h); rw [mem_ball_zero_iff] at this; linarith
    have hzΓ : z ∉ Γ := fun h => by
      have := hR₁ (Or.inr h); rw [mem_ball_zero_iff] at this; linarith
    have : z ∈ Γᶜ := hzΓ
    rw [hunion] at this
    exact this.resolve_left hzJ
  have hR₁0 : 0 ≤ R₁ := by
    have := hR₁ (Or.inl (mem_connectedComponentIn hx₁))
    rw [mem_ball_zero_iff] at this; linarith [norm_nonneg x₁]
  have hLΓ : lowerHalf ⊆ Γᶜ := fun z hz hzΓ => absurd hz (not_lt.2 (hΓH z hzΓ))
  have hzL : (-(R₁ + 1 : ℝ) : ℂ) * I ∈ lowerHalf := by
    show (_ : ℂ).im < 0; simp; linarith
  have hLE : lowerHalf ⊆ E := by
    have h := isPreconnected_lowerHalf.subset_connectedComponentIn hzL hLΓ
    rwa [← connectedComponentIn_eq (hfarE _ (by
      rw [norm_mul, Complex.norm_I, mul_one, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]; linarith))] at h
  have hJH : J ⊆ H := by
    intro z hz
    show 0 < z.im
    rcases lt_trichotomy z.im 0 with h | h | h
    · exact absurd (hLE h) (Set.disjoint_left.1 hdisj hz)
    · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΓo z (connectedComponentIn_subset _ _ hz)
      have hballJ : ball z r ⊆ J := by
        have h' := (convex_ball z r).isPreconnected.subset_connectedComponentIn (mem_ball_self hr) hball
        rwa [← connectedComponentIn_eq hz] at h'
      set w : ℂ := z - ((r / 2 : ℝ) : ℂ) * I with hw
      have hwb : w ∈ ball z r := by
        rw [mem_ball, dist_eq_norm, hw, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I,
          mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
      have hwL : w ∈ lowerHalf := by show w.im < 0; simp [hw, h]; linarith
      exact absurd (hLE hwL) (Set.disjoint_left.1 hdisj (hballJ hwb))
    · exact h
  exact ⟨J, E, hΓo.connectedComponentIn, hΓo.connectedComponentIn, isPreconnected_connectedComponentIn,
    isPreconnected_connectedComponentIn, ⟨x₁, mem_connectedComponentIn hx₁⟩, hb, hJH, hdisj, hunion, hfr₁,
    R₁, hfarE⟩

/-! ### The semicircle over a real interval -/

/-- The upper semicircle of centre `m` and radius `ρ`: `θ ↦ m + ρ e^{iθ}`. -/
def semicircle (m ρ : ℝ) (θ : ℝ) : ℂ := (m : ℂ) + (ρ : ℂ) * exp ((θ : ℂ) * I)

theorem continuous_semicircle (m ρ : ℝ) : Continuous (semicircle m ρ) := by
  unfold semicircle; fun_prop

theorem semicircle_re (m ρ θ : ℝ) : (semicircle m ρ θ).re = m + ρ * Real.cos θ := by
  simp [semicircle, Complex.exp_ofReal_mul_I_re]

theorem semicircle_im (m ρ θ : ℝ) : (semicircle m ρ θ).im = ρ * Real.sin θ := by
  simp [semicircle, Complex.exp_ofReal_mul_I_im]

theorem semicircle_zero (m ρ : ℝ) : semicircle m ρ 0 = ((m + ρ : ℝ) : ℂ) := by
  simp [semicircle]

theorem semicircle_pi (m ρ : ℝ) : semicircle m ρ Real.pi = ((m - ρ : ℝ) : ℂ) := by
  simp [semicircle, Complex.exp_pi_mul_I]; ring

theorem norm_semicircle_sub (m ρ θ : ℝ) (hρ : 0 ≤ ρ) : ‖semicircle m ρ θ - m‖ = ρ := by
  simp [semicircle, Complex.norm_exp_ofReal_mul_I, abs_of_nonneg hρ]

theorem semicircle_mem_H {m ρ θ : ℝ} (hρ : 0 < ρ) (hθ : θ ∈ Ioo 0 Real.pi) : semicircle m ρ θ ∈ H := by
  show 0 < (semicircle m ρ θ).im
  rw [semicircle_im]
  exact mul_pos hρ (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)

theorem semicircle_mem_Hbar {m ρ θ : ℝ} (hρ : 0 ≤ ρ) (hθ : θ ∈ Icc 0 Real.pi) :
    semicircle m ρ θ ∈ Hbar := by
  show 0 ≤ (semicircle m ρ θ).im
  rw [semicircle_im]
  exact mul_nonneg hρ (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2)

theorem injOn_semicircle {m ρ : ℝ} (hρ : 0 < ρ) : InjOn (semicircle m ρ) (Icc 0 Real.pi) := by
  intro θ hθ θ' hθ' h
  have h1 := congrArg Complex.re h
  rw [semicircle_re, semicircle_re] at h1
  have h2 : Real.cos θ = Real.cos θ' := by
    have := mul_left_cancel₀ hρ.ne' (by linarith : ρ * Real.cos θ = ρ * Real.cos θ')
    exact this
  exact Real.injOn_cos hθ hθ' h2

end InteractingSLE.ZhanGT4

namespace InteractingSLE.ZhanGT4

open QuantumZipper

/-! ### Boundary injectivity -/

/-- The loop `α = F ∘ semicircle` through a boundary value `p ∉ D`: its two halves form a Jordan curve contained in
`α([0, π])`. -/
theorem exists_jordan_loop {F : ℂ → ℂ} {D : Set ℂ} (hFc : ContinuousOn F Hbar)
    (hFi : InjOn F H) (hFD : MapsTo F H D) {m ρ : ℝ} (hρ : 0 < ρ) {p : ℂ} (hpD : p ∉ D)
    (h0 : F (semicircle m ρ 0) = p) (hπ : F (semicircle m ρ Real.pi) = p) :
    ∃ Γ' : Set ℂ, LQGMetric.JordanMap.IsJordanCurve Γ' ∧ p ∈ Γ' ∧ F (semicircle m ρ (Real.pi / 2)) ∈ Γ' ∧
      Γ' ⊆ (fun θ => F (semicircle m ρ θ)) '' Icc 0 Real.pi := by
  set α : ℝ → ℂ := fun θ => F (semicircle m ρ θ) with hα
  have hπ0 := Real.pi_pos
  have hαc : ContinuousOn α (Icc 0 Real.pi) :=
    hFc.comp (continuous_semicircle m ρ).continuousOn fun θ hθ => semicircle_mem_Hbar hρ.le hθ
  have hαp : ∀ θ ∈ Icc 0 Real.pi, α θ = p → θ = 0 ∨ θ = Real.pi := by
    intro θ hθ hθp
    rcases eq_or_lt_of_le hθ.1 with h | h
    · exact Or.inl h.symm
    rcases eq_or_lt_of_le hθ.2 with h' | h'
    · exact Or.inr h'
    exact absurd (hθp ▸ hFD (semicircle_mem_H hρ ⟨h, h'⟩)) hpD
  have hαi : ∀ θ ∈ Ioo 0 Real.pi, ∀ θ' ∈ Ioo 0 Real.pi, α θ = α θ' → θ = θ' := by
    intro θ hθ θ' hθ' h
    exact injOn_semicircle hρ (Ioo_subset_Icc_self hθ) (Ioo_subset_Icc_self hθ')
      (hFi (semicircle_mem_H hρ hθ) (semicircle_mem_H hρ hθ') h)
  -- the two halves
  set u : ℝ → ℂ := fun s => α (Real.pi / 2 * s) with hu
  set v : ℝ → ℂ := fun s => α (Real.pi - Real.pi / 2 * s) with hv
  have hmu : ∀ s ∈ Icc (0 : ℝ) 1, Real.pi / 2 * s ∈ Icc 0 Real.pi := fun s hs =>
    ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
  have hmv : ∀ s ∈ Icc (0 : ℝ) 1, Real.pi - Real.pi / 2 * s ∈ Icc 0 Real.pi := fun s hs =>
    ⟨by nlinarith [hs.2], by nlinarith [hs.1]⟩
  have huc : ContinuousOn u (Icc 0 1) := hαc.comp (by fun_prop) hmu
  have hvc : ContinuousOn v (Icc 0 1) := hαc.comp (by fun_prop) hmv
  -- equal values of `α` on `[0, π]`
  have hαeq : ∀ θ ∈ Icc 0 Real.pi, ∀ θ' ∈ Icc 0 Real.pi, α θ = α θ' →
      θ = θ' ∨ (α θ = p ∧ (θ = 0 ∨ θ = Real.pi) ∧ (θ' = 0 ∨ θ' = Real.pi)) := by
    intro θ hθ θ' hθ' h
    by_cases hp : α θ = p
    · exact Or.inr ⟨hp, hαp θ hθ hp, hαp θ' hθ' (h ▸ hp)⟩
    have hθo : θ ∈ Ioo 0 Real.pi := by
      refine ⟨lt_of_le_of_ne hθ.1 fun h0' => hp ?_, lt_of_le_of_ne hθ.2 fun hπ' => hp ?_⟩
      · rw [← h0']; exact h0
      · rw [hπ']; exact hπ
    have hθ'o : θ' ∈ Ioo 0 Real.pi := by
      have hp' : α θ' ≠ p := h ▸ hp
      refine ⟨lt_of_le_of_ne hθ'.1 fun h0' => hp' ?_, lt_of_le_of_ne hθ'.2 fun hπ' => hp' ?_⟩
      · rw [← h0']; exact h0
      · rw [hπ']; exact hπ
    exact Or.inl (hαi θ hθo θ' hθ'o h)
  have hui : InjOn u (Icc 0 1) := by
    intro s hs s' hs' h
    rcases hαeq _ (hmu s hs) _ (hmu s' hs') h with h1 | ⟨-, h2, h3⟩
    · have := mul_left_cancel₀ (by positivity : Real.pi / 2 ≠ 0) h1; exact this
    · rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;> nlinarith [hs.1, hs.2, hs'.1, hs'.2]
  have hvi : InjOn v (Icc 0 1) := by
    intro s hs s' hs' h
    rcases hαeq _ (hmv s hs) _ (hmv s' hs') h with h1 | ⟨-, h2, h3⟩
    · have h1' : Real.pi / 2 * s = Real.pi / 2 * s' := by linarith
      exact mul_left_cancel₀ (by positivity : Real.pi / 2 ≠ 0) h1'
    · rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;> nlinarith [hs.1, hs.2, hs'.1, hs'.2]
  have hu0 : u 0 = v 0 := by
    simp only [hu, hv, mul_zero, sub_zero]
    exact h0.trans hπ.symm
  have hu1 : u 1 = v 1 := by simp only [hu, hv, mul_one]; congr 1; ring
  have hint : u '' Icc 0 1 ∩ v '' Icc 0 1 ⊆ {u 0, u 1} := by
    rintro z ⟨⟨s, hs, rfl⟩, ⟨s', hs', hs'z⟩⟩
    rcases hαeq _ (hmu s hs) _ (hmv s' hs') hs'z.symm with h1 | ⟨h2, -, -⟩
    · right
      have : s = 1 := by nlinarith [hs.1, hs.2, hs'.1, hs'.2]
      subst this
      exact mem_singleton _
    · left
      simp only [hu, mul_zero] at h2 ⊢
      exact h2.trans h0.symm
  refine ⟨u '' Icc 0 1 ∪ v '' Icc 0 1, Sec7.isJordanCurve_image_union huc hvc hui hvi hu0 hu1 hint,
    Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, by simp only [hu, mul_zero]; exact h0⟩,
    Or.inl ⟨1, ⟨zero_le_one, le_rfl⟩, by simp only [hu, hα, mul_one]⟩, ?_⟩
  rintro z (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
  · exact ⟨_, hmu s hs, rfl⟩
  · exact ⟨_, hmv s hs, rfl⟩

/-- **Boundary injectivity** (the Jordan-domain part of §A.4.2). Let `D` be bounded by the crosscut `γ`, and let `F`
be continuous on `ℍ̄`, holomorphic and injective on `ℍ` with `F(ℍ) = D`, moving points by a bounded amount, with
real boundary values off `D`. Then `F` is injective on `ℝ`: it does not take the same value at two distinct real
points. -/
theorem IsCrosscutDomain.false_of_eq {D : Set ℂ} {γ : ℝ → ℂ} (hD : IsCrosscutDomain D γ) {F : ℂ → ℂ}
    (hFc : ContinuousOn F Hbar) (hFd : DifferentiableOn ℂ F H) (hFi : InjOn F H) (hFs : F '' H = D)
    (hFb : ∀ x : ℝ, F x ∉ D) (hFC : ∃ C : ℝ, ∀ w ∈ H, ‖F w - w‖ ≤ C) {v₁ v₂ : ℝ} (hv : v₁ < v₂)
    (heq : F v₁ = F v₂) : False := by
  set p := F v₁ with hp
  set m := (v₁ + v₂) / 2 with hm
  set ρ := (v₂ - v₁) / 2 with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; linarith
  have hFD : MapsTo F H D := fun w hw => hFs ▸ mem_image_of_mem F hw
  have hpD : p ∉ D := hFb v₁
  have hpcl : p ∈ closure D := by
    have hv₁ : ((v₁ : ℂ)) ∈ closure H := by rw [closure_H]; show (0 : ℝ) ≤ ((v₁ : ℂ)).im; simp
    have := (hFc (v₁ : ℂ) (by rw [← closure_H]; exact hv₁)).mono
      (show H ⊆ Hbar from fun z hz => (le_of_lt hz : (0 : ℝ) ≤ z.im)) |>.mem_closure_image hv₁
    rwa [hFs] at this
  have hpHbar : 0 ≤ p.im := by
    have : closure D ⊆ closure H := closure_mono hD.subset_H
    rw [closure_H] at this
    exact this hpcl
  have h0 : F (semicircle m ρ 0) = p := by
    rw [semicircle_zero, heq]; congr 2; rw [hm, hρdef]; ring
  have hπ : F (semicircle m ρ Real.pi) = p := by
    rw [semicircle_pi]; congr 2; rw [hm, hρdef]; ring
  obtain ⟨Γ', hΓ', hpΓ', -, hΓ'α⟩ := exists_jordan_loop hFc hFi hFD hρ hpD h0 hπ
  -- `Γ' ⊆ D ∪ {p}`, and a point of `F(ℍ)` on `Γ'` comes from the semicircle
  have hΓ'D : ∀ z ∈ Γ', z = p ∨ z ∈ D := by
    rintro z hz
    obtain ⟨θ, hθ, rfl⟩ := hΓ'α hz
    rcases eq_or_lt_of_le hθ.1 with h | h
    · left; rw [← h]; exact h0
    rcases eq_or_lt_of_le hθ.2 with h' | h'
    · left; rw [h']; exact hπ
    exact Or.inr (hFD (semicircle_mem_H hρ ⟨h, h'⟩))
  have hΓ'semi : ∀ w ∈ H, F w ∈ Γ' → ‖w - m‖ = ρ := by
    intro w hw hwΓ
    obtain ⟨θ, hθ, hθw⟩ := hΓ'α hwΓ
    rcases eq_or_lt_of_le hθ.1 with h | h
    · exact absurd (show F w ∈ D from hFD hw) (by rw [← hθw, ← h]; beta_reduce; rw [h0]; exact hpD)
    rcases eq_or_lt_of_le hθ.2 with h' | h'
    · exact absurd (show F w ∈ D from hFD hw) (by rw [← hθw, h']; beta_reduce; rw [hπ]; exact hpD)
    have := hFi (semicircle_mem_H hρ ⟨h, h'⟩) hw hθw
    rw [← this]; exact norm_semicircle_sub m ρ θ hρ.le
  have hΓ'H : ∀ z ∈ Γ', 0 ≤ z.im := by
    intro z hz
    rcases hΓ'D z hz with rfl | h
    · exact hpHbar
    · exact (hD.subset_H h).le
  obtain ⟨J, E, hJo, hEo, hJc, hEc, hJne, hJb, hJH, hJE, hunion, hJfr, R, hRE⟩ :=
    exists_inside_of_subset_Hbar hΓ' hΓ'H
  have hJΓ' : ∀ z ∈ J, z ∉ Γ' := fun z hz hzΓ => by
    have : z ∈ Γ'ᶜ := by rw [hunion]; exact Or.inl hz
    exact this hzΓ
  -- the inside of the crosscut
  obtain ⟨V, hVo, hVc, hVH, hVD, hHD, hVfr, hVΓ⟩ := hD.exists_inside
  -- `J ⊆ D`
  have hJD : J ⊆ D := by
    intro z hzJ
    by_contra hzD
    have hJV : (J ∩ V).Nonempty := by
      rcases hHD ⟨hJH hzJ, hzD⟩ with hzV | hzγ
      · exact ⟨z, hzJ, hzV⟩
      · have hzf : z ∈ frontier V := by
          rw [hVfr]; exact Or.inl (image_mono Ioo_subset_Icc_self hzγ)
        obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hJo z hzJ
        obtain ⟨w, hwV, hwd⟩ := Metric.mem_closure_iff.1 hzf.1 r hr
        exact ⟨w, hball (by rw [mem_ball, dist_comm]; exact hwd), hwV⟩
    have hVΓ' : V ⊆ Γ'ᶜ := by
      intro w hwV hwΓ
      rcases hΓ'D w hwΓ with rfl | h
      · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hVo _ hwV
        obtain ⟨d, hdD, hdd⟩ := Metric.mem_closure_iff.1 hpcl r hr
        exact Set.disjoint_left.1 hVD (hball (by rw [mem_ball, dist_comm]; exact hdd)) hdD
      · exact Set.disjoint_left.1 hVD hwV h
    have hVJ : V ⊆ J := hVc.subset_left_of_subset_union hJo hEo hJE (hunion ▸ hVΓ')
      (by obtain ⟨w, hwJ, hwV⟩ := hJV; exact ⟨w, hwV, hwJ⟩)
    have hclV : closure V ⊆ J ∪ Γ' := by
      calc closure V ⊆ closure J := closure_mono hVJ
        _ = J ∪ frontier J := by rw [closure_eq_self_union_frontier]
        _ = J ∪ Γ' := by rw [hJfr]
    -- a real point of `(γ 0, γ 1)` other than `p`
    obtain ⟨x, hx, hxp⟩ : ∃ x : ℝ, x ∈ Ioo (γ 0).re (γ 1).re ∧ (x : ℂ) ≠ p := by
      have hlt := hD.re_lt
      by_cases h : (((γ 0).re + (γ 1).re) / 2 : ℝ) = p.re
      · refine ⟨(3 * (γ 0).re + (γ 1).re) / 4, ⟨by linarith, by linarith⟩, fun hc => ?_⟩
        have := congrArg Complex.re hc
        rw [Complex.ofReal_re] at this
        linarith
      · refine ⟨((γ 0).re + (γ 1).re) / 2, ⟨by linarith, by linarith⟩, fun hc => h ?_⟩
        rw [← hc, Complex.ofReal_re]
    have hxV : (x : ℂ) ∈ closure V := by
      have : (x : ℂ) ∈ frontier V := by
        rw [hVfr]; exact mem_crosscutCurve_of_real hD.crosscut hD.re_lt (Ioo_subset_Icc_self hx)
      exact this.1
    rcases hclV hxV with h | h
    · have : 0 < ((x : ℂ)).im := hJH h
      simp at this
    · rcases hΓ'D _ h with h' | h'
      · exact hxp h'
      · have : 0 < ((x : ℂ)).im := hD.subset_H h'
        simp at this
  -- the image of the open half-disc lies in `J`
  set Δ := ball (m : ℂ) ρ ∩ H with hΔ
  have hΔΓ' : ∀ w ∈ Δ, F w ∉ Γ' := by
    intro w hw hwΓ
    have := hΓ'semi w hw.2 hwΓ
    have h2 : ‖w - m‖ < ρ := by rw [← dist_eq_norm]; exact hw.1
    linarith
  have hΔc : IsPreconnected (F '' Δ) := by
    have hconv : Convex ℝ Δ := (convex_ball _ ρ).inter
      (convex_halfSpace_gt (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0)
    exact hconv.isPreconnected.image F (hFd.continuousOn.mono inter_subset_right)
  obtain ⟨C, hC⟩ := hFC
  have hFΔJ : F '' Δ ⊆ J := by
    obtain ⟨j, hj⟩ := hJne
    obtain ⟨w, hwH, rfl⟩ := hFs.symm ▸ hJD hj
    by_cases hwΔ : w ∈ ball (m : ℂ) ρ
    · exact hΔc.subset_left_of_subset_union hJo hEo hJE
        (by rintro _ ⟨w', hw', rfl⟩; rw [← hunion]; exact hΔΓ' w' hw')
        ⟨F w, ⟨w, ⟨hwΔ, hwH⟩, rfl⟩, hj⟩
    exfalso
    -- the vertical ray above `w`
    set ray : Set ℂ := (fun t : ℝ => w + (t : ℂ) * I) '' Ici 0 with hray
    have hrayH : ∀ t : ℝ, 0 ≤ t → w + (t : ℂ) * I ∈ H := fun t ht => by
      show 0 < (w + (t : ℂ) * I).im
      simp only [add_im, mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_zero, mul_one, add_zero]
      linarith [show 0 < w.im from hwH]
    have hrayΓ : ∀ t : ℝ, 0 ≤ t → F (w + (t : ℂ) * I) ∉ Γ' := by
      intro t ht hΓ
      rcases eq_or_lt_of_le ht with h | h
      · rw [← h] at hΓ; simp only [ofReal_zero, zero_mul, add_zero] at hΓ; exact hJΓ' _ hj hΓ
      have h1 := hΓ'semi _ (hrayH t ht) hΓ
      have h2 : ρ ≤ ‖w - m‖ := by
        rw [← dist_eq_norm]; exact not_lt.1 hwΔ
      have hnorm : ‖w - m‖ ^ 2 < ‖w + (t : ℂ) * I - m‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
          Complex.normSq_apply]
        simp only [sub_re, add_re, mul_re, ofReal_re, I_re, ofReal_im, I_im, sub_im, add_im, mul_im]
        nlinarith [show 0 < w.im from hwH]
      nlinarith [norm_nonneg (w - m), norm_nonneg (w + (t : ℂ) * I - m)]
    have hrayc : IsPreconnected (F '' ray) :=
      ((convex_Ici (0 : ℝ)).isPreconnected.image _ (by fun_prop)).image F
        (hFd.continuousOn.mono (by rintro _ ⟨t, ht, rfl⟩; exact hrayH t ht))
    have hrayJ : F '' ray ⊆ J := hrayc.subset_left_of_subset_union hJo hEo hJE
      (by rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩; rw [← hunion]; exact hrayΓ t ht)
      ⟨F w, ⟨w, ⟨0, mem_Ici.2 le_rfl, by simp⟩, rfl⟩, hj⟩
    -- far along the ray, `F` leaves every bounded set
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC w hwH)
    have hR0 : ∀ z ∈ J, ‖z‖ < R := fun z hz => by
      by_contra h
      exact Set.disjoint_left.1 hJE hz (hRE z (not_lt.1 h))
    have hRpos : 0 ≤ R := le_trans (norm_nonneg _) (le_of_lt (hR0 _ hj))
    set t : ℝ := R + C + ‖w‖ + 1 with ht
    have ht0 : 0 ≤ t := by rw [ht]; linarith [norm_nonneg w]
    have hJt := hrayJ ⟨_, ⟨t, mem_Ici.2 ht0, rfl⟩, rfl⟩
    have h1 := hC _ (hrayH t ht0)
    have h2 : t - ‖w‖ ≤ ‖w + (t : ℂ) * I‖ := by
      have := norm_sub_norm_le ((t : ℂ) * I) (-w)
      rw [sub_neg_eq_add, add_comm] at this
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ht0, norm_neg] at this
      linarith
    have h3 : ‖w + (t : ℂ) * I‖ - C ≤ ‖F (w + (t : ℂ) * I)‖ := by
      have := norm_sub_norm_le (w + (t : ℂ) * I) (F (w + (t : ℂ) * I))
      rw [norm_sub_rev] at this
      linarith
    have := hR0 _ hJt
    linarith
  -- boundary values on `(v₁, v₂)` equal `p`
  have hbv : ∀ x : ℝ, x ∈ Ioo v₁ v₂ → F x = p := by
    intro x hx
    have hxcl : (x : ℂ) ∈ closure Δ := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      set δ := min (ε / 2) ((min (x - v₁) (v₂ - x)) / 2) with hδ
      have hδ0 : 0 < δ := lt_min (by linarith) (by have := lt_min (sub_pos.2 hx.1) (sub_pos.2 hx.2); linarith)
      refine ⟨(x : ℂ) + (δ : ℂ) * I, ⟨?_, ?_⟩, ?_⟩
      · rw [mem_ball, dist_eq_norm]
        have hxm : |x - m| + δ < ρ := by
          have hδ2 : δ ≤ (min (x - v₁) (v₂ - x)) / 2 := min_le_right _ _
          have hm1 : min (x - v₁) (v₂ - x) ≤ x - v₁ := min_le_left _ _
          have hm2 : min (x - v₁) (v₂ - x) ≤ v₂ - x := min_le_right _ _
          rcases abs_cases (x - m) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h, hρdef] <;> rw [hm] <;> linarith
        calc ‖(x : ℂ) + (δ : ℂ) * I - m‖ = ‖((x - m : ℝ) : ℂ) + (δ : ℂ) * I‖ := by push_cast; ring_nf
          _ ≤ ‖((x - m : ℝ) : ℂ)‖ + ‖(δ : ℂ) * I‖ := norm_add_le _ _
          _ = |x - m| + δ := by
            rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
              Real.norm_eq_abs, abs_of_pos hδ0]
          _ < ρ := hxm
      · show 0 < ((x : ℂ) + (δ : ℂ) * I).im
        simp [hδ0]
      · rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0]
        have := min_le_left (ε / 2) ((min (x - v₁) (v₂ - x)) / 2)
        linarith
    have hFx : F x ∈ closure (F '' Δ) :=
      ((hFc (x : ℂ) (show (0 : ℝ) ≤ ((x : ℂ)).im by simp)).mono
        (show Δ ⊆ Hbar from fun z hz => (le_of_lt hz.2 : (0 : ℝ) ≤ z.im))).mem_closure_image hxcl
    have hFxJ : F x ∈ J ∪ Γ' := by
      have : closure (F '' Δ) ⊆ J ∪ Γ' := by
        calc closure (F '' Δ) ⊆ closure J := closure_mono hFΔJ
          _ = J ∪ frontier J := by rw [closure_eq_self_union_frontier]
          _ = J ∪ Γ' := by rw [hJfr]
      exact this hFx
    rcases hFxJ with h | h
    · exact absurd (hJD h) (hFb x)
    · rcases hΓ'D _ h with h' | h'
      · exact h'
      · exact absurd h' (hFb x)
  -- reflection and the identity theorem
  set g : ℂ → ℂ := fun z => F z - p with hg
  have hgd : DifferentiableOn ℂ g (H ∩ ball (m : ℂ) ρ) :=
    (hFd.mono inter_subset_left).sub_const p
  have hgc : ContinuousOn g (Hbar ∩ ball (m : ℂ) ρ) := (hFc.mono inter_subset_left).sub continuousOn_const
  have hreal' : ∀ z ∈ ball (m : ℂ) ρ, z.im = 0 → (g z).im = 0 := by
    intro z hz hzim
    have hz' : z = (z.re : ℂ) := eq_ofReal_re_of_im_eq_zero hzim
    have hzre : z.re ∈ Ioo v₁ v₂ := by
      rw [mem_ball, dist_eq_norm, hz', ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_lt, hρdef, hm] at hz
      exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
    simp only [hg]
    rw [hz', hbv _ hzre, sub_self, zero_im]
  obtain ⟨G, hGd, hGeq, -⟩ := QuantumZipper.CA.exists_reflection_extension hgd hgc hreal'
  have hGa : AnalyticOnNhd ℂ G (ball (m : ℂ) ρ) := hGd.analyticOnNhd isOpen_ball
  have hfreq : ∃ᶠ z in 𝓝[≠] (m : ℂ), G z = 0 := by
    have hev : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), G ((m : ℂ) + (t : ℂ)) = 0 := by
      have hball : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), |t| < ρ := by
        have := (continuous_abs.tendsto (0 : ℝ)).eventually (gt_mem_nhds (show |(0 : ℝ)| < ρ by simpa))
        exact this
      filter_upwards [nhdsWithin_le_nhds hball] with t ht
      have hmem : (m : ℂ) + t ∈ Hbar ∩ ball (m : ℂ) ρ := by
        refine ⟨show (0 : ℝ) ≤ ((m : ℂ) + t).im by simp, ?_⟩
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
        exact ht
      rw [hGeq hmem]
      simp only [hg]
      have : (m : ℂ) + t = ((m + t : ℝ) : ℂ) := by push_cast; ring
      rw [this, hbv _ (by rw [abs_lt, hρdef] at ht; constructor <;> rw [hm] <;> linarith [ht.1, ht.2]),
        sub_self]
    have htend : Tendsto (fun t : ℝ => (m : ℂ) + t) (𝓝[≠] 0) (𝓝[≠] (m : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun t : ℝ => (m : ℂ) + t) (𝓝 0) (𝓝 ((m : ℂ) + ((0 : ℝ) : ℂ))) :=
          tendsto_const_nhds.add (Complex.continuous_ofReal.tendsto 0)
        simp only [ofReal_zero, add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simp only [mem_compl_iff, mem_singleton_iff, add_eq_left, ofReal_eq_zero]
        exact ht
    exact htend.frequently hev.frequently
  have hG0 := hGa.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_ball _ ρ).isPreconnected
    (mem_ball_self hρ) hfreq
  -- `F` is constant on the half-disc: contradiction with injectivity
  have hFp : ∀ w ∈ Δ, F w = p := by
    intro w hw
    have h1 := hG0 hw.1
    rw [hGeq ⟨(show (0 : ℝ) < w.im from hw.2).le, hw.1⟩] at h1
    simpa [hg, sub_eq_zero] using h1
  set w₁ : ℂ := (m : ℂ) + ((ρ / 2 : ℝ) : ℂ) * I with hw₁
  set w₂ : ℂ := (m : ℂ) + ((ρ / 3 : ℝ) : ℂ) * I with hw₂
  have hwΔ : ∀ c : ℝ, 0 < c → c < ρ → (m : ℂ) + (c : ℂ) * I ∈ Δ := by
    intro c hc hcρ
    refine ⟨?_, show 0 < ((m : ℂ) + (c : ℂ) * I).im by simp [hc]⟩
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hc]
    exact hcρ
  have h1 := hwΔ (ρ / 2) (by linarith) (by linarith)
  have h2 := hwΔ (ρ / 3) (by linarith) (by linarith)
  have := hFi h1.2 h2.2 ((hFp _ h1).trans (hFp _ h2).symm)
  have := congrArg Complex.im this
  simp at this
  linarith

end InteractingSLE.ZhanGT4
