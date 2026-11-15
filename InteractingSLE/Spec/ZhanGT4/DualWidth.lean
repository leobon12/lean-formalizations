/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualCondMirror

/-!
# Width independence: the image chain on `[0, x]` does not depend on the horizon

Packet PROVE-ZHAN-GT4-A18. Source: Astra, *Follow-up proofs*, §A.1.4–A.1.5 (`source/external/AstraIG1/
ig1_followup_proofs.txt` L401–L406, L409–L425, R38): "its restriction to each stopped rectangle has density
`M(S₁ᵐ, S₂ᵐ)`" and "for each fixed enclosure pair, all sufficiently late couplings have exactly the same joint law of
its two recorded stopped histories, namely the density from (D6)". The density `M(S₁ᵐ, S₂ᵐ)` is a function of the two
stopped paths alone; in Lean the image data of a frozen-hull view are *selected* up to a staircase width that depends
on the whole family of rectangles. This file proves that the selection does not matter:

* `OwnData.eqOn_clock`, `OwnData.W'_clock_eq`, `OwnData.eqOn_imgDriver`: two image chains (`OwnData`) of the same
  growing driver, frozen hull and chart, with horizons `T`, `T'`, have the same clock on `[0, min T T']` and the same
  image driver on `[0, a(min T T')]` (the capacity rate `a' = (R')²` and the boundary value `W'(a t) = lim R` are
  intrinsic to the mapping-out function `R` of `g_t(A)`);
* **`OwnData.ell_congr`**: hence the frozen-hull log-density `ℓ(x, w)` (`FrzData.ell`) is the same for both;
* **`TwoEncl.sEll_congr`**, **`TwoEncl.tEll_congr`**: for two families of protected rectangles of the same pair of
  paths, the canonical `s`-view (resp. `t`-view) log-densities agree at every point under a rectangle of each family;
* **`DualHyp.rectDens_congr`**, `DualHyp.condMeasure₁_congr`, `DualHyp.condMeasure₂_congr`: the rectangle density and
  the conditional laws of a rectangle are the same for every family containing that rectangle.
-/

set_option autoImplicit false

noncomputable section

open Finset Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull drive)

/-! ### Two image chains of the same frozen-hull configuration -/

namespace OwnData

variable {W : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T T' : ℝ} {a a' W' W'' : ℝ → ℝ}

/-- The common capacity rate at time `t`: a mapping-out function `R` of `g_t(A)`, a holomorphic extension `Rext`
across `W t`, and `HasDerivWithinAt` of both clocks with the rate `(Rext'(W t))²`. -/
theorem exists_common_rate (h : OwnData W A φ T a W') (h' : OwnData W A φ T' a' W'') {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) (ht' : t ∈ Icc (0 : ℝ) T') :
    ∃ c : ℝ, HasDerivWithinAt a c (Icc 0 T) t ∧ HasDerivWithinAt a' c (Icc 0 T') t ∧
      W' (a t) = W'' (a' t) := by
  have hR := ConformalImage.isMapOut_mapOut (h.isHPHull_E ht)
  obtain ⟨-, hlim, ⟨δ, hδ, Rext, hd, he⟩, hrate⟩ := h.rate t ht _ hR
  obtain ⟨-, hlim', -, hrate'⟩ := h'.rate t ht' _ hR
  refine ⟨(deriv Rext (W t)).re ^ 2, (hrate δ hδ Rext hd he).2.2, (hrate' δ hδ Rext hd he).2.2, ?_⟩
  have hne : (𝓝[H] ((W t : ℝ) : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (Complex.ofReal_im _)
  exact Complex.ofReal_injective (tendsto_nhds_unique hlim hlim')

/-- **The clocks agree on `[0, min T T']`.** -/
theorem eqOn_clock (h : OwnData W A φ T a W') (h' : OwnData W A φ T' a' W'') : EqOn a a' (Icc 0 (min T T')) := by
  have hm : 0 ≤ min T T' := le_min h.pos.le h'.pos.le
  have hsub : Icc (0 : ℝ) (min T T') ⊆ Icc 0 T := Icc_subset_Icc_right (min_le_left _ _)
  have hsub' : Icc (0 : ℝ) (min T T') ⊆ Icc 0 T' := Icc_subset_Icc_right (min_le_right _ _)
  have hcont : ContinuousOn (fun t => a t - a' t) (Icc 0 (min T T')) :=
    (h.contA.mono hsub).sub (h'.contA.mono hsub')
  have hderiv : ∀ x ∈ Ico (0 : ℝ) (min T T'), HasDerivWithinAt (fun t => a t - a' t) 0 (Ici x) x := by
    intro x hx
    have hxT : x ∈ Ico (0 : ℝ) T := ⟨hx.1, hx.2.trans_le (min_le_left _ _)⟩
    have hxT' : x ∈ Ico (0 : ℝ) T' := ⟨hx.1, hx.2.trans_le (min_le_right _ _)⟩
    obtain ⟨c, hc, hc', -⟩ := exists_common_rate h h' (Ico_subset_Icc_self hxT) (Ico_subset_Icc_self hxT')
    have h1 := hc.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hxT)
    have h2 := hc'.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hxT')
    have h3 := h1.sub h2
    rw [sub_self] at h3
    exact h3
  intro x hx
  have := constant_of_has_deriv_right_zero hcont hderiv x hx
  rw [h.a0, h'.a0, sub_zero] at this
  exact sub_eq_zero.1 this

/-- **The image drivers agree along the clock**: `W'(a t) = W''(a' t)` on `[0, min T T']`. -/
theorem W'_clock_eq (h : OwnData W A φ T a W') (h' : OwnData W A φ T' a' W'') {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (min T T')) : W' (a t) = W'' (a' t) := by
  obtain ⟨-, -, -, he⟩ := exists_common_rate h h' ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
    ⟨ht.1, ht.2.trans (min_le_right _ _)⟩
  exact he

/-- **The image drivers agree on `[0, a x]`** for `x ≤ min T T'`. -/
theorem eqOn_imgDriver (h : OwnData W A φ T a W') (h' : OwnData W A φ T' a' W'') {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (min T T')) : EqOn W' W'' (Icc 0 (a x)) := by
  intro s hs
  have hxT : x ∈ Icc (0 : ℝ) T := ⟨hx.1, hx.2.trans (min_le_left _ _)⟩
  have hc : ContinuousOn a (Icc 0 x) := h.contA.mono (Icc_subset_Icc_right hxT.2)
  obtain ⟨u, hu, hus⟩ := intermediate_value_Icc hx.1 hc (by rw [h.a0]; exact hs)
  have huT : u ∈ Icc (0 : ℝ) (min T T') := ⟨hu.1, hu.2.trans hx.2⟩
  rw [← hus, W'_clock_eq h h' huT, eqOn_clock h h' huT]

/-- **The canonical own-time maps agree** at every time `u ≤ min T T'`. -/
theorem ownExt_congr (h : OwnData W A φ T a W') (h' : OwnData W A φ T' a' W'') {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) (min T T')) : ownExt W W' a φ u = ownExt W W'' a' φ u := by
  have hfwd : ∀ z, fwdMap W' (a u) z = fwdMap W'' (a' u) z := fun z => by
    rw [← eqOn_clock h h' hu]
    exact Ito.fwdMap_congr_of_eqOn_of_le (eqOn_imgDriver h h' hu) le_rfl
  have hown : ownMap W W' a φ u = ownMap W W'' a' φ u := by
    funext z
    unfold ownMap
    rw [hfwd, W'_clock_eq h h' hu]
  funext z
  unfold ownExt
  rw [hown]

/-- **The frozen-hull log-density does not depend on the horizon of the image chain** (width independence). -/
theorem ell_congr {n : ℕ} (h : OwnData W A φ T a W') (h' : OwnData W A φ T' a' W'') {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (min T T')) (κ : ℝ) (r : Fin n → ℝ) (ζ₀ : ℝ) (ζ : Fin n → ℝ) (w : ℝ) :
    (⟨W, W', a, φ, κ, r, ζ₀, ζ⟩ : FrzData n).ell x w = (⟨W, W'', a', φ, κ, r, ζ₀, ζ⟩ : FrzData n).ell x w := by
  have hext := ownExt_congr h h' hx
  have hfwd : fwdMap W' (a x) = fwdMap W'' (a' x) := by
    funext z
    rw [← eqOn_clock h h' hx]
    exact Ito.fwdMap_congr_of_eqOn_of_le (eqOn_imgDriver h h' hx) le_rfl
  have himg : ∀ c : ℝ, frzImg W' a c x = frzImg W'' a' c x := fun c => by
    unfold frzImg; rw [hfwd, W'_clock_eq h h' hx]
  have himgD : ∀ c : ℝ, frzImgD W' a c x = frzImgD W'' a' c x := fun c => by
    unfold frzImgD; rw [hfwd]
  have hlogF : frzLogF W W' a φ x = frzLogF W W'' a' φ x := by
    unfold frzLogF
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le hx.1] at hu
    have hu' : u ∈ Icc (0 : ℝ) (min T T') := ⟨hu.1, hu.2.trans hx.2⟩
    unfold frzRate frzA
    rw [ownExt_congr h h' hu']
  unfold FrzData.ell FrzData.LT FrzData.LS FrzData.F FrzData.A20 FrzData.A21 FrzData.B0 FrzData.B1
  simp only [hext, himg, himgD, hlogF]

end OwnData

/-! ### Two families of protected rectangles of the same pair of paths -/

namespace TwoEncl

variable {ι ι' : Type*} [Fintype ι] [Fintype ι'] {n : ℕ} {W₁ W₂ : ℝ → ℝ} {S₁ S₂ : ι → ℝ} {S₁' S₂' : ι' → ℝ}
  {H₁ H₂ : ι → Set ℂ} {H₁' H₂' : ι' → Set ℂ} {δ q d : ι → ℝ} {δ' q' d' : ι' → ℝ} {p : Fin n → ℝ} {Tm Tm' : ℝ}

/-- **Width independence of the `s`-view**: the canonical `s`-view log-density `ℓ(x, y)` (curve `1` at time `x`,
curve `2`'s hull of height `y` frozen) is the same for two families of protected rectangles at every point under a
rectangle of each family. -/
theorem sEll_congr (h : TwoEncl W₁ W₂ S₁ S₂ H₁ H₂ δ q d p Tm) (h' : TwoEncl W₁ W₂ S₁' S₂' H₁' H₂' δ' q' d' p Tm')
    (κ : ℝ) (r : Fin n → ℝ) {i : ι} {i' : ι'} {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) (S₁ i)) (hx' : x ≤ S₁' i')
    (hy : y ∈ Icc (0 : ℝ) (S₂ i)) (hy' : y ≤ S₂' i') :
    sEll κ r W₁ W₂ (sSelA W₁ W₂ S₁ S₂) (sSelW W₁ W₂ S₁ S₂) p x y =
      sEll κ r W₁ W₂ (sSelA W₁ W₂ S₁' S₂') (sSelW W₁ W₂ S₁' S₂') p x y := by
  obtain ⟨hw, hown, -, -⟩ := h.sView_encl i hy
  obtain ⟨hw', hown', -, -⟩ := h'.sView_encl i' ⟨hy.1, hy'⟩
  exact OwnData.ell_congr hown hown' ⟨hx.1, le_min (hx.2.trans hw) (hx'.trans hw')⟩ κ r (W₂ y) (frzMarks W₂ p y)
    (W₁ x)

/-- **Width independence of the `t`-view**: the canonical `t`-view log-density `ℓ_t(x, y)` (curve `2` at time `y`,
curve `1`'s hull of height `x` frozen, translated coordinates) is the same for two families of protected rectangles at
every point under a rectangle of each family. -/
theorem tEll_congr (h : TwoEncl W₁ W₂ S₁ S₂ H₁ H₂ δ q d p Tm) (h' : TwoEncl W₁ W₂ S₁' S₂' H₁' H₂' δ' q' d' p Tm')
    (κ : ℝ) (r : Fin n → ℝ) {i : ι} {i' : ι'} {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) (S₁ i)) (hx' : x ≤ S₁' i')
    (hy : y ∈ Icc (0 : ℝ) (S₂ i)) (hy' : y ≤ S₂' i') :
    tEll κ r W₁ W₂ (tSelA W₁ W₂ S₁ S₂) (tSelW W₁ W₂ S₁ S₂) p x y =
      tEll κ r W₁ W₂ (tSelA W₁ W₂ S₁' S₂') (tSelW W₁ W₂ S₁' S₂') p x y := by
  obtain ⟨hw, hown, -, -⟩ := h.tView_encl i hx
  obtain ⟨hw', hown', -, -⟩ := h'.tView_encl i' ⟨hx.1, hx'⟩
  exact OwnData.ell_congr hown hown' ⟨hy.1, le_min (hy.2.trans hw) (hy'.trans hw')⟩ (16 / κ)
    (fun m => -(κ / 4) * r m) (W₁ x - W₂ 0) (frzMarks (fun u => W₁ u - W₂ 0) (fun m => p m - W₂ 0) x)
    (W₂ y - W₂ 0)

end TwoEncl

/-! ### The rectangle density and the conditional laws of one rectangle -/

section Dual

variable {Ω₁ Ω₂ : Type*} {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂} {ι ι' : Type*} [Fintype ι]
  [Fintype ι'] {n : ℕ} {κ : ℝ} {P₁ : Measure Ω₁} {𝓕₁ : Filtration ℝ≥0 mΩ₁} {B₁ : ℝ≥0 → Ω₁ → ℝ}
  {P₂ : Measure Ω₂} {𝓕₂ : Filtration ℝ≥0 mΩ₂} {B₂ : ℝ≥0 → Ω₂ → ℝ} {x₂ : ℝ} {p : Fin n → ℝ}
  {H₁ H₂ : ι → Set ℂ} {δ q d : ι → ℝ} {Tm : ℝ} {S₁ : ι → Ω₁ → ℝ≥0} {S₂ : ι → Ω₂ → ℝ≥0}
  {H₁' H₂' : ι' → Set ℂ} {δ' q' d' : ι' → ℝ} {Tm' : ℝ} {S₁' : ι' → Ω₁ → ℝ≥0} {S₂' : ι' → Ω₂ → ℝ≥0}

namespace DualHyp

variable (h : DualHyp κ P₁ 𝓕₁ B₁ P₂ 𝓕₂ B₂ x₂ H₁ H₂ δ q d p Tm S₁ S₂)
  (h' : DualHyp κ P₁ 𝓕₁ B₁ P₂ 𝓕₂ B₂ x₂ H₁' H₂' δ' q' d' p Tm' S₁' S₂')
include h h'

/-- Width independence of `pairS` under a common rectangle. -/
theorem pairS_congr (rr : Fin n → ℝ) {i : ι} {i' : ι'} (ω₁ : Ω₁) (ω₂ : Ω₂) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (S₁ i ω₁)) (hx' : x ≤ S₁' i' ω₁) (hy : y ∈ Icc (0 : ℝ) (S₂ i ω₂)) (hy' : y ≤ S₂' i' ω₂) :
    pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ x y = pairS κ rr p B₁ B₂ x₂ S₁' S₂' ω₁ ω₂ x y :=
  (h.twoEncl ω₁ ω₂).sEll_congr (h'.twoEncl ω₁ ω₂) κ rr hx hx' hy hy'

/-- Width independence of `pairT` under a common rectangle. -/
theorem pairT_congr (rr : Fin n → ℝ) {i : ι} {i' : ι'} (ω₁ : Ω₁) (ω₂ : Ω₂) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (S₁ i ω₁)) (hx' : x ≤ S₁' i' ω₁) (hy : y ∈ Icc (0 : ℝ) (S₂ i ω₂)) (hy' : y ≤ S₂' i' ω₂) :
    pairT κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ x y = pairT κ rr p B₁ B₂ x₂ S₁' S₂' ω₁ ω₂ x y :=
  (h.twoEncl ω₁ ω₂).tEll_congr (h'.twoEncl ω₁ ω₂) κ rr hx hx' hy hy'

/-- **The rectangle density is the same for every family containing the rectangle** (§A.1.5, "all sufficiently late
couplings have exactly the same joint law of its two recorded stopped histories, namely the density from (D6)"). -/
theorem rectDens_congr (rr : Fin n → ℝ) {i : ι} {i' : ι'} (h₁ : S₁' i' = S₁ i) (h₂ : S₂' i' = S₂ i)
    (ω : Ω₁ × Ω₂) : rectDens κ rr p B₁ B₂ x₂ S₁' S₂' i' ω = rectDens κ rr p B₁ B₂ x₂ S₁ S₂ i ω := by
  have hx : ∀ x : ℝ, x ∈ Icc (0 : ℝ) (S₁ i ω.1) → x ≤ S₁' i' ω.1 := fun x hx => by rw [h₁]; exact hx.2
  have hy : ∀ y : ℝ, y ∈ Icc (0 : ℝ) (S₂ i ω.2) → y ≤ S₂' i' ω.2 := fun y hy => by rw [h₂]; exact hy.2
  have hS : (S₁ i ω.1 : ℝ) ∈ Icc (0 : ℝ) (S₁ i ω.1) := ⟨(S₁ i ω.1).coe_nonneg, le_rfl⟩
  have hT : (S₂ i ω.2 : ℝ) ∈ Icc (0 : ℝ) (S₂ i ω.2) := ⟨(S₂ i ω.2).coe_nonneg, le_rfl⟩
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (S₁ i ω.1) := ⟨le_rfl, (S₁ i ω.1).coe_nonneg⟩
  have h0' : (0 : ℝ) ∈ Icc (0 : ℝ) (S₂ i ω.2) := ⟨le_rfl, (S₂ i ω.2).coe_nonneg⟩
  rw [rectDens_eq, rectDens_eq, h₁, h₂,
    h.pairS_congr h' rr ω.1 ω.2 hS (hx _ hS) hT (hy _ hT), h.pairS_congr h' rr ω.1 ω.2 h0 (hx _ h0) hT (hy _ hT),
    h.pairT_congr h' rr ω.1 ω.2 h0 (hx _ h0) hT (hy _ hT), h.pairT_congr h' rr ω.1 ω.2 h0 (hx _ h0) h0' (hy _ h0')]

/-- **The conditional law of curve `1` given the curve-`2` prefix is the same for every family containing the
rectangle.** -/
theorem condMeasure₁_congr (rr : Fin n → ℝ) {i : ι} {i' : ι'} (h₁ : S₁' i' = S₁ i) (h₂ : S₂' i' = S₂ i) (ω₂ : Ω₂) :
    condMeasure₁ κ rr p P₁ B₁ B₂ x₂ S₁' S₂' i' ω₂ = condMeasure₁ κ rr p P₁ B₁ B₂ x₂ S₁ S₂ i ω₂ := by
  unfold condMeasure₁
  congr 1
  funext ω₁
  have hS : (S₁ i ω₁ : ℝ) ∈ Icc (0 : ℝ) (S₁ i ω₁) := ⟨(S₁ i ω₁).coe_nonneg, le_rfl⟩
  have hT : (S₂ i ω₂ : ℝ) ∈ Icc (0 : ℝ) (S₂ i ω₂) := ⟨(S₂ i ω₂).coe_nonneg, le_rfl⟩
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (S₁ i ω₁) := ⟨le_rfl, (S₁ i ω₁).coe_nonneg⟩
  have hx : ∀ x : ℝ, x ∈ Icc (0 : ℝ) (S₁ i ω₁) → x ≤ S₁' i' ω₁ := fun x hx => by rw [h₁]; exact hx.2
  have hy : (S₂ i ω₂ : ℝ) ≤ S₂' i' ω₂ := by rw [h₂]
  rw [h₁, h₂, h.pairS_congr h' rr ω₁ ω₂ hS (hx _ hS) hT hy, h.pairS_congr h' rr ω₁ ω₂ h0 (hx _ h0) hT hy]

/-- **The conditional law of curve `2` given the curve-`1` prefix is the same for every family containing the
rectangle.** -/
theorem condMeasure₂_congr (rr : Fin n → ℝ) {i : ι} {i' : ι'} (h₁ : S₁' i' = S₁ i) (h₂ : S₂' i' = S₂ i) (ω₁ : Ω₁) :
    condMeasure₂ κ rr p P₂ B₁ B₂ x₂ S₁' S₂' i' ω₁ = condMeasure₂ κ rr p P₂ B₁ B₂ x₂ S₁ S₂ i ω₁ := by
  unfold condMeasure₂
  congr 1
  funext ω₂
  have hS : (S₁ i ω₁ : ℝ) ∈ Icc (0 : ℝ) (S₁ i ω₁) := ⟨(S₁ i ω₁).coe_nonneg, le_rfl⟩
  have hT : (S₂ i ω₂ : ℝ) ∈ Icc (0 : ℝ) (S₂ i ω₂) := ⟨(S₂ i ω₂).coe_nonneg, le_rfl⟩
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (S₂ i ω₂) := ⟨le_rfl, (S₂ i ω₂).coe_nonneg⟩
  have hx : (S₁ i ω₁ : ℝ) ≤ S₁' i' ω₁ := by rw [h₁]
  have hy : ∀ y : ℝ, y ∈ Icc (0 : ℝ) (S₂ i ω₂) → y ≤ S₂' i' ω₂ := fun y hy => by rw [h₂]; exact hy.2
  rw [h₁, h₂, h.pairT_congr h' rr ω₁ ω₂ hS hx hT (hy _ hT), h.pairT_congr h' rr ω₁ ω₂ hS hx h0 (hy _ h0)]

end DualHyp

end Dual

end InteractingSLE.ZhanGT4
