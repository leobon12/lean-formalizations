/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.closedLeftSide
import InteractingSLE.Frozen.Spec.IsProperCompletion
import InteractingSLE.Frozen.Spec.HasOrderedProperCompletions
import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Supplement §7.8: interiorization while fixing the stopped tangle (Lemma G10)

Packet PROVE-SUPP7 (specification supplement §7.8, `source/spec/p481-528.md`, anchor `id-G10`, p. 502).

**Lemma G10.** Let `P₁, P₂` be compact stopped prefixes of two ordered proper reference curves in the closed
upper half-plane. There are ordered proper extensions of these same stopped prefixes whose only remaining real
points are the real points already in `P₁ ∪ P₂` (in particular the two seeds); if the complete curves do not
visit each other's seeds, neither do the extensions.

*Proof (source).* With `d(x) = min{1, dist((x, 0), P₁ ∪ P₂)/3}`, the map `Φ(x, y) = (x, F_x(y))`,
`F_x(y) = y` for `y ≥ d`, `y/2 + d/2` for `0 ≤ y ≤ d`, `y + d/2` for `y < 0`, is a plane homeomorphism moving points
by at most `1/2`, fixing `P₁ ∪ P₂` and the lower vertical closing rays at the (real) seeds; apply it to the two
complete curves.

In Lean, `F_x(y) = y + interiorShift (d x) y` with `interiorShift δ y = min (δ/2) (max 0 ((δ − y)/2))`, whose inverse
is `u ↦ u − interiorShiftInv δ u`, `interiorShiftInv δ u = min (δ/2) (max 0 (δ − u))` (`interiorize`,
`interiorizeHomeomorph`). The "orientation-preserving" step of the source is made concrete for the frozen order
predicate `closedLeftSide` (W0): `Φ` maps `seedRayClosure γ` onto `seedRayClosure (Φ ∘ γ)` and the component of the
base point `γ 0 − 1 − i` onto the component of the same base point (`image_closedLeftSide`).

* `exists_interiorized_completions` : **Lemma G10** for any two ordered proper completions with real seeds;
* `exists_interiorized_completions_of_seeds` : the source's form, including seed avoidance.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal

namespace InteractingSLE

namespace Supp7

/-! ### The vertical shift and its inverse -/

/-- The vertical shift of G10: `F(δ, y) = y + interiorShift δ y` equals `y` for `y ≥ δ`, `y/2 + δ/2` for
`0 ≤ y ≤ δ`, and `y + δ/2` for `y < 0`. -/
def interiorShift (δ y : ℝ) : ℝ := min (δ / 2) (max 0 ((δ - y) / 2))

/-- The inverse shift: `G(δ, u) = u − interiorShiftInv δ u` equals `u` for `u ≥ δ`, `2u − δ` for
`δ/2 ≤ u ≤ δ`, and `u − δ/2` for `u < δ/2`. -/
def interiorShiftInv (δ u : ℝ) : ℝ := min (δ / 2) (max 0 (δ - u))

theorem interiorShift_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (y : ℝ) : 0 ≤ interiorShift δ y :=
  le_min (by linarith) (le_max_left _ _)

theorem interiorShift_le {δ : ℝ} (y : ℝ) : interiorShift δ y ≤ δ / 2 := min_le_left _ _

theorem interiorShift_eq_zero_of_le {δ y : ℝ} (hδ : 0 ≤ δ) (h : δ ≤ y) : interiorShift δ y = 0 := by
  have : max 0 ((δ - y) / 2) = 0 := max_eq_left (by linarith)
  rw [interiorShift, this, min_eq_right (by linarith)]

theorem interiorShift_zero (y : ℝ) : interiorShift 0 y = 0 := by
  rw [interiorShift, zero_div, min_eq_left (le_max_left _ _)]

theorem interiorShiftInv_zero (u : ℝ) : interiorShiftInv 0 u = 0 := by
  rw [interiorShiftInv, zero_div, min_eq_left (le_max_left _ _)]

/-- `G(δ, F(δ, y)) = y`. -/
theorem interiorShiftInv_add_interiorShift {δ : ℝ} (hδ : 0 ≤ δ) (y : ℝ) :
    interiorShiftInv δ (y + interiorShift δ y) = interiorShift δ y := by
  simp only [interiorShift, interiorShiftInv, min_def, max_def]
  split_ifs <;> linarith

/-- `F(δ, G(δ, u)) = u`. -/
theorem interiorShift_sub_interiorShiftInv {δ : ℝ} (hδ : 0 ≤ δ) (u : ℝ) :
    interiorShift δ (u - interiorShiftInv δ u) = interiorShiftInv δ u := by
  simp only [interiorShift, interiorShiftInv, min_def, max_def]
  split_ifs <;> linarith

/-- For `y ≥ 0`, `F(δ, y) ≥ (y + δ)/2`. -/
theorem add_interiorShift_ge {δ y : ℝ} (hδ : 0 ≤ δ) (hy : 0 ≤ y) :
    (y + δ) / 2 ≤ y + interiorShift δ y := by
  simp only [interiorShift, min_def, max_def]
  split_ifs <;> linarith

theorem continuous_interiorShift : Continuous fun p : ℝ × ℝ => interiorShift p.1 p.2 := by
  unfold interiorShift; fun_prop

theorem continuous_interiorShiftInv : Continuous fun p : ℝ × ℝ => interiorShiftInv p.1 p.2 := by
  unfold interiorShiftInv; fun_prop

/-! ### The height function `d` -/

/-- The height `d(x) = min{1, dist((x, 0), P)/3}` of G10. -/
def interiorHeight (P : Set ℂ) (x : ℝ) : ℝ := min 1 (infDist (x : ℂ) P / 3)

theorem interiorHeight_nonneg (P : Set ℂ) (x : ℝ) : 0 ≤ interiorHeight P x :=
  le_min zero_le_one (div_nonneg infDist_nonneg (by norm_num))

theorem interiorHeight_le_one (P : Set ℂ) (x : ℝ) : interiorHeight P x ≤ 1 := min_le_left _ _

theorem continuous_interiorHeight (P : Set ℂ) : Continuous (interiorHeight P) := by
  unfold interiorHeight
  exact continuous_const.min ((continuous_infDist_pt P).comp continuous_ofReal |>.div_const _)

/-- At the abscissa of a real point of `P`, `d = 0`. -/
theorem interiorHeight_eq_zero_of_mem {P : Set ℂ} {x : ℝ} (hx : (x : ℂ) ∈ P) : interiorHeight P x = 0 := by
  rw [interiorHeight, infDist_zero_of_mem hx, zero_div, min_eq_right zero_le_one]

/-- For `z ∈ P`, `3 d(Re z) ≤ |Im z|`. -/
theorem three_mul_interiorHeight_le {P : Set ℂ} {z : ℂ} (hz : z ∈ P) :
    3 * interiorHeight P z.re ≤ |z.im| := by
  have h1 : infDist (z.re : ℂ) P ≤ dist (z.re : ℂ) z := infDist_le_dist_of_mem hz
  have h2 : dist (z.re : ℂ) z = |z.im| := by
    rw [dist_eq_re_im, ofReal_re, ofReal_im, sub_self, zero_sub, neg_sq, ← sq_abs (z.im),
      show (0 : ℝ) ^ 2 + |z.im| ^ 2 = |z.im| ^ 2 by ring, Real.sqrt_sq (abs_nonneg _)]
  have h3 : interiorHeight P z.re ≤ infDist (z.re : ℂ) P / 3 := min_le_right _ _
  linarith

/-! ### The interiorization map -/

/-- The interiorization map `Φ(x, y) = (x, F_x(y))` of G10, for the compact stopped set `P`. -/
def interiorize (P : Set ℂ) (z : ℂ) : ℂ := z + (interiorShift (interiorHeight P z.re) z.im : ℂ) * I

/-- The inverse of `interiorize`. -/
def interiorizeInv (P : Set ℂ) (z : ℂ) : ℂ :=
  z - (interiorShiftInv (interiorHeight P z.re) z.im : ℂ) * I

@[simp] theorem interiorize_re (P : Set ℂ) (z : ℂ) : (interiorize P z).re = z.re := by
  simp [interiorize]

@[simp] theorem interiorize_im (P : Set ℂ) (z : ℂ) :
    (interiorize P z).im = z.im + interiorShift (interiorHeight P z.re) z.im := by
  simp [interiorize]

@[simp] theorem interiorizeInv_re (P : Set ℂ) (z : ℂ) : (interiorizeInv P z).re = z.re := by
  simp [interiorizeInv]

@[simp] theorem interiorizeInv_im (P : Set ℂ) (z : ℂ) :
    (interiorizeInv P z).im = z.im - interiorShiftInv (interiorHeight P z.re) z.im := by
  simp [interiorizeInv]

theorem interiorizeInv_interiorize (P : Set ℂ) (z : ℂ) : interiorizeInv P (interiorize P z) = z := by
  apply Complex.ext
  · simp
  · simp only [interiorizeInv_im, interiorize_im, interiorize_re]
    rw [interiorShiftInv_add_interiorShift (interiorHeight_nonneg P _)]
    ring

theorem interiorize_interiorizeInv (P : Set ℂ) (z : ℂ) : interiorize P (interiorizeInv P z) = z := by
  apply Complex.ext
  · simp
  · simp only [interiorize_im, interiorizeInv_im, interiorizeInv_re]
    rw [interiorShift_sub_interiorShiftInv (interiorHeight_nonneg P _)]
    ring

theorem continuous_interiorize (P : Set ℂ) : Continuous (interiorize P) := by
  unfold interiorize
  have h : Continuous fun z : ℂ => interiorShift (interiorHeight P z.re) z.im :=
    continuous_interiorShift.comp
      (((continuous_interiorHeight P).comp continuous_re).prodMk continuous_im)
  fun_prop

theorem continuous_interiorizeInv (P : Set ℂ) : Continuous (interiorizeInv P) := by
  unfold interiorizeInv
  have h : Continuous fun z : ℂ => interiorShiftInv (interiorHeight P z.re) z.im :=
    continuous_interiorShiftInv.comp
      (((continuous_interiorHeight P).comp continuous_re).prodMk continuous_im)
  fun_prop

/-- The interiorization map as a homeomorphism of the plane. -/
def interiorizeHomeomorph (P : Set ℂ) : ℂ ≃ₜ ℂ where
  toFun := interiorize P
  invFun := interiorizeInv P
  left_inv := interiorizeInv_interiorize P
  right_inv := interiorize_interiorizeInv P
  continuous_toFun := continuous_interiorize P
  continuous_invFun := continuous_interiorizeInv P

@[simp] theorem interiorizeHomeomorph_apply (P : Set ℂ) (z : ℂ) :
    interiorizeHomeomorph P z = interiorize P z := rfl

theorem interiorize_injective (P : Set ℂ) : Function.Injective (interiorize P) :=
  (interiorizeHomeomorph P).injective

/-- `Φ` moves every point by at most `1/2`. -/
theorem norm_interiorize_sub_le (P : Set ℂ) (z : ℂ) : ‖interiorize P z - z‖ ≤ 1 / 2 := by
  have h0 := interiorShift_nonneg (interiorHeight_nonneg P z.re) z.im
  have h1 := interiorShift_le (δ := interiorHeight P z.re) z.im
  have h2 := interiorHeight_le_one P z.re
  rw [interiorize, add_sub_cancel_left, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs,
    abs_of_nonneg h0]
  linarith

/-- `Φ` maps the closed upper half-plane into itself. -/
theorem interiorize_im_nonneg (P : Set ℂ) {z : ℂ} (hz : 0 ≤ z.im) : 0 ≤ (interiorize P z).im := by
  rw [interiorize_im]
  linarith [interiorShift_nonneg (interiorHeight_nonneg P z.re) z.im]

/-- `Φ` fixes every point of `P` in the closed upper half-plane. -/
theorem interiorize_eq_self_of_mem {P : Set ℂ} {z : ℂ} (hz : z ∈ P) (him : 0 ≤ z.im) :
    interiorize P z = z := by
  have h := three_mul_interiorHeight_le hz
  rw [abs_of_nonneg him] at h
  have h0 := interiorHeight_nonneg P z.re
  rw [interiorize, interiorShift_eq_zero_of_le h0 (by linarith)]
  simp

/-- `Φ` fixes every point on the vertical line through a real point of `P`. -/
theorem interiorize_eq_self_of_re {P : Set ℂ} {x : ℝ} (hx : (x : ℂ) ∈ P) {z : ℂ} (hz : z.re = x) :
    interiorize P z = z := by
  rw [interiorize, hz, interiorHeight_eq_zero_of_mem hx, interiorShift_zero]
  simp

/-- A point of the closed upper half-plane whose image is real is a (real) point of the closed set `P`, and is
fixed. -/
theorem mem_of_interiorize_im_eq_zero {P : Set ℂ} (hPc : IsClosed P) (hPne : P.Nonempty) {z : ℂ}
    (hz : 0 ≤ z.im) (h : (interiorize P z).im = 0) : interiorize P z ∈ P ∧ interiorize P z = z := by
  have hδ := interiorHeight_nonneg P z.re
  have hge := add_interiorShift_ge hδ hz
  rw [interiorize_im] at h
  have hδ0 : interiorHeight P z.re = 0 := by linarith
  have him0 : z.im = 0 := by linarith
  have hinf : infDist (z.re : ℂ) P = 0 := by
    have hnn : 0 ≤ infDist (z.re : ℂ) P := infDist_nonneg
    rw [interiorHeight] at hδ0
    rcases min_eq_iff.1 hδ0 with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd h1 one_ne_zero
    · linarith
  have hmem : (z.re : ℂ) ∈ P := (hPc.mem_iff_infDist_zero hPne).2 hinf
  have hzre : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him0])
  have hfix : interiorize P z = z := by
    rw [interiorize, hδ0, interiorShift_zero]; simp
  exact ⟨by rw [hfix, hzre]; exact hmem, hfix⟩

/-! ### `Φ` preserves the closed Jordan-side order -/

/-- The open lower-left quadrant at the seed avoids the seed-ray closure of a curve in the closed upper
half-plane. -/
theorem quadrant_subset_compl_seedRayClosure {γ : ℝ≥0 → ℂ} (hγ : ∀ t, 0 ≤ (γ t).im) :
    {z : ℂ | z.re < (γ 0).re} ∩ {z : ℂ | z.im < 0} ⊆ (seedRayClosure γ)ᶜ := by
  rintro z ⟨hre, him⟩ hz
  rcases hz with ⟨t, rfl⟩ | ⟨hz, -⟩
  · exact absurd (hγ t) (not_le.2 him)
  · exact absurd hz (ne_of_lt hre)

/-- `Φ` maps the seed-ray closure of a curve with a real seed in `P` onto the seed-ray closure of the image
curve: it fixes the seed and the whole vertical line through it. -/
theorem image_seedRayClosure {P : Set ℂ} {γ : ℝ≥0 → ℂ} (h0 : (γ 0).im = 0) (h0P : γ 0 ∈ P) :
    interiorize P '' seedRayClosure γ = seedRayClosure (interiorize P ∘ γ) := by
  have hfix0 : interiorize P (γ 0) = γ 0 := interiorize_eq_self_of_mem h0P h0.ge
  have hx : ((γ 0).re : ℂ) ∈ P := by
    have : ((γ 0).re : ℂ) = γ 0 := Complex.ext (by simp) (by simp [h0])
    rw [this]; exact h0P
  have hray : ∀ z ∈ {z : ℂ | z.re = (γ 0).re ∧ z.im ≤ (γ 0).im}, interiorize P z = id z :=
    fun z hz => interiorize_eq_self_of_re hx hz.1
  unfold seedRayClosure
  rw [image_union, ← range_comp, image_congr hray, image_id, Function.comp_apply, hfix0]

/-- **The order step of G10.** For a curve `γ` in the closed upper half-plane with a real seed in `P`, `Φ` maps
the full closed left Jordan side of `γ` onto that of `Φ ∘ γ`. -/
theorem image_closedLeftSide {P : Set ℂ} {γ : ℝ≥0 → ℂ} (hγ : ∀ t, 0 ≤ (γ t).im) (h0 : (γ 0).im = 0)
    (h0P : γ 0 ∈ P) : interiorize P '' closedLeftSide γ = closedLeftSide (interiorize P ∘ γ) := by
  set Φ := interiorizeHomeomorph P with hΦ
  have hS := image_seedRayClosure h0 h0P
  have hfix0 : (interiorize P ∘ γ) 0 = γ 0 := interiorize_eq_self_of_mem h0P h0.ge
  have hγ' : ∀ t, 0 ≤ ((interiorize P ∘ γ) t).im := fun t => interiorize_im_nonneg P (hγ t)
  set p : ℂ := γ 0 - 1 - I with hp
  have hpQ : p ∈ {z : ℂ | z.re < (γ 0).re} ∩ {z : ℂ | z.im < 0} := by
    constructor <;> simp [hp, h0]
  have hΦpQ : interiorize P p ∈ {z : ℂ | z.re < ((interiorize P ∘ γ) 0).re} ∩ {z : ℂ | z.im < 0} := by
    rw [hfix0]
    refine ⟨by simpa using hpQ.1, ?_⟩
    have h1 := interiorShift_le (δ := interiorHeight P p.re) p.im
    have h2 := interiorHeight_le_one P p.re
    have h3 : p.im = -1 := by simp [hp, h0]
    simp only [mem_ofPred_eq, interiorize_im, h3] at h1 ⊢
    linarith
  have hpS : p ∈ (seedRayClosure γ)ᶜ := quadrant_subset_compl_seedRayClosure hγ hpQ
  have hcompl : Φ '' (seedRayClosure γ)ᶜ = (seedRayClosure (interiorize P ∘ γ))ᶜ := by
    rw [← hS]; exact Φ.toEquiv.image_compl _
  have hcc : Φ '' connectedComponentIn (seedRayClosure γ)ᶜ p =
      connectedComponentIn (seedRayClosure (interiorize P ∘ γ))ᶜ p := by
    rw [Φ.image_connectedComponentIn hpS, hcompl]
    symm
    apply connectedComponentIn_eq
    have hQ : IsPreconnected ({z : ℂ | z.re < ((interiorize P ∘ γ) 0).re} ∩ {z : ℂ | z.im < 0}) :=
      ((convex_halfSpace_re_lt _).inter (convex_halfSpace_im_lt _)).isPreconnected
    have hpQ' : p ∈ {z : ℂ | z.re < ((interiorize P ∘ γ) 0).re} ∩ {z : ℂ | z.im < 0} := by
      rw [hfix0]; exact hpQ
    exact hQ.subset_connectedComponentIn hpQ' (quadrant_subset_compl_seedRayClosure hγ') hΦpQ
  unfold closedLeftSide
  rw [image_union, hfix0, ← hp]
  exact congrArg₂ (· ∪ ·) hcc hS

/-! ### Lemma G10 -/

/-- **Lemma G10** (interiorization while fixing the stopped tangle; supplement §7.8, p. 502). Let `αh, βh` be ordered
proper completions (`range βh ⊆ closedLeftSide αh`) of the stopped prefixes `P₁ = α([0, a])`, `P₂ = β([0, c])`, with
a real seed `α 0` (the source has two real seeds; the seed of `β` need not be real here). Then there are ordered proper completions `α', β'` of the same prefixes whose real points all lie in
`P₁ ∪ P₂`, and which meet each point of `P₁ ∪ P₂` exactly when `αh`, resp. `βh`, does (so no new contacts with the
stopped tangle, and in particular no new seed visits). -/
theorem exists_interiorized_completions {α β αh βh : ℝ≥0 → ℂ} {a c : ℝ≥0}
    (hα : IsProperCompletion α a αh) (hβ : IsProperCompletion β c βh) (hα0 : (α 0).im = 0) (hord : range βh ⊆ closedLeftSide αh) :
    ∃ α' β' : ℝ≥0 → ℂ, IsProperCompletion α a α' ∧ IsProperCompletion β c β' ∧
      range β' ⊆ closedLeftSide α' ∧
      (∀ t, (α' t).im = 0 → α' t ∈ α '' Iic a ∪ β '' Iic c) ∧
      (∀ t, (β' t).im = 0 → β' t ∈ α '' Iic a ∪ β '' Iic c) ∧
      ∀ z ∈ α '' Iic a ∪ β '' Iic c, (z ∈ range α' ↔ z ∈ range αh) ∧ (z ∈ range β' ↔ z ∈ range βh) := by
  obtain ⟨hαc, hαi, hαim, hαp, hαe⟩ := hα
  obtain ⟨hβc, hβi, hβim, hβp, hβe⟩ := hβ
  set P := α '' Iic a ∪ β '' Iic c with hPdef
  have hPα : α '' Iic a = αh '' Iic a := image_congr fun t ht => (hαe t ht).symm
  have hPβ : β '' Iic c = βh '' Iic c := image_congr fun t ht => (hβe t ht).symm
  have hPc : IsClosed P := by
    rw [hPdef, hPα, hPβ]
    have hK : ∀ b : ℝ≥0, IsCompact (Iic b) := fun b => by rw [← Icc_bot]; exact isCompact_Icc
    exact (((hK a).image hαc).union ((hK c).image hβc)).isClosed
  have hα0P : α 0 ∈ P := Or.inl ⟨0, mem_Iic.2 zero_le, rfl⟩
  have hβ0P : β 0 ∈ P := Or.inr ⟨0, mem_Iic.2 zero_le, rfl⟩
  have hPne : P.Nonempty := ⟨_, hα0P⟩
  have hPim : ∀ z ∈ P, 0 ≤ z.im := by
    rintro z (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · rw [← hαe t ht]; exact hαim t
    · rw [← hβe t ht]; exact hβim t
  have hαh0 : αh 0 = α 0 := hαe 0 (zero_le)
  have hβh0 : βh 0 = β 0 := hβe 0 (zero_le)
  have hfix : ∀ z ∈ P, interiorize P z = z := fun z hz => interiorize_eq_self_of_mem hz (hPim z hz)
  -- the completion property is preserved
  have hcompl : ∀ {γ γh : ℝ≥0 → ℂ} {b : ℝ≥0}, Continuous γh → Function.Injective γh →
      (∀ t, 0 ≤ (γh t).im) → Tendsto (fun t => ‖γh t‖) atTop atTop → (∀ t ≤ b, γh t = γ t) →
      (∀ t ≤ b, γ t ∈ P) → IsProperCompletion γ b (interiorize P ∘ γh) := by
    intro γ γh b hc hi him hp he hmem
    refine ⟨(continuous_interiorize P).comp hc, (interiorize_injective P).comp hi,
      fun t => interiorize_im_nonneg P (him t), ?_, fun t ht => ?_⟩
    · refine tendsto_atTop_mono (fun t => ?_) (tendsto_atTop_add_const_right _ (-(1 / 2)) hp)
      have h1 := norm_interiorize_sub_le P (γh t)
      have h2 := norm_sub_norm_le (γh t) (interiorize P (γh t))
      rw [norm_sub_rev] at h2
      simp only [Function.comp_apply]
      linarith
    · simp only [Function.comp_apply, he t ht]
      exact hfix _ (hmem t ht)
  refine ⟨interiorize P ∘ αh, interiorize P ∘ βh,
    hcompl hαc hαi hαim hαp hαe (fun t ht => Or.inl ⟨t, ht, rfl⟩),
    hcompl hβc hβi hβim hβp hβe (fun t ht => Or.inr ⟨t, ht, rfl⟩), ?_, ?_, ?_, ?_⟩
  · rw [range_comp, ← image_closedLeftSide hαim (by rw [hαh0]; exact hα0) (by rw [hαh0]; exact hα0P)]
    exact image_mono hord
  · intro t ht
    exact (mem_of_interiorize_im_eq_zero hPc hPne (hαim t) ht).1
  · intro t ht
    exact (mem_of_interiorize_im_eq_zero hPc hPne (hβim t) ht).1
  · intro z hz
    have key : ∀ γh : ℝ≥0 → ℂ, (z ∈ range (interiorize P ∘ γh) ↔ z ∈ range γh) := by
      intro γh
      constructor
      · rintro ⟨t, ht⟩
        refine ⟨t, interiorize_injective P ?_⟩
        rw [hfix z hz]; exact ht
      · rintro ⟨t, rfl⟩
        exact ⟨t, by simp only [Function.comp_apply]; exact hfix _ hz⟩
    exact ⟨key αh, key βh⟩

/-- **Lemma G10**, the source's form: if the complete curves do not visit each other's initial seeds, the
interiorized ordered completions do not either, and their only real points are the real points already in the
stopped prefixes `P₁ ∪ P₂` (which include the two seeds). -/
theorem exists_interiorized_completions_of_seeds {α β αh βh : ℝ≥0 → ℂ} {a c : ℝ≥0}
    (hα : IsProperCompletion α a αh) (hβ : IsProperCompletion β c βh) (hα0 : (α 0).im = 0) (hord : range βh ⊆ closedLeftSide αh) (hαβ : α 0 ∉ range βh)
    (hβα : β 0 ∉ range αh) :
    ∃ α' β' : ℝ≥0 → ℂ, IsProperCompletion α a α' ∧ IsProperCompletion β c β' ∧
      range β' ⊆ closedLeftSide α' ∧ α 0 ∉ range β' ∧ β 0 ∉ range α' ∧
      (∀ t, (α' t).im = 0 → α' t ∈ α '' Iic a ∪ β '' Iic c) ∧
      (∀ t, (β' t).im = 0 → β' t ∈ α '' Iic a ∪ β '' Iic c) := by
  obtain ⟨α', β', h1, h2, h3, h4, h5, h6⟩ := exists_interiorized_completions hα hβ hα0 hord
  refine ⟨α', β', h1, h2, h3, fun h => hαβ ((h6 _ (Or.inl ⟨0, mem_Iic.2 zero_le, rfl⟩)).2.1 h),
    fun h => hβα ((h6 _ (Or.inr ⟨0, mem_Iic.2 zero_le, rfl⟩)).1.1 h), h4, h5⟩

/-- **Lemma G10** for the W0 predicate: ordered proper completions of prefixes with real seeds can be chosen
interiorized (every real point of either completion lies in the stopped prefixes). -/
theorem HasOrderedProperCompletions.exists_interiorized {α β : ℝ≥0 → ℂ} {a c : ℝ≥0}
    (h : HasOrderedProperCompletions α a β c) (hα0 : (α 0).im = 0) :
    ∃ α' β' : ℝ≥0 → ℂ, IsProperCompletion α a α' ∧ IsProperCompletion β c β' ∧
      range β' ⊆ closedLeftSide α' ∧
      (∀ t, (α' t).im = 0 → α' t ∈ α '' Iic a ∪ β '' Iic c) ∧
      (∀ t, (β' t).im = 0 → β' t ∈ α '' Iic a ∪ β '' Iic c) := by
  obtain ⟨αh, βh, hα, hβ, hord⟩ := h
  obtain ⟨α', β', h1, h2, h3, h4, h5, -⟩ := exists_interiorized_completions hα hβ hα0 hord
  exact ⟨α', β', h1, h2, h3, h4, h5⟩

end Supp7

end InteractingSLE
