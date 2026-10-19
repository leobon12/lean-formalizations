import HigherDimLFPP.Lower.Frames
import HigherDimLFPP.Lower.Profiles
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Topology.Order.IntermediateValue

/-!
# Lemma 5.1: polygons with equal edge lengths (source §5.1)

Packet P-L1, target T1 (ruling H6; audit HA4, "Details for later use" D1, finding HA4-9).

Fix a profile `f ∈ V_n(ℝ^{d-1})` with `E(f) ≤ e`, a unit vector `v ∈ ℝ^{d-1}`, the mesh
`K = 2^{n+g}` (`g ≥ 1`), and put `E₀ = e + 1`, `s = 1 + δ² E₀`, `q = s / K`. For an amplitude
`a`, the padded profile `f + a ψ_K v` has increments `Δ_i(a)`; the horizontal increments are
`ℓ_i(a) = (q² - δ²|Δ_i(a)|²)^{1/2}` and `S_δ(a) = Σ_i ℓ_i(a)` (`sumHIncr`). The polygon with
vertices `v_i = (x_i, δ (f + a ψ_K v)(i/K))`, `x_i = Σ_{k<i} ℓ_k` (`eqVert`), has all edges of
length exactly `q`, and it ends at `e₁` exactly when `S_δ(a) = 1`.

Main result `lemma51` (HA4 D1 with explicit constants): there is `δ₁ > 0` and a function
`δ ↦ a_{f,δ}` such that `a_{f,δ} → a_f = (2(E₀ - E(f)))^{1/2}` as `δ ↓ 0`, and for every
`δ ∈ (0, δ₁)`:

1. `a_{f,δ}` is the **unique** zero of `S_δ - 1` in `(0, a_f + 1)` (`S_δ` is concave);
2. the polygon runs from `0` to `e₁` with `K` edges of length `q`, all directed forward;
3. the knots satisfy `|x_i - i/K| ≤ δ² E₀` (5.4);
4. the edge directions satisfy `‖q⁻¹(v_{i+1} - v_i) - e₁‖ ≤ √2 c₁ δ`, with
   `c₁ = (2 e 2ⁿ)^{1/2} + (2E₀)^{1/2} + 1`;
5. the transverse parts are `δ (f + a_{f,δ} ψ_K v)(i/K)`, of norm `≤ (√e + 1) δ` (5.5).

The output geometry is recorded in the structure `EqualEdgeData` (HA4's "Output geometry of
Lemma 5.1 for one profile", with the extra field `forward`).

2D source: none (the 2D proof `LQGDimension` uses unequal edges and the uniform-in-`μ`
Lemma 5.1 core `L51.*`, which is not ported, ruling H6).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Lower

/-! ## Scalar lemmas -/

/-- Second-order expansion of the square root:
`q - u/(2q) - u²/(2q³) ≤ (q² - u)^{1/2} ≤ q - u/(2q)` for `0 ≤ u ≤ q²`. -/
theorem sqrt_sub_bounds {q u : ℝ} (hq : 0 < q) (huq : u ≤ q ^ 2) :
    q - u / (2 * q) - u ^ 2 / (2 * q ^ 3) ≤ √(q ^ 2 - u) ∧ √(q ^ 2 - u) ≤ q - u / (2 * q) := by
  set r := √(q ^ 2 - u) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = q ^ 2 - u := Real.sq_sqrt (by linarith)
  have hu : u = q ^ 2 - r ^ 2 := by linarith
  have hq' : q ≠ 0 := hq.ne'
  constructor
  · have h : q - u / (2 * q) - u ^ 2 / (2 * q ^ 3) - r =
        -((q - r) ^ 2 * (2 * q * r + r ^ 2)) / (2 * q ^ 3) := by
      rw [hu]; field_simp; ring
    have h' : -((q - r) ^ 2 * (2 * q * r + r ^ 2)) / (2 * q ^ 3) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (by positivity)) (by positivity)
    linarith
  · have h : q - u / (2 * q) - r = (q - r) ^ 2 / (2 * q) := by
      rw [hu]; field_simp; ring
    have h' : 0 ≤ (q - r) ^ 2 / (2 * q) := by positivity
    linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Convexity of `‖·‖²`: `‖(1-t) x + t y‖² ≤ (1-t)‖x‖² + t‖y‖²`. -/
theorem norm_sq_convex_comb_le (x y : E) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖(1 - t) • x + t • y‖ ^ 2 ≤ (1 - t) * ‖x‖ ^ 2 + t * ‖y‖ ^ 2 := by
  have h1 : ‖(1 - t) • x + t • y‖ ^ 2 =
      (1 - t) ^ 2 * ‖x‖ ^ 2 + 2 * ((1 - t) * t) * ⟪x, y⟫ + t ^ 2 * ‖y‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
    ring
  have h2 := norm_sub_sq_real x y
  have h3 : (1 - t) * ‖x‖ ^ 2 + t * ‖y‖ ^ 2 - ‖(1 - t) • x + t • y‖ ^ 2 =
      t * (1 - t) * ‖x - y‖ ^ 2 := by
    rw [h1, h2]; ring
  have h4 : 0 ≤ t * (1 - t) * ‖x - y‖ ^ 2 :=
    mul_nonneg (mul_nonneg ht0 (sub_nonneg.2 ht1)) (sq_nonneg _)
  linarith

/-! ## Horizontal increments -/

/-- Horizontal increment `ℓ = (q² - δ²‖Δ‖²)^{1/2}` of an edge of length `q` whose transverse
increment is `δ Δ`. -/
def hIncr (q δ : ℝ) (Δ : E) : ℝ := √(q ^ 2 - δ ^ 2 * ‖Δ‖ ^ 2)

omit [InnerProductSpace ℝ E] in
theorem hIncr_nonneg (q δ : ℝ) (Δ : E) : 0 ≤ hIncr q δ Δ := Real.sqrt_nonneg _

omit [InnerProductSpace ℝ E] in
theorem hIncr_sq {q δ : ℝ} {Δ : E} (h : δ ^ 2 * ‖Δ‖ ^ 2 ≤ q ^ 2) :
    hIncr q δ Δ ^ 2 = q ^ 2 - δ ^ 2 * ‖Δ‖ ^ 2 :=
  Real.sq_sqrt (by linarith)

omit [InnerProductSpace ℝ E] in
theorem hIncr_le {q δ : ℝ} (hq : 0 ≤ q) (Δ : E) : hIncr q δ Δ ≤ q := by
  rw [hIncr, Real.sqrt_le_left hq]
  nlinarith [sq_nonneg δ, sq_nonneg ‖Δ‖, mul_nonneg (sq_nonneg δ) (sq_nonneg ‖Δ‖)]

omit [InnerProductSpace ℝ E] in
theorem hIncr_pos {q δ : ℝ} {Δ : E} (h : δ ^ 2 * ‖Δ‖ ^ 2 < q ^ 2) : 0 < hIncr q δ Δ :=
  Real.sqrt_pos.2 (by linarith)

/-- Concavity of `a ↦ ℓ(D + a w)` between `0` and `b`. -/
theorem hIncr_concave {q δ : ℝ} (D w : E) {b t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h0 : δ ^ 2 * ‖D‖ ^ 2 ≤ q ^ 2) (hb : δ ^ 2 * ‖D + b • w‖ ^ 2 ≤ q ^ 2) :
    (1 - t) * hIncr q δ D + t * hIncr q δ (D + b • w) ≤ hIncr q δ (D + (t * b) • w) := by
  have hmid : D + (t * b) • w = (1 - t) • D + t • (D + b • w) := by module
  have hrad : (1 - t) * (q ^ 2 - δ ^ 2 * ‖D‖ ^ 2) + t * (q ^ 2 - δ ^ 2 * ‖D + b • w‖ ^ 2) ≤
      q ^ 2 - δ ^ 2 * ‖D + (t * b) • w‖ ^ 2 := by
    rw [hmid]
    have := norm_sq_convex_comb_le D (D + b • w) ht0 ht1
    nlinarith [sq_nonneg δ]
  have hX : (0 : ℝ) ≤ q ^ 2 - δ ^ 2 * ‖D‖ ^ 2 := by linarith
  have hY : (0 : ℝ) ≤ q ^ 2 - δ ^ 2 * ‖D + b • w‖ ^ 2 := by linarith
  have hconc := Real.strictConcaveOn_sqrt.concaveOn.2 (mem_Ici.2 hX) (mem_Ici.2 hY)
    (sub_nonneg.2 ht1) ht0 (by ring : (1 - t) + t = 1)
  simp only [smul_eq_mul] at hconc
  calc (1 - t) * hIncr q δ D + t * hIncr q δ (D + b • w)
      ≤ √((1 - t) * (q ^ 2 - δ ^ 2 * ‖D‖ ^ 2) + t * (q ^ 2 - δ ^ 2 * ‖D + b • w‖ ^ 2)) := hconc
    _ ≤ hIncr q δ (D + (t * b) • w) := Real.sqrt_le_sqrt hrad

/-! ## The sum `S_δ` and the knots -/

/-- `S_δ(a) = Σ_{i<K} ℓ_i(a)`: total horizontal extent of the padded polygon. -/
def sumHIncr (K : ℕ) (q δ : ℝ) (f : ℝ → E) (v : E) (a : ℝ) : ℝ :=
  ∑ i ∈ Finset.range K, hIncr q δ (incr K (padProf K f v a) i)

/-- Horizontal knots `x_i = Σ_{k<i} ℓ_k(a)`. -/
def knot (K : ℕ) (q δ : ℝ) (f : ℝ → E) (v : E) (a : ℝ) (i : ℕ) : ℝ :=
  ∑ k ∈ Finset.range i, hIncr q δ (incr K (padProf K f v a) k)

theorem knot_zero (K : ℕ) (q δ : ℝ) (f : ℝ → E) (v : E) (a : ℝ) : knot K q δ f v a 0 = 0 := by
  simp [knot]

theorem knot_succ (K : ℕ) (q δ : ℝ) (f : ℝ → E) (v : E) (a : ℝ) (i : ℕ) :
    knot K q δ f v a (i + 1) = knot K q δ f v a i + hIncr q δ (incr K (padProf K f v a) i) :=
  Finset.sum_range_succ _ _

theorem knot_self (K : ℕ) (q δ : ℝ) (f : ℝ → E) (v : E) (a : ℝ) :
    knot K q δ f v a K = sumHIncr K q δ f v a := rfl

/-- The step `q = (1 + δ² E₀)/K` (5.2). -/
def qOf (K : ℕ) (E₀ δ : ℝ) : ℝ := (1 + δ ^ 2 * E₀) / K

/-- The increment constant `c₁ = (2 e 2ⁿ)^{1/2} + (2(e+1))^{1/2} + 1` of HA4 D1. -/
def incrConst (n : ℕ) (e : ℝ) : ℝ := √(2 * e * 2 ^ n) + √(2 * (e + 1)) + 1

/-- The limit amplitude `a_f = (2(E₀ - E(f)))^{1/2}`, `E₀ = e + 1` (5.5). -/
def aLim (e : ℝ) (f : ℝ → E) : ℝ := √(2 * (e + 1 - energy f))

theorem one_le_incrConst (n : ℕ) (e : ℝ) : 1 ≤ incrConst n e := by
  unfold incrConst
  have := Real.sqrt_nonneg (2 * e * 2 ^ n)
  have := Real.sqrt_nonneg (2 * (e + 1))
  linarith

section Profile

variable {n g : ℕ} {e : ℝ} {f : ℝ → E} {v : E}

/-- Padded increments: `Δ_i(a) = Δ_i f + a (ψ_K-increment)_i v`. -/
theorem incr_padProf_eq (K : ℕ) (f : ℝ → E) (v : E) (a : ℝ) (i : ℕ) :
    incr K (padProf K f v a) i = incr K f i + a • (incr K (psiK K) i • v) := by
  rw [incr_padProf, smul_smul]

/-- `a_f ≤ (2E₀)^{1/2}`. -/
theorem aLim_le (f : ℝ → E) (e : ℝ) : aLim e f ≤ √(2 * (e + 1)) := by
  unfold aLim
  have := Var.energy_nonneg f
  exact Real.sqrt_le_sqrt (by linarith)

theorem aLim_sq (hfe : energy f ≤ e) : aLim e f ^ 2 = 2 * (e + 1 - energy f) :=
  Real.sq_sqrt (by linarith)

theorem one_le_aLim (hfe : energy f ≤ e) : 1 ≤ aLim e f := by
  unfold aLim
  rw [Real.le_sqrt zero_le_one (by linarith)]
  linarith

/-- **Increment bound for the padded profile**: `‖Δ_i(a)‖ ≤ c₁ / K` for `0 ≤ a ≤ a_f + 1`. -/
theorem norm_incr_padProf_le (hf : f ∈ Vg E n) (hfe : energy f ≤ e) (hv : ‖v‖ = 1) {a : ℝ}
    (ha0 : 0 ≤ a) (ha : a ≤ aLim e f + 1) {i : ℕ} (hi : i < 2 ^ (n + g)) :
    ‖incr (2 ^ (n + g)) (padProf (2 ^ (n + g)) f v a) i‖ ≤
      incrConst n e / ((2 ^ (n + g) : ℕ) : ℝ) := by
  set K : ℕ := 2 ^ (n + g) with hK
  have hKpos : 0 < K := by positivity
  have hK' : (0 : ℝ) < K := by exact_mod_cast hKpos
  have h1 : ‖incr K f i‖ ≤ √(2 * e * 2 ^ n) / K := by
    refine (norm_incr_le hf hi).trans ?_
    gcongr
  have h2 : ‖a • (incr K (psiK K) i • v)‖ ≤ (aLim e f + 1) / K := by
    rw [norm_smul, norm_smul, hv, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg ha0, incr_psiK hKpos hi]
    have habs : |(if Even i then (1 : ℝ) / K else (-1 : ℝ) / K)| = 1 / K := by
      split_ifs
      · rw [abs_of_pos (by positivity)]
      · rw [neg_div, abs_neg, abs_of_pos (by positivity)]
    rw [habs, mul_one_div]
    gcongr
  have h3 := aLim_le f e
  rw [incr_padProf_eq]
  calc ‖incr K f i + a • (incr K (psiK K) i • v)‖
      ≤ ‖incr K f i‖ + ‖a • (incr K (psiK K) i • v)‖ := norm_add_le _ _
    _ ≤ √(2 * e * 2 ^ n) / K + (aLim e f + 1) / K := add_le_add h1 h2
    _ ≤ incrConst n e / K := by
        rw [← add_div]
        gcongr
        unfold incrConst
        linarith

/-- The squared padded increments sum to `(2/K)(E(f) + a²/2)`. -/
theorem sum_sq_incr_padProf_eq (hg : 1 ≤ g) (hf : f ∈ Vg E n) (hv : ‖v‖ = 1) (a : ℝ) :
    ∑ i ∈ Finset.range (2 ^ (n + g)), ‖incr (2 ^ (n + g)) (padProf (2 ^ (n + g)) f v a) i‖ ^ 2 =
      2 * (energy f + a ^ 2 / 2) / ((2 ^ (n + g) : ℕ) : ℝ) := by
  have hf' : f ∈ Vg E (n + g) := Var.Vg_mono (by omega) hf
  rw [sum_sq_incr_padProf hg hf hv, energy_eq_sum hf']
  have hK' : (0 : ℝ) < ((2 ^ (n + g) : ℕ) : ℝ) := by positivity
  push_cast at hK' ⊢
  field_simp

/-- Under `δ c₁ ≤ 1` and `q ≥ 1/K`, the radicands are controlled: `δ²‖Δ_i(a)‖² ≤ δ²c₁² q²`. -/
theorem radicand_le (hf : f ∈ Vg E n) (hfe : energy f ≤ e) (hv : ‖v‖ = 1) {a : ℝ}
    (ha0 : 0 ≤ a) (ha : a ≤ aLim e f + 1) {i : ℕ} (hi : i < 2 ^ (n + g)) {q δ : ℝ}
    (hq : 1 / ((2 ^ (n + g) : ℕ) : ℝ) ≤ q) :
    δ ^ 2 * ‖incr (2 ^ (n + g)) (padProf (2 ^ (n + g)) f v a) i‖ ^ 2 ≤
      δ ^ 2 * incrConst n e ^ 2 * q ^ 2 := by
  have hK' : (0 : ℝ) < ((2 ^ (n + g) : ℕ) : ℝ) := by positivity
  have h1 := norm_incr_padProf_le hf hfe hv (g := g) ha0 ha hi
  have hc : 0 ≤ incrConst n e := le_trans zero_le_one (one_le_incrConst n e)
  have h2 : incrConst n e / ((2 ^ (n + g) : ℕ) : ℝ) ≤ incrConst n e * q := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hq hc
  have h3 : ‖incr (2 ^ (n + g)) (padProf (2 ^ (n + g)) f v a) i‖ ≤ incrConst n e * q :=
    h1.trans h2
  have h4 : ‖incr (2 ^ (n + g)) (padProf (2 ^ (n + g)) f v a) i‖ ^ 2 ≤ (incrConst n e * q) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h3 2
  calc δ ^ 2 * ‖incr (2 ^ (n + g)) (padProf (2 ^ (n + g)) f v a) i‖ ^ 2
      ≤ δ ^ 2 * (incrConst n e * q) ^ 2 := mul_le_mul_of_nonneg_left h4 (sq_nonneg δ)
    _ = δ ^ 2 * incrConst n e ^ 2 * q ^ 2 := by ring

/-- **Expansion of `S_δ`** (HA4 D1): for `0 ≤ a ≤ a_f + 1`, `q ≥ 1/K` and `δ c₁ ≤ 1`,
`Kq - δ²(E(f) + a²/2)/(Kq) - Kq δ⁴c₁⁴/2 ≤ S_δ(a) ≤ Kq - δ²(E(f) + a²/2)/(Kq)`. -/
theorem sumHIncr_bounds (hg : 1 ≤ g) (hf : f ∈ Vg E n) (hfe : energy f ≤ e) (hv : ‖v‖ = 1)
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ aLim e f + 1) {q δ : ℝ}
    (hq : 1 / ((2 ^ (n + g) : ℕ) : ℝ) ≤ q) (hδc : δ ^ 2 * incrConst n e ^ 2 ≤ 1) :
    ((2 ^ (n + g) : ℕ) : ℝ) * q -
        δ ^ 2 * (energy f + a ^ 2 / 2) / (((2 ^ (n + g) : ℕ) : ℝ) * q) -
        ((2 ^ (n + g) : ℕ) : ℝ) * q * (δ ^ 4 * incrConst n e ^ 4) / 2 ≤
      sumHIncr (2 ^ (n + g)) q δ f v a ∧
    sumHIncr (2 ^ (n + g)) q δ f v a ≤
      ((2 ^ (n + g) : ℕ) : ℝ) * q -
        δ ^ 2 * (energy f + a ^ 2 / 2) / (((2 ^ (n + g) : ℕ) : ℝ) * q) := by
  set K : ℕ := 2 ^ (n + g) with hK
  have hK' : (0 : ℝ) < K := by positivity
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
  set c := incrConst n e with hc
  set Δ : ℕ → E := fun i => incr K (padProf K f v a) i with hΔ
  have hrad : ∀ i ∈ Finset.range K, δ ^ 2 * ‖Δ i‖ ^ 2 ≤ δ ^ 2 * c ^ 2 * q ^ 2 := fun i hi =>
    radicand_le hf hfe hv ha0 ha (Finset.mem_range.1 hi) hq
  have hrad' : ∀ i ∈ Finset.range K, δ ^ 2 * ‖Δ i‖ ^ 2 ≤ q ^ 2 := by
    intro i hi
    have := hrad i hi
    nlinarith [sq_nonneg q]
  have hsum : ∑ i ∈ Finset.range K, ‖Δ i‖ ^ 2 = 2 * (energy f + a ^ 2 / 2) / K :=
    sum_sq_incr_padProf_eq hg hf hv a
  have hmain : ∑ i ∈ Finset.range K, (q - δ ^ 2 * ‖Δ i‖ ^ 2 / (2 * q)) =
      (K : ℝ) * q - δ ^ 2 * (energy f + a ^ 2 / 2) / ((K : ℝ) * q) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.sum_div, ← Finset.mul_sum, hsum]
    field_simp
  have hS : sumHIncr K q δ f v a = ∑ i ∈ Finset.range K, √(q ^ 2 - δ ^ 2 * ‖Δ i‖ ^ 2) := rfl
  constructor
  · -- lower bound
    have hterm : ∀ i ∈ Finset.range K,
        q - δ ^ 2 * ‖Δ i‖ ^ 2 / (2 * q) - q * (δ ^ 4 * c ^ 4) / 2 ≤
          √(q ^ 2 - δ ^ 2 * ‖Δ i‖ ^ 2) := by
      intro i hi
      have hb := (sqrt_sub_bounds hq0 (hrad' i hi)).1
      have hu0 : 0 ≤ δ ^ 2 * ‖Δ i‖ ^ 2 := by positivity
      have hu2 : (δ ^ 2 * ‖Δ i‖ ^ 2) ^ 2 ≤ (δ ^ 2 * c ^ 2 * q ^ 2) ^ 2 :=
        pow_le_pow_left₀ hu0 (hrad i hi) 2
      have hdiv : (δ ^ 2 * ‖Δ i‖ ^ 2) ^ 2 / (2 * q ^ 3) ≤ q * (δ ^ 4 * c ^ 4) / 2 := by
        rw [div_le_iff₀ (by positivity)]
        have : q * (δ ^ 4 * c ^ 4) / 2 * (2 * q ^ 3) = (δ ^ 2 * c ^ 2 * q ^ 2) ^ 2 := by ring
        rw [this]
        exact hu2
      linarith
    calc (K : ℝ) * q - δ ^ 2 * (energy f + a ^ 2 / 2) / ((K : ℝ) * q) -
          (K : ℝ) * q * (δ ^ 4 * c ^ 4) / 2
        = ∑ i ∈ Finset.range K, (q - δ ^ 2 * ‖Δ i‖ ^ 2 / (2 * q) - q * (δ ^ 4 * c ^ 4) / 2) := by
          rw [Finset.sum_sub_distrib, hmain, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
      _ ≤ ∑ i ∈ Finset.range K, √(q ^ 2 - δ ^ 2 * ‖Δ i‖ ^ 2) := Finset.sum_le_sum hterm
      _ = sumHIncr K q δ f v a := hS.symm
  · -- upper bound
    rw [hS, ← hmain]
    exact Finset.sum_le_sum fun i hi => (sqrt_sub_bounds hq0 (hrad' i hi)).2

/-- `S_δ` is continuous in the amplitude. -/
theorem continuous_sumHIncr (K : ℕ) (q δ : ℝ) (f : ℝ → E) (v : E) :
    Continuous fun a => sumHIncr K q δ f v a := by
  unfold sumHIncr hIncr
  refine continuous_finsetSum _ fun i _ => ?_
  simp only [incr_padProf_eq]
  fun_prop

/-- **Concavity of `S_δ`** on `[0, a_f + 1]` (HA4 finding HA4-9). -/
theorem sumHIncr_concave (hf : f ∈ Vg E n) (hfe : energy f ≤ e) (hv : ‖v‖ = 1) {q δ : ℝ}
    (hq : 1 / ((2 ^ (n + g) : ℕ) : ℝ) ≤ q) (hδc : δ ^ 2 * incrConst n e ^ 2 ≤ 1) {b t : ℝ}
    (hb0 : 0 ≤ b) (hb : b ≤ aLim e f + 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * sumHIncr (2 ^ (n + g)) q δ f v 0 + t * sumHIncr (2 ^ (n + g)) q δ f v b ≤
      sumHIncr (2 ^ (n + g)) q δ f v (t * b) := by
  set K : ℕ := 2 ^ (n + g) with hK
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
  have hrad : ∀ a, 0 ≤ a → a ≤ aLim e f + 1 → ∀ i ∈ Finset.range K,
      δ ^ 2 * ‖incr K (padProf K f v a) i‖ ^ 2 ≤ q ^ 2 := by
    intro a ha0 ha i hi
    have := radicand_le hf hfe hv ha0 ha (Finset.mem_range.1 hi) hq (δ := δ)
    nlinarith [sq_nonneg q]
  unfold sumHIncr
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have h0 := hrad 0 le_rfl (by linarith [one_le_aLim hfe]) i hi
  have hb' := hrad b hb0 hb i hi
  rw [incr_padProf_eq] at h0 hb' ⊢
  rw [incr_padProf_eq K f v b, incr_padProf_eq K f v (t * b)]
  rw [zero_smul, add_zero] at h0 ⊢
  exact hIncr_concave _ _ ht0 ht1 h0 hb'

end Profile

/-! ## Existence, uniqueness and localization of the zero of `S_δ - 1` -/

/-- A function that is concave between `0` and every `b ∈ [0, A]` and exceeds `1` at `0` takes
the value `1` at most once on `(0, A]`, and stays above `1` before that point. -/
theorem lt_of_concave_of_one_lt {S : ℝ → ℝ} {A : ℝ}
    (hconc : ∀ b, 0 ≤ b → b ≤ A → ∀ t, 0 ≤ t → t ≤ 1 → (1 - t) * S 0 + t * S b ≤ S (t * b))
    (h0 : 1 < S 0) {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b ≤ A) (hSb : 1 ≤ S b) :
    1 < S a := by
  have hb0 : 0 < b := ha.trans hab
  set t := a / b with ht
  have ht0 : 0 ≤ t := div_nonneg ha.le hb0.le
  have ht1 : t < 1 := (div_lt_one hb0).2 hab
  have htb : t * b = a := by rw [ht]; field_simp
  have := hconc b hb0.le hb t ht0 ht1.le
  rw [htb] at this
  nlinarith

section Zero

variable {n g : ℕ} {e : ℝ} {f : ℝ → E} {v : E}

/-- The zero is unique on `(0, a_f + 1)`. -/
theorem sumHIncr_eq_one_unique (hf : f ∈ Vg E n) (hfe : energy f ≤ e) (hv : ‖v‖ = 1) {q δ : ℝ}
    (hq : 1 / ((2 ^ (n + g) : ℕ) : ℝ) ≤ q) (hδc : δ ^ 2 * incrConst n e ^ 2 ≤ 1)
    (h0 : 1 < sumHIncr (2 ^ (n + g)) q δ f v 0) {a b : ℝ}
    (ha : a ∈ Ioo 0 (aLim e f + 1)) (hb : b ∈ Ioo 0 (aLim e f + 1))
    (hSa : sumHIncr (2 ^ (n + g)) q δ f v a = 1) (hSb : sumHIncr (2 ^ (n + g)) q δ f v b = 1) :
    a = b := by
  have hconc : ∀ c, 0 ≤ c → c ≤ aLim e f + 1 → ∀ t, 0 ≤ t → t ≤ 1 →
      (1 - t) * sumHIncr (2 ^ (n + g)) q δ f v 0 + t * sumHIncr (2 ^ (n + g)) q δ f v c ≤
        sumHIncr (2 ^ (n + g)) q δ f v (t * c) :=
    fun c hc0 hc t ht0 ht1 => sumHIncr_concave hf hfe hv hq hδc hc0 hc ht0 ht1
  rcases lt_trichotomy a b with h | h | h
  · have := lt_of_concave_of_one_lt hconc h0 ha.1 h hb.2.le hSb.ge
    linarith
  · exact h
  · have := lt_of_concave_of_one_lt hconc h0 hb.1 h ha.2.le hSa.ge
    linarith

/-- Values of `S_δ` at `0`, at `a_f ± η`, under the smallness conditions of `lemma51`. -/
theorem sumHIncr_values (hg : 1 ≤ g) (hf : f ∈ Vg E n) (hfe : energy f ≤ e) (hv : ‖v‖ = 1)
    {δ : ℝ} (hδ : 0 < δ) (hδc : δ ^ 2 * incrConst n e ^ 2 ≤ 1) (hδE : δ ^ 2 * (e + 1) ≤ 1) :
    (δ ^ 2 * incrConst n e ^ 4 < 1 →
      1 < sumHIncr (2 ^ (n + g)) (qOf (2 ^ (n + g)) (e + 1) δ) δ f v 0) ∧
    (∀ η, 0 < η → η ≤ 1 → δ ^ 2 * incrConst n e ^ 4 < η / 2 →
      1 < sumHIncr (2 ^ (n + g)) (qOf (2 ^ (n + g)) (e + 1) δ) δ f v (aLim e f - η)) ∧
    (∀ η, 0 < η → η ≤ 1 → δ ^ 2 * (e + 1) ^ 2 < η →
      sumHIncr (2 ^ (n + g)) (qOf (2 ^ (n + g)) (e + 1) δ) δ f v (aLim e f + η) < 1) := by
  set K : ℕ := 2 ^ (n + g) with hK
  have hK' : (0 : ℝ) < K := by positivity
  set q := qOf K (e + 1) δ with hq_def
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = 1 + δ ^ 2 * (e + 1) := ⟨_, rfl⟩
  have hE0 := Var.energy_nonneg f
  have he : 0 ≤ e := hE0.trans hfe
  have hs1 : 1 ≤ s := by rw [hs]; nlinarith [sq_nonneg δ]
  have hs2 : s ≤ 2 := by rw [hs]; linarith
  have hKq : (K : ℝ) * q = s := by
    rw [hq_def, qOf, hs]; field_simp
  have hq1 : 1 / (K : ℝ) ≤ q := by
    rw [hq_def, qOf, ← hs]
    exact div_le_div_of_nonneg_right hs1 hK'.le
  set c := incrConst n e with hc
  have hc1 : 1 ≤ c := one_le_incrConst n e
  have haf := one_le_aLim hfe
  have haf2 := aLim_sq hfe
  -- the expansion, rewritten with `Kq = s`
  have hexp : ∀ a, 0 ≤ a → a ≤ aLim e f + 1 →
      s - δ ^ 2 * (energy f + a ^ 2 / 2) / s - δ ^ 4 * c ^ 4 ≤ sumHIncr K q δ f v a ∧
      sumHIncr K q δ f v a ≤ s - δ ^ 2 * (energy f + a ^ 2 / 2) / s := by
    intro a ha0 ha
    obtain ⟨h1, h2⟩ := sumHIncr_bounds hg hf hfe hv ha0 ha hq1 hδc
    rw [hKq] at h1 h2
    refine ⟨le_trans ?_ h1, h2⟩
    have h3 : 0 ≤ δ ^ 4 * c ^ 4 := by positivity
    have h4 : s * (δ ^ 4 * c ^ 4) / 2 ≤ δ ^ 4 * c ^ 4 := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith
    linarith
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hs0 : 0 < s := by linarith
  refine ⟨fun hsmall => ?_, fun η hη hη1 hsmall => ?_, fun η hη hη1 hsmall => ?_⟩
  · -- `S(0) > 1`
    have h := (hexp 0 le_rfl (by linarith)).1
    have h1 : δ ^ 2 * (energy f + 0 ^ 2 / 2) / s ≤ δ ^ 2 * energy f := by
      rw [show (0 : ℝ) ^ 2 / 2 = 0 by ring, add_zero, div_le_iff₀ hs0]
      have := mul_nonneg (mul_nonneg hδ2.le hE0) (sub_nonneg.2 hs1)
      linarith
    have h2 : δ ^ 4 * c ^ 4 < δ ^ 2 := by
      have : δ ^ 4 * c ^ 4 = δ ^ 2 * (δ ^ 2 * c ^ 4) := by ring
      rw [this]
      calc δ ^ 2 * (δ ^ 2 * c ^ 4) < δ ^ 2 * 1 := mul_lt_mul_of_pos_left hsmall hδ2
        _ = δ ^ 2 := mul_one _
    have h3 := mul_nonneg hδ2.le (sub_nonneg.2 hfe)
    linarith
  · -- `S(a_f - η) > 1`
    have ha0 : 0 ≤ aLim e f - η := by linarith
    have h := (hexp (aLim e f - η) ha0 (by linarith)).1
    have hnum : energy f + (aLim e f - η) ^ 2 / 2 = (e + 1) - aLim e f * η + η ^ 2 / 2 := by
      linear_combination (1 / 2 : ℝ) * haf2
    have hnum0 : 0 ≤ (e + 1) - aLim e f * η + η ^ 2 / 2 := by
      rw [← hnum]; positivity
    have h1 : δ ^ 2 * (energy f + (aLim e f - η) ^ 2 / 2) / s ≤
        δ ^ 2 * ((e + 1) - aLim e f * η + η ^ 2 / 2) := by
      rw [hnum, div_le_iff₀ hs0]
      have := mul_nonneg (mul_nonneg hδ2.le hnum0) (sub_nonneg.2 hs1)
      linarith
    have h2 : δ ^ 4 * c ^ 4 < δ ^ 2 * (η / 2) := by
      have : δ ^ 4 * c ^ 4 = δ ^ 2 * (δ ^ 2 * c ^ 4) := by ring
      rw [this]
      exact mul_lt_mul_of_pos_left hsmall hδ2
    have haη : η ≤ aLim e f * η := by
      have := mul_le_mul_of_nonneg_right haf hη.le
      linarith
    have hη2 : η ^ 2 ≤ η := by nlinarith
    have h3 : η / 2 ≤ aLim e f * η - η ^ 2 / 2 := by linarith
    have h4 : δ ^ 2 * (η / 2) ≤ δ ^ 2 * (aLim e f * η - η ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left h3 hδ2.le
    linarith
  · -- `S(a_f + η) < 1`
    have ha0 : 0 ≤ aLim e f + η := by linarith
    have h := (hexp (aLim e f + η) ha0 (by linarith)).2
    have hnum : energy f + (aLim e f + η) ^ 2 / 2 = (e + 1) + aLim e f * η + η ^ 2 / 2 := by
      linear_combination (1 / 2 : ℝ) * haf2
    have key : s - δ ^ 2 * (energy f + (aLim e f + η) ^ 2 / 2) / s - 1 =
        δ ^ 2 / s * (δ ^ 2 * (e + 1) ^ 2 - aLim e f * η - η ^ 2 / 2) := by
      rw [hnum]
      field_simp
      rw [hs]
      ring
    have haη : η ≤ aLim e f * η := by
      have := mul_le_mul_of_nonneg_right haf hη.le
      linarith
    have hneg : δ ^ 2 * (e + 1) ^ 2 - aLim e f * η - η ^ 2 / 2 < 0 := by
      have := sq_nonneg η
      linarith
    have : δ ^ 2 / s * (δ ^ 2 * (e + 1) ^ 2 - aLim e f * η - η ^ 2 / 2) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) hneg
    linarith

/-- **Existence and uniqueness of the zero** of `S_δ - 1` on `(0, a_f + 1)`. -/
theorem exists_unique_sumHIncr_eq_one (hg : 1 ≤ g) (hf : f ∈ Vg E n) (hfe : energy f ≤ e)
    (hv : ‖v‖ = 1) {δ : ℝ} (hδ : 0 < δ) (hδc : δ ^ 2 * incrConst n e ^ 2 ≤ 1)
    (hδE : δ ^ 2 * (e + 1) ≤ 1) (hδc4 : δ ^ 2 * incrConst n e ^ 4 < 1)
    (hδE2 : δ ^ 2 * (e + 1) ^ 2 < 1) :
    ∃ a ∈ Ioo 0 (aLim e f + 1),
      sumHIncr (2 ^ (n + g)) (qOf (2 ^ (n + g)) (e + 1) δ) δ f v a = 1 ∧
      ∀ b ∈ Ioo 0 (aLim e f + 1),
        sumHIncr (2 ^ (n + g)) (qOf (2 ^ (n + g)) (e + 1) δ) δ f v b = 1 → b = a := by
  set K : ℕ := 2 ^ (n + g) with hK
  have hK' : (0 : ℝ) < K := by positivity
  set q := qOf K (e + 1) δ with hq_def
  have hE0 := Var.energy_nonneg f
  have hq1 : 1 / (K : ℝ) ≤ q := by
    rw [hq_def, qOf]
    refine div_le_div_of_nonneg_right ?_ hK'.le
    have : 0 ≤ δ ^ 2 * (e + 1) := by nlinarith [sq_nonneg δ]
    linarith
  obtain ⟨hS0, -, hSA⟩ := sumHIncr_values hg hf hfe hv hδ hδc hδE
  have h0 := hS0 hδc4
  have hA := hSA 1 one_pos le_rfl (by linarith)
  have haf := one_le_aLim hfe
  -- intermediate value theorem
  obtain ⟨a, ha, hSa⟩ : ∃ a ∈ Icc 0 (aLim e f + 1), sumHIncr K q δ f v a = 1 := by
    have := intermediate_value_Icc' (a := (0 : ℝ)) (b := aLim e f + 1) (by linarith)
      (continuous_sumHIncr K q δ f v).continuousOn
      (show (1 : ℝ) ∈ Icc (sumHIncr K q δ f v (aLim e f + 1)) (sumHIncr K q δ f v 0) from
        ⟨hA.le, h0.le⟩)
    obtain ⟨a, ha, hSa⟩ := this
    exact ⟨a, ha, hSa⟩
  have ha' : a ∈ Ioo 0 (aLim e f + 1) := by
    refine ⟨lt_of_le_of_ne ha.1 ?_, lt_of_le_of_ne ha.2 ?_⟩
    · rintro rfl; linarith
    · rintro rfl; linarith
  refine ⟨a, ha', hSa, fun b hb hSb => ?_⟩
  exact sumHIncr_eq_one_unique hf hfe hv hq1 hδc h0 hb ha' hSb hSa

/-- **Localization of the zero**: under the extra smallness conditions, the zero lies within `η`
of `a_f`. -/
theorem abs_sub_aLim_lt (hg : 1 ≤ g) (hf : f ∈ Vg E n) (hfe : energy f ≤ e) (hv : ‖v‖ = 1)
    {δ : ℝ} (hδ : 0 < δ) (hδc : δ ^ 2 * incrConst n e ^ 2 ≤ 1) (hδE : δ ^ 2 * (e + 1) ≤ 1)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hδc4 : δ ^ 2 * incrConst n e ^ 4 < η / 2)
    (hδE2 : δ ^ 2 * (e + 1) ^ 2 < η) {a : ℝ} (ha : a ∈ Ioo 0 (aLim e f + 1))
    (hSa : sumHIncr (2 ^ (n + g)) (qOf (2 ^ (n + g)) (e + 1) δ) δ f v a = 1) :
    |a - aLim e f| < η := by
  set K : ℕ := 2 ^ (n + g) with hK
  have hK' : (0 : ℝ) < K := by positivity
  set q := qOf K (e + 1) δ with hq_def
  have hq1 : 1 / (K : ℝ) ≤ q := by
    rw [hq_def, qOf]
    refine div_le_div_of_nonneg_right ?_ hK'.le
    have : 0 ≤ δ ^ 2 * (e + 1) := by nlinarith [sq_nonneg δ, Var.energy_nonneg f]
    linarith
  obtain ⟨hS0, hSm, hSp⟩ := sumHIncr_values hg hf hfe hv hδ hδc hδE
  have h0 := hS0 (by linarith)
  have hm := hSm η hη hη1 hδc4
  have hp := hSp η hη hη1 hδE2
  have haf := one_le_aLim hfe
  have hconc : ∀ c, 0 ≤ c → c ≤ aLim e f + 1 → ∀ t, 0 ≤ t → t ≤ 1 →
      (1 - t) * sumHIncr K q δ f v 0 + t * sumHIncr K q δ f v c ≤ sumHIncr K q δ f v (t * c) :=
    fun c hc0 hc t ht0 ht1 => sumHIncr_concave hf hfe hv hq1 hδc hc0 hc ht0 ht1
  rw [abs_lt]
  constructor
  · -- `a > a_f - η`
    by_contra hcon
    push Not at hcon
    rcases lt_or_eq_of_le (show a ≤ aLim e f - η by linarith) with hlt | heq
    · have := lt_of_concave_of_one_lt hconc h0 ha.1 hlt (by linarith) hm.le
      linarith
    · rw [heq] at hSa
      linarith
  · -- `a < a_f + η`
    by_contra hcon
    push Not at hcon
    have hapos : 0 < a := ha.1
    set t := (aLim e f + η) / a with ht
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hapos.le
    have ht1 : t ≤ 1 := (div_le_one hapos).2 (by linarith)
    have hta : t * a = aLim e f + η := by rw [ht]; field_simp
    have := hconc a hapos.le ha.2.le t ht0 ht1
    rw [hta, hSa] at this
    nlinarith

end Zero

/-! ## The polygon -/

variable {d : ℕ}

/-- Vertices of the equal-edge polygon: `v_i = x_i e₁ + δ (0, (f + a ψ_K v)(i/K))`. -/
def eqVert (K : ℕ) (q δ : ℝ) (f : ℝ → Rd (d - 1)) (v : Rd (d - 1)) (a : ℝ) (i : ℕ) : Rd d :=
  knot K q δ f v a i • e₁ d + δ • embedT (padProf K f v a ((i : ℝ) / K))

/-- **Output geometry of Lemma 5.1 for one profile** (HA4's `EqualEdgeData`, with the extra
field `forward`): a polygon `v 0, …, v K` from `0` to `e₁` whose `K` edges have length `q`, are
directed forward, have angle `≤ c δ` with `e₁`, whose knots are within `δ² E₀` of the uniform
mesh, and whose vertices have transverse parts of norm `≤ M₀ δ`. -/
structure EqualEdgeData (K : ℕ) (δ q E₀ M₀ c : ℝ) (v : ℕ → Rd d) : Prop where
  start : v 0 = 0
  finish : v K = e₁ d
  edge_len : ∀ i < K, ‖v (i + 1) - v i‖ = q
  forward : ∀ i < K, 0 < horiz (v (i + 1)) - horiz (v i)
  knots : ∀ i ≤ K, |horiz (v i) - (i : ℝ) / K| ≤ δ ^ 2 * E₀
  transverse : ∀ i ≤ K, ‖transv (v i)‖ ≤ M₀ * δ
  angle : ∀ i < K, ‖q⁻¹ • (v (i + 1) - v i) - e₁ d‖ ≤ c * δ

theorem horiz_eqVert (hd : 0 < d) (K : ℕ) (q δ : ℝ) (f : ℝ → Rd (d - 1)) (v : Rd (d - 1))
    (a : ℝ) (i : ℕ) : horiz (eqVert K q δ f v a i) = knot K q δ f v a i := by
  rw [eqVert, ← embedT_smul, horiz_smul_e₁_add_embedT hd]

theorem transv_eqVert (hd : 0 < d) (K : ℕ) (q δ : ℝ) (f : ℝ → Rd (d - 1)) (v : Rd (d - 1))
    (a : ℝ) (i : ℕ) :
    transv (eqVert K q δ f v a i) = δ • embedT (padProf K f v a ((i : ℝ) / K)) := by
  rw [eqVert, ← embedT_smul, transv_smul_e₁_add_embedT hd, embedT_smul]

/-- Edge vectors: `v_{i+1} - v_i = ℓ_i e₁ + δ (0, Δ_i)`. -/
theorem eqVert_succ_sub (K : ℕ) (q δ : ℝ) (f : ℝ → Rd (d - 1)) (v : Rd (d - 1)) (a : ℝ)
    (i : ℕ) :
    eqVert K q δ f v a (i + 1) - eqVert K q δ f v a i =
      hIncr q δ (incr K (padProf K f v a) i) • e₁ d +
        δ • (embedT (incr K (padProf K f v a) i) : Rd d) := by
  simp only [eqVert, knot_succ, incr, embedT_sub, Nat.cast_add, Nat.cast_one, add_smul, smul_sub]
  abel

/-- **Geometry of the equal-edge polygon** for a zero `a ∈ [0, a_f + 1]` of `S_δ - 1`. -/
theorem eqVert_equalEdgeData (hd : 0 < d) {n g : ℕ} (hg : 1 ≤ g) {e : ℝ}
    {f : ℝ → Rd (d - 1)} (hf : f ∈ Vg (Rd (d - 1)) n) (hfe : energy f ≤ e) {v : Rd (d - 1)}
    (hv : ‖v‖ = 1) (hK : √(2 * (e + 1)) + 1 ≤ ((2 ^ (n + g) : ℕ) : ℝ)) {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ * incrConst n e < 1) {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ aLim e f + 1)
    (hSa : sumHIncr (2 ^ (n + g)) (qOf (2 ^ (n + g)) (e + 1) δ) δ f v a = 1) :
    EqualEdgeData (2 ^ (n + g)) δ (qOf (2 ^ (n + g)) (e + 1) δ) (e + 1) (√e + 1)
      (√2 * incrConst n e)
      (eqVert (2 ^ (n + g)) (qOf (2 ^ (n + g)) (e + 1) δ) δ f v a) := by
  set K : ℕ := 2 ^ (n + g) with hK_def
  have hKpos : 0 < K := by positivity
  have hK' : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hKe : Even K := (Nat.even_pow' (by omega)).2 even_two
  set q := qOf K (e + 1) δ with hq_def
  set c := incrConst n e with hc
  have hc1 : 1 ≤ c := one_le_incrConst n e
  have hE0 := Var.energy_nonneg f
  have he : 0 ≤ e := hE0.trans hfe
  have hδ2 : 0 ≤ δ ^ 2 * (e + 1) := by positivity
  have hq1 : 1 / (K : ℝ) ≤ q := by
    rw [hq_def, qOf]
    exact div_le_div_of_nonneg_right (by linarith) hK'.le
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq1
  have hKq : (K : ℝ) * q = 1 + δ ^ 2 * (e + 1) := by
    rw [hq_def, qOf]; field_simp
  have hδc2 : δ ^ 2 * c ^ 2 < 1 := by
    have h0 : 0 ≤ δ * c := by positivity
    have : (δ * c) ^ 2 < 1 := pow_lt_one₀ h0 hδc two_ne_zero
    calc δ ^ 2 * c ^ 2 = (δ * c) ^ 2 := by ring
      _ < 1 := this
  set Δ : ℕ → Rd (d - 1) := fun i => incr K (padProf K f v a) i with hΔ
  have hrad : ∀ i < K, δ ^ 2 * ‖Δ i‖ ^ 2 ≤ δ ^ 2 * c ^ 2 * q ^ 2 := fun i hi =>
    radicand_le hf hfe hv ha0 ha hi hq1
  have hrad' : ∀ i < K, δ ^ 2 * ‖Δ i‖ ^ 2 < q ^ 2 := by
    intro i hi
    have h1 := hrad i hi
    have hq2 : 0 < q ^ 2 := by positivity
    have h2 : δ ^ 2 * c ^ 2 * q ^ 2 < 1 * q ^ 2 := mul_lt_mul_of_pos_right hδc2 hq2
    linarith
  have hsq : ∀ i < K, hIncr q δ (Δ i) ^ 2 + δ ^ 2 * ‖Δ i‖ ^ 2 = q ^ 2 := by
    intro i hi
    rw [hIncr_sq (hrad' i hi).le]
    ring
  have hedge : ∀ i, eqVert K q δ f v a (i + 1) - eqVert K q δ f v a i =
      hIncr q δ (Δ i) • e₁ d + embedT (δ • Δ i) := by
    intro i
    rw [eqVert_succ_sub, embedT_smul]
  have hnormsq : ∀ i < K, ‖eqVert K q δ f v a (i + 1) - eqVert K q δ f v a i‖ ^ 2 = q ^ 2 := by
    intro i hi
    rw [hedge, norm_sq_smul_e₁_add_embedT hd, norm_smul, Real.norm_eq_abs, abs_of_pos hδ,
      mul_pow, ← hsq i hi]
  have hpad0 : padProf K f v a 0 = 0 := by
    simp [padProf, hf.1, psiK_zero]
  have hpad1 : padProf K f v a 1 = 0 := by
    simp [padProf, hf.2.1, psiK_one hKe]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- start
    simp only [eqVert, knot_zero, zero_smul, Nat.cast_zero, zero_div, hpad0, embedT_zero,
      smul_zero, add_zero]
  · -- finish
    simp only [eqVert]
    rw [knot_self, hSa, div_self hK'.ne', hpad1, embedT_zero, smul_zero, add_zero, one_smul]
  · -- edge lengths
    intro i hi
    have h := hnormsq i hi
    exact (pow_left_inj₀ (norm_nonneg _) hq0.le two_ne_zero).mp h
  · -- forward
    intro i hi
    rw [horiz_eqVert hd, horiz_eqVert hd, knot_succ]
    have := hIncr_pos (hrad' i hi)
    linarith
  · -- knots
    intro i hi
    rw [horiz_eqVert hd]
    have hi' : (i : ℝ) ≤ K := by exact_mod_cast hi
    have hupper : knot K q δ f v a i ≤ i * q := by
      unfold knot
      calc ∑ k ∈ Finset.range i, hIncr q δ (incr K (padProf K f v a) k)
          ≤ ∑ _k ∈ Finset.range i, q := Finset.sum_le_sum fun k _ => hIncr_le hq0.le _
        _ = i * q := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hdef : ∑ k ∈ Finset.range K, (q - hIncr q δ (Δ k)) = δ ^ 2 * (e + 1) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have : ∑ k ∈ Finset.range K, hIncr q δ (Δ k) = 1 := hSa
      rw [this, hKq]
      ring
    have hlower : i * q - δ ^ 2 * (e + 1) ≤ knot K q δ f v a i := by
      have hsub : ∑ k ∈ Finset.range i, (q - hIncr q δ (Δ k)) ≤
          ∑ k ∈ Finset.range K, (q - hIncr q δ (Δ k)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hi)
          (fun k _ _ => sub_nonneg.2 (hIncr_le hq0.le _))
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hdef]
        at hsub
      unfold knot
      linarith
    have hiq : (i : ℝ) * q = i / K + (i / K) * (δ ^ 2 * (e + 1)) := by
      rw [hq_def, qOf]; field_simp
    have hfrac : (i : ℝ) / K ≤ 1 := by rw [div_le_one hK']; exact hi'
    have hfrac0 : 0 ≤ (i : ℝ) / K := by positivity
    have hmul : (i / K : ℝ) * (δ ^ 2 * (e + 1)) ≤ δ ^ 2 * (e + 1) := by nlinarith
    have hmul0 : 0 ≤ (i / K : ℝ) * (δ ^ 2 * (e + 1)) := mul_nonneg hfrac0 hδ2
    rw [abs_le]
    constructor <;> linarith
  · -- transverse
    intro i hi
    rw [transv_eqVert hd, norm_smul, norm_embedT, Real.norm_eq_abs, abs_of_pos hδ, mul_comm]
    gcongr
    have hf' : f ∈ Vg (Rd (d - 1)) (n + g) := Var.Vg_mono (by omega) hf
    have h1 : ‖f ((i : ℝ) / K)‖ ≤ √e :=
      (norm_node_le hK_def hf' hi).trans (Real.sqrt_le_sqrt hfe)
    have h2 : ‖(a * psiK K ((i : ℝ) / K)) • v‖ ≤ 1 := by
      rw [norm_smul, hv, mul_one, Real.norm_eq_abs, abs_mul, abs_of_nonneg ha0]
      have hps := abs_psiK_le K ((i : ℝ) / K)
      have hA : aLim e f + 1 ≤ K := by linarith [aLim_le f e]
      calc a * |psiK K ((i : ℝ) / K)| ≤ (aLim e f + 1) * (1 / K) :=
            mul_le_mul ha hps (abs_nonneg _) (by linarith [one_le_aLim hfe])
        _ ≤ K * (1 / K) := by gcongr
        _ = 1 := by field_simp
    calc ‖padProf K f v a ((i : ℝ) / K)‖
        ≤ ‖f ((i : ℝ) / K)‖ + ‖(a * psiK K ((i : ℝ) / K)) • v‖ := norm_add_le _ _
      _ ≤ √e + 1 := add_le_add h1 h2
  · -- angle
    intro i hi
    have hℓ := hIncr_nonneg q δ (Δ i)
    have hℓq := hIncr_le (δ := δ) hq0.le (Δ i)
    have hw : q⁻¹ • (eqVert K q δ f v a (i + 1) - eqVert K q δ f v a i) - e₁ d =
        (q⁻¹ * hIncr q δ (Δ i) - 1) • e₁ d + embedT (q⁻¹ • (δ • Δ i)) := by
      rw [hedge, smul_add, ← embedT_smul, smul_smul, sub_smul, one_smul]
      abel
    have hnorm2 : ‖q⁻¹ • (eqVert K q δ f v a (i + 1) - eqVert K q δ f v a i) - e₁ d‖ ^ 2 =
        2 - 2 * (q⁻¹ * hIncr q δ (Δ i)) := by
      rw [hw, norm_sq_smul_e₁_add_embedT hd, norm_smul, norm_smul, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos hδ, abs_inv, abs_of_pos hq0]
      have h := hsq i hi
      have hq' : q ≠ 0 := hq0.ne'
      calc (q⁻¹ * hIncr q δ (Δ i) - 1) ^ 2 + (q⁻¹ * (δ * ‖Δ i‖)) ^ 2
          = q⁻¹ ^ 2 * (hIncr q δ (Δ i) ^ 2 + δ ^ 2 * ‖Δ i‖ ^ 2) -
              2 * (q⁻¹ * hIncr q δ (Δ i)) + 1 := by ring
        _ = 2 - 2 * (q⁻¹ * hIncr q δ (Δ i)) := by
            rw [h]; field_simp; ring
    have hbound : 2 - 2 * (q⁻¹ * hIncr q δ (Δ i)) ≤ (√2 * c * δ) ^ 2 := by
      have h := hsq i hi
      have hr := hrad i hi
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      -- `2 - 2ℓ/q ≤ 2(q² - ℓ²)/q² = 2δ²‖Δ‖²/q² ≤ 2δ²c²`
      have hq2 : 0 < q ^ 2 := by positivity
      have key : 2 - 2 * (q⁻¹ * hIncr q δ (Δ i)) ≤ 2 * (δ ^ 2 * ‖Δ i‖ ^ 2) / q ^ 2 := by
        rw [le_div_iff₀ hq2]
        have : (2 - 2 * (q⁻¹ * hIncr q δ (Δ i))) * q ^ 2 = 2 * q ^ 2 - 2 * q * hIncr q δ (Δ i) := by
          field_simp
        rw [this]
        have h5 := mul_nonneg hℓ (sub_nonneg.2 hℓq)
        linarith
      have key2 : 2 * (δ ^ 2 * ‖Δ i‖ ^ 2) / q ^ 2 ≤ 2 * c ^ 2 * δ ^ 2 := by
        rw [div_le_iff₀ hq2]
        linarith
      linarith
    have hpos : 0 ≤ √2 * c * δ := by positivity
    calc ‖q⁻¹ • (eqVert K q δ f v a (i + 1) - eqVert K q δ f v a i) - e₁ d‖
        = √(‖q⁻¹ • (eqVert K q δ f v a (i + 1) - eqVert K q δ f v a i) - e₁ d‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ √((√2 * c * δ) ^ 2) := Real.sqrt_le_sqrt (by rw [hnorm2]; exact hbound)
      _ = √2 * c * δ := Real.sqrt_sq hpos

/-- **Lemma 5.1** (source §5.1; HA4 D1 with explicit constants).

Let `f ∈ V_n(ℝ^{d-1})` with `E(f) ≤ e`, let `v ∈ ℝ^{d-1}` be a unit vector, and let
`K = 2^{n+g}` with `g ≥ 1` and `K ≥ (2(e+1))^{1/2} + 1`. Put `E₀ = e + 1`,
`q_δ = (1 + δ²E₀)/K`, `a_f = (2(E₀ - E(f)))^{1/2}` and `c₁ = (2e2ⁿ)^{1/2} + (2E₀)^{1/2} + 1`.
There are `δ₁ > 0` and amplitudes `a_{f,δ}` with `a_{f,δ} → a_f` as `δ ↓ 0` such that for
`0 < δ < δ₁`: `a_{f,δ}` is the unique zero in `(0, a_f + 1)` of `S_δ - 1`; the polygon
`eqVert` with amplitude `a_{f,δ}` satisfies `EqualEdgeData` with `M₀ = √e + 1` and angle
constant `√2 c₁`; and its transverse vertices are `δ (f + a_{f,δ} ψ_K v)(i/K)`. -/
theorem lemma51 (hd : 0 < d) {n g : ℕ} (hg : 1 ≤ g) {e : ℝ} {f : ℝ → Rd (d - 1)}
    (hf : f ∈ Vg (Rd (d - 1)) n) (hfe : energy f ≤ e) {v : Rd (d - 1)} (hv : ‖v‖ = 1)
    (hK : √(2 * (e + 1)) + 1 ≤ ((2 ^ (n + g) : ℕ) : ℝ)) :
    ∃ δ₁ > 0, ∃ a : ℝ → ℝ, Tendsto a (𝓝[>] 0) (𝓝 (aLim e f)) ∧
      ∀ δ ∈ Ioo 0 δ₁,
        a δ ∈ Ioo 0 (aLim e f + 1) ∧
        sumHIncr (2 ^ (n + g)) (qOf (2 ^ (n + g)) (e + 1) δ) δ f v (a δ) = 1 ∧
        (∀ b ∈ Ioo 0 (aLim e f + 1),
          sumHIncr (2 ^ (n + g)) (qOf (2 ^ (n + g)) (e + 1) δ) δ f v b = 1 → b = a δ) ∧
        EqualEdgeData (2 ^ (n + g)) δ (qOf (2 ^ (n + g)) (e + 1) δ) (e + 1) (√e + 1)
          (√2 * incrConst n e)
          (eqVert (2 ^ (n + g)) (qOf (2 ^ (n + g)) (e + 1) δ) δ f v (a δ)) ∧
        ∀ i ≤ 2 ^ (n + g),
          transv (eqVert (2 ^ (n + g)) (qOf (2 ^ (n + g)) (e + 1) δ) δ f v (a δ) i) =
            δ • embedT (f ((i : ℝ) / ((2 ^ (n + g) : ℕ) : ℝ)) +
              (a δ * psiK (2 ^ (n + g)) ((i : ℝ) / ((2 ^ (n + g) : ℕ) : ℝ))) • v) := by
  set c := incrConst n e with hc
  have hc1 : 1 ≤ c := one_le_incrConst n e
  have hE0 := Var.energy_nonneg f
  have he : 0 ≤ e := hE0.trans hfe
  set E₀ := e + 1 with hE₀
  have hE₀1 : 1 ≤ E₀ := by linarith
  -- the smallness threshold
  set δ₁ := min (1 / (2 * c ^ 2)) (1 / (2 * E₀)) with hδ₁
  have hδ₁pos : 0 < δ₁ := lt_min (by positivity) (by positivity)
  have hsmall : ∀ δ ∈ Ioo 0 δ₁, δ ^ 2 * c ^ 2 ≤ 1 ∧ δ ^ 2 * E₀ ≤ 1 ∧ δ ^ 2 * c ^ 4 < 1 ∧
      δ ^ 2 * E₀ ^ 2 < 1 ∧ δ * c < 1 := by
    intro δ hδ
    have h1 : δ < 1 / (2 * c ^ 2) := lt_of_lt_of_le hδ.2 (min_le_left _ _)
    have h2 : δ < 1 / (2 * E₀) := lt_of_lt_of_le hδ.2 (min_le_right _ _)
    have hc2 : 1 ≤ c ^ 2 := by nlinarith
    have h1' : δ * (2 * c ^ 2) < 1 := by rwa [lt_div_iff₀ (by positivity)] at h1
    have h2' : δ * (2 * E₀) < 1 := by rwa [lt_div_iff₀ (by positivity)] at h2
    have hδ0 := hδ.1
    have hδ1 : δ < 1 := by nlinarith
    have hδc : δ * c ^ 2 < 1 / 2 := by linarith
    have hδE : δ * E₀ < 1 / 2 := by linarith
    have hδc0 : 0 ≤ δ * c ^ 2 := by positivity
    have hδE0 : 0 ≤ δ * E₀ := by positivity
    have hc0 : 0 ≤ c := by linarith
    have e1 : δ ^ 2 * c ^ 4 = (δ * c ^ 2) ^ 2 := by ring
    have e2 : δ ^ 2 * E₀ ^ 2 = (δ * E₀) ^ 2 := by ring
    have e3 : δ ^ 2 * c ^ 2 = δ * (δ * c ^ 2) := by ring
    have e4 : δ ^ 2 * E₀ = δ * (δ * E₀) := by ring
    have hcc : δ * c ≤ δ * c ^ 2 := by nlinarith
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [e3]; nlinarith
    · rw [e4]; nlinarith
    · rw [e1]; nlinarith
    · rw [e2]; nlinarith
    · linarith
  have hex : ∀ δ ∈ Ioo 0 δ₁, ∃ a ∈ Ioo 0 (aLim e f + 1),
      sumHIncr (2 ^ (n + g)) (qOf (2 ^ (n + g)) E₀ δ) δ f v a = 1 ∧
      ∀ b ∈ Ioo 0 (aLim e f + 1),
        sumHIncr (2 ^ (n + g)) (qOf (2 ^ (n + g)) E₀ δ) δ f v b = 1 → b = a := by
    intro δ hδ
    obtain ⟨h1, h2, h3, h4, -⟩ := hsmall δ hδ
    exact exists_unique_sumHIncr_eq_one hg hf hfe hv hδ.1 h1 h2 h3 h4
  classical
  let a : ℝ → ℝ := fun δ => if h : δ ∈ Ioo 0 δ₁ then (hex δ h).choose else aLim e f
  have ha_spec : ∀ δ (h : δ ∈ Ioo 0 δ₁), a δ ∈ Ioo 0 (aLim e f + 1) ∧
      sumHIncr (2 ^ (n + g)) (qOf (2 ^ (n + g)) E₀ δ) δ f v (a δ) = 1 ∧
      ∀ b ∈ Ioo 0 (aLim e f + 1),
        sumHIncr (2 ^ (n + g)) (qOf (2 ^ (n + g)) E₀ δ) δ f v b = 1 → b = a δ := by
    intro δ h
    have ha : a δ = (hex δ h).choose := dite_eq_left h
    rw [ha]
    exact (hex δ h).choose_spec
  refine ⟨δ₁, hδ₁pos, a, ?_, fun δ hδ => ?_⟩
  · -- convergence `a_{f,δ} → a_f`
    rw [Metric.tendsto_nhds]
    intro η hη
    set η' := min η 1 with hη'
    have hη'0 : 0 < η' := lt_min hη one_pos
    have hη'1 : η' ≤ 1 := min_le_right _ _
    have hη'η : η' ≤ η := min_le_left _ _
    -- a threshold `δ₂` for the localization conditions
    set δ₂ := min δ₁ (min (η' / (2 * (c ^ 4 + 1))) (η' / (E₀ ^ 2 + 1))) with hδ₂
    have hδ₂pos : 0 < δ₂ := lt_min hδ₁pos (lt_min (by positivity) (by positivity))
    filter_upwards [Ioo_mem_nhdsGT hδ₂pos] with δ hδ
    have hδ1 : δ ∈ Ioo 0 δ₁ := ⟨hδ.1, lt_of_lt_of_le hδ.2 (min_le_left _ _)⟩
    obtain ⟨h1, h2, -, -, -⟩ := hsmall δ hδ1
    have hδ0 := hδ.1
    have hδlt1 : δ < 1 := by
      have : δ₁ ≤ 1 / (2 * E₀) := min_le_right _ _
      have : 1 / (2 * E₀) ≤ 1 / 2 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num); linarith
      linarith [hδ1.2]
    have hδa : δ < η' / (2 * (c ^ 4 + 1)) :=
      lt_of_lt_of_le hδ.2 ((min_le_right _ _).trans (min_le_left _ _))
    have hδb : δ < η' / (E₀ ^ 2 + 1) :=
      lt_of_lt_of_le hδ.2 ((min_le_right _ _).trans (min_le_right _ _))
    have hc4 : δ ^ 2 * c ^ 4 < η' / 2 := by
      rw [lt_div_iff₀ (by positivity)] at hδa
      have : δ ^ 2 ≤ δ := by nlinarith
      nlinarith [pow_nonneg (le_trans zero_le_one hc1) 4]
    have hE2 : δ ^ 2 * E₀ ^ 2 < η' := by
      rw [lt_div_iff₀ (by positivity)] at hδb
      have : δ ^ 2 ≤ δ := by nlinarith
      nlinarith [sq_nonneg E₀]
    obtain ⟨hmem, hS, -⟩ := ha_spec δ hδ1
    have := abs_sub_aLim_lt hg hf hfe hv hδ0 h1 h2 hη'0 hη'1 hc4 hE2 hmem hS
    rw [Real.dist_eq]
    linarith
  · obtain ⟨hmem, hS, huniq⟩ := ha_spec δ hδ
    obtain ⟨-, -, -, -, h5⟩ := hsmall δ hδ
    refine ⟨hmem, hS, huniq, ?_, fun i _ => ?_⟩
    · exact eqVert_equalEdgeData hd hg hf hfe hv hK hδ.1 h5 hmem.1.le hmem.2.le hS
    · rw [transv_eqVert hd]
      rfl

end HigherDimLFPP.Lower
