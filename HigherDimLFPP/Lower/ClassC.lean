import HigherDimLFPP.Lower.EqualEdge

/-!
# The class `C_δ` in distribution-function form (source §5.2, Lemma 5.3, Steps 1–3)

Packet P-L1, target T3 (ruling H6; audit HA4, "Details for later use" D3 and D6, findings
HA4-3 and HA4-10). All statements are deterministic.

**Distribution-function form of `W∞`** (HA4 D3). For a distribution function `F` on `ℝ`,
`W∞(σ, 𝓛) ≤ r` (with `𝓛` the uniform law on `[0,1]`) is equivalent to the sandwich
`clamp(x - r) ≤ F(x) ≤ clamp(x + r)` for all `x` (`InW r F`), `clamp = clamp01`. We work with the
sandwich throughout:

* `InW.mono`, `InW.sum` (mixtures, D3(b)), `InW.shift` (horizontal displacement, D3(c)),
  `InW.quantile_observation` (D3(d), HA4's Lean-checked `quantile_observation`), and the
  normalization estimate `abs_div_sub_le` used in (5.20).
* Finitely supported measures `μ = Σ_{z∈S} w z δ_z` (`IsFinProb`), their horizontal distribution
  function `hCDF S w`, the class `C_δ` (`InCDelta`, (5.12)–(5.13)), and `V_δ` (`Vdelta`).
  `InCDelta.mem_Vdelta`: the support of `μ ∈ C_δ` lies in `V_δ` (the horizontal part of the
  support condition follows from the sandwich).
* `polyCDF_inW`: the horizontal distribution function of normalized arclength on a forward
  polygon whose knots are within `ρ` of the uniform mesh lies in `W(ρ)` (D3(c), "`(ν_j)_x ∈
  W(δ²E₀)` by D1").
* `pushCDF_bounds`, `replCDF_inW`: **(5.18)**. For `μ ∈ C_δ`-type data and the edge similarities
  of an equal-edge polygon, the horizontal distribution function of
  `ν_{j,μ} = K⁻¹ Σ_i (T_i)_* μ` lies in `W(δ²E₀ + q(r + cδm))` (`r = Bδ²`, `m = Mδ` give
  `δ²(E₀ + q(B + cM))`); no coupling or disintegration is needed.
* `horiz_edgeSim_mem`, `norm_transv_edgeSim_le`, `edgeSim_mapsTo_Vdelta`, `Vdelta_subset_cube`:
  **Step 3**, `T_i(V_δ) ⊆ V_δ ⊆ U`, and the horizontal support of `Tμ` used with the quantile
  observation in Step 2.
* `refMeasure_inCDelta`: the reference measure `ν₀^N = N⁻¹ Σ_{l<N} δ_{(l/N) e₁}` lies in `C_δ`
  when `1/N ≤ Bδ²` (HA4 D7, start of the iteration).
* `hCDF_image_imgW`: horizontal distribution function of an image measure with collected weights
  (bookkeeping for the tilted replacement `Tμ`).

2D source: none (the 2D proof uses the uniform-in-`μ` Lemma 5.1 and no class `C_δ`).
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Lower

/-! ## Clamping to `[0,1]` -/

/-- `clamp(x) = max(0, min(1, x))`, the distribution function of the uniform law on `[0,1]`. -/
def clamp01 (x : ℝ) : ℝ := max 0 (min 1 x)

theorem clamp01_nonneg (x : ℝ) : 0 ≤ clamp01 x := le_max_left _ _

theorem clamp01_le_one (x : ℝ) : clamp01 x ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem clamp01_mono : Monotone clamp01 := fun _ _ h => max_le_max le_rfl (min_le_min le_rfl h)

theorem clamp01_of_nonpos {x : ℝ} (h : x ≤ 0) : clamp01 x = 0 :=
  max_eq_left (le_trans (min_le_right _ _) h)

theorem clamp01_of_one_le {x : ℝ} (h : 1 ≤ x) : clamp01 x = 1 := by
  unfold clamp01
  rw [min_eq_left h, max_eq_right zero_le_one]

theorem clamp01_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : clamp01 x = x := by
  unfold clamp01
  rw [min_eq_right h1, max_eq_right h0]

theorem abs_sub_clamp01_le {x r : ℝ} (hr : 0 ≤ r) (hx : x ∈ Icc (-r) (1 + r)) :
    |x - clamp01 x| ≤ r := by
  rcases le_or_gt x 0 with h | h
  · rw [clamp01_of_nonpos h, sub_zero, abs_of_nonpos h]; linarith [hx.1]
  · rcases le_or_gt x 1 with h' | h'
    · rw [clamp01_of_mem h.le h', sub_self, abs_zero]; linarith [hx.1, hx.2]
    · rw [clamp01_of_one_le h'.le, abs_of_pos (by linarith)]; linarith [hx.2]

/-- Comparison of clamped values through their sublevel sets in `[0,1]`. -/
theorem clamp01_le_clamp01_of_forall {a b : ℝ}
    (h : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t ≤ a → t ≤ b) : clamp01 a ≤ clamp01 b := by
  rcases le_or_gt a 0 with ha | ha
  · rw [clamp01_of_nonpos ha]; exact clamp01_nonneg b
  · have ht0 : 0 ≤ min 1 a := le_min zero_le_one ha.le
    have ht1 : min 1 a ≤ 1 := min_le_left _ _
    have htb := h (min 1 a) ht0 ht1 (min_le_right _ _)
    have hca : clamp01 a = min 1 a := max_eq_right ht0
    rw [hca]
    calc min 1 a = min 1 (min 1 a) := (min_eq_right ht1).symm
      _ ≤ min 1 b := min_le_min le_rfl htb
      _ ≤ clamp01 b := le_max_right _ _

/-- `Σ_{i<K} clamp(y - i) = max(0, min(K, y))`. -/
theorem sum_clamp01_sub (K : ℕ) (y : ℝ) :
    ∑ i ∈ Finset.range K, clamp01 (y - i) = max 0 (min (K : ℝ) y) := by
  induction K with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero]
    exact (max_eq_left (min_le_left 0 y)).symm
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    rcases le_total y K with h | h
    · rw [clamp01_of_nonpos (by linarith), add_zero, min_eq_right h, min_eq_right (by linarith)]
    · rw [min_eq_left h, max_eq_right hK0]
      rcases le_total y (K + 1) with h' | h'
      · rw [clamp01_of_mem (by linarith) (by linarith), min_eq_right h',
          max_eq_right (by linarith)]
        ring
      · rw [clamp01_of_one_le (by linarith), min_eq_left h', max_eq_right (by linarith)]

/-- `K⁻¹ Σ_{i<K} clamp(K s - i) = clamp(s)`. -/
theorem avg_clamp01 {K : ℕ} (hK : 0 < K) (s : ℝ) :
    (1 / (K : ℝ)) * ∑ i ∈ Finset.range K, clamp01 ((K : ℝ) * s - i) = clamp01 s := by
  rw [sum_clamp01_sub]
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have h : max 0 (min (K : ℝ) ((K : ℝ) * s)) = (K : ℝ) * clamp01 s := by
    unfold clamp01
    rw [mul_max_of_nonneg _ _ hK'.le, mul_min_of_nonneg _ _ hK'.le, mul_zero, mul_one]
  rw [h]
  field_simp

/-! ## The sandwich `W(r)` -/

/-- `F ∈ W(r)`: `clamp(x - r) ≤ F(x) ≤ clamp(x + r)` for all `x`. For a distribution function
`F_σ` this is `W∞(σ, 𝓛) ≤ r` (HA4 D3(a)). -/
def InW (r : ℝ) (F : ℝ → ℝ) : Prop := ∀ x, clamp01 (x - r) ≤ F x ∧ F x ≤ clamp01 (x + r)

theorem InW.mono {r r' : ℝ} {F : ℝ → ℝ} (h : InW r F) (hr : r ≤ r') : InW r' F := fun x =>
  ⟨(clamp01_mono (by linarith)).trans (h x).1, (h x).2.trans (clamp01_mono (by linarith))⟩

/-- **Horizontal displacement** (HA4 D3(c)): if `F ∈ W(r₁)` and
`F(x - r₂) ≤ G(x) ≤ F(x + r₂)`, then `G ∈ W(r₁ + r₂)`. -/
theorem InW.shift {r₁ r₂ : ℝ} {F G : ℝ → ℝ} (hF : InW r₁ F)
    (hG : ∀ x, F (x - r₂) ≤ G x ∧ G x ≤ F (x + r₂)) : InW (r₁ + r₂) G := by
  intro x
  constructor
  · have h := (hF (x - r₂)).1
    rw [show x - r₂ - r₁ = x - (r₁ + r₂) by ring] at h
    exact h.trans (hG x).1
  · have h := (hF (x + r₂)).2
    rw [show x + r₂ + r₁ = x + (r₁ + r₂) by ring] at h
    exact (hG x).2.trans h

/-- **Mixtures** (HA4 D3(b)): `W(r)` is convex. -/
theorem InW.sum {ι : Type*} (s : Finset ι) {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i)
    (hsum : ∑ i ∈ s, p i = 1) {r : ℝ} {F : ι → ℝ → ℝ} (hF : ∀ i ∈ s, InW r (F i)) :
    InW r (fun x => ∑ i ∈ s, p i * F i x) := by
  intro x
  constructor
  · calc clamp01 (x - r) = ∑ i ∈ s, p i * clamp01 (x - r) := by
          rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ ∑ i ∈ s, p i * F i x :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hF i hi x).1 (hp i hi)
  · calc ∑ i ∈ s, p i * F i x ≤ ∑ i ∈ s, p i * clamp01 (x + r) :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hF i hi x).2 (hp i hi)
      _ = clamp01 (x + r) := by rw [← Finset.sum_mul, hsum, one_mul]

/-- **The quantile observation** (HA4 D3(d); HA4's Lean-checked `quantile_observation`): if
`F ∈ W(r)`, `G` is a distribution function that vanishes on `(-∞, -r)` and equals `1` on
`[1 + r, ∞)`, and `|G - F| ≤ η`, then `G ∈ W(r + η)`. -/
theorem InW.quantile_observation {F G : ℝ → ℝ} {r η : ℝ} (hη : 0 ≤ η) (hF : InW r F)
    (hGF : ∀ x, |G x - F x| ≤ η) (hG0 : ∀ x, 0 ≤ G x) (hG1 : ∀ x, G x ≤ 1)
    (hlow : ∀ x, x < -r → G x = 0) (hhigh : ∀ x, 1 + r ≤ x → G x = 1) : InW (r + η) G := by
  intro x
  obtain ⟨hFl, hFu⟩ := hF x
  have hG := abs_le.mp (hGF x)
  unfold clamp01 at *
  constructor
  · rcases le_or_gt (x - (r + η)) 0 with h | h
    · exact max_le (hG0 x) (le_trans (min_le_right _ _) (by linarith [hG0 x]))
    · rcases le_or_gt (1 + r) x with h' | h'
      · rw [hhigh x h']; exact max_le zero_le_one (min_le_left _ _)
      · refine max_le (hG0 x) (le_trans (min_le_right _ _) ?_)
        have e1 : min 1 (x - r) = x - r := min_eq_right (by linarith)
        rw [e1] at hFl
        have e2 : max 0 (x - r) = x - r := max_eq_right (by linarith)
        rw [e2] at hFl
        linarith
  · rcases le_or_gt 1 (x + (r + η)) with h | h
    · rw [min_eq_left h, max_eq_right zero_le_one]; exact hG1 x
    · rcases lt_or_ge x (-r) with h' | h'
      · rw [hlow x h']; exact le_max_left _ _
      · have e1 : min 1 (x + r) = x + r := min_eq_right (by linarith)
        rw [e1] at hFu
        have e2 : max 0 (x + r) = x + r := max_eq_right (by linarith)
        rw [e2] at hFu
        rw [min_eq_right h.le]
        exact le_trans (by linarith) (le_max_right _ _)

/-- **Normalization** in (5.20): if `|W - F| ≤ η`, `|m - 1| ≤ η`, `0 ≤ F ≤ 1` and `m ≥ 2/3`,
then `|W/m - F| ≤ 3η`. -/
theorem abs_div_sub_le {W F m η : ℝ} (hWF : |W - F| ≤ η) (hm : |m - 1| ≤ η) (hF0 : 0 ≤ F)
    (hF1 : F ≤ 1) (hm23 : 2 / 3 ≤ m) : |W / m - F| ≤ 3 * η := by
  have hm0 : 0 < m := by linarith
  have hη : 0 ≤ η := (abs_nonneg _).trans hWF
  have h1 : W / m - F = (W - F + F * (1 - m)) / m := by field_simp; ring
  rw [h1, abs_div, abs_of_pos hm0, div_le_iff₀ hm0]
  have h2 : |F * (1 - m)| ≤ η := by
    rw [abs_mul, abs_of_nonneg hF0, abs_sub_comm]
    calc F * |m - 1| ≤ 1 * |m - 1| := mul_le_mul_of_nonneg_right hF1 (abs_nonneg _)
      _ ≤ η := by rw [one_mul]; exact hm
  calc |W - F + F * (1 - m)| ≤ |W - F| + |F * (1 - m)| := abs_add_le _ _
    _ ≤ 2 * η := by linarith
    _ ≤ 3 * η * m := by nlinarith

/-! ## Finitely supported measures and the class `C_δ` -/

variable {d : ℕ}

/-- `μ = Σ_{z∈S} w z δ_z` is a probability measure. -/
def IsFinProb (S : Finset (Rd d)) (w : Rd d → ℝ) : Prop := (∀ z ∈ S, 0 ≤ w z) ∧ ∑ z ∈ S, w z = 1

/-- Horizontal distribution function `x ↦ μ{z₁ ≤ x}` of `μ = Σ_{z∈S} w z δ_z`. -/
def hCDF (S : Finset (Rd d)) (w : Rd d → ℝ) (x : ℝ) : ℝ :=
  ∑ z ∈ S.filter (fun z => horiz z ≤ x), w z

/-- Horizontal distribution function of the image measure `φ_* μ`. -/
def pushCDF (S : Finset (Rd d)) (w : Rd d → ℝ) (φ : Rd d → Rd d) (x : ℝ) : ℝ :=
  ∑ z ∈ S.filter (fun z => horiz (φ z) ≤ x), w z

/-- `W∞(μ_x, 𝓛) ≤ r`, in distribution-function form. -/
def HorizW (S : Finset (Rd d)) (w : Rd d → ℝ) (r : ℝ) : Prop := InW r (hCDF S w)

/-- `V_δ = [-Bδ², 1 + Bδ²] × {|y| ≤ Mδ}` (5.12). -/
def Vdelta (δ M B : ℝ) : Set (Rd d) :=
  {z | horiz z ∈ Icc (-(B * δ ^ 2)) (1 + B * δ ^ 2) ∧ ‖transv z‖ ≤ M * δ}

/-- The class `C_δ` (5.12)–(5.13), finitely supported version, in distribution-function form:
probability measures whose atoms have transverse part `≤ Mδ` and whose horizontal marginal is in
`W(Bδ²)`. (The horizontal support condition follows, `InCDelta.mem_Vdelta`.) -/
def InCDelta (δ M B : ℝ) (S : Finset (Rd d)) (w : Rd d → ℝ) : Prop :=
  IsFinProb S w ∧ (∀ z ∈ S, w z ≠ 0 → ‖transv z‖ ≤ M * δ) ∧ HorizW S w (B * δ ^ 2)

theorem hCDF_eq_sum_ite (S : Finset (Rd d)) (w : Rd d → ℝ) (x : ℝ) :
    hCDF S w x = ∑ z ∈ S, if horiz z ≤ x then w z else 0 :=
  Finset.sum_filter _ _

theorem pushCDF_eq_sum_ite (S : Finset (Rd d)) (w : Rd d → ℝ) (φ : Rd d → Rd d) (x : ℝ) :
    pushCDF S w φ x = ∑ z ∈ S, if horiz (φ z) ≤ x then w z else 0 :=
  Finset.sum_filter _ _

theorem hCDF_mono {S : Finset (Rd d)} {w : Rd d → ℝ} (hw : ∀ z ∈ S, 0 ≤ w z) :
    Monotone (hCDF S w) := by
  intro x y hxy
  rw [hCDF_eq_sum_ite, hCDF_eq_sum_ite]
  refine Finset.sum_le_sum fun z hz => ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h1.trans hxy) h2
  · exact hw z hz
  · exact le_rfl

/-- **Horizontal support** of `μ ∈ W(r)`: atoms of positive weight have `z₁ ∈ [-r, 1 + r]`. -/
theorem horiz_mem_of_horizW {S : Finset (Rd d)} {w : Rd d → ℝ} (hμ : IsFinProb S w) {r : ℝ}
    (hW : HorizW S w r) {z : Rd d} (hz : z ∈ S) (hwz : w z ≠ 0) :
    horiz z ∈ Icc (-r) (1 + r) := by
  have hw0 : 0 < w z := lt_of_le_of_ne (hμ.1 z hz) (Ne.symm hwz)
  constructor
  · by_contra hcon
    push Not at hcon
    have h1 : w z ≤ hCDF S w (horiz z) := by
      unfold hCDF
      exact Finset.single_le_sum (f := w) (fun z' hz' => hμ.1 z' (Finset.mem_filter.1 hz').1)
        (Finset.mem_filter.2 ⟨hz, le_rfl⟩)
    have h2 := (hW (horiz z)).2
    rw [clamp01_of_nonpos (by linarith)] at h2
    linarith
  · by_contra hcon
    push Not at hcon
    have h1 := (hW (1 + r)).1
    rw [show 1 + r - r = 1 by ring, clamp01_of_one_le le_rfl] at h1
    have h2 : hCDF S w (1 + r) ≤ ∑ z' ∈ S.erase z, w z' := by
      unfold hCDF
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun z' hz' _ => hμ.1 z'
        (Finset.mem_of_mem_erase hz')
      intro z' hz'
      rw [Finset.mem_filter] at hz'
      refine Finset.mem_erase.2 ⟨?_, hz'.1⟩
      rintro rfl
      linarith [hz'.2]
    have h3 : ∑ z' ∈ S.erase z, w z' = 1 - w z := by
      rw [← hμ.2, ← Finset.add_sum_erase S w hz]
      ring
    linarith

/-- The support of `μ ∈ C_δ` lies in `V_δ`. -/
theorem InCDelta.mem_Vdelta {δ M B : ℝ} {S : Finset (Rd d)} {w : Rd d → ℝ}
    (h : InCDelta δ M B S w) {z : Rd d} (hz : z ∈ S) (hwz : w z ≠ 0) : z ∈ Vdelta δ M B :=
  ⟨horiz_mem_of_horizW h.1 h.2.2 hz hwz, h.2.1 z hz hwz⟩

/-! ## The horizontal distribution function of a forward polygon -/

/-- Horizontal distribution function of normalized arclength on a polygon with `K` edges of
equal length and horizontal knots `x 0 < ⋯ < x K`: `K⁻¹ Σ_i clamp((t - x_i)/(x_{i+1} - x_i))`. -/
def polyCDF (K : ℕ) (x : ℕ → ℝ) (t : ℝ) : ℝ :=
  (1 / (K : ℝ)) * ∑ i ∈ Finset.range K, clamp01 ((t - x i) / (x (i + 1) - x i))

/-- **`(ν_j)_x ∈ W(ρ)`** when the knots are within `ρ` of the uniform mesh (HA4 D3(c)). -/
theorem polyCDF_inW {K : ℕ} (hK : 0 < K) {x : ℕ → ℝ} (hinc : ∀ i < K, x i < x (i + 1)) {ρ : ℝ}
    (hknot : ∀ i ≤ K, |x i - i / K| ≤ ρ) : InW ρ (polyCDF K x) := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  intro t
  constructor
  · rw [← avg_clamp01 hK (t - ρ), polyCDF]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) (by positivity)
    have hi' := Finset.mem_range.1 hi
    have hℓ : 0 < x (i + 1) - x i := sub_pos.2 (hinc i hi')
    have h1 := abs_le.1 (hknot i hi'.le)
    have h2 := abs_le.1 (hknot (i + 1) hi')
    refine clamp01_le_clamp01_of_forall fun s hs0 hs1 hs => ?_
    rw [le_div_iff₀ hℓ]
    have hs' : ((i : ℝ) + s) / K ≤ t - ρ := by
      rw [div_le_iff₀ hK']; linarith
    have e1 : (i : ℝ) / K + s / K = ((i : ℝ) + s) / K := by ring
    push_cast at h2
    have e2 : ((i : ℝ) + 1) / K = (i : ℝ) / K + 1 / K := by ring
    have h3 : s * (x (i + 1) - (i : ℝ) / K - 1 / K) ≤ s * ρ :=
      mul_le_mul_of_nonneg_left (by linarith) hs0
    have h4 : (1 - s) * (x i - (i : ℝ) / K) ≤ (1 - s) * ρ :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e3 : s * (1 / K) = s / K := by ring
    nlinarith
  · rw [← avg_clamp01 hK (t + ρ), polyCDF]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) (by positivity)
    have hi' := Finset.mem_range.1 hi
    have hℓ : 0 < x (i + 1) - x i := sub_pos.2 (hinc i hi')
    have h1 := abs_le.1 (hknot i hi'.le)
    have h2 := abs_le.1 (hknot (i + 1) hi')
    refine clamp01_le_clamp01_of_forall fun s hs0 hs1 hs => ?_
    rw [le_div_iff₀ hℓ] at hs
    push_cast at h2
    have h3 : s * ((i : ℝ) / K + 1 / K - ρ) ≤ s * x (i + 1) :=
      mul_le_mul_of_nonneg_left (by
        have : ((i : ℝ) + 1) / K = (i : ℝ) / K + 1 / K := by ring
        linarith) hs0
    have h4 : (1 - s) * ((i : ℝ) / K - ρ) ≤ (1 - s) * x i :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h5 : ((i : ℝ) + s) / K - ρ ≤ t := by
      have e : ((i : ℝ) + s) / K = (1 - s) * ((i : ℝ) / K) + s * ((i : ℝ) / K + 1 / K) := by
        field_simp; ring
      nlinarith
    have h6 : (i : ℝ) + s ≤ K * (t + ρ) := by
      have := (div_le_iff₀ hK').1 (show ((i : ℝ) + s) / K ≤ t + ρ by linarith)
      linarith
    linarith

/-! ## (5.18): the horizontal marginal of `ν_{j,μ}` -/

/-- Image of an atom under a similarity, horizontally: for `O e₁ = u`, `‖u - e₁‖ ≤ θ` and
`‖z_⊥‖ ≤ m`, `|(Tz)₁ - (b₁ + r u₁ z₁)| ≤ r θ m`. -/
theorem abs_horiz_app_sub_le (hd : 0 < d) (T : SimD d) {u : Rd d} (hu : T.O (e₁ d) = u)
    {θ : ℝ} (hθ : ‖u - e₁ d‖ ≤ θ) (hr : 0 ≤ T.r) {m : ℝ} {z : Rd d} (hz : ‖transv z‖ ≤ m) :
    |horiz (T.app z) - (horiz T.b + T.r * horiz u * horiz z)| ≤ T.r * (θ * m) := by
  have h := abs_horiz_map_sub_le hd T.O hu hθ z
  have hθ0 : 0 ≤ θ := (norm_nonneg _).trans hθ
  have e : horiz (T.app z) - (horiz T.b + T.r * horiz u * horiz z) =
      T.r * (horiz (T.O z) - horiz z * horiz u) := by
    rw [SimD.app_def, horiz_add, horiz_smul]; ring
  rw [e, abs_mul, abs_of_nonneg hr]
  exact mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left hz hθ0)) hr

/-- **Horizontal marginal of a pushforward** (Lemma 5.3, Step 1, one edge). If `μ ∈ W(r)` has
atoms with `‖z_⊥‖ ≤ m`, and `T` is a similarity of ratio `q > 0` whose frame sends `e₁` to a
unit vector `u` with `‖u - e₁‖ ≤ θ` and `u₁ > 0`, then, with `ℓ = q u₁` and `x₀ = (T 0)₁`,
`clamp((t - q(r + θm) - x₀)/ℓ) ≤ (T_*μ){z₁ ≤ t} ≤ clamp((t + q(r + θm) - x₀)/ℓ)`. -/
theorem pushCDF_bounds (hd : 0 < d) {S : Finset (Rd d)} {w : Rd d → ℝ}
    (hw : ∀ z ∈ S, 0 ≤ w z) {r : ℝ} (hr : 0 ≤ r) (hW : HorizW S w r) {m : ℝ}
    (htr : ∀ z ∈ S, w z ≠ 0 → ‖transv z‖ ≤ m) (T : SimD d) {u : Rd d} (hu1 : ‖u‖ = 1)
    (hu : T.O (e₁ d) = u) {θ : ℝ} (hθ : ‖u - e₁ d‖ ≤ θ) (hq : 0 < T.r) (hℓ : 0 < horiz u)
    (t : ℝ) :
    clamp01 ((t - T.r * (r + θ * m) - horiz T.b) / (T.r * horiz u)) ≤ pushCDF S w T.app t ∧
      pushCDF S w T.app t ≤ clamp01 ((t + T.r * (r + θ * m) - horiz T.b) / (T.r * horiz u)) := by
  set L := T.r * horiz u with hL
  have hL0 : 0 < L := mul_pos hq hℓ
  have hu_le : horiz u ≤ 1 := by
    have := abs_horiz_le u hd
    rw [hu1] at this
    exact (le_abs_self _).trans this
  have hLq : L ≤ T.r := by
    calc L = T.r * horiz u := rfl
      _ ≤ T.r * 1 := mul_le_mul_of_nonneg_left hu_le hq.le
      _ = T.r := mul_one _
  have hrL : r ≤ T.r * r / L := by
    rw [le_div_iff₀ hL0]
    nlinarith
  have key : ∀ z ∈ S, w z ≠ 0 →
      |horiz (T.app z) - (horiz T.b + L * horiz z)| ≤ T.r * (θ * m) := fun z hz hwz =>
    abs_horiz_app_sub_le hd T hu hθ hq.le (htr z hz hwz)
  constructor
  · -- lower bound
    have hcmp : hCDF S w ((t - T.r * (θ * m) - horiz T.b) / L) ≤ pushCDF S w T.app t := by
      rw [hCDF_eq_sum_ite, pushCDF_eq_sum_ite]
      refine Finset.sum_le_sum fun z hz => ?_
      by_cases hwz : w z = 0
      · simp [hwz]
      · split_ifs with h1 h2
        · exact le_rfl
        · exfalso
          have hk := abs_le.1 (key z hz hwz)
          have h1' : L * horiz z ≤ t - T.r * (θ * m) - horiz T.b := by
            have := (le_div_iff₀ hL0).1 h1
            linarith
          exact h2 (by linarith [hk.2])
        · exact hw z hz
        · exact le_rfl
    have hlow := (hW ((t - T.r * (θ * m) - horiz T.b) / L)).1
    refine le_trans ?_ (hlow.trans hcmp)
    apply clamp01_mono
    have : (t - T.r * (r + θ * m) - horiz T.b) / L =
        (t - T.r * (θ * m) - horiz T.b) / L - T.r * r / L := by ring
    rw [this]
    linarith
  · -- upper bound
    set s := (t + T.r * (θ * m) - horiz T.b) / L with hs
    have hcmp : pushCDF S w T.app t ≤ hCDF S w s := by
      rw [hCDF_eq_sum_ite, pushCDF_eq_sum_ite]
      refine Finset.sum_le_sum fun z hz => ?_
      by_cases hwz : w z = 0
      · simp [hwz]
      · split_ifs with h1 h2
        · exact le_rfl
        · exfalso
          have hk := abs_le.1 (key z hz hwz)
          have h3 : L * horiz z ≤ t + T.r * (θ * m) - horiz T.b := by linarith [hk.1]
          exact h2 ((le_div_iff₀ hL0).2 (by linarith))
        · exact hw z hz
        · exact le_rfl
    have hup := (hW s).2
    refine (hcmp.trans hup).trans ?_
    apply clamp01_mono
    have : (t + T.r * (r + θ * m) - horiz T.b) / L =
        (t + T.r * (θ * m) - horiz T.b) / L + T.r * r / L := by ring
    rw [this, hs]
    linarith

/-- Horizontal coordinates of the vertices of an equal-edge polygon increase from `0` to `1`. -/
theorem horiz_mono_of_EqualEdgeData {K : ℕ} {δ q E₀ M₀ c : ℝ} {v : ℕ → Rd d}
    (hE : EqualEdgeData K δ q E₀ M₀ c v) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ K) :
    horiz (v i) ≤ horiz (v j) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = i + k := ⟨j - i, by omega⟩
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    have h1 := ih (by omega) (by omega)
    have h2 := hE.forward (i + k) (by omega)
    rw [← add_assoc]
    linarith

theorem horiz_mem_Icc_of_EqualEdgeData (hd : 0 < d) {K : ℕ} {δ q E₀ M₀ c : ℝ} {v : ℕ → Rd d}
    (hE : EqualEdgeData K δ q E₀ M₀ c v) {i : ℕ} (hi : i ≤ K) : horiz (v i) ∈ Icc 0 1 := by
  have h0 : horiz (v 0) = 0 := by rw [hE.start, horiz_zero]
  have h1 : horiz (v K) = 1 := by rw [hE.finish, horiz_e₁ hd]
  exact ⟨h0 ▸ horiz_mono_of_EqualEdgeData hE (Nat.zero_le i) hi,
    h1 ▸ horiz_mono_of_EqualEdgeData hE hi le_rfl⟩

/-- The frame data of an edge similarity of an equal-edge polygon. -/
theorem edgeSim_frame (hd : 0 < d) {K : ℕ} {δ q E₀ M₀ c : ℝ} {v : ℕ → Rd d}
    (hE : EqualEdgeData K δ q E₀ M₀ c v) (hq : 0 < q) {i : ℕ} (hi : i < K) :
    (edgeSim q v i).O (e₁ d) = q⁻¹ • (v (i + 1) - v i) ∧ ‖q⁻¹ • (v (i + 1) - v i)‖ = 1 ∧
      ‖q⁻¹ • (v (i + 1) - v i) - e₁ d‖ ≤ c * δ ∧
      (edgeSim q v i).r * horiz (q⁻¹ • (v (i + 1) - v i)) = horiz (v (i + 1)) - horiz (v i) := by
  refine ⟨edgeSim_O_e₁ hd hq (hE.edge_len i hi), norm_edgeDir hq (hE.edge_len i hi),
    hE.angle i hi, ?_⟩
  rw [edgeSim_r, horiz_smul, horiz_sub, ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul]

/-- The replaced measure `ν_{j,μ} = K⁻¹ Σ_i (T_i)_* μ`: its horizontal distribution function. -/
def replCDF (K : ℕ) (q : ℝ) (v : ℕ → Rd d) (S : Finset (Rd d)) (w : Rd d → ℝ) (t : ℝ) : ℝ :=
  (1 / (K : ℝ)) * ∑ i ∈ Finset.range K, pushCDF S w (edgeSim q v i).app t

/-- **(5.18)** (Lemma 5.3, Step 1; HA4 D3(c), D6 Step 1). If `μ = Σ w z δ_z` is a probability
measure in `W(r)` whose atoms have transverse part `≤ m`, and `v` is an equal-edge polygon
(`EqualEdgeData`), then `(ν_{j,μ})_x ∈ W(δ²E₀ + q(r + cδ m))`. -/
theorem replCDF_inW (hd : 0 < d) {K : ℕ} (hK : 0 < K) {δ q E₀ M₀ c : ℝ} {v : ℕ → Rd d}
    (hE : EqualEdgeData K δ q E₀ M₀ c v) (hq : 0 < q) {S : Finset (Rd d)} {w : Rd d → ℝ}
    (hw : ∀ z ∈ S, 0 ≤ w z) {r : ℝ} (hr : 0 ≤ r) (hW : HorizW S w r) {m : ℝ}
    (htr : ∀ z ∈ S, w z ≠ 0 → ‖transv z‖ ≤ m) :
    InW (δ ^ 2 * E₀ + q * (r + c * δ * m)) (replCDF K q v S w) := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  set x : ℕ → ℝ := fun i => horiz (v i) with hx
  have hpoly : InW (δ ^ 2 * E₀) (polyCDF K x) :=
    polyCDF_inW hK (fun i hi => sub_pos.1 (hE.forward i hi)) (fun i hi => hE.knots i hi)
  refine hpoly.shift fun t => ?_
  have hbd : ∀ i ∈ Finset.range K,
      clamp01 ((t - q * (r + c * δ * m) - x i) / (x (i + 1) - x i)) ≤
        pushCDF S w (edgeSim q v i).app t ∧
      pushCDF S w (edgeSim q v i).app t ≤
        clamp01 ((t + q * (r + c * δ * m) - x i) / (x (i + 1) - x i)) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    obtain ⟨hO, hu1, hθ, hℓ⟩ := edgeSim_frame hd hE hq hi'
    have hu_pos : 0 < horiz (q⁻¹ • (v (i + 1) - v i)) := by
      have h := hE.forward i hi'
      rw [← hℓ, edgeSim_r] at h
      exact pos_of_mul_pos_right h hq.le
    have := pushCDF_bounds hd hw hr hW htr (edgeSim q v i) hu1 hO hθ (by rw [edgeSim_r]; exact hq)
      hu_pos t
    rw [hℓ, edgeSim_r, edgeSim_b, show c * δ * m = (c * δ) * m by ring] at this
    rw [show c * δ * m = (c * δ) * m by ring]
    exact this
  constructor
  · unfold polyCDF replCDF
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) (by positivity)
    exact (hbd i hi).1
  · unfold polyCDF replCDF
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) (by positivity)
    exact (hbd i hi).2

/-! ## Step 3: `T_i(V_δ) ⊆ V_δ ⊆ U` and the horizontal support of `Tμ` -/

/-- For `z₁ ∈ [-r, 1+r]` and `‖z_⊥‖ ≤ m`, the image under the `i`-th edge similarity of an
equal-edge polygon has `(T_i z)₁ ∈ [-q(r + cδm), 1 + q(r + cδm)]`. -/
theorem horiz_edgeSim_mem (hd : 0 < d) {K : ℕ} {δ q E₀ M₀ c : ℝ} {v : ℕ → Rd d}
    (hE : EqualEdgeData K δ q E₀ M₀ c v) (hq : 0 < q) {i : ℕ} (hi : i < K) {r m : ℝ}
    (hr : 0 ≤ r) {z : Rd d} (hz : horiz z ∈ Icc (-r) (1 + r)) (hzt : ‖transv z‖ ≤ m) :
    horiz ((edgeSim q v i).app z) ∈ Icc (-(q * (r + c * δ * m))) (1 + q * (r + c * δ * m)) := by
  obtain ⟨hO, hu1, hθ, hℓ⟩ := edgeSim_frame hd hE hq hi
  set u := q⁻¹ • (v (i + 1) - v i) with hu
  set u₀ := clamp01 (horiz z) with hu₀
  have hu₀0 : 0 ≤ u₀ := clamp01_nonneg _
  have hu₀1 : u₀ ≤ 1 := clamp01_le_one _
  have hzu : |horiz z - u₀| ≤ r := abs_sub_clamp01_le hr hz
  set w := z - u₀ • e₁ d with hw
  have hw1 : horiz w = horiz z - u₀ := by rw [hw, horiz_sub, horiz_smul_e₁ hd]
  have hwt : transv w = transv z := by rw [hw, transv_sub, transv_smul_e₁ hd, sub_zero]
  -- the edge point `T_i(u₀ e₁)`
  have hp : (edgeSim q v i).app (u₀ • e₁ d) = v i + u₀ • (v (i + 1) - v i) :=
    edgeSim_app_smul_e₁ hd hq (hE.edge_len i hi) u₀
  have hTz : (edgeSim q v i).app z = (edgeSim q v i).app (u₀ • e₁ d) + q • (edgeSim q v i).O w := by
    have := SimD.app_sub (edgeSim q v i) z (u₀ • e₁ d)
    rw [edgeSim_r] at this
    rw [← this]
    abel
  have hxp : horiz ((edgeSim q v i).app (u₀ • e₁ d)) ∈ Icc (0 : ℝ) 1 := by
    rw [hp, horiz_add, horiz_smul, horiz_sub]
    have h0 := horiz_mem_Icc_of_EqualEdgeData hd hE (Nat.le_of_lt hi)
    have h1 := horiz_mem_Icc_of_EqualEdgeData hd hE (show i + 1 ≤ K by omega)
    have hinc := hE.forward i hi
    constructor
    · nlinarith [h0.1]
    · nlinarith [h1.2]
  have hOw : |horiz ((edgeSim q v i).O w)| ≤ r + c * δ * m := by
    have h1 := abs_horiz_map_sub_le hd (edgeSim q v i).O hO hθ w
    rw [hwt] at h1
    have hθ0 : 0 ≤ c * δ := (norm_nonneg _).trans hθ
    have h2 : |horiz w * horiz u| ≤ r := by
      rw [abs_mul, hw1]
      have := abs_horiz_le u hd
      rw [hu1] at this
      calc |horiz z - u₀| * |horiz u| ≤ r * 1 :=
            mul_le_mul hzu this (abs_nonneg _) ((abs_nonneg _).trans hzu)
        _ = r := mul_one r
    have h3 : c * δ * ‖transv z‖ ≤ c * δ * m := mul_le_mul_of_nonneg_left hzt hθ0
    calc |horiz ((edgeSim q v i).O w)|
        = |(horiz ((edgeSim q v i).O w) - horiz w * horiz u) + horiz w * horiz u| := by ring_nf
      _ ≤ |horiz ((edgeSim q v i).O w) - horiz w * horiz u| + |horiz w * horiz u| :=
          abs_add_le _ _
      _ ≤ c * δ * m + r := add_le_add (h1.trans h3) h2
      _ = r + c * δ * m := by ring
  have hTz1 : horiz ((edgeSim q v i).app z) =
      horiz ((edgeSim q v i).app (u₀ • e₁ d)) + q * horiz ((edgeSim q v i).O w) := by
    rw [hTz, horiz_add, horiz_smul]
  have hb := abs_le.1 hOw
  rw [hTz1]
  constructor
  · nlinarith [hxp.1]
  · nlinarith [hxp.2]

/-- Transverse bound for the image under an edge similarity:
`‖(T_i z)_⊥‖ ≤ M₀δ + q(r + m)` for `z₁ ∈ [-r, 1+r]`, `‖z_⊥‖ ≤ m`. -/
theorem norm_transv_edgeSim_le (hd : 0 < d) {K : ℕ} {δ q E₀ M₀ c : ℝ} {v : ℕ → Rd d}
    (hE : EqualEdgeData K δ q E₀ M₀ c v) (hq : 0 < q) {i : ℕ} (hi : i < K) {r m : ℝ}
    (hr : 0 ≤ r) {z : Rd d} (hz : horiz z ∈ Icc (-r) (1 + r)) (hzt : ‖transv z‖ ≤ m) :
    ‖transv ((edgeSim q v i).app z)‖ ≤ M₀ * δ + q * (r + m) := by
  set u₀ := clamp01 (horiz z) with hu₀
  have hu₀0 : 0 ≤ u₀ := clamp01_nonneg _
  have hu₀1 : u₀ ≤ 1 := clamp01_le_one _
  have hzu : |horiz z - u₀| ≤ r := abs_sub_clamp01_le hr hz
  set w := z - u₀ • e₁ d with hw
  have hw1 : horiz w = horiz z - u₀ := by rw [hw, horiz_sub, horiz_smul_e₁ hd]
  have hwt : transv w = transv z := by rw [hw, transv_sub, transv_smul_e₁ hd, sub_zero]
  have hp : (edgeSim q v i).app (u₀ • e₁ d) = v i + u₀ • (v (i + 1) - v i) :=
    edgeSim_app_smul_e₁ hd hq (hE.edge_len i hi) u₀
  have hTz : (edgeSim q v i).app z = (edgeSim q v i).app (u₀ • e₁ d) + q • (edgeSim q v i).O w := by
    have := SimD.app_sub (edgeSim q v i) z (u₀ • e₁ d)
    rw [edgeSim_r] at this
    rw [← this]
    abel
  have hnw : ‖w‖ ≤ r + m := by
    calc ‖w‖ = ‖horiz w • e₁ d + transv w‖ := by rw [horiz_add_transv]
      _ ≤ ‖horiz w • e₁ d‖ + ‖transv w‖ := norm_add_le _ _
      _ = |horiz w| + ‖transv w‖ := by rw [norm_smul, norm_e₁ hd, mul_one, Real.norm_eq_abs]
      _ ≤ r + m := by rw [hw1, hwt]; exact add_le_add hzu hzt
  have hpt : ‖transv ((edgeSim q v i).app (u₀ • e₁ d))‖ ≤ M₀ * δ := by
    rw [hp, transv_add, transv_smul, transv_sub]
    have h0 := hE.transverse i (Nat.le_of_lt hi)
    have h1 := hE.transverse (i + 1) (by omega)
    have e : transv (v i) + u₀ • (transv (v (i + 1)) - transv (v i)) =
        (1 - u₀) • transv (v i) + u₀ • transv (v (i + 1)) := by module
    rw [e]
    calc ‖(1 - u₀) • transv (v i) + u₀ • transv (v (i + 1))‖
        ≤ ‖(1 - u₀) • transv (v i)‖ + ‖u₀ • transv (v (i + 1))‖ := norm_add_le _ _
      _ = (1 - u₀) * ‖transv (v i)‖ + u₀ * ‖transv (v (i + 1))‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hu₀0,
            abs_of_nonneg (by linarith)]
      _ ≤ (1 - u₀) * (M₀ * δ) + u₀ * (M₀ * δ) :=
          add_le_add (mul_le_mul_of_nonneg_left h0 (by linarith))
            (mul_le_mul_of_nonneg_left h1 hu₀0)
      _ = M₀ * δ := by ring
  rw [hTz, transv_add, transv_smul]
  calc ‖transv ((edgeSim q v i).app (u₀ • e₁ d)) + q • transv ((edgeSim q v i).O w)‖
      ≤ ‖transv ((edgeSim q v i).app (u₀ • e₁ d))‖ + ‖q • transv ((edgeSim q v i).O w)‖ :=
        norm_add_le _ _
    _ ≤ M₀ * δ + q * (r + m) := by
        refine add_le_add hpt ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq]
        refine mul_le_mul_of_nonneg_left ?_ hq.le
        calc ‖transv ((edgeSim q v i).O w)‖ ≤ ‖(edgeSim q v i).O w‖ := norm_transv_le hd _
          _ = ‖w‖ := LinearIsometryEquiv.norm_map _ _
          _ ≤ r + m := hnw

/-- **Lemma 5.3 (i), first half**: every edge similarity maps `V_δ` into itself, provided
`q(B + cM) ≤ B` and `M₀ + q(Bδ + M) ≤ M` (both hold for `M = (M₀ + q₀ + 1)/(1 - q₀)`,
`B ≥ q₀ c M/(1 - q₀)`, `q ≤ q₀ < 1` and `Bδ ≤ 1`, HA4 D6). -/
theorem edgeSim_mapsTo_Vdelta (hd : 0 < d) {K : ℕ} {δ q E₀ M₀ c : ℝ} {v : ℕ → Rd d}
    (hE : EqualEdgeData K δ q E₀ M₀ c v) (hq : 0 < q) (hδ : 0 ≤ δ) {M B : ℝ} (hB : 0 ≤ B)
    (h1 : q * (B + c * M) ≤ B) (h2 : M₀ + q * (B * δ + M) ≤ M) {i : ℕ} (hi : i < K) :
    MapsTo (edgeSim q v i).app (Vdelta δ M B) (Vdelta δ M B) := by
  intro z hz
  obtain ⟨hz1, hz2⟩ := hz
  have hδ2 : 0 ≤ δ ^ 2 := sq_nonneg δ
  have hr : 0 ≤ B * δ ^ 2 := mul_nonneg hB hδ2
  have hx := horiz_edgeSim_mem hd hE hq hi hr hz1 hz2
  have ht := norm_transv_edgeSim_le hd hE hq hi hr hz1 hz2
  have e1 : q * (B * δ ^ 2 + c * δ * (M * δ)) = q * (B + c * M) * δ ^ 2 := by ring
  have hh : q * (B * δ ^ 2 + c * δ * (M * δ)) ≤ B * δ ^ 2 := by
    rw [e1]; exact mul_le_mul_of_nonneg_right h1 hδ2
  refine ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, ?_⟩
  have e2 : M₀ * δ + q * (B * δ ^ 2 + M * δ) = (M₀ + q * (B * δ + M)) * δ := by ring
  calc ‖transv ((edgeSim q v i).app z)‖ ≤ M₀ * δ + q * (B * δ ^ 2 + M * δ) := ht
    _ = (M₀ + q * (B * δ + M)) * δ := e2
    _ ≤ M * δ := mul_le_mul_of_nonneg_right h2 hδ

/-- **Lemma 5.3 (i), second half**: `V_δ ⊆ U = (-2,2)^d` when `Bδ² < 1` and `Mδ < 2`. -/
theorem Vdelta_subset_cube (hd : 0 < d) {δ M B : ℝ} (hB : B * δ ^ 2 < 1) (hM : M * δ < 2) :
    Vdelta δ M B ⊆ cube d := by
  intro z hz i
  by_cases hi : (i : ℕ) = 0
  · have hi' : i = ⟨0, hd⟩ := Fin.ext hi
    rw [hi', ← horiz_apply hd, abs_lt]
    exact ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
  · exact lt_of_le_of_lt ((abs_ofLp_le_norm_transv z hi).trans hz.2) hM

/-! ## Lemma 5.3 (ii): the deterministic skeleton -/

theorem hCDF_nonneg {S : Finset (Rd d)} {w : Rd d → ℝ} (hw : ∀ z ∈ S, 0 ≤ w z) (x : ℝ) :
    0 ≤ hCDF S w x :=
  Finset.sum_nonneg fun z hz => hw z (Finset.mem_filter.1 hz).1

theorem hCDF_le_one {S : Finset (Rd d)} {w : Rd d → ℝ} (hμ : IsFinProb S w) (x : ℝ) :
    hCDF S w x ≤ 1 := by
  rw [← hμ.2]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun z hz _ => hμ.1 z hz)

/-- A measure whose atoms have `z₁ ≥ a` has `F(x) = 0` for `x < a`. -/
theorem hCDF_eq_zero_of_lt {S : Finset (Rd d)} {w : Rd d → ℝ} {a : ℝ}
    (hsupp : ∀ z ∈ S, w z ≠ 0 → a ≤ horiz z) {x : ℝ} (hx : x < a) : hCDF S w x = 0 := by
  rw [hCDF_eq_sum_ite]
  refine Finset.sum_eq_zero fun z hz => ?_
  split_ifs with h
  · by_contra hne
    have := hsupp z hz hne
    linarith
  · rfl

/-- A probability measure whose atoms have `z₁ ≤ b` has `F(x) = 1` for `x ≥ b`. -/
theorem hCDF_eq_one_of_le {S : Finset (Rd d)} {w : Rd d → ℝ} (hμ : IsFinProb S w) {b : ℝ}
    (hsupp : ∀ z ∈ S, w z ≠ 0 → horiz z ≤ b) {x : ℝ} (hx : b ≤ x) : hCDF S w x = 1 := by
  rw [hCDF_eq_sum_ite, ← hμ.2]
  refine Finset.sum_congr rfl fun z hz => ?_
  split_ifs with h
  · rfl
  · by_contra hne
    exact h ((hsupp z hz fun h0 => hne h0.symm).trans hx)

/-- **Lemma 5.3 (ii), deterministic skeleton** (HA4 D6, Steps 1–3). Let `μ ∈ C_δ`, let
`v j` (`j ∈ ι`) be equal-edge polygons satisfying the containment conditions of
`edgeSim_mapsTo_Vdelta`, and let `p` be a probability vector on `ι` (the law of the selector).
Let `μ'` be a finitely supported probability measure carried by `⋃_{j,i} T_i^j(supp μ)` whose
horizontal distribution function is within `η` of that of the mixture
`ν̄ = Σ_j p_j ν_{j,μ}` (this closeness is the probabilistic estimate (5.20)). If
`δ²E₀ + q(Bδ² + cδ·Mδ) + η ≤ Bδ²` (the choice (5.22)), then `μ' ∈ C_δ`. -/
theorem inCDelta_of_hCDF_close (hd : 0 < d) {K : ℕ} (hK : 0 < K) {ι : Type*} [Fintype ι]
    {δ q E₀ M₀ c M B : ℝ} {v : ι → ℕ → Rd d} (hE : ∀ j, EqualEdgeData K δ q E₀ M₀ c (v j))
    (hq : 0 < q) (hδ : 0 ≤ δ) (hB : 0 ≤ B) (h1 : q * (B + c * M) ≤ B)
    (h2 : M₀ + q * (B * δ + M) ≤ M) {S : Finset (Rd d)} {w : Rd d → ℝ}
    (hμ : InCDelta δ M B S w) {p : ι → ℝ} (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    {S' : Finset (Rd d)} {w' : Rd d → ℝ} (hμ' : IsFinProb S' w')
    (hsupp : ∀ z' ∈ S', w' z' ≠ 0 →
      ∃ j, ∃ i < K, ∃ z ∈ S, w z ≠ 0 ∧ z' = (edgeSim q (v j) i).app z)
    {η : ℝ} (hη : 0 ≤ η)
    (hclose : ∀ x, |hCDF S' w' x - ∑ j, p j * replCDF K q (v j) S w x| ≤ η)
    (hB' : δ ^ 2 * E₀ + q * (B * δ ^ 2 + c * δ * (M * δ)) + η ≤ B * δ ^ 2) :
    InCDelta δ M B S' w' := by
  obtain ⟨hfp, htr, hW⟩ := hμ
  have hr : 0 ≤ B * δ ^ 2 := mul_nonneg hB (sq_nonneg δ)
  set h := q * (B * δ ^ 2 + c * δ * (M * δ)) with hh
  set r₁ := δ ^ 2 * E₀ + h with hr₁
  -- `ι` is nonempty, and `δ² E₀ ≥ 0` (knot bound at `i = 0`)
  obtain ⟨j₀⟩ : Nonempty ι := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    simp at hp1
  have hE0 : 0 ≤ δ ^ 2 * E₀ := le_trans (abs_nonneg _) ((hE j₀).knots 0 (Nat.zero_le _))
  -- support of `μ'`
  have hsupp' : ∀ z' ∈ S', w' z' ≠ 0 →
      z' ∈ Vdelta δ M B ∧ horiz z' ∈ Icc (-h) (1 + h) := by
    intro z' hz' hw'
    obtain ⟨j, i, hi, z, hz, hwz, rfl⟩ := hsupp z' hz' hw'
    have hzV := InCDelta.mem_Vdelta ⟨hfp, htr, hW⟩ hz hwz
    exact ⟨edgeSim_mapsTo_Vdelta hd (hE j) hq hδ hB h1 h2 hi hzV,
      horiz_edgeSim_mem hd (hE j) hq hi hr hzV.1 hzV.2⟩
  -- the mixture is in `W(r₁)`
  have hmix : InW r₁ (fun x => ∑ j, p j * replCDF K q (v j) S w x) :=
    InW.sum Finset.univ (fun j _ => hp j) hp1 fun j _ => by
      have := replCDF_inW hd hK (hE j) hq hfp.1 hr hW htr
      rwa [show q * (B * δ ^ 2 + c * δ * (M * δ)) = h from rfl] at this
  refine ⟨hμ', fun z' hz' hw' => (hsupp' z' hz' hw').1.2, ?_⟩
  have hG := InW.quantile_observation hη hmix hclose (hCDF_nonneg hμ'.1) (hCDF_le_one hμ')
    (fun x hx => hCDF_eq_zero_of_lt (a := -h) (fun z' hz' hw' => (hsupp' z' hz' hw').2.1)
      (by linarith))
    (fun x hx => hCDF_eq_one_of_le hμ' (b := 1 + h) (fun z' hz' hw' => (hsupp' z' hz' hw').2.2)
      (by linarith))
  exact hG.mono (by linarith)

/-! ## The reference measure `ν₀^N` -/

/-- Left Riemann reference points `(l/N) e₁`, `l < N`. -/
def refPt (N l : ℕ) : Rd d := ((l : ℝ) / N) • e₁ d

/-- The support of `ν₀^N = N⁻¹ Σ_{l<N} δ_{(l/N) e₁}`. -/
def refSet (N : ℕ) : Finset (Rd d) := (Finset.range N).image (refPt N)

theorem refPt_injective (hd : 0 < d) {N : ℕ} (hN : 0 < N) :
    Function.Injective (refPt (d := d) N) := by
  intro l l' h
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := congrArg horiz h
  simp only [refPt, horiz_smul_e₁ hd] at h1
  have : (l : ℝ) = l' := by
    field_simp at h1
    exact h1
  exact_mod_cast this

/-- **`ν₀^N ∈ C_δ`** when `1/N ≤ Bδ²` (HA4 D7: `(ν₀^N)_x ∈ W(1/N)`, transverse part `0`). -/
theorem refMeasure_inCDelta (hd : 0 < d) {N : ℕ} (hN : 0 < N)
    {δ M B : ℝ} (hM : 0 ≤ M * δ) (hNB : 1 / (N : ℝ) ≤ B * δ ^ 2) :
    InCDelta δ M B (refSet (d := d) N) (fun _ => 1 / (N : ℝ)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hinj := refPt_injective (d := d) hd hN
  refine ⟨⟨fun _ _ => by positivity, ?_⟩, ?_, ?_⟩
  · rw [refSet, Finset.sum_image (fun x _ y _ h => hinj h), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    field_simp
  · intro z hz _
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hz
    rw [refPt, transv_smul_e₁ hd, norm_zero]
    exact hM
  · refine InW.mono ?_ hNB
    have hsum : ∀ t, hCDF (refSet (d := d) N) (fun _ => 1 / (N : ℝ)) t =
        (1 / (N : ℝ)) * ∑ l ∈ Finset.range N, (if (l : ℝ) / N ≤ t then (1 : ℝ) else 0) := by
      intro t
      rw [hCDF_eq_sum_ite, refSet, Finset.sum_image (fun x _ y _ h => hinj h), Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [refPt, horiz_smul_e₁ hd]
      split_ifs <;> ring
    intro t
    rw [hsum]
    constructor
    · rw [← avg_clamp01 hN (t - 1 / N)]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => ?_) (by positivity)
      split_ifs with h
      · exact clamp01_le_one _
      · push Not at h
        apply le_of_eq
        apply clamp01_of_nonpos
        rw [lt_div_iff₀ hN'] at h
        have : (N : ℝ) * (t - 1 / N) = N * t - 1 := by field_simp
        rw [this]
        linarith
    · rw [← avg_clamp01 hN (t + 1 / N)]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => ?_) (by positivity)
      split_ifs with h
      · rw [div_le_iff₀ hN'] at h
        apply le_of_eq
        symm
        apply clamp01_of_one_le
        have : (N : ℝ) * (t + 1 / N) = N * t + 1 := by field_simp
        rw [this]
        linarith
      · exact clamp01_nonneg _

/-! ## Image measures with collected weights -/

/-- Weight collected at `p` by the image of `Σ_{a∈A} u a δ_{φ a}`. -/
def imgW {α : Type*} (A : Finset α) (φ : α → Rd d) (u : α → ℝ) (p : Rd d) : ℝ :=
  ∑ a ∈ A, if φ a = p then u a else 0

/-- Horizontal distribution function of an image measure with collected weights. -/
theorem hCDF_image_imgW {α : Type*} (A : Finset α) (φ : α → Rd d)
    (u : α → ℝ) (t : ℝ) :
    hCDF (A.image φ) (imgW A φ u) t = ∑ a ∈ A.filter (fun a => horiz (φ a) ≤ t), u a := by
  unfold hCDF imgW
  rw [Finset.sum_comm]
  rw [show (∑ a ∈ A.filter (fun a => horiz (φ a) ≤ t), u a) =
      ∑ a ∈ A, if horiz (φ a) ≤ t then u a else 0 from Finset.sum_filter _ _]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_filter, Finset.mem_image_of_mem φ ha, true_and]

/-- Total mass of an image measure with collected weights. -/
theorem sum_image_imgW {α : Type*} (A : Finset α) (φ : α → Rd d)
    (u : α → ℝ) : ∑ p ∈ A.image φ, imgW A φ u p = ∑ a ∈ A, u a := by
  unfold imgW
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_image_of_mem φ ha)]

end HigherDimLFPP.Lower
