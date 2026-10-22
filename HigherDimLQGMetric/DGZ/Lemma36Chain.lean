import HigherDimLQGMetric.DGZ.FunctionalsLaw

/-!
# Chains of rigid motions for DGZ Lemma 3.6 (packet L3b3, MA7 D-3.6L, deterministic part)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), Lemma 3.6 (TeX l. 1153–1214), lower half;
planning audit `planning/audits/MA7-ref2-sections-4-6.md`, Details (a) D-3.6L ("Chain", "Rigid
motions").

Let `d ≥ 2`, `x, y ∈ B̄₂(0)` with `ϱ = |y - x|₂ ≥ 1/2`, and `L = 2^m` with `9√d < L`.
* `zigzag d s ϱ i = (i s) e₁ + [i odd] h e₂`, `h = √(ϱ² - s²)`: for `0 ≤ s ≤ ϱ` consecutive points
  are at Euclidean distance exactly `ϱ` (`norm_zigzag_succ_sub`), `z_0 = 0` and
  `z_{2K} = 2K s e₁`. D-3.6L uses `s = 1/2` and `2L` steps, so `z_{2L} = L e₁`. (MA7 uses `J - 2`
  steps along `e₁` and an isosceles pair of steps; the zigzag is the same idea, needs only
  `ϱ ≥ 1/2`, and has the uniform length `J = 2L`.)
* `chainRefl d x y i`: a reflection `O_i ∈ O(d)` with `O_i(y - x) = z_{i+1} - z_i`
  (Mathlib `Submodule.reflection_sub`), and the rigid motion `T_i w = (z_i - O_i x) + O_i w`
  (`T_i x = z_i`, `T_i y = z_{i+1}`).
* `T_i(B₃(0))` is convex and lies in `B_{2L}(0) ⊆ 2^m (-2,2)^d`, because
  `|T_i w - z_i| = |w - x| ≤ 5√d` and `|z_i| ≤ L + ϱ ≤ L + 4√d` (`sim_mem_obox`).
* **Chain bound** (`lfppDistOn_le_sum_chain`): for every continuous field `φ`,
  `D_{2^m (-2,2)^d}(0, 2^m e₁)(φ) ≤ Σ_{i < 2L} D_{T_i B₃(0)}(T_i x, T_i y)(φ)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped RealInnerProductSpace

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP
open HigherDimLFPP.DGZ (cbox obox)

variable {d : ℕ}

/-! ### The second unit vector -/

/-- `e₂ = (0, 1, 0, …, 0)` (the zero vector if `d ≤ 1`). -/
def e₂ (d : ℕ) : Rd d := WithLp.toLp 2 (fun i : Fin d => if (i : ℕ) = 1 then (1 : ℝ) else 0)

theorem e₂_ofLp (d : ℕ) (i : Fin d) : (e₂ d).ofLp i = if (i : ℕ) = 1 then 1 else 0 := rfl

theorem norm_e₂ (hd : 2 ≤ d) : ‖e₂ d‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have : ∑ i : Fin d, ‖(e₂ d).ofLp i‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single ⟨1, by omega⟩]
    · rw [e₂_ofLp]; simp
    · intro i _ hi
      rw [e₂_ofLp, ite_eq_right (fun h => hi (Fin.ext h))]
      simp
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [this, Real.sqrt_one]

theorem inner_e₁_e₂ (d : ℕ) : ⟪e₁ d, e₂ d⟫ = 0 := by
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [e₁_ofLp, e₂_ofLp]
  split_ifs with h1 h2 h2
  · omega
  · simp
  · simp
  · simp

/-- `‖a e₁ + b e₂‖² = a² + b²` (`d ≥ 2`). -/
theorem norm_smul_e₁_add_smul_e₂_sq (hd : 2 ≤ d) (a b : ℝ) :
    ‖a • e₁ d + b • e₂ d‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, inner_e₁_e₂, norm_smul,
    norm_smul, norm_e₁ (by omega), norm_e₂ hd, Real.norm_eq_abs, Real.norm_eq_abs, mul_one,
    mul_one, sq_abs, sq_abs]
  ring

/-! ### The zigzag chain -/

/-- The zigzag chain `z_i = (i s) e₁ + [i odd] h e₂` with `h = √(ϱ² - s²)` (MA7 D-3.6L, "Chain";
also usable for the equal-step chains of D-6.5): for `0 ≤ s ≤ ϱ` consecutive points are at
Euclidean distance exactly `ϱ`, `z_0 = 0` and `z_{2K} = 2K s e₁`. -/
def zigzag (d : ℕ) (s ϱ : ℝ) (i : ℕ) : Rd d :=
  ((i : ℝ) * s) • e₁ d + (if Even i then (0 : ℝ) else √(ϱ ^ 2 - s ^ 2)) • e₂ d

theorem zigzag_zero (d : ℕ) (s ϱ : ℝ) : zigzag d s ϱ 0 = 0 := by
  simp [zigzag]

theorem zigzag_two_mul (d : ℕ) (s ϱ : ℝ) (K : ℕ) :
    zigzag d s ϱ (2 * K) = (2 * (K : ℝ) * s) • e₁ d := by
  rw [zigzag, ite_eq_left (even_two_mul K), zero_smul, add_zero]
  push_cast
  rfl

theorem zigzag_succ_sub (d : ℕ) (s ϱ : ℝ) (i : ℕ) :
    zigzag d s ϱ (i + 1) - zigzag d s ϱ i = s • e₁ d +
      (if Even i then √(ϱ ^ 2 - s ^ 2) else -√(ϱ ^ 2 - s ^ 2)) • e₂ d := by
  unfold zigzag
  by_cases hi : Even i
  · have hi' : ¬ Even (i + 1) := Nat.even_add_one.not.2 (not_not.2 hi)
    rw [ite_eq_right hi', ite_eq_left hi, ite_eq_left hi]
    push_cast
    module
  · have hi' : Even (i + 1) := Nat.even_add_one.2 hi
    rw [ite_eq_left hi', ite_eq_right hi, ite_eq_right hi]
    push_cast
    module

/-- Consecutive points of the zigzag are at distance exactly `ϱ` (`0 ≤ s ≤ ϱ`). -/
theorem norm_zigzag_succ_sub (hd : 2 ≤ d) {s ϱ : ℝ} (hs : 0 ≤ s) (hsϱ : s ≤ ϱ) (i : ℕ) :
    ‖zigzag d s ϱ (i + 1) - zigzag d s ϱ i‖ = ϱ := by
  rw [zigzag_succ_sub]
  have h0 : 0 ≤ ϱ ^ 2 - s ^ 2 := by nlinarith
  have hsq := norm_smul_e₁_add_smul_e₂_sq hd s
    (if Even i then √(ϱ ^ 2 - s ^ 2) else -√(ϱ ^ 2 - s ^ 2))
  have hh : (if Even i then √(ϱ ^ 2 - s ^ 2) else -√(ϱ ^ 2 - s ^ 2)) ^ 2 = ϱ ^ 2 - s ^ 2 := by
    split_ifs
    · exact Real.sq_sqrt h0
    · rw [neg_sq]; exact Real.sq_sqrt h0
  rw [hh] at hsq
  have hϱ0 : 0 ≤ ϱ := hs.trans hsϱ
  refine (sq_eq_sq₀ (norm_nonneg _) hϱ0).1 ?_
  rw [hsq]
  ring

/-- `|z_i| ≤ i s + ϱ` (`0 ≤ s ≤ ϱ`). -/
theorem norm_zigzag_le (hd : 2 ≤ d) {s ϱ : ℝ} (hs : 0 ≤ s) (hsϱ : s ≤ ϱ) (i : ℕ) :
    ‖zigzag d s ϱ i‖ ≤ i * s + ϱ := by
  unfold zigzag
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, norm_e₁ (by omega), norm_e₂ hd, mul_one, mul_one]
  have h1 : ‖((i : ℝ) * s)‖ = i * s := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h2 : ‖(if Even i then (0 : ℝ) else √(ϱ ^ 2 - s ^ 2))‖ ≤ ϱ := by
    split_ifs
    · rw [norm_zero]; linarith
    · rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      calc √(ϱ ^ 2 - s ^ 2) ≤ √(ϱ ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = ϱ := Real.sqrt_sq (by linarith)
  linarith

/-! ### Reflections and rigid motions -/

/-- A linear isometry of `ℝ^d` mapping `u` to `v` when `‖u‖ = ‖v‖`: the reflection in the
hyperplane orthogonal to `u - v` (Mathlib `Submodule.reflection_sub`). -/
def reflTo (u v : Rd d) : Rd d ≃ₗᵢ[ℝ] Rd d := (ℝ ∙ (u - v))ᗮ.reflection

theorem reflTo_apply {u v : Rd d} (h : ‖u‖ = ‖v‖) : reflTo u v u = v :=
  Submodule.reflection_sub h

/-- The rigid motion `w ↦ (p - O x) + O w = p + O(w - x)`. -/
theorem sim_one_apply (O : Rd d ≃ₗᵢ[ℝ] Rd d) (p x w : Rd d) :
    (p - O x) + (1 : ℝ) • O w = p + O (w - x) := by
  rw [one_smul, map_sub]
  abel

/-- The image of a convex set under a similarity `z ↦ x₀ + r O z` is convex. -/
theorem convex_image_sim (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) (r : ℝ) {S : Set (Rd d)}
    (hS : Convex ℝ S) : Convex ℝ ((fun z => x₀ + r • O z) '' S) := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ a b ha hb hab
  refine ⟨a • p + b • q, hS hp hq ha hb hab, ?_⟩
  simp only [map_add, map_smul]
  rw [show a • (x₀ + r • O p) + b • (x₀ + r • O q) = (a + b) • x₀ + r • (a • O p + b • O q) by
    module, hab, one_smul]

/-- **Containment**: for `x ∈ B̄₂(0)` and `w ∈ B₃(0)`, `|p + O(w - x)| ≤ |p| + 5√d`, so the rigid
motion `T w = (p - O x) + O w` maps `B₃(0)` into `B_R(0)` once `|p| + 5√d < R`. -/
theorem sim_mem_obox {O : Rd d ≃ₗᵢ[ℝ] Rd d} {p x w : Rd d} {R : ℝ} (hx : x ∈ cbox 0 2)
    (hw : w ∈ obox 0 3) (hR : ‖p‖ + 5 * √(d : ℝ) < R) :
    (p - O x) + (1 : ℝ) • O w ∈ obox 0 R := by
  rw [sim_one_apply]
  have hwx : ‖w - x‖ ≤ √(d : ℝ) * 5 := by
    refine norm_sub_le_of_forall_abs_le fun j => ?_
    have h1 := (mem_obox.1 hw) j
    have h2 := (mem_cbox.1 hx) j
    simp only [PiLp.zero_apply, sub_zero] at h1 h2
    calc |w j - x j| ≤ |w j| + |x j| := abs_sub _ _
      _ ≤ 5 := by linarith
  refine mem_obox.2 fun j => ?_
  simp only [PiLp.zero_apply, sub_zero]
  calc |(p + O (w - x)) j| ≤ ‖p + O (w - x)‖ := HigherDimLFPP.DGZ.abs_apply_le_norm _ j
    _ ≤ ‖p‖ + ‖O (w - x)‖ := norm_add_le _ _
    _ = ‖p‖ + ‖w - x‖ := by rw [LinearIsometryEquiv.norm_map]
    _ < R := by linarith

/-- `B_{2·2^m}(0) ⊆ 2^m (-2, 2)^d`, written as the image of the cube under `z ↦ 0 + 2^m z`. -/
theorem obox_subset_image_cube (m : ℕ) :
    obox (0 : Rd d) (2 * 2 ^ m) ⊆
      (fun z => (0 : Rd d) + (2 : ℝ) ^ m • (LinearIsometryEquiv.refl ℝ (Rd d)) z) '' cube d := by
  intro w hw
  have hm : (0 : ℝ) < 2 ^ m := by positivity
  refine ⟨((2 : ℝ) ^ m)⁻¹ • w, fun j => ?_, ?_⟩
  · have h1 := (mem_obox.1 hw) j
    simp only [PiLp.zero_apply, sub_zero] at h1
    show |(((2 : ℝ) ^ m)⁻¹ • w) j| < 2
    rw [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.2 hm), inv_mul_lt_iff₀ hm]
    linarith
  · simp only [LinearIsometryEquiv.coe_refl, id, zero_add, smul_smul,
      mul_inv_cancel₀ hm.ne', one_smul]

/-! ### The chain -/

/-- The points of the chain of D-3.6L: the zigzag with `e₁`-steps `1/2` and steps of length
`ϱ = |y - x|`. -/
def chainPt (d : ℕ) (x y : Rd d) (i : ℕ) : Rd d := zigzag d (1 / 2) ‖y - x‖ i

/-- The reflection `O_i` with `O_i(y - x) = z_{i+1} - z_i`. -/
def chainRefl (d : ℕ) (x y : Rd d) (i : ℕ) : Rd d ≃ₗᵢ[ℝ] Rd d :=
  reflTo (y - x) (chainPt d x y (i + 1) - chainPt d x y i)

/-- The translation part `z_i - O_i x` of the rigid motion `T_i w = z_i + O_i(w - x)`. -/
def chainBase (d : ℕ) (x y : Rd d) (i : ℕ) : Rd d := chainPt d x y i - chainRefl d x y i x

theorem chainRefl_apply (hd : 2 ≤ d) {x y : Rd d} (hϱ : 1 / 2 ≤ ‖y - x‖) (i : ℕ) :
    chainRefl d x y i (y - x) = chainPt d x y (i + 1) - chainPt d x y i :=
  reflTo_apply (by rw [chainPt, chainPt, norm_zigzag_succ_sub hd (by norm_num) hϱ])

/-- `T_i x = z_i`. -/
theorem chain_sim_left (x y : Rd d) (i : ℕ) :
    chainBase d x y i + (1 : ℝ) • chainRefl d x y i x = chainPt d x y i := by
  rw [chainBase, one_smul, sub_add_cancel]

/-- `T_i y = z_{i+1}`. -/
theorem chain_sim_right (hd : 2 ≤ d) {x y : Rd d} (hϱ : 1 / 2 ≤ ‖y - x‖) (i : ℕ) :
    chainBase d x y i + (1 : ℝ) • chainRefl d x y i y = chainPt d x y (i + 1) := by
  rw [chainBase, sim_one_apply, chainRefl_apply hd hϱ]
  abel

/-- `|x - y| ≤ 4√d` on `B̄₂(0)`. -/
theorem norm_sub_le_of_mem_cbox_two {x y : Rd d} (hx : x ∈ cbox 0 2) (hy : y ∈ cbox 0 2) :
    ‖y - x‖ ≤ 4 * √(d : ℝ) := by
  have h := norm_sub_le_of_mem_cbox hy hx
  linarith

/-- **The chain bound of D-3.6L** (deterministic). Let `d ≥ 2`, `x, y ∈ B̄₂(0)` with
`|y - x| ≥ 1/2` and `9√d < 2^m`. For every continuous field `φ`,
`D_{2^m (-2,2)^d}(0, 2^m e₁)(φ) ≤ Σ_{i < 2·2^m} D_{T_i B₃(0)}(T_i x, T_i y)(φ)` with the rigid
motions `T_i w = chainBase i + O_i w`. -/
theorem lfppDistOn_le_sum_chain (hd : 2 ≤ d) (ξ : ℝ) {φ : Rd d → ℝ} (hφ : Continuous φ)
    {x y : Rd d} (hx : x ∈ cbox 0 2) (hy : y ∈ cbox 0 2) (hϱ : 1 / 2 ≤ ‖y - x‖) {m : ℕ}
    (hm : 9 * √(d : ℝ) < 2 ^ m) :
    lfppDistOn ξ φ
        ((fun z => (0 : Rd d) + (2 : ℝ) ^ m • (LinearIsometryEquiv.refl ℝ (Rd d)) z) '' cube d)
        ((0 : Rd d) + (2 : ℝ) ^ m • (LinearIsometryEquiv.refl ℝ (Rd d)) 0)
        ((0 : Rd d) + (2 : ℝ) ^ m • (LinearIsometryEquiv.refl ℝ (Rd d)) (e₁ d)) ≤
      ∑ i ∈ Finset.range (2 * 2 ^ m), lfppDistOn ξ φ
        ((fun z => chainBase d x y i + (1 : ℝ) • chainRefl d x y i z) '' obox 0 3)
        (chainBase d x y i + (1 : ℝ) • chainRefl d x y i x)
        (chainBase d x y i + (1 : ℝ) • chainRefl d x y i y) := by
  set L : ℕ := 2 ^ m with hL
  set Wi : ℕ → Set (Rd d) := fun i =>
    (fun z => chainBase d x y i + (1 : ℝ) • chainRefl d x y i z) '' obox 0 3 with hWi
  have hx3 : x ∈ obox (0 : Rd d) 3 := cbox_subset_obox (by norm_num) hx
  have hy3 : y ∈ obox (0 : Rd d) 3 := cbox_subset_obox (by norm_num) hy
  have hϱ4 := norm_sub_le_of_mem_cbox_two hx hy
  -- each `T_i B₃(0)` lies in the big domain (for `i ≤ 2L`)
  have hsub : ∀ i, i < 2 * L → Wi i ⊆
      (fun z => (0 : Rd d) + (2 : ℝ) ^ m • (LinearIsometryEquiv.refl ℝ (Rd d)) z) '' cube d := by
    rintro i hi _ ⟨w, hw, rfl⟩
    refine obox_subset_image_cube m ?_
    have hz := norm_zigzag_le hd (by norm_num) hϱ i
    have hi' : (i : ℝ) * (1 / 2) ≤ L := by
      have : (i : ℝ) ≤ 2 * L := by exact_mod_cast hi.le
      linarith
    have hLc : ((L : ℕ) : ℝ) = (2 : ℝ) ^ m := by rw [hL]; push_cast; ring
    rw [hLc] at hi'
    simp only [chainBase]
    refine sim_mem_obox hx hw ?_
    rw [chainPt]
    have hsqrt : 0 ≤ √(d : ℝ) := Real.sqrt_nonneg _
    linarith
  -- the summands are joined in their domains
  have hj : ∀ i < 2 * L, PcwJoined (Wi i) (chainPt d x y i) (chainPt d x y (i + 1)) := by
    intro i _
    rw [← chain_sim_left x y i, ← chain_sim_right hd hϱ i]
    exact PcwJoined.of_convex (convex_image_sim _ _ _ (HigherDimLFPP.DGZ.convex_obox 0 3))
      (mem_image_of_mem _ hx3) (mem_image_of_mem _ hy3)
  -- the big domain contains all `T_i B₃(0)`; use the chain bound with `Wi i = big` for `i ≥ 2L`
  set Big := (fun z => (0 : Rd d) + (2 : ℝ) ^ m • (LinearIsometryEquiv.refl ℝ (Rd d)) z) '' cube d
  set Wi' : ℕ → Set (Rd d) := fun i => if i < 2 * L then Wi i else Big with hWi'
  have hW' : ∀ i, Wi' i ⊆ Big := fun i => by
    simp only [hWi']
    split_ifs with h
    · exact hsub i h
    · exact le_rfl
  have hj' : ∀ i < 2 * L, PcwJoined (Wi' i) (chainPt d x y i) (chainPt d x y (i + 1)) :=
    fun i hi => by simp only [hWi', ite_eq_left hi]; exact hj i hi
  have hchain := lfppDistOn_le_sum (ζ := ξ) hφ (chainPt d x y) Wi' hW' (2 * L) hj'
  have h0 : (0 : Rd d) + (2 : ℝ) ^ m • (LinearIsometryEquiv.refl ℝ (Rd d)) 0 = chainPt d x y 0 := by
    rw [chainPt, zigzag_zero]; simp
  have h1 : (0 : Rd d) + (2 : ℝ) ^ m • (LinearIsometryEquiv.refl ℝ (Rd d)) (e₁ d) =
      chainPt d x y (2 * L) := by
    rw [chainPt, zigzag_two_mul, hL]
    simp only [LinearIsometryEquiv.coe_refl, id, zero_add]
    congr 1
    push_cast
    ring
  rw [h0, h1]
  refine hchain.trans_eq (Finset.sum_congr rfl fun i hi => ?_)
  have hi' : i < 2 * L := Finset.mem_range.1 hi
  simp only [hWi', ite_eq_left hi']
  rw [chain_sim_left x y i, chain_sim_right hd hϱ i]

end HigherDimLQGMetric.DGZ
