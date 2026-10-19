import HigherDimLFPP.Upper.LocalMeanParam

/-!
# Lemma 4.3, Step 1: the compact part and the fixed-endpoint bound

Source: `source/higher-dimensional-lfpp-limit.pdf`, §4.2, proof of Lemma 4.3, Step 1 ((4.12),
(4.13)), as completed by the planning audit HA3 (`planning/audits/HA3-section-4.md`), Details D5,
Steps 1b–1d (fixes F6, F15); packet P-U4.

* **The modulus of `Q_δ`** (`norm_qVert_sub_le`, `qPoly_edge_bounds`): on `B̂_R` and for small `δ`,
  the vertices of `Q_δ(f)` and `Q_δ(g)` differ by at most `2δ ‖verts f - verts g‖` and the edges
  have lengths in `[2⁻ⁿ/2, 2]`, so the polygon coupling and Lemma 3.1 give
  `E(Z(f) - Z(g))² ≤ L ‖verts f - verts g‖`.
* **The reference polygon** `Q_δ(0)` (`qPoly_zero_mem`, `shapeV_qPoly_zero`, `eDelta_qPoly_zero`;
  fix F6): the subdivided chord, a good polygon of value `0`.
* **Step 1** (`step1`): for `α, β, θ > 0` there is `δ₁ > 0` such that for `δ < δ₁` and every
  finite `F ⊆ G_K(0, e₁)`, `E max_F (αZ - βE_δ) ≤ α^{4/3} β^{-1/3} A_{n,d} + θ`.  Shells
  (`exists_shell_bound`, with `Q_δ(0)` added), then the compact part by
  `HigherDimLFPP.expectedSupLimit_Vg` (interface (I5): `polygonCovLimit_scaleCov`; the energy
  expansion; the modulus), then the scaling (2.5) (`HigherDimLFPP.Var.scaling25`,
  `gEM_scaled_le_A`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Upper

open LQGDimension (gaussianExpectedMax vecExpectedMax PSDOn)

variable {d : ℕ}

/-! ## The modulus of the polygons `Q_δ(f)` (HA3 D5, Step 1b, on `B̂_R`) -/

section QModulus

/-- `|√x - √y| ≤ |x - y| / q` if `x, y ≥ q²/4`... in the form used below: for `x, y ≥ q² / 4`
with `q > 0`, `|√x - √y| ≤ |x - y| / q`. -/
theorem abs_sqrt_sub_sqrt_le {x y q : ℝ} (hq : 0 < q) (hx : q ^ 2 / 4 ≤ x) (hy : q ^ 2 / 4 ≤ y) :
    |Real.sqrt x - Real.sqrt y| ≤ |x - y| / q := by
  have hx0 : 0 ≤ x := le_trans (by positivity) hx
  have hy0 : 0 ≤ y := le_trans (by positivity) hy
  have hsx : q / 2 ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by positivity) hx0]; linarith
  have hsy : q / 2 ≤ Real.sqrt y := by
    rw [Real.le_sqrt (by positivity) hy0]; linarith
  have hsum : q ≤ Real.sqrt x + Real.sqrt y := by linarith
  have e : (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y) = x - y := by
    rw [show (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y) =
      Real.sqrt x ^ 2 - Real.sqrt y ^ 2 by ring, Real.sq_sqrt hx0, Real.sq_sqrt hy0]
  rw [le_div_iff₀ hq]
  calc |Real.sqrt x - Real.sqrt y| * q ≤ |Real.sqrt x - Real.sqrt y| * (Real.sqrt x + Real.sqrt y) :=
        mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = |x - y| := by
        rw [← e, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.sqrt x + Real.sqrt y)]

/-- **Vertex Lipschitz bound** (HA3 D5, Step 1b): on `B̂_R`, for `δ (1 + 2R)(8 R 4ⁿ + 1) ≤ 2⁻ⁿ/2`,
the vertices of `Q_δ(f)` and `Q_δ(g)` differ by at most `2 δ ‖verts f - verts g‖`. -/
theorem norm_qVert_sub_le (hd : 0 < d) {n : ℕ} {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (hδs : δ * (2 * R) ≤ ((2 : ℝ) ^ n)⁻¹ / 2) (hδs' : δ * (8 * R * ((2 : ℝ) ^ n) ^ 2) ≤ 1)
    {f g : ℝ → Rd (d - 1)} (hf : f ∈ vertBall (Rd (d - 1)) n R)
    (hg : g ∈ vertBall (Rd (d - 1)) n R) {i : ℕ} (hi : i ≤ 2 ^ n) :
    ‖qVert d n δ f i - qVert d n δ g i‖ ≤ 2 * δ * ‖verts n f - verts n g‖ := by
  obtain ⟨-, hfR⟩ := hf
  obtain ⟨-, hgR⟩ := hg
  set v := ‖verts n f - verts n g‖ with hv
  have hv0 : 0 ≤ v := norm_nonneg _
  have hnode : ∀ j : ℕ, j ≤ 2 ^ n → ‖f ((j : ℝ) / 2 ^ n) - g ((j : ℝ) / 2 ^ n)‖ ≤ v := by
    intro j hj
    have := norm_le_pi_norm (verts n f - verts n g) ⟨j, Nat.lt_succ_of_le hj⟩
    simpa [verts] using this
  set q : ℝ := ((2 : ℝ) ^ n)⁻¹ with hq
  have hq0 : 0 < q := by positivity
  have hKq : (2 : ℝ) ^ n * q = 1 := mul_inv_cancel₀ (by positivity)
  -- increments
  have hinc : ∀ l < 2 ^ n, |qInc n δ f l - qInc n δ g l| ≤ (2 : ℝ) ^ n * (8 * R * δ ^ 2 * v) := by
    intro l hl
    have hfl := (hfR (l + 1) hl)
    have hfl' := hfR l hl.le
    have hgl := (hgR (l + 1) hl)
    have hgl' := hgR l hl.le
    rw [Nat.cast_add, Nat.cast_one] at hfl hgl
    have hΔf : ‖f (((l : ℝ) + 1) / 2 ^ n) - f ((l : ℝ) / 2 ^ n)‖ ≤ 2 * R :=
      (norm_sub_le _ _).trans (by linarith)
    have hΔg : ‖g (((l : ℝ) + 1) / 2 ^ n) - g ((l : ℝ) / 2 ^ n)‖ ≤ 2 * R :=
      (norm_sub_le _ _).trans (by linarith)
    have hΔfg : ‖(f (((l : ℝ) + 1) / 2 ^ n) - f ((l : ℝ) / 2 ^ n)) -
        (g (((l : ℝ) + 1) / 2 ^ n) - g ((l : ℝ) / 2 ^ n))‖ ≤ 2 * v := by
      have h1 := hnode (l + 1) hl
      have h2 := hnode l hl.le
      rw [Nat.cast_add, Nat.cast_one] at h1
      calc _ = ‖(f (((l : ℝ) + 1) / 2 ^ n) - g (((l : ℝ) + 1) / 2 ^ n)) -
            (f ((l : ℝ) / 2 ^ n) - g ((l : ℝ) / 2 ^ n))‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
        _ ≤ 2 * v := by linarith
    set A := ‖f (((l : ℝ) + 1) / 2 ^ n) - f ((l : ℝ) / 2 ^ n)‖ with hA
    set B := ‖g (((l : ℝ) + 1) / 2 ^ n) - g ((l : ℝ) / 2 ^ n)‖ with hB
    have hAB : |A - B| ≤ 2 * v := (abs_norm_sub_norm_le _ _).trans hΔfg
    have hsa : δ ^ 2 * A ^ 2 ≤ q ^ 2 / 4 := by
      have h1 : δ * A ≤ q / 2 := (mul_le_mul_of_nonneg_left hΔf hδ.le).trans hδs
      have h2 := pow_le_pow_left₀ (by positivity) h1 2
      rw [mul_pow, div_pow] at h2
      linarith
    have hsb : δ ^ 2 * B ^ 2 ≤ q ^ 2 / 4 := by
      have h1 : δ * B ≤ q / 2 := (mul_le_mul_of_nonneg_left hΔg hδ.le).trans hδs
      have h2 := pow_le_pow_left₀ (by positivity) h1 2
      rw [mul_pow, div_pow] at h2
      linarith
    have h := abs_sqrt_sub_sqrt_le hq0 (x := q ^ 2 - δ ^ 2 * A ^ 2) (y := q ^ 2 - δ ^ 2 * B ^ 2)
      (by nlinarith) (by nlinarith)
    have e1 : qInc n δ f l = Real.sqrt (q ^ 2 - δ ^ 2 * A ^ 2) := rfl
    have e2 : qInc n δ g l = Real.sqrt (q ^ 2 - δ ^ 2 * B ^ 2) := rfl
    rw [e1, e2]
    refine h.trans ?_
    have e3 : q ^ 2 - δ ^ 2 * A ^ 2 - (q ^ 2 - δ ^ 2 * B ^ 2) = δ ^ 2 * ((B + A) * (B - A)) := by ring
    rw [e3, abs_mul, abs_of_nonneg (sq_nonneg δ), abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ B + A),
      abs_sub_comm, div_le_iff₀ hq0]
    have h4 : (B + A) * |A - B| ≤ (4 * R) * (2 * v) :=
      mul_le_mul (by linarith) hAB (abs_nonneg _) (by positivity)
    have h5 : (2 : ℝ) ^ n * (8 * R * δ ^ 2 * v) * q = 8 * R * δ ^ 2 * v := by
      calc (2 : ℝ) ^ n * (8 * R * δ ^ 2 * v) * q = (8 * R * δ ^ 2 * v) * ((2 : ℝ) ^ n * q) := by
            ring
        _ = 8 * R * δ ^ 2 * v := by rw [hKq, mul_one]
    rw [h5]
    nlinarith [sq_nonneg δ]
  have hknot : ∀ j ≤ 2 ^ n, |qKnot n δ f j - qKnot n δ g j| ≤ δ * v := by
    intro j hj
    rw [qKnot, qKnot, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ l ∈ Finset.range j, |qInc n δ f l - qInc n δ g l|
        ≤ ∑ _l ∈ Finset.range j, (2 : ℝ) ^ n * (8 * R * δ ^ 2 * v) :=
          Finset.sum_le_sum fun l hl => hinc l (lt_of_lt_of_le (Finset.mem_range.1 hl) hj)
      _ = j * ((2 : ℝ) ^ n * (8 * R * δ ^ 2 * v)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ n * ((2 : ℝ) ^ n * (8 * R * δ ^ 2 * v)) := by
          gcongr
          exact_mod_cast hj
      _ = (δ * (8 * R * ((2 : ℝ) ^ n) ^ 2)) * (δ * v) := by ring
      _ ≤ 1 * (δ * v) := mul_le_mul_of_nonneg_right hδs' (by positivity)
      _ = δ * v := one_mul _
  rcases lt_or_eq_of_le hi with hlt | rfl
  · rw [qVert, qVert, ite_eq_left hlt, ite_eq_left hlt]
    have e : qKnot n δ f i • e₁ d + Lower.embedT (δ • f ((i : ℝ) / 2 ^ n)) -
        (qKnot n δ g i • e₁ d + Lower.embedT (δ • g ((i : ℝ) / 2 ^ n))) =
        (qKnot n δ f i - qKnot n δ g i) • e₁ d +
          Lower.embedT (δ • (f ((i : ℝ) / 2 ^ n) - g ((i : ℝ) / 2 ^ n))) := by
      rw [smul_sub, Lower.embedT_sub, sub_smul]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Lower.norm_e₁ hd, mul_one, Real.norm_eq_abs, Lower.norm_embedT, norm_smul,
      Real.norm_eq_abs, abs_of_pos hδ]
    have h1 := hknot i hi
    have h2 := mul_le_mul_of_nonneg_left (hnode i hi) hδ.le
    linarith
  · rw [qVert, qVert, ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _), sub_self, norm_zero]
    positivity

/-- **Edges of `Q_δ(f)`** on `B̂_R` for small `δ`: lengths in `[2⁻ⁿ/2, 2]`, and total length `≥ 1`. -/
theorem qPoly_edge_bounds (hd : 0 < d) {n : ℕ} {R δ : ℝ}
    (hδs : (2 * ((2 ^ n) ^ 2 * (2 * R) ^ 2) + 2 ^ n * (2 * R) ^ 2 / 2) * δ ^ 2 ≤
      ((2 : ℝ) ^ n)⁻¹ / 2)
    {f : ℝ → Rd (d - 1)} (hf : f ∈ vertBall (Rd (d - 1)) n R) :
    (∀ i < 2 ^ n, ((2 : ℝ) ^ n)⁻¹ / 2 ≤ ‖qVert d n δ f (i + 1) - qVert d n δ f i‖ ∧
      ‖qVert d n δ f (i + 1) - qVert d n δ f i‖ ≤ 2) ∧ 1 ≤ plen (qVert d n δ f) (2 ^ n) := by
  have hq1 : ((2 : ℝ) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  refine ⟨fun i hi => ?_, ?_⟩
  · have h := abs_norm_qEdge_sub_le hd (δ := δ) hf hi
    rw [abs_le] at h
    constructor <;> linarith [h.1, h.2]
  · have h1 := norm_sub_le_plen (qVert d n δ f) (2 ^ n)
    rw [qVert_zero hf.1.1 δ, sub_zero, qVert, ite_eq_right (lt_irrefl _), Lower.norm_e₁ hd] at h1
    exact h1

end QModulus

/-! ## The reference polygon `Q_δ(0)` (HA3 D5, Step 1c, fix F6) -/

section Reference

theorem qVert_zero_fun (n : ℕ) (δ : ℝ) {i : ℕ} (hi : i ≤ 2 ^ n) :
    qVert d n δ (0 : ℝ → Rd (d - 1)) i = ((i : ℝ) / 2 ^ n) • e₁ d := by
  have hinc : ∀ l, qInc n δ (0 : ℝ → Rd (d - 1)) l = ((2 : ℝ) ^ n)⁻¹ := by
    intro l
    simp only [qInc, Pi.zero_apply, sub_zero, norm_zero]
    rw [show (0 : ℝ) ^ 2 = 0 by norm_num, mul_zero, sub_zero, Real.sqrt_sq (by positivity)]
  rcases lt_or_eq_of_le hi with hlt | rfl
  · rw [qVert, ite_eq_left hlt, qKnot, Finset.sum_congr rfl fun l _ => hinc l, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, Pi.zero_apply, smul_zero, Lower.embedT_zero, add_zero,
      div_eq_mul_inv]
  · rw [qVert, ite_eq_right (lt_irrefl _)]
    push_cast
    rw [div_self (by positivity), one_smul]

theorem qPoly_zero_eq (n : ℕ) (δ : ℝ) :
    qPoly d n δ (0 : ℝ → Rd (d - 1)) =
      (List.range (2 ^ n + 1)).map (fun i : ℕ => ((i : ℝ) / 2 ^ n) • e₁ d) := by
  rw [qPoly]
  refine List.map_congr_left fun i hi => ?_
  exact qVert_zero_fun n δ (by have := List.mem_range.1 hi; omega)

/-- The subdivided chord: its edges have length `2⁻ⁿ`. -/
theorem norm_subdiv_edge (hd : 0 < d) (n i : ℕ) :
    ‖(((i + 1 : ℕ) : ℝ) / 2 ^ n) • e₁ d - ((i : ℝ) / 2 ^ n) • e₁ d‖ = ((2 : ℝ) ^ n)⁻¹ := by
  rw [← sub_smul, norm_smul, Lower.norm_e₁ hd, mul_one, Real.norm_eq_abs]
  push_cast
  rw [show ((i : ℝ) + 1) / 2 ^ n - i / 2 ^ n = ((2 : ℝ) ^ n)⁻¹ by field_simp; ring,
    abs_of_pos (by positivity)]

theorem plen_subdiv (hd : 0 < d) (n : ℕ) :
    plen (fun i : ℕ => ((i : ℝ) / 2 ^ n) • e₁ d) (2 ^ n) = 1 := by
  rw [plen, Finset.sum_congr rfl fun i _ => norm_subdiv_edge hd n i, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  push_cast
  exact mul_inv_cancel₀ (by positivity)

theorem polyLen_qPoly_zero (hd : 0 < d) (n : ℕ) (δ : ℝ) :
    polyLen (qPoly d n δ (0 : ℝ → Rd (d - 1))) = 1 := by
  rw [qPoly_zero_eq, polyLen_range_map]
  exact plen_subdiv hd n

theorem eDelta_qPoly_zero (hd : 0 < d) (n : ℕ) (δ : ℝ) :
    eDelta δ (qPoly d n δ (0 : ℝ → Rd (d - 1))) = 0 := by
  rw [eDelta, polyLen_qPoly_zero hd, Real.log_one, mul_zero]

/-- `Q_δ(0)` carries the uniform measure on the chord. -/
theorem polyMeasure_qPoly_zero (hd : 0 < d) (n : ℕ) (δ : ℝ) :
    polyMeasure (qPoly d n δ (0 : ℝ → Rd (d - 1))) = segMeasure 0 (e₁ d) := by
  have hτ : ∀ i : ℕ, i < 2 ^ n → (i : ℝ) / 2 ^ n ≤ ((i + 1 : ℕ) : ℝ) / 2 ^ n := fun i _ =>
    (mesh_lt n i).le
  rw [segMeasure_split 0 (e₁ d) (fun i : ℕ => (i : ℝ) / 2 ^ n) hτ (by simp)
    (by push_cast; exact div_self (by positivity)), qPoly_zero_eq, polyMeasure_range_map,
    plen_subdiv hd, segSum, segSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hlin : ∀ j : ℕ, lin 0 (e₁ d) ((j : ℝ) / 2 ^ n) = ((j : ℝ) / 2 ^ n) • e₁ d := by
    intro j; rw [lin, zero_add, sub_zero]
  rw [hlin, hlin, norm_subdiv_edge hd n i, div_one]
  congr 2
  push_cast
  field_simp
  ring

theorem shapeV_qPoly_zero (hd : 0 < d) (κ : Rd d → ℝ) (n : ℕ) (δ : ℝ) :
    shapeV κ (qPoly d n δ (0 : ℝ → Rd (d - 1))) = 0 := by
  rw [shapeV, polyMeasure_qPoly_zero hd, bandVecM_self]

/-- `Q_δ(0)` is a good polygon of the unit chord. -/
theorem qPoly_zero_mem (hd : 0 < d) (n : ℕ) (δ : ℝ) {a₀ : ℝ} (ha₀ : 0 ≤ a₀) :
    qPoly d n δ (0 : ℝ → Rd (d - 1)) ∈ goodFamily (2 ^ n) a₀ 0 (e₁ d) := by
  rw [qPoly_zero_eq]
  have he : ‖e₁ d - 0‖ = 1 := by rw [sub_zero, Lower.norm_e₁ hd]
  refine ⟨by simp, by rw [head?_range_map]; simp, ?_, ?_, ?_, ?_⟩
  · rw [getLast?_range_map]
    push_cast
    rw [div_self (by positivity), one_smul]
  · intro e he'
    obtain ⟨i, -, rfl⟩ := mem_dropLast_edges he'
    rw [norm_subdiv_edge hd n i, he]
    push_cast
    ring
  · intro e he'
    rw [edges_range_map] at he'
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 he'
    simp only
    rw [norm_subdiv_edge hd n i, he, mul_one, sub_zero, ← sub_smul, real_inner_smul_left,
      Lower.inner_e₁_self hd, mul_one]
    push_cast
    rw [show ((i : ℝ) + 1) / 2 ^ n - i / 2 ^ n = ((2 : ℝ) ^ n)⁻¹ by field_simp; ring]
    have h1 : Real.cos (1 / 10) ≤ 1 := Real.cos_le_one _
    have h2 : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := by positivity
    nlinarith
  · have h1 : polyLen ((List.range (2 ^ n + 1)).map (fun i : ℕ => ((i : ℝ) / 2 ^ n) • e₁ d)) =
        1 := by rw [polyLen_range_map]; exact plen_subdiv hd n
    rw [h1, he, mul_one]
    exact Real.one_le_exp ha₀

end Reference

/-! ## Step 1 (HA3 D5, Steps 1c–1d) -/

section Step1

/-- The covariance of the compact part:
`α² δ⁻¹ Λ(ν_{Q_δ(f)} - ν_I, ν_{Q_δ(g)} - ν_I)` (all-scale covariance of the kernel `κ`). -/
def cKer (κ : Rd d → ℝ) (n : ℕ) (α δ : ℝ) (f g : ℝ → Rd (d - 1)) : ℝ :=
  α ^ 2 * (δ⁻¹ * scaleCov κ (Ioi 0) (qMeasure d n δ f) (segMeasure 0 (e₁ d)) (qMeasure d n δ g)
    (segMeasure 0 (e₁ d)))

/-- The discrete energy of vertex values. -/
def vEnergy (n : ℕ) (v : Fin (2 ^ n + 1) → Rd (d - 1)) : ℝ :=
  (2 : ℝ) ^ n / 2 * ∑ k : Fin (2 ^ n), ‖v k.succ - v k.castSucc‖ ^ 2

theorem vEnergy_verts {n : ℕ} {f : ℝ → Rd (d - 1)} (hf : f ∈ Vg (Rd (d - 1)) n) :
    vEnergy n (verts n f) = energy f := by
  rw [HigherDimLFPP.Var.Vg_energy hf, vEnergy]
  congr 1
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [verts, Fin.val_succ, Fin.val_castSucc]
  push_cast
  ring_nf

theorem continuous_vEnergy (n : ℕ) : Continuous (vEnergy (d := d) n) := by
  unfold vEnergy
  fun_prop

variable {κ : Rd d → ℝ}

theorem psdOn_cKer (n : ℕ) (α : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (F : Finset (ℝ → Rd (d - 1))) :
    PSDOn F (cKer κ n α δ) :=
  HigherDimLFPP.Var.psdOn_const_mul (HigherDimLFPP.Var.psdOn_const_mul
    (psdOn_scaleCov (κ := κ) (Ioi 0) F (fun f => qMeasure d n δ f)
      (fun _ => segMeasure 0 (e₁ d))) (inv_nonneg.2 hδ)) (sq_nonneg α)

/-- `gaussianExpectedMax` is monotone in the (nonempty) index set. -/
theorem gEM_mono_of_subset {ι : Type*} {F F' : Finset ι} (hFF' : F ⊆ F') (hF : F.Nonempty)
    {C : ι → ι → ℝ} (hC : PSDOn F' C) (b : ι → ℝ) :
    gaussianExpectedMax F C b ≤ gaussianExpectedMax F' C b := by
  obtain ⟨v, hv, hvE⟩ := LQGDimension.exists_vecExpectedMax_eq_gaussianExpectedMax F' C hC
  have e : gaussianExpectedMax F C b = vecExpectedMax F v b := by
    rw [← LQGDimension.gaussianExpectedMax_gram_eq_vecExpectedMax]
    exact LQGDimension.gaussianExpectedMax_congr F b fun i hi j hj =>
      (hv i (hFF' hi) j (hFF' hj)).symm
  rw [e, hvE b]
  unfold vecExpectedMax
  have : Nonempty F := hF.to_subtype
  refine integral_mono (LQGDimension.integrable_iSup_inner_add F v b)
    (LQGDimension.integrable_iSup_inner_add F' v b) fun x => ?_
  exact ciSup_le fun i => le_ciSup (f := fun j : F' => ⟪v j, x⟫ + b j) (Finite.bddAbove_range _)
    ⟨i, hFF' i.2⟩

/-- **The scaling (2.5)** in the form used in Step 1d: for a finite `G ⊆ V_{n,d}`,
`E max_G (α G_d - β E) ≤ α^{4/3} β^{-1/3} A_{n,d}`. -/
theorem gEM_scaled_le_A (hd2 : 2 ≤ d) (n : ℕ) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (G : Finset (ℝ → Rd (d - 1))) (hG : ↑G ⊆ Vg (Rd (d - 1)) n) :
    gaussianExpectedMax G (fun f g => α ^ 2 * gCov f g) (fun f => -(β * vEnergy n (verts n f))) ≤
      α ^ (4 / 3 : ℝ) * β ^ (-1 / 3 : ℝ) * (A n d).toReal := by
  classical
  rw [gEM_congr_drift G _ (b' := fun f => -(β * energy f)) fun f hf => by
    rw [vEnergy_verts (hG hf)]]
  set G₁ : Finset (Vg (Rd (d - 1)) n) := G.subtype (· ∈ Vg (Rd (d - 1)) n) with hG₁
  have himg : G₁.image Subtype.val = G := by
    ext f
    simp only [hG₁, Finset.mem_image, Finset.mem_subtype, Subtype.exists, exists_and_right,
      exists_eq_right]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hG h, h⟩⟩
  have hpsd : PSDOn (G₁.image Subtype.val) (fun f g => α ^ 2 * gCov f g) :=
    HigherDimLFPP.Var.psdOn_const_mul (HigherDimLFPP.Var.gCov_psdOn_of_continuous _ fun f hf => by
      rw [himg] at hf
      exact HigherDimLFPP.Var.Vg_continuous (hG hf)) (sq_nonneg α)
  have h1 := gEM_subtype G₁ (fun f g => α ^ 2 * gCov f g) (fun f => -(β * energy f)) hpsd
  rw [himg] at h1
  rw [← h1]
  have h2 := le_iSup (fun F : Finset (Vg (Rd (d - 1)) n) =>
    ((gaussianExpectedMax F (fun f g => α ^ 2 * gCov (f : ℝ → Rd (d - 1)) g)
      (fun f => -(β * energy (f : ℝ → Rd (d - 1)))) : ℝ) : EReal)) G₁
  rw [HigherDimLFPP.Var.scaling25 n hα hβ] at h2
  have hAg : Ag (Rd (d - 1)) n = (((A n d).toReal : ℝ) : EReal) :=
    (HigherDimLFPP.Var.Ag_eq_coe_toReal (HigherDimLFPP.Var.A_ne_top hd2 n)).symm
  rw [hAg, ← EReal.coe_mul] at h2
  exact EReal.coe_le_coe_iff.1 h2

/-- Differences of kernel vectors with a common second measure. -/
theorem bandVecM_sub_common (hκ : IsLFPPKernel κ) {S : Set ℝ} {μ μ' ν : Measure (Rd d)}
    [IsFiniteMeasure μ] [IsFiniteMeasure μ'] [IsFiniteMeasure ν] (h : IsPairable κ S μ ν)
    (h' : IsPairable κ S μ' ν) : bandVecM κ S μ ν - bandVecM κ S μ' ν = bandVecM κ S μ μ' := by
  rw [bandVecM_sub_bandVecM hκ h h', add_comm ν μ', bandVecM_add_right hκ]

/-- The canonical distance of `cKer` is `α² δ⁻¹ Λ(ν_{Q_δ(f)} - ν_{Q_δ(g)})`. -/
theorem cKer_dist (hκ : IsLFPPKernel κ) (n : ℕ) (α δ : ℝ) {f g : ℝ → Rd (d - 1)}
    [IsFiniteMeasure (qMeasure d n δ f)] [IsFiniteMeasure (qMeasure d n δ g)]
    (hf : IsPairable κ (Ioi 0) (qMeasure d n δ f) (segMeasure 0 (e₁ d)))
    (hg : IsPairable κ (Ioi 0) (qMeasure d n δ g) (segMeasure 0 (e₁ d))) :
    cKer κ n α δ f f - 2 * cKer κ n α δ f g + cKer κ n α δ g g =
      α ^ 2 * (δ⁻¹ * scaleCov κ (Ioi 0) (qMeasure d n δ f) (qMeasure d n δ g)
        (qMeasure d n δ f) (qMeasure d n δ g)) := by
  have e := bandVecM_sub_common hκ hf hg
  have h2 : scaleCov κ (Ioi 0) (qMeasure d n δ f) (qMeasure d n δ g) (qMeasure d n δ f)
      (qMeasure d n δ g) = scaleCov κ (Ioi 0) (qMeasure d n δ f) (segMeasure 0 (e₁ d))
        (qMeasure d n δ f) (segMeasure 0 (e₁ d)) -
      2 * scaleCov κ (Ioi 0) (qMeasure d n δ f) (segMeasure 0 (e₁ d)) (qMeasure d n δ g)
        (segMeasure 0 (e₁ d)) + scaleCov κ (Ioi 0) (qMeasure d n δ g) (segMeasure 0 (e₁ d))
        (qMeasure d n δ g) (segMeasure 0 (e₁ d)) := by
    rw [scaleCov_self, ← e, norm_sub_sq_real, scaleCov, scaleCov, scaleCov,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  rw [h2]
  simp only [cKer]
  ring

/-- **Step 1** (HA3 D5): for `α, β, θ > 0` there is `δ₁ > 0` such that for `0 < δ < δ₁` and every
finite `F ⊆ G_K(0, e₁)`, `E max_F (αZ - βE_δ) ≤ α^{4/3} β^{-1/3} A_{n,d} + θ`. -/
theorem step1 (hd2 : 2 ≤ d) (hκ : IsLFPPKernel κ) (n : ℕ) {α β θ : ℝ} (hα : 0 < α)
    (hβ : 0 < β) (hθ : 0 < θ) :
    ∃ δ₁ > 0, ∀ δ ∈ Ioo (0 : ℝ) δ₁, ∀ F : Finset (List (Rd d)),
      ↑F ⊆ goodFamily (2 ^ n) (a0 n) 0 (e₁ d) →
      gaussianExpectedMax F (zKer κ α δ) (fun Q => -(β * eDelta δ Q)) ≤
        α ^ (4 / 3 : ℝ) * β ^ (-1 / 3 : ℝ) * (A n d).toReal + θ := by
  classical
  have hd : 0 < d := by omega
  have ha₀ : a0 n ≤ 1 / 2 := a0_le_half n
  -- shells
  obtain ⟨R₀, hR₀1, hshell⟩ := exists_shell_bound hd hκ n hα hβ (half_pos hθ)
  -- the compact family
  set R₁ : ℝ := 2 * Real.sqrt R₀ with hR₁
  have hR₁0 : 0 ≤ R₁ := by positivity
  set Ks := vertBall (Rd (d - 1)) n R₁ with hKs
  have hKsV : Ks ⊆ Vg (Rd (d - 1)) n := fun f hf => hf.1
  -- constants of the modulus
  obtain ⟨C₄, hC₄0, hC₄⟩ := transport_var_bound hκ 4
  set q : ℝ := ((2 : ℝ) ^ n)⁻¹ with hq
  have hq0 : 0 < q := by positivity
  set cc := cplConst (2 ^ n) (q / 2) 2 with hcc
  have hcc0 : 0 ≤ cc := cplConst_nonneg _ (by positivity) (by norm_num)
  set A₁ : ℝ := 2 * ((2 ^ n) ^ 2 * (2 * R₁) ^ 2) + 2 ^ n * (2 * R₁) ^ 2 / 2 with hA₁
  have hA₁0 : 0 ≤ A₁ := by positivity
  set δ₄ : ℝ := min (qDelta0 n R₁) (min (q / 2 / (2 * R₁ + 1))
    (min (1 / (8 * R₁ * ((2 : ℝ) ^ n) ^ 2 + 1)) (min 1 (q / 2 / (A₁ + 1))))) with hδ₄
  have hδ₄0 : 0 < δ₄ := by
    refine lt_min (qDelta0_pos n hR₁0) (lt_min (by positivity) (lt_min (by positivity)
      (lt_min one_pos (by positivity))))
  have hsmall : ∀ δ, 0 < δ → δ ≤ δ₄ → δ ≤ qDelta0 n R₁ ∧ δ * (2 * R₁) ≤ q / 2 ∧
      δ * (8 * R₁ * ((2 : ℝ) ^ n) ^ 2) ≤ 1 ∧ A₁ * δ ^ 2 ≤ q / 2 := by
    intro δ hδ hδ4
    have h1 : δ ≤ qDelta0 n R₁ := hδ4.trans (min_le_left _ _)
    have h2 : δ ≤ q / 2 / (2 * R₁ + 1) := hδ4.trans ((min_le_right _ _).trans (min_le_left _ _))
    have h3 : δ ≤ 1 / (8 * R₁ * ((2 : ℝ) ^ n) ^ 2 + 1) :=
      hδ4.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have h4 : δ ≤ 1 := hδ4.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
    have h5 : δ ≤ q / 2 / (A₁ + 1) := hδ4.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
    refine ⟨h1, ?_, ?_, ?_⟩
    · rw [le_div_iff₀ (by positivity)] at h2
      nlinarith
    · rw [le_div_iff₀ (by positivity)] at h3
      nlinarith
    · rw [le_div_iff₀ (by positivity)] at h5
      have hδ2 : δ ^ 2 ≤ δ := by nlinarith
      nlinarith
  -- the modulus of the compact part
  have hmod : ∀ᶠ δ in 𝓝[>] 0, ∀ f ∈ Ks, ∀ g ∈ Ks,
      cKer κ n α δ f f - 2 * cKer κ n α δ f g + cKer κ n α δ g g ≤
        (2 * α ^ 2 * C₄ * cc) * ‖verts n f - verts n g‖ := by
    filter_upwards [Ioo_mem_nhdsGT hδ₄0] with δ hδ f hf g hg
    obtain ⟨hs1, hs2, hs3, hs4⟩ := hsmall δ hδ.1 hδ.2.le
    obtain ⟨hpf, hGf, -, hSf⟩ := qPolygon_facts hd hR₁0 hδ.1 hs1 hf
    obtain ⟨hpg, hGg, -, hSg⟩ := qPolygon_facts hd hR₁0 hδ.1 hs1 hg
    have hI := (graphMeasure_growthBound (δ := δ) hd (f := 0) measurable_const).mono_const
      one_pos (show (2 : ℝ) ≤ 4 by norm_num)
    have hIs : ∀ᵐ z ∂(graphMeasure d δ 0), ‖z‖ ≤ 2 := by
      filter_upwards [ae_norm_le_graphMeasure (δ := δ) hd (f := 0) measurable_const
        (M := 0) fun x _ => by simp] with z hz
      linarith
    rw [graphMeasure_zero] at hI hIs
    have hpf' := (scaleCov_eq_logCov_of_growthBound hκ one_pos one_pos hGf hI hGf hI hSf hIs hSf
      hIs).1
    have hpg' := (scaleCov_eq_logCov_of_growthBound hκ one_pos one_pos hGg hI hGg hI hSg hIs hSg
      hIs).1
    rw [cKer_dist hκ n α δ hpf' hpg']
    -- the coupling of `Q_δ(f)` and `Q_δ(g)`
    obtain ⟨hef, hSf1⟩ := qPoly_edge_bounds hd (R := R₁) (δ := δ) (by rw [← hA₁]; linarith) hf
    obtain ⟨heg, hSg1⟩ := qPoly_edge_bounds hd (R := R₁) (δ := δ) (by rw [← hA₁]; linarith) hg
    have hcpl : HigherDimLFPP.CoupledWithin (qMeasure d n δ f) (qMeasure d n δ g)
        (cc * (2 * δ * ‖verts n f - verts n g‖)) := by
      have h := coupledWithin_polyMeasure_of_close (m := 2 ^ n) (Nat.two_pow_pos n)
        (V := qVert d n δ f) (V' := qVert d n δ g) (c := q / 2) (D := 2)
        (η := 2 * δ * ‖verts n f - verts n g‖) (half_pos hq0) hef heg hSf1 hSg1
        (fun i hi => norm_qVert_sub_le hd hR₁0 hδ.1 hs2 hs3 hf hg hi)
      exact h
    have hu : 0 ≤ cc * (2 * δ * ‖verts n f - verts n g‖) :=
      mul_nonneg hcc0 (by have := hδ.1; positivity)
    have hvar := (hC₄ (Ioi 0) measurableSet_Ioi subset_rfl (qMeasure d n δ f) (qMeasure d n δ g)
      1 _ one_pos hu hGf hGg hcpl).2
    rw [div_one] at hvar
    calc α ^ 2 * (δ⁻¹ * scaleCov κ (Ioi 0) (qMeasure d n δ f) (qMeasure d n δ g)
          (qMeasure d n δ f) (qMeasure d n δ g))
        ≤ α ^ 2 * (δ⁻¹ * (C₄ * (cc * (2 * δ * ‖verts n f - verts n g‖)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvar (inv_nonneg.2 hδ.1.le))
            (sq_nonneg α)
      _ = (2 * α ^ 2 * C₄ * cc) * ‖verts n f - verts n g‖ := by
          have hδ0 : δ ≠ 0 := hδ.1.ne'
          field_simp
  -- uniform convergence of the covariances (interface (I5))
  have hconv : TendstoUniformlyOn (fun δ (p : (ℝ → Rd (d - 1)) × (ℝ → Rd (d - 1))) =>
      cKer κ n α δ p.1 p.2) (fun p => α ^ 2 * gCov p.1 p.2) (𝓝[>] 0) (Ks ×ˢ Ks) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hε' : 0 < ε / (2 * α ^ 2) := by positivity
    filter_upwards [polygonCovLimit_scaleCov hd hκ n R₁ _ hε'] with δ h p hp
    rw [Real.dist_eq, cKer, ← mul_sub, abs_mul, abs_of_pos (by positivity), abs_sub_comm]
    have := h p.1 hp.1 p.2 hp.2
    calc α ^ 2 * |δ⁻¹ * scaleCov κ (Ioi 0) (qMeasure d n δ p.1) (segMeasure 0 (e₁ d))
          (qMeasure d n δ p.2) (segMeasure 0 (e₁ d)) - gCov p.1 p.2|
        ≤ α ^ 2 * (ε / (2 * α ^ 2)) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  -- uniform convergence of the drifts (the energy expansion)
  obtain ⟨Cn, δ₂, hδ₂, hEexp⟩ := abs_eDelta_qPoly_sub_energy_le hd n hR₁0
  have hbconv : TendstoUniformlyOn (fun δ f => -(β * eDelta δ (qPoly d n δ f)))
      (fun f => -(β * vEnergy n (verts n f))) (𝓝[>] 0) Ks := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hε' : 0 < ε / (2 * β * (|Cn| + 1)) := by positivity
    filter_upwards [Ioo_mem_nhdsGT (lt_min hδ₂ (lt_min one_pos hε'))] with δ hδ f hf
    have hδ1 : δ ≤ 1 := hδ.2.le.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hδε : δ ≤ ε / (2 * β * (|Cn| + 1)) :=
      hδ.2.le.trans ((min_le_right _ _).trans (min_le_right _ _))
    have h1 := hEexp δ hδ.1 (hδ.2.le.trans (min_le_left _ _)) f hf
    rw [Real.dist_eq, vEnergy_verts (hKsV hf), show -(β * energy f) - -(β * eDelta δ
      (qPoly d n δ f)) = β * (eDelta δ (qPoly d n δ f) - energy f) by ring, abs_mul,
      abs_of_pos hβ]
    have hδ2 : δ ^ 2 ≤ δ := by nlinarith [hδ.1]
    calc β * |eDelta δ (qPoly d n δ f) - energy f| ≤ β * (Cn * δ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 hβ.le
      _ ≤ β * ((|Cn| + 1) * δ) := by
          gcongr
          nlinarith [le_abs_self Cn, abs_nonneg Cn, sq_nonneg δ]
      _ ≤ β * ((|Cn| + 1) * (ε / (2 * β * (|Cn| + 1)))) := by gcongr
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  -- the expected-supremum limit on the compact family
  have hESL := expectedSupLimit_Vg Ks hKsV (isCompact_verts_vertBall n R₁) (cKer κ n α)
    (fun f g => α ^ 2 * gCov f g) (fun δ f => -(β * eDelta δ (qPoly d n δ f)))
    (fun v => -(β * vEnergy n v)) (2 * α ^ 2 * C₄ * cc)
    (fun δ hδ F _ => psdOn_cKer n α hδ.le F)
    (fun F hF => HigherDimLFPP.Var.psdOn_const_mul
      (HigherDimLFPP.Var.gCov_psdOn_of_continuous F fun f hf =>
        HigherDimLFPP.Var.Vg_continuous (hKsV (hF hf))) (sq_nonneg α))
    hconv hbconv hmod (continuous_const.mul (continuous_vEnergy (d := d) n)).neg.continuousOn
    (θ / 2) (half_pos hθ)
  obtain ⟨δ₃, hδ₃, hδ₃sub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hESL
  refine ⟨δ₃, hδ₃, fun δ hδ F hF => ?_⟩
  have hESLδ := hδ₃sub hδ
  simp only [Set.mem_ofPred_eq] at hESLδ
  have hA0 : 0 ≤ (A n d).toReal := EReal.toReal_nonneg (HigherDimLFPP.Var.A_nonneg n d)
  have hRHS0 : 0 ≤ α ^ (4 / 3 : ℝ) * β ^ (-1 / 3 : ℝ) * (A n d).toReal := by positivity
  rcases F.eq_empty_or_nonempty with rfl | hFne
  · rw [HigherDimLFPP.Var.gEM_empty]
    linarith
  -- add the reference polygon `Q_δ(0)`
  set Q₀ := qPoly d n δ (0 : ℝ → Rd (d - 1)) with hQ₀
  have hQ₀G : Q₀ ∈ goodFamily (2 ^ n) (a0 n) 0 (e₁ d) := qPoly_zero_mem hd n δ (a0_pos n).le
  set Fp := insert Q₀ F with hFp
  have hFpG : ↑Fp ⊆ goodFamily (2 ^ n) (a0 n) 0 (e₁ d) := by
    intro Q hQ
    rcases Finset.mem_insert.1 hQ with rfl | hQ'
    · exact hQ₀G
    · exact hF hQ'
  have hmono : gaussianExpectedMax F (zKer κ α δ) (fun Q => -(β * eDelta δ Q)) ≤
      gaussianExpectedMax Fp (zKer κ α δ) (fun Q => -(β * eDelta δ Q)) :=
    gEM_mono_of_subset (Finset.subset_insert _ _) hFne (psdOn_zKer Fp α hδ.1.le) _
  have hsh := hshell δ hδ.1 Fp hFpG Q₀ (Finset.mem_insert_self _ _) (shapeV_qPoly_zero hd κ n δ)
    (eDelta_qPoly_zero hd n δ)
  set F' := Fp.filter (fun Q => eDelta δ Q < R₀) with hF'
  have hF'G : ∀ Q ∈ F', Q ∈ goodFamily (2 ^ n) (a0 n) 0 (e₁ d) := fun Q hQ =>
    hFpG (Finset.mem_filter.1 hQ).1
  have hF'K : ↑(F'.image (prof n δ)) ⊆ Ks := by
    intro f hf
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hf
    exact prof_mem_vertBall hd ha₀ (hF'G Q hQ) hδ.1 (Finset.mem_filter.1 hQ).2.le
  obtain ⟨G'', hG''K, hG''⟩ := hESLδ (F'.image (prof n δ)) hF'K
  -- the compact part is a family of polygons `Q_δ(f)`
  have hid : gaussianExpectedMax F' (zKer κ α δ) (fun Q => -(β * eDelta δ Q)) =
      gaussianExpectedMax (F'.image (prof n δ)) (cKer κ n α δ)
        (fun f => -(β * eDelta δ (qPoly d n δ f))) := by
    rw [HigherDimLFPP.Var.gEM_image F' (prof n δ) _ _ (psdOn_cKer n α hδ.1.le _)]
    refine LQGDimension.Subadd.gEM_congr F' (fun Q hQ Q' hQ' => ?_) (fun Q hQ => ?_)
    · have e1 := qPoly_prof hd ha₀ (hF'G Q hQ) hδ.1.ne'
      have e2 := qPoly_prof hd ha₀ (hF'G Q' hQ') hδ.1.ne'
      simp only [zKer, cKer, qMeasure, e1, e2]
      rw [scaleCov_swap_left, scaleCov_swap_right, neg_neg]
      rfl
    · rw [qPoly_prof hd ha₀ (hF'G Q hQ) hδ.1.ne']
  have hscale := gEM_scaled_le_A hd2 n hα hβ G'' (hG''K.trans hKsV)
  linarith

end Step1

end HigherDimLFPP.Upper
