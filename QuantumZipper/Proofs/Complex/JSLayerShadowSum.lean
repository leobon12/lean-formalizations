import QuantumZipper.Proofs.Complex.JSLayerShadow

/-!
# EXT-JS node C1, part 2a: geometric Cauchy–Schwarz and the descendant partition

Blueprint `blueprint/EXT_JS_BLUEPRINT.md`, §2 ("(C1: layer decay LA ⇒ SH.)").

Source: P. W. Jones, S. K. Smirnov, *Removability theorems for Sobolev functions and
quasiconformal maps*, Ark. Mat. 38 (2000) 263–279, §2–3 (Proposition 1), where the vertical
chain along the dyadic descendants of a square is estimated with the elementary inequality
`(Σ_k x_k)² ≤ C_ε Σ_k 2^{εk} x_k²` (blueprint §2 C1). Here that inequality is formalised as
the weighted Cauchy–Schwarz `sq_tsum_le_mul_tsum_sq` in `ℝ≥0∞`, with the geometric weight `Q`.

Contents:

* `descIdx j k` — the `2^k` level-`(m+k)` descendants of the level-`m` index `j`;
* `sum_descIdx`, `sum_range_mul_range` — the descendants of a level partition the next level;
* `two_mul_mul_le_mul_sq_add_inv_mul_sq` — Young's inequality in `ℝ≥0∞` (own elementary proof);
* `sq_tsum_le_mul_tsum_sq` — the weighted Cauchy–Schwarz.

The chain argument and the final summation are in `JSLayerTentChain.lean` and
`JSLayerShadowFinal.lean`.
-/

noncomputable section

open Set Metric MeasureTheory Complex
open scoped ENNReal

namespace QuantumZipper
namespace JS

/-! ### Descendants of one dyadic index -/

/-- The `2 ^ k` level-`(m+k)` descendants of the level-`m` index `j`: the indices
`j * 2 ^ k + t`, `t < 2 ^ k`. -/
def descIdx (j k : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ k)).map ⟨fun t => j * 2 ^ k + t, fun _a _b h => Nat.add_left_cancel h⟩

lemma mem_descIdx_iff {j k j' : ℕ} : j' ∈ descIdx j k ↔ ∃ t < 2 ^ k, j * 2 ^ k + t = j' := by
  rw [descIdx, Finset.mem_map]
  exact ⟨fun ⟨t, ht, h⟩ => ⟨t, Finset.mem_range.1 ht, h⟩,
    fun ⟨t, ht, h⟩ => ⟨t, Finset.mem_range.2 ht, h⟩⟩

/-- **Descendant partition, product form**: the pairs `(j, t)` with `j < 2^m`, `t < 2^k`
correspond bijectively to the level-`(m+k)` indices via `j * 2^k + t`. -/
theorem sum_product_range {M : Type*} [AddCommMonoid M] (g : ℕ → M) (m k : ℕ) :
    ∑ x ∈ (Finset.range (2 ^ m)).product (Finset.range (2 ^ k)), g (x.1 * 2 ^ k + x.2) =
      ∑ j' ∈ Finset.range (2 ^ (m + k)), g j' := by
  refine Finset.sum_bij' (fun a _ => a.1 * 2 ^ k + a.2) (fun b _ => (b / 2 ^ k, b % 2 ^ k))
    ?_ ?_ ?_ ?_ (fun a _ => rfl)
  · rintro ⟨j, t⟩ ha
    obtain ⟨hj, ht⟩ := Finset.mem_product.1 ha
    rw [Finset.mem_range] at hj ht ⊢
    calc j * 2 ^ k + t < j * 2 ^ k + 2 ^ k := Nat.add_lt_add_left ht _
      _ = (j + 1) * 2 ^ k := by ring
      _ ≤ 2 ^ m * 2 ^ k := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ (m + k) := by rw [pow_add]
  · rintro b hb
    rw [Finset.mem_range] at hb
    refine Finset.mem_product.2 ⟨Finset.mem_range.2 ?_, Finset.mem_range.2 (Nat.mod_lt _
      (pow_pos (by norm_num : (0 : ℕ) < 2) k))⟩
    rw [Nat.div_lt_iff_lt_mul (pow_pos (by norm_num : (0 : ℕ) < 2) k), ← pow_add]
    exact hb
  · rintro ⟨j, t⟩ ha
    obtain ⟨hj, ht⟩ := Finset.mem_product.1 ha
    rw [Finset.mem_range] at hj ht
    have hdiv : (j * 2 ^ k + t) / 2 ^ k = j := by
      refine Nat.div_eq_of_lt_le (Nat.le_add_right _ _) ?_
      calc j * 2 ^ k + t < j * 2 ^ k + 2 ^ k := Nat.add_lt_add_left ht _
        _ = (j + 1) * 2 ^ k := by ring
    have hmod : (j * 2 ^ k + t) % 2 ^ k = t := by
      rw [Nat.mul_add_mod', Nat.mod_eq_of_lt ht]
    simp only [Prod.mk.injEq]
    exact ⟨hdiv, hmod⟩
  · rintro b hb
    rw [Finset.mem_range] at hb
    have h : (b / 2 ^ k) * 2 ^ k + b % 2 ^ k = b := by
      rw [mul_comm]
      exact Nat.div_add_mod b (2 ^ k)
    simp only [h]

/-- **Descendant partition, nested form**: the level-`(m+k)` indices are the level-`k`
descendants of the level-`m` indices. -/
theorem sum_range_mul_range {M : Type*} [AddCommMonoid M] (g : ℕ → M) (m k : ℕ) :
    ∑ j ∈ Finset.range (2 ^ m), ∑ t ∈ Finset.range (2 ^ k), g (j * 2 ^ k + t) =
      ∑ j' ∈ Finset.range (2 ^ (m + k)), g j' := by
  rw [← sum_product_range g m k]
  exact (Finset.sum_product (s := Finset.range (2 ^ m)) (t := Finset.range (2 ^ k))
    (f := fun x : ℕ × ℕ => g (x.1 * 2 ^ k + x.2))).symm

/-! ### Young's inequality and weighted Cauchy–Schwarz in `ℝ≥0∞` -/

/-- **Young's inequality** in `ℝ≥0∞`: `2 x y ≤ t x² + t⁻¹ y²` for every `t` (own elementary
proof: reduce to the finite case and use `(t x - y)² ≥ 0`). -/
lemma two_mul_mul_le_mul_sq_add_inv_mul_sq (t x y : ℝ≥0∞) :
    2 * (x * y) ≤ t * x ^ 2 + t⁻¹ * y ^ 2 := by
  rcases eq_or_ne t 0 with rfl | ht0
  · rcases eq_or_ne y 0 with rfl | hy0
    · simp
    · rw [ENNReal.inv_zero, zero_mul, zero_add,
        ENNReal.top_mul (pow_ne_zero 2 hy0)]
      exact le_top
  rcases eq_or_ne t ⊤ with rfl | htt
  · rcases eq_or_ne x 0 with rfl | hx0
    · simp
    · rw [ENNReal.inv_top, zero_mul, add_zero, ENNReal.top_mul (pow_ne_zero 2 hx0)]
      exact le_top
  rcases eq_or_ne x ⊤ with rfl | hxt
  · rw [ENNReal.top_pow (by norm_num : 2 ≠ 0), ENNReal.mul_top ht0, top_add]
    exact le_top
  rcases eq_or_ne y ⊤ with rfl | hyt
  · rw [ENNReal.top_pow (by norm_num : 2 ≠ 0), ENNReal.mul_top (ENNReal.inv_ne_zero.2 htt),
      add_top]
    exact le_top
  have hxsq : x ^ 2 ≠ ⊤ := by rw [pow_two]; exact ENNReal.mul_ne_top hxt hxt
  have hysq : y ^ 2 ≠ ⊤ := by rw [pow_two]; exact ENNReal.mul_ne_top hyt hyt
  have htinv : t⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 ht0
  refine (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top (ENNReal.ofNat_ne_top (n := 2)) (ENNReal.mul_ne_top hxt hyt))
    (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top htt hxsq,
      ENNReal.mul_ne_top htinv hysq⟩)).1 ?_
  have htr : (0 : ℝ) < t.toReal := ENNReal.toReal_pos ht0 htt
  have key : 2 * (x.toReal * y.toReal) ≤
      t.toReal * x.toReal ^ 2 + t.toReal⁻¹ * y.toReal ^ 2 := by
    have h := sq_nonneg (t.toReal * x.toReal - y.toReal)
    rw [sub_sq, mul_pow] at h
    have hstep : 2 * (x.toReal * y.toReal) - t.toReal * x.toReal ^ 2 ≤
        y.toReal ^ 2 / t.toReal := by
      rw [le_div_iff₀ htr]
      nlinarith [h]
    have hstep' : 2 * (x.toReal * y.toReal) - t.toReal * x.toReal ^ 2 ≤
        t.toReal⁻¹ * y.toReal ^ 2 := by
      rw [div_eq_mul_inv] at hstep
      linarith [hstep]
    linarith
  have h2t : (2 * (x * y)).toReal = 2 * (x.toReal * y.toReal) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
    norm_num
  have h3t : (t * x ^ 2 + t⁻¹ * y ^ 2).toReal =
      t.toReal * x.toReal ^ 2 + t.toReal⁻¹ * y.toReal ^ 2 := by
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top htt hxsq) (ENNReal.mul_ne_top htinv hysq),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
      ENNReal.toReal_inv]
  rw [h2t, h3t]
  exact key

/-- **Weighted Cauchy–Schwarz.** For `1 < Q ≠ ⊤` and any `e : ℕ → ℝ≥0∞`,
`(Σ_k e k)² ≤ (Σ_k Q^k (e k)²) (1 - Q⁻¹)⁻¹`. This is the elementary inequality
`(Σ x_k)² ≤ C_ε Σ 2^{εk} x_k²` of the blueprint (Jones–Smirnov §2), with the Young weight
`t = Q^{k-l} = Q^k (Q^l)⁻¹` and a symmetric two-sided sum so that both halves contribute the
same factor `Σ_l Q^{-l} = (1 - Q⁻¹)⁻¹`. The hypothesis `Q ≠ ⊤` is what makes the weight
invertible; the application (and the blueprint) only uses finite `Q`. -/
theorem sq_tsum_le_mul_tsum_sq {Q : ℝ≥0∞} (hQ : 1 < Q) (hQt : Q ≠ ⊤) (e : ℕ → ℝ≥0∞) :
    (∑' k, e k) ^ 2 ≤ (∑' k, Q ^ k * e k ^ 2) * (1 - Q⁻¹)⁻¹ := by
  classical
  have hQ0 : Q ≠ 0 := (lt_trans zero_lt_one hQ).ne'
  set g : ℕ → ℕ → ℝ≥0∞ := fun a b => (Q ^ a * (Q ^ b)⁻¹) * e a ^ 2 with hg
  -- Young with the weight `Q^k (Q^l)⁻¹`
  have hyoung : ∀ k l, 2 * (e k * e l) ≤ g k l + g l k := by
    intro k l
    have hwit : (Q ^ k * (Q ^ l)⁻¹)⁻¹ = Q ^ l * (Q ^ k)⁻¹ := by
      rw [ENNReal.mul_inv (Or.inl (pow_ne_zero k hQ0))
          (Or.inr (ENNReal.inv_ne_zero.2 (ENNReal.pow_ne_top hQt))),
        inv_inv, mul_comm]
    have h := two_mul_mul_le_mul_sq_add_inv_mul_sq (Q ^ k * (Q ^ l)⁻¹) (e k) (e l)
    simp only [hg] at h ⊢
    rw [hwit] at h
    exact h
  -- `(Σ e)² = Σ_k Σ_l e k * e l`
  have hsq : (∑' k, e k) ^ 2 = ∑' k, ∑' l, e k * e l := by
    rw [pow_two, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [← ENNReal.tsum_mul_right]
    exact tsum_congr fun l => mul_comm (e l) (e k)
  rw [hsq]
  have hgeom : (∑' l, (Q ^ l)⁻¹) = (1 - Q⁻¹)⁻¹ := by
    have h : (∑' l, (Q ^ l)⁻¹) = ∑' l, (Q⁻¹) ^ l := tsum_congr fun l => ENNReal.inv_pow
    rw [h, ENNReal.tsum_geometric]
  have hg1 : (∑' k, ∑' l, g k l) = (∑' k, Q ^ k * e k ^ 2) * (1 - Q⁻¹)⁻¹ := by
    have hinner : ∀ k, (∑' l, g k l) = (Q ^ k * e k ^ 2) * (1 - Q⁻¹)⁻¹ := by
      intro k
      have hgkl : ∀ l, g k l = (Q ^ k * e k ^ 2) * (Q ^ l)⁻¹ := by
        intro l
        rw [hg]
        ring
      rw [tsum_congr hgkl, ENNReal.tsum_mul_left, hgeom]
    rw [tsum_congr hinner, ENNReal.tsum_mul_right]
  have hsymm : (∑' k, ∑' l, g l k) = ∑' k, ∑' l, g k l := by
    rw [ENNReal.tsum_comm]
  have hsplit : (∑' k, ∑' l, (g k l + g l k)) =
      (∑' k, ∑' l, g k l) + (∑' k, ∑' l, g l k) := by
    simp only [ENNReal.tsum_add]
  have h2 : 2 * (∑' k, ∑' l, e k * e l) ≤
      2 * ((∑' k, Q ^ k * e k ^ 2) * (1 - Q⁻¹)⁻¹) := by
    calc 2 * (∑' k, ∑' l, e k * e l) = ∑' k, 2 * (∑' l, e k * e l) :=
          ENNReal.tsum_mul_left.symm
      _ = ∑' k, ∑' l, 2 * (e k * e l) := tsum_congr fun k => ENNReal.tsum_mul_left.symm
      _ ≤ ∑' k, ∑' l, (g k l + g l k) :=
          ENNReal.tsum_le_tsum fun k => ENNReal.tsum_le_tsum fun l => hyoung k l
      _ = (∑' k, ∑' l, g k l) + (∑' k, ∑' l, g l k) := hsplit
      _ = ((∑' k, Q ^ k * e k ^ 2) * (1 - Q⁻¹)⁻¹) * 2 := by rw [hg1, hsymm, hg1, mul_two]
      _ = 2 * ((∑' k, Q ^ k * e k ^ 2) * (1 - Q⁻¹)⁻¹) := by ring
  exact (ENNReal.mul_le_mul_iff_right (by simp : (2 : ℝ≥0∞) ≠ 0)
    (by simp : (2 : ℝ≥0∞) ≠ ⊤)).1 h2

end JS

end QuantumZipper
