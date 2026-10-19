import HigherDimLFPP.Var.Bridge
import Mathlib.Analysis.Subadditive

/-!
# The Gaussian part of Theorem 1.1, `κ₂ = a*/log 16`, and (1.8)

For every `d ≥ 2` (paper §2, Lemma 2.1 and Lemma 2.3; HA1 D7, D8, D11, D12):

* `A_{n,d}` is finite: `A_{n,d} ≤ (d-1) A_n(ℝ) ≤ (d-1) a_n < ∞` (`Ag_Rd_le`, `Ag_real_ne_top`);
* `A_{n+r,d} ≤ A_{n,d} + A_{r,d}` (`Ag_subadditive`);
* Fekete (`Subadditive.tendsto_lim`): `A_{n,d}/(n log 2) → κ_d = inf_{n ≥ 1} A_{n,d}/(n log 2)`;
* `κ₂ = a*/log 16` (`kappa_two_eq_impl`): along `n = 4k`, `A_{4k,2} = a_k` and `a_k/k → a*`;
* (1.8) `(d-1)^{2/3} κ₂ ≤ κ_d ≤ (d-1) κ₂` (`dimension_comparison_impl`), from Lemma 2.3 at each `n`
  and passage to the limit;
* `0 < κ_d` from `κ_d ≥ (d-1)^{2/3} κ₂` and `κ₂ = a*/log 16 > 0` (`LQGDimension.theorem11_aStar`;
  ruling H4: no LFPP input).

The Fekete assembly follows `LQGDimension/Assembly/AStar.lean` (`subadditive_a`, `aStar_eq_lim`,
`tendsto_a_div`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace HigherDimLFPP

namespace Var

/-! ## Finiteness and subadditivity of `A_{n,d}` -/

lemma A_nonneg (n d : ℕ) : 0 ≤ A n d := Ag_nonneg n

lemma A_ne_bot (n d : ℕ) : A n d ≠ ⊥ := Ag_ne_bot n

lemma A_ne_top {d : ℕ} (hd : 2 ≤ d) (n : ℕ) : A n d ≠ ⊤ := by
  have hm : 1 ≤ d - 1 := by omega
  have h1 : A n d ≤ ((d - 1 : ℕ) : EReal) * Ag ℝ n := Ag_Rd_le hm n
  have hfin : ((d - 1 : ℕ) : EReal) * Ag ℝ n ≠ ⊤ := by
    rw [← Ag_eq_coe_toReal (Ag_real_ne_top n),
      show ((d - 1 : ℕ) : EReal) = (((d - 1 : ℕ) : ℝ) : EReal) from rfl, ← EReal.coe_mul]
    exact EReal.coe_ne_top _
  exact ne_top_of_le_ne_top hfin h1

lemma A_subadd (d n r : ℕ) : A (n + r) d ≤ A n d + A r d := Ag_subadditive n r

lemma A_coe_toReal {d : ℕ} (hd : 2 ≤ d) (n : ℕ) : (((A n d).toReal : ℝ) : EReal) = A n d :=
  EReal.coe_toReal (A_ne_top hd n) (A_ne_bot n d)

lemma A_toReal_nonneg (n d : ℕ) : 0 ≤ (A n d).toReal := EReal.toReal_nonneg (A_nonneg n d)

lemma A_toReal_subadd {d : ℕ} (hd : 2 ≤ d) (n r : ℕ) :
    (A (n + r) d).toReal ≤ (A n d).toReal + (A r d).toReal := by
  have h := A_subadd d n r
  rw [← A_coe_toReal hd (n + r), ← A_coe_toReal hd n, ← A_coe_toReal hd r, ← EReal.coe_add] at h
  exact EReal.coe_le_coe_iff.1 h

/-! ## Fekete's lemma -/

/-- The real subadditive sequence `A_{n,d}/log 2`. -/
def uSeq (d n : ℕ) : ℝ := (A n d).toReal / Real.log 2

lemma uSeq_div (d n : ℕ) : uSeq d n / n = (A n d).toReal / ((n : ℝ) * Real.log 2) := by
  rw [uSeq, div_div, mul_comm (Real.log 2)]

lemma uSeq_subadditive {d : ℕ} (hd : 2 ≤ d) : Subadditive (uSeq d) := fun n r => by
  have h := A_toReal_subadd hd n r
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  simp only [uSeq]
  rw [← add_div]
  exact div_le_div_of_nonneg_right h hl.le

lemma uSeq_div_nonneg (d n : ℕ) : 0 ≤ uSeq d n / n :=
  div_nonneg (div_nonneg (A_toReal_nonneg n d) (Real.log_pos one_lt_two).le) (Nat.cast_nonneg n)

lemma bddBelow_uSeq_div (d : ℕ) : BddBelow (Set.range fun n : ℕ => uSeq d n / n) :=
  ⟨0, by rintro _ ⟨n, rfl⟩; exact uSeq_div_nonneg d n⟩

lemma kappa_eq_iInf_uSeq (d : ℕ) : kappa d = ⨅ n : ℕ+, uSeq d n / (n : ℕ) := by
  unfold kappa
  congr 1
  funext n
  rw [uSeq_div]

/-- `κ_d` (the infimum over `n ≥ 1`) is Mathlib's `Subadditive.lim` (the infimum over `n ≥ 1` of
the same values).  (Pattern of `LQGDimension.Assembly.aStar_eq_lim`.) -/
lemma kappa_eq_lim {d : ℕ} (hd : 2 ≤ d) : kappa d = (uSeq_subadditive hd).lim := by
  rw [kappa_eq_iInf_uSeq, Subadditive.lim, iInf]
  congr 1
  ext y
  simp only [Set.mem_range, Set.mem_image, Set.mem_Ici]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨(n : ℕ), n.2, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨⟨n, hn⟩, rfl⟩

/-- **Fekete**: `A_{n,d}/(n log 2) → κ_d` (HA1 D8). -/
theorem tendsto_A_div {d : ℕ} (hd : 2 ≤ d) :
    Tendsto (fun n : ℕ => (A n d).toReal / ((n : ℝ) * Real.log 2)) atTop (𝓝 (kappa d)) := by
  have h := (uSeq_subadditive hd).tendsto_lim (bddBelow_uSeq_div d)
  rw [← kappa_eq_lim hd] at h
  refine h.congr fun n => ?_
  exact uSeq_div d n

lemma kappa_nonneg {d : ℕ} (hd : 2 ≤ d) : 0 ≤ kappa d :=
  ge_of_tendsto' (tendsto_A_div hd) fun n =>
    div_nonneg (A_toReal_nonneg n d) (mul_nonneg (Nat.cast_nonneg n)
      (Real.log_pos one_lt_two).le)

end Var

open Var

/-! ## `κ₂ = a*/log 16` -/

/-- **`κ₂ = a*/log 16`** (HA1 D11, ruling H4): `A_{4k,2} = a_k` and `a_k/k → a*`. -/
theorem kappa_two_eq_impl : kappa 2 = LQGDimension.aStar / Real.log 16 := by
  have hlim := tendsto_A_div (d := 2) le_rfl
  have h4 : Tendsto (fun k : ℕ => 4 * k) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩
  have hsub := hlim.comp h4
  have ha := (LQGDimension.theorem11_aStar.2.2.2).div_const (Real.log 16)
  have hlog : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have heq : ∀ k : ℕ, (fun n : ℕ => (A n 2).toReal / ((n : ℝ) * Real.log 2)) (4 * k) =
      LQGDimension.a k / k / Real.log 16 := by
    intro k
    simp only
    rw [A_two_four_mul, hlog, div_div]
    push_cast
    congr 1
    ring
  exact tendsto_nhds_unique (hsub.congr heq) ha

lemma kappa_two_pos : 0 < kappa 2 := by
  rw [kappa_two_eq_impl]
  exact div_pos LQGDimension.theorem11_aStar.2.2.1 (Real.log_pos (by norm_num))

/-! ## The dimension comparison (1.8) -/

namespace Var

/-- Lemma 2.3 in real form at each `n`: `(d-1)^{2/3} A_{n,2} ≤ A_{n,d} ≤ (d-1) A_{n,2}`. -/
lemma lemma23_real {d : ℕ} (hd : 2 ≤ d) (n : ℕ) :
    ((d : ℝ) - 1) ^ (2 / 3 : ℝ) * (A n 2).toReal ≤ (A n d).toReal ∧
      (A n d).toReal ≤ ((d : ℝ) - 1) * (A n 2).toReal := by
  have hm : 1 ≤ d - 1 := by omega
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d)]; norm_num
  have h2 : (((A n 2).toReal : ℝ) : EReal) = Ag ℝ n := by
    rw [A_coe_toReal le_rfl n, A_two_eq]
  constructor
  · have h := Ag_Rd_ge hm n
    change _ ≤ A n d at h
    rw [← h2, ← EReal.coe_mul, hcast] at h
    rw [← A_coe_toReal hd n] at h
    exact EReal.coe_le_coe_iff.1 h
  · have h := Ag_Rd_le hm n
    change A n d ≤ _ at h
    rw [← h2, show ((d - 1 : ℕ) : EReal) = (((d - 1 : ℕ) : ℝ) : EReal) from rfl,
      ← EReal.coe_mul, hcast] at h
    rw [← A_coe_toReal hd n] at h
    exact EReal.coe_le_coe_iff.1 h

end Var

/-- **(1.8)** `(d-1)^{2/3} κ₂ ≤ κ_d ≤ (d-1) κ₂` for every `d ≥ 2` (Lemma 2.3 and HA1 D12). -/
theorem dimension_comparison_impl : ∀ d : ℕ, 2 ≤ d →
    ((d : ℝ) - 1) ^ (2 / 3 : ℝ) * kappa 2 ≤ kappa d ∧ kappa d ≤ ((d : ℝ) - 1) * kappa 2 := by
  intro d hd
  have hd2 := tendsto_A_div (d := 2) le_rfl
  have hdd := tendsto_A_div hd
  have hpos : ∀ n : ℕ, 0 ≤ (n : ℝ) * Real.log 2 := fun n =>
    mul_nonneg (Nat.cast_nonneg n) (Real.log_pos one_lt_two).le
  constructor
  · refine le_of_tendsto_of_tendsto' (hd2.const_mul (((d : ℝ) - 1) ^ (2 / 3 : ℝ))) hdd
      fun n => ?_
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (lemma23_real hd n).1 (hpos n)
  · refine le_of_tendsto_of_tendsto' hdd (hd2.const_mul ((d : ℝ) - 1)) fun n => ?_
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (lemma23_real hd n).2 (hpos n)

/-! ## Theorem 1.1, Gaussian part -/

/-- **Theorem 1.1 (Gaussian part)**, for every `d ≥ 2` with no hypotheses: `A_{n,d}` is finite and
subadditive, `A_{n,d}/(n log 2) → κ_d` (`κ_d` is the infimum by definition), and `0 < κ_d`. -/
theorem theorem11_variational (d : ℕ) (hd : 2 ≤ d) :
    (∀ n : ℕ, A n d ≠ ⊥ ∧ A n d ≠ ⊤) ∧
    (∀ n r : ℕ, A (n + r) d ≤ A n d + A r d) ∧
    Tendsto (fun n : ℕ => (A n d).toReal / ((n : ℝ) * Real.log 2)) atTop (𝓝 (kappa d)) ∧
    0 < kappa d := by
  refine ⟨fun n => ⟨A_ne_bot n d, A_ne_top hd n⟩, fun n r => A_subadd d n r, tendsto_A_div hd,
    ?_⟩
  have hm : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hc : 0 < ((d : ℝ) - 1) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  exact lt_of_lt_of_le (mul_pos hc kappa_two_pos) (dimension_comparison_impl d hd).1

end HigherDimLFPP
