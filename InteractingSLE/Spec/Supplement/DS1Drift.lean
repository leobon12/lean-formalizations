/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.DS1Fun
import InteractingSLE.Spec.Supplement.GB5Path

/-!
# Lemma DS1: the pointwise drift bounds

Packet PROVE-T14-TIP (specification supplement §12, **Lemma DS1**, `source/spec/p529-576.md` L523–L575, pp. 551–553).

**Deterministic part.** For the test function `f = fn p ν r` of `DS1Fun.lean`:

* `fn_nonneg`, `fn_le`: `0 ≤ f ≤ (3r)^p` on `[0, ∞)` (`ν ≤ r`);
* `gen_ge_of_lt`: on `0 < x < r`, if the drift `v` of `X₁` satisfies `v ≥ ε/x − C₀`, then
  `f'(x) v + (κ/2) f''(x) ≥ (pε/4)(x + ν)^{p−2}` (the source's "its Itô drift is at least
  `p(X₁ + ν)^{p−2}[ε − κ(1 − p)/2 − C₀(X₁ + ν)] ≥ c₀(X₁ + ν)^{p−2}`"), given `κ(1 − p) ≤ ε` and `2rC₀ ≤ ε/4`;
* `gen_ge_of_mem_Icc`: on `[r, 2r]`, `|v| ≤ V` gives `f'(x) v + (κ/2) f''(x) ≥ −(A₁V + (κ/2)A₂)`
  ("the drift there is bounded below by a uniform negative constant"), with `A₁`, `A₂` independent of `ν ≤ r`;
* `gen_eq_zero_of_ge`: for `x ≥ 2r` the generator vanishes ("outside `[0, 2r]` the derivatives vanish").

**Abel summation (DS1.4).** `abel_inner`: if `0 < X₀ ≤ X₁ ≤ ⋯` and every inner partial sum has `S_i + 2 ≥ ε`, then
`2/X₀ + Σ_{i<m} ρ_i/X_i ≥ ε/X₀`.

**The drift of `X₁` along a path** (`drift_ge`, `abs_drift_le`): at a non-collision time before the far stop, with
`X₁ ≤ 2r ≤ a/4` and the cross gap at least `a`, the density of the Itô coordinate `Λ = X₁ + √κ B`,
`2/X₁ + Σ_R ρ_j/X_j − Σ_L ρ_i/Y_i`, is at least `ε/X₁ − C₀` with `C₀ = n_R R/g + n_L R·4/(3a)`
(the source's "`b_X ≥ ε/X₁ − C₀` in this region"); for `X₁ ∈ [r, 2r]` its modulus is at most
`(2 + n_R R)/r + n_L R·4/(3a)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp12

namespace DS1

/-! ### Bounds on the test function -/

section Fun

variable {p ν r x : ℝ}

theorem pw_nonneg (hp : 0 ≤ p) (hν : 0 ≤ ν) (hx : 0 ≤ x) : 0 ≤ pw p ν x := by
  unfold pw
  have := Real.rpow_le_rpow hν (by linarith : ν ≤ x + ν) hp
  linarith

theorem pw_le (hp : 0 ≤ p) (hν : 0 ≤ ν) (hx : 0 ≤ x) {M : ℝ} (hM : x + ν ≤ M) : pw p ν x ≤ M ^ p := by
  unfold pw
  have h1 := Real.rpow_le_rpow (by linarith) hM hp
  have h2 := Real.rpow_nonneg hν p
  linarith

theorem fn_nonneg (hp : 0 ≤ p) (hν : 0 ≤ ν) (hx : 0 ≤ x) : 0 ≤ fn p ν r x :=
  mul_nonneg (pw_nonneg hp hν hx) (cut_nonneg r x)

theorem fn_le (hp : 0 ≤ p) (hν : 0 ≤ ν) (hνr : ν ≤ r) (hr : 0 < r) (hx : 0 ≤ x) :
    fn p ν r x ≤ (3 * r) ^ p := by
  unfold fn
  rcases lt_or_ge x (2 * r) with h | h
  · have h1 := pw_le hp hν hx (M := 3 * r) (by linarith)
    have h2 := pw_nonneg hp hν hx
    calc pw p ν x * cut r x ≤ pw p ν x * 1 := mul_le_mul_of_nonneg_left (cut_le_one r x) h2
      _ ≤ (3 * r) ^ p := by linarith
  · rw [cut_eq_zero hr h, mul_zero]; exact Real.rpow_nonneg (by linarith) p

theorem fn1_eq_of_lt (hr : 0 < r) (hx : x < r) : fn1 p ν r x = pw1 p ν x := by
  simp [fn1, cut_eq_one hr hx.le, cut1_eq_zero_of_lt hr hx]

theorem fn2_eq_of_lt (hr : 0 < r) (hx : x < r) : fn2 p ν r x = pw2 p ν x := by
  simp [fn2, cut_eq_one hr hx.le, cut1_eq_zero_of_lt hr hx, cut2_eq_zero_of_lt hr hx]

theorem fn1_eq_zero_of_ge (hr : 0 < r) (hx : 2 * r ≤ x) : fn1 p ν r x = 0 := by
  simp [fn1, cut_eq_zero hr hx, cut1_eq_zero_of_ge hr hx]

theorem fn2_eq_zero_of_ge (hr : 0 < r) (hx : 2 * r ≤ x) : fn2 p ν r x = 0 := by
  simp [fn2, cut_eq_zero hr hx, cut1_eq_zero_of_ge hr hx, cut2_eq_zero_of_ge hr hx]

/-- **The generator vanishes for `x ≥ 2r`.** -/
theorem gen_eq_zero_of_ge (hr : 0 < r) (hx : 2 * r ≤ x) (κ v : ℝ) :
    fn1 p ν r x * v + κ / 2 * fn2 p ν r x = 0 := by
  rw [fn1_eq_zero_of_ge hr hx, fn2_eq_zero_of_ge hr hx]; ring

/-- **The generator on `(0, r)`.** -/
theorem gen_ge_of_lt {κ ε C₀ v : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hκ : 0 ≤ κ) (hν : 0 < ν) (hνr : ν ≤ r)
    (hr : 0 < r) (hx0 : 0 < x) (hxr : x < r) (hκp : κ * (1 - p) ≤ ε) (hC₀ : 0 ≤ C₀)
    (hrC : 2 * r * C₀ ≤ ε / 4) (hv : ε / x - C₀ ≤ v) :
    p * ε / 4 * (x + ν) ^ (p - 2) ≤ fn1 p ν r x * v + κ / 2 * fn2 p ν r x := by
  rw [fn1_eq_of_lt hr hxr, fn2_eq_of_lt hr hxr, pw1, pw2]
  set u := x + ν with hu
  have hu0 : 0 < u := by linarith
  set y := u ^ (p - 2) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos hu0 _
  have hp1' : u ^ (p - 1) = y * u := by
    rw [hy, ← Real.rpow_add_one hu0.ne']; ring_nf
  rw [hp1']
  have hpyu : 0 ≤ p * (y * u) := by positivity
  have h1 : p * (y * u) * (ε / x - C₀) ≤ p * (y * u) * v := mul_le_mul_of_nonneg_left hv hpyu
  have hε : 0 ≤ ε := by have := mul_nonneg hκ (by linarith : (0 : ℝ) ≤ 1 - p); linarith
  have hxu : x ≤ u := by rw [hu]; linarith
  have hux : ε ≤ u * (ε / x) := by
    rw [mul_div_assoc', le_div_iff₀ hx0, mul_comm u ε]
    exact mul_le_mul_of_nonneg_left hxu hε
  have hu2 : u ≤ 2 * r := by rw [hu]; linarith
  have huC : u * C₀ ≤ 2 * r * C₀ := mul_le_mul_of_nonneg_right hu2 hC₀
  have h2 : p * y * (ε - ε / 4) ≤ p * (y * u) * (ε / x - C₀) := by
    have : p * (y * u) * (ε / x - C₀) = p * y * (u * (ε / x) - u * C₀) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h3 : -(p * y * (ε / 2)) ≤ κ / 2 * (p * (p - 1) * y) := by
    have : κ / 2 * (p * (p - 1) * y) = -(p * y * (κ * (1 - p) / 2)) := by ring
    rw [this, neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  nlinarith

/-- The bound on `|f'|` on `[r, 2r]`. -/
def bnd1 (p r K : ℝ) : ℝ := r ^ (p - 1) + (3 * r) ^ p * (K / r)

/-- The bound on `|f''|` on `[r, 2r]`. -/
def bnd2 (p r K : ℝ) : ℝ := r ^ (p - 2) + 2 * (r ^ (p - 1) * (K / r)) + (3 * r) ^ p * (K / r ^ 2)

theorem bnd1_nonneg (hr : 0 < r) {K : ℝ} (hK : 0 ≤ K) : 0 ≤ bnd1 p r K := by
  unfold bnd1; have := Real.rpow_nonneg hr.le (p - 1); have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 3 * r) p
  positivity

theorem bnd2_nonneg (hr : 0 < r) {K : ℝ} (hK : 0 ≤ K) : 0 ≤ bnd2 p r K := by
  unfold bnd2; have := Real.rpow_nonneg hr.le (p - 2); have := Real.rpow_nonneg hr.le (p - 1)
  have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 3 * r) p
  positivity

theorem abs_fn1_le (hp0 : 0 < p) (hp1 : p < 1) (hν : 0 < ν) (hνr : ν ≤ r) (hr : 0 < r) (hxr : r ≤ x)
    (hx2 : x ≤ 2 * r) {K : ℝ} (hK : ∀ y, |deriv Real.smoothTransition y| ≤ K ∧
      |deriv (deriv Real.smoothTransition) y| ≤ K) :
    |fn1 p ν r x| ≤ bnd1 p r K := by
  have hu : r ≤ x + ν := by linarith
  have hu0 : 0 < x + ν := by linarith
  have hpw1 : |pw1 p ν x| ≤ r ^ (p - 1) := by
    rw [pw1, abs_mul, abs_of_pos hp0, abs_of_nonneg (Real.rpow_nonneg hu0.le _)]
    have := Real.rpow_le_rpow_of_nonpos hr hu (by linarith : p - 1 ≤ 0)
    have := Real.rpow_nonneg hu0.le (p - 1)
    nlinarith
  have hpw : |pw p ν x| ≤ (3 * r) ^ p := by
    rw [abs_of_nonneg (pw_nonneg hp0.le hν.le (by linarith))]
    exact pw_le hp0.le hν.le (by linarith) (by linarith)
  have hc : |cut r x| ≤ 1 := by rw [abs_of_nonneg (cut_nonneg r x)]; exact cut_le_one r x
  have hc1 := abs_cut1_le hr (fun y => (hK y).1) x
  unfold fn1 bnd1
  calc |pw1 p ν x * cut r x + pw p ν x * cut1 r x| ≤ |pw1 p ν x| * |cut r x| + |pw p ν x| * |cut1 r x| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ r ^ (p - 1) * 1 + (3 * r) ^ p * (K / r) := by
        gcongr
    _ = _ := by ring

theorem abs_fn2_le (hp0 : 0 < p) (hp1 : p < 1) (hν : 0 < ν) (hνr : ν ≤ r) (hr : 0 < r) (hxr : r ≤ x)
    (hx2 : x ≤ 2 * r) {K : ℝ} (hK : ∀ y, |deriv Real.smoothTransition y| ≤ K ∧
      |deriv (deriv Real.smoothTransition) y| ≤ K) :
    |fn2 p ν r x| ≤ bnd2 p r K := by
  have hu : r ≤ x + ν := by linarith
  have hu0 : 0 < x + ν := by linarith
  have hpw2 : |pw2 p ν x| ≤ r ^ (p - 2) := by
    rw [pw2, abs_mul, abs_of_nonneg (Real.rpow_nonneg hu0.le _)]
    have h1 := Real.rpow_le_rpow_of_nonpos hr hu (by linarith : p - 2 ≤ 0)
    have h2 := Real.rpow_nonneg hu0.le (p - 2)
    have h3 : |p * (p - 1)| ≤ 1 := by
      rw [abs_le]; constructor <;> nlinarith
    calc |p * (p - 1)| * (x + ν) ^ (p - 2) ≤ 1 * (x + ν) ^ (p - 2) := mul_le_mul_of_nonneg_right h3 h2
      _ ≤ r ^ (p - 2) := by linarith
  have hpw1 : |pw1 p ν x| ≤ r ^ (p - 1) := by
    rw [pw1, abs_mul, abs_of_pos hp0, abs_of_nonneg (Real.rpow_nonneg hu0.le _)]
    have := Real.rpow_le_rpow_of_nonpos hr hu (by linarith : p - 1 ≤ 0)
    have := Real.rpow_nonneg hu0.le (p - 1)
    nlinarith
  have hpw : |pw p ν x| ≤ (3 * r) ^ p := by
    rw [abs_of_nonneg (pw_nonneg hp0.le hν.le (by linarith))]
    exact pw_le hp0.le hν.le (by linarith) (by linarith)
  have hc : |cut r x| ≤ 1 := by rw [abs_of_nonneg (cut_nonneg r x)]; exact cut_le_one r x
  have hc1 := abs_cut1_le hr (fun y => (hK y).1) x
  have hc2 := abs_cut2_le hr (fun y => (hK y).2) x
  unfold fn2 bnd2
  calc |pw2 p ν x * cut r x + 2 * (pw1 p ν x * cut1 r x) + pw p ν x * cut2 r x|
        ≤ |pw2 p ν x * cut r x| + |2 * (pw1 p ν x * cut1 r x)| + |pw p ν x * cut2 r x| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ = |pw2 p ν x| * |cut r x| + 2 * (|pw1 p ν x| * |cut1 r x|) + |pw p ν x| * |cut2 r x| := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_two]
    _ ≤ r ^ (p - 2) * 1 + 2 * (r ^ (p - 1) * (K / r)) + (3 * r) ^ p * (K / r ^ 2) := by
        gcongr
    _ = _ := by ring

/-- **The generator on `[r, 2r]`.** -/
theorem gen_ge_of_mem_Icc {κ v V : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hκ : 0 ≤ κ) (hν : 0 < ν) (hνr : ν ≤ r)
    (hr : 0 < r) (hxr : r ≤ x) (hx2 : x ≤ 2 * r) (hv : |v| ≤ V) {K : ℝ}
    (hK : ∀ y, |deriv Real.smoothTransition y| ≤ K ∧ |deriv (deriv Real.smoothTransition) y| ≤ K) :
    -(bnd1 p r K * V + κ / 2 * bnd2 p r K) ≤ fn1 p ν r x * v + κ / 2 * fn2 p ν r x := by
  have h1 := abs_fn1_le hp0 hp1 hν hνr hr hxr hx2 hK
  have h2 := abs_fn2_le hp0 hp1 hν hνr hr hxr hx2 hK
  have hb1 : |fn1 p ν r x * v| ≤ bnd1 p r K * V := by
    rw [abs_mul]; exact mul_le_mul h1 hv (abs_nonneg _) ((abs_nonneg _).trans h1)
  have hb2 : |κ / 2 * fn2 p ν r x| ≤ κ / 2 * bnd2 p r K := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ κ / 2)]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have := neg_abs_le (fn1 p ν r x * v)
  have := neg_abs_le (κ / 2 * fn2 p ν r x)
  linarith

end Fun

/-! ### Abel summation (DS1.4) -/

/-- **(DS1.4)**: if `0 < X₀ ≤ X₁ ≤ ⋯ ≤ X_{m−1}` and the partial sums satisfy `S_i + 2 ≥ ε` (`i < m`, `m ≥ 1`),
then `2/X₀ + Σ_{i<m} ρ_i/X_i ≥ ε/X₀`. -/
theorem abel_inner {ρ X : ℕ → ℝ} {ε : ℝ} {m : ℕ} (hm : 0 < m) (hX0 : 0 < X 0)
    (hX : ∀ i, i + 1 < m → X i ≤ X (i + 1))
    (hS : ∀ i < m, ε ≤ ∑ l ∈ range (i + 1), ρ l + 2) :
    ε / X 0 ≤ 2 / X 0 + ∑ i ∈ range m, ρ i / X i := by
  -- the inductive claim: `T_m ≥ ε(1/X₀ − 1/X_{m−1}) + (S_{m−1} + 2)/X_{m−1}`
  have hpos : ∀ i, i < m → 0 < X i := by
    intro i
    induction i with
    | zero => intro _; exact hX0
    | succ i ih => intro hi; exact lt_of_lt_of_le (ih (by omega)) (hX i hi)
  have key : ∀ k, k + 1 ≤ m → ε * (1 / X 0 - 1 / X k) + (∑ l ∈ range (k + 1), ρ l + 2) / X k ≤
      2 / X 0 + ∑ i ∈ range (k + 1), ρ i / X i := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [sub_self, mul_zero, zero_add, range_one, sum_singleton]
      rw [add_div]; ring_nf; exact le_rfl
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have hXk := hpos k (by omega)
      have hXk1 := hpos (k + 1) (by omega)
      have hle : X k ≤ X (k + 1) := hX k (by omega)
      have hinv : 1 / X (k + 1) ≤ 1 / X k := one_div_le_one_div_of_le hXk hle
      have hSk := hS k (by omega)
      rw [sum_range_succ (fun i => ρ i / X i), sum_range_succ ρ]
      have e1 : (∑ l ∈ range (k + 1), ρ l + ρ (k + 1) + 2) / X (k + 1) =
          (∑ l ∈ range (k + 1), ρ l + 2) / X (k + 1) + ρ (k + 1) / X (k + 1) := by ring
      have e2 : (∑ l ∈ range (k + 1), ρ l + 2) / X k - (∑ l ∈ range (k + 1), ρ l + 2) / X (k + 1) =
          (∑ l ∈ range (k + 1), ρ l + 2) * (1 / X k - 1 / X (k + 1)) := by ring
      have h3 : ε * (1 / X k - 1 / X (k + 1)) ≤
          (∑ l ∈ range (k + 1), ρ l + 2) * (1 / X k - 1 / X (k + 1)) :=
        mul_le_mul_of_nonneg_right hSk (by linarith)
      rw [e1]
      nlinarith
  have hk := key (m - 1) (by omega)
  rw [show m - 1 + 1 = m by omega] at hk
  have hXm := hpos (m - 1) (by omega)
  have hSm := hS (m - 1) (by omega)
  rw [show m - 1 + 1 = m by omega] at hSm
  have : ε / X (m - 1) ≤ (∑ l ∈ range m, ρ l + 2) / X (m - 1) := div_le_div_of_nonneg_right hSm hXm.le
  have e : ε * (1 / X 0 - 1 / X (m - 1)) = ε / X 0 - ε / X (m - 1) := by ring
  linarith

/-! ### The drift of the nearest right gap -/

section Drift

variable {nL nR : ℕ}

/-- The far-gap and cross-gap constant `C₀ = n_R R/g + n_L R·4/(3a)`. -/
def cst0 (nL nR : ℕ) (Rw g a : ℝ) : ℝ := nR * (Rw / g) + nL * (Rw / (3 * a / 4))

/-- The bound on the drift of `X₁` while `X₁ ∈ [r, 2r]`. -/
def cstV (nL nR : ℕ) (Rw a r : ℝ) : ℝ := 2 / r + nR * (Rw / r) + nL * (Rw / (3 * a / 4))

theorem cst0_nonneg {Rw g a : ℝ} (hR : 0 ≤ Rw) (hg : 0 < g) (ha : 0 < a) : 0 ≤ cst0 nL nR Rw g a := by
  unfold cst0; positivity

theorem cstV_nonneg {Rw a r : ℝ} (hR : 0 ≤ Rw) (ha : 0 < a) (hr : 0 < r) : 0 ≤ cstV nL nR Rw a r := by
  unfold cstV; positivity

/-- `|Σ ρ_i/Y_i| ≤ n R/c` when `|ρ_i| ≤ R` and `Y_i ≥ c > 0`. -/
theorem abs_sum_div_le {n : ℕ} {ρ Y : Fin n → ℝ} {Rw c : ℝ} (hR : 0 ≤ Rw) (hc : 0 < c)
    (hρ : ∀ i, |ρ i| ≤ Rw) (hY : ∀ i, c ≤ Y i) : |∑ i, ρ i / Y i| ≤ n * (Rw / c) := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ i ∈ (univ : Finset (Fin n)), |ρ i / Y i| ≤ Rw / c := fun i _ => by
    have hY0 : 0 < Y i := hc.trans_le (hY i)
    rw [abs_div, abs_of_pos hY0]
    calc |ρ i| / Y i ≤ Rw / Y i := div_le_div_of_nonneg_right (hρ i) hY0.le
      _ ≤ Rw / c := div_le_div_of_nonneg_left hR hc (hY i)
  calc ∑ i, |ρ i / Y i| ≤ ∑ _i : Fin n, Rw / c := sum_le_sum hterm
    _ = n * (Rw / c) := by simp [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The far right labels contribute at most `n_R R/g`. -/
theorem abs_sum_Ico_le {ρR X : Fin nR → ℝ} {Rw g : ℝ} (hR : 0 ≤ Rw) (hg : 0 < g)
    (hρ : ∀ j, |ρR j| ≤ Rw) {mR : ℕ} (hfar : ∀ j : Fin nR, mR ≤ (j : ℕ) → g ≤ X j) :
    |∑ i ∈ Finset.Ico mR nR, Supp8.GB5.rhoN ρR i / Supp8.GB5.gapN X i| ≤ nR * (Rw / g) := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ i ∈ Finset.Ico mR nR, |Supp8.GB5.rhoN ρR i / Supp8.GB5.gapN X i| ≤ Rw / g := fun i hi => by
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hi
    have hX := hfar ⟨i, h2⟩ h1
    have hX0 : 0 < X ⟨i, h2⟩ := hg.trans_le hX
    simp only [Supp8.GB5.rhoN, Supp8.GB5.gapN, h2, ↓reduceDIte]
    rw [abs_div, abs_of_pos hX0]
    calc |ρR ⟨i, h2⟩| / X ⟨i, h2⟩ ≤ Rw / X ⟨i, h2⟩ := div_le_div_of_nonneg_right (hρ _) hX0.le
      _ ≤ Rw / g := div_le_div_of_nonneg_left hR hg hX
  calc ∑ i ∈ Finset.Ico mR nR, |Supp8.GB5.rhoN ρR i / Supp8.GB5.gapN X i|
      ≤ ∑ _i ∈ Finset.Ico mR nR, Rw / g := sum_le_sum hterm
    _ = ((nR - mR : ℕ) : ℝ) * (Rw / g) := by simp [sum_const, Nat.card_Ico, nsmul_eq_mul]
    _ ≤ nR * (Rw / g) := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le nR mR) (by positivity)

/-- **The drift of `X₁` near zero** (DS1.4 and the bounded far and opposite contributions): if `0 < X₀ < g`, the
gaps are nondecreasing, the far labels `j ≥ m_R` have gaps at least `g`, the inner partial sums have `S_j + 2 ≥ ε`,
and every left gap is at least `3a/4`, then `2/X₀ + Σ_R ρ_j/X_j − Σ_L ρ_i/Y_i ≥ ε/X₀ − C₀`. -/
theorem drift_ge {X : Fin nR → ℝ} {Y : Fin nL → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hnR : 0 < nR) {mR : ℕ} (hmR : mR ≤ nR) {ε Rw g a : ℝ} (hR : 0 ≤ Rw) (hg : 0 < g) (ha : 0 < a)
    (hρL : ∀ i, |ρL i| ≤ Rw) (hρR : ∀ j, |ρR j| ≤ Rw)
    (hX0 : 0 < X ⟨0, hnR⟩) (hXm : Monotone X) (hfar : ∀ j : Fin nR, mR ≤ (j : ℕ) → g ≤ X j)
    (hin : ∀ j : Fin nR, (j : ℕ) < mR → ε ≤ ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l + 2)
    (hY : ∀ i, 3 * a / 4 ≤ Y i) (hXg : X ⟨0, hnR⟩ < g) :
    ε / X ⟨0, hnR⟩ - cst0 nL nR Rw g a ≤ 2 / X ⟨0, hnR⟩ + ∑ j, ρR j / X j - ∑ i, ρL i / Y i := by
  have hm0 : 0 < mR := by
    by_contra h
    have := hfar ⟨0, hnR⟩ (by omega)
    linarith
  have hg0 : Supp8.GB5.gapN X 0 = X ⟨0, hnR⟩ := by simp [Supp8.GB5.gapN, hnR]
  have hsplit : ∑ j, ρR j / X j = ∑ i ∈ range mR, Supp8.GB5.rhoN ρR i / Supp8.GB5.gapN X i +
      ∑ i ∈ Finset.Ico mR nR, Supp8.GB5.rhoN ρR i / Supp8.GB5.gapN X i := by
    rw [Supp8.GB5.sum_div_eq_sum_range, sum_range_add_sum_Ico _ hmR]
  have habel := abel_inner (ρ := Supp8.GB5.rhoN ρR) (X := Supp8.GB5.gapN X) (ε := ε) hm0 (by rw [hg0]; exact hX0)
    (fun i hi => by
      have h1 : i < nR := by omega
      have h2 : i + 1 < nR := by omega
      simp only [Supp8.GB5.gapN, h1, h2, ↓reduceDIte]
      exact hXm (Fin.mk_le_mk.2 (Nat.le_succ i)))
    (fun i hi => by
      have h1 : i < nR := by omega
      rw [← Supp8.GB5.partialSum_eq ρR ⟨i, h1⟩]
      exact hin ⟨i, h1⟩ hi)
  rw [hg0] at habel
  have hfarB := abs_sum_Ico_le hR hg hρR hfar
  have hleft := abs_sum_div_le hR (by positivity : (0 : ℝ) < 3 * a / 4) hρL hY
  have h1 := neg_abs_le (∑ i ∈ Finset.Ico mR nR, Supp8.GB5.rhoN ρR i / Supp8.GB5.gapN X i)
  have h2 := le_abs_self (∑ i, ρL i / Y i)
  rw [hsplit]
  unfold cst0
  linarith

/-- **The drift of `X₁` on `[r, 2r]` is bounded.** -/
theorem abs_drift_le {X : Fin nR → ℝ} {Y : Fin nL → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hnR : 0 < nR) {Rw a r : ℝ} (hR : 0 ≤ Rw) (ha : 0 < a) (hr : 0 < r)
    (hρL : ∀ i, |ρL i| ≤ Rw) (hρR : ∀ j, |ρR j| ≤ Rw) (hXr : r ≤ X ⟨0, hnR⟩) (hXm : Monotone X)
    (hY : ∀ i, 3 * a / 4 ≤ Y i) :
    |2 / X ⟨0, hnR⟩ + ∑ j, ρR j / X j - ∑ i, ρL i / Y i| ≤ cstV nL nR Rw a r := by
  have hX : ∀ j, r ≤ X j := fun j => hXr.trans (hXm (Fin.mk_le_mk.2 (Nat.zero_le _)))
  have hright := abs_sum_div_le hR hr hρR hX
  have hleft := abs_sum_div_le hR (by positivity : (0 : ℝ) < 3 * a / 4) hρL hY
  have h2 : |2 / X ⟨0, hnR⟩| ≤ 2 / r := by
    rw [abs_div, abs_two, abs_of_pos (hr.trans_le hXr)]
    exact div_le_div_of_nonneg_left (by norm_num) hr hXr
  unfold cstV
  calc |2 / X ⟨0, hnR⟩ + ∑ j, ρR j / X j - ∑ i, ρL i / Y i|
      ≤ |2 / X ⟨0, hnR⟩ + ∑ j, ρR j / X j| + |∑ i, ρL i / Y i| := abs_sub _ _
    _ ≤ |2 / X ⟨0, hnR⟩| + |∑ j, ρR j / X j| + |∑ i, ρL i / Y i| := by
        gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

/-- The first component of the density of GB5's coordinates with `j = i₀ = 0` is the drift of `X₁`. -/
theorem densAt_fst_eq (hnR : 0 < nR) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ)
    (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (s : ℝ) :
    (Supp8.GB5.densAt ρL ρR ⟨0, hnR⟩ ⟨0, hnR⟩ w vL vR s).1 =
      2 / (vR ⟨0, hnR⟩ s.toNNReal - w s.toNNReal) + ∑ j, ρR j / (vR j s.toNNReal - w s.toNNReal) -
        ∑ i, ρL i / (w s.toNNReal - vL i s.toNNReal) := by
  simp only [Supp8.GB5.densAt, Ito.driftAt]
  have : ∑ j, ρR j / (w s.toNNReal - vR j s.toNNReal) = -∑ j, ρR j / (vR j s.toNNReal - w s.toNNReal) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [← neg_sub, div_neg]
  rw [this]; ring

end Drift

end DS1

end Supp12

end InteractingSLE
