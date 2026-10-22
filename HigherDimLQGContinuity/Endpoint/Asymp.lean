import HigherDimLQGContinuity.Endpoint.Grid

/-!
# The Euclidean endpoint (packet E3), part 3: the elementary asymptotics of the grids

Blueprint Part C `c:lem-end-bridge` and `c:lem-end-fine` (the arithmetic parts: (G), the depth condition, the drift and
the failure sums), for the explicit grids of `Endpoint/Grid.lean`. Every bound is reduced to two elementary facts,
`K ≤ 2^n` eventually and `K u² ≤ 2^u` eventually, through the crude comparisons
`δ^{-M} ≤ 2^{n⌈M⌉}` and `δ^M ≥ 2^{-n⌈M⌉}` for `2^{-n} ≤ δ ≤ 1` (`endpt_rpow_neg_le`, `endpt_pow_le_rpow`).

For fine level `j` of block `k` put `N = k + j` and `u = 2^{DN}` (`D = endDexp B M`); then
* (G): `a_k 2^{-u} ≤ exp(-C a_k^{-B} δ^{-B})` (`endpt_fine_G`);
* depth: `C δ^{-M} log(C/δ) ≤ c δ / (a_k 2^{-u})` (`endpt_fine_depth`);
* failure: `(2^{2^D u} + 1) C δ^{-M} exp(-c δ^M n) ≤ 2^{-(N+1)}` with `n = c δ / (a_k 2^{-u})` (`endpt_fine_fail`),
for `N` large, uniformly in `(k, j)`. For the bridge of block `k` (`δ = ε_k / 8`, base spacing `a_k 2^{-Lk}`,
`L = endLexp B M`): depth (`endpt_bridge_depth`) and failure over the `2^{2^{Dk}} + 1` level-`0` nodes
(`endpt_bridge_fail`), for `k` large.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

/-! ## Elementary facts -/

theorem endpt_two_pow_eq_exp (u : ℕ) : (2 : ℝ) ^ u = Real.exp (u * Real.log 2) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]

theorem endpt_half_pow_eq_exp (u : ℕ) : (1 / 2 : ℝ) ^ u = Real.exp (-(u * Real.log 2)) := by
  rw [Real.exp_neg, ← endpt_two_pow_eq_exp, one_div, inv_pow]

/-- Crude upper bound: `x^{-M} ≤ 2^{n⌈M⌉}` for `2^{-n} ≤ x ≤ 1`. -/
theorem endpt_rpow_neg_le {x M : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) {n : ℕ}
    (hn : (1 / 2 : ℝ) ^ n ≤ x) : x ^ (-M) ≤ (2 : ℝ) ^ (n * ⌈M⌉₊) := by
  have h1 : x ^ (-M) ≤ x ^ (-(⌈M⌉₊ : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (neg_le_neg (Nat.le_ceil M))
  have h2 : x ^ (-(⌈M⌉₊ : ℝ)) = (x⁻¹) ^ ⌈M⌉₊ := by
    rw [Real.rpow_neg hx0.le, Real.rpow_natCast, inv_pow]
  have h3 : x⁻¹ ≤ 2 ^ n := by
    rw [inv_le_comm₀ hx0 (by positivity)]
    calc ((2 : ℝ) ^ n)⁻¹ = (1 / 2) ^ n := by rw [one_div, inv_pow]
      _ ≤ x := hn
  calc x ^ (-M) ≤ (x⁻¹) ^ ⌈M⌉₊ := h1.trans h2.le
    _ ≤ (2 ^ n) ^ ⌈M⌉₊ := pow_le_pow_left₀ (inv_nonneg.2 hx0.le) h3 _
    _ = 2 ^ (n * ⌈M⌉₊) := by rw [← pow_mul]

/-- Crude lower bound: `x^M ≥ 2^{-n⌈M⌉}` for `2^{-n} ≤ x ≤ 1`, `M ≥ 0`. -/
theorem endpt_pow_le_rpow {x M : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) {n : ℕ}
    (hn : (1 / 2 : ℝ) ^ n ≤ x) : (1 / 2 : ℝ) ^ (n * ⌈M⌉₊) ≤ x ^ M := by
  have h1 : x ^ (⌈M⌉₊ : ℝ) ≤ x ^ M := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (Nat.le_ceil M)
  rw [Real.rpow_natCast] at h1
  calc (1 / 2 : ℝ) ^ (n * ⌈M⌉₊) = ((1 / 2) ^ n) ^ ⌈M⌉₊ := by rw [pow_mul]
    _ ≤ x ^ ⌈M⌉₊ := pow_le_pow_left₀ (by positivity) hn _
    _ ≤ x ^ M := h1

/-- `log(C/x) ≤ C 2^n` for `2^{-n} ≤ x`, `C ≥ 1`. -/
theorem endpt_log_div_le {x C : ℝ} (hx0 : 0 < x) (hC : 1 ≤ C) {n : ℕ} (hn : (1 / 2 : ℝ) ^ n ≤ x) :
    Real.log (C / x) ≤ C * 2 ^ n := by
  have h1 : Real.log (C / x) ≤ C / x := Real.log_le_self (by positivity)
  have h2 : x⁻¹ ≤ 2 ^ n := by
    rw [inv_le_comm₀ hx0 (by positivity)]
    calc ((2 : ℝ) ^ n)⁻¹ = (1 / 2) ^ n := by rw [one_div, inv_pow]
      _ ≤ x := hn
  calc Real.log (C / x) ≤ C / x := h1
    _ = C * x⁻¹ := div_eq_mul_inv _ _
    _ ≤ C * 2 ^ n := by gcongr

theorem endpt_eventually_le_two_pow (K : ℝ) : ∀ᶠ n : ℕ in atTop, K ≤ (2 : ℝ) ^ n :=
  (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop K

theorem endpt_eventually_mul_sq_le_two_pow (K : ℝ) :
    ∀ᶠ u : ℕ in atTop, K * (u : ℝ) ^ 2 ≤ (2 : ℝ) ^ u := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1 : ℝ) < 2)
  have hK : (0 : ℝ) < 1 / (|K| + 1) := by positivity
  filter_upwards [h.eventually (gt_mem_nhds hK)] with u hu
  have h2 : (0 : ℝ) < 2 ^ u := by positivity
  rw [div_lt_iff₀ h2] at hu
  have hu2 : (0 : ℝ) ≤ (u : ℝ) ^ 2 := sq_nonneg _
  have hK1 : 0 < |K| + 1 := by positivity
  calc K * (u : ℝ) ^ 2 ≤ (|K| + 1) * (u : ℝ) ^ 2 := by
        gcongr
        linarith [le_abs_self K]
    _ ≤ (|K| + 1) * (1 / (|K| + 1) * 2 ^ u) := by gcongr
    _ = 2 ^ u := by field_simp

/-- `C · 2^E · exp(-Y) ≤ 2^{-b}` when `log C + E log 2 ≤ Y` and `E = a + b`, as `2^a 2^{-(a+b)} = 2^{-b}`. -/
theorem endpt_mul_exp_le {C Y : ℝ} (hC : 0 < C) {a b : ℕ}
    (h : Real.log C + ((a + b : ℕ) : ℝ) * Real.log 2 ≤ Y) :
    (2 : ℝ) ^ a * C * Real.exp (-Y) ≤ (1 / 2) ^ b := by
  have h1 : Real.exp (-Y) ≤ Real.exp (-(Real.log C + ((a + b : ℕ) : ℝ) * Real.log 2)) :=
    Real.exp_le_exp.2 (neg_le_neg h)
  have h2 : Real.exp (-(Real.log C + ((a + b : ℕ) : ℝ) * Real.log 2)) = C⁻¹ * (1 / 2) ^ (a + b) := by
    rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_log hC, endpt_half_pow_eq_exp]
  calc (2 : ℝ) ^ a * C * Real.exp (-Y) ≤ (2 : ℝ) ^ a * C * (C⁻¹ * (1 / 2) ^ (a + b)) := by
        rw [← h2]
        gcongr
    _ = (2 : ℝ) ^ a * (1 / 2) ^ a * (1 / 2) ^ b * (C * C⁻¹) := by rw [pow_add]; ring
    _ = (1 / 2) ^ b := by
        rw [mul_inv_cancel₀ hC.ne', ← mul_pow]
        norm_num

/-! ## Fine levels -/

/-- **(G) for fine level `j` of block `k`**, for `k + j` large. -/
theorem endpt_fine_G {B M C : ℝ} (hC : 0 < C) :
    ∃ N₀ : ℕ, ∀ k j : ℕ, N₀ ≤ k + j →
      endA (k + endLevel (endDexp B M) k j) ≤
        Real.exp (-(C * endA k ^ (-B) * endDelta k j ^ (-B))) := by
  set B' := ⌈B⌉₊
  set D := endDexp B M
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨N₀, hN₀⟩ :=
    (endpt_eventually_le_two_pow (C * 2 ^ (6 * B') / Real.log 2)).exists_forall_of_atTop
  refine ⟨N₀, fun k j hkj => ?_⟩
  set N := k + j with hNdef
  set u := endLevel D k j with hudef
  have hx0 : 0 < endA k * endDelta k j := mul_pos (endA_pos k) (endDelta_pos k j)
  have hx1 : endA k * endDelta k j ≤ 1 :=
    calc endA k * endDelta k j ≤ 1 * 1 :=
          mul_le_mul (endA_le_one k) ((endDelta_lt_eighth k j).le.trans (by norm_num))
            (endDelta_pos k j).le zero_le_one
      _ = 1 := one_mul 1
  have hxn : (1 / 2 : ℝ) ^ (2 * N + 6) ≤ endA k * endDelta k j := by
    calc (1 / 2 : ℝ) ^ (2 * N + 6) ≤ (1 / 2) ^ (k + (k + j + 6)) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = endA k * (1 / 2) ^ (k + j + 6) := by rw [pow_add]; rfl
      _ ≤ endA k * endDelta k j := by
          gcongr
          · exact (endA_pos k).le
          · exact le_endDelta k j
  have hrw : endA k ^ (-B) * endDelta k j ^ (-B) = (endA k * endDelta k j) ^ (-B) :=
    (Real.mul_rpow (endA_pos k).le (endDelta_pos k j).le).symm
  have hcrude : (endA k * endDelta k j) ^ (-B) ≤ (2 : ℝ) ^ ((2 * N + 6) * B') :=
    endpt_rpow_neg_le hx0 hx1 hxn
  have hN := hN₀ N hkj
  have hD : 2 * B' + 1 ≤ D := by
    simp only [D, endDexp, B']
    omega
  have hu : (2 : ℝ) ^ (N + 2 * B' * N) ≤ u := by
    have : N + 2 * B' * N ≤ D * N := by nlinarith
    calc (2 : ℝ) ^ (N + 2 * B' * N) ≤ 2 ^ (D * N) := pow_le_pow_right₀ (by norm_num) this
      _ = u := by simp only [hudef, endLevel, hNdef]; push_cast; ring_nf
  have hkey : C * (2 : ℝ) ^ ((2 * N + 6) * B') ≤ u * Real.log 2 := by
    have e : (2 : ℝ) ^ ((2 * N + 6) * B') = 2 ^ (6 * B') * 2 ^ (2 * B' * N) := by
      rw [← pow_add]
      congr 1
      ring
    rw [e]
    calc C * (2 ^ (6 * B') * 2 ^ (2 * B' * N))
        = (C * 2 ^ (6 * B') / Real.log 2) * 2 ^ (2 * B' * N) * Real.log 2 := by
          field_simp
      _ ≤ 2 ^ N * 2 ^ (2 * B' * N) * Real.log 2 := by gcongr
      _ = 2 ^ (N + 2 * B' * N) * Real.log 2 := by rw [← pow_add]
      _ ≤ u * Real.log 2 := by gcongr
  calc endA (k + u) ≤ endA u := endA_anti (by omega)
    _ = Real.exp (-(u * Real.log 2)) := endpt_half_pow_eq_exp u
    _ ≤ Real.exp (-(C * endA k ^ (-B) * endDelta k j ^ (-B))) := by
        rw [Real.exp_le_exp, neg_le_neg_iff, mul_assoc, hrw]
        calc C * (endA k * endDelta k j) ^ (-B) ≤ C * 2 ^ ((2 * N + 6) * B') := by gcongr
          _ ≤ u * Real.log 2 := hkey

/-- `c δ / (a_k 2^{-u}) ≥ c 2^{-(N+6)} 2^u` for fine level `j` of block `k`. -/
theorem endpt_fine_n_ge {c : ℝ} (hc : 0 < c) (D k j : ℕ) :
    c * (1 / 2) ^ (k + j + 6) * 2 ^ endLevel D k j ≤ c * endDelta k j / endA (k + endLevel D k j) := by
  set u := endLevel D k j
  have hA : 0 < endA (k + u) := endA_pos _
  rw [le_div_iff₀ hA]
  have h2 : (2 : ℝ) ^ u * endA (k + u) ≤ 1 := by
    rw [endA_add, show (2 : ℝ) ^ u * (endA k * endA u) = endA k * (endA u * 2 ^ u) by ring,
      endA_mul_two_pow, mul_one]
    exact endA_le_one k
  calc c * (1 / 2) ^ (k + j + 6) * 2 ^ u * endA (k + u)
      = c * (1 / 2) ^ (k + j + 6) * (2 ^ u * endA (k + u)) := by ring
    _ ≤ c * (1 / 2) ^ (k + j + 6) * 1 := by gcongr
    _ ≤ c * endDelta k j := by rw [mul_one]; gcongr; exact le_endDelta k j

/-- **The depth condition for fine level `j` of block `k`**, for `k + j` large. -/
theorem endpt_fine_depth {B M C c : ℝ} (hC : 1 ≤ C) (hc : 0 < c) :
    ∃ N₀ : ℕ, ∀ k j : ℕ, N₀ ≤ k + j →
      C * endDelta k j ^ (-M) * Real.log (C / endDelta k j) ≤
        c * endDelta k j / endA (k + endLevel (endDexp B M) k j) := by
  set M' := ⌈M⌉₊
  set D := endDexp B M
  have hC0 : 0 < C := by linarith
  obtain ⟨U₀, hU₀⟩ :=
    (endpt_eventually_mul_sq_le_two_pow (C ^ 2 * 2 ^ (6 * (M' + 2)) / c)).exists_forall_of_atTop
  refine ⟨U₀, fun k j hkj => ?_⟩
  set N := k + j with hNdef
  set u := endLevel D k j with hudef
  set δ := endDelta k j
  have hδ0 : 0 < δ := endDelta_pos k j
  have hδ1 : δ ≤ 1 := (endDelta_lt_eighth k j).le.trans (by norm_num)
  have hδn : (1 / 2 : ℝ) ^ (N + 6) ≤ δ := le_endDelta k j
  have hNu : N ≤ u := le_endLevel (one_le_endDexp B M) k j
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast one_le_endLevel D k j
  have hneg : δ ^ (-M) ≤ 2 ^ ((N + 6) * M') := endpt_rpow_neg_le hδ0 hδ1 hδn
  have hlog : Real.log (C / δ) ≤ C * 2 ^ (N + 6) := endpt_log_div_le hδ0 hC hδn
  have hlog0 : 0 ≤ Real.log (C / δ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have hn := endpt_fine_n_ge hc D k j
  -- `2^{(M'+2)N} ≤ u`
  have hMu : (2 : ℝ) ^ ((M' + 2) * N) ≤ u := by
    have hD : M' + 2 ≤ D := by simp only [D, endDexp, M']; omega
    calc (2 : ℝ) ^ ((M' + 2) * N) ≤ 2 ^ (D * N) :=
          pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right _ hD)
      _ = u := by simp only [hudef, endLevel, hNdef]; push_cast; ring_nf
  have hasymp := hU₀ u (le_trans hkj hNu)
  have huu : (u : ℝ) ≤ (u : ℝ) ^ 2 := by nlinarith
  -- `C² 2^{6(M'+2)} u ≤ c 2^u`
  have hkey : C ^ 2 * 2 ^ (6 * (M' + 2)) * (u : ℝ) ≤ c * 2 ^ u := by
    have := hasymp
    rw [div_mul_eq_mul_div, div_le_iff₀ hc] at this
    calc C ^ 2 * 2 ^ (6 * (M' + 2)) * (u : ℝ) ≤ C ^ 2 * 2 ^ (6 * (M' + 2)) * (u : ℝ) ^ 2 := by
          gcongr
      _ ≤ 2 ^ u * c := this
      _ = c * 2 ^ u := mul_comm _ _
  calc C * δ ^ (-M) * Real.log (C / δ) ≤ C * 2 ^ ((N + 6) * M') * (C * 2 ^ (N + 6)) := by
        gcongr
    _ = C ^ 2 * 2 ^ (6 * (M' + 2)) * 2 ^ ((M' + 2) * N) * (1 / 2) ^ (N + 6) := by
        have e : (2 : ℝ) ^ ((N + 6) * M') * 2 ^ (N + 6) * 2 ^ (N + 6) =
            2 ^ (6 * (M' + 2)) * 2 ^ ((M' + 2) * N) := by
          rw [← pow_add, ← pow_add, ← pow_add]
          congr 1
          ring
        have e2 : (2 : ℝ) ^ (N + 6) * (1 / 2) ^ (N + 6) = 1 := by
          rw [← mul_pow]; norm_num
        calc C * 2 ^ ((N + 6) * M') * (C * 2 ^ (N + 6))
            = C ^ 2 * (2 ^ ((N + 6) * M') * 2 ^ (N + 6) * 2 ^ (N + 6)) * (1 / 2) ^ (N + 6) := by
              rw [show C ^ 2 * (2 ^ ((N + 6) * M') * 2 ^ (N + 6) * 2 ^ (N + 6)) * (1 / 2) ^ (N + 6)
                  = C ^ 2 * (2 ^ ((N + 6) * M') * 2 ^ (N + 6)) * ((2 : ℝ) ^ (N + 6) * (1 / 2) ^ (N + 6))
                  by ring, e2]
              ring
          _ = _ := by rw [e]; ring
    _ ≤ C ^ 2 * 2 ^ (6 * (M' + 2)) * u * (1 / 2) ^ (N + 6) := by gcongr
    _ ≤ c * 2 ^ u * (1 / 2) ^ (N + 6) := by gcongr
    _ = c * (1 / 2) ^ (k + j + 6) * 2 ^ u := by ring
    _ ≤ c * δ / endA (k + u) := hn

/-- **The failure bound for fine level `j` of block `k`**: the `2^{2^D u} + 1` comparisons of level `j` fail with
total probability at most `2^{-(k+j+1)}`, for `k + j` large. -/
theorem endpt_fine_fail {B M C c : ℝ} (hC : 1 ≤ C) (hc : 0 < c) :
    ∃ N₀ : ℕ, ∀ k j : ℕ, N₀ ≤ k + j →
      ((2 : ℝ) ^ endLevel (endDexp B M) k (j + 1) + 1) *
        (C * endDelta k j ^ (-M) * Real.exp (-(c * endDelta k j ^ M *
          (c * endDelta k j / endA (k + endLevel (endDexp B M) k j))))) ≤ (1 / 2) ^ (k + j + 1) := by
  set M' := ⌈M⌉₊
  set D := endDexp B M
  have hC0 : 0 < C := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  set K₂ : ℝ := Real.log C + (2 ^ D + 3 + 7 * M') * Real.log 2 with hK₂
  set γ : ℝ := c ^ 2 * (1 / 2) ^ (6 * (M' + 1)) with hγdef
  have hγ : 0 < γ := by positivity
  have hK₂0 : 0 ≤ K₂ := by positivity
  obtain ⟨U₀, hU₀⟩ := (endpt_eventually_mul_sq_le_two_pow (K₂ / γ)).exists_forall_of_atTop
  refine ⟨U₀, fun k j hkj => ?_⟩
  set N := k + j with hNdef
  set u := endLevel D k j with hudef
  set δ := endDelta k j with hδdef
  have hδ0 : 0 < δ := endDelta_pos k j
  have hδ1 : δ ≤ 1 := (endDelta_lt_eighth k j).le.trans (by norm_num)
  have hδn : (1 / 2 : ℝ) ^ (N + 6) ≤ δ := le_endDelta k j
  have hNu : N ≤ u := le_endLevel (one_le_endDexp B M) k j
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast one_le_endLevel D k j
  have hu0 : (0 : ℝ) < u := by linarith
  have hNu' : (N : ℝ) ≤ u := by exact_mod_cast hNu
  have hneg : δ ^ (-M) ≤ 2 ^ ((N + 6) * M') := endpt_rpow_neg_le hδ0 hδ1 hδn
  have hpos : (1 / 2 : ℝ) ^ ((N + 6) * M') ≤ δ ^ M := endpt_pow_le_rpow hδ0 hδ1 hδn
  have hn := endpt_fine_n_ge hc D k j
  -- `2^{(M'+1)N} ≤ u`
  have hMu : (2 : ℝ) ^ ((M' + 1) * N) ≤ u := by
    have hD : M' + 1 ≤ D := by simp only [D, endDexp, M']; omega
    calc (2 : ℝ) ^ ((M' + 1) * N) ≤ 2 ^ (D * N) :=
          pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right _ hD)
      _ = u := by simp only [hudef, endLevel, hNdef]; push_cast; ring_nf
  -- the exponent `Y ≥ γ 2^u / u`
  set X := c * δ ^ M * (c * δ / endA (k + u)) with hXdef
  have hX : γ * 2 ^ u / u ≤ X := by
    have h1 : c * (1 / 2) ^ ((N + 6) * M') * (c * (1 / 2) ^ (k + j + 6) * 2 ^ u) ≤ X := by
      rw [hXdef]
      gcongr
    have h2 : γ * 2 ^ u / u ≤ c * (1 / 2) ^ ((N + 6) * M') * (c * (1 / 2) ^ (k + j + 6) * 2 ^ u) := by
      rw [div_le_iff₀ hu0]
      have e : c * (1 / 2 : ℝ) ^ ((N + 6) * M') * (c * (1 / 2) ^ (k + j + 6) * 2 ^ u) * u =
          γ * 2 ^ u * ((1 / 2) ^ ((M' + 1) * N) * u) := by
        rw [hγdef]
        have : (1 / 2 : ℝ) ^ ((N + 6) * M') * (1 / 2) ^ (k + j + 6) =
            (1 / 2) ^ (6 * (M' + 1)) * (1 / 2) ^ ((M' + 1) * N) := by
          rw [← pow_add, ← pow_add, hNdef]
          congr 1
          ring
        calc c * (1 / 2 : ℝ) ^ ((N + 6) * M') * (c * (1 / 2) ^ (k + j + 6) * 2 ^ u) * u
            = c ^ 2 * ((1 / 2) ^ ((N + 6) * M') * (1 / 2) ^ (k + j + 6)) * 2 ^ u * u := by ring
          _ = _ := by rw [this]; ring
      rw [e]
      have h3 : 1 ≤ (1 / 2 : ℝ) ^ ((M' + 1) * N) * u := by
        have h4 : (1 / 2 : ℝ) ^ ((M' + 1) * N) * 2 ^ ((M' + 1) * N) = 1 := by
          rw [← mul_pow]; norm_num
        calc (1 : ℝ) = (1 / 2) ^ ((M' + 1) * N) * 2 ^ ((M' + 1) * N) := h4.symm
          _ ≤ (1 / 2) ^ ((M' + 1) * N) * u := by gcongr
      have h5 : 0 ≤ γ * 2 ^ u := by positivity
      nlinarith
    exact h2.trans h1
  -- the asymptotic step: `K₂ u ≤ γ 2^u / u`
  have hasymp : K₂ * u ≤ γ * 2 ^ u / u := by
    have := hU₀ u (le_trans hkj hNu)
    rw [le_div_iff₀ hu0]
    rw [div_mul_eq_mul_div, div_le_iff₀ hγ] at this
    nlinarith
  -- the exponent of the prefactor
  set a : ℕ := 2 ^ D * u + 1 + (N + 6) * M' with hadef
  have hE : Real.log C + ((a + (N + 1) : ℕ) : ℝ) * Real.log 2 ≤ K₂ * u := by
    have hcast : ((a + (N + 1) : ℕ) : ℝ) = 2 ^ D * (u : ℝ) + 1 + ((N : ℝ) + 6) * M' + ((N : ℝ) + 1) := by
      rw [hadef]
      push_cast
      ring
    rw [hcast, hK₂]
    have hM'0 : (0 : ℝ) ≤ M' := Nat.cast_nonneg _
    have h2D : (0 : ℝ) ≤ 2 ^ D := by positivity
    have : 2 ^ D * (u : ℝ) + 1 + ((N : ℝ) + 6) * M' + ((N : ℝ) + 1) ≤ (2 ^ D + 3 + 7 * M') * u := by
      nlinarith
    nlinarith
  -- conclusion
  have hlev : endLevel D k (j + 1) = 2 ^ D * u := endLevel_succ D k j
  have hpre : ((2 : ℝ) ^ endLevel D k (j + 1) + 1) ≤ 2 ^ (2 ^ D * u + 1) := by
    rw [hlev, pow_succ]
    have : (1 : ℝ) ≤ 2 ^ (2 ^ D * u) := one_le_pow₀ (by norm_num)
    linarith
  calc ((2 : ℝ) ^ endLevel D k (j + 1) + 1) * (C * δ ^ (-M) * Real.exp (-X))
      ≤ 2 ^ (2 ^ D * u + 1) * (C * 2 ^ ((N + 6) * M') * Real.exp (-X)) := by gcongr
    _ = (2 : ℝ) ^ a * C * Real.exp (-X) := by rw [hadef, pow_add (2 : ℝ) (2 ^ D * u + 1)]; ring
    _ ≤ (1 / 2) ^ (N + 1) := endpt_mul_exp_le hC0 (hE.trans (hasymp.trans hX))

/-! ## The bridge -/

/-- `c (ε_k/8) / (a_k 2^{-Lk}) ≥ (c/8) 2^{Lk}`. -/
theorem endpt_bridge_n_ge {c : ℝ} (hc : 0 < c) (L k : ℕ) :
    c / 8 * 2 ^ (L * k) ≤ c * (endEps k / 8) / endA (k + L * k) := by
  have hA : 0 < endA (k + L * k) := endA_pos _
  rw [le_div_iff₀ hA, endA_add]
  have h1 : (2 : ℝ) ^ (L * k) * endA (L * k) = 1 := by rw [mul_comm]; exact endA_mul_two_pow _
  calc c / 8 * 2 ^ (L * k) * (endA k * endA (L * k)) = c / 8 * endA k * (2 ^ (L * k) * endA (L * k)) := by
        ring
    _ = c / 8 * endA k := by rw [h1, mul_one]
    _ ≤ c / 8 * endEps k := by gcongr; exact endA_le_endEps k
    _ = c * (endEps k / 8) := by ring

theorem endpt_le_eps_div_eight (k : ℕ) : (1 / 2 : ℝ) ^ (k + 3) ≤ endEps k / 8 := by
  rw [pow_add]
  calc (1 / 2 : ℝ) ^ k * (1 / 2) ^ 3 = endA k / 8 := by unfold endA; ring
    _ ≤ endEps k / 8 := by gcongr; exact endA_le_endEps k

theorem endpt_eps_div_eight_le_one (k : ℕ) : endEps k / 8 ≤ 1 := by
  have := endEps_le_one k
  linarith

/-- **The depth condition of the bridge of block `k`**, for `k` large. -/
theorem endpt_bridge_depth {B M C c : ℝ} (hC : 1 ≤ C) (hc : 0 < c) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, C * (endEps k / 8) ^ (-M) * Real.log (C / (endEps k / 8)) ≤
      c * (endEps k / 8) / endA (k + endLexp B M * k) := by
  set M' := ⌈M⌉₊
  set L := endLexp B M
  have hC0 : 0 < C := by linarith
  obtain ⟨k₀, hk₀⟩ :=
    (endpt_eventually_le_two_pow (8 * C ^ 2 * 2 ^ (3 * (M' + 1)) / c)).exists_forall_of_atTop
  refine ⟨k₀, fun k hk => ?_⟩
  set δ := endEps k / 8
  have hδ0 : 0 < δ := by positivity [endEps_pos k]
  have hδ1 : δ ≤ 1 := endpt_eps_div_eight_le_one k
  have hδn : (1 / 2 : ℝ) ^ (k + 3) ≤ δ := endpt_le_eps_div_eight k
  have hneg : δ ^ (-M) ≤ 2 ^ ((k + 3) * M') := endpt_rpow_neg_le hδ0 hδ1 hδn
  have hlog : Real.log (C / δ) ≤ C * 2 ^ (k + 3) := endpt_log_div_le hδ0 hC hδn
  have hlog0 : 0 ≤ Real.log (C / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; nlinarith)
  have hn := endpt_bridge_n_ge hc L k
  have hL : M' + 2 ≤ L := by simp only [L, endLexp, endDexp, M']; omega
  have hk := hk₀ k hk
  rw [div_le_iff₀ hc] at hk
  have hLk : (2 : ℝ) ^ ((M' + 1) * k + k) ≤ 2 ^ (L * k) :=
    pow_le_pow_right₀ (by norm_num) (by nlinarith)
  calc C * δ ^ (-M) * Real.log (C / δ) ≤ C * 2 ^ ((k + 3) * M') * (C * 2 ^ (k + 3)) := by gcongr
    _ = C ^ 2 * 2 ^ (3 * (M' + 1)) * 2 ^ ((M' + 1) * k) := by
        rw [show C * 2 ^ ((k + 3) * M') * (C * 2 ^ (k + 3)) = C ^ 2 * (2 ^ ((k + 3) * M') * 2 ^ (k + 3))
          by ring, ← pow_add, mul_assoc, ← pow_add]
        congr 2
        ring
    _ ≤ c / 8 * 2 ^ k * 2 ^ ((M' + 1) * k) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
    _ = c / 8 * 2 ^ ((M' + 1) * k + k) := by rw [pow_add]; ring
    _ ≤ c / 8 * 2 ^ (L * k) := by gcongr
    _ ≤ c * δ / endA (k + L * k) := hn

/-- **The failure bound of the bridge of block `k`**: the `2^{2^{Dk}} + 1` bridge comparisons fail with total
probability at most `2^{-k}`, for `k` large. -/
theorem endpt_bridge_fail {B M C c : ℝ} (hC : 1 ≤ C) (hc : 0 < c) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀,
      ((2 : ℝ) ^ endLevel (endDexp B M) k 0 + 1) *
        (C * (endEps k / 8) ^ (-M) * Real.exp (-(c * (endEps k / 8) ^ M *
          (c * (endEps k / 8) / endA (k + endLexp B M * k))))) ≤ (1 / 2) ^ k := by
  set M' := ⌈M⌉₊
  set D := endDexp B M
  set L := endLexp B M
  have hC0 : 0 < C := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  set K₅ : ℝ := Real.log C + (3 + 4 * M') * Real.log 2 with hK₅
  set γ : ℝ := c ^ 2 / 8 * (1 / 2) ^ (3 * M') with hγdef
  have hγ : 0 < γ := by positivity
  obtain ⟨k₀, hk₀⟩ := (endpt_eventually_le_two_pow (K₅ / γ)).exists_forall_of_atTop
  refine ⟨k₀, fun k hk => ?_⟩
  set q := endLevel D k 0 with hqdef
  set δ := endEps k / 8 with hδdef
  have hδ0 : 0 < δ := by positivity [endEps_pos k]
  have hδ1 : δ ≤ 1 := endpt_eps_div_eight_le_one k
  have hδn : (1 / 2 : ℝ) ^ (k + 3) ≤ δ := endpt_le_eps_div_eight k
  have hneg : δ ^ (-M) ≤ 2 ^ ((k + 3) * M') := endpt_rpow_neg_le hδ0 hδ1 hδn
  have hpos : (1 / 2 : ℝ) ^ ((k + 3) * M') ≤ δ ^ M := endpt_pow_le_rpow hδ0 hδ1 hδn
  have hn := endpt_bridge_n_ge hc L k
  have hkq : k ≤ q := by simpa using le_endLevel (one_le_endDexp B M) k 0
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast one_le_endLevel D k 0
  have hkq' : (k : ℝ) ≤ q := by exact_mod_cast hkq
  -- `2^{Lk} ≥ 2^{M'k} · 2^k · q`, as `L = D + M' + 2`
  have hLq : (2 : ℝ) ^ (M' * k) * 2 ^ k * q ≤ 2 ^ (L * k) := by
    have hq : (q : ℝ) = 2 ^ (D * k) := by simp only [hqdef, endLevel]; push_cast; ring_nf
    rw [hq, ← pow_add, ← pow_add]
    apply pow_le_pow_right₀ (by norm_num)
    have : L = D + M' + 2 := rfl
    rw [this]
    nlinarith
  -- the exponent `X ≥ γ 2^k q`
  set X := c * δ ^ M * (c * δ / endA (k + L * k)) with hXdef
  have hX : γ * 2 ^ k * q ≤ X := by
    have h1 : c * (1 / 2) ^ ((k + 3) * M') * (c / 8 * 2 ^ (L * k)) ≤ X := by
      rw [hXdef]
      gcongr
    refine le_trans ?_ h1
    have e : c * (1 / 2 : ℝ) ^ ((k + 3) * M') * (c / 8 * 2 ^ (L * k)) =
        γ * ((1 / 2) ^ (M' * k) * 2 ^ (L * k)) := by
      rw [hγdef, show (k + 3) * M' = 3 * M' + M' * k by ring, pow_add]
      ring
    rw [e]
    have h4 : (1 / 2 : ℝ) ^ (M' * k) * 2 ^ (M' * k) = 1 := by rw [← mul_pow]; norm_num
    have h5 : 2 ^ k * (q : ℝ) ≤ (1 / 2 : ℝ) ^ (M' * k) * 2 ^ (L * k) := by
      calc 2 ^ k * (q : ℝ) = ((1 / 2 : ℝ) ^ (M' * k) * 2 ^ (M' * k)) * (2 ^ k * q) := by
            rw [h4, one_mul]
        _ = (1 / 2 : ℝ) ^ (M' * k) * (2 ^ (M' * k) * 2 ^ k * q) := by ring
        _ ≤ (1 / 2 : ℝ) ^ (M' * k) * 2 ^ (L * k) := by gcongr
    calc γ * 2 ^ k * q = γ * (2 ^ k * q) := by ring
      _ ≤ γ * ((1 / 2) ^ (M' * k) * 2 ^ (L * k)) := by gcongr
  -- the prefactor
  set a : ℕ := q + 1 + (k + 3) * M' with hadef
  have hE : Real.log C + ((a + k : ℕ) : ℝ) * Real.log 2 ≤ K₅ * q := by
    have hcast : ((a + k : ℕ) : ℝ) = (q : ℝ) + 1 + ((k : ℝ) + 3) * M' + k := by
      rw [hadef]
      push_cast
      ring
    rw [hcast, hK₅]
    have hM'0 : (0 : ℝ) ≤ M' := Nat.cast_nonneg _
    have : (q : ℝ) + 1 + ((k : ℝ) + 3) * M' + k ≤ (3 + 4 * M') * q := by nlinarith
    nlinarith
  have hk2 := hk₀ k hk
  have hasymp : K₅ * q ≤ γ * 2 ^ k * q := by
    rw [div_le_iff₀ hγ] at hk2
    have : K₅ ≤ γ * 2 ^ k := by linarith
    have hq0 : (0 : ℝ) ≤ q := by linarith
    nlinarith
  have hpre : ((2 : ℝ) ^ q + 1) ≤ 2 ^ (q + 1) := by
    rw [pow_succ]
    have : (1 : ℝ) ≤ 2 ^ q := one_le_pow₀ (by norm_num)
    linarith
  calc ((2 : ℝ) ^ q + 1) * (C * δ ^ (-M) * Real.exp (-X))
      ≤ 2 ^ (q + 1) * (C * 2 ^ ((k + 3) * M') * Real.exp (-X)) := by gcongr
    _ = (2 : ℝ) ^ a * C * Real.exp (-X) := by rw [hadef, pow_add (2 : ℝ) (q + 1)]; ring
    _ ≤ (1 / 2) ^ k := endpt_mul_exp_le hC0 (hE.trans (hasymp.trans hX))

end HigherDimLQGContinuity
