import HigherDimLQGMetric.DGZ.CompareCover
import HigherDimLQGMetric.DGZ.CompareShell
import HigherDimLQGMetric.DGZ.BadBoxJ
import HigherDimLQGMetric.DGZ.Interfaces

/-!
# DGZ Proposition 5.1, left inequality, for the pair `(0, e₁)` (packet L4c)

Source: [2] Prop 5.1 (TeX l. 1997–2004), the direction used (MA7 D-5.1, gap G14; blueprint Part C
`r2:prop:51`; ruling M23 (iii)): the interface shape `Prop51Shape` of the orchestrator-owned module
`DGZ/Interfaces.lean` (verbatim MA7 Details (c); it keeps [2]'s restriction `k ≤ c n`, which the
proof below does not use).

**Statement** (`prop51Shape : ∀ d κ ξ Q, Prop51Shape d κ ξ Q`). Under `DGZHyp`, for every `ε > 0`
there are `c > 0` and `N` such that for every dyadic realization, `n ≥ N`, `1 ≤ k ≤ c n`:
`P[D_{n+k}(0,e₁;B₂(0)) ≤ c 2^{-(1-ξQ+ε)k} D_n(0,e₁;B₂(0))] ≤ 2^{-cn}`.

**Proof** (D-5.1 / blueprint `r2:prop:51`). Fix `θ = θ₀` (Lemma 5.9), `K` large (L4a2's `K₀`, the
cover's threshold, and the numerical conditions of Prop 5.10 / Lemma 5.11: `cmp_exists_K`), then
`L ≥ L₀(K, ε)`. On `𝒥₁ ∩ 𝒥₂′` and the good event of Lemma 5.14 (`λ' = λ/2`), for every path `P`
from `0` to `e₁` in `B₂(0)`, Prop 5.13 (`prop513`) and the deterministic consequence of Lemma 5.14
(`lfppDistance_le_of_lemma514Good`) give `D_n(0,e₁) ≤ (3/2) C_13 2^{(1-ξQ+ε)k} len(P; h_{n+k})`,
hence `D_n ≤ (3/2) C_13 2^{(1-ξQ+ε)k} D_{n+k}` (`cmp_lfppDistance_le`). With
`c ≤ 1/(3 C_13 + 1)` the event of the shape contradicts `D_n > 0`, so its probability is at most
`P[(𝒥₁ ∩ 𝒥₂′)ᶜ] + P[(Lemma 5.14)ᶜ] ≤ C_J 2^{-n/C_J} + C_14 e^{-n/C_14} ≤ 2^{-cn}` for
`c ≤ 1/(2(C_J + C_14))` and `n ≥ N`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox)

variable {d : ℕ}

/-! ## Choice of `K` -/

/-- `K^{3/2} = K √K`. -/
theorem cmp_rpow_three_halves {x : ℝ} (hx : 0 < x) : x ^ ((3 : ℝ) / 2) = x * √x := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hx, Real.rpow_one,
    Real.sqrt_eq_rpow]

/-- **The numerical conditions on `K`** (DGZ: "`K` large"): above any `K₀`, there is `K` with
`K ≥ 2`, `N₀ ≤ K⁴`, `3 ≤ λK⁴`, `40R ≤ 2^{λK⁴}`, `6ξK + K ≤ K^{3/2}`, `log 2 ≤ λK³/3` and
`8·41^d ≤ e^{K³}`. -/
theorem cmp_exists_K {lam : ℝ} (ξ : ℝ) (hlam : 0 < lam) (R N₀ K₀ d : ℕ) :
    ∃ K : ℕ, K₀ ≤ K ∧ 2 ≤ K ∧ N₀ ≤ K ^ 4 ∧ (3 : ℝ) ≤ lam * (K : ℝ) ^ 4 ∧
      40 * (R : ℝ) ≤ (2 : ℝ) ^ (lam * (K : ℝ) ^ 4) ∧
      6 * ξ * K + K ≤ (K : ℝ) ^ ((3 : ℝ) / 2) ∧
      Real.log 2 ≤ lam * (K : ℝ) ^ 3 / 3 ∧ 8 * (41 : ℝ) ^ d ≤ Real.exp ((K : ℝ) ^ 3) := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  set M : ℝ := max (max (max 2 (N₀ : ℝ)) (max (3 / lam) (40 * R / (lam * Real.log 2))))
    (max (max ((6 * ξ + 1) ^ 2) (3 * Real.log 2 / lam)) (8 * 41 ^ d)) with hMdef
  refine ⟨max K₀ ⌈M⌉₊, le_max_left _ _, ?_⟩
  set K : ℕ := max K₀ ⌈M⌉₊ with hKdef
  have hKM : M ≤ (K : ℝ) := (Nat.le_ceil M).trans (by exact_mod_cast le_max_right _ _)
  have hall := hKM
  simp only [hMdef, max_le_iff] at hall
  obtain ⟨⟨⟨h2, hN⟩, h3, h40⟩, ⟨h6, hl⟩, h8⟩ := hall
  have hK1 : (1 : ℝ) ≤ K := by linarith
  have hKpos : (0 : ℝ) < K := by linarith
  have hK4 : (K : ℝ) ≤ (K : ℝ) ^ 4 := le_self_pow₀ hK1 (by norm_num)
  have hK3' : (K : ℝ) ≤ (K : ℝ) ^ 3 := le_self_pow₀ hK1 (by norm_num)
  refine ⟨by exact_mod_cast h2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : (N₀ : ℝ) ≤ ((K ^ 4 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · rw [div_le_iff₀ hlam] at h3
    nlinarith
  · have hy : 40 * (R : ℝ) ≤ lam * (K : ℝ) ^ 4 * Real.log 2 := by
      rw [div_le_iff₀ (mul_pos hlam hlog)] at h40
      have := mul_le_mul_of_nonneg_right hK4 (mul_pos hlam hlog).le
      nlinarith
    have hexp := Real.add_one_le_exp (Real.log 2 * (lam * (K : ℝ) ^ 4))
    rw [Real.rpow_def_of_pos two_pos]
    nlinarith
  · rw [cmp_rpow_three_halves hKpos]
    have hs : 6 * ξ + 1 ≤ √(K : ℝ) :=
      (le_abs_self _).trans (Real.abs_le_sqrt h6)
    nlinarith
  · rw [div_le_iff₀ hlam] at hl
    nlinarith
  · have := Real.add_one_le_exp ((K : ℝ) ^ 3)
    linarith

/-! ## Exponential bounds -/

/-- `e^{-x} ≤ 2^{-x}` for `x ≥ 0`. -/
theorem cmp_exp_neg_le_two_rpow {x : ℝ} (hx : 0 ≤ x) : Real.exp (-x) ≤ (2 : ℝ) ^ (-x) := by
  rw [Real.rpow_def_of_pos two_pos]
  refine Real.exp_le_exp.2 ?_
  have h1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (two_pos : (0 : ℝ) < 2)
    linarith
  nlinarith

/-- `a 2^{-n/a} + b 2^{-n/b} ≤ (a + b) 2^{-n/(a+b)}`. -/
theorem cmp_add_two_rpow_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    a * (2 : ℝ) ^ (-(n : ℝ) / a) + b * (2 : ℝ) ^ (-(n : ℝ) / b) ≤
      (a + b) * (2 : ℝ) ^ (-(n : ℝ) / (a + b)) := by
  have hmono : ∀ {x y : ℝ}, 0 < x → x ≤ y → (2 : ℝ) ^ (-(n : ℝ) / x) ≤ (2 : ℝ) ^ (-(n : ℝ) / y) :=
    fun hx hxy => Real.rpow_le_rpow_of_exponent_le one_le_two (by
      rw [neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg n) hx hxy)
  have h1 := hmono ha (le_add_of_nonneg_right hb.le)
  have h2 := hmono hb (le_add_of_nonneg_left ha.le)
  nlinarith

/-- `C 2^{-n/C} ≤ 2^{-n/(2C)}` for large `n`. -/
theorem cmp_two_rpow_tail {C : ℝ} (hC : 0 < C) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → C * (2 : ℝ) ^ (-(n : ℝ) / C) ≤ (2 : ℝ) ^ (-(n : ℝ) / (2 * C)) := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨⌈2 * C ^ 2 / Real.log 2⌉₊, fun n hn => ?_⟩
  have hn' : 2 * C ^ 2 / Real.log 2 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have e : (2 : ℝ) ^ (-(n : ℝ) / (2 * C)) = (2 : ℝ) ^ ((n : ℝ) / (2 * C)) *
      (2 : ℝ) ^ (-(n : ℝ) / C) := by
    rw [← Real.rpow_add two_pos]
    congr 1
    field_simp
    ring
  have hbig : C ≤ (2 : ℝ) ^ ((n : ℝ) / (2 * C)) := by
    rw [Real.rpow_def_of_pos two_pos]
    have h1 := Real.add_one_le_exp (Real.log 2 * ((n : ℝ) / (2 * C)))
    have h2 : C ≤ Real.log 2 * ((n : ℝ) / (2 * C)) := by
      rw [div_le_iff₀ hlog] at hn'
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      nlinarith
    linarith
  rw [e]
  exact mul_le_mul_of_nonneg_right hbig (Real.rpow_pos_of_pos two_pos _).le

/-! ## The deterministic comparison -/

/-- **The comparison of D-5.1, deterministic**: on `𝒥₁ ∩ 𝒥₂′` and the good event of Lemma 5.14
(`λ' = λ/2`), in DGZ's parameter regime,
`D_n(0, e₁; B₂(0)) ≤ (3/2) C_13 2^{(1-ξQ+ε)k} D_{n+k}(0, e₁; B₂(0))`. -/
theorem cmp_lfppDistance_le (hd : 2 ≤ d) {ξ Q θ : ℝ} (hξ : 0 < ξ) (hθ : 0 < θ) {R : ℕ}
    (hR : 100 ≤ R) (hα : 0 < dgzAlpha d Q) :
    ∃ N₀ : ℕ, ∀ (ε L u : ℝ) (K n k : ℕ) (H : ℕ → Rd d → ℝ), (∀ q, Continuous (H q)) →
      2 ≤ K → N₀ ≤ K ^ 4 → (3 : ℝ) ≤ dgzLambda d Q * (K : ℝ) ^ 4 →
      40 * (R : ℝ) ≤ (2 : ℝ) ^ (dgzLambda d Q * (K : ℝ) ^ 4) →
      6 * ξ * K + K ≤ (K : ℝ) ^ ((3 : ℝ) / 2) →
      Real.log 2 ≤ dgzLambda d Q * (K : ℝ) ^ 3 / 3 → 8 * (41 : ℝ) ^ d ≤ Real.exp ((K : ℝ) ^ 3) →
      0 < L → ((K ^ 4 : ℕ) : ℝ) ≤ (1 - dgzLambda d Q) * n → 8 / dgzLambda d Q ≤ n →
      4 * (R : ℝ) / dgzLambda d Q ≤ n →
      EventJ1 (dgzParams d ξ Q θ ε L K R n k) H (dgzLevel (dgzLambda d Q) K n) →
      EventJ2' (dgzParams d ξ Q θ ε L K R n k) H (dgzLevel (dgzLambda d Q) K n) →
      Lemma514Good ξ Q u (dgzLambda d Q / 2) (H n) n →
      lfppDistance d ξ (H n) ≤
        3 / 2 * prop513Const d ξ L * (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) *
          lfppDistance d ξ (H (n + k)) := by
  obtain ⟨N₀, h513⟩ := prop513 hd hξ hθ hR
  refine ⟨N₀, fun ε L u K n k H hc hK2 hKN₀ hK3 hK40 hK6 hKlog hK8 hL hnK hn8 hnR hJ1 hJ2 hG =>
    ?_⟩
  have hlam0 : 0 < dgzLambda d Q := dgzLambda_pos hα
  have hlam4 : dgzLambda d Q ≤ 1 / 4 := dgzLambda_le_quarter hα
  set lam : ℝ := dgzLambda d Q with hlamdef
  set p : NiceParams := dgzParams d ξ Q θ ε L K R n k with hpdef
  set m : ℕ := dgzLevel lam K n with hmdef
  have hpa : p.a = dgzSeq lam p.K := rfl
  have hK1 : 1 ≤ K := by omega
  have hmonoa : Monotone p.a := dgzSeq_monotone hlam0.le hK1
  obtain ⟨hm1, ham, -⟩ := dgzLevel_spec hlam0.le hK1 hnK
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- `a_m ≤ n` and `n - a_m ≥ λ n`
  have hamn' : (dgzSeq lam K m : ℝ) ≤ n := ham.trans (by nlinarith)
  have hamn : p.a m ≤ p.n := by
    show dgzSeq lam K m ≤ n
    exact_mod_cast hamn'
  have hgapn : lam * n ≤ ((p.n - p.a m : ℕ) : ℝ) := by
    show lam * n ≤ ((n - dgzSeq lam K m : ℕ) : ℝ)
    rw [Nat.cast_sub (by exact_mod_cast hamn')]
    linarith
  have hlamn8 : 8 ≤ lam * n := by
    rw [div_le_iff₀ hlam0] at hn8
    linarith
  have hlamnR : 4 * (R : ℝ) ≤ lam * n := by
    rw [div_le_iff₀ hlam0] at hnR
    linarith
  -- the cube condition
  have hCube : 4 * R ≤ 2 ^ (p.n - p.a m + 1) := by
    have h1 : 4 * R ≤ p.n - p.a m := by
      have : ((4 * R : ℕ) : ℝ) ≤ ((p.n - p.a m : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have h2 := Nat.lt_two_pow_self (n := p.n - p.a m + 1)
    omega
  -- the gaps `40 R s_j ≤ s_{j+1}`
  have hgap : ∀ j, j < m → 40 * (p.R : ℝ) * p.s j ≤ p.s (j + 1) := by
    intro j hj
    have hj1n : p.a (j + 1) ≤ p.n := (hmonoa (by omega : j + 1 ≤ m)).trans hamn
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · have e := p.s_succ_eq (i := 0) (hmonoa (Nat.zero_le 1)) hj1n
      have ha01 : p.a (0 + 1) - p.a 0 = K ^ 4 := rfl
      rw [ha01] at e
      rw [e]
      refine mul_le_mul_of_nonneg_right ?_ (p.s_pos 0).le
      have hK4nn : (0 : ℝ) ≤ (K : ℝ) ^ 4 := by positivity
      have h1 : (2 : ℝ) ^ (lam * (K : ℝ) ^ 4) ≤ (2 : ℝ) ^ ((K : ℝ) ^ 4) :=
        Real.rpow_le_rpow_of_exponent_le one_le_two (by nlinarith)
      have h2 : (2 : ℝ) ^ ((K : ℝ) ^ 4) = (2 : ℝ) ^ (K ^ 4) := by
        rw [← Real.rpow_natCast 2 (K ^ 4), Nat.cast_pow]
      rw [← h2]
      exact hK40.trans h1
    · have := dgz_rpow_mul_s_le p hlam0.le hK1 hpa hjpos hj1n
      exact (mul_le_mul_of_nonneg_right hK40 (p.s_pos j).le).trans this
  -- `s_m ≤ 1/100` and `10 s_m ≤ 2^{-⌊λn/2⌋}`
  have hsm_le : ∀ t : ℕ, t ≤ p.n - p.a m → p.s m ≤ (2 : ℝ)⁻¹ ^ t := fun t ht =>
    pow_le_pow_of_le_one (by norm_num) (by norm_num) ht
  have hsm : p.s m ≤ 1 / 100 := by
    have h7 : 7 ≤ p.n - p.a m := by
      have : ((7 : ℕ) : ℝ) ≤ ((p.n - p.a m : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    exact (hsm_le 7 h7).trans (by norm_num)
  have hrad : 10 * p.s m ≤ (2 : ℝ)⁻¹ ^ ⌊lam / 2 * n⌋₊ := by
    set r' : ℕ := ⌊lam / 2 * n⌋₊
    have hr' : (r' : ℝ) ≤ lam / 2 * n := Nat.floor_le (by positivity)
    have h4 : r' + 4 ≤ p.n - p.a m := by
      have : ((r' + 4 : ℕ) : ℝ) ≤ ((p.n - p.a m : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    calc 10 * p.s m ≤ 10 * (2 : ℝ)⁻¹ ^ (r' + 4) := by linarith [hsm_le (r' + 4) h4]
      _ = 10 / 16 * (2 : ℝ)⁻¹ ^ r' := by rw [pow_add]; norm_num; ring
      _ ≤ (2 : ℝ)⁻¹ ^ r' := by
        have : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ r' := by positivity
        linarith
  have he₁ : e₁ d ∉ cbox (0 : Rd d) (10 * p.s m) := by
    intro h
    have h0 := h ⟨0, by omega⟩
    rw [PiLp.zero_apply, sub_zero, e₁_ofLp] at h0
    simp only [ite_true, abs_one] at h0
    linarith
  have hcbox : ∀ {c x : Rd d}, x ∈ cbox c (10 * p.s m) → x ∈ cbox c ((2 : ℝ)⁻¹ ^ ⌊lam / 2 * n⌋₊) :=
    fun hx i => (hx i).trans hrad
  -- every path from `0` to `e₁` controls `D_n(0, e₁)`
  have hC : 0 ≤ 3 / 2 * prop513Const d ξ L * (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) := by
    have : 0 ≤ prop513Const d ξ L := by
      unfold prop513Const
      exact mul_nonneg (mul_nonneg (by norm_num) (lemma512Const_nonneg d ξ L)) hL.le
    positivity
  have key : ∀ P : ℝ → Rd d, IsPcwC1Path P 0 (e₁ d) → MapsTo P (Icc 0 1) (obox (0 : Rd d) 2) →
      lfppDistance d ξ (H n) ≤ 3 / 2 * prop513Const d ξ L * (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) *
        lfppLength ξ (H (n + k)) P := by
    intro P hP hPB
    obtain ⟨γ', hγ', hγ'B, hγ'0, hγ'1, hγ'len⟩ := h513 p rfl rfl rfl rfl H hc m hm1 hlam0.le
      (by linarith) hK2 hpa (g := 3) le_rfl (by push_cast; exact hK3) hamn hKN₀ hCube hgap hK6
      hKlog hK8 hsm hL hJ1 hJ2 hP hPB he₁
    have h1 := lfppDistance_le_of_lemma514Good (hc n) hG hγ' hγ'B (hcbox hγ'0) (hcbox hγ'1)
    calc lfppDistance d ξ (H n) ≤ 3 / 2 * lfppLength ξ (H n) γ' := h1
      _ ≤ 3 / 2 * (prop513Const d ξ L * (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) *
            lfppLength ξ (H (n + k)) P) := mul_le_mul_of_nonneg_left hγ'len (by norm_num)
      _ = 3 / 2 * prop513Const d ξ L * (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) *
            lfppLength ξ (H (n + k)) P := by ring
  rw [cmp_lfppDistance_eq_obox ξ (H (n + k))]
  exact le_mul_lfppDistOn_of_forall (PcwJoined.of_convex (HigherDimLFPP.DGZ.convex_obox 0 2)
    cmp_zero_mem_obox_two cmp_e₁_mem_obox_two) hC key

/-! ## Proposition 5.1 -/

/-- **DGZ Proposition 5.1, the direction used, for the pair `(0, e₁)`** (MA7 D-5.1, G14;
blueprint `r2:prop:51`; ruling M23 (iii)): the interface shape `Prop51Shape` holds for all
`d κ ξ Q`. The restriction `k ≤ c n` of the shape is not used. -/
theorem prop51Shape (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ) : Prop51Shape d κ ξ Q := by
  intro h ε hε
  have hd := h.dim
  have hξ := h.xi_pos
  have hα : 0 < dgzAlpha d Q := dgzAlpha_pos h.subcritical
  have hlam0 : 0 < dgzLambda d Q := dgzLambda_pos hα
  have hlam4 : dgzLambda d Q ≤ 1 / 4 := dgzLambda_le_quarter hα
  obtain ⟨ρ, -, hρ⟩ := h.kernel.exists_radius
  have hR10 : 2 * ρ + 10 ≤ (dgzR ρ : ℝ) := le_dgzR ρ
  have hR100 : 100 ≤ dgzR ρ := by
    unfold dgzR
    omega
  obtain ⟨θ₀, hθ₀, hJθ⟩ := prob_J_compl_le h hρ hR10
  obtain ⟨K₀, hJK⟩ := hJθ θ₀ hθ₀ le_rfl
  obtain ⟨N₀, hdet⟩ := cmp_lfppDistance_le hd hξ hθ₀ hR100 hα
  obtain ⟨K, hKK₀, hK2, hKN₀, hK3, hK40, hK6, hKlog, hK8⟩ :=
    cmp_exists_K ξ hlam0 (dgzR ρ) N₀ K₀ d
  obtain ⟨CJ, hCJ, hJε⟩ := hJK K hKK₀
  obtain ⟨L₀, hJL⟩ := hJε ε hε
  set L : ℝ := max L₀ 1 with hLdef
  have hL : 0 < L := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨u, -, C14, hC14, h514⟩ := prob_not_lemma514Good_le h (lam' := dgzLambda d Q / 2)
    (by positivity) (by linarith)
  set C13 : ℝ := prop513Const d ξ L with hC13def
  have hC13 : 0 ≤ C13 :=
    mul_nonneg (mul_nonneg (by norm_num) (lemma512Const_nonneg d ξ L)) hL.le
  set CT : ℝ := CJ + C14 with hCTdef
  have hCT : 0 < CT := add_pos hCJ hC14
  obtain ⟨Nt, hNt⟩ := cmp_two_rpow_tail hCT
  set c : ℝ := min (1 / (3 * C13 + 1)) (1 / (2 * CT)) with hcdef
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have hc1 : c * (3 * C13 + 1) ≤ 1 := by
    have := min_le_left (1 / (3 * C13 + 1)) (1 / (2 * CT))
    rw [le_div_iff₀ (by positivity)] at this
    exact this
  have hc2 : c * (2 * CT) ≤ 1 := by
    have := min_le_right (1 / (3 * C13 + 1)) (1 / (2 * CT))
    rw [le_div_iff₀ (by positivity)] at this
    exact this
  set M : ℝ := max (((K ^ 4 : ℕ) : ℝ) / (1 - dgzLambda d Q))
    (max (8 / dgzLambda d Q) (4 * (dgzR ρ : ℝ) / dgzLambda d Q)) with hMdef
  refine ⟨c, hc, max Nt ⌈M⌉₊, fun Ω _ P W H hH n k hn hk _ => ?_⟩
  have hPprob := hH.whiteNoise.isProbabilityMeasure
  have hnNt : Nt ≤ n := (le_max_left _ _).trans hn
  have hnM : M ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hn)
  simp only [hMdef, max_le_iff] at hnM
  obtain ⟨hnK, hn8, hnR⟩ := hnM
  have h1lam : 0 < 1 - dgzLambda d Q := by linarith
  rw [div_le_iff₀ h1lam] at hnK
  have hnK' : ((K ^ 4 : ℕ) : ℝ) ≤ (1 - dgzLambda d Q) * n := by linarith
  set p : NiceParams := dgzParams d ξ Q θ₀ ε L K (dgzR ρ) n k with hpdef
  have hJn := hJL Ω P W H hH p rfl rfl rfl rfl rfl rfl (le_max_left _ _) rfl
  have h514n := h514 Ω P W H hH n
  -- the event of the shape forces `(𝒥₁ ∩ 𝒥₂′)ᶜ` or the failure of Lemma 5.14
  have hsub : {ω | lfppDistance d ξ (fun z => H (n + k) z ω) ≤
      c * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) * lfppDistance d ξ (fun z => H n z ω)} ⊆
      {ω | ¬ (EventJ1 p (fun q z => H q z ω) (dgzLevel (dgzLambda d Q) K p.n) ∧
        EventJ2' p (fun q z => H q z ω) (dgzLevel (dgzLambda d Q) K p.n))} ∪
      {ω | ¬ Lemma514Good ξ Q u (dgzLambda d Q / 2) (fun z => H n z ω) n} := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hcon hω
    obtain ⟨⟨hJ1, hJ2⟩, hG⟩ := hcon
    have hcmp := hdet ε L u K n k (fun q z => H q z ω) (fun q => (hH.band q).continuous ω) hK2
      hKN₀ hK3 hK40 hK6 hKlog hK8 hL hnK' hn8 hnR hJ1 hJ2 hG
    have hpos : 0 < lfppDistance d ξ (fun z => H n z ω) :=
      lfppDistance_pos (by omega) ((hH.band n).continuous ω)
    set Dn : ℝ := lfppDistance d ξ (fun z => H n z ω) with hDn
    set Dnk : ℝ := lfppDistance d ξ (fun z => H (n + k) z ω) with hDnk
    set X : ℝ := (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) with hXdef
    set Y : ℝ := (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) with hYdef
    have hXY : X * Y = 1 := by
      rw [hXdef, hYdef, ← Real.rpow_add two_pos,
        show (1 - ξ * Q + ε) * (k : ℝ) + -(1 - ξ * Q + ε) * k = 0 by ring, Real.rpow_zero]
    have hX : 0 ≤ X := (Real.rpow_pos_of_pos two_pos _).le
    have hc3 : 3 / 2 * C13 * c ≤ 1 / 2 := by nlinarith
    have hmain : Dn ≤ 3 / 2 * C13 * c * Dn := by
      calc Dn ≤ 3 / 2 * C13 * X * Dnk := hcmp
        _ ≤ 3 / 2 * C13 * X * (c * Y * Dn) :=
            mul_le_mul_of_nonneg_left hω (by positivity)
        _ = 3 / 2 * C13 * c * (X * Y) * Dn := by ring
        _ = 3 / 2 * C13 * c * Dn := by rw [hXY, mul_one]
    have := mul_le_mul_of_nonneg_right hc3 hpos.le
    linarith
  have hexp : Real.exp (-(n : ℝ) / C14) ≤ (2 : ℝ) ^ (-(n : ℝ) / C14) := by
    rw [neg_div]
    exact cmp_exp_neg_le_two_rpow (by positivity)
  have hreal : CJ * (2 : ℝ) ^ (-(n : ℝ) / CJ) + C14 * Real.exp (-(n : ℝ) / C14) ≤
      (2 : ℝ) ^ (-(c * n)) := by
    calc CJ * (2 : ℝ) ^ (-(n : ℝ) / CJ) + C14 * Real.exp (-(n : ℝ) / C14)
        ≤ CJ * (2 : ℝ) ^ (-(n : ℝ) / CJ) + C14 * (2 : ℝ) ^ (-(n : ℝ) / C14) := by
          have := mul_le_mul_of_nonneg_left hexp hC14.le
          linarith
      _ ≤ CT * (2 : ℝ) ^ (-(n : ℝ) / CT) := cmp_add_two_rpow_le hCJ hC14 n
      _ ≤ (2 : ℝ) ^ (-(n : ℝ) / (2 * CT)) := hNt n hnNt
      _ ≤ (2 : ℝ) ^ (-(c * n)) := by
          refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
          rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
          have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          nlinarith
  calc P {ω | lfppDistance d ξ (fun z => H (n + k) z ω) ≤
        c * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) * lfppDistance d ξ (fun z => H n z ω)}
      ≤ P ({ω | ¬ (EventJ1 p (fun q z => H q z ω) (dgzLevel (dgzLambda d Q) K p.n) ∧
          EventJ2' p (fun q z => H q z ω) (dgzLevel (dgzLambda d Q) K p.n))} ∪
          {ω | ¬ Lemma514Good ξ Q u (dgzLambda d Q / 2) (fun z => H n z ω) n}) :=
        measure_mono hsub
    _ ≤ P {ω | ¬ (EventJ1 p (fun q z => H q z ω) (dgzLevel (dgzLambda d Q) K p.n) ∧
          EventJ2' p (fun q z => H q z ω) (dgzLevel (dgzLambda d Q) K p.n))} +
        P {ω | ¬ Lemma514Good ξ Q u (dgzLambda d Q / 2) (fun z => H n z ω) n} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (CJ * (2 : ℝ) ^ (-(n : ℝ) / CJ)) +
        ENNReal.ofReal (C14 * Real.exp (-(n : ℝ) / C14)) := add_le_add hJn h514n
    _ = ENNReal.ofReal (CJ * (2 : ℝ) ^ (-(n : ℝ) / CJ) + C14 * Real.exp (-(n : ℝ) / C14)) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(c * n))) := ENNReal.ofReal_le_ofReal hreal

end DGZ

end HigherDimLQGMetric
