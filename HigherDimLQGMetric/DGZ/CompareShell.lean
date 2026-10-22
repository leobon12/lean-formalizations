import HigherDimLQGMetric.DGZ.SelfDiam
import HigherDimLQGMetric.DGZ.Lemma36Dyadic
import HigherDimLQGMetric.DGZ.AcrossAroundTools

/-!
# DGZ Lemma 5.14 for `k = 0` and the pair `(0, e₁)` (packet L4c)

Source: [2] Lemma 5.14 (TeX l. 2720–2821), only `k = 0` and the pair `(0, e₁)` (MA7 §4.3, D-5.14;
blueprint Part C `r2:lem:514`, gap G14).

**The form used** (`Lemma514Good`, `prob_not_lemma514Good_le`). Fix `λ' ∈ (0, 1)` and put
`σ_n := 2^{-⌊λ' n⌋}`, `τ_n := 2^{-(1-ξQ+u)n}`. There are `u > 0` and `C` such that, for every
dyadic realization and every `n`, outside probability `C e^{-n/C}`:
(i) `D_n(0, a; B₂(0)) ≤ τ_n` for `a ∈ B̄_{σ_n}(0)` and `D_n(b, e₁; B₂(0)) ≤ τ_n` for
`b ∈ B̄_{σ_n}(e₁)`; (ii) `6 τ_n ≤ D_n(0, e₁; B₂(0))`.
Deterministic consequence (`lfppDistance_le_of_lemma514Good`): every piecewise `C¹` path `γ` in
`B₂(0)` from `B̄_{σ_n}(0)` to `B̄_{σ_n}(e₁)` has `D_n(0, e₁; B₂(0)) ≤ (3/2) len(γ; h_n)`. The set
distance form of [2] (`lemma514`): `P[D_n(0,e₁;B₂) > 3 D_n(B̄_σ(0), B̄_σ(e₁); B₂)] ≤ C e^{-n/C}`
for `0 < σ ≤ σ_n`.

**Proof.** (i) is D-5.14 (i): L3c2's self-internal chaining `chain_selfInternal` (i) with
`ρ = 3/2`, `j = r = ⌊λ' n⌋` on `𝒜_{r,n}` (probability `≥ 1 - C e^{-r/C}`), `η = ξ(Q - √(2d))/2`,
the quantile bound `a^{(q)}_N ≤ A 2^{-(1-ξQ-ε')N}` (`ε' = ηλ'/8`), `chainSum_le_tail`, and
`u = ηλ'/4`: the bound is `≤ K n^{2d} 2^{-(η+ε')r - (1-ξQ-ε')n} ≤ τ_n` for large `n`.
**(ii) replaces the separating shell of D-5.14 (ii)**: by L3b3's lower tail of Lemma 3.6
(`lemma36_lower_of_dgzHyp`, `δ = u/2`), `D_n(0, e₁; B₃(0)) ≥ 2^{-(1-ξQ+u/2)n} ≥ 6 τ_n` outside
probability `C e^{-n/C}` (`n ≥ 6/u`), and `D_n(·;B₂(0)) ≥ D_n(·;B₃(0))`. This needs neither the
field decomposition `h_n = h_l + h_{l,n}` nor the infimum tail of `h_l`. The consequence:
`D_n(0,e₁) ≤ D_n(0,γ(0)) + D_n(γ(0),γ(1)) + D_n(γ(1),e₁) ≤ 2τ_n + len(γ) ≤ D_n(0,e₁)/3 + len(γ)`.
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

/-! ## Elementary bounds on constants -/

/-- `e^{-n/a} ≤ e^{-n/b}` for `0 < a ≤ b`. -/
theorem cmp_exp_neg_div_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (n : ℕ) :
    Real.exp (-(n : ℝ) / a) ≤ Real.exp (-(n : ℝ) / b) := by
  refine Real.exp_le_exp.2 ?_
  rw [neg_div, neg_div, neg_le_neg_iff]
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg n) ha hab

/-- `a e^{-n/a} + b e^{-n/b} ≤ (a + b) e^{-n/(a+b)}`. -/
theorem cmp_add_exp_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    a * Real.exp (-(n : ℝ) / a) + b * Real.exp (-(n : ℝ) / b) ≤
      (a + b) * Real.exp (-(n : ℝ) / (a + b)) := by
  have h1 := cmp_exp_neg_div_mono ha (le_add_of_nonneg_right hb.le) n
  have h2 := cmp_exp_neg_div_mono hb (le_add_of_nonneg_left ha.le) n
  nlinarith

/-- One constant `C ≥ C₁` with `1 ≤ C e^{-n/C}` for all `n < n₀`. -/
theorem cmp_exists_exp_const {C₁ : ℝ} (hC₁ : 0 < C₁) (n₀ : ℕ) :
    ∃ C > 0, (∀ n : ℕ, n < n₀ → 1 ≤ C * Real.exp (-(n : ℝ) / C)) ∧
      ∀ n : ℕ, C₁ * Real.exp (-(n : ℝ) / C₁) ≤ C * Real.exp (-(n : ℝ) / C) := by
  have hn₀ : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg n₀
  refine ⟨max C₁ (n₀ + 3), lt_of_lt_of_le hC₁ (le_max_left _ _), fun n hn => ?_, fun n => ?_⟩
  · have hC3 : (n₀ : ℝ) + 3 ≤ max C₁ (n₀ + 3) := le_max_right _ _
    have hCpos : 0 < max C₁ (n₀ + 3) := by linarith
    have hn' : (n : ℝ) < n₀ := by exact_mod_cast hn
    have h1 : 1 - (n : ℝ) / max C₁ (n₀ + 3) ≤ Real.exp (-(n : ℝ) / max C₁ (n₀ + 3)) := by
      have := Real.add_one_le_exp (-(n : ℝ) / max C₁ (n₀ + 3))
      rw [neg_div] at this ⊢
      linarith
    have h2 : max C₁ (n₀ + 3) * (1 - (n : ℝ) / max C₁ (n₀ + 3)) = max C₁ (n₀ + 3) - n := by
      field_simp
    calc (1 : ℝ) ≤ max C₁ (n₀ + 3) - n := by linarith
      _ = max C₁ (n₀ + 3) * (1 - (n : ℝ) / max C₁ (n₀ + 3)) := h2.symm
      _ ≤ max C₁ (n₀ + 3) * Real.exp (-(n : ℝ) / max C₁ (n₀ + 3)) :=
          mul_le_mul_of_nonneg_left h1 hCpos.le
  · exact mul_le_mul (le_max_left _ _) (cmp_exp_neg_div_mono hC₁ (le_max_left _ _) n)
      (Real.exp_pos _).le (by linarith [le_max_left C₁ ((n₀ : ℝ) + 3)])

/-! ## (i) Small diameters near `0` and `e₁` -/

/-- **D-5.14 (i), deterministic**: on `𝒜_{r,n}`, the points of `B̄_{2^{-r}}(0)` are within
`C₀ · chainSum r n` of `0`, and those of `B̄_{2^{-r}}(e₁)` within the same bound of `e₁`, for the
internal distance of `h_n` in `B₂(0)` (L3c2's chaining (i) with `ρ = 3/2`). -/
theorem cmp_diam_le (hd : 2 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (H : ℕ → Rd d → Ω → ℝ)
      (ξ Q η : ℝ) (q : ℝ≥0∞) (r n : ℕ) (ω : Ω), 0 < ξ → 110 ≤ r → r < n →
      Continuous (fun z => H n z ω) → ω ∈ eventA P H ξ Q η q r n →
      (∀ a ∈ cbox (0 : Rd d) ((2 : ℝ)⁻¹ ^ r),
        lfppDistOn ξ (fun z => H n z ω) (obox (0 : Rd d) 2) 0 a ≤
          C₀ * chainSum P H ξ Q η q r n) ∧
      (∀ b ∈ cbox (e₁ d) ((2 : ℝ)⁻¹ ^ r),
        lfppDistOn ξ (fun z => H n z ω) (obox (0 : Rd d) 2) b (e₁ d) ≤
          C₀ * chainSum P H ξ Q η q r n) := by
  obtain ⟨C₀, hC₀, hch⟩ := chain_selfInternal.{0} hd
  refine ⟨C₀, hC₀, fun {Ω} _ P H ξ Q η q r n ω hξ hr hrn hc hA => ?_⟩
  have key := (hch P H ξ Q η q r n (3 / 2) ω hξ hr hrn (by norm_num) le_rfl hc hA).1 r le_rfl
    hrn.le
  have hr4 : (2 : ℝ)⁻¹ ^ r ≤ 1 / 4 := by
    calc (2 : ℝ)⁻¹ ^ r ≤ (2 : ℝ)⁻¹ ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num)
          (by omega)
      _ = 1 / 4 := by norm_num
  have hmono : ∀ x y : Rd d, x ∈ obox (0 : Rd d) (3 / 2) → y ∈ obox (0 : Rd d) (3 / 2) →
      lfppDistOn ξ (fun z => H n z ω) (obox (0 : Rd d) 2) x y ≤
        lfppDistOn ξ (fun z => H n z ω) (obox (0 : Rd d) (3 / 2)) x y := fun x y hx hy =>
    lfppDistOn_mono (fun z hz i => (hz i).trans (by norm_num))
      (PcwJoined.of_convex (HigherDimLFPP.DGZ.convex_obox 0 (3 / 2)) hx hy)
  have h0 : (0 : Rd d) ∈ obox (0 : Rd d) (3 / 2) := HigherDimLFPP.DGZ.mem_obox_self _ (by norm_num)
  have he : e₁ d ∈ obox (0 : Rd d) (3 / 2) := fun i => by
    show |(e₁ d).ofLp i - (0 : Rd d).ofLp i| < 3 / 2
    rw [PiLp.zero_apply, sub_zero, e₁_ofLp]
    split_ifs <;> norm_num
  constructor
  · intro a ha
    have ha' : a ∈ obox (0 : Rd d) (3 / 2) := fun i => lt_of_le_of_lt (ha i) (by linarith)
    refine (hmono 0 a h0 ha').trans (key 0 h0 a ha' fun i => ?_)
    rw [abs_sub_comm]
    exact ha i
  · intro b hb
    have hb' : b ∈ obox (0 : Rd d) (3 / 2) := fun i => by
      have h1 := hb i
      have h2 := he i
      show |b.ofLp i - (0 : Rd d).ofLp i| < 3 / 2
      rw [PiLp.zero_apply, sub_zero]
      have h3 : |(e₁ d).ofLp i| ≤ 1 := by
        rw [e₁_ofLp]
        split_ifs <;> norm_num
      calc |b.ofLp i| = |(b.ofLp i - (e₁ d).ofLp i) + (e₁ d).ofLp i| := by ring_nf
        _ ≤ |b.ofLp i - (e₁ d).ofLp i| + |(e₁ d).ofLp i| := abs_add_le _ _
        _ < 3 / 2 := by
          have : |b.ofLp i - (e₁ d).ofLp i| ≤ (2 : ℝ)⁻¹ ^ r := h1
          linarith
    exact (hmono b (e₁ d) hb' he).trans (key b hb' (e₁ d) he fun i => hb i)

/-- **The numerics of D-5.14 (i)**: for `u + ε' + β ≤ (η + ε')λ'` (`β > 0`), eventually in `n`,
`K n^{2d} (2^{-(η+ε')})^{⌊λ'n⌋} 2^{-(1-ξQ-ε')n} ≤ 2^{-(1-ξQ+u)n}`. -/
theorem cmp_eventually_chain_le {K η ε' lam' u β : ℝ} (ξ Q : ℝ) (hK : 0 ≤ K) (hηε : 0 < η + ε')
    (hβ : 0 < β) (hmargin : u + ε' + β ≤ (η + ε') * lam') (d : ℕ) :
    ∀ᶠ n : ℕ in atTop, K * (n : ℝ) ^ (2 * d) * ((2 : ℝ) ^ (-(η + ε'))) ^ ⌊lam' * n⌋₊ *
      (2 : ℝ) ^ (-(1 - ξ * Q - ε') * n) ≤ (2 : ℝ) ^ (-(1 - ξ * Q + u) * n) := by
  have h2 : (0 : ℝ) < 2 := two_pos
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpoly := eventually_mul_poly_le_exp (K * (2 : ℝ) ^ (η + ε')) 1 0 d
    (mul_nonneg hK (Real.rpow_pos_of_pos h2 _).le) zero_le_one le_rfl (b := β * Real.log 2)
    (mul_pos hβ hlog)
  filter_upwards [hpoly] with n hn
  set r : ℕ := ⌊lam' * n⌋₊ with hrdef
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hr : lam' * n ≤ (r : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  have e1 : ((2 : ℝ) ^ (-(η + ε'))) ^ r = (2 : ℝ) ^ (-(η + ε') * r) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h2.le]
  have e2 : Real.exp (β * Real.log 2 * n) = (2 : ℝ) ^ (β * n) := by
    rw [Real.rpow_def_of_pos h2]
    ring_nf
  have e3 : ((1 : ℝ) * (n : ℝ) ^ 2 + 0) ^ d = (n : ℝ) ^ (2 * d) := by
    rw [one_mul, add_zero, ← pow_mul]
  rw [e2, e3] at hn
  have hX : 0 ≤ (2 : ℝ) ^ (-(η + ε') * r) * (2 : ℝ) ^ (-(1 - ξ * Q - ε') * n) :=
    mul_nonneg (Real.rpow_pos_of_pos h2 _).le (Real.rpow_pos_of_pos h2 _).le
  have hexp : β * n + (-(η + ε') + (-(η + ε') * r + -(1 - ξ * Q - ε') * n)) ≤
      -(1 - ξ * Q + u) * n := by
    have h1 : (u + ε' + β) * n ≤ (η + ε') * lam' * n := mul_le_mul_of_nonneg_right hmargin hn0
    have h3 : (η + ε') * (lam' * n) ≤ (η + ε') * ((r : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hr hηε.le
    nlinarith
  calc K * (n : ℝ) ^ (2 * d) * ((2 : ℝ) ^ (-(η + ε'))) ^ r * (2 : ℝ) ^ (-(1 - ξ * Q - ε') * n)
      = K * (2 : ℝ) ^ (η + ε') * (n : ℝ) ^ (2 * d) * ((2 : ℝ) ^ (-(η + ε')) *
          ((2 : ℝ) ^ (-(η + ε') * r) * (2 : ℝ) ^ (-(1 - ξ * Q - ε') * n))) := by
        rw [e1, Real.rpow_neg h2.le]
        have : (2 : ℝ) ^ (η + ε') ≠ 0 := (Real.rpow_pos_of_pos h2 _).ne'
        field_simp
    _ ≤ (2 : ℝ) ^ (β * n) * ((2 : ℝ) ^ (-(η + ε')) *
          ((2 : ℝ) ^ (-(η + ε') * r) * (2 : ℝ) ^ (-(1 - ξ * Q - ε') * n))) :=
        mul_le_mul_of_nonneg_right hn (mul_nonneg (Real.rpow_pos_of_pos h2 _).le hX)
    _ = (2 : ℝ) ^ (β * n + (-(η + ε') + (-(η + ε') * r + -(1 - ξ * Q - ε') * n))) := by
        rw [Real.rpow_add h2, Real.rpow_add h2, Real.rpow_add h2]
    _ ≤ (2 : ℝ) ^ (-(1 - ξ * Q + u) * n) := Real.rpow_le_rpow_of_exponent_le one_le_two hexp

/-! ## The good event of Lemma 5.14 -/

/-- The good event of Lemma 5.14 (form used), for the field `φ = h_n`: small `D_n`-diameters
`≤ τ_n = 2^{-(1-ξQ+u)n}` of `B̄_{σ_n}(0)`, `B̄_{σ_n}(e₁)` (`σ_n = 2^{-⌊λ'n⌋}`) as seen from
`0`, `e₁`, and `6 τ_n ≤ D_n(0, e₁; B₂(0))`. -/
def Lemma514Good (ξ Q u lam' : ℝ) (φ : Rd d → ℝ) (n : ℕ) : Prop :=
  (∀ a ∈ cbox (0 : Rd d) ((2 : ℝ)⁻¹ ^ ⌊lam' * n⌋₊),
      lfppDistOn ξ φ (obox (0 : Rd d) 2) 0 a ≤ (2 : ℝ) ^ (-(1 - ξ * Q + u) * n)) ∧
    (∀ b ∈ cbox (e₁ d) ((2 : ℝ)⁻¹ ^ ⌊lam' * n⌋₊),
      lfppDistOn ξ φ (obox (0 : Rd d) 2) b (e₁ d) ≤ (2 : ℝ) ^ (-(1 - ξ * Q + u) * n)) ∧
    6 * (2 : ℝ) ^ (-(1 - ξ * Q + u) * n) ≤ lfppDistance d ξ φ

theorem cmp_zero_mem_obox_two : (0 : Rd d) ∈ obox (0 : Rd d) 2 :=
  HigherDimLFPP.DGZ.mem_obox_self _ two_pos

theorem cmp_e₁_mem_obox_two : e₁ d ∈ obox (0 : Rd d) 2 := by
  rw [← HigherDimLFPP.DGZ.cube_eq_obox]
  exact e₁_mem_cube d

theorem cmp_lfppDistance_eq_obox (ξ : ℝ) (φ : Rd d → ℝ) :
    lfppDistance d ξ φ = lfppDistOn ξ φ (obox (0 : Rd d) 2) 0 (e₁ d) := by
  rw [lfppDistance_eq_lfppDistOn, HigherDimLFPP.DGZ.cube_eq_obox]

/-- The triangle inequality `D(0,e₁) ≤ D(0,a) + D(a,b) + D(b,e₁)` in `B₂(0)`. -/
theorem cmp_lfppDistance_le_add_three {ξ : ℝ} {φ : Rd d → ℝ} (hφ : Continuous φ) {a b : Rd d}
    (ha : a ∈ obox (0 : Rd d) 2) (hb : b ∈ obox (0 : Rd d) 2) :
    lfppDistance d ξ φ ≤ lfppDistOn ξ φ (obox (0 : Rd d) 2) 0 a +
      lfppDistOn ξ φ (obox (0 : Rd d) 2) a b + lfppDistOn ξ φ (obox (0 : Rd d) 2) b (e₁ d) := by
  have hO := HigherDimLFPP.DGZ.isOpen_obox (0 : Rd d) 2
  have hC := (HigherDimLFPP.DGZ.convex_obox (0 : Rd d) 2).isPreconnected
  rw [cmp_lfppDistance_eq_obox]
  have h1 := lfppDistOn_triangle_of_isPreconnected (ξ := ξ) hO hC hφ cmp_zero_mem_obox_two ha
    cmp_e₁_mem_obox_two
  have h2 := lfppDistOn_triangle_of_isPreconnected (ξ := ξ) hO hC hφ ha hb cmp_e₁_mem_obox_two
  linarith

/-- **The deterministic consequence of Lemma 5.14** (form used): on the good event, every
piecewise `C¹` path `γ` in `B₂(0)` from `B̄_{σ_n}(0)` to `B̄_{σ_n}(e₁)` has
`D_n(0, e₁; B₂(0)) ≤ (3/2) len(γ; h_n)`. -/
theorem lfppDistance_le_of_lemma514Good {ξ Q u lam' : ℝ} {φ : Rd d → ℝ} (hφ : Continuous φ)
    {n : ℕ} (hG : Lemma514Good ξ Q u lam' φ n) {γ : ℝ → Rd d} (hγ : IsPcwC1Path γ (γ 0) (γ 1))
    (hγB : MapsTo γ (Icc 0 1) (obox (0 : Rd d) 2))
    (h0 : γ 0 ∈ cbox (0 : Rd d) ((2 : ℝ)⁻¹ ^ ⌊lam' * n⌋₊))
    (h1 : γ 1 ∈ cbox (e₁ d) ((2 : ℝ)⁻¹ ^ ⌊lam' * n⌋₊)) :
    lfppDistance d ξ φ ≤ 3 / 2 * lfppLength ξ φ γ := by
  obtain ⟨hd0, hd1, h6⟩ := hG
  have hγ0 : γ 0 ∈ obox (0 : Rd d) 2 := hγB ⟨le_rfl, zero_le_one⟩
  have hγ1 : γ 1 ∈ obox (0 : Rd d) 2 := hγB ⟨zero_le_one, le_rfl⟩
  have htri := cmp_lfppDistance_le_add_three (ξ := ξ) hφ hγ0 hγ1
  have hlen : lfppDistOn ξ φ (obox (0 : Rd d) 2) (γ 0) (γ 1) ≤ lfppLength ξ φ γ :=
    lfppDistOn_le_lfppLength hγ hγB
  have := hd0 _ h0
  have := hd1 _ h1
  linarith

/-- **DGZ Lemma 5.14 for `k = 0` and the pair `(0, e₁)`, form used** (MA7 D-5.14): the good
event fails with probability at most `C e^{-n/C}`, uniformly in the realization. -/
theorem prob_not_lemma514Good_le {κ : Rd d → ℝ} {ξ Q : ℝ} (h : DGZHyp d κ ξ Q) {lam' : ℝ}
    (hlam' : 0 < lam') (hlam1 : lam' < 1) :
    ∃ u > 0, ∃ C > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ n : ℕ,
        P {ω | ¬ Lemma514Good ξ Q u lam' (fun z => H n z ω) n} ≤
          ENNReal.ofReal (C * Real.exp (-(n : ℝ) / C)) := by
  have hd := h.dim
  have hξ := h.xi_pos
  have hQ : 0 < Q - √(2 * d) := sub_pos.2 h.subcritical
  set η : ℝ := ξ * (Q - √(2 * d)) / 2 with hηdef
  have hη : 0 < η := by positivity
  have hηlt : η < ξ * (Q - √(2 * d)) := by linarith [mul_pos hξ hQ]
  obtain ⟨c₄, hc₄, C₁, hC₁, hAc⟩ := prob_eventA_compl_le hd h.kernel hξ hηlt
  obtain ⟨q, hc₄q, hq1⟩ := exists_between hc₄
  have hq0 : 0 < q := lt_of_le_of_lt zero_le hc₄q
  set ε' : ℝ := η * lam' / 8 with hε'def
  set u : ℝ := η * lam' / 4 with hudef
  have hε' : 0 < ε' := by positivity
  have hu : 0 < u := by positivity
  obtain ⟨A, hA0, haQ⟩ := exists_aQ_le h hq0 hq1 hε'
  obtain ⟨C₀, hC₀, hdiam⟩ := cmp_diam_le hd
  obtain ⟨C₂, hC₂, h36⟩ := lemma36_lower_of_dgzHyp.{0} h (δ := u / 2) (by positivity)
  have hηε : 0 < η + ε' := by positivity
  have hgeo : 0 < 1 - (2 : ℝ) ^ (-(η + ε')) := by
    have : (2 : ℝ) ^ (-(η + ε')) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
    linarith
  set K : ℝ := C₀ * ((A + 1) / (1 - (2 : ℝ) ^ (-(η + ε')))) with hKdef
  have hK : 0 ≤ K := mul_nonneg hC₀.le (div_nonneg (by linarith) hgeo.le)
  -- the numerics, eventually in `n`
  have hmargin : u + ε' + η * lam' / 2 ≤ (η + ε') * lam' := by
    have : 0 ≤ ε' * lam' := mul_nonneg hε'.le hlam'.le
    nlinarith
  have hev1 := cmp_eventually_chain_le ξ Q hK hηε (by positivity : 0 < η * lam' / 2) hmargin d
  have hev2 : ∀ᶠ n : ℕ in atTop, 110 ≤ ⌊lam' * n⌋₊ :=
    (tendsto_nat_floor_atTop.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop
      hlam')).eventually_ge_atTop 110
  have hev3 : ∀ᶠ n : ℕ in atTop, (6 : ℝ) / u ≤ n :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _
  have hev4 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hev1.and (hev2.and (hev3.and hev4)))
  -- the constants
  set C₃ : ℝ := max (C₁ * Real.exp (1 / C₁)) (C₁ / lam') with hC₃def
  have hC₃ : 0 < C₃ := lt_of_lt_of_le (mul_pos hC₁ (Real.exp_pos _)) (le_max_left _ _)
  obtain ⟨C, hC, hsmall, hbig⟩ := cmp_exists_exp_const (add_pos hC₃ hC₂) n₀
  refine ⟨u, hu, C, hC, fun Ω _ P W H hH n => ?_⟩
  have hPprob := hH.whiteNoise.isProbabilityMeasure
  rcases lt_or_ge n n₀ with hn | hn
  · exact prob_le_one.trans (ENNReal.one_le_ofReal.2 (hsmall n hn))
  obtain ⟨hnum, hr110, hn6, hn1⟩ := hn₀ n hn
  set r : ℕ := ⌊lam' * n⌋₊ with hrdef
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hrn : r < n := by
    have h1 : (r : ℝ) ≤ lam' * n := Nat.floor_le (by positivity)
    have h2 : lam' * (n : ℝ) < n := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      nlinarith
    exact_mod_cast h1.trans_lt h2
  set τ : ℝ := (2 : ℝ) ^ (-(1 - ξ * Q + u) * n) with hτdef
  -- the chain bound gives (i) on `𝒜_{r,n}`
  have hchain : C₀ * chainSum P H ξ Q η q r n ≤ τ := by
    have h1 := chainSum_le_tail (P := P) (H := H) (ξ := ξ) (Q := Q) (η := η) (ε := ε') hηε
      (q := q) hA0.le (haQ Ω P W H hH) (j := r) (n := n) hrn.le
    calc C₀ * chainSum P H ξ Q η q r n ≤ C₀ * ((A + 1) / (1 - (2 : ℝ) ^ (-(η + ε'))) *
          (n : ℝ) ^ (2 * d) * ((2 : ℝ) ^ (-(η + ε'))) ^ r * (2 : ℝ) ^ (-(1 - ξ * Q - ε') * n)) :=
          mul_le_mul_of_nonneg_left h1 hC₀.le
      _ = K * (n : ℝ) ^ (2 * d) * ((2 : ℝ) ^ (-(η + ε'))) ^ r *
          (2 : ℝ) ^ (-(1 - ξ * Q - ε') * n) := by
          rw [hKdef]
          ring
      _ ≤ τ := hnum
  -- `6 τ ≤ 2^{-(1-ξQ+u/2)n}`
  have h6 : 6 * τ ≤ (2 : ℝ) ^ (-(1 - ξ * Q + u / 2) * n) := by
    have e : (2 : ℝ) ^ (-(1 - ξ * Q + u / 2) * n) = (2 : ℝ) ^ (u / 2 * n) * τ := by
      rw [hτdef, ← Real.rpow_add two_pos]
      ring_nf
    have h8 : (6 : ℝ) ≤ (2 : ℝ) ^ (u / 2 * n) := by
      have h3 : (3 : ℝ) ≤ u / 2 * n := by
        rw [div_le_iff₀ hu] at hn6
        nlinarith
      calc (6 : ℝ) ≤ (2 : ℝ) ^ (3 : ℝ) := by norm_num
        _ ≤ (2 : ℝ) ^ (u / 2 * n) := Real.rpow_le_rpow_of_exponent_le one_le_two h3
    rw [e]
    exact mul_le_mul_of_nonneg_right h8 (Real.rpow_pos_of_pos two_pos _).le
  -- the bad event is covered by `𝒜ᶜ` and the lower tail of `D_n(0, e₁; B₃(0))`
  have hsub : {ω | ¬ Lemma514Good ξ Q u lam' (fun z => H n z ω) n} ⊆
      (eventA P H ξ Q η q r n)ᶜ ∪ {ω | lfppDistOn ξ (fun z => H n z ω) (obox (0 : Rd d) 3) 0
        (e₁ d) < (2 : ℝ) ^ (-(1 - ξ * Q + u / 2) * n)} := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, mem_compl_iff, mem_ofPred_eq, not_or, not_not, not_lt] at hcon
    obtain ⟨hAω, hDω⟩ := hcon
    apply hω
    have hc := (hH.band n).continuous ω
    obtain ⟨hd0, hde⟩ := hdiam P H ξ Q η q r n ω hξ hr110 hrn hc hAω
    refine ⟨fun a ha => (hd0 a ha).trans hchain, fun b hb => (hde b hb).trans hchain, ?_⟩
    have hmono : lfppDistOn ξ (fun z => H n z ω) (obox (0 : Rd d) 3) 0 (e₁ d) ≤
        lfppDistance d ξ (fun z => H n z ω) := by
      rw [cmp_lfppDistance_eq_obox]
      exact lfppDistOn_mono (fun z hz i => (hz i).trans (by norm_num))
        (PcwJoined.of_convex (HigherDimLFPP.DGZ.convex_obox 0 2) cmp_zero_mem_obox_two
          cmp_e₁_mem_obox_two)
    linarith
  have h0mem : (0 : Rd d) ∈ cbox (0 : Rd d) 2 := fun i => by
    show |(0 : Rd d).ofLp i - (0 : Rd d).ofLp i| ≤ 2
    rw [sub_self, abs_zero]
    norm_num
  have he₁mem : e₁ d ∈ cbox (0 : Rd d) 2 := fun i => by
    show |(e₁ d).ofLp i - (0 : Rd d).ofLp i| ≤ 2
    rw [PiLp.zero_apply, sub_zero, e₁_ofLp]
    split_ifs <;> norm_num
  have hfar : ∃ i, (1 : ℝ) / 2 ≤ |(0 : Rd d).ofLp i - (e₁ d).ofLp i| := by
    refine ⟨⟨0, by omega⟩, ?_⟩
    rw [PiLp.zero_apply, e₁_ofLp]
    norm_num
  -- the first term: `C₁ e^{-r/C₁} ≤ C₃ e^{-n/C₃}`
  have hterm1 : C₁ * Real.exp (-(r : ℝ) / C₁) ≤ C₃ * Real.exp (-(n : ℝ) / C₃) := by
    have hr' : lam' * n - 1 ≤ r := by
      have := Nat.lt_floor_add_one (lam' * n)
      linarith
    have e1 : C₁ * Real.exp (-(r : ℝ) / C₁) ≤
        C₁ * Real.exp (1 / C₁) * Real.exp (-(n : ℝ) / (C₁ / lam')) := by
      rw [mul_assoc, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC₁.le
      have key : -(r : ℝ) / C₁ ≤ (1 - lam' * n) / C₁ :=
        div_le_div_of_nonneg_right (by linarith) hC₁.le
      have e : 1 / C₁ + -(n : ℝ) / (C₁ / lam') = (1 - lam' * n) / C₁ := by
        field_simp
        ring
      rw [e]
      exact key
    refine e1.trans (mul_le_mul (le_max_left _ _) ?_ (Real.exp_pos _).le hC₃.le)
    exact cmp_exp_neg_div_mono (div_pos hC₁ hlam') (le_max_right _ _) n
  calc P {ω | ¬ Lemma514Good ξ Q u lam' (fun z => H n z ω) n}
      ≤ P ((eventA P H ξ Q η q r n)ᶜ ∪ {ω | lfppDistOn ξ (fun z => H n z ω) (obox (0 : Rd d) 3)
          0 (e₁ d) < (2 : ℝ) ^ (-(1 - ξ * Q + u / 2) * n)}) := measure_mono hsub
    _ ≤ P (eventA P H ξ Q η q r n)ᶜ + P {ω | lfppDistOn ξ (fun z => H n z ω)
          (obox (0 : Rd d) 3) 0 (e₁ d) < (2 : ℝ) ^ (-(1 - ξ * Q + u / 2) * n)} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (C₁ * Real.exp (-(r : ℝ) / C₁)) +
          ENNReal.ofReal (C₂ * Real.exp (-(n : ℝ) / C₂)) :=
        add_le_add (hAc q hc₄q hq1 hH r n (by omega) hrn)
          (h36 Ω P W H hH 0 (e₁ d) h0mem he₁mem hfar n)
    _ ≤ ENNReal.ofReal (C₃ * Real.exp (-(n : ℝ) / C₃)) +
          ENNReal.ofReal (C₂ * Real.exp (-(n : ℝ) / C₂)) :=
        add_le_add (ENNReal.ofReal_le_ofReal hterm1) le_rfl
    _ = ENNReal.ofReal (C₃ * Real.exp (-(n : ℝ) / C₃) + C₂ * Real.exp (-(n : ℝ) / C₂)) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal (C * Real.exp (-(n : ℝ) / C)) :=
        ENNReal.ofReal_le_ofReal ((cmp_add_exp_le hC₃ hC₂ n).trans (hbig n))

/-- **DGZ Lemma 5.14 for `k = 0` and the pair `(0, e₁)`**, the set-distance form of [2] (MA7
D-5.14): for `0 < σ ≤ σ_n = 2^{-⌊λ'n⌋}`,
`P[D_n(0, e₁; B₂(0)) > 3 D_n(B̄_σ(0), B̄_σ(e₁); B₂(0))] ≤ C e^{-n/C}`. -/
theorem lemma514 {κ : Rd d → ℝ} {ξ Q : ℝ} (h : DGZHyp d κ ξ Q) {lam' : ℝ} (hlam' : 0 < lam')
    (hlam1 : lam' < 1) :
    ∃ C > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ (n : ℕ) (σ : ℝ), 0 < σ →
        σ ≤ 1 / 2 → σ ≤ (2 : ℝ)⁻¹ ^ ⌊lam' * n⌋₊ →
        P {ω | 3 * lfppSetDist ξ (fun z => H n z ω) (obox (0 : Rd d) 2) (cbox 0 σ)
          (cbox (e₁ d) σ) < lfppDistance d ξ (fun z => H n z ω)} ≤
          ENNReal.ofReal (C * Real.exp (-(n : ℝ) / C)) := by
  obtain ⟨u, hu, C, hC, hP⟩ := prob_not_lemma514Good_le h hlam' hlam1
  refine ⟨C, hC, fun Ω _ P W H hH n σ hσ hσ2 hσn =>
    le_trans (measure_mono ?_) (hP Ω P W H hH n)⟩
  intro ω hω hG
  simp only [mem_ofPred_eq] at hω
  obtain ⟨hd0, hd1, h6⟩ := hG
  have hφ := (hH.band n).continuous ω
  have hσ12 : σ < 2 := by linarith
  have hτ : 0 < (2 : ℝ) ^ (-(1 - ξ * Q + u) * n) := Real.rpow_pos_of_pos two_pos _
  have hA : ∀ a ∈ cbox (0 : Rd d) σ, a ∈ obox (0 : Rd d) 2 := fun a ha i =>
    lt_of_le_of_lt (ha i) hσ12
  have hB : ∀ b ∈ cbox (e₁ d) σ, b ∈ obox (0 : Rd d) 2 := fun b hb i => by
    have h1 := hb i
    show |b.ofLp i - (0 : Rd d).ofLp i| < 2
    rw [PiLp.zero_apply, sub_zero]
    have h3 : |(e₁ d).ofLp i| ≤ 1 := by
      rw [e₁_ofLp]
      split_ifs <;> norm_num
    calc |b.ofLp i| = |(b.ofLp i - (e₁ d).ofLp i) + (e₁ d).ofLp i| := by ring_nf
      _ ≤ |b.ofLp i - (e₁ d).ofLp i| + |(e₁ d).ofLp i| := abs_add_le _ _
      _ < 2 := by
        have : |b.ofLp i - (e₁ d).ofLp i| ≤ σ := h1
        linarith
  have hsub0 : cbox (0 : Rd d) σ ⊆ cbox (0 : Rd d) ((2 : ℝ)⁻¹ ^ ⌊lam' * n⌋₊) :=
    fun a ha i => (ha i).trans hσn
  have hsub1 : cbox (e₁ d) σ ⊆ cbox (e₁ d) ((2 : ℝ)⁻¹ ^ ⌊lam' * n⌋₊) :=
    fun a ha i => (ha i).trans hσn
  have hne0 : (cbox (0 : Rd d) σ).Nonempty := ⟨0, fun i => by
    show |(0 : Rd d).ofLp i - (0 : Rd d).ofLp i| ≤ σ
    rw [sub_self, abs_zero]
    exact hσ.le⟩
  have hne1 : (cbox (e₁ d) σ).Nonempty := ⟨e₁ d, fun i => by
    show |(e₁ d).ofLp i - (e₁ d).ofLp i| ≤ σ
    rw [sub_self, abs_zero]
    exact hσ.le⟩
  have key : 2 / 3 * lfppDistance d ξ (fun z => H n z ω) ≤
      lfppSetDist ξ (fun z => H n z ω) (obox (0 : Rd d) 2) (cbox 0 σ) (cbox (e₁ d) σ) := by
    refine le_lfppSetDist hne0 hne1 fun a ha b hb => ?_
    have htri := cmp_lfppDistance_le_add_three (ξ := ξ) hφ (hA a ha) (hB b hb)
    have := hd0 a (hsub0 ha)
    have := hd1 b (hsub1 hb)
    linarith
  linarith

end DGZ

end HigherDimLQGMetric
