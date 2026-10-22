import HigherDimLQGMetric.DGZ.ChainLink
import HigherDimLQGMetric.DGZ.Sec41Config

/-!
# DGZ Props 4.3^s, 4.5^s: self-internal chaining on `𝒜_{r,n}` (packet L3c2; MA7 D-4.3s)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), Props 4.3 and 4.5 (TeX l. 1487–1600);
planning audit `planning/audits/MA7-ref2-sections-4-6.md`, §5 row L3c2 and Details (a) D-4.3s
(self-internal chaining; strengthens Props 4.3 and 4.5 and repairs the footnote of TeX l. 1898).

Notation (`h_n = H n · ω`, `ε_k = 2^{-k}`, `a_N = a^{(q)}_N = aQ P H ξ N q`):
* `eventA P H ξ Q η q r n` is `𝒜_{r,n} = 𝒢_n ∩ ⋂_{r ≤ k ≤ n-1} ℱ_{k,n}` (so `𝒜_{r,n} ⊆ ℰ_{k,n}`
  for `r - 1 ≤ k ≤ n - 1`);
* `chainSum P H ξ Q η q j n = Σ_{k=j}^{n-1} k^{2d} 2^{-(1-ξQ+η)k} a_{n-k} + n^{2d} 2^{-(1-ξQ+η)n}`,
  the sum of D-4.3s with `a₀ := 1` (the term `k = n`).

Main result (`chain_selfInternal`, MA7 D-4.3s (i) and (ii), deterministic on `𝒜_{r,n}`): there
is `C = C(d)` such that for `ξ > 0`, any `η, Q, q`, integers `110 ≤ r < n`, `ρ ∈ [1, 3/2]` and
every `ω ∈ 𝒜_{r,n}` (with `h_n` continuous):
* (i) `D_n(x, y; B_ρ(0)) ≤ C · chainSum j n` for `x, y ∈ B_ρ(0)`, `|x - y|_∞ ≤ 2^{-j}`,
  `r ≤ j ≤ n`;
* (ii) `selfDiam_n(B_ρ(0)) ≤ C 2^r · chainSum r n`.

Proof (MA7 D-4.3s with explicit constants). The contraction drift is `δ_k = 1000 k² 2^{-k}`
(closed form; MA7 takes `100 Σ_{k' ≥ k} k'² 2^{-k'}`) and `x^{(k)} = (1 - δ_k/ρ) x`, so
`|x^{(k)}|_∞ ≤ ρ - δ_k`, `|x - x^{(k)}|_∞ ≤ δ_k` and
`|x^{(k)} - x^{(k+1)}|_∞ ≤ δ_k - δ_{k+1} ≤ 1000 (k+1)² 2^{-(k+1)}`.
* Points (`exists_chainPoint`): for `j ≤ ℓ ≤ n - 2`, the third clause of `ℱ_{ℓ+1,n}` at the site
  of `2^{-(ℓ+1)} ℤ^d` obtained by rounding `x^{(ℓ)}` toward `0` gives a coarse site `u_ℓ`, free
  for `O_ℓ`, with `2 u_ℓ` free for `O_{ℓ+1}` and `|2^{-ℓ} u_ℓ - x^{(ℓ)}|_∞ ≤ ℓ² 2^{-ℓ}`; for
  `ℓ = n - 1` the hole lemma on `ℰ_{n-1,n}` gives `u_{n-1}`, free for `O_{n-1}`, with the same
  bound.
* Links (`ChainLink.lean`): `u_{ℓ+1}` and `2 u_ℓ` are free for `O_{ℓ+1}`, within `1003 (ℓ+1)²`
  lattice steps, with margin `≥ (D_{ℓ+1} + 3) 2^{-(ℓ+1)}` to `∂B_ρ(0)`, so
  `D_n(X_ℓ, X_{ℓ+1}; B_ρ) ≤ 2011^d (ℓ+1)^{2d} 2^{-(1-ξQ+η)(ℓ+1)} a_{n-ℓ-1}`; the middle link
  between the points of `x` and `y` at scale `j` is the same with `|u - v|_∞ ≤ (2j² + 1)`.
* The segment from `x` to `X_{n-1}` has `ℓ^∞`-length `≤ 2002 n² 2^{-n}`, and
  `e^{ξ h_n} ≤ 2^{(ξQ-η)n}` on `B̄₃(0)` (`𝒢_n`).
* (ii): split the segment `[x, y]` into `3 · 2^r` pieces of `ℓ^∞`-length `< 2^{-r}` and apply (i)
  with `j = r` (instead of MA7's rounding to the grid `2^{-r} ℤ^d`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Relation
open scoped ENNReal

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox latPt_apply convex_obox mem_obox_self roundLat
  abs_latPt_roundLat_le abs_latPt_roundLat_sub_lt)

variable {d : ℕ}

/-! ### The event `𝒜_{r,n}` and the chaining sum -/

/-- `𝒜_{r,n} = 𝒢_n ∩ ⋂_{r ≤ k ≤ n-1} ℱ_{k,n}` (MA7 D-4.3s) -/
def eventA {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (H : ℕ → Rd d → Ω → ℝ)
    (ξ Q η : ℝ) (q : ℝ≥0∞) (r n : ℕ) : Set Ω :=
  eventG ξ Q η H n ∩ ⋂ k ∈ Finset.Ico r n, eventF P H ξ Q η q k n

/-- the chaining sum of MA7 D-4.3s,
`Σ_{k=j}^{n-1} k^{2d} 2^{-(1-ξQ+η)k} a^{(q)}_{n-k} + n^{2d} 2^{-(1-ξQ+η)n}` (the term `k = n` with
`a^{(q)}_0 := 1`) -/
def chainSum {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (H : ℕ → Rd d → Ω → ℝ)
    (ξ Q η : ℝ) (q : ℝ≥0∞) (j n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico j n, (k : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * k) * aQ P H ξ (n - k) q +
    (n : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n)

theorem mem_eventA_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℕ → Rd d → Ω → ℝ}
    {ξ Q η : ℝ} {q : ℝ≥0∞} {r n : ℕ} {ω : Ω} :
    ω ∈ eventA P H ξ Q η q r n ↔
      ω ∈ eventG ξ Q η H n ∧ ∀ k, r ≤ k → k < n → ω ∈ eventF P H ξ Q η q k n := by
  simp only [eventA, mem_inter_iff, mem_iInter, Finset.mem_Ico]
  exact Iff.rfl.and (forall_congr' fun k => ⟨fun h hr hn => h ⟨hr, hn⟩, fun h hk => h hk.1 hk.2⟩)

/-! ### Numerics: the contraction drift `δ_k = 1000 k² 2^{-k}` -/

/-- the contraction drift `δ_k = 1000 k² 2^{-k}` of the chaining (MA7 D-4.3s uses
`100 Σ_{k' ≥ k} k'² 2^{-k'}`) -/
def chainDelta (k : ℕ) : ℝ := 1000 * (k : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ k

theorem chainDelta_nonneg (k : ℕ) : 0 ≤ chainDelta k := by
  unfold chainDelta; positivity

lemma thousand_mul_sq_le_two_pow {k : ℕ} (hk : 20 ≤ k) : 1000 * k ^ 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h1 : (k + 1) ^ 2 ≤ 2 * k ^ 2 := by nlinarith
    calc 1000 * (k + 1) ^ 2 ≤ 1000 * (2 * k ^ 2) := Nat.mul_le_mul_left 1000 h1
      _ = 2 * (1000 * k ^ 2) := by ring
      _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (k + 1) := by ring

theorem chainDelta_le_one {k : ℕ} (hk : 20 ≤ k) : chainDelta k ≤ 1 := by
  unfold chainDelta
  have h' : (1000 : ℝ) * (k : ℝ) ^ 2 ≤ (2 : ℝ) ^ k := by
    exact_mod_cast thousand_mul_sq_le_two_pow hk
  rw [inv_pow, ← div_eq_mul_inv, div_le_one (by positivity)]
  exact h'

lemma inv_two_pow_succ' (k : ℕ) : (2 : ℝ)⁻¹ ^ (k + 1) = (2 : ℝ)⁻¹ ^ k / 2 := by
  rw [pow_succ]; ring

theorem chainDelta_succ_le {k : ℕ} (hk : 3 ≤ k) : chainDelta (k + 1) ≤ chainDelta k := by
  unfold chainDelta
  rw [inv_two_pow_succ']
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hε : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
  push_cast
  have key : ((k : ℝ) + 1) ^ 2 ≤ 2 * (k : ℝ) ^ 2 := by nlinarith
  calc 1000 * ((k : ℝ) + 1) ^ 2 * ((2 : ℝ)⁻¹ ^ k / 2)
      = 500 * ((k : ℝ) + 1) ^ 2 * (2 : ℝ)⁻¹ ^ k := by ring
    _ ≤ 500 * (2 * (k : ℝ) ^ 2) * (2 : ℝ)⁻¹ ^ k := by gcongr
    _ = 1000 * (k : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ k := by ring

theorem chainDelta_sub_succ_le (k : ℕ) :
    chainDelta k - chainDelta (k + 1) ≤ 1000 * ((k : ℝ) + 1) ^ 2 * (2 : ℝ)⁻¹ ^ (k + 1) := by
  unfold chainDelta
  rw [inv_two_pow_succ']
  have hε : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
  push_cast
  have key : (k : ℝ) ^ 2 ≤ ((k : ℝ) + 1) ^ 2 := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have h2 : 1000 * (k : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ k ≤ 1000 * ((k : ℝ) + 1) ^ 2 * (2 : ℝ)⁻¹ ^ k := by
    gcongr
  nlinarith

/-! ### The contraction `x ↦ (1 - δ/ρ) x` -/

section Contraction

variable {ρ δ δ' t t' : ℝ}

lemma contract_coef_nonneg (hρ : 1 ≤ ρ) (hδ1 : δ ≤ 1) : 0 ≤ 1 - δ / ρ := by
  have : δ / ρ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  linarith

lemma abs_contract_le (hρ : 1 ≤ ρ) (hδ1 : δ ≤ 1) (ht : |t| < ρ) :
    |(1 - δ / ρ) * t| ≤ ρ - δ := by
  have hc := contract_coef_nonneg hρ hδ1
  rw [abs_mul, abs_of_nonneg hc]
  calc (1 - δ / ρ) * |t| ≤ (1 - δ / ρ) * ρ := mul_le_mul_of_nonneg_left ht.le hc
    _ = ρ - δ := by field_simp

lemma abs_sub_contract_le (hρ : 1 ≤ ρ) (hδ0 : 0 ≤ δ) (ht : |t| < ρ) :
    |t - (1 - δ / ρ) * t| ≤ δ := by
  have hρ0 : 0 < ρ := by linarith
  have e : t - (1 - δ / ρ) * t = (δ / ρ) * t := by ring
  rw [e, abs_mul, abs_of_nonneg (div_nonneg hδ0 hρ0.le)]
  calc δ / ρ * |t| ≤ δ / ρ * ρ := mul_le_mul_of_nonneg_left ht.le (div_nonneg hδ0 hρ0.le)
    _ = δ := by field_simp

lemma abs_contract_sub_contract_le (hρ : 1 ≤ ρ) (hδδ' : δ' ≤ δ) (ht : |t| < ρ) :
    |(1 - δ / ρ) * t - (1 - δ' / ρ) * t| ≤ δ - δ' := by
  have hρ0 : 0 < ρ := by linarith
  have e : (1 - δ / ρ) * t - (1 - δ' / ρ) * t = -((δ - δ') / ρ * t) := by ring
  rw [e, abs_neg, abs_mul, abs_of_nonneg (div_nonneg (by linarith) hρ0.le)]
  calc (δ - δ') / ρ * |t| ≤ (δ - δ') / ρ * ρ :=
        mul_le_mul_of_nonneg_left ht.le (div_nonneg (by linarith) hρ0.le)
    _ = δ - δ' := by field_simp

lemma abs_contract_sub_le (hρ : 1 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    |(1 - δ / ρ) * t - (1 - δ / ρ) * t'| ≤ |t - t'| := by
  have hc := contract_coef_nonneg hρ hδ1
  have hc1 : 1 - δ / ρ ≤ 1 := by
    have : 0 ≤ δ / ρ := div_nonneg hδ0 (by linarith)
    linarith
  rw [← mul_sub, abs_mul, abs_of_nonneg hc]
  calc (1 - δ / ρ) * |t - t'| ≤ 1 * |t - t'| := mul_le_mul_of_nonneg_right hc1 (abs_nonneg _)
    _ = |t - t'| := one_mul _

end Contraction

/-! ### The points of the chaining -/

/-- **The points of D-4.3s** at scale `ℓ` (`110 ≤ ℓ < n`): for a point `w` with `|w|_∞ < 2` there
is a site `u` of `2^{-ℓ} ℤ^d`, free for the `ℓ`-open configuration, with
`|2^{-ℓ} u - w|_∞ ≤ ℓ² 2^{-ℓ}`, such that `2 u` is free for the `(ℓ+1)`-open configuration when
`ℓ + 1 < n`. For `ℓ + 1 < n` this is the third clause of `ℱ_{ℓ+1,n}` at the rounding of `w` toward
`0` to `2^{-(ℓ+1)} ℤ^d`; for `ℓ = n - 1` it is the hole lemma on `ℰ_{n-1,n}`. -/
theorem exists_chainPoint (hd : 2 ≤ d) {φ : Rd d → ℝ} {ξ Q η : ℝ} {a : ℕ → ℝ} {ℓ n : ℕ}
    (hℓ : 110 ≤ ℓ) (hℓn : ℓ < n)
    (hE : SmallClusters (mOpen ξ Q η φ ℓ (a ℓ)) (ℓ ^ 2 - 101 ^ 2))
    (hF : ℓ + 1 < n → ∀ x ∈ latRegion (ℓ + 1), ∃ y : Zd d,
      WithinInf (((ℓ + 1 : ℕ) : ℤ) ^ 2) x (2 • y) ∧
      FreeSite (mOpen ξ Q η φ (ℓ + 1) (a (ℓ + 1))) (2 • y) ∧ FreeSite (mOpen ξ Q η φ ℓ (a ℓ)) y)
    {w : Rd d} (hw : ∀ i, |w i| < 2) :
    ∃ u : Zd d, FreeSite (mOpen ξ Q η φ ℓ (a ℓ)) u ∧
      (∀ i, |latPt ((2 : ℝ)⁻¹ ^ ℓ) u i - w i| ≤ (ℓ : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ ℓ) ∧
      (ℓ + 1 < n → FreeSite (mOpen ξ Q η φ (ℓ + 1) (a (ℓ + 1))) (2 • u)) := by
  have hℓ' : (110 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  rcases Nat.lt_or_ge (ℓ + 1) n with h | h
  · set s : ℝ := (2 : ℝ)⁻¹ ^ (ℓ + 1) with hs_def
    have hs : 0 < s := by positivity
    set p : Zd d := roundLat s w with hp_def
    have hp : p ∈ latRegion (ℓ + 1) := (mem_latRegion_iff_mem_obox _ _).2 fun i => by
      rw [PiLp.zero_apply, sub_zero]
      exact (abs_latPt_roundLat_le hs w i).trans_lt (hw i)
    obtain ⟨y, hpy, hy2, hy⟩ := hF h p hp
    refine ⟨y, hy, fun i => ?_, fun _ => hy2⟩
    rw [← latPt_two_smul]
    have h1 := abs_latPt_sub_le_of_withinInf hs.le hpy.symm i
    have h2 := abs_latPt_roundLat_sub_lt hs w i
    push_cast at h1
    have h3 : |latPt s (2 • y) i - w i| ≤ s * ((ℓ : ℝ) + 1) ^ 2 + s := by
      have := abs_sub_le (latPt s (2 • y) i) (latPt s p i) (w i)
      linarith
    have key : s * ((ℓ : ℝ) + 1) ^ 2 + s ≤ (ℓ : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ ℓ := by
      rw [hs_def, inv_two_pow_succ']
      have hε : (0 : ℝ) < (2 : ℝ)⁻¹ ^ ℓ := by positivity
      have : ((ℓ : ℝ) + 1) ^ 2 + 1 ≤ 2 * (ℓ : ℝ) ^ 2 := by nlinarith
      nlinarith
    exact h3.trans key
  · have hℓ1 : ℓ + 1 = n := by omega
    set D : ℕ := ℓ ^ 2 - 101 ^ 2 with hD_def
    set s : ℝ := (2 : ℝ)⁻¹ ^ ℓ with hs_def
    have hs : 0 < s := by positivity
    obtain ⟨u, hup, hu⟩ := holeLemma d hd _ _ hE (roundLat s w)
    refine ⟨u, hu, fun i => ?_, fun h' => absurd h' (by omega)⟩
    have h1 := abs_latPt_sub_le_of_withinInf hs.le hup i
    have h2 := abs_latPt_roundLat_sub_lt hs w i
    have hD : (D : ℝ) + 2 ≤ (ℓ : ℝ) ^ 2 := by
      have h101 : 101 ^ 2 ≤ ℓ ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have : D + 2 ≤ ℓ ^ 2 := by rw [hD_def]; omega
      exact_mod_cast this
    push_cast at h1
    have h3 := abs_sub_le (latPt s u i) (latPt s (roundLat s w) i) (w i)
    calc |latPt s u i - w i| ≤ s * ((D : ℝ) + 1) + s := by linarith
      _ = s * ((D : ℝ) + 2) := by ring
      _ ≤ s * (ℓ : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hD hs.le
      _ = (ℓ : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ ℓ := by rw [hs_def]; ring

/-! ### Links with the constants of the chaining -/

/-- **A link of the chaining** (MA7 D-4.3s, Step 2, with explicit constants): at a scale `k ≥ 1`,
two free sites `u, v` of the `k`-open configuration (under `SmallClusters` with `D_k = k² - 101²`)
with `|2^{-k} u - 2^{-k} v|_∞ ≤ 1003 k² 2^{-k}` and
`|2^{-k} u|_∞, |2^{-k} v|_∞ ≤ ρ - (k² + 3) 2^{-k}` (`ρ ≤ 2`) satisfy
`D(2^{-k} u, 2^{-k} v; B_ρ(0)) ≤ 2011^d k^{2d} 2^{-(1-ξQ+η)k} a`. -/
theorem lfppDistOn_le_link (hd : 1 ≤ d) {φ : Rd d → ℝ} (hφ : Continuous φ) {ξ Q η a ρ : ℝ}
    {k : ℕ} (hk : 1 ≤ k) (hρ : ρ ≤ 2)
    (hsmall : SmallClusters (mOpen ξ Q η φ k a) (k ^ 2 - 101 ^ 2)) {u v : Zd d}
    (hu : FreeSite (mOpen ξ Q η φ k a) u) (hv : FreeSite (mOpen ξ Q η φ k a) v)
    (huv : ∀ i, |latPt ((2 : ℝ)⁻¹ ^ k) u i - latPt ((2 : ℝ)⁻¹ ^ k) v i| ≤
      1003 * (k : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ k)
    (hmu : ∀ i, |latPt ((2 : ℝ)⁻¹ ^ k) u i| ≤ ρ - ((k : ℝ) ^ 2 + 3) * (2 : ℝ)⁻¹ ^ k)
    (hmv : ∀ i, |latPt ((2 : ℝ)⁻¹ ^ k) v i| ≤ ρ - ((k : ℝ) ^ 2 + 3) * (2 : ℝ)⁻¹ ^ k) :
    lfppDistOn ξ φ (obox (0 : Rd d) ρ) (latPt ((2 : ℝ)⁻¹ ^ k) u) (latPt ((2 : ℝ)⁻¹ ^ k) v) ≤
      (2011 : ℝ) ^ d * ((k : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * k) * a) := by
  set s : ℝ := (2 : ℝ)⁻¹ ^ k with hs_def
  have hs : 0 < s := by positivity
  set D : ℕ := k ^ 2 - 101 ^ 2 with hD_def
  have hDk : D ≤ k ^ 2 := Nat.sub_le _ _
  have hDk' : (D : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast hDk
  have hR : WithinInf ((1003 * k ^ 2 : ℕ) : ℤ) u v :=
    withinInf_of_abs_latPt_sub_le hs fun i => by
      have := huv i
      push_cast
      linarith
  have hmu' : ∀ i, |latPt s u i| + ((D : ℝ) + 3) * s ≤ ρ := fun i => by
    have := hmu i
    have : (D : ℝ) * s ≤ (k : ℝ) ^ 2 * s := mul_le_mul_of_nonneg_right hDk' hs.le
    linarith
  have hmv' : ∀ i, |latPt s v i| + ((D : ℝ) + 3) * s ≤ ρ := fun i => by
    have := hmv i
    have : (D : ℝ) * s ≤ (k : ℝ) ^ 2 * s := mul_le_mul_of_nonneg_right hDk' hs.le
    linarith
  have hL := lfppDistOn_le_of_freeSite hd hφ hρ hsmall hu hv hR hmu' hmv'
  have hureg : u ∈ latRegion k := (mem_latRegion_iff_mem_obox k u).2 fun i => by
    rw [PiLp.zero_apply, sub_zero, ← hs_def]
    have := hmu i
    have : 0 < ((k : ℝ) ^ 2 + 3) * s := by positivity
    linarith
  have ha : 0 ≤ a := nonneg_of_mem_mOpen hd hu.1 hureg
  have hb : 0 ≤ (2 : ℝ) ^ (-(1 - ξ * Q + η) * k) * a :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) ha
  have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hcnt : 2 * (1003 * k ^ 2 + D + 1) + 1 ≤ 2011 * k ^ 2 := by omega
  have hcnt' : ((2 * (1003 * k ^ 2 + D + 1) + 1 : ℕ) : ℝ) ^ d ≤
      (2011 : ℝ) ^ d * (k : ℝ) ^ (2 * d) := by
    have h1 : ((2 * (1003 * k ^ 2 + D + 1) + 1 : ℕ) : ℝ) ≤ 2011 * (k : ℝ) ^ 2 := by
      exact_mod_cast hcnt
    calc ((2 * (1003 * k ^ 2 + D + 1) + 1 : ℕ) : ℝ) ^ d ≤ (2011 * (k : ℝ) ^ 2) ^ d :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) h1 d
      _ = (2011 : ℝ) ^ d * (k : ℝ) ^ (2 * d) := by rw [mul_pow, pow_mul]
  calc lfppDistOn ξ φ (obox (0 : Rd d) ρ) (latPt s u) (latPt s v)
      ≤ ((2 * (1003 * k ^ 2 + D + 1) + 1 : ℕ) : ℝ) ^ d *
          ((2 : ℝ) ^ (-(1 - ξ * Q + η) * k) * a) := hL
    _ ≤ (2011 : ℝ) ^ d * (k : ℝ) ^ (2 * d) * ((2 : ℝ) ^ (-(1 - ξ * Q + η) * k) * a) :=
        mul_le_mul_of_nonneg_right hcnt' hb
    _ = (2011 : ℝ) ^ d * ((k : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * k) * a) := by ring

/-! ### The half chain -/

/-- `B_ρ(0) ⊆ B̄₃(0)` for `ρ ≤ 3`. -/
lemma obox_zero_subset_cbox_three {ρ : ℝ} (hρ : ρ ≤ 3) : obox (0 : Rd d) ρ ⊆ cbox (0 : Rd d) 3 :=
  fun _ hz i => ((hz i).le).trans hρ

/-- **The segment bound on `𝒢_n`** (MA7 D-4.3s, Step 1): if `ξ h_n ≤ (ξQ - η) n log 2` on `B̄₃(0)`,
then for `x, y ∈ B_ρ(0)` (`ρ ≤ 3`) with `|x - y|_∞ ≤ L 2^{-n}`:
`D_n(x, y; B_ρ(0)) ≤ √d L 2^{-(1-ξQ+η)n}`. -/
theorem lfppDistOn_le_segment {φ : Rd d → ℝ} (hφ : Continuous φ) {ξ Q η ρ : ℝ} (hξ : 0 < ξ)
    {n : ℕ} (hρ : ρ ≤ 3) (hG : ∀ z ∈ cbox (0 : Rd d) 3, φ z ≤ n * (Q - η / ξ) * Real.log 2)
    {x y : Rd d} (hx : x ∈ obox (0 : Rd d) ρ) (hy : y ∈ obox (0 : Rd d) ρ) {L : ℝ}
    (hxy : ∀ i, |y i - x i| ≤ L * (2 : ℝ)⁻¹ ^ n) :
    lfppDistOn ξ φ (obox (0 : Rd d) ρ) x y ≤ √(d : ℝ) * L * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n) := by
  have hM : ∀ z ∈ obox (0 : Rd d) ρ, ξ * φ z ≤ ξ * (n * (Q - η / ξ) * Real.log 2) := fun z hz =>
    mul_le_mul_of_nonneg_left (hG z (obox_zero_subset_cbox_three hρ hz)) hξ.le
  have h1 := lfppDistOn_le_exp_mul_norm_of_convex hφ (convex_obox (0 : Rd d) ρ) hx hy hM
  rw [exp_eq_two_rpow hξ n] at h1
  have hnorm := norm_sub_le_of_forall_abs_le hxy
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ ((ξ * Q - η) * n) := Real.rpow_nonneg (by norm_num) _
  calc lfppDistOn ξ φ (obox (0 : Rd d) ρ) x y ≤ (2 : ℝ) ^ ((ξ * Q - η) * n) * ‖y - x‖ := h1
    _ ≤ (2 : ℝ) ^ ((ξ * Q - η) * n) * (√(d : ℝ) * (L * (2 : ℝ)⁻¹ ^ n)) :=
        mul_le_mul_of_nonneg_left hnorm h2
    _ = √(d : ℝ) * L * ((2 : ℝ)⁻¹ ^ n * (2 : ℝ) ^ ((ξ * Q - η) * n)) := by ring
    _ = √(d : ℝ) * L * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n) := by rw [inv_two_pow_mul_rpow]

/-- **The half chain** (MA7 D-4.3s, Steps 1–2): for `x ∈ B_ρ(0)` and points `u_ℓ`
(`j ≤ ℓ ≤ n - 1`) as in `exists_chainPoint` relative to the contracted points
`x^{(ℓ)} = (1 - δ_ℓ/ρ) x`, on `𝒢_n` and `ℰ_{k,n}` (`j ≤ k ≤ n - 1`):
`D_n(x, 2^{-j} u_j; B_ρ(0)) ≤ 2002 √d n² 2^{-(1-ξQ+η)n}
  + 2011^d Σ_{k=j+1}^{n-1} k^{2d} 2^{-(1-ξQ+η)k} a_k`. -/
theorem lfppDistOn_le_halfChain (hd : 2 ≤ d) {φ : Rd d → ℝ} (hφ : Continuous φ) {ξ Q η ρ : ℝ}
    (hξ : 0 < ξ) {a : ℕ → ℝ} {j n : ℕ} (hj : 110 ≤ j) (hjn : j < n) (hρ1 : 1 ≤ ρ)
    (hρ2 : ρ ≤ 3 / 2) (hG : ∀ z ∈ cbox (0 : Rd d) 3, φ z ≤ n * (Q - η / ξ) * Real.log 2)
    (hE : ∀ k, j ≤ k → k < n → SmallClusters (mOpen ξ Q η φ k (a k)) (k ^ 2 - 101 ^ 2))
    {x : Rd d} (hx : x ∈ obox (0 : Rd d) ρ) {U : ℕ → Zd d}
    (hU1 : ∀ ℓ, j ≤ ℓ → ℓ < n → FreeSite (mOpen ξ Q η φ ℓ (a ℓ)) (U ℓ))
    (hU2 : ∀ ℓ, j ≤ ℓ → ℓ < n → ∀ i,
      |latPt ((2 : ℝ)⁻¹ ^ ℓ) (U ℓ) i - (1 - chainDelta ℓ / ρ) * x i| ≤
        (ℓ : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ ℓ)
    (hU3 : ∀ ℓ, j ≤ ℓ → ℓ + 1 < n → FreeSite (mOpen ξ Q η φ (ℓ + 1) (a (ℓ + 1))) (2 • U ℓ)) :
    lfppDistOn ξ φ (obox (0 : Rd d) ρ) x (latPt ((2 : ℝ)⁻¹ ^ j) (U j)) ≤
      2002 * √(d : ℝ) * (n : ℝ) ^ 2 * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n) +
        (2011 : ℝ) ^ d * ∑ k ∈ Finset.Ico (j + 1) n,
          (k : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * k) * a k := by
  set V : Set (Rd d) := obox (0 : Rd d) ρ with hV
  set X : ℕ → Rd d := fun ℓ => latPt ((2 : ℝ)⁻¹ ^ ℓ) (U ℓ) with hX
  set f : ℕ → ℝ := fun k => (k : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * k) * a k with hf
  have hxi : ∀ i, |x i| < ρ := fun i => by
    have := hx i
    rwa [PiLp.zero_apply, sub_zero] at this
  -- location of the points
  have hXabs : ∀ ℓ, j ≤ ℓ → ℓ < n → ∀ i,
      |X ℓ i| ≤ ρ - chainDelta ℓ + (ℓ : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ ℓ := by
    intro ℓ h1 h2 i
    have e1 : |X ℓ i - (1 - chainDelta ℓ / ρ) * x i| ≤ (ℓ : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ ℓ :=
      hU2 ℓ h1 h2 i
    have e2 := abs_contract_le hρ1 (chainDelta_le_one (by omega : 20 ≤ ℓ)) (hxi i)
    have e3 := abs_sub_abs_le_abs_sub (X ℓ i) ((1 - chainDelta ℓ / ρ) * x i)
    linarith
  have hXabs' : ∀ ℓ, j ≤ ℓ → ℓ < n → ∀ i,
      |X ℓ i| ≤ ρ - 999 * (ℓ : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ ℓ := by
    intro ℓ h1 h2 i
    have := hXabs ℓ h1 h2 i
    unfold chainDelta at this
    linarith
  have hXV : ∀ ℓ, j ≤ ℓ → ℓ < n → X ℓ ∈ V := fun ℓ h1 h2 i => by
    rw [PiLp.zero_apply, sub_zero]
    have := hXabs' ℓ h1 h2 i
    have hpos : 0 < 999 * (ℓ : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ ℓ := by
      have : (1 : ℝ) ≤ ℓ := by exact_mod_cast (by omega : 1 ≤ ℓ)
      positivity
    linarith
  -- Step 1: the segment from `x` to `X (n - 1)`
  have hjN : j ≤ n - 1 := by omega
  have hN1 : n - 1 + 1 = n := by omega
  have hseg : lfppDistOn ξ φ V x (X (n - 1)) ≤
      2002 * √(d : ℝ) * (n : ℝ) ^ 2 * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n) := by
    have hcoord : ∀ i, |X (n - 1) i - x i| ≤ (2002 * (n : ℝ) ^ 2) * (2 : ℝ)⁻¹ ^ n := by
      intro i
      have e1 : |X (n - 1) i - (1 - chainDelta (n - 1) / ρ) * x i| ≤
          ((n - 1 : ℕ) : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ (n - 1) := hU2 (n - 1) hjN (by omega) i
      have e2 := abs_sub_contract_le hρ1 (chainDelta_nonneg (n - 1)) (hxi i)
      have e3 := abs_sub_le (X (n - 1) i) ((1 - chainDelta (n - 1) / ρ) * x i) (x i)
      rw [abs_sub_comm (x i)] at e2
      have hbd : ((n - 1 : ℕ) : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ (n - 1) + chainDelta (n - 1) ≤
          (2002 * (n : ℝ) ^ 2) * (2 : ℝ)⁻¹ ^ n := by
        have hε : (2 : ℝ)⁻¹ ^ (n - 1) = 2 * (2 : ℝ)⁻¹ ^ n := by
          have : (2 : ℝ)⁻¹ ^ n = (2 : ℝ)⁻¹ ^ (n - 1) * 2⁻¹ := by
            rw [← pow_succ, hN1]
          rw [this]; ring
        have hsq : ((n - 1 : ℕ) : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
          gcongr
          exact_mod_cast Nat.sub_le n 1
        unfold chainDelta
        rw [hε]
        calc ((n - 1 : ℕ) : ℝ) ^ 2 * (2 * (2 : ℝ)⁻¹ ^ n) +
              1000 * ((n - 1 : ℕ) : ℝ) ^ 2 * (2 * (2 : ℝ)⁻¹ ^ n)
            = 2002 * ((n - 1 : ℕ) : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ n := by ring
          _ ≤ 2002 * (n : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ n := by gcongr
      linarith
    have h := lfppDistOn_le_segment hφ hξ (by linarith : ρ ≤ 3) hG hx (hXV (n - 1) hjN (by omega))
      hcoord
    calc lfppDistOn ξ φ V x (X (n - 1))
        ≤ √(d : ℝ) * (2002 * (n : ℝ) ^ 2) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n) := h
      _ = 2002 * √(d : ℝ) * (n : ℝ) ^ 2 * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n) := by ring
  -- Step 2: the links between consecutive scales
  have hlink : ∀ ℓ, j ≤ ℓ → ℓ + 1 < n →
      lfppDistOn ξ φ V (X ℓ) (X (ℓ + 1)) ≤ (2011 : ℝ) ^ d * f (ℓ + 1) := by
    intro ℓ h1 h2
    have hℓ3 : 3 ≤ ℓ := by omega
    set s : ℝ := (2 : ℝ)⁻¹ ^ (ℓ + 1) with hs_def
    have hs : 0 < s := by positivity
    have hsℓ : (2 : ℝ)⁻¹ ^ ℓ = 2 * s := by rw [hs_def, inv_two_pow_succ']; ring
    have hlat : latPt s (2 • U ℓ) = X ℓ := latPt_two_smul ℓ (U ℓ)
    have hℓ' : (110 : ℝ) ≤ ℓ := by exact_mod_cast (le_trans hj h1)
    have hk' : ((ℓ + 1 : ℕ) : ℝ) = (ℓ : ℝ) + 1 := by push_cast; ring
    have huv : ∀ i, |latPt s (U (ℓ + 1)) i - latPt s (2 • U ℓ) i| ≤
        1003 * ((ℓ + 1 : ℕ) : ℝ) ^ 2 * s := by
      intro i
      rw [hlat]
      show |X (ℓ + 1) i - X ℓ i| ≤ 1003 * ((ℓ + 1 : ℕ) : ℝ) ^ 2 * s
      have e1 : |X (ℓ + 1) i - (1 - chainDelta (ℓ + 1) / ρ) * x i| ≤
          ((ℓ + 1 : ℕ) : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ (ℓ + 1) := hU2 (ℓ + 1) (by omega) h2 i
      have e2 : |X ℓ i - (1 - chainDelta ℓ / ρ) * x i| ≤ (ℓ : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ ℓ :=
        hU2 ℓ h1 (by omega) i
      have e3 := abs_contract_sub_contract_le hρ1 (chainDelta_succ_le hℓ3) (hxi i)
      have e4 := chainDelta_sub_succ_le ℓ
      have e5 := abs_sub_le (X (ℓ + 1) i) ((1 - chainDelta (ℓ + 1) / ρ) * x i) (X ℓ i)
      have e6 := abs_sub_le ((1 - chainDelta (ℓ + 1) / ρ) * x i)
        ((1 - chainDelta ℓ / ρ) * x i) (X ℓ i)
      rw [abs_sub_comm ((1 - chainDelta (ℓ + 1) / ρ) * x i) ((1 - chainDelta ℓ / ρ) * x i),
        abs_sub_comm ((1 - chainDelta ℓ / ρ) * x i) (X ℓ i)] at e6
      rw [hsℓ] at e2
      rw [← hs_def] at e1 e4
      rw [hk'] at e1 ⊢
      have e7 : (ℓ : ℝ) ^ 2 * (2 * s) ≤ 2 * ((ℓ : ℝ) + 1) ^ 2 * s := by
        have : (ℓ : ℝ) ^ 2 ≤ ((ℓ : ℝ) + 1) ^ 2 := by nlinarith
        nlinarith
      linarith
    have hmu : ∀ i, |latPt s (U (ℓ + 1)) i| ≤ ρ - (((ℓ + 1 : ℕ) : ℝ) ^ 2 + 3) * s := by
      intro i
      show |X (ℓ + 1) i| ≤ ρ - (((ℓ + 1 : ℕ) : ℝ) ^ 2 + 3) * s
      have e1 := hXabs (ℓ + 1) (by omega) h2 i
      unfold chainDelta at e1
      rw [← hs_def] at e1
      have hK : (1 : ℝ) ≤ ((ℓ + 1 : ℕ) : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ ((ℓ + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ ℓ + 1)
        nlinarith
      have := mul_le_mul_of_nonneg_right hK hs.le
      linarith
    have hmv : ∀ i, |latPt s (2 • U ℓ) i| ≤ ρ - (((ℓ + 1 : ℕ) : ℝ) ^ 2 + 3) * s := by
      intro i
      rw [hlat]
      have e1 := hXabs' ℓ h1 (by omega) i
      rw [hsℓ] at e1
      rw [hk']
      have hpoly : ((ℓ : ℝ) + 1) ^ 2 + 3 ≤ 1998 * (ℓ : ℝ) ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_right hpoly hs.le
      linarith
    have hL := lfppDistOn_le_link (by omega : 1 ≤ d) hφ (by omega : 1 ≤ ℓ + 1)
      (by linarith : ρ ≤ 2) (hE (ℓ + 1) (by omega) h2) (hU1 (ℓ + 1) (by omega) h2) (hU3 ℓ h1 h2)
      huv hmu hmv
    rw [hlat, lfppDistOn_comm] at hL
    exact hL
  -- the sum over the scales `j < k < n`
  have hchain : lfppDistOn ξ φ V (X j) (X (n - 1)) ≤
      (2011 : ℝ) ^ d * ∑ k ∈ Finset.Ico (j + 1) n, f k := by
    have hsum := lfppDistOn_le_sum (ζ := ξ) hφ (fun i => X (j + i)) (fun _ => V)
      (fun _ => subset_rfl) (n - 1 - j) (fun i hi =>
        PcwJoined.of_convex (convex_obox (0 : Rd d) ρ) (hXV (j + i) (by omega) (by omega))
          (hXV (j + (i + 1)) (by omega) (by omega)))
    have eN : j + (n - 1 - j) = n - 1 := by omega
    simp only [Nat.add_zero, eN] at hsum
    rw [Finset.mul_sum, Finset.sum_Ico_eq_sum_range, show n - (j + 1) = n - 1 - j by omega]
    refine hsum.trans (Finset.sum_le_sum fun i hi => ?_)
    rw [Finset.mem_range] at hi
    have := hlink (j + i) (by omega) (by omega)
    rw [show j + (i + 1) = j + i + 1 by omega, show j + 1 + i = j + i + 1 by omega]
    exact this
  calc lfppDistOn ξ φ V x (X j)
      ≤ lfppDistOn ξ φ V x (X (n - 1)) + lfppDistOn ξ φ V (X (n - 1)) (X j) :=
        lfppDistOn_triangle hφ (PcwJoined.of_convex (convex_obox (0 : Rd d) ρ) hx
          (hXV (n - 1) hjN (by omega)))
          (PcwJoined.of_convex (convex_obox (0 : Rd d) ρ) (hXV (n - 1) hjN (by omega))
            (hXV j le_rfl hjn))
    _ ≤ _ := by
        rw [lfppDistOn_comm ξ φ V (X (n - 1)) (X j)]
        exact add_le_add hseg hchain

/-! ### Self-internal chaining (MA7 D-4.3s (i), (ii)) -/

/-- **Props 4.3^s and 4.5^s** (MA7 D-4.3s (i), (ii); deterministic on `𝒜_{r,n}`): there is
`C = C(d) > 0` such that for `ξ > 0`, all `Q, η, q`, integers `110 ≤ r < n`, `ρ ∈ [1, 3/2]` and
every `ω ∈ 𝒜_{r,n}` with `h_n = H n · ω` continuous:
* (i) `D_n(x, y; B_ρ(0)) ≤ C · chainSum j n` for all `x, y ∈ B_ρ(0)` with `|x - y|_∞ ≤ 2^{-j}`,
  `r ≤ j ≤ n`;
* (ii) `selfDiam_n(B_ρ(0)) = Diam_n(B_ρ(0); B_ρ(0)) ≤ C 2^r · chainSum r n`,

where `chainSum j n = Σ_{k=j}^{n-1} k^{2d} 2^{-(1-ξQ+η)k} a^{(q)}_{n-k} + n^{2d} 2^{-(1-ξQ+η)n}`. -/
theorem chain_selfInternal (hd : 2 ≤ d) : ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (H : ℕ → Rd d → Ω → ℝ) (ξ Q η : ℝ)
      (q : ℝ≥0∞) (r n : ℕ) (ρ : ℝ) (ω : Ω), 0 < ξ → 110 ≤ r → r < n → 1 ≤ ρ → ρ ≤ 3 / 2 →
      Continuous (fun z => H n z ω) → ω ∈ eventA P H ξ Q η q r n →
      (∀ j : ℕ, r ≤ j → j ≤ n → ∀ x ∈ obox (0 : Rd d) ρ, ∀ y ∈ obox (0 : Rd d) ρ,
        (∀ i, |x i - y i| ≤ (2 : ℝ)⁻¹ ^ j) →
        lfppDistOn ξ (fun z => H n z ω) (obox (0 : Rd d) ρ) x y ≤
          C * chainSum P H ξ Q η q j n) ∧
      selfDiam ξ (fun z => H n z ω) 0 ρ ≤ C * 2 ^ r * chainSum P H ξ Q η q r n := by
  set C₀ : ℝ := 2 * (2011 : ℝ) ^ d + 4004 * √(d : ℝ) with hC₀_def
  have hC₀ : 0 < C₀ := by positivity
  refine ⟨3 * C₀, by positivity, ?_⟩
  intro Ω _ P H ξ Q η q r n ρ ω hξ hr hrn hρ1 hρ2 hφ hω
  set φ : Rd d → ℝ := fun z => H n z ω with hφ_def
  set a : ℕ → ℝ := fun k => aQ P H ξ (n - k) q with ha_def
  obtain ⟨hG, hF⟩ := mem_eventA_iff.1 hω
  have hE : ∀ k, r ≤ k → k < n → SmallClusters (mOpen ξ Q η φ k (a k)) (k ^ 2 - 101 ^ 2) :=
    fun k h1 h2 => (hF k h1 h2).1.1
  have hF3 : ∀ ℓ, r ≤ ℓ → ℓ + 1 < n → ∀ x ∈ latRegion (ℓ + 1), ∃ y : Zd d,
      WithinInf (((ℓ + 1 : ℕ) : ℤ) ^ 2) x (2 • y) ∧
      FreeSite (mOpen ξ Q η φ (ℓ + 1) (a (ℓ + 1))) (2 • y) ∧
      FreeSite (mOpen ξ Q η φ ℓ (a ℓ)) y := by
    intro ℓ h1 h2 x hx
    have := (hF (ℓ + 1) (by omega) h2).2 x hx
    simpa only [Nat.add_sub_cancel] using this
  -- the points of the chaining, for every point `w` of `B_ρ(0)` and every scale
  have hpts : ∀ w : Rd d, ∀ ℓ : ℕ, ∃ u : Zd d, w ∈ obox (0 : Rd d) ρ → r ≤ ℓ → ℓ < n →
      FreeSite (mOpen ξ Q η φ ℓ (a ℓ)) u ∧
      (∀ i, |latPt ((2 : ℝ)⁻¹ ^ ℓ) u i - (1 - chainDelta ℓ / ρ) * w i| ≤
        (ℓ : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ ℓ) ∧
      (ℓ + 1 < n → FreeSite (mOpen ξ Q η φ (ℓ + 1) (a (ℓ + 1))) (2 • u)) := by
    intro w ℓ
    by_cases h : w ∈ obox (0 : Rd d) ρ ∧ r ≤ ℓ ∧ ℓ < n
    · obtain ⟨hw, h1, h2⟩ := h
      have hw' : ∀ i, |((1 - chainDelta ℓ / ρ) • w) i| < 2 := fun i => by
        rw [PiLp.smul_apply, smul_eq_mul]
        have hwi : |w i| < ρ := by
          have := hw i
          rwa [PiLp.zero_apply, sub_zero] at this
        have := abs_contract_le hρ1 (chainDelta_le_one (by omega : 20 ≤ ℓ)) hwi
        have := chainDelta_nonneg ℓ
        linarith
      obtain ⟨u, hu1, hu2, hu3⟩ := exists_chainPoint hd (by omega : 110 ≤ ℓ) h2 (hE ℓ h1 h2)
        (fun h' => hF3 ℓ h1 h') hw'
      refine ⟨u, fun _ _ _ => ⟨hu1, fun i => ?_, hu3⟩⟩
      have := hu2 i
      rwa [PiLp.smul_apply, smul_eq_mul] at this
    · exact ⟨0, fun hw h1 h2 => absurd ⟨hw, h1, h2⟩ h⟩
  choose U hU using hpts
  -- the levels `a_k = a^{(q)}_{n-k}`, `r ≤ k < n`, are nonnegative on `𝒜_{r,n}`
  have hzero : (0 : Rd d) ∈ obox (0 : Rd d) ρ := mem_obox_self 0 (by linarith)
  have ha : ∀ k, r ≤ k → k < n → 0 ≤ a k := by
    intro k h1 h2
    obtain ⟨hu1, hu2, -⟩ := hU 0 k hzero h1 h2
    refine nonneg_of_mem_mOpen (by omega) hu1.1 ((mem_latRegion_iff_mem_obox k _).2 fun i => ?_)
    rw [PiLp.zero_apply, sub_zero]
    have e1 := hu2 i
    rw [PiLp.zero_apply, mul_zero, sub_zero] at e1
    have e2 := chainDelta_le_one (by omega : 20 ≤ k)
    unfold chainDelta at e2
    have : 0 ≤ (k : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ k := by positivity
    linarith
  have hcs : ∀ j, r ≤ j → 0 ≤ chainSum P H ξ Q η q j n := by
    intro j hj
    unfold chainSum
    refine add_nonneg (Finset.sum_nonneg fun k hk => ?_) (by positivity)
    rw [Finset.mem_Ico] at hk
    exact mul_nonneg (by positivity) (ha k (by omega) hk.2)
  -- (i)
  have hi : ∀ j : ℕ, r ≤ j → j ≤ n → ∀ x ∈ obox (0 : Rd d) ρ, ∀ y ∈ obox (0 : Rd d) ρ,
      (∀ i, |x i - y i| ≤ (2 : ℝ)⁻¹ ^ j) →
      lfppDistOn ξ φ (obox (0 : Rd d) ρ) x y ≤ C₀ * chainSum P H ξ Q η q j n := by
    intro j hrj hjn x hx y hy hxy
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hT0 : 0 ≤ (2 : ℝ) ^ (-(1 - ξ * Q + η) * n) := by positivity
    have hpow : (1 : ℝ) ≤ (n : ℝ) ^ (2 * d) := one_le_pow₀ hn1
    have hsq : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (2 * d) := pow_le_pow_right₀ hn1 (by omega)
    have hsqrt : 0 ≤ √(d : ℝ) := Real.sqrt_nonneg _
    have hA : (0 : ℝ) ≤ (2011 : ℝ) ^ d := by positivity
    rcases eq_or_lt_of_le hjn with hjn' | hjn'
    · -- `j = n`: the segment
      rw [hjn'] at hxy ⊢
      have h := lfppDistOn_le_segment (L := 1) hφ hξ (by linarith : ρ ≤ 3) hG hx hy
        (fun i => by rw [abs_sub_comm, one_mul]; exact hxy i)
      have hcs_eq : chainSum P H ξ Q η q n n =
          (n : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n) := by
        simp [chainSum]
      rw [hcs_eq]
      have e1 : √(d : ℝ) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n) ≤
          √(d : ℝ) * ((n : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n)) := by
        have : (2 : ℝ) ^ (-(1 - ξ * Q + η) * n) ≤
            (n : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n) := by nlinarith
        exact mul_le_mul_of_nonneg_left this hsqrt
      have e2 : 0 ≤ (2011 : ℝ) ^ d * ((n : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n)) := by
        positivity
      have e3 : 0 ≤ √(d : ℝ) * ((n : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n)) := by
        positivity
      rw [hC₀_def]
      nlinarith
    · -- `j < n`: two half chains and the middle link at scale `j`
      have hj110 : 110 ≤ j := by omega
      have hEj : ∀ k, j ≤ k → k < n → SmallClusters (mOpen ξ Q η φ k (a k)) (k ^ 2 - 101 ^ 2) :=
        fun k h1 h2 => hE k (by omega) h2
      have hX := lfppDistOn_le_halfChain hd hφ hξ hj110 hjn' hρ1 hρ2 hG hEj hx (U := U x)
        (fun ℓ h1 h2 => (hU x ℓ hx (by omega) h2).1)
        (fun ℓ h1 h2 => (hU x ℓ hx (by omega) h2).2.1)
        (fun ℓ h1 h2 => (hU x ℓ hx (by omega) (by omega)).2.2 h2)
      have hY := lfppDistOn_le_halfChain hd hφ hξ hj110 hjn' hρ1 hρ2 hG hEj hy (U := U y)
        (fun ℓ h1 h2 => (hU y ℓ hy (by omega) h2).1)
        (fun ℓ h1 h2 => (hU y ℓ hy (by omega) h2).2.1)
        (fun ℓ h1 h2 => (hU y ℓ hy (by omega) (by omega)).2.2 h2)
      obtain ⟨hux1, hux2, -⟩ := hU x j hx hrj hjn'
      obtain ⟨huy1, huy2, -⟩ := hU y j hy hrj hjn'
      set s : ℝ := (2 : ℝ)⁻¹ ^ j with hs_def
      have hs : 0 < s := by positivity
      have hxi : ∀ i, |x i| < ρ := fun i => by
        have := hx i
        rwa [PiLp.zero_apply, sub_zero] at this
      have hyi : ∀ i, |y i| < ρ := fun i => by
        have := hy i
        rwa [PiLp.zero_apply, sub_zero] at this
      have hδ1 := chainDelta_le_one (by omega : 20 ≤ j)
      have hδ0 := chainDelta_nonneg j
      have hj1 : (1 : ℝ) ≤ (j : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ j := by exact_mod_cast (by omega : 1 ≤ j)
        nlinarith
      have hloc : ∀ (w : Rd d) (u : Zd d), (∀ i, |w i| < ρ) →
          (∀ i, |latPt s u i - (1 - chainDelta j / ρ) * w i| ≤ (j : ℝ) ^ 2 * s) →
          ∀ i, |latPt s u i| ≤ ρ - ((j : ℝ) ^ 2 + 3) * s := by
        intro w u hw hu i
        have e1 := hu i
        have e2 := abs_contract_le hρ1 hδ1 (hw i)
        have e3 := abs_sub_abs_le_abs_sub (latPt s u i) ((1 - chainDelta j / ρ) * w i)
        have hδ : chainDelta j = 1000 * (j : ℝ) ^ 2 * s := by rw [hs_def]; rfl
        have := mul_le_mul_of_nonneg_right hj1 hs.le
        linarith
      have hmid := lfppDistOn_le_link (by omega : 1 ≤ d) hφ (by omega : 1 ≤ j)
        (by linarith : ρ ≤ 2) (hE j hrj hjn') hux1 huy1 (fun i => by
          show |latPt s (U x j) i - latPt s (U y j) i| ≤ 1003 * (j : ℝ) ^ 2 * s
          have e1 := hux2 i
          have e2 := huy2 i
          have e3 := abs_contract_sub_le hρ1 hδ0 hδ1 (t := x i) (t' := y i)
          have e4 := abs_sub_le (latPt s (U x j) i) ((1 - chainDelta j / ρ) * x i)
            (latPt s (U y j) i)
          have e5 := abs_sub_le ((1 - chainDelta j / ρ) * x i) ((1 - chainDelta j / ρ) * y i)
            (latPt s (U y j) i)
          rw [abs_sub_comm ((1 - chainDelta j / ρ) * y i)] at e5
          have e6 := hxy i
          have := mul_le_mul_of_nonneg_right hj1 hs.le
          linarith)
        (hloc x (U x j) hxi hux2) (hloc y (U y j) hyi huy2)
      have hXV : latPt s (U x j) ∈ obox (0 : Rd d) ρ := fun i => by
        rw [PiLp.zero_apply, sub_zero]
        have := hloc x (U x j) hxi hux2 i
        have : 0 < ((j : ℝ) ^ 2 + 3) * s := by positivity
        linarith
      have hYV : latPt s (U y j) ∈ obox (0 : Rd d) ρ := fun i => by
        rw [PiLp.zero_apply, sub_zero]
        have := hloc y (U y j) hyi huy2 i
        have : 0 < ((j : ℝ) ^ 2 + 3) * s := by positivity
        linarith
      have htri : lfppDistOn ξ φ (obox (0 : Rd d) ρ) x y ≤
          lfppDistOn ξ φ (obox (0 : Rd d) ρ) x (latPt s (U x j)) +
            (lfppDistOn ξ φ (obox (0 : Rd d) ρ) (latPt s (U x j)) (latPt s (U y j)) +
              lfppDistOn ξ φ (obox (0 : Rd d) ρ) y (latPt s (U y j))) := by
        have hc := convex_obox (0 : Rd d) ρ
        refine (lfppDistOn_triangle hφ (PcwJoined.of_convex hc hx hXV)
          (PcwJoined.of_convex hc hXV hy)).trans (add_le_add (le_refl _) ?_)
        rw [lfppDistOn_comm ξ φ _ y (latPt s (U y j))]
        exact lfppDistOn_triangle hφ (PcwJoined.of_convex hc hXV hYV)
          (PcwJoined.of_convex hc hYV hy)
      -- the arithmetic
      set f : ℕ → ℝ := fun k => (k : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * k) * a k
        with hf
      set G : ℝ := ∑ k ∈ Finset.Ico (j + 1) n, f k with hG_def
      set S : ℝ := (n : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n) with hS_def
      have hcs_eq : chainSum P H ξ Q η q j n = f j + G + S := by
        rw [chainSum, Finset.sum_eq_sum_Ico_succ_bot hjn']
      have hF0 : 0 ≤ f j := mul_nonneg (by positivity) (ha j hrj hjn')
      have hG0 : 0 ≤ G := Finset.sum_nonneg fun k hk => by
        rw [Finset.mem_Ico] at hk
        exact mul_nonneg (by positivity) (ha k (by omega) hk.2)
      have hS0 : 0 ≤ S := by positivity
      have hTS : (n : ℝ) ^ 2 * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n) ≤ S :=
        mul_le_mul_of_nonneg_right hsq hT0
      have hmid' : lfppDistOn ξ φ (obox (0 : Rd d) ρ) (latPt s (U x j)) (latPt s (U y j)) ≤
          (2011 : ℝ) ^ d * f j := hmid
      rw [hcs_eq, hC₀_def]
      have k1 := mul_nonneg hA hF0
      have k2 := mul_nonneg hA hS0
      have k3 := mul_nonneg hsqrt hF0
      have k4 := mul_nonneg hsqrt hG0
      have k5 := mul_le_mul_of_nonneg_left hTS hsqrt
      have k6 : 2002 * √(d : ℝ) * (n : ℝ) ^ 2 * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n) =
          2002 * (√(d : ℝ) * ((n : ℝ) ^ 2 * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n))) := by ring
      rw [k6] at hX hY
      nlinarith
  -- (ii): split the segment `[x, y]` into `3 · 2^r` pieces and apply (i) with `j = r`
  have hii : selfDiam ξ φ 0 ρ ≤ 3 * 2 ^ r * C₀ * chainSum P H ξ Q η q r n := by
    have hcsr := hcs r le_rfl
    refine selfDiam_le (by positivity) fun x hx y hy => ?_
    set N : ℕ := 3 * 2 ^ r with hN
    have hN0 : (0 : ℝ) < N := by positivity
    set v : ℕ → Rd d := fun t => x + ((t : ℝ) / N) • (y - x) with hv
    have hvV : ∀ t ≤ N, v t ∈ obox (0 : Rd d) ρ := fun t ht =>
      (convex_obox (0 : Rd d) ρ).add_smul_sub_mem hx hy
        ⟨by positivity, by rw [div_le_one hN0]; exact_mod_cast ht⟩
    have hsum := lfppDistOn_le_sum (ζ := ξ) hφ v (fun _ => obox (0 : Rd d) ρ)
      (fun _ => subset_rfl) N (fun t ht =>
        PcwJoined.of_convex (convex_obox (0 : Rd d) ρ) (hvV t ht.le) (hvV (t + 1) ht))
    have hv0 : v 0 = x := by simp [hv]
    have hvN : v N = y := by
      simp only [hv]
      rw [div_self hN0.ne', one_smul, add_sub_cancel]
    rw [hv0, hvN] at hsum
    refine hsum.trans ?_
    have hterm : ∀ t ∈ Finset.range N,
        lfppDistOn ξ φ (obox (0 : Rd d) ρ) (v t) (v (t + 1)) ≤
          C₀ * chainSum P H ξ Q η q r n := by
      intro t ht
      rw [Finset.mem_range] at ht
      refine hi r le_rfl hrn.le (v t) (hvV t ht.le) (v (t + 1)) (hvV (t + 1) ht) fun i => ?_
      simp only [hv, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      have e : x i + (t : ℝ) / N * (y i - x i) - (x i + ((t + 1 : ℕ) : ℝ) / N * (y i - x i)) =
          -((y i - x i) / N) := by
        push_cast
        field_simp
        ring
      rw [e, abs_neg, abs_div, abs_of_pos hN0, div_le_iff₀ hN0]
      have hxi : |x i| < ρ := by
        have := hx i
        rwa [PiLp.zero_apply, sub_zero] at this
      have hyi : |y i| < ρ := by
        have := hy i
        rwa [PiLp.zero_apply, sub_zero] at this
      have e2 : (2 : ℝ)⁻¹ ^ r * N = 3 := by
        rw [hN]
        push_cast
        rw [inv_pow]
        field_simp
      have e3 := abs_sub (y i) (x i)
      rw [e2]
      linarith
    calc ∑ t ∈ Finset.range N, lfppDistOn ξ φ (obox (0 : Rd d) ρ) (v t) (v (t + 1))
        ≤ ∑ _t ∈ Finset.range N, C₀ * chainSum P H ξ Q η q r n := Finset.sum_le_sum hterm
      _ = 3 * 2 ^ r * C₀ * chainSum P H ξ Q η q r n := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hN]
        push_cast
        ring
  refine ⟨fun j h1 h2 x hx y hy hxy => (hi j h1 h2 x hx y hy hxy).trans ?_, ?_⟩
  · have := hcs j h1
    nlinarith
  · calc selfDiam ξ φ 0 ρ ≤ 3 * 2 ^ r * C₀ * chainSum P H ξ Q η q r n := hii
      _ = 3 * C₀ * 2 ^ r * chainSum P H ξ Q η q r n := by ring

end DGZ

end HigherDimLQGMetric
