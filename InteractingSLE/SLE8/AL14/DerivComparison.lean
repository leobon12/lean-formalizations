import QuantumZipper.Proofs.RS.KoebeLoewnerTime

/-!
# [AL14] Lemma 1: the deterministic derivative comparison (SLE₈ note, proof of Lemma 2.1)

Sources: Alvisio–Lawler [AL14], `source/external/AL14/AL14.md` (anchors `lem-1`, `lem-1-proof`,
`id-Dn`, p. 4); the SLE₈ note `source/sle8-continuity.pdf`, proof of Lemma 2.1 (anchor
`lem-2.1-proof`, PDF pp. 2–3, displays (2.2)–(2.3)): "Lemma 1 and the definitions following it in
[AL14] give `D̂_k ≤ c D_k^*`". [AL14] cites [JVL12] (Lemma 2.2, Proposition 2.3 (2.7), and the proof
of Proposition 2.5); see `planning/handoffs/SRC-JVL.md` §4.5.

## Normalization

QuantumZipper's Loewner chain has `∂_t g_t = 2/(g_t − W_t)` and `fwdMapInv W t w = g_t⁻¹(W_t + w)`.
[AL14] uses `∂_t ḡ_t = (1/4)/(ḡ_t − U_t)`. With `W = √8 U` one has `ḡ_t(z) = g_t(√8 z)/√8` (the
note's renormalization, with `U = B`), hence `F̄_t(z) = ḡ_t⁻¹(U_t + z) = F_t(√8 z)/√8`; this is
`barInv U t z`. The heights are `y_k = 2^{-k}` (`alHeight k`), the grid times `j y_k²`
(`alTime k j`).

## Exponent

QuantumZipper's Koebe distortion is not sharp, so the printed `Δ⁴` becomes `Δ^p` for every
`p ≥ alExp = 4m + 1`, `m = ⌈koebeDistExp⌉₊` (`RS.kdNatExp`). The constant `c` is universal (it
does not depend on the driver, on `k`, `j`, `s`, or `p`). The downstream use ([AL14] Theorem 2)
holds for any fixed power of `Δ` (`planning/handoffs/SRC-EXT-S8.md`, "Robustness").

## Main results

* `exists_deriv_comparison`: the comparison in QuantumZipper's normalization at an arbitrary
  height `Y` and time step `s ≤ Y²`, for any `Δ ≥ 1` dominating the driver displacement.
* `exists_lemma_one`: [AL14] Lemma 1 (both derivative inequalities and the increment bound).
* `exists_norm_deriv_barInv_le_derivGridMaxStar`, `exists_derivSup_le_derivGridMaxStar`:
  `D̂_k ≤ c D_k^*` (pointwise in `t ∈ [0, 1]`, and for the supremum, with `BddAbove`).
* `exists_norm_barInv_sub_le_derivGridMaxStar`: `Θ_k ≤ c 2^{-k} D_k^*` (pointwise form).
-/

noncomputable section

open Complex Set
open QuantumZipper

namespace InteractingSLE.SLE8.AL14

/-! ## Horizontal distortion with an explicit exponent -/

/-- The exponent `4m`, `m = ⌈koebeDistExp⌉₊`, of the horizontal distortion bound
`norm_deriv_horiz_le`. -/
def horizExp : ℕ := 4 * RS.kdNatExp

/-- The constant `64^m`, `m = ⌈koebeDistExp⌉₊`, of the horizontal distortion bound
`norm_deriv_horiz_le`. -/
def horizConst : ℝ := 64 ^ RS.kdNatExp

theorem one_le_horizConst : 1 ≤ horizConst := one_le_pow₀ (by norm_num)

/-- The Koebe factor `K^{4n+2}` of `RS.deriv_ratio_le_full` is at most `64^m (1 + |x|)^{4m}` when
`2^n ≤ 2(1 + |x|)`. -/
theorem koebeStepConst_pow_le {x : ℝ} {n : ℕ} (hn : (2 : ℝ) ^ n ≤ 2 * (1 + |x|)) :
    RS.koebeStepConst ^ (4 * n + 2) ≤ horizConst * (1 + |x|) ^ horizExp := by
  have hK0 : 0 ≤ RS.koebeStepConst := le_trans zero_le_one RS.one_le_koebeStepConst
  have h1 : ((2 : ℝ) ^ RS.kdNatExp) ^ (4 * n + 2) = (((2 : ℝ) ^ n) ^ 4 * 4) ^ RS.kdNatExp := by
    rw [← pow_mul, show ((2 : ℝ) ^ n) ^ 4 * 4 = 2 ^ (4 * n + 2) by ring, ← pow_mul, mul_comm]
  have h2 : ((2 : ℝ) ^ n) ^ 4 * 4 ≤ 64 * (1 + |x|) ^ 4 := by
    calc ((2 : ℝ) ^ n) ^ 4 * 4 ≤ (2 * (1 + |x|)) ^ 4 * 4 := by gcongr
      _ = 64 * (1 + |x|) ^ 4 := by ring
  calc RS.koebeStepConst ^ (4 * n + 2) ≤ ((2 : ℝ) ^ RS.kdNatExp) ^ (4 * n + 2) :=
        pow_le_pow_left₀ hK0 RS.koebeStepConst_le_two_pow _
    _ = (((2 : ℝ) ^ n) ^ 4 * 4) ^ RS.kdNatExp := h1
    _ ≤ (64 * (1 + |x|) ^ 4) ^ RS.kdNatExp := pow_le_pow_left₀ (by positivity) h2 _
    _ = horizConst * (1 + |x|) ^ horizExp := by
        rw [mul_pow, ← pow_mul]
        rfl

/-- **Horizontal distortion** (non-sharp form of [JVL12] (2.7)): for `f` univalent on `ℍ`,
`|f'(y(x+i))|` and `|f'(iy)|` agree up to the factor `64^m (1 + |x|)^{4m}`. -/
theorem norm_deriv_horiz_le {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hinj : InjOn f {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    ‖deriv f ((y : ℂ) * ((x : ℂ) + I))‖ ≤
        horizConst * (1 + |x|) ^ horizExp * ‖deriv f ((y : ℂ) * I)‖ ∧
      ‖deriv f ((y : ℂ) * I)‖ ≤
        horizConst * (1 + |x|) ^ horizExp * ‖deriv f ((y : ℂ) * ((x : ℂ) + I))‖ := by
  classical
  obtain ⟨n, hn, hmin⟩ : ∃ n : ℕ, (1 + |x| ≤ (2 : ℝ) ^ n) ∧ ∀ j < n, ¬ (1 + |x| < (2 : ℝ) ^ j) := by
    have hex : ∃ n : ℕ, 1 + |x| < (2 : ℝ) ^ n := pow_unbounded_of_one_lt (1 + |x|) (by norm_num)
    exact ⟨Nat.find hex, (Nat.find_spec hex).le, fun j hj => Nat.find_min hex hj⟩
  obtain ⟨h1, h2⟩ := RS.deriv_ratio_le_full hd hinj hy hn
  have hK := koebeStepConst_pow_le (RS.two_pow_le_of_min hmin)
  exact ⟨h1.trans (mul_le_mul_of_nonneg_right hK (norm_nonneg _)),
    h2.trans (mul_le_mul_of_nonneg_right hK (norm_nonneg _))⟩

/-- A point of the horizontal segment from `iy` to `y(x + i)` is `y(θx + i)` with `θ ∈ [0, 1]`. -/
theorem exists_eq_of_mem_segment_horiz {y x : ℝ} {z : ℂ}
    (hz : z ∈ segment ℝ ((y : ℂ) * I) ((y : ℂ) * ((x : ℂ) + I))) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ z = (y : ℂ) * (((θ * x : ℝ) : ℂ) + I) := by
  rw [segment_eq_image'] at hz
  obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hz
  refine ⟨θ, h0, h1, ?_⟩
  dsimp only
  rw [real_smul]
  push_cast
  ring

/-- **Horizontal increment** (non-sharp form of [JVL12] (2.8)): for `f` univalent on `ℍ`,
`|f(y(x+i)) − f(iy)| ≤ 64^m (1 + |x|)^{4m} |f'(iy)| · y|x|`. -/
theorem norm_sub_horiz_le {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hinj : InjOn f {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    ‖f ((y : ℂ) * ((x : ℂ) + I)) - f ((y : ℂ) * I)‖ ≤
      horizConst * (1 + |x|) ^ horizExp * ‖deriv f ((y : ℂ) * I)‖ * (y * |x|) := by
  have him : ∀ θ : ℝ, 0 < ((y : ℂ) * (((θ * x : ℝ) : ℂ) + I)).im := by
    intro θ
    simpa using hy
  have hdiff : ∀ z ∈ segment ℝ ((y : ℂ) * I) ((y : ℂ) * ((x : ℂ) + I)), DifferentiableAt ℂ f z := by
    intro z hz
    obtain ⟨θ, -, -, rfl⟩ := exists_eq_of_mem_segment_horiz hz
    exact (hd _ (him θ)).differentiableAt
      ((isOpen_lt continuous_const continuous_im).mem_nhds (him θ))
  have hbound : ∀ z ∈ segment ℝ ((y : ℂ) * I) ((y : ℂ) * ((x : ℂ) + I)),
      ‖deriv f z‖ ≤ horizConst * (1 + |x|) ^ horizExp * ‖deriv f ((y : ℂ) * I)‖ := by
    intro z hz
    obtain ⟨θ, h0, h1, rfl⟩ := exists_eq_of_mem_segment_horiz hz
    refine (norm_deriv_horiz_le hd hinj hy (θ * x)).1.trans ?_
    have hθx : |θ * x| ≤ |x| := by
      rw [abs_mul, abs_of_nonneg h0]
      exact mul_le_of_le_one_left (abs_nonneg x) h1
    have hH := one_le_horizConst
    gcongr
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_segment _ _)
    (left_mem_segment _ _ _) (right_mem_segment _ _ _)
  have hn : ‖(y : ℂ) * ((x : ℂ) + I) - (y : ℂ) * I‖ = y * |x| := by
    rw [show (y : ℂ) * ((x : ℂ) + I) - (y : ℂ) * I = ((y * x : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hy]
  rwa [hn] at h

/-! ## The comparison in QuantumZipper's normalization -/

/-- The exponent of `Δ` obtained here for [AL14] Lemma 1 (printed there as `4`):
`alExp = 4m + 1`, `m = ⌈koebeDistExp⌉₊`. Every `p ≥ alExp` works with the same constant. -/
def alExp : ℕ := horizExp + 1

/-- **Derivative comparison, QuantumZipper normalization** ([AL14] Lemma 1, deterministic core;
[JVL12] Lemma 2.2 + (2.7) + the bound in the proof of Proposition 2.5). There is a universal
`c ≥ 1` such that for every continuous driver `W` with `W 0 = 0`, every `t ≥ 0`, height `Y > 0`,
time step `0 ≤ s ≤ Y²`, and every `Δ ≥ 1` with `|W_{t+s} − W_t| ≤ (Δ − 1) Y`, and every `p ≥ alExp`:
`|F_{t+s}'(iY)| ≤ c Δ^p |F_t'(iY)|`, `|F_t'(iY)| ≤ c Δ^p |F_{t+s}'(iY)|` and
`|F_{t+s}(iY) − F_t(iY)| ≤ c Δ^p Y |F_t'(iY)|`, where `F_t = fwdMapInv W t`. -/
theorem exists_deriv_comparison : ∃ c : ℝ, 1 ≤ c ∧ ∀ W : ℝ → ℝ, Continuous W → W 0 = 0 →
    ∀ t s Y Δ : ℝ, 0 ≤ t → 0 ≤ s → 0 < Y → s ≤ Y ^ 2 → 1 ≤ Δ →
      |W (t + s) - W t| ≤ (Δ - 1) * Y → ∀ p : ℕ, alExp ≤ p →
        ‖deriv (fwdMapInv W (t + s)) ((Y : ℂ) * I)‖ ≤
            c * Δ ^ p * ‖deriv (fwdMapInv W t) ((Y : ℂ) * I)‖ ∧
          ‖deriv (fwdMapInv W t) ((Y : ℂ) * I)‖ ≤
            c * Δ ^ p * ‖deriv (fwdMapInv W (t + s)) ((Y : ℂ) * I)‖ ∧
          ‖fwdMapInv W (t + s) ((Y : ℂ) * I) - fwdMapInv W t ((Y : ℂ) * I)‖ ≤
            c * Δ ^ p * Y * ‖deriv (fwdMapInv W t) ((Y : ℂ) * I)‖ := by
  obtain ⟨C, hC1, hC⟩ := RS.kd_time_step
  have hH := one_le_horizConst
  refine ⟨(C + 1) * horizConst, by nlinarith,
    fun W hW hW0 t s Y Δ ht hs hY hsY hΔ hinc p hp => ?_⟩
  set x : ℝ := (W (t + s) - W t) / Y with hx_def
  set w : ℂ := (Y : ℂ) * ((x : ℂ) + I) with hw_def
  have hw_im : w.im = Y := by simp [hw_def]
  have hw_sub : w - ((W (t + s) - W t : ℝ) : ℂ) = (Y : ℂ) * I := by
    have hY0 : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
    rw [hw_def, hx_def]
    push_cast
    field_simp
    ring
  obtain ⟨k1, k2, k3⟩ := hC W hW hW0 t s ht hs w (by rw [hw_im]; exact hY)
    (by rw [hw_im]; exact hsY)
  rw [hw_sub] at k1 k2 k3
  rw [hw_im] at k3
  have hd := RS.differentiableOn_fwdMapInv hW hW0 ht
  have hi := RS.injOn_fwdMapInv hW hW0 ht
  obtain ⟨h1, h2⟩ := norm_deriv_horiz_le hd hi hY x
  have h3 := norm_sub_horiz_le hd hi hY x
  rw [← hw_def] at h1 h2 h3
  have hx : |x| ≤ Δ - 1 := by
    rw [hx_def, abs_div, abs_of_pos hY, div_le_iff₀ hY]
    exact hinc
  have hxΔ : 1 + |x| ≤ Δ := by linarith
  have hΔ0 : 0 ≤ Δ := by linarith
  have hp' : horizExp ≤ p := by
    have : alExp = horizExp + 1 := rfl
    omega
  have hpow : (1 + |x|) ^ horizExp ≤ Δ ^ p :=
    calc (1 + |x|) ^ horizExp ≤ Δ ^ horizExp := pow_le_pow_left₀ (by positivity) hxΔ _
      _ ≤ Δ ^ p := pow_le_pow_right₀ hΔ hp'
  have hpow' : |x| * (1 + |x|) ^ horizExp ≤ Δ ^ p :=
    calc |x| * (1 + |x|) ^ horizExp ≤ Δ * Δ ^ horizExp := by
          gcongr
          linarith
      _ = Δ ^ (horizExp + 1) := (pow_succ' Δ horizExp).symm
      _ ≤ Δ ^ p := pow_le_pow_right₀ hΔ hp
  set A := ‖deriv (fwdMapInv W t) ((Y : ℂ) * I)‖ with hA
  set Bw := ‖deriv (fwdMapInv W t) w‖ with hBw
  set A' := ‖deriv (fwdMapInv W (t + s)) ((Y : ℂ) * I)‖ with hA'
  have hA0 : 0 ≤ A := norm_nonneg _
  have hBw0 : 0 ≤ Bw := norm_nonneg _
  have hA'0 : 0 ≤ A' := norm_nonneg _
  have hC0 : 0 ≤ C := by linarith
  have hΔp : 0 ≤ Δ ^ p := pow_nonneg hΔ0 _
  have hE0 : 0 ≤ (1 + |x|) ^ horizExp := by positivity
  refine ⟨?_, ?_, ?_⟩
  · calc A' ≤ C * Bw := k1
      _ ≤ C * (horizConst * (1 + |x|) ^ horizExp * A) := by gcongr
      _ ≤ (C + 1) * (horizConst * Δ ^ p * A) := by
          gcongr
          linarith
      _ = (C + 1) * horizConst * Δ ^ p * A := by ring
  · calc A ≤ horizConst * (1 + |x|) ^ horizExp * Bw := h2
      _ ≤ horizConst * Δ ^ p * (C * A') := by gcongr
      _ ≤ horizConst * Δ ^ p * ((C + 1) * A') := by
          gcongr
          linarith
      _ = (C + 1) * horizConst * Δ ^ p * A' := by ring
  · calc ‖fwdMapInv W (t + s) ((Y : ℂ) * I) - fwdMapInv W t ((Y : ℂ) * I)‖
        ≤ ‖fwdMapInv W (t + s) ((Y : ℂ) * I) - fwdMapInv W t w‖ +
            ‖fwdMapInv W t w - fwdMapInv W t ((Y : ℂ) * I)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ C * Y * Bw + horizConst * (1 + |x|) ^ horizExp * A * (Y * |x|) := add_le_add k3 h3
      _ ≤ C * Y * (horizConst * (1 + |x|) ^ horizExp * A) +
            horizConst * (|x| * (1 + |x|) ^ horizExp) * Y * A :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (mul_nonneg hC0 hY.le)) (le_of_eq (by ring))
      _ ≤ C * Y * (horizConst * Δ ^ p * A) + horizConst * Δ ^ p * Y * A := by
          gcongr
      _ = (C + 1) * horizConst * Δ ^ p * Y * A := by ring

/-! ## [AL14]'s objects in the note's notation ((2.2)–(2.3)) -/

/-- [AL14]'s centered inverse Loewner map in the normalization
`∂_t ḡ_t(z) = (1/4)/(ḡ_t(z) − U_t)`: `F̄_t(z) = ḡ_t⁻¹(U_t + z)`. With `W = √8 U` and QuantumZipper's
chain `g_t` (`∂_t g_t = 2/(g_t − W_t)`), `ḡ_t(z) = g_t(√8 z)/√8`, so `F̄_t(z) = F_t(√8 z)/√8`
with `F_t = fwdMapInv W t` (the note's renormalization, proof of Lemma 2.1, with `U = B`). -/
def barInv (U : ℝ → ℝ) (t : ℝ) (z : ℂ) : ℂ :=
  fwdMapInv (fun r => Real.sqrt 8 * U r) t ((Real.sqrt 8 : ℂ) * z) / (Real.sqrt 8 : ℂ)

/-- The dyadic height `y_k = 2^{-k}` of the note (and `2^{-n}` of [AL14]). -/
def alHeight (k : ℕ) : ℝ := ((2 : ℝ) ^ k)⁻¹

/-- The grid time `j y_k² = j 2^{-2k}` (the points of [AL14]'s `𝒟_k` for `j ≤ 4^k`). -/
def alTime (k j : ℕ) : ℝ := j * alHeight k ^ 2

/-- The note's (2.2) (= [AL14]'s `Δ(j, k)`):
`Δ_{j,k} = 1 + y_k⁻¹ sup_{j y_k² ≤ u ≤ (j+1) y_k²} |U_u − U_{j y_k²}|`. -/
def incDelta (U : ℝ → ℝ) (k j : ℕ) : ℝ :=
  1 + (alHeight k)⁻¹ *
    sSup ((fun u => |U u - U (alTime k j)|) '' Icc (alTime k j) ((j + 1) * alHeight k ^ 2))

/-- The note's `D_k = max_{0 ≤ j ≤ 4^k} |F̄'_{j y_k²}(i y_k)|` ((2.3); [AL14]'s `D_k`). -/
def derivGridMax (U : ℝ → ℝ) (k : ℕ) : ℝ :=
  (Finset.range (4 ^ k + 1)).sup' Finset.nonempty_range_add_one
    fun j => ‖deriv (barInv U (alTime k j)) ((alHeight k : ℂ) * I)‖

/-- The note's `D̂_k = sup_{0 ≤ t ≤ 1} |F̄'_t(i y_k)|` ((2.3); [AL14]'s `D̂_k`). As a real `sSup` it
is meaningful only together with `BddAbove`, which `exists_derivSup_le_derivGridMaxStar`
provides. -/
def derivSup (U : ℝ → ℝ) (k : ℕ) : ℝ :=
  sSup ((fun t => ‖deriv (barInv U t) ((alHeight k : ℂ) * I)‖) '' Icc 0 1)

/-- The note's `D_k^* = max_{0 ≤ j ≤ 4^k} Δ_{j,k}^p |F̄'_{j y_k²}(i y_k)|` ((2.3); [AL14]'s
`D_k^*`), with the exponent `p` as a parameter (printed `p = 4`). -/
def derivGridMaxStar (p : ℕ) (U : ℝ → ℝ) (k : ℕ) : ℝ :=
  (Finset.range (4 ^ k + 1)).sup' Finset.nonempty_range_add_one
    fun j => incDelta U k j ^ p * ‖deriv (barInv U (alTime k j)) ((alHeight k : ℂ) * I)‖

theorem alHeight_pos (k : ℕ) : 0 < alHeight k := by
  unfold alHeight
  positivity

theorem alHeight_sq (k : ℕ) : alHeight k ^ 2 = ((4 : ℝ) ^ k)⁻¹ := by
  rw [alHeight, inv_pow, ← pow_mul, mul_comm, pow_mul]
  norm_num

theorem alTime_nonneg (k j : ℕ) : 0 ≤ alTime k j := by
  unfold alTime
  positivity

/-- `F̄_t'(z) = F_t'(√8 z)`. -/
theorem deriv_barInv (U : ℝ → ℝ) (t : ℝ) (z : ℂ) :
    deriv (barInv U t) z =
      deriv (fwdMapInv (fun r => Real.sqrt 8 * U r) t) ((Real.sqrt 8 : ℂ) * z) := by
  have h8 : (Real.sqrt 8 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 8)).ne'
  change deriv (fun z => fwdMapInv (fun r => Real.sqrt 8 * U r) t ((Real.sqrt 8 : ℂ) * z) /
    (Real.sqrt 8 : ℂ)) z = _
  rw [deriv_div_const, deriv_comp_mul_left, smul_eq_mul]
  field_simp

/-- [AL14]'s forward map `ḡ_t(z) = g_t(√8 z)/√8`, where `g_t = fwdMap W t + W_t` is QuantumZipper's
(uncentred) Loewner map driven by `W = √8 U`. -/
def barFwd (U : ℝ → ℝ) (t : ℝ) (z : ℂ) : ℂ :=
  (fwdMap (fun r => Real.sqrt 8 * U r) t ((Real.sqrt 8 : ℂ) * z) + ((Real.sqrt 8 * U t : ℝ) : ℂ)) /
    (Real.sqrt 8 : ℂ)

/-- `barInv` is the centered inverse of `barFwd`: `ḡ_t(F̄_t(z)) = U_t + z` on `ℍ`. -/
theorem barFwd_barInv {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    {z : ℂ} (hz : 0 < z.im) : barFwd U t (barInv U t z) = U t + z := by
  have h8 : (Real.sqrt 8 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 8)).ne'
  have h8r : 0 < Real.sqrt 8 := Real.sqrt_pos.2 (by norm_num)
  have hW : Continuous fun r => Real.sqrt 8 * U r := continuous_const.mul hU
  have hW0 : (fun r => Real.sqrt 8 * U r) 0 = 0 := by simp [hU0]
  have hmem : (Real.sqrt 8 : ℂ) * z ∈ H := by
    show 0 < ((Real.sqrt 8 : ℂ) * z).im
    rw [Complex.im_ofReal_mul]
    exact mul_pos h8r hz
  unfold barFwd barInv
  rw [mul_div_cancel₀ _ h8, RS.fwdMap_fwdMapInv hW hW0 ht hmem]
  push_cast
  field_simp
  ring

/-- For the note's driver, `barInv` is QuantumZipper's `fwdMapInv (drive 8 B ω)` rescaled. -/
theorem barInv_eq_drive {Ω : Type*} (B : NNReal → Ω → ℝ) (ω : Ω) (t : ℝ) (z : ℂ) :
    barInv (fun r => B r.toNNReal ω) t z =
      fwdMapInv (drive 8 B ω) t ((Real.sqrt 8 : ℂ) * z) / (Real.sqrt 8 : ℂ) :=
  rfl

/-- `0 ≤ sup |U_u − U_{j y_k²}|`. -/
theorem sSup_incr_nonneg (U : ℝ → ℝ) (k j : ℕ) :
    0 ≤ sSup ((fun u => |U u - U (alTime k j)|) '' Icc (alTime k j) ((j + 1) * alHeight k ^ 2)) :=
  Real.sSup_nonneg (by rintro _ ⟨u, -, rfl⟩; exact abs_nonneg _)

theorem one_le_incDelta (U : ℝ → ℝ) (k j : ℕ) : 1 ≤ incDelta U k j := by
  unfold incDelta
  have := sSup_incr_nonneg U k j
  have := inv_pos.2 (alHeight_pos k)
  nlinarith

/-- `|U_{j y_k² + s} − U_{j y_k²}| ≤ (Δ_{j,k} − 1) y_k` for `0 ≤ s ≤ y_k²`. -/
theorem abs_sub_le_incDelta {U : ℝ → ℝ} (hU : Continuous U) (k j : ℕ) {s : ℝ} (hs : 0 ≤ s)
    (hs' : s ≤ alHeight k ^ 2) :
    |U (alTime k j + s) - U (alTime k j)| ≤ (incDelta U k j - 1) * alHeight k := by
  have hy := alHeight_pos k
  have hbdd : BddAbove ((fun u => |U u - U (alTime k j)|) ''
      Icc (alTime k j) ((j + 1) * alHeight k ^ 2)) :=
    (isCompact_Icc.image (by fun_prop)).bddAbove
  have hmem : alTime k j + s ∈ Icc (alTime k j) ((j + 1) * alHeight k ^ 2) := by
    refine ⟨by linarith, ?_⟩
    unfold alTime
    linarith
  have hle := le_csSup hbdd (mem_image_of_mem (fun u => |U u - U (alTime k j)|) hmem)
  have e : (incDelta U k j - 1) * alHeight k =
      sSup ((fun u => |U u - U (alTime k j)|) '' Icc (alTime k j) ((j + 1) * alHeight k ^ 2)) := by
    unfold incDelta
    field_simp
    ring
  rw [e]
  exact hle

/-! ## [AL14] Lemma 1 and `D̂_k ≤ c D_k^*` -/

/-- **[AL14] Lemma 1** (with `Δ^p`, `p ≥ alExp`, in place of the printed `Δ⁴`). There is a universal
`c₃ ≥ 1` such that for every continuous driver `U` with `U 0 = 0`, every `p ≥ alExp`, every `k`, `j`
and every `0 ≤ s ≤ y_k²`, with `t = j y_k²` and `Δ = Δ_{j,k}`:
`|F̄_t'(iy_k)| ≤ c₃ Δ^p |F̄_{t+s}'(iy_k)|`, `|F̄_{t+s}'(iy_k)| ≤ c₃ Δ^p |F̄_t'(iy_k)|` and
`|F̄_{t+s}(iy_k) − F̄_t(iy_k)| ≤ c₃ Δ^p y_k |F̄_t'(iy_k)|` (the increment of `γ^{(k)}`). -/
theorem exists_lemma_one : ∃ c : ℝ, 1 ≤ c ∧ ∀ U : ℝ → ℝ, Continuous U → U 0 = 0 →
    ∀ p : ℕ, alExp ≤ p → ∀ k j : ℕ, ∀ s : ℝ, 0 ≤ s → s ≤ alHeight k ^ 2 →
      ‖deriv (barInv U (alTime k j + s)) ((alHeight k : ℂ) * I)‖ ≤
          c * incDelta U k j ^ p * ‖deriv (barInv U (alTime k j)) ((alHeight k : ℂ) * I)‖ ∧
        ‖deriv (barInv U (alTime k j)) ((alHeight k : ℂ) * I)‖ ≤
          c * incDelta U k j ^ p * ‖deriv (barInv U (alTime k j + s)) ((alHeight k : ℂ) * I)‖ ∧
        ‖barInv U (alTime k j + s) ((alHeight k : ℂ) * I) -
            barInv U (alTime k j) ((alHeight k : ℂ) * I)‖ ≤
          c * incDelta U k j ^ p * alHeight k *
            ‖deriv (barInv U (alTime k j)) ((alHeight k : ℂ) * I)‖ := by
  obtain ⟨c, hc1, hc⟩ := exists_deriv_comparison
  refine ⟨c, hc1, fun U hU hU0 p hp k j s hs hs' => ?_⟩
  have h8 : 0 < Real.sqrt 8 := Real.sqrt_pos.2 (by norm_num)
  have h88 : Real.sqrt 8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  have hy := alHeight_pos k
  set W : ℝ → ℝ := fun r => Real.sqrt 8 * U r with hW_def
  have hW : Continuous W := continuous_const.mul hU
  have hW0 : W 0 = 0 := by simp [hW_def, hU0]
  set y := alHeight k with hy_def
  set Y := Real.sqrt 8 * y with hY_def
  have hY : 0 < Y := mul_pos h8 hy
  have hsY : s ≤ Y ^ 2 := by
    rw [hY_def, mul_pow, h88]
    nlinarith [sq_nonneg y]
  have hinc : |W (alTime k j + s) - W (alTime k j)| ≤ (incDelta U k j - 1) * Y := by
    have h := abs_sub_le_incDelta hU k j hs hs'
    rw [hW_def]
    dsimp only
    rw [← mul_sub, abs_mul, abs_of_pos h8]
    calc Real.sqrt 8 * |U (alTime k j + s) - U (alTime k j)|
        ≤ Real.sqrt 8 * ((incDelta U k j - 1) * y) := mul_le_mul_of_nonneg_left h h8.le
      _ = (incDelta U k j - 1) * Y := by rw [hY_def]; ring
  obtain ⟨d1, d2, d3⟩ := hc W hW hW0 (alTime k j) s Y (incDelta U k j) (alTime_nonneg k j) hs hY
    hsY (one_le_incDelta U k j) hinc p hp
  have hpt : (Real.sqrt 8 : ℂ) * ((y : ℂ) * I) = ((Y : ℝ) : ℂ) * I := by
    rw [hY_def]
    push_cast
    ring
  have hder : ∀ τ, deriv (barInv U τ) ((y : ℂ) * I) = deriv (fwdMapInv W τ) ((Y : ℂ) * I) := by
    intro τ
    rw [deriv_barInv, hpt]
  have hval : ∀ τ, barInv U τ ((y : ℂ) * I) = fwdMapInv W τ ((Y : ℂ) * I) / (Real.sqrt 8 : ℂ) := by
    intro τ
    rw [barInv, hpt]
  rw [hder, hder]
  refine ⟨d1, d2, ?_⟩
  rw [hval, hval, ← sub_div, norm_div, Complex.norm_real, Real.norm_of_nonneg h8.le,
    div_le_iff₀ h8]
  calc ‖fwdMapInv W (alTime k j + s) ((Y : ℂ) * I) - fwdMapInv W (alTime k j) ((Y : ℂ) * I)‖
      ≤ c * incDelta U k j ^ p * Y * ‖deriv (fwdMapInv W (alTime k j)) ((Y : ℂ) * I)‖ := d3
    _ = c * incDelta U k j ^ p * y * ‖deriv (fwdMapInv W (alTime k j)) ((Y : ℂ) * I)‖ *
          Real.sqrt 8 := by
        rw [hY_def]
        ring

/-- Every `t ∈ [0, 1]` is `j y_k² + s` with `j ≤ 4^k` and `0 ≤ s ≤ y_k²`. -/
theorem exists_grid_index (k : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ j : ℕ, j ≤ 4 ^ k ∧ alTime k j ≤ t ∧ t ≤ alTime k j + alHeight k ^ 2 := by
  have hy2 : 0 < alHeight k ^ 2 := pow_pos (alHeight_pos k) 2
  refine ⟨⌊t / alHeight k ^ 2⌋₊, ?_, ?_, ?_⟩
  · refine Nat.floor_le_of_le ?_
    rw [alHeight_sq, div_inv_eq_mul]
    push_cast
    have h4 : (0 : ℝ) ≤ 4 ^ k := by positivity
    nlinarith [ht.2]
  · have h := Nat.floor_le (div_nonneg ht.1 hy2.le)
    rw [le_div_iff₀ hy2] at h
    exact h
  · have h := Nat.lt_floor_add_one (t / alHeight k ^ 2)
    rw [div_lt_iff₀ hy2] at h
    unfold alTime
    linarith

/-- **`D̂_k ≤ c D_k^*`, pointwise form** (the note, proof of Lemma 2.1: "Lemma 1 and the definitions
following it in [AL14] give `D̂_k ≤ c D_k^*`"): `|F̄_t'(iy_k)| ≤ c D_k^*` for every `t ∈ [0, 1]`. -/
theorem exists_norm_deriv_barInv_le_derivGridMaxStar : ∃ c : ℝ, 1 ≤ c ∧ ∀ U : ℝ → ℝ,
    Continuous U → U 0 = 0 → ∀ p : ℕ, alExp ≤ p → ∀ k : ℕ, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖deriv (barInv U t) ((alHeight k : ℂ) * I)‖ ≤ c * derivGridMaxStar p U k := by
  obtain ⟨c, hc1, hc⟩ := exists_lemma_one
  refine ⟨c, hc1, fun U hU hU0 p hp k t ht => ?_⟩
  obtain ⟨j, hj, hjt, hts⟩ := exists_grid_index k ht
  have h := (hc U hU hU0 p hp k j (t - alTime k j) (by linarith) (by linarith)).1
  rw [add_sub_cancel] at h
  refine h.trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (Finset.le_sup'
      (fun j => incDelta U k j ^ p * ‖deriv (barInv U (alTime k j)) ((alHeight k : ℂ) * I)‖)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))
    (by linarith)

/-- **`D̂_k ≤ c D_k^*`** ([AL14], the display after Lemma 1; the note, proof of Lemma 2.1), with the
boundedness that makes the supremum `D̂_k` meaningful. -/
theorem exists_derivSup_le_derivGridMaxStar : ∃ c : ℝ, 1 ≤ c ∧ ∀ U : ℝ → ℝ,
    Continuous U → U 0 = 0 → ∀ p : ℕ, alExp ≤ p → ∀ k : ℕ,
      BddAbove ((fun t => ‖deriv (barInv U t) ((alHeight k : ℂ) * I)‖) '' Icc 0 1) ∧
        derivSup U k ≤ c * derivGridMaxStar p U k := by
  obtain ⟨c, hc1, hc⟩ := exists_norm_deriv_barInv_le_derivGridMaxStar
  refine ⟨c, hc1, fun U hU hU0 p hp k => ⟨⟨c * derivGridMaxStar p U k, ?_⟩, ?_⟩⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact hc U hU hU0 p hp k t ht
  · exact csSup_le ⟨_, mem_image_of_mem _ (left_mem_Icc.2 zero_le_one)⟩
      (by rintro _ ⟨t, ht, rfl⟩; exact hc U hU hU0 p hp k t ht)

/-- **`Θ_k ≤ c 2^{-k} D_k^*`, pointwise form** ([AL14], the display after Lemma 1):
`|F̄_{t+s}(iy_k) − F̄_t(iy_k)| ≤ c y_k D_k^*` for `t = j y_k²`, `j ≤ 4^k`, `0 ≤ s ≤ y_k²`. -/
theorem exists_norm_barInv_sub_le_derivGridMaxStar : ∃ c : ℝ, 1 ≤ c ∧ ∀ U : ℝ → ℝ,
    Continuous U → U 0 = 0 → ∀ p : ℕ, alExp ≤ p → ∀ k j : ℕ, j ≤ 4 ^ k →
      ∀ s : ℝ, 0 ≤ s → s ≤ alHeight k ^ 2 →
        ‖barInv U (alTime k j + s) ((alHeight k : ℂ) * I) -
            barInv U (alTime k j) ((alHeight k : ℂ) * I)‖ ≤
          c * alHeight k * derivGridMaxStar p U k := by
  obtain ⟨c, hc1, hc⟩ := exists_lemma_one
  refine ⟨c, hc1, fun U hU hU0 p hp k j hj s hs hs' => ?_⟩
  refine (hc U hU hU0 p hp k j s hs hs').2.2.trans ?_
  have hmem := Finset.le_sup'
    (fun j => incDelta U k j ^ p * ‖deriv (barInv U (alTime k j)) ((alHeight k : ℂ) * I)‖)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  have hcy : 0 ≤ c * alHeight k := mul_nonneg (by linarith) (alHeight_pos k).le
  calc c * incDelta U k j ^ p * alHeight k * ‖deriv (barInv U (alTime k j)) ((alHeight k : ℂ) * I)‖
      = c * alHeight k *
          (incDelta U k j ^ p * ‖deriv (barInv U (alTime k j)) ((alHeight k : ℂ) * I)‖) := by ring
    _ ≤ c * alHeight k * derivGridMaxStar p U k := mul_le_mul_of_nonneg_left hmem hcy

/-- `D_k ≤ D_k^*` (as `Δ_{j,k} ≥ 1`). -/
theorem derivGridMax_le_derivGridMaxStar (p : ℕ) (U : ℝ → ℝ) (k : ℕ) :
    derivGridMax U k ≤ derivGridMaxStar p U k := by
  refine Finset.sup'_le _ _ fun j hj => le_trans ?_ (Finset.le_sup' _ hj)
  exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (one_le_incDelta U k j))

end InteractingSLE.SLE8.AL14
