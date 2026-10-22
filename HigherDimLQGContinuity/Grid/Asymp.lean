import HigherDimLQGContinuity.Grid.Arithmetic
import HigherDimLQGContinuity.Endpoint.Asymp

/-!
# Growth estimates for the positive-window grid

The endpoint grid arithmetic is reused by comparing its level `2^(Dj)` with the
positive-window level `2^(j²)` for sufficiently large `j`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGContinuity

theorem posLevel_ge_endLevel_add (D : ℕ) :
    ∀ᶠ j : ℕ in atTop, endLevel D 0 j + j ≤ posLevel j := by
  filter_upwards [eventually_ge_atTop (D + 9)] with j hj
  have hlarge := posLevel_ge_pow_linear (D + 1) (by omega : D + 1 + 8 ≤ j)
  have hexp : D * j + j ≤ (D + 1) * (j + 6) := by nlinarith
  have hpow : 2 ^ (D * j + j) ≤ posLevel j :=
    (Nat.pow_le_pow_right (by omega) hexp).trans hlarge
  have hE : 1 ≤ endLevel D 0 j := Nat.one_le_two_pow
  have hjpow : j + 1 ≤ 2 ^ j := pos_nat_succ_le_two_pow (by omega)
  have heq : 2 ^ (D * j + j) = endLevel D 0 j * 2 ^ j := by
    simp only [endLevel, zero_add, ← pow_add]
  have hmul : endLevel D 0 j + j ≤ endLevel D 0 j * 2 ^ j := by
    have hreal : (endLevel D 0 j : ℝ) + j ≤ endLevel D 0 j * (2 ^ j : ℝ) := by
      have hjR : (j : ℝ) + 1 ≤ (2 ^ j : ℕ) := by exact_mod_cast hjpow
      have hER : (1 : ℝ) ≤ endLevel D 0 j := by exact_mod_cast hE
      have hprod : 0 ≤ ((endLevel D 0 j : ℝ) - 1) * (j : ℝ) :=
        mul_nonneg (by linarith) (Nat.cast_nonneg _)
      have hE0 : (0 : ℝ) ≤ endLevel D 0 j := by exact_mod_cast (Nat.zero_le (endLevel D 0 j))
      have hmul' := mul_le_mul_of_nonneg_left hjR hE0
      have hmul'' : (endLevel D 0 j : ℝ) * ((j : ℝ) + 1) ≤
          endLevel D 0 j * (2 : ℝ) ^ j := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using hmul'
      have hleft : (endLevel D 0 j : ℝ) + j ≤ endLevel D 0 j * ((j : ℝ) + 1) := by
        nlinarith
      exact hleft.trans hmul''
    exact_mod_cast hreal
  exact hmul.trans (heq ▸ hpow)

/-- Any fixed window length times the super-exponential mesh is eventually finer
than the endpoint packet's level `2^(Dj)` mesh. -/
theorem eventually_posWidth_le_endA_endLevel {lo hi : ℝ} (h : lo < hi) (D : ℕ) :
    ∀ᶠ j : ℕ in atTop, posWidth lo hi j ≤ endA (endLevel D 0 j) := by
  filter_upwards [posLevel_ge_endLevel_add D,
    endpt_eventually_le_two_pow (hi - lo)] with j hlev hlen
  have hw : 0 < hi - lo := sub_pos.2 h
  unfold posWidth
  calc
    (hi - lo) * endA (posLevel j) ≤ (2 : ℝ) ^ j * endA (posLevel j) := by
      gcongr
      exact (endA_pos _).le
    _ ≤ 2 ^ j * endA (endLevel D 0 j + j) := by
      gcongr
      exact endA_anti hlev
    _ = endA (endLevel D 0 j) := by
      rw [endA_add]
      have hkey := endA_mul_two_pow j
      calc 2 ^ j * (endA (endLevel D 0 j) * endA j)
          = endA (endLevel D 0 j) * (endA j * 2 ^ j) := by ring
        _ = endA (endLevel D 0 j) := by rw [hkey, mul_one]

/-- The generic-seed gap condition, inherited from the endpoint arithmetic after
the radius-independent level overtakes the endpoint's exponential level. -/
theorem eventually_posGrid_G {lo hi B M C : ℝ} (hlo : 0 < lo) (hlohi : lo < hi)
    (hC : 0 < C) :
    ∀ᶠ j : ℕ in atTop,
      posWidth lo hi j ≤ Real.exp (-(C * lo ^ (-B) * posDelta j ^ (-B))) := by
  let C' : ℝ := C * lo ^ (-B)
  have hC' : 0 < C' := mul_pos hC (Real.rpow_pos_of_pos hlo _)
  obtain ⟨N, hN⟩ := endpt_fine_G (B := B) (M := M) hC'
  filter_upwards [eventually_posWidth_le_endA_endLevel hlohi (endDexp B M),
    eventually_ge_atTop N] with j hwidth hj
  have hendpoint := hN 0 j (by simpa using hj)
  have heq : endDelta 0 j = posDelta j := by
    simp only [endDelta, endEps, endA, pow_zero, Real.sqrt_one, one_mul, posDelta]
  have h0 : endA 0 = 1 := by norm_num [endA]
  calc posWidth lo hi j ≤ endA (endLevel (endDexp B M) 0 j) := hwidth
    _ = endA (0 + endLevel (endDexp B M) 0 j) := by rw [zero_add]
    _ ≤ Real.exp (-(C * lo ^ (-B) * posDelta j ^ (-B))) := by
      simpa only [C', h0, Real.one_rpow, mul_one, heq] using hendpoint

/-- The depth inequality for the real comparison depth `c δ_j / w_j`. -/
theorem eventually_posGrid_depth {lo hi B M C c : ℝ} (hlohi : lo < hi)
    (hC : 1 ≤ C) (hc : 0 < c) :
    ∀ᶠ j : ℕ in atTop,
      C * posDelta j ^ (-M) * Real.log (C / posDelta j) ≤
        c * posDelta j / posWidth lo hi j := by
  obtain ⟨N, hN⟩ := endpt_fine_depth (B := B) (M := M) hC hc
  filter_upwards [eventually_posWidth_le_endA_endLevel hlohi (endDexp B M),
    eventually_ge_atTop N] with j hwidth hj
  have hendpoint := hN 0 j (by simpa using hj)
  have heq : endDelta 0 j = posDelta j := by
    simp only [endDelta, endEps, endA, pow_zero, Real.sqrt_one, one_mul, posDelta]
  have h0 : endA 0 = 1 := by norm_num [endA]
  have hw : 0 < posWidth lo hi j := posWidth_pos hlohi j
  have he : 0 < endA (endLevel (endDexp B M) 0 j) := endA_pos _
  have hnum : 0 ≤ c * posDelta j := mul_nonneg hc.le (posDelta_pos j).le
  calc
    C * posDelta j ^ (-M) * Real.log (C / posDelta j) ≤
        c * posDelta j / endA (endLevel (endDexp B M) 0 j) := by
      simpa only [heq, h0, Real.one_rpow, mul_one, zero_add] using hendpoint
    _ ≤ c * posDelta j / posWidth lo hi j := by
      apply (div_le_div_iff₀ he hw).2
      nlinarith [mul_le_mul_of_nonneg_left hwidth hnum]

/-- Double exponential domination after losing any fixed linear number of binary digits. -/
theorem eventually_posLevel_exp_dominates_sq (A : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    ∀ᶠ j : ℕ in atTop,
      K * (posLevel j : ℝ) ^ 2 ≤
        (2 : ℝ) ^ (posLevel j - A * (j + 6)) := by
  let v (j : ℕ) := posLevel j - A * (j + 6)
  have hvgrow : Tendsto v atTop atTop := by
    apply Filter.tendsto_atTop_mono' atTop _ tendsto_id
    filter_upwards [eventually_ge_atTop (2 * A + 8)] with j hj
    have h := posLevel_ge_quadratic (2 * A) hj
    have hlevel' : j + 2 * (A * (j + 6)) ≤ posLevel j := by nlinarith
    have hA : A * (j + 6) ≤ posLevel j := by omega
    dsimp [v]
    omega
  have hexp' : ∀ᶠ j : ℕ in atTop,
      (4 * K) * (v j : ℝ) ^ 2 ≤ (2 : ℝ) ^ (v j) :=
    hvgrow.eventually (endpt_eventually_mul_sq_le_two_pow (4 * K))
  filter_upwards [eventually_ge_atTop (2 * A + 8), hexp'] with j hj hbound
  have hlevel := posLevel_ge_quadratic (2 * A) hj
  have hlevel' : j + 2 * (A * (j + 6)) ≤ posLevel j := by nlinarith
  have hA : A * (j + 6) ≤ posLevel j := by omega
  have htwice : posLevel j ≤ 2 * v j := by
    dsimp [v]
    omega
  have hreal : (posLevel j : ℝ) ≤ 2 * (v j : ℝ) := by exact_mod_cast htwice
  have hv0 : (0 : ℝ) ≤ v j := Nat.cast_nonneg _
  calc
    K * (posLevel j : ℝ) ^ 2 ≤ K * (2 * (v j : ℝ)) ^ 2 := by gcongr
    _ = (4 * K) * (v j : ℝ) ^ 2 := by ring
    _ ≤ (2 : ℝ) ^ (v j) := hbound

/-- The union-bound summand at one level is eventually at most `2^(-j-1)`;
the two bracket families then cost at most `2^(-j)`. -/
theorem eventually_posGrid_fail {lo hi M C c : ℝ} (hlohi : lo < hi)
    (hC : 1 ≤ C) (hc : 0 < c) :
    ∀ᶠ j : ℕ in atTop,
      ((2 : ℝ) ^ posLevel (j + 1) + 1) *
        (C * posDelta j ^ (-M) * Real.exp (-(c * posDelta j ^ M *
          (c * posDelta j / posWidth lo hi j)))) ≤ endA (j + 1) := by
  let A : ℕ := ⌈M⌉₊ + 1
  let L : ℝ := hi - lo
  let γ : ℝ := c ^ 2 / L
  let K : ℝ := Real.log C + ((A : ℝ) + 3) * Real.log 2
  have hL : 0 < L := sub_pos.2 hlohi
  have hγ : 0 < γ := div_pos (sq_pos_of_pos hc) hL
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hKγ : 0 ≤ K / γ := div_nonneg hK hγ.le
  filter_upwards [eventually_ge_atTop (2 * A + 8),
    eventually_posLevel_exp_dominates_sq A hKγ] with j hj hdom
  let u := posLevel j
  let q := posLevel (j + 1)
  let v := u - A * (j + 6)
  let δ := posDelta j
  let w := posWidth lo hi j
  let X := c * δ ^ M * (c * δ / w)
  have huBig := posLevel_ge_quadratic (2 * A) hj
  have hAj : A * (j + 6) ≤ u := by dsimp [u]; nlinarith
  have hsum : v + A * (j + 6) = u := Nat.sub_add_cancel hAj
  have hu1 : 1 ≤ u := Nat.one_le_two_pow
  have huj : j + 6 ≤ u := by
    dsimp [u]
    nlinarith [huBig]
  have hq : q ≤ u ^ 2 := posLevel_succ_le_sq (by omega)
  have hδ0 : 0 < δ := posDelta_pos j
  have hδ1 : δ ≤ 1 := (posDelta_lt_eighth j).le.trans (by norm_num)
  have hδid : δ = (1 / 2 : ℝ) ^ (j + 6) := rfl
  have hneg : δ ^ (-M) ≤ (2 : ℝ) ^ ((j + 6) * ⌈M⌉₊) := by
    apply endpt_rpow_neg_le hδ0 hδ1
    rw [hδid]
  have hpos : (1 / 2 : ℝ) ^ ((j + 6) * ⌈M⌉₊) ≤ δ ^ M := by
    apply endpt_pow_le_rpow hδ0 hδ1
    rw [hδid]
  have hw : 0 < w := posWidth_pos hlohi j
  have hX : γ * (2 : ℝ) ^ v ≤ X := by
    have hδprod : endA (A * (j + 6)) ≤ δ ^ M * δ := by
      have hpow : endA (A * (j + 6)) =
          (1 / 2 : ℝ) ^ ((j + 6) * ⌈M⌉₊) * δ := by
        dsimp [A]
        rw [show (⌈M⌉₊ + 1) * (j + 6) = (j + 6) * ⌈M⌉₊ + (j + 6) by ring,
          endA_add, hδid]
        rfl
      rw [hpow]
      exact mul_le_mul_of_nonneg_right hpos hδ0.le
    have hwu : w * (2 : ℝ) ^ u = L := by
      dsimp [w, posWidth]
      have h := endA_mul_two_pow u
      calc L * endA u * (2 : ℝ) ^ u = L * (endA u * (2 : ℝ) ^ u) := by ring
        _ = L := by rw [h, mul_one]
    have hkey' : endA (A * (j + 6)) * (2 : ℝ) ^ u = (2 : ℝ) ^ v := by
      rw [← hsum, pow_add]
      have h1 := endA_mul_two_pow (A * (j + 6))
      calc endA (A * (j + 6)) *
          ((2 : ℝ) ^ v * (2 : ℝ) ^ (A * (j + 6)))
          = (2 : ℝ) ^ v *
            (endA (A * (j + 6)) * (2 : ℝ) ^ (A * (j + 6))) := by ring
        _ = (2 : ℝ) ^ v := by rw [h1, mul_one]
    have hXeq : X = γ * (δ ^ M * δ * (2 : ℝ) ^ u) := by
      have hinv : w⁻¹ = (2 : ℝ) ^ u / L := by
        apply (eq_div_iff hL.ne').2
        have hpow : 0 < (2 : ℝ) ^ u := by positivity
        have hwu' := hwu
        field_simp at hwu' ⊢
        nlinarith
      dsimp [X, γ]
      rw [div_eq_mul_inv, hinv]
      ring
    rw [hXeq]
    have hmul := mul_le_mul_of_nonneg_left hδprod (by positivity : 0 ≤ γ)
    calc γ * (2 : ℝ) ^ v = γ * (endA (A * (j + 6)) * (2 : ℝ) ^ u) := by rw [hkey']
      _ ≤ γ * (δ ^ M * δ * (2 : ℝ) ^ u) := by gcongr
  have hdom' : K * (u : ℝ) ^ 2 ≤ γ * (2 : ℝ) ^ v := by
    have h := mul_le_mul_of_nonneg_left hdom hγ.le
    have hγ0 : γ ≠ 0 := hγ.ne'
    dsimp [u, v] at h ⊢
    calc K * (posLevel j : ℝ) ^ 2 = γ * ((K / γ) * (posLevel j : ℝ) ^ 2) := by field_simp
      _ ≤ γ * (2 : ℝ) ^ (posLevel j - A * (j + 6)) := h
  have hlogbound : Real.log C +
      ((q + 1 + (j + 6) * ⌈M⌉₊ + (j + 1) : ℕ) : ℝ) * Real.log 2 ≤ K * (u : ℝ) ^ 2 := by
    have hqR : (q : ℝ) ≤ (u : ℝ) ^ 2 := by exact_mod_cast hq
    have huR : (j : ℝ) + 6 ≤ (u : ℝ) := by exact_mod_cast huj
    have huSq : (u : ℝ) ≤ (u : ℝ) ^ 2 := by
      have huR1 : (1 : ℝ) ≤ u := by exact_mod_cast hu1
      nlinarith
    have hunit : (1 : ℝ) ≤ (u : ℝ) ^ 2 := by nlinarith [huSq]
    have hMR : 0 ≤ (⌈M⌉₊ : ℝ) := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_left (huR.trans huSq) hMR
    dsimp [K, A]
    push_cast
    nlinarith [mul_nonneg hlogC (sub_nonneg.mpr hunit)]
  have hlogX : Real.log C +
      ((q + 1 + (j + 6) * ⌈M⌉₊ + (j + 1) : ℕ) : ℝ) * Real.log 2 ≤ X :=
    hlogbound.trans (hdom'.trans hX)
  have hpowbound : ((2 : ℝ) ^ q + 1) ≤ (2 : ℝ) ^ (q + 1) := by
    rw [pow_succ]
    have hq1 : (1 : ℝ) ≤ (2 : ℝ) ^ q := one_le_pow₀ (by norm_num)
    nlinarith
  have hfinal := endpt_mul_exp_le (a := q + 1 + (j + 6) * ⌈M⌉₊)
    (b := j + 1) (show 0 < C by linarith) hlogX
  calc
    ((2 : ℝ) ^ q + 1) * (C * δ ^ (-M) * Real.exp (-X)) ≤
        (2 : ℝ) ^ (q + 1) * (C * (2 : ℝ) ^ ((j + 6) * ⌈M⌉₊) * Real.exp (-X)) := by
      gcongr
    _ = (2 : ℝ) ^ (q + 1 + (j + 6) * ⌈M⌉₊) * C * Real.exp (-X) := by
      calc
        (2 : ℝ) ^ (q + 1) * (C * (2 : ℝ) ^ ((j + 6) * ⌈M⌉₊) * Real.exp (-X))
            = ((2 : ℝ) ^ (q + 1) * (2 : ℝ) ^ ((j + 6) * ⌈M⌉₊)) * C * Real.exp (-X) := by ring
        _ = (2 : ℝ) ^ (q + 1 + (j + 6) * ⌈M⌉₊) * C * Real.exp (-X) := by rw [← pow_add]
    _ ≤ endA (j + 1) := hfinal

end HigherDimLQGContinuity
