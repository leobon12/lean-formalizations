import InteractingSLE.SLE8.ReverseFlow
import QuantumZipper.Proofs.RS.KoebeLoewnerTime

/-!
# Comparison with a time grid (SLE₈ note, Lemma 2.3)

SLE₈ note `source/sle8-continuity.pdf`, §2.2, p. 4 (transcription `source/sle8/sle8-continuity.md`,
anchors `lem-2.3`, `lem-2.3-proof`).

With `y_k = 2^{-k}` (`dyadicHeight k`), `t_k = y_k² ⌊t / y_k²⌋` (`gridTime k t`) and the normalized
derivative `A_k(t) = y_k |F_t'(iy_k)|` (`normalizedDeriv W k t`, with `F_t = fwdMapInv W t`), Lemma 2.3
says that on the event `Ω_M` of (2.11) (`DriverBound M W`) one has `A_k(t) ≤ C_M k² A_k(t_k)` for all
`k ≥ 1` and `t ∈ [0, 1]`.

## Exponent

The printed power `k²` comes from the sharp Koebe distortion (2.14), which is not available in the
host library. We prove the estimate with a fixed (non-explicit, absolute) exponent `p ≥ 1`: the
exponent of QuantumZipper's non-sharp distortion `RS.kd_distortion`. Any polynomial power suffices for
the note's later use (its (5.3)).

## Proof

Write `δ = t - t_k ∈ [0, y_k²)` and `d = W_t - W_{t_k}`. QuantumZipper's time step `RS.kd_time_step`
(Kemppainen, Lemma 6.7; its proof is the reverse-flow argument of the note: (2.7), `Φ ≤ e²`, and a
Koebe chain) gives `|F_t'(iy_k)| ≤ C₁ |F_{t_k}'(d + iy_k)|`, and the Koebe distortion `RS.kd_distortion`
gives `|F_{t_k}'(d + iy_k)| ≤ C₂ (1 + (d/y_k)²)^{C₂} |F_{t_k}'(iy_k)|`. By (2.11) and the monotonicity
of `u ↦ u log(e/u)` on `(0, 1]` (`mul_log_exp_div_le`), `(d/y_k)² ≤ M²(1 + 2k log 2) ≤ 3M² k`.
-/

noncomputable section

open Set Filter Complex
open scoped Topology

namespace InteractingSLE.SLE8

open QuantumZipper

/-! ## The dyadic heights, the time grid and the normalized derivative -/

/-- The dyadic height `y_k = 2^{-k}` of the SLE₈ note. -/
def dyadicHeight (k : ℕ) : ℝ := ((2 : ℝ) ^ k)⁻¹

/-- The grid time `t_k = y_k² ⌊t / y_k²⌋` of (2.12). -/
def gridTime (k : ℕ) (t : ℝ) : ℝ := dyadicHeight k ^ 2 * ⌊t / dyadicHeight k ^ 2⌋

/-- The normalized derivative `A_k(t) = y_k |F_t'(iy_k)|` of (2.12), for the centred inverse maps
`F_t = fwdMapInv W t` driven by `W`. -/
def normalizedDeriv (W : ℝ → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  dyadicHeight k * ‖deriv (fwdMapInv W t) ((dyadicHeight k : ℂ) * I)‖

/-- The event `Ω_M` of (2.11), for a deterministic driver `W`: `sup_{0 ≤ t ≤ 1} |W_t| ≤ M` and
`|W_t - W_s| ≤ M √((t - s) log(e/(t - s)))` for `0 ≤ s < t ≤ 1`. -/
def DriverBound (M : ℝ) (W : ℝ → ℝ) : Prop :=
  (∀ t ∈ Icc (0 : ℝ) 1, |W t| ≤ M) ∧
    ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      |W t - W s| ≤ M * Real.sqrt ((t - s) * Real.log (Real.exp 1 / (t - s)))

theorem dyadicHeight_pos (k : ℕ) : 0 < dyadicHeight k := by
  unfold dyadicHeight; positivity

theorem dyadicHeight_le_one (k : ℕ) : dyadicHeight k ≤ 1 := by
  unfold dyadicHeight
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

theorem log_dyadicHeight_sq (k : ℕ) : Real.log (dyadicHeight k ^ 2) = -(2 * k * Real.log 2) := by
  unfold dyadicHeight
  rw [Real.log_pow, Real.log_inv, Real.log_pow]
  push_cast; ring

theorem gridTime_nonneg (k : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ gridTime k t := by
  unfold gridTime
  have hy := dyadicHeight_pos k
  have : (0 : ℝ) ≤ ⌊t / dyadicHeight k ^ 2⌋ := by
    exact_mod_cast Int.floor_nonneg.2 (by positivity)
  positivity

theorem gridTime_le (k : ℕ) (t : ℝ) : gridTime k t ≤ t := by
  unfold gridTime
  have hy : 0 < dyadicHeight k ^ 2 := by have := dyadicHeight_pos k; positivity
  calc dyadicHeight k ^ 2 * ⌊t / dyadicHeight k ^ 2⌋ ≤ dyadicHeight k ^ 2 * (t / dyadicHeight k ^ 2) :=
        mul_le_mul_of_nonneg_left (Int.floor_le _) hy.le
    _ = t := mul_div_cancel₀ t hy.ne'

theorem sub_gridTime_lt (k : ℕ) (t : ℝ) : t - gridTime k t < dyadicHeight k ^ 2 := by
  unfold gridTime
  have hy : 0 < dyadicHeight k ^ 2 := by have := dyadicHeight_pos k; positivity
  have h := Int.lt_floor_add_one (t / dyadicHeight k ^ 2)
  have h2 : t < dyadicHeight k ^ 2 * (⌊t / dyadicHeight k ^ 2⌋ + 1) := by
    rw [div_lt_iff₀ hy] at h; linarith
  linarith

/-- `u ↦ u log(e/u)` is nondecreasing on `(0, 1]`. -/
theorem mul_log_exp_div_le {δ a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (ha : a ≤ 1) :
    δ * Real.log (Real.exp 1 / δ) ≤ a * Real.log (Real.exp 1 / a) := by
  have ha0 : 0 < a := hδ.trans_le hδa
  rw [Real.log_div (Real.exp_pos 1).ne' hδ.ne', Real.log_div (Real.exp_pos 1).ne' ha0.ne',
    Real.log_exp]
  have h1 : Real.log (a / δ) ≤ a / δ - 1 := Real.log_le_sub_one_of_pos (div_pos ha0 hδ)
  rw [Real.log_div ha0.ne' hδ.ne'] at h1
  have h2 : δ * (Real.log a - Real.log δ) ≤ a - δ := by
    have := mul_le_mul_of_nonneg_left h1 hδ.le
    have e : δ * (a / δ - 1) = a - δ := by field_simp
    rw [e] at this
    exact this
  have hla : Real.log a ≤ 0 := Real.log_nonpos ha0.le ha
  have h3 : (a - δ) * Real.log a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hla
  nlinarith


/-- The increment over one grid step: under the modulus bound of (2.11),
`(W_t - W_{t_k})² ≤ M² y_k² (1 + 2k log 2)` for `t ∈ [0, 1]`. -/
theorem sq_sub_gridTime_le {M : ℝ} {W : ℝ → ℝ}
    (hmod : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      |W t - W s| ≤ M * Real.sqrt ((t - s) * Real.log (Real.exp 1 / (t - s))))
    (k : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (W t - W (gridTime k t)) ^ 2 ≤ M ^ 2 * (dyadicHeight k ^ 2 * (1 + 2 * k * Real.log 2)) := by
  have hy2 : 0 < dyadicHeight k ^ 2 := by have := dyadicHeight_pos k; positivity
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rcases (gridTime_le k t).eq_or_lt with h | h
  · rw [h, sub_self]
    have : 0 ≤ M ^ 2 * (dyadicHeight k ^ 2 * (1 + 2 * k * Real.log 2)) := by positivity
    simpa using this
  · have hδ : 0 < t - gridTime k t := sub_pos.2 h
    have hδy : t - gridTime k t ≤ dyadicHeight k ^ 2 := (sub_gridTime_lt k t).le
    have hy1 : dyadicHeight k ^ 2 ≤ 1 := pow_le_one₀ (dyadicHeight_pos k).le (dyadicHeight_le_one k)
    have hb := hmod (gridTime k t) t (gridTime_nonneg k ht.1) h ht.2
    have hx : 0 ≤ (t - gridTime k t) * Real.log (Real.exp 1 / (t - gridTime k t)) := by
      refine mul_nonneg hδ.le (Real.log_nonneg ?_)
      rw [le_div_iff₀ hδ, one_mul]
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have hsq : (W t - W (gridTime k t)) ^ 2 ≤
        M ^ 2 * ((t - gridTime k t) * Real.log (Real.exp 1 / (t - gridTime k t))) := by
      calc (W t - W (gridTime k t)) ^ 2 = |W t - W (gridTime k t)| ^ 2 := (sq_abs _).symm
        _ ≤ (M * Real.sqrt ((t - gridTime k t) *
              Real.log (Real.exp 1 / (t - gridTime k t)))) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hb 2
        _ = _ := by rw [mul_pow, Real.sq_sqrt hx]
    have hmono := mul_log_exp_div_le hδ hδy hy1
    have he : dyadicHeight k ^ 2 * Real.log (Real.exp 1 / dyadicHeight k ^ 2) =
        dyadicHeight k ^ 2 * (1 + 2 * k * Real.log 2) := by
      rw [Real.log_div (Real.exp_pos 1).ne' hy2.ne', Real.log_exp, log_dyadicHeight_sq]; ring
    rw [he] at hmono
    exact hsq.trans (mul_le_mul_of_nonneg_left hmono (sq_nonneg M))

/-- **Lemma 2.3** (SLE₈ note, p. 4), deterministic form, from the modulus bound of (2.11) alone, with
a fixed exponent `p ≥ 1` in place of the printed `2`: there is `p` such that for every `M` there is
`C_M` with `A_k(t) ≤ C_M k^p A_k(t_k)` for every continuous driver `W` with `W 0 = 0` satisfying
`|W_t - W_s| ≤ M √((t - s) log(e/(t - s)))` (`0 ≤ s < t ≤ 1`), every `k ≥ 1` and `t ∈ [0, 1]`. -/
theorem exists_normalizedDeriv_le_of_modulus :
    ∃ p : ℝ, 1 ≤ p ∧ ∀ M : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ W : ℝ → ℝ, Continuous W → W 0 = 0 →
      (∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
        |W t - W s| ≤ M * Real.sqrt ((t - s) * Real.log (Real.exp 1 / (t - s)))) →
      ∀ k : ℕ, 1 ≤ k → ∀ t ∈ Icc (0 : ℝ) 1,
        normalizedDeriv W k t ≤ C * (k : ℝ) ^ p * normalizedDeriv W k (gridTime k t) := by
  obtain ⟨C₁, hC₁, hts⟩ := RS.kd_time_step
  obtain ⟨C₂, hC₂, hkd⟩ := RS.kd_distortion
  refine ⟨C₂, hC₂, fun M => ⟨C₁ * C₂ * (1 + 3 * M ^ 2) ^ C₂, by positivity, ?_⟩⟩
  intro W hW hW0 hmod k hk t ht
  have hy : 0 < dyadicHeight k := dyadicHeight_pos k
  have htk0 : 0 ≤ gridTime k t := gridTime_nonneg k ht.1
  have hδ0 : 0 ≤ t - gridTime k t := sub_nonneg.2 (gridTime_le k t)
  have hδy : t - gridTime k t ≤ dyadicHeight k ^ 2 := (sub_gridTime_lt k t).le
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = W t - W (gridTime k t) := ⟨_, rfl⟩
  obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = dyadicHeight k := ⟨_, rfl⟩
  obtain ⟨tk, htk⟩ : ∃ tk : ℝ, tk = gridTime k t := ⟨_, rfl⟩
  rw [← hydef] at hy hδy
  rw [← htk] at htk0 hδ0 hδy hd
  -- the time step `t_k → t` (Kemppainen, Lemma 6.7)
  have hwim : ((d : ℂ) + (y : ℂ) * I).im = y := by simp
  obtain ⟨h1, -, -⟩ := hts W hW hW0 tk (t - tk) htk0 hδ0 ((d : ℂ) + (y : ℂ) * I)
    (by rw [hwim]; exact hy) (by rw [hwim]; exact hδy)
  have htt : tk + (t - tk) = t := by ring
  rw [htt, ← hd] at h1
  have hpt : (d : ℂ) + (y : ℂ) * I - (d : ℂ) = (y : ℂ) * I := by ring
  rw [hpt] at h1
  -- the horizontal Koebe distortion from `d + iy` to `iy`
  obtain ⟨-, h2, -⟩ := hkd (fwdMapInv W tk) (RS.differentiableOn_fwdMapInv hW hW0 htk0)
    (RS.injOn_fwdMapInv hW hW0 htk0) y hy (d / y)
  have hpt2 : (y : ℂ) * (((d / y : ℝ) : ℂ) + I) = (d : ℂ) + (y : ℂ) * I := by
    have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 hy.ne'
    push_cast
    field_simp
  rw [hpt2] at h2
  -- the increment bound `1 + (d/y)² ≤ (1 + 3M²) k`
  have hdsq := sq_sub_gridTime_le hmod k ht
  rw [← htk, ← hd, ← hydef] at hdsq
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (two_pos : (0 : ℝ) < 2); linarith
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hdy : (d / y) ^ 2 ≤ M ^ 2 * (1 + 2 * k * Real.log 2) := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    linarith
  have hx : 1 + (d / y) ^ 2 ≤ (1 + 3 * M ^ 2) * k := by
    have hM : 0 ≤ M ^ 2 := sq_nonneg M
    have h3 : M ^ 2 * (1 + 2 * k * Real.log 2) ≤ 3 * M ^ 2 * k := by
      have : 1 + 2 * k * Real.log 2 ≤ 3 * k := by nlinarith
      nlinarith
    nlinarith
  have hpow : (1 + (d / y) ^ 2) ^ C₂ ≤ (1 + 3 * M ^ 2) ^ C₂ * (k : ℝ) ^ C₂ := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) hx (by linarith)
  -- assembly
  unfold normalizedDeriv
  rw [← hydef, ← htk]
  have hC₁0 : 0 ≤ C₁ := by linarith
  have hC₂0 : 0 ≤ C₂ := by linarith
  calc y * ‖deriv (fwdMapInv W t) ((y : ℂ) * I)‖
      ≤ y * (C₁ * ‖deriv (fwdMapInv W tk) ((d : ℂ) + (y : ℂ) * I)‖) :=
        mul_le_mul_of_nonneg_left h1 hy.le
    _ ≤ y * (C₁ * (C₂ * (1 + (d / y) ^ 2) ^ C₂ * ‖deriv (fwdMapInv W tk) ((y : ℂ) * I)‖)) := by
        gcongr
    _ ≤ y * (C₁ * (C₂ * ((1 + 3 * M ^ 2) ^ C₂ * (k : ℝ) ^ C₂) *
          ‖deriv (fwdMapInv W tk) ((y : ℂ) * I)‖)) := by
        gcongr
    _ = C₁ * C₂ * (1 + 3 * M ^ 2) ^ C₂ * (k : ℝ) ^ C₂ *
          (y * ‖deriv (fwdMapInv W tk) ((y : ℂ) * I)‖) := by ring

/-- **Lemma 2.3** (SLE₈ note, p. 4: comparison with a time grid), deterministic form on the event
`Ω_M` of (2.11), with a fixed exponent `p ≥ 1` in place of the printed `2` (the exponent of the
non-sharp Koebe distortion `RS.kd_distortion`): there is `p` such that for every `M` there is a
deterministic `C_M` with `A_k(t) ≤ C_M k^p A_k(t_k)`, `t_k = y_k² ⌊t/y_k²⌋`, for every continuous
driver `W` with `W 0 = 0` in `Ω_M`, every `k ≥ 1` and `t ∈ [0, 1]`. -/
theorem exists_normalizedDeriv_le_gridTime :
    ∃ p : ℝ, 1 ≤ p ∧ ∀ M : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ W : ℝ → ℝ, Continuous W → W 0 = 0 →
      DriverBound M W → ∀ k : ℕ, 1 ≤ k → ∀ t ∈ Icc (0 : ℝ) 1,
        normalizedDeriv W k t ≤ C * (k : ℝ) ^ p * normalizedDeriv W k (gridTime k t) := by
  obtain ⟨p, hp, h⟩ := exists_normalizedDeriv_le_of_modulus
  refine ⟨p, hp, fun M => ?_⟩
  obtain ⟨C, hC, hW⟩ := h M
  exact ⟨C, hC, fun W hc h0 hM => hW W hc h0 hM.2⟩

end InteractingSLE.SLE8
