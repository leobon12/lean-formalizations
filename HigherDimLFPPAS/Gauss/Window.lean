import HigherDimLFPPAS.Gauss.Cell

/-!
# The window processes of (2.8) (packet F2b)

For `a > 0` and `n ≥ 1` put `t_n = a log n`, `τ_n = a log (n + 1) - a log n` (so that
`ε ∈ [(n+1)^{-a}, n^{-a}]` iff `log ε⁻¹ ∈ [t_n, t_n + τ_n]`) and the mesh `ℓ_n = e^{-t_n} τ_n`. The
window process on `[0,1]^{1+d}` is
`Y_{n,k}(σ, v) = H_{t_n + σ τ_n}(ℓ_n (k + v)) - H_{t_n}(ℓ_n (k + v))` (`winProcF2b`).

This is the derivative-free route of the planning audit MA3, Details P6, with one change: the
cells have mesh `e^{-t_n} τ_n` instead of `e^{-⌊t_n⌋}`. Then P4.1′ gives the *linear* increment bound
`E (Y_p - Y_q)² ≤ K τ_n ‖p - q‖_∞` and `Var Y_p ≤ K τ_n` (`exists_win_increment_F2b`), so the chaining
bound `E sup Y = O(√τ_n)` and Borell–TIS give `P(sup |Y_{n,k}| ≥ x) ≤ c exp(-x²/(4 K τ_n))`
(`exists_win_sup_tail_F2b`), uniformly in `k`. The number of cells stays polynomial in `n`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

namespace HigherDimLFPPAS.Gauss

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

variable {d : ℕ} {κ : Rd d → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistRd d}

/-- `t_n = a log n`. -/
def winTimeF2b (a : ℝ) (n : ℕ) : ℝ := a * Real.log n

/-- `τ_n = a log (n + 1) - a log n`. -/
def winSpanF2b (a : ℝ) (n : ℕ) : ℝ := a * Real.log ((n : ℝ) + 1) - a * Real.log n

/-- The mesh `ℓ_n = e^{-t_n} τ_n`. -/
def winMeshF2b (a : ℝ) (n : ℕ) : ℝ := Real.exp (-winTimeF2b a n) * winSpanF2b a n

lemma winSpanF2b_eq {a : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    winSpanF2b a n = a * Real.log (((n : ℝ) + 1) / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [winSpanF2b, Real.log_div (by positivity) hn0.ne']
  ring

lemma winSpanF2b_pos {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) : 0 < winSpanF2b a n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [winSpanF2b_eq hn]
  refine mul_pos ha (Real.log_pos ?_)
  rw [one_lt_div hn0]
  linarith

lemma winSpanF2b_le {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) : winSpanF2b a n ≤ a / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [winSpanF2b_eq hn]
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
  have he : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
  rw [he] at h
  calc a * Real.log (((n : ℝ) + 1) / n) ≤ a * (1 / n) := mul_le_mul_of_nonneg_left h ha.le
    _ = a / n := by ring

lemma winSpanF2b_ge {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) :
    a / ((n : ℝ) + 1) ≤ winSpanF2b a n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [winSpanF2b_eq hn]
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
  have he : 1 - (((n : ℝ) + 1) / n)⁻¹ = 1 / ((n : ℝ) + 1) := by field_simp; ring
  rw [he] at h
  calc a / ((n : ℝ) + 1) = a * (1 / ((n : ℝ) + 1)) := by ring
    _ ≤ a * Real.log (((n : ℝ) + 1) / n) := mul_le_mul_of_nonneg_left h ha.le

/-- The top index `(t_n + σ τ_n, ℓ_n (k + v))`. -/
def winTopF2b (a : ℝ) (n : ℕ) (k : Fin d → ℤ) (p : Fin (d + 1) → unitInterval) : ℝ × Rd d :=
  (winTimeF2b a n + (p 0 : ℝ) * winSpanF2b a n, cellPtF2b (winMeshF2b a n) k (cubeSpaceF2b p))

/-- The base index `(t_n, ℓ_n (k + v))`. -/
def winBaseF2b (a : ℝ) (n : ℕ) (k : Fin d → ℤ) (p : Fin (d + 1) → unitInterval) : ℝ × Rd d :=
  (winTimeF2b a n, cellPtF2b (winMeshF2b a n) k (cubeSpaceF2b p))

lemma continuous_winTopF2b (a : ℝ) (n : ℕ) (k : Fin d → ℤ) :
    Continuous (winTopF2b (d := d) a n k) :=
  (continuous_const.add ((continuous_subtype_val.comp (continuous_apply 0)).mul
    continuous_const)).prodMk ((continuous_cellPtF2b _ k).comp continuous_cubeSpaceF2b)

lemma continuous_winBaseF2b (a : ℝ) (n : ℕ) (k : Fin d → ℤ) :
    Continuous (winBaseF2b (d := d) a n k) :=
  continuous_const.prodMk ((continuous_cellPtF2b _ k).comp continuous_cubeSpaceF2b)

/-- **The window process** `Y_{n,k}(σ, v) = H_{t_n + σ τ_n}(ℓ_n (k + v)) - H_{t_n}(ℓ_n (k + v))`. -/
def winProcF2b (κ : Rd d → ℝ) (h : Ω → DistRd d) (a : ℝ) (n : ℕ) (k : Fin d → ℤ)
    (p : Fin (d + 1) → unitInterval) (ω : Ω) : ℝ :=
  fieldF2b κ h (winTopF2b a n k p) ω - fieldF2b κ h (winBaseF2b a n k p) ω

/-- `(x + y + z)² ≤ 3 (x² + y² + z²)`. -/
lemma sq_add_add_le_F2b (x y z : ℝ) : (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]

/-- The uniform window increment bound: `E (Y_p - Y_q)² ≤ K τ_n ‖p - q‖_∞`, `E Y_p² ≤ K τ_n`,
for `n ≥ 1` with `τ_n ≤ 1`. -/
theorem exists_win_increment_F2b (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, IsNormalizedLGF h P → ∀ {a : ℝ}, 0 < a → ∀ {n : ℕ}, 1 ≤ n →
        winSpanF2b a n ≤ 1 → ∀ (k : Fin d → ℤ) (p q : Fin (d + 1) → unitInterval),
        (∫ ω, (winProcF2b κ h a n k p ω - winProcF2b κ h a n k q ω) ^ 2 ∂P ≤
          K * winSpanF2b a n * ‖cubeCoordF2b p - cubeCoordF2b q‖) ∧
        ∫ ω, winProcF2b κ h a n k p ω ^ 2 ∂P ≤ K * winSpanF2b a n := by
  obtain ⟨C₃, hC₃0, hC₃⟩ := exists_integral_sq_convMollify_sub_le_F2b hd hκ
  refine ⟨3 * C₃ * (1 + 4 * √d) + 1, by positivity,
    fun {Ω} _ {P} _ {h} hh {a} ha {n} hn hτ1 k p q => ?_⟩
  set τ := winSpanF2b a n with hτ
  set T := winTimeF2b a n with hT
  set ℓ := winMeshF2b a n with hℓ
  have hτ0 : 0 < τ := winSpanF2b_pos ha hn
  have hℓ0 : 0 < ℓ := mul_pos (Real.exp_pos _) hτ0
  set Δ := ‖cubeCoordF2b p - cubeCoordF2b q‖ with hΔ
  have hΔ0 : 0 ≤ Δ := norm_nonneg _
  set xp := cellPtF2b ℓ k (cubeSpaceF2b p) with hxp
  set xq := cellPtF2b ℓ k (cubeSpaceF2b q) with hxq
  set tp := T + (p 0 : ℝ) * τ with htp
  set tq := T + (q 0 : ℝ) * τ with htq
  have hp0 := (p 0).2
  have hq0 := (q 0).2
  have htp1 : |tp - T| ≤ τ := by
    rw [htp, add_sub_cancel_left, abs_of_nonneg (by nlinarith [hp0.1]), mul_comm]
    nlinarith [hp0.2]
  have htq1 : |tq - T| ≤ τ := by
    rw [htq, add_sub_cancel_left, abs_of_nonneg (by nlinarith [hq0.1]), mul_comm]
    nlinarith [hq0.2]
  have hpq : |tp - tq| ≤ τ * Δ := by
    have : tp - tq = ((p 0 : ℝ) - (q 0 : ℝ)) * τ := by rw [htp, htq]; ring
    rw [this, abs_mul, abs_of_pos hτ0, mul_comm]
    exact mul_le_mul_of_nonneg_left (abs_sub_le_cubeCoord p q 0) hτ0.le
  have hpq1 : |tp - tq| ≤ 1 := by
    have : tp - tq = ((p 0 : ℝ) - (q 0 : ℝ)) * τ := by rw [htp, htq]; ring
    rw [this, abs_mul, abs_of_pos hτ0]
    have h1 : |(p 0 : ℝ) - (q 0 : ℝ)| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [hp0.1, hp0.2, hq0.1, hq0.2]
    nlinarith [abs_nonneg ((p 0 : ℝ) - (q 0 : ℝ))]
  -- the spatial displacement
  have hx : ‖xp - xq‖ ≤ √d * (ℓ * Δ) :=
    (norm_cellPtF2b_sub_le hℓ0.le k _ _).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_cubeSpace_sub_le p q) hℓ0.le)
        (Real.sqrt_nonneg _))
  have hexpT : Real.exp T * ℓ = τ := by
    rw [hℓ, winMeshF2b, ← hT, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
      one_mul]
  have hmaxq : max tq tq = tq := max_self _
  have hmaxT : max T T = T := max_self _
  have htqT : tq ≤ T + 1 := by
    have := (abs_le.mp htq1).2
    linarith
  have hsp1 : Real.exp (max tq tq) * ‖xp - xq‖ ≤ 3 * √d * τ * Δ := by
    rw [hmaxq]
    have he : Real.exp tq ≤ 3 * Real.exp T := by
      calc Real.exp tq ≤ Real.exp (T + 1) := Real.exp_le_exp.2 htqT
        _ = Real.exp T * Real.exp 1 := Real.exp_add _ _
        _ ≤ Real.exp T * 3 := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
            have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
        _ = 3 * Real.exp T := by ring
    calc Real.exp tq * ‖xp - xq‖ ≤ (3 * Real.exp T) * (√d * (ℓ * Δ)) :=
          mul_le_mul he hx (norm_nonneg _) (by positivity)
      _ = 3 * √d * (Real.exp T * ℓ) * Δ := by ring
      _ = 3 * √d * τ * Δ := by rw [hexpT]
  have hsp2 : Real.exp (max T T) * ‖xp - xq‖ ≤ √d * τ * Δ := by
    rw [hmaxT]
    calc Real.exp T * ‖xp - xq‖ ≤ Real.exp T * (√d * (ℓ * Δ)) :=
          mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le
      _ = √d * (Real.exp T * ℓ) * Δ := by ring
      _ = √d * τ * Δ := by rw [hexpT]
  -- the three moments
  have m1 := hC₃ hh tp tq hpq1 xp xp
  have m2 := hC₃ hh tq tq (by simp) xp xq
  have m3 := hC₃ hh T T (by simp) xp xq
  have m4 := hC₃ hh tp T (htp1.trans hτ1) xp xp
  simp only [sub_self, norm_zero, mul_zero, add_zero, abs_zero, zero_add] at m1 m2 m3 m4
  -- integrability of the pieces
  have hG := isGaussianProcess_fieldF2b hd hκ hh
  have hmem : ∀ r : ℝ × Rd d, MemLp (fieldF2b κ h r) 2 P := fun r =>
    (hG.hasGaussianLaw_eval r).memLp_two
  constructor
  · have hdecomp : ∀ ω, winProcF2b κ h a n k p ω - winProcF2b κ h a n k q ω =
        (convMollify κ (Real.exp (-tp)) (h ω) xp - convMollify κ (Real.exp (-tq)) (h ω) xp) +
        (convMollify κ (Real.exp (-tq)) (h ω) xp - convMollify κ (Real.exp (-tq)) (h ω) xq) +
        -(convMollify κ (Real.exp (-T)) (h ω) xp - convMollify κ (Real.exp (-T)) (h ω) xq) := by
      intro ω
      simp only [winProcF2b, fieldF2b, winTopF2b, winBaseF2b]
      ring
    have i1 : Integrable (fun ω => (convMollify κ (Real.exp (-tp)) (h ω) xp -
        convMollify κ (Real.exp (-tq)) (h ω) xp) ^ 2) P :=
      ((hmem (tp, xp)).sub (hmem (tq, xp))).integrable_sq
    have i2 : Integrable (fun ω => (convMollify κ (Real.exp (-tq)) (h ω) xp -
        convMollify κ (Real.exp (-tq)) (h ω) xq) ^ 2) P :=
      ((hmem (tq, xp)).sub (hmem (tq, xq))).integrable_sq
    have i3 : Integrable (fun ω => (convMollify κ (Real.exp (-T)) (h ω) xp -
        convMollify κ (Real.exp (-T)) (h ω) xq) ^ 2) P :=
      ((hmem (T, xp)).sub (hmem (T, xq))).integrable_sq
    have i12 : Integrable (fun ω => (convMollify κ (Real.exp (-tp)) (h ω) xp -
        convMollify κ (Real.exp (-tq)) (h ω) xp) ^ 2 +
        (convMollify κ (Real.exp (-tq)) (h ω) xp -
        convMollify κ (Real.exp (-tq)) (h ω) xq) ^ 2) P := i1.add i2
    have i123 : Integrable (fun ω => (convMollify κ (Real.exp (-tp)) (h ω) xp -
        convMollify κ (Real.exp (-tq)) (h ω) xp) ^ 2 +
        (convMollify κ (Real.exp (-tq)) (h ω) xp -
        convMollify κ (Real.exp (-tq)) (h ω) xq) ^ 2 +
        (convMollify κ (Real.exp (-T)) (h ω) xp -
        convMollify κ (Real.exp (-T)) (h ω) xq) ^ 2) P := i12.add i3
    calc ∫ ω, (winProcF2b κ h a n k p ω - winProcF2b κ h a n k q ω) ^ 2 ∂P
        ≤ ∫ ω, 3 * ((convMollify κ (Real.exp (-tp)) (h ω) xp -
              convMollify κ (Real.exp (-tq)) (h ω) xp) ^ 2 +
            (convMollify κ (Real.exp (-tq)) (h ω) xp -
              convMollify κ (Real.exp (-tq)) (h ω) xq) ^ 2 +
            (convMollify κ (Real.exp (-T)) (h ω) xp -
              convMollify κ (Real.exp (-T)) (h ω) xq) ^ 2) ∂P := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
            (i123.const_mul 3) (Eventually.of_forall fun ω => ?_)
          dsimp only
          rw [hdecomp ω]
          have := sq_add_add_le_F2b
            (convMollify κ (Real.exp (-tp)) (h ω) xp - convMollify κ (Real.exp (-tq)) (h ω) xp)
            (convMollify κ (Real.exp (-tq)) (h ω) xp - convMollify κ (Real.exp (-tq)) (h ω) xq)
            (-(convMollify κ (Real.exp (-T)) (h ω) xp - convMollify κ (Real.exp (-T)) (h ω) xq))
          simpa only [neg_sq] using this
      _ = 3 * ((∫ ω, (convMollify κ (Real.exp (-tp)) (h ω) xp -
              convMollify κ (Real.exp (-tq)) (h ω) xp) ^ 2 ∂P) +
            (∫ ω, (convMollify κ (Real.exp (-tq)) (h ω) xp -
              convMollify κ (Real.exp (-tq)) (h ω) xq) ^ 2 ∂P) +
            ∫ ω, (convMollify κ (Real.exp (-T)) (h ω) xp -
              convMollify κ (Real.exp (-T)) (h ω) xq) ^ 2 ∂P) := by
          rw [integral_const_mul, integral_add i12 i3, integral_add i1 i2]
      _ ≤ 3 * (C₃ * (τ * Δ) + C₃ * (3 * √d * τ * Δ) + C₃ * (√d * τ * Δ)) := by
          gcongr
          · exact m1.trans (mul_le_mul_of_nonneg_left hpq hC₃0)
          · exact m2.trans (mul_le_mul_of_nonneg_left hsp1 hC₃0)
          · exact m3.trans (mul_le_mul_of_nonneg_left hsp2 hC₃0)
      _ ≤ (3 * C₃ * (1 + 4 * √d) + 1) * τ * Δ := by
          have : 0 ≤ τ * Δ := mul_nonneg hτ0.le hΔ0
          nlinarith
  · have he : (fun ω => winProcF2b κ h a n k p ω ^ 2) = fun ω =>
        (convMollify κ (Real.exp (-tp)) (h ω) xp - convMollify κ (Real.exp (-T)) (h ω) xp) ^ 2 := by
      funext ω
      rfl
    rw [he]
    refine m4.trans ?_
    have hc : C₃ ≤ 3 * C₃ * (1 + 4 * √d) + 1 := by nlinarith [Real.sqrt_nonneg (d : ℝ)]
    calc C₃ * |tp - T| ≤ C₃ * τ := mul_le_mul_of_nonneg_left htp1 hC₃0
      _ ≤ (3 * C₃ * (1 + 4 * √d) + 1) * τ := mul_le_mul_of_nonneg_right hc hτ0.le

/-- **Uniform Gaussian tail of the window suprema.** -/
theorem exists_win_sup_tail_F2b (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, IsNormalizedLGF h P → ∀ {a : ℝ}, 0 < a → ∀ {n : ℕ}, 1 ≤ n →
        winSpanF2b a n ≤ 1 → ∀ (k : Fin d → ℤ) {x : ℝ}, 0 ≤ x →
        P.real {ω | x ≤ ⨆ p, |winProcF2b κ h a n k p ω|} ≤
          2 * Real.exp (1000 * ((d : ℝ) + 2)) *
            Real.exp (-x ^ 2 / (2 * (2 * (K * winSpanF2b a n)))) := by
  obtain ⟨K, hK0, hK⟩ := exists_win_increment_F2b hd hκ
  refine ⟨K, hK0, fun {Ω} _ {P} _ {h} hh {a} ha {n} hn hτ1 k x hx => ?_⟩
  have hτ0 := winSpanF2b_pos ha hn
  set L : ℝ := √(K * winSpanF2b a n) with hLdef
  have hL0 : 0 < L := Real.sqrt_pos.2 (mul_pos hK0 hτ0)
  have hL2 : L ^ 2 = K * winSpanF2b a n := Real.sq_sqrt (mul_pos hK0 hτ0).le
  have hG : IsGaussianProcess (winProcF2b κ h a n k) P :=
    isGaussianProcess_fieldDiff_F2b hd hκ hh (winTopF2b a n k) (winBaseF2b a n k)
  have h0 : ∀ p, ∫ ω, winProcF2b κ h a n k p ω ∂P = 0 := fun p =>
    integral_fieldDiff_F2b hd hκ hh _ _
  have hc : ∀ᵐ ω ∂P, Continuous fun p => winProcF2b κ h a n k p ω := by
    filter_upwards [ae_continuous_fieldF2b hd hκ hh] with ω hω
    exact (hω.comp (continuous_winTopF2b a n k)).sub (hω.comp (continuous_winBaseF2b a n k))
  have hinc : ∀ p q, ∫ ω, (winProcF2b κ h a n k p ω - winProcF2b κ h a n k q ω) ^ 2 ∂P ≤
      L ^ 2 * ‖cubeCoordF2b p - cubeCoordF2b q‖ := fun p q => by
    rw [hL2]
    exact (hK hh ha hn hτ1 k p q).1
  have hvar : ∀ p, Var[winProcF2b κ h a n k p; P] ≤ L ^ 2 := by
    intro p
    refine (variance_le_expectation_sq (hG.aemeasurable p).aestronglyMeasurable).trans ?_
    rw [hL2]
    exact (hK hh ha hn hτ1 k p p).2
  have ht := cube_sup_tail_F2b hG h0 hc hL0.le hinc hvar hx
  have hconst : (20 * √5 * L * √((((d + 1 : ℕ) : ℝ) + 1) * 1)) ^ 2 / (2 * L ^ 2) =
      1000 * ((d : ℝ) + 2) := by
    have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hd2 : √((((d + 1 : ℕ) : ℝ) + 1) * 1) ^ 2 = (d : ℝ) + 2 := by
      rw [Real.sq_sqrt (by positivity)]
      push_cast
      ring
    rw [mul_pow, mul_pow, mul_pow, h5, hd2]
    field_simp
    ring
  rw [hconst, hL2] at ht
  exact ht

end HigherDimLFPPAS.Gauss
