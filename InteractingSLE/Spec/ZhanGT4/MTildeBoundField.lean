/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.MTildeBound

/-!
# (D9) for `M̃`: the log-field of `M̃` on a frozen-center piece, with an explicit uniform bound

Packet PROVE-ZHAN-GT4-A7. Source: Astra, *Follow-up proofs*, §A.1.3 (`ig1_followup_proofs.txt` L300–L341, R38).

Given the (D9) constants of the protected rectangle on `[0, T]` (`FrzData.D9Const`: a clearance `r` of the frozen hull's
image from the driver, `A_{j,1} ≥ a₀`, the separations `γ ≤ |E|, |E_{j,m}|, |E_{k,m}|, |C_{mn}| ≤ Γ`, and
`A_{k,1}, B_{m,1}/φ'(p_m) ∈ [e^{−λ}, e^λ]` — all supplied by PROVE-ZHAN-GT4-A6's `D9*` theorems) and any scale `L`
satisfying the numerical conditions `ScaleOK`, on every time piece `[b, c]` on which the driver stays within
`ρ_c = cutRad r a₀ γ` of a center `y`:

* `FrzData.isLogField_of_D9`: `log M̃` is a regular log-field (`IsLogField`) on `[b, c] × (y − 3ρ_c, y + 3ρ_c)` with
  the explicit bound `K = 2 · coefTot κ r · scaleBound L` — independent of the driver, the piece and the center;
* `FrzData.cutField_gen_eq_zero_of_D9`: the generator of the cut-off field vanishes at the driver.

Together with `IsLogField.scaled` these are all the pathwise hypotheses of the A5 stopped Itô theorem
(`Ito.integral_mul_fieldStopped_sub_eq_zero`) for `M̃`, with constants uniform over the paths.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped Interval

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H Hbar IsForwardSol fwdMap fwdMapInv fwdHull logDerivFwd)

theorem cutRad_pos {r a₀ γ : ℝ} (hr : 0 < r) (ha₀ : 0 < a₀) (hγ : 0 < γ) : 0 < cutRad r a₀ γ :=
  lt_min (by have := clrRad_pos hr ha₀; positivity) (by positivity)

namespace FrzData

variable {n : ℕ} (d : FrzData n)

/-- **The (D9) constants on `[0, T]`** for the frozen data `d` and the frozen hull `A`. -/
structure D9Const (A : Set ℂ) (T r a₀ γ Γ lam : ℝ) : Prop where
  r0 : 0 < r
  a0 : 0 < a₀
  g0 : 0 < γ
  clr : ∀ t ∈ Icc (0 : ℝ) T, Disjoint (ball (d.W t : ℂ) r) ((fun z => fwdMap d.W t z + d.W t) '' A)
  A1 : ∀ t ∈ Icc (0 : ℝ) T, a₀ ≤ d.A 1 t
  E0 : ∀ t ∈ Icc (0 : ℝ) T, γ ≤ |d.A20 t - d.A 0 t| ∧ |d.A20 t - d.A 0 t| ≤ Γ
  Em : ∀ t ∈ Icc (0 : ℝ) T, ∀ m, γ ≤ |d.B0 t m - d.A 0 t| ∧ |d.B0 t m - d.A 0 t| ≤ Γ
  E2m : ∀ t ∈ Icc (0 : ℝ) T, ∀ m, γ ≤ |d.A20 t - d.B0 t m| ∧ |d.A20 t - d.B0 t m| ≤ Γ
  Cmk : ∀ t ∈ Icc (0 : ℝ) T, ∀ m k, m ≠ k → γ ≤ |d.B0 t m - d.B0 t k| ∧ |d.B0 t m - d.B0 t k| ≤ Γ
  A21 : ∀ t ∈ Icc (0 : ℝ) T, InScale lam (d.A21 t)
  B1 : ∀ t ∈ Icc (0 : ℝ) T, ∀ m, InScale lam (d.B1 t m)

variable {A : Set ℂ} {T : ℝ} (h : OwnData d.W A d.φ T d.a d.W')
  {v₀ : ℝ → ℂ} (hv₀ : IsForwardSol d.W' d.ζ₀ (d.a T) v₀) {v : Fin n → ℝ → ℂ}
  (hv : ∀ m, IsForwardSol d.W' (d.ζ m) (d.a T) (v m)) (hζ₀ : ∀ m, d.ζ m ≠ d.ζ₀) (hζ : Function.Injective d.ζ)
  {r a₀ γ Γ lam L : ℝ}

omit d in
theorem inScale_mono {L L' u : ℝ} (h : InScale L u) (hLL : L ≤ L') : InScale L' u :=
  ⟨(Real.exp_le_exp.2 (by linarith)).trans h.1, h.2.trans (Real.exp_le_exp.2 hLL)⟩

omit d in
theorem inScale_of_le {L γ Γ u : ℝ} (hγ : Real.exp (-L) ≤ γ) (hΓ : Γ ≤ Real.exp L) (h : γ ≤ |u| ∧ |u| ≤ Γ) :
    InScale L u :=
  ⟨hγ.trans h.1, h.2.trans hΓ⟩

include h in
/-- `0 < A_{j,1} ≤ 1` and `|A_{j,2}| ≤ 384/r`, `|A_{j,3}| ≤ 3072/r²` at every time (D9 at the driver). -/
theorem driver_bounds (hc : d.D9Const A T r a₀ γ Γ lam) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    a₀ ≤ d.A 1 t ∧ d.A 1 t ≤ 1 ∧ |d.A 2 t| ≤ 384 / r ∧ |d.A 3 t| ≤ 3072 / r ^ 2 := by
  have hW : (d.W t : ℂ) ∈ ball (d.W t : ℂ) (r / 8) := mem_ball_self (by have := hc.r0; positivity)
  refine ⟨hc.A1 t ht, (h.deriv_ownExt_driver ht hc.r0 (hc.clr t ht)).2.2, ?_, ?_⟩
  · exact (abs_re_le_norm _).trans (h.norm_deriv2_ownExt_le ht (hc.clr t ht) (ball_subset_ball (by
      have := hc.r0; linarith) hW))
  · exact (abs_re_le_norm _).trans (h.norm_deriv3_ownExt_le ht (hc.clr t ht) hW)

include h in
theorem abs_frzRate_le (hc : d.D9Const A T r a₀ γ Γ lam) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    |frzRate d.W d.W' d.a d.φ t| ≤ rateBound r a₀ := by
  obtain ⟨h1, -, h2, h3⟩ := d.driver_bounds h hc ht
  have ha := hc.a0
  have hr := hc.r0
  have hA1 : 0 < d.A 1 t := lt_of_lt_of_le ha h1
  have q2 : |d.A 2 t / d.A 1 t| ≤ 384 / (r * a₀) := by
    rw [abs_div, abs_of_pos hA1, div_le_div_iff₀ hA1 (by positivity)]
    calc |d.A 2 t| * (r * a₀) ≤ 384 / r * (r * a₀) := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = 384 * a₀ := by field_simp
      _ ≤ 384 * d.A 1 t := by linarith
  have q3 : |d.A 3 t / d.A 1 t| ≤ 3072 / (r ^ 2 * a₀) := by
    rw [abs_div, abs_of_pos hA1, div_le_div_iff₀ hA1 (by positivity)]
    calc |d.A 3 t| * (r ^ 2 * a₀) ≤ 3072 / r ^ 2 * (r ^ 2 * a₀) := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = 3072 * a₀ := by field_simp
      _ ≤ 3072 * d.A 1 t := by linarith
  have e : frzRate d.W d.W' d.a d.φ t = 1 / 4 * (d.A 2 t / d.A 1 t) ^ 2 - 1 / 6 * (d.A 3 t / d.A 1 t) := rfl
  rw [e, rateBound]
  have s2 : (d.A 2 t / d.A 1 t) ^ 2 ≤ (384 / (r * a₀)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) q2 2
  calc |1 / 4 * (d.A 2 t / d.A 1 t) ^ 2 - 1 / 6 * (d.A 3 t / d.A 1 t)|
      ≤ |1 / 4 * (d.A 2 t / d.A 1 t) ^ 2| + |1 / 6 * (d.A 3 t / d.A 1 t)| := abs_sub _ _
    _ ≤ 1 / 4 * (384 / (r * a₀)) ^ 2 + 1 / 6 * (3072 / (r ^ 2 * a₀)) := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4),
          abs_of_pos (by norm_num : (0 : ℝ) < 1 / 6), abs_of_nonneg (sq_nonneg _)]
        linarith

include h in
/-- The time inputs of the formal bounds at scale `L`. -/
theorem time_inputs (hc : d.D9Const A T r a₀ γ Γ lam) (hL : ScaleOK r a₀ γ Γ lam T L) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    InScale L (d.A21 t) ∧ (∀ m, InScale L (d.B1 t m)) ∧ (∀ m, InScale L (d.A20 t - d.B0 t m)) ∧
      (∀ m k, m ≠ k → InScale L (d.B0 t m - d.B0 t k)) ∧ |frzLogF d.W d.W' d.a d.φ t| ≤ Real.exp L ∧
      |d.dA21 t| ≤ Real.exp L ∧ |frzRate d.W d.W' d.a d.φ t| ≤ Real.exp L ∧ |d.dA20 t| ≤ Real.exp L ∧
      (∀ m, |d.dB0 t m| ≤ Real.exp L) ∧ (∀ m, |d.dB1 t m| ≤ Real.exp L) := by
  have hγ := hc.g0
  have hlo : Real.exp (-L) ≤ γ := hL.g.trans (by linarith)
  have hhi : Γ ≤ Real.exp L := le_trans (by linarith) hL.G
  obtain ⟨ha1, ha1', -, -⟩ := d.driver_bounds h hc ht
  have hA1p : 0 < d.A 1 t := lt_of_lt_of_le hc.a0 ha1
  have hA1sq : d.A 1 t ^ 2 ≤ 1 := by nlinarith
  -- `2A₁²X/E` with `|E| ≥ γ'`
  have frac : ∀ (X E : ℝ) (B : ℝ), |X| ≤ B → γ ≤ |E| → |2 * d.A 1 t ^ 2 * X / E| ≤ 2 * B / γ := fun X E B hX hE => by
    have hE0 : 0 < |E| := lt_of_lt_of_le hγ hE
    rw [abs_div, div_le_div_iff₀ hE0 hγ, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_nonneg (sq_nonneg _)]
    have hB : 0 ≤ B := (abs_nonneg _).trans hX
    calc 2 * d.A 1 t ^ 2 * |X| * γ ≤ 2 * 1 * B * γ := by gcongr
      _ ≤ 2 * B * |E| := by nlinarith
  have frac2 : ∀ (X E : ℝ), |X| ≤ Real.exp lam → γ ≤ |E| →
      |-2 * d.A 1 t ^ 2 * X / E ^ 2| ≤ Real.exp L := fun X E hX hE => by
    have hE0 : 0 < |E| := lt_of_lt_of_le hγ hE
    have hE2 : γ ^ 2 ≤ E ^ 2 := by rw [← sq_abs E]; exact pow_le_pow_left₀ hγ.le hE 2
    have hE2p : 0 < E ^ 2 := by rw [← sq_abs]; positivity
    refine le_trans ?_ hL.gl
    rw [abs_div, abs_of_nonneg (sq_nonneg E), div_le_div_iff₀ hE2p (by positivity), abs_mul, abs_mul, abs_neg,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg (sq_nonneg _)]
    have hel := (Real.exp_pos lam).le
    calc 2 * d.A 1 t ^ 2 * |X| * γ ^ 2 ≤ 2 * 1 * Real.exp lam * γ ^ 2 := by gcongr
      _ ≤ 2 * Real.exp lam * E ^ 2 := by nlinarith
  refine ⟨inScale_mono (hc.A21 t ht) hL.la, fun m => inScale_mono (hc.B1 t ht m) hL.la,
    fun m => inScale_of_le hlo hhi (hc.E2m t ht m), fun m k hmk => inScale_of_le hlo hhi (hc.Cmk t ht m k hmk),
    ?_, ?_, (d.abs_frzRate_le h hc ht).trans hL.rate, ?_, fun m => ?_, fun m => ?_⟩
  · have hb : ∀ u ∈ Ι (0 : ℝ) t, ‖frzRate d.W d.W' d.a d.φ u‖ ≤ rateBound r a₀ := fun u hu => by
      rw [uIoc_of_le ht.1] at hu
      exact d.abs_frzRate_le h hc ⟨hu.1.le, hu.2.trans ht.2⟩
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] at this
    refine this.trans (le_trans ?_ hL.logF)
    have : 0 ≤ rateBound r a₀ := (abs_nonneg _).trans (d.abs_frzRate_le h hc ht)
    nlinarith [ht.2]
  · have := frac2 (d.A21 t) (d.A20 t - d.A 0 t) (hc.A21 t ht).2 (hc.E0 t ht).1
    exact this
  · refine (frac 1 (d.A20 t - d.A 0 t) 1 (by simp) (hc.E0 t ht).1).trans ?_ |>.trans' (le_of_eq (by
      simp only [FrzData.dA20]; ring_nf))
    exact (show 2 * 1 / γ = 2 / γ by ring).le.trans hL.g2
  · refine (frac 1 (d.B0 t m - d.A 0 t) 1 (by simp) (hc.Em t ht m).1).trans ?_ |>.trans' (le_of_eq (by
      simp only [FrzData.dB0]; ring_nf))
    exact (show 2 * 1 / γ = 2 / γ by ring).le.trans hL.g2
  · exact frac2 (d.B1 t m) (d.B0 t m - d.A 0 t) (hc.B1 t ht m).2 (hc.Em t ht m).1

/-! ### The log-field on a frozen-center piece -/

section Piece

variable {b c y : ℝ} (hJ : Icc b c ⊆ Icc 0 T)

omit d in
theorem cutRad_le {r a₀ γ : ℝ} : cutRad r a₀ γ ≤ clrRad r a₀ / 24 ∧ cutRad r a₀ γ ≤ γ / 768 :=
  ⟨min_le_left _ _, min_le_right _ _⟩

include h hJ in
/-- **The box hypotheses and the space inputs on a frozen-center piece.** -/
theorem piece_facts (hc : d.D9Const A T r a₀ γ Γ lam) (hL : ScaleOK r a₀ γ Γ lam T L)
    (hWy : ∀ t ∈ Icc b c, |d.W t - y| < cutRad r a₀ γ) :
    (∀ t ∈ Icc b c, Disjoint (ball (y : ℂ) (2 * (clrRad r a₀ / 8))) ((fun z => fwdMap d.W t z + d.W t) '' A)) ∧
    (∀ t ∈ Icc b c, (d.W t : ℂ) ∈ ball (y : ℂ) (clrRad r a₀ / 8)) ∧
    (∀ t ∈ Icc b c, ∀ z ∈ ball (y : ℂ) (clrRad r a₀ / 8), dslope (ownExt d.W d.W' d.a d.φ t) (d.W t) z ≠ 0) ∧
    3 * cutRad r a₀ γ ≤ clrRad r a₀ / 8 ∧
    ∀ t ∈ Icc b c, ∀ x : ℝ, |x - y| < 3 * cutRad r a₀ γ →
      InScale L (d.F 1 t x) ∧ InScale L (d.F 0 t x - d.A20 t) ∧ (∀ m, InScale L (d.F 0 t x - d.B0 t m)) ∧
      |d.F 2 t x| ≤ Real.exp L ∧ |d.F 3 t x| ≤ Real.exp L ∧ |d.F 4 t x| ≤ Real.exp L ∧
      |(dHat (ownExt d.W d.W' d.a d.φ t) (d.W t) x).re| ≤ Real.exp L ∧
      |(deriv (dHat (ownExt d.W d.W' d.a d.φ t) (d.W t)) x).re| ≤ Real.exp L := by
  have hr := hc.r0
  have ha := hc.a0
  have hγ := hc.g0
  set ρ := clrRad r a₀ with hρ
  set ρc := cutRad r a₀ γ with hρc
  have hρp : 0 < ρ := clrRad_pos hr ha
  obtain ⟨hc1, hc2⟩ := cutRad_le (r := r) (a₀ := a₀) (γ := γ)
  have hWy' : ∀ t ∈ Icc b c, |d.W t - y| < ρ / 24 := fun t ht => lt_of_lt_of_le (hWy t ht) hc1
  obtain ⟨hdisj, hWm, hq0, hloc⟩ := h.box_of_clearance hr ha hc.clr hc.A1 hJ hWy'
  have h3 : 3 * ρc ≤ ρ / 8 := by linarith
  refine ⟨hdisj, hWm, hq0, h3, fun t ht x hx => ?_⟩
  have hxb : (x : ℂ) ∈ ball (y : ℂ) (ρ / 8) := mem_ball_of_near h3 hx
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := hloc t ht x hxb
  have hlo : Real.exp (-L) ≤ γ / 2 := hL.g
  -- `|F_t(x) − F_t(W_t)| ≤ γ/2`
  have hxW : ‖(x : ℂ) - d.W t‖ ≤ 4 * ρc := by
    rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have := hWy t ht
    calc |x - d.W t| = |(x - y) - (d.W t - y)| := by ring_nf
      _ ≤ |x - y| + |d.W t - y| := abs_sub _ _
      _ ≤ 4 * ρc := by linarith
  have hF0 : |d.F 0 t x - d.A 0 t| ≤ γ / 2 := by
    have e : d.F 0 t x - d.A 0 t = (ownExt d.W d.W' d.a d.φ t x - ownExt d.W d.W' d.a d.φ t (d.W t)).re := by
      simp [FrzData.F, FrzData.A, frzA]
    rw [e]
    calc _ ≤ ‖ownExt d.W d.W' d.a d.φ t x - ownExt d.W d.W' d.a d.φ t (d.W t)‖ := abs_re_le_norm _
      _ ≤ 96 * ‖(x : ℂ) - d.W t‖ := l6
      _ ≤ 96 * (4 * ρc) := by gcongr
      _ ≤ γ / 2 := by linarith
  have sep : ∀ E : ℝ, γ ≤ |E - d.A 0 t| ∧ |E - d.A 0 t| ≤ Γ → InScale L (d.F 0 t x - E) := fun E hE => by
    refine ⟨hlo.trans ?_, ?_⟩
    · have : |E - d.A 0 t| ≤ |d.F 0 t x - E| + |d.F 0 t x - d.A 0 t| := by
        calc |E - d.A 0 t| = |(d.F 0 t x - d.A 0 t) - (d.F 0 t x - E)| := by ring_nf
          _ ≤ |d.F 0 t x - d.A 0 t| + |d.F 0 t x - E| := abs_sub _ _
          _ = _ := by ring
      linarith [hE.1]
    · calc |d.F 0 t x - E| = |(d.F 0 t x - d.A 0 t) - (E - d.A 0 t)| := by ring_nf
        _ ≤ |d.F 0 t x - d.A 0 t| + |E - d.A 0 t| := abs_sub _ _
        _ ≤ γ / 2 + Γ := add_le_add hF0 hE.2
        _ ≤ Real.exp L := by linarith [hL.G]
  refine ⟨⟨hL.a.trans (l1.trans (le_abs_self _)), (abs_re_le_norm _).trans (l2.trans hL.c96)⟩,
    sep _ (hc.E0 t (hJ ht)), fun m => sep _ (hc.Em t (hJ ht) m), (abs_re_le_norm _).trans (l3.trans hL.r2),
    (abs_re_le_norm _).trans (l4.trans hL.r3), (abs_re_le_norm _).trans (l5.trans hL.r4),
    (abs_re_le_norm _).trans (l7.trans hL.D), (abs_re_le_norm _).trans (l8.trans hL.D')⟩

include h hv₀ hv hζ₀ hζ hJ in
/-- **(D9) for the field: `log M̃` is a regular log-field on a frozen-center piece**, with the explicit bound
`K = 2 · coefTot κ r · scaleBound L`. -/
theorem isLogField_of_D9 (hc : d.D9Const A T r a₀ γ Γ lam) (hL : ScaleOK r a₀ γ Γ lam T L)
    (hWy : ∀ t ∈ Icc b c, |d.W t - y| < cutRad r a₀ γ) :
    IsLogField d.ell d.LSX d.LSXX d.LSXXX d.ellT b c y (cutRad r a₀ γ) (2 * coefTot d.κ d.r * scaleBound L) := by
  obtain ⟨hdisj, hWm, hq0, h3, hsp⟩ := d.piece_facts h hJ hc hL hWy
  have hL0 := hL.L0
  have hcT := (coefTot_ge (κ := d.κ) (r := d.r)).2.2.2
  have hSB : 0 ≤ scaleBound L := hL0.trans (le_scaleBound hL0).1
  have hKK : coefTot d.κ d.r * scaleBound L ≤ 2 * coefTot d.κ d.r * scaleBound L := by nlinarith
  have hnd : ∀ t ∈ Icc b c, ∀ x : ℝ, |x - y| < 3 * cutRad r a₀ γ →
      d.F 1 t x ≠ 0 ∧ d.F 0 t x - d.A20 t ≠ 0 ∧ ∀ m, d.F 0 t x - d.B0 t m ≠ 0 := fun t ht x hx => by
    obtain ⟨s1, s0, sm, -⟩ := hsp t ht x hx
    have nz : ∀ u, InScale L u → u ≠ 0 := fun u hu h0 => by
      have := lt_of_lt_of_le (Real.exp_pos _) hu.1; rw [h0, abs_zero] at this; exact lt_irrefl _ this
    exact ⟨nz _ s1, nz _ s0, fun m => nz _ (sm m)⟩
  refine d.isLogField h hv₀ hv hζ₀ hζ hJ hdisj hWm hq0 h3 hnd (cutRad_pos hc.r0 hc.a0 hc.g0) (by positivity)
    fun t ht x hx => ?_
  obtain ⟨s1, s0, sm, s2, s3, s4, sD, sD'⟩ := hsp t ht x hx
  obtain ⟨-, -, -, -, -, -, -, t20, tB0, -⟩ := d.time_inputs h hc hL (hJ ht)
  obtain ⟨t21, tB1, t2m, tmk, tlF, td21, tdL, -, -, tdB1⟩ := d.time_inputs h hc hL (hJ ht)
  obtain ⟨b0, b1, b2, b3, bT⟩ := abs_dualLogSpace_le (κ := d.κ) (r := d.r) hL0 s1 s0 sm s2 s3 s4 sD sD' t20 tB0
  obtain ⟨c0, cT⟩ := abs_dualLogTime_le (κ := d.κ) (r := d.r) (lF := frzLogF d.W d.W' d.a d.φ t) (B0 := d.B0 t)
    hL0 t21 tB1 t2m tmk tlF td21 tdL t20 tB0 tdB1
  refine ⟨?_, b1.trans hKK, b2.trans hKK, b3.trans hKK, ?_⟩
  · calc |d.ell t x| ≤ |d.LT t| + |d.LS t x| := abs_add_le _ _
      _ ≤ coefTot d.κ d.r * scaleBound L + coefTot d.κ d.r * scaleBound L := add_le_add c0 b0
      _ = 2 * coefTot d.κ d.r * scaleBound L := by ring
  · calc |d.ellT t x| ≤ |d.LTT t| + |d.LST t x| := abs_add_le _ _
      _ ≤ coefTot d.κ d.r * scaleBound L + coefTot d.κ d.r * scaleBound L := add_le_add cT bT
      _ = 2 * coefTot d.κ d.r * scaleBound L := by ring

include h hv₀ hv hζ₀ hζ hJ in
/-- **The cut-off generator vanishes at the driver** on a frozen-center piece ((D9) version of
`FrzData.cutField_gen_eq_zero`). -/
theorem cutField_gen_eq_zero_of_D9 (hκ : d.κ ≠ 0) (hc : d.D9Const A T r a₀ γ Γ lam)
    (hL : ScaleOK r a₀ γ Γ lam T L) (hWy : ∀ t ∈ Icc b c, |d.W t - y| < cutRad r a₀ γ) {t : ℝ}
    (ht : t ∈ Icc b c) :
    cutFieldT d.ell d.ellT y (cutRad r a₀ γ) t (d.W t) +
      d.κ / 2 * cutField2 d.ell d.LSX d.LSXX y (cutRad r a₀ γ) t (d.W t) = 0 := by
  obtain ⟨hdisj, hWm, hq0, -, -⟩ := d.piece_facts h hJ hc hL hWy
  exact d.cutField_gen_eq_zero h hv₀ hv hζ₀ hζ hJ hdisj hWm hq0 hκ (cutRad_pos hc.r0 hc.a0 hc.g0) ht (hWy t ht)

end Piece

end FrzData

end InteractingSLE.ZhanGT4
