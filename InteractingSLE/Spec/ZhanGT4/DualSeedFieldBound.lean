/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFieldBox
import InteractingSLE.Spec.ZhanGT4.MTildeBoundField

/-!
# Zhan's A.1.6, the seeded field V: the log-field on a frozen-center piece with explicit constants

Packet PROVE-ZHAN-GT4-A20. Source: Astra, *Follow-up proofs*, §A.1.3 and §A.1.6 (`source/external/AstraIG1/
ig1_followup_proofs.txt` L300–L341, L426–L500, R38): "(D9) … bounded above and below on the protected rectangle"; for
the seeded factors, "the identity extends to time zero by bounded convergence on a protected rectangle" — so the Itô
step is done after a positive time `ε` and up to the first time a gap of the seeded configuration gets small.

`SeedConst` collects the constants of such a cut-off piece `[ε, T]`: A7's (D9) constants for the driver (the clearance
`r` of the frozen hull image, `A_{j,1} ≥ a₀`, on `[0, T]`), a clearance `ρ_m` of the frozen hull image from every
own-chart mark, and on `[ε, T]` the separations `γ ≤ |·| ≤ Γ` of the image-chart positions (`A_{j,0}`, `A_{k,0}`,
`B_{m,0}`) and of the own-chart positions (`W`, `V⁰`, `V^m`), and `A_{k,1}/G⁰`, `B_{m,1} ∈ [e^{−λ}, e^λ]`.
`SeedScaleOK` is A7's `ScaleOK` plus the two conditions for the own-chart rates `2/(V − W)²`.

## Main results

* `SeedData.timeNd_of_const`: the time factors do not degenerate on `[ε, T]`;
* `SeedData.time_bounds_y`, `SeedData.time_bounds_0`: the formal bounds of the two time parts and their derivatives;
* `SeedData.piece_space`: on a frozen-center piece the space factors are in scale (A4's quantitative box
  `box_of_clearance`);
* **`SeedData.isLogField_of_const`**: on every piece `[b, c] ⊆ [ε, T]` during which the driver stays within
  `cutRad r a₀ γ` of a center `y`, the seeded log-density is a regular log-field with the explicit bound
  `K = 4 · coefTot κ r · scaleBound L` — uniform over the paths, the piece and the center.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped Interval

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H Hbar IsForwardSol fwdMap fwdMapInv fwdHull logDerivFwd)

/-- **The scale conditions of the seeded field**: A7's `ScaleOK` and the bounds `4e^λ/γ² ≤ e^L`, `4/γ² ≤ e^L` for the
own-chart rates. -/
structure SeedScaleOK (r a₀ γ Γ lam T L : ℝ) : Prop where
  base : ScaleOK r a₀ γ Γ lam T L
  e4 : 4 * Real.exp lam / γ ^ 2 ≤ Real.exp L
  g4 : 4 / γ ^ 2 ≤ Real.exp L

namespace OwnData

variable {W : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : ℝ} {a W' : ℝ → ℝ} (h : OwnData W A φ T a W')
include h

/-- `0 < A_{j,1} ≤ 1`, `|A_{j,2}| ≤ 384/r`, `|A_{j,3}| ≤ 3072/r²` from a clearance `r` and `A_{j,1} ≥ a₀`. -/
theorem driver_bounds' {r a₀ : ℝ} (hr : 0 < r) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (hclr : Disjoint (ball (W t : ℂ) r) ((fun z => fwdMap W t z + W t) '' A)) (hA1 : a₀ ≤ frzA W W' a φ 1 t) :
    a₀ ≤ frzA W W' a φ 1 t ∧ frzA W W' a φ 1 t ≤ 1 ∧ |frzA W W' a φ 2 t| ≤ 384 / r ∧
      |frzA W W' a φ 3 t| ≤ 3072 / r ^ 2 := by
  have hW : (W t : ℂ) ∈ ball (W t : ℂ) (r / 8) := mem_ball_self (by positivity)
  refine ⟨hA1, (h.deriv_ownExt_driver ht hr hclr).2.2, ?_, ?_⟩
  · exact (abs_re_le_norm _).trans (h.norm_deriv2_ownExt_le ht hclr (ball_subset_ball (by linarith) hW))
  · exact (abs_re_le_norm _).trans (h.norm_deriv3_ownExt_le ht hclr hW)

/-- `|∂_t log F| ≤ rateBound r a₀`. -/
theorem abs_frzRate_le' {r a₀ : ℝ} (hr : 0 < r) (ha : 0 < a₀) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (hclr : Disjoint (ball (W t : ℂ) r) ((fun z => fwdMap W t z + W t) '' A)) (hA1 : a₀ ≤ frzA W W' a φ 1 t) :
    |frzRate W W' a φ t| ≤ rateBound r a₀ := by
  obtain ⟨h1, -, h2, h3⟩ := h.driver_bounds' hr ht hclr hA1
  have hA1p : 0 < frzA W W' a φ 1 t := lt_of_lt_of_le ha h1
  have q2 : |frzA W W' a φ 2 t / frzA W W' a φ 1 t| ≤ 384 / (r * a₀) := by
    rw [abs_div, abs_of_pos hA1p, div_le_div_iff₀ hA1p (by positivity)]
    calc |frzA W W' a φ 2 t| * (r * a₀) ≤ 384 / r * (r * a₀) := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = 384 * a₀ := by field_simp
      _ ≤ 384 * frzA W W' a φ 1 t := by linarith
  have q3 : |frzA W W' a φ 3 t / frzA W W' a φ 1 t| ≤ 3072 / (r ^ 2 * a₀) := by
    rw [abs_div, abs_of_pos hA1p, div_le_div_iff₀ hA1p (by positivity)]
    calc |frzA W W' a φ 3 t| * (r ^ 2 * a₀) ≤ 3072 / r ^ 2 * (r ^ 2 * a₀) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = 3072 * a₀ := by field_simp
      _ ≤ 3072 * frzA W W' a φ 1 t := by linarith
  have e : frzRate W W' a φ t = 1 / 4 * (frzA W W' a φ 2 t / frzA W W' a φ 1 t) ^ 2 -
      1 / 6 * (frzA W W' a φ 3 t / frzA W W' a φ 1 t) := rfl
  rw [e, rateBound]
  have s2 : (frzA W W' a φ 2 t / frzA W W' a φ 1 t) ^ 2 ≤ (384 / (r * a₀)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) q2 2
  calc |1 / 4 * (frzA W W' a φ 2 t / frzA W W' a φ 1 t) ^ 2 - 1 / 6 * (frzA W W' a φ 3 t / frzA W W' a φ 1 t)|
      ≤ |1 / 4 * (frzA W W' a φ 2 t / frzA W W' a φ 1 t) ^ 2| +
          |1 / 6 * (frzA W W' a φ 3 t / frzA W W' a φ 1 t)| := abs_sub _ _
    _ ≤ 1 / 4 * (384 / (r * a₀)) ^ 2 + 1 / 6 * (3072 / (r ^ 2 * a₀)) := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4),
          abs_of_pos (by norm_num : (0 : ℝ) < 1 / 6), abs_of_nonneg (sq_nonneg _)]
        linarith

end OwnData

namespace SeedData

variable {n : ℕ} (d : SeedData n)

/-- **The constants of a cut-off piece `[ε, T]` of the seeded field.** -/
structure SeedConst (A : Set ℂ) (ε T r a₀ γ Γ lam ρm : ℝ) : Prop where
  r0 : 0 < r
  a0 : 0 < a₀
  g0 : 0 < γ
  m0 : 0 < ρm
  clr : ∀ t ∈ Icc (0 : ℝ) T, Disjoint (ball (d.W t : ℂ) r) ((fun z => fwdMap d.W t z + d.W t) '' A)
  A1 : ∀ t ∈ Icc (0 : ℝ) T, a₀ ≤ d.A 1 t
  mclr : ∀ m, ∀ t ∈ Icc (0 : ℝ) T,
    Disjoint (ball (d.V m t : ℂ) ρm) ((fun z => fwdMap d.W t z + d.W t) '' A)
  E0 : ∀ t ∈ Icc ε T, γ ≤ |d.A20 t - d.A 0 t| ∧ |d.A20 t - d.A 0 t| ≤ Γ
  Em : ∀ t ∈ Icc ε T, ∀ m, γ ≤ |d.B0 t m - d.A 0 t| ∧ |d.B0 t m - d.A 0 t| ≤ Γ
  E2m : ∀ t ∈ Icc ε T, ∀ m, γ ≤ |d.A20 t - d.B0 t m| ∧ |d.A20 t - d.B0 t m| ≤ Γ
  Cmk : ∀ t ∈ Icc ε T, ∀ m k, m ≠ k → γ ≤ |d.B0 t m - d.B0 t k| ∧ |d.B0 t m - d.B0 t k| ≤ Γ
  A21 : ∀ t ∈ Icc ε T, InScale lam (d.A21 t)
  B1 : ∀ t ∈ Icc ε T, ∀ m, InScale lam (d.B1 t m)
  O0 : ∀ t ∈ Icc ε T, γ ≤ |d.V₀ t - d.W t| ∧ |d.V₀ t - d.W t| ≤ Γ
  Om : ∀ t ∈ Icc ε T, ∀ m, γ ≤ |d.V m t - d.W t| ∧ |d.V m t - d.W t| ≤ Γ
  O0m : ∀ t ∈ Icc ε T, ∀ m, γ ≤ |d.V₀ t - d.V m t| ∧ |d.V₀ t - d.V m t| ≤ Γ
  Omk : ∀ t ∈ Icc ε T, ∀ m k, m ≠ k → γ ≤ |d.V m t - d.V k t| ∧ |d.V m t - d.V k t| ≤ Γ

variable {A : Set ℂ} {ε T r a₀ γ Γ lam ρm L : ℝ}

omit d in
theorem ne_zero_of_le_abs {γ u : ℝ} (hγ : 0 < γ) (hu : γ ≤ |u|) : u ≠ 0 := fun h0 => by
  rw [h0, abs_zero] at hu; linarith

omit d in
theorem ne_zero_of_inScale {u : ℝ} (hu : InScale L u) : u ≠ 0 := fun h0 => by
  have := lt_of_lt_of_le (Real.exp_pos _) hu.1; rw [h0, abs_zero] at this; exact lt_irrefl _ this

/-- **The time factors do not degenerate on `[ε, T]`.** -/
theorem timeNd_of_const (hc : d.SeedConst A ε T r a₀ γ Γ lam ρm) {t : ℝ} (ht : t ∈ Icc ε T) : d.TimeNd t where
  G₀ := fun h0 => ne_zero_of_inScale (hc.A21 t ht) (by simp [SeedData.A21, h0])
  V₀W := ne_zero_of_le_abs hc.g0 (hc.O0 t ht).1
  VW := fun m => ne_zero_of_le_abs hc.g0 (hc.Om t ht m).1
  V₀V := fun m => ne_zero_of_le_abs hc.g0 (hc.O0m t ht m).1
  VV := fun m k hmk => ne_zero_of_le_abs hc.g0 (hc.Omk t ht m k hmk).1
  BA := fun m => ne_zero_of_le_abs hc.g0 (hc.Em t ht m).1
  A2B := fun m => ne_zero_of_le_abs hc.g0 (hc.E2m t ht m).1
  BB := fun m k hmk => ne_zero_of_le_abs hc.g0 (hc.Cmk t ht m k hmk).1
  B1 := fun m => ne_zero_of_inScale (hc.B1 t ht m)

omit d in
theorem abs_two_mul_div_sq_le {c X E γ M : ℝ} (hγ : 0 < γ) (hc : |c| ≤ 1) (hX : |X| ≤ M) (hE : γ ≤ |E|) :
    |2 * c * X / E ^ 2| ≤ 2 * M / γ ^ 2 := by
  have hE2 : γ ^ 2 ≤ E ^ 2 := by rw [← sq_abs E]; exact pow_le_pow_left₀ hγ.le hE 2
  have hM : 0 ≤ M := (abs_nonneg _).trans hX
  have hE2p : 0 < E ^ 2 := lt_of_lt_of_le (by positivity) hE2
  rw [abs_div, abs_mul, abs_mul, abs_two, abs_of_nonneg (sq_nonneg E)]
  calc 2 * |c| * |X| / E ^ 2 ≤ 2 * 1 * M / E ^ 2 := by gcongr
    _ ≤ 2 * M / γ ^ 2 := by rw [mul_one]; exact div_le_div_of_nonneg_left (by positivity) (by positivity) hE2

omit d in
theorem abs_two_mul_div_le {c E γ : ℝ} (hγ : 0 < γ) (hc : |c| ≤ 1) (hE : γ ≤ |E|) : |2 * c / E| ≤ 2 / γ := by
  have hE0 : 0 < |E| := lt_of_lt_of_le hγ hE
  rw [abs_div, abs_mul, abs_two]
  calc 2 * |c| / |E| ≤ 2 * 1 / |E| := by gcongr
    _ ≤ 2 / γ := by rw [mul_one]; exact div_le_div_of_nonneg_left (by norm_num) hγ hE

omit d in
theorem inScale_one (hL : 0 ≤ L) : InScale L 1 := by
  refine ⟨?_, ?_⟩ <;> rw [abs_one]
  · exact Real.exp_le_one_iff.2 (by linarith)
  · exact Real.one_le_exp hL

/-- **The time part at height `y`**: `|LT|, |LTT| ≤ coefTot κ r · scaleBound L` on `[ε, T]`. -/
theorem time_bounds_y (h : OwnData d.W A d.φ T d.a d.W') (hc : d.SeedConst A ε T r a₀ γ Γ lam ρm)
    (hL : SeedScaleOK r a₀ γ Γ lam T L) (hε : 0 ≤ ε) {t : ℝ} (ht : t ∈ Icc ε T) :
    |d.LT t| ≤ coefTot d.κ d.r * scaleBound L ∧ |d.LTT t| ≤ coefTot d.κ d.r * scaleBound L := by
  have hγ := hc.g0
  have hB := hL.base
  have ht0 : t ∈ Icc (0 : ℝ) T := ⟨hε.trans ht.1, ht.2⟩
  have hlo : Real.exp (-L) ≤ γ := hB.g.trans (by linarith)
  have hhi : Γ ≤ Real.exp L := le_trans (by linarith) hB.G
  obtain ⟨ha1, ha1', -, -⟩ := h.driver_bounds' hc.r0 ht0 (hc.clr t ht0) (hc.A1 t ht0)
  have hA1p : 0 < d.A 1 t := lt_of_lt_of_le hc.a0 ha1
  have hA1le : d.A 1 t ≤ 1 := ha1'
  have hc1 : |-(d.A 1 t ^ 2)| ≤ 1 := by rw [abs_neg, abs_of_nonneg (sq_nonneg _)]; nlinarith
  have hc1' : |d.A 1 t ^ 2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg _)]; nlinarith
  have hone : |(1 : ℝ)| ≤ 1 := by rw [abs_one]
  have hel := Real.exp_pos lam
  -- the (D3) rates with the own-chart terms
  have rate2 : ∀ X E O : ℝ, |X| ≤ Real.exp lam → γ ≤ |E| → γ ≤ |O| →
      |-2 * d.A 1 t ^ 2 * X / E ^ 2 + 2 / O ^ 2 * X| ≤ Real.exp L := fun X E O hX hE hO => by
    have e1 : -2 * d.A 1 t ^ 2 * X / E ^ 2 = 2 * (-(d.A 1 t ^ 2)) * X / E ^ 2 := by ring
    have e2 : 2 / O ^ 2 * X = 2 * 1 * X / O ^ 2 := by ring
    rw [e1, e2]
    calc _ ≤ |2 * (-(d.A 1 t ^ 2)) * X / E ^ 2| + |2 * 1 * X / O ^ 2| := abs_add_le _ _
      _ ≤ 2 * Real.exp lam / γ ^ 2 + 2 * Real.exp lam / γ ^ 2 :=
          add_le_add (abs_two_mul_div_sq_le hγ hc1 hX hE) (abs_two_mul_div_sq_le hγ hone hX hO)
      _ = 4 * Real.exp lam / γ ^ 2 := by ring
      _ ≤ Real.exp L := hL.e4
  have rate1 : ∀ E : ℝ, γ ≤ |E| → |2 * d.A 1 t ^ 2 / E| ≤ Real.exp L := fun E hE =>
    (abs_two_mul_div_le hγ hc1' hE).trans hB.g2
  have hlF : |d.L t| ≤ Real.exp L := by
    have hb : ∀ u ∈ Ι (0 : ℝ) t, ‖frzRate d.W d.W' d.a d.φ u‖ ≤ rateBound r a₀ := fun u hu => by
      rw [uIoc_of_le ht0.1] at hu
      have hu0 : u ∈ Icc (0 : ℝ) T := ⟨hu.1.le, hu.2.trans ht0.2⟩
      exact h.abs_frzRate_le' hc.r0 hc.a0 hu0 (hc.clr u hu0) (hc.A1 u hu0)
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht0.1] at this
    refine this.trans (le_trans ?_ hB.logF)
    have : 0 ≤ rateBound r a₀ :=
      (abs_nonneg _).trans (h.abs_frzRate_le' hc.r0 hc.a0 ht0 (hc.clr t ht0) (hc.A1 t ht0))
    nlinarith [ht0.2]
  have hE0' : γ ≤ |d.A 0 t - d.A20 t| := by rw [abs_sub_comm]; exact (hc.E0 t ht).1
  have hEm' : ∀ m, γ ≤ |d.A 0 t - d.B0 t m| := fun m => by rw [abs_sub_comm]; exact (hc.Em t ht m).1
  exact abs_dualLogTime_le (κ := d.κ) (r := d.r) (A21 := d.A21 t) (lF := d.L t) (A20 := d.A20 t) (B0 := d.B0 t)
    (B1 := d.B1 t) (dA21 := -2 * d.A 1 t ^ 2 * d.A21 t / (d.A 0 t - d.A20 t) ^ 2 + 2 / (d.V₀ t - d.W t) ^ 2 * d.A21 t)
    (dL := frzRate d.W d.W' d.a d.φ t) (dA20 := 2 * d.A 1 t ^ 2 / (d.A20 t - d.A 0 t))
    (dB0 := fun m => 2 * d.A 1 t ^ 2 / (d.B0 t m - d.A 0 t))
    (dB1 := fun m => -2 * d.A 1 t ^ 2 * d.B1 t m / (d.A 0 t - d.B0 t m) ^ 2 + 2 / (d.Vv t m - d.W t) ^ 2 * d.B1 t m)
    hB.L0 (FrzData.inScale_mono (hc.A21 t ht) hB.la) (fun m => FrzData.inScale_mono (hc.B1 t ht m) hB.la)
    (fun m => FrzData.inScale_of_le hlo hhi (hc.E2m t ht m))
    (fun m k hmk => FrzData.inScale_of_le hlo hhi (hc.Cmk t ht m k hmk))
    hlF (rate2 _ _ _ (hc.A21 t ht).2 hE0' (hc.O0 t ht).1)
    ((h.abs_frzRate_le' hc.r0 hc.a0 ht0 (hc.clr t ht0) (hc.A1 t ht0)).trans hB.rate) (rate1 _ (hc.E0 t ht).1)
    (fun m => rate1 _ (hc.Em t ht m).1) (fun m => rate2 _ _ _ (hc.B1 t ht m).2 (hEm' m) (hc.Om t ht m).1)

/-- **The time part at height `0`**: `|LT0|, |LT0T| ≤ coefTot κ r · scaleBound L` on `[ε, T]`. -/
theorem time_bounds_0 (hc : d.SeedConst A ε T r a₀ γ Γ lam ρm) (hL : SeedScaleOK r a₀ γ Γ lam T L) {t : ℝ}
    (ht : t ∈ Icc ε T) :
    |d.LT0 t| ≤ coefTot d.κ d.r * scaleBound L ∧ |d.LT0T t| ≤ coefTot d.κ d.r * scaleBound L := by
  have hγ := hc.g0
  have hB := hL.base
  have hlo : Real.exp (-L) ≤ γ := hB.g.trans (by linarith)
  have hhi : Γ ≤ Real.exp L := le_trans (by linarith) hB.G
  have hone : |(1 : ℝ)| ≤ 1 := by rw [abs_one]
  have hone' : |(-1 : ℝ)| ≤ 1 := by rw [abs_neg, abs_one]
  have rate2 : ∀ E O : ℝ, γ ≤ |E| → γ ≤ |O| → |-2 * 1 ^ 2 * 1 / E ^ 2 + 2 / O ^ 2 * 1| ≤ Real.exp L :=
    fun E O hE hO => by
      have e1 : -2 * (1 : ℝ) ^ 2 * 1 / E ^ 2 = 2 * (-1) * 1 / E ^ 2 := by ring
      have e2 : 2 / O ^ 2 * 1 = 2 * 1 * 1 / O ^ 2 := by ring
      rw [e1, e2]
      calc _ ≤ |2 * (-1) * 1 / E ^ 2| + |2 * 1 * 1 / O ^ 2| := abs_add_le _ _
        _ ≤ 2 * 1 / γ ^ 2 + 2 * 1 / γ ^ 2 :=
            add_le_add (abs_two_mul_div_sq_le hγ hone' hone hE) (abs_two_mul_div_sq_le hγ hone hone hO)
        _ = 4 / γ ^ 2 := by ring
        _ ≤ Real.exp L := hL.g4
  have rate1 : ∀ E : ℝ, γ ≤ |E| → |2 * 1 ^ 2 / E| ≤ Real.exp L := fun E hE =>
    (abs_two_mul_div_le hγ (by rw [one_pow]; exact hone) hE).trans hB.g2
  have hWV₀ : γ ≤ |d.W t - d.V₀ t| := by rw [abs_sub_comm]; exact (hc.O0 t ht).1
  have hWV : ∀ m, γ ≤ |d.W t - d.Vv t m| := fun m => by rw [abs_sub_comm]; exact (hc.Om t ht m).1
  have h0 : |(0 : ℝ)| ≤ Real.exp L := by rw [abs_zero]; exact (Real.exp_pos _).le
  exact abs_dualLogTime_le (κ := d.κ) (r := d.r) (A21 := 1) (lF := 0) (A20 := d.V₀ t) (B0 := d.Vv t)
    (B1 := fun _ => 1) (dA21 := -2 * 1 ^ 2 * 1 / (d.W t - d.V₀ t) ^ 2 + 2 / (d.V₀ t - d.W t) ^ 2 * 1)
    (dL := 0) (dA20 := 2 * 1 ^ 2 / (d.V₀ t - d.W t)) (dB0 := fun m => 2 * 1 ^ 2 / (d.Vv t m - d.W t))
    (dB1 := fun m => -2 * 1 ^ 2 * 1 / (d.W t - d.Vv t m) ^ 2 + 2 / (d.Vv t m - d.W t) ^ 2 * 1)
    hB.L0 (inScale_one hB.L0) (fun _ => inScale_one hB.L0)
    (fun m => FrzData.inScale_of_le hlo hhi (hc.O0m t ht m))
    (fun m k hmk => FrzData.inScale_of_le hlo hhi (hc.Omk t ht m k hmk)) h0 (rate2 _ _ hWV₀ (hc.O0 t ht).1) h0
    (rate1 _ (hc.O0 t ht).1) (fun m => rate1 _ (hc.Om t ht m).1) (fun m => rate2 _ _ (hWV m) (hc.Om t ht m).1)

/-! ### The space factors on a frozen-center piece -/

/-- **The box hypotheses and the space inputs on a frozen-center piece** `[b, c] ⊆ [ε, T]` (the driver within
`cutRad r a₀ γ` of `y`): A4's quantitative box and the scale of both heights' space factors. -/
theorem piece_space (h : OwnData d.W A d.φ T d.a d.W') (hc : d.SeedConst A ε T r a₀ γ Γ lam ρm)
    (hL : SeedScaleOK r a₀ γ Γ lam T L) (hε : 0 ≤ ε) {b c y : ℝ} (hJ : Icc b c ⊆ Icc ε T)
    (hWy : ∀ t ∈ Icc b c, |d.W t - y| < cutRad r a₀ γ) :
    (∀ t ∈ Icc b c, Disjoint (ball (y : ℂ) (2 * (clrRad r a₀ / 8))) ((fun z => fwdMap d.W t z + d.W t) '' A)) ∧
    (∀ t ∈ Icc b c, (d.W t : ℂ) ∈ ball (y : ℂ) (clrRad r a₀ / 8)) ∧
    (∀ t ∈ Icc b c, ∀ z ∈ ball (y : ℂ) (clrRad r a₀ / 8), dslope (ownExt d.W d.W' d.a d.φ t) (d.W t) z ≠ 0) ∧
    3 * cutRad r a₀ γ ≤ clrRad r a₀ / 8 ∧
    ∀ t ∈ Icc b c, ∀ x : ℝ, |x - y| < 3 * cutRad r a₀ γ →
      InScale L (d.F 1 t x) ∧ InScale L (d.F 0 t x - d.A20 t) ∧ (∀ m, InScale L (d.F 0 t x - d.B0 t m)) ∧
      |d.F 2 t x| ≤ Real.exp L ∧ |d.F 3 t x| ≤ Real.exp L ∧ |d.F 4 t x| ≤ Real.exp L ∧
      |(dHat (ownExt d.W d.W' d.a d.φ t) (d.W t) x).re| ≤ Real.exp L ∧
      |(deriv (dHat (ownExt d.W d.W' d.a d.φ t) (d.W t)) x).re| ≤ Real.exp L ∧
      InScale L (x - d.V₀ t) ∧ ∀ m, InScale L (x - d.V m t) := by
  have hr := hc.r0
  have ha := hc.a0
  have hγ := hc.g0
  have hB := hL.base
  set ρ := clrRad r a₀ with hρ
  set ρc := cutRad r a₀ γ with hρc
  have hρp : 0 < ρ := clrRad_pos hr ha
  obtain ⟨hc1, hc2⟩ := FrzData.cutRad_le (r := r) (a₀ := a₀) (γ := γ)
  have hJ0 : Icc b c ⊆ Icc 0 T := fun t ht => ⟨hε.trans (hJ ht).1, (hJ ht).2⟩
  have hWy' : ∀ t ∈ Icc b c, |d.W t - y| < ρ / 24 := fun t ht => lt_of_lt_of_le (hWy t ht) hc1
  obtain ⟨hdisj, hWm, hq0, hloc⟩ := h.box_of_clearance hr ha hc.clr hc.A1 hJ0 hWy'
  have h3 : 3 * ρc ≤ ρ / 8 := by linarith
  refine ⟨hdisj, hWm, hq0, h3, fun t ht x hx => ?_⟩
  have hxb : (x : ℂ) ∈ ball (y : ℂ) (ρ / 8) := FrzData.mem_ball_of_near h3 hx
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := hloc t ht x hxb
  have hlo : Real.exp (-L) ≤ γ / 2 := hB.g
  have hxW' : |x - d.W t| ≤ 4 * ρc := by
    have := hWy t ht
    calc |x - d.W t| = |(x - y) - (d.W t - y)| := by ring_nf
      _ ≤ |x - y| + |d.W t - y| := abs_sub _ _
      _ ≤ 4 * ρc := by linarith
  have hxW : ‖(x : ℂ) - d.W t‖ ≤ 4 * ρc := by
    rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hxW'
  have hF0 : |d.F 0 t x - d.A 0 t| ≤ γ / 2 := by
    have e : d.F 0 t x - d.A 0 t = (ownExt d.W d.W' d.a d.φ t x - ownExt d.W d.W' d.a d.φ t (d.W t)).re := by
      simp [SeedData.F, SeedData.A, frzA]
    rw [e]
    calc _ ≤ ‖ownExt d.W d.W' d.a d.φ t x - ownExt d.W d.W' d.a d.φ t (d.W t)‖ := abs_re_le_norm _
      _ ≤ 96 * ‖(x : ℂ) - d.W t‖ := l6
      _ ≤ 96 * (4 * ρc) := by gcongr
      _ ≤ γ / 2 := by linarith
  have hxW2 : |x - d.W t| ≤ γ / 2 := by linarith
  have sep : ∀ u P E : ℝ, |u - P| ≤ γ / 2 → γ ≤ |E - P| ∧ |E - P| ≤ Γ → InScale L (u - E) :=
    fun u P E hu hE => by
      refine ⟨hlo.trans ?_, ?_⟩
      · have : |E - P| ≤ |u - E| + |u - P| := by
          calc |E - P| = |(u - P) - (u - E)| := by ring_nf
            _ ≤ |u - P| + |u - E| := abs_sub _ _
            _ = _ := by ring
        linarith [hE.1]
      · calc |u - E| = |(u - P) - (E - P)| := by ring_nf
          _ ≤ |u - P| + |E - P| := abs_sub _ _
          _ ≤ γ / 2 + Γ := add_le_add hu hE.2
          _ ≤ Real.exp L := by linarith [hB.G]
  have ht' := hJ ht
  refine ⟨⟨hB.a.trans (l1.trans (le_abs_self _)), (abs_re_le_norm _).trans (l2.trans hB.c96)⟩,
    sep _ _ _ hF0 (hc.E0 t ht'), fun m => sep _ _ _ hF0 (hc.Em t ht' m), (abs_re_le_norm _).trans (l3.trans hB.r2),
    (abs_re_le_norm _).trans (l4.trans hB.r3), (abs_re_le_norm _).trans (l5.trans hB.r4),
    (abs_re_le_norm _).trans (l7.trans hB.D), (abs_re_le_norm _).trans (l8.trans hB.D'),
    sep _ _ _ hxW2 (hc.O0 t ht'), fun m => sep _ _ _ hxW2 (hc.Om t ht' m)⟩

/-! ### The seeded log-field on a frozen-center piece -/

/-- A moving clearance of a continuous mark gives a clearance of a fixed disc around its position for nearby times. -/
theorem exists_mark_clear (hc : d.SeedConst A ε T r a₀ γ Γ lam ρm) (m : Fin n)
    (hVc : ContinuousOn (d.V m) (Icc 0 T)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ∃ ρ' > (0 : ℝ), ∃ η₀ > (0 : ℝ), ∀ s ∈ Icc (max 0 (t - η₀)) (min T (t + η₀)),
      Disjoint (ball (d.V m t : ℂ) ρ') ((fun z => fwdMap d.W s z + d.W s) '' A) := by
  obtain ⟨δ, hδ, hδV⟩ := Metric.continuousOn_iff.1 hVc t ht (ρm / 2) (by have := hc.m0; positivity)
  refine ⟨ρm / 2, by have := hc.m0; positivity, δ / 2, by positivity, fun s hs => ?_⟩
  obtain ⟨hs0, hst⟩ := OwnData.mem_box_of_abs_lt (T := T) hs
  have hV := hδV s hs0 (by rw [Real.dist_eq]; linarith)
  rw [Real.dist_eq] at hV
  refine Set.disjoint_of_subset_left (fun z hz => ?_) (hc.mclr m s hs0)
  rw [mem_ball, Complex.dist_eq] at hz ⊢
  have hVs : ‖((d.V m t : ℝ) : ℂ) - d.V m s‖ < ρm / 2 := by
    rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]; exact hV
  calc ‖z - d.V m s‖ = ‖(z - d.V m t) + ((d.V m t : ℂ) - d.V m s)‖ := by ring_nf
    _ ≤ ‖z - d.V m t‖ + ‖((d.V m t : ℝ) : ℂ) - d.V m s‖ := norm_add_le _ _
    _ < ρm := by linarith

/-- **The seeded log-density is a regular log-field on every frozen-center piece of `[ε, T]`**, with the explicit
bound `K = 4 · coefTot κ r · scaleBound L`. The marks follow the force ODE on `[ε, T]` and are continuous on
`[0, T]`. -/
theorem isLogField_of_const (h : OwnData d.W A d.φ T d.a d.W') {v₀ : ℝ → ℂ}
    (hv₀ : IsForwardSol d.W' d.ζ₀ (d.a T) v₀) (hc : d.SeedConst A ε T r a₀ γ Γ lam ρm)
    (hL : SeedScaleOK r a₀ γ Γ lam T L) (hε : 0 ≤ ε)
    (hV₀ : ∀ t ∈ Icc ε T, HasDerivWithinAt d.V₀ (2 / (d.V₀ t - d.W t)) (Icc ε T) t)
    (hG₀ : ∀ t ∈ Icc ε T, HasDerivWithinAt d.G₀ (-2 * d.G₀ t / (d.V₀ t - d.W t) ^ 2) (Icc ε T) t)
    (hV : ∀ m, ∀ t ∈ Icc ε T, HasDerivWithinAt (d.V m) (2 / (d.V m t - d.W t)) (Icc ε T) t)
    (hVc : ∀ m, ContinuousOn (d.V m) (Icc 0 T)) {b c y : ℝ} (hJ : Icc b c ⊆ Icc ε T)
    (hWy : ∀ t ∈ Icc b c, |d.W t - y| < cutRad r a₀ γ) :
    IsLogField d.ell d.ellX d.ellXX d.ellXXX d.ellT b c y (cutRad r a₀ γ)
      (4 * (coefTot d.κ d.r * scaleBound L)) := by
  have hγ := hc.g0
  have hB := hL.base
  have hJ0 : Icc b c ⊆ Icc 0 T := fun t ht => ⟨hε.trans (hJ ht).1, (hJ ht).2⟩
  obtain ⟨hdisj, hWm, hq0, h3, hsp⟩ := d.piece_space h hc hL hε hJ hWy
  have hV₀' : ∀ t ∈ Icc b c, HasDerivWithinAt d.V₀ (2 / (d.V₀ t - d.W t)) (Icc b c) t := fun t ht =>
    (hV₀ t (hJ ht)).mono hJ
  have hG₀' : ∀ t ∈ Icc b c, HasDerivWithinAt d.G₀ (-2 * d.G₀ t / (d.V₀ t - d.W t) ^ 2) (Icc b c) t :=
    fun t ht => (hG₀ t (hJ ht)).mono hJ
  have hV' : ∀ m, ∀ t ∈ Icc b c, HasDerivWithinAt (d.V m) (2 / (d.V m t - d.W t)) (Icc b c) t := fun m t ht =>
    (hV m t (hJ ht)).mono hJ
  have hmcl : ∀ m, ∀ t ∈ Icc b c, ∃ ρ' > (0 : ℝ), ∃ η₀ > (0 : ℝ),
      ∀ s ∈ Icc (max 0 (t - η₀)) (min T (t + η₀)),
        Disjoint (ball (d.V m t : ℂ) ρ') ((fun z => fwdMap d.W s z + d.W s) '' A) := fun m t ht =>
    d.exists_mark_clear hc m (hVc m) (hJ0 ht)
  have hnt : ∀ t ∈ Icc b c, d.TimeNd t := fun t ht => d.timeNd_of_const hc (hJ ht)
  have hnd : ∀ t ∈ Icc b c, ∀ x : ℝ, |x - y| < 3 * cutRad r a₀ γ → d.SpaceNd t x := fun t ht x hx => by
    obtain ⟨s1, s0, sm, -, -, -, -, -, sV₀, sV⟩ := hsp t ht x hx
    exact ⟨ne_zero_of_inScale s1, ne_zero_of_inScale s0, fun m => ne_zero_of_inScale (sm m),
      ne_zero_of_inScale sV₀, fun m => ne_zero_of_inScale (sV m)⟩
  set C := coefTot d.κ d.r * scaleBound L with hC
  have hL0 := hB.L0
  have hC0 : 0 ≤ C := mul_nonneg (coefTot_ge (κ := d.κ) (r := d.r)).2.2.2 (hL0.trans (le_scaleBound hL0).1)
  refine d.isLogField h hv₀ hJ0 hdisj hWm hq0 hV₀' hG₀' hV' hmcl hnt (cutRad_pos hc.r0 hc.a0 hγ) (by positivity)
    h3 hnd fun t ht x hx => ?_
  have ht' := hJ ht
  have ht0 := hJ0 ht
  obtain ⟨s1, s0, sm, s2, s3, s4, sD, sD', sV₀, sV⟩ := hsp t ht x hx
  obtain ⟨ha1, ha1', -, -⟩ := h.driver_bounds' hc.r0 ht0 (hc.clr t ht0) (hc.A1 t ht0)
  have hA1le : d.A 1 t ≤ 1 := ha1'
  have hA1p : 0 < d.A 1 t := lt_of_lt_of_le hc.a0 ha1
  have hc1' : |d.A 1 t ^ 2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg _)]; nlinarith
  have rate1 : ∀ E : ℝ, γ ≤ |E| → |2 * d.A 1 t ^ 2 / E| ≤ Real.exp L := fun E hE =>
    (abs_two_mul_div_le hγ hc1' hE).trans hB.g2
  have rate0 : ∀ E : ℝ, γ ≤ |E| → |2 / E| ≤ Real.exp L := fun E hE => by
    have := abs_two_mul_div_le hγ (c := 1) (by rw [abs_one]) hE
    rw [mul_one] at this
    exact this.trans hB.g2
  have h0 : |(0 : ℝ)| ≤ Real.exp L := by rw [abs_zero]; exact (Real.exp_pos _).le
  obtain ⟨b0, b1, b2, b3, bT⟩ := abs_dualLogSpace_le (κ := d.κ) (r := d.r) hL0 s1 s0 sm s2 s3 s4 sD sD'
    (rate1 _ (hc.E0 t ht').1) (fun m => rate1 _ (hc.Em t ht' m).1)
  obtain ⟨z0, z1, z2, z3, zT⟩ := abs_dualLogSpace_le (κ := d.κ) (r := d.r) (f := x) (f1 := 1) (f2 := 0) (f3 := 0)
    (f4 := 0) (A0 := d.V₀ t) (B0 := d.Vv t) (df := 0) (df1 := 0) (dA0 := 2 / (d.V₀ t - d.W t))
    (dB0 := fun m => 2 / (d.V m t - d.W t)) hL0 (inScale_one hL0) sV₀ sV h0 h0 h0 h0 h0
    (rate0 _ (hc.O0 t ht').1) (fun m => rate0 _ (hc.Om t ht' m).1)
  obtain ⟨c0, cT⟩ := d.time_bounds_y h hc hL hε ht'
  obtain ⟨e0, eT⟩ := d.time_bounds_0 hc hL ht'
  have sub2 : ∀ u v : ℝ, |u| ≤ C → |v| ≤ C → |u - v| ≤ 4 * C := fun u v hu hv => by
    have := abs_sub u v; linarith
  have sub4 : ∀ u v w z : ℝ, |u| ≤ C → |v| ≤ C → |w| ≤ C → |z| ≤ C → |(u + v) - (w + z)| ≤ 4 * C :=
    fun u v w z hu hv hw hz => by
      have h1 := abs_sub (u + v) (w + z)
      have h2 := abs_add_le u v
      have h3 := abs_add_le w z
      linarith
  exact ⟨sub4 _ _ _ _ c0 b0 e0 z0, sub2 _ _ b1 z1, sub2 _ _ b2 z2, sub2 _ _ b3 z3, sub4 _ _ _ _ cT bT eT zT⟩

end SeedData

end InteractingSLE.ZhanGT4
