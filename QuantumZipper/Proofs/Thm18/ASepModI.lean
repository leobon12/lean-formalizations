import QuantumZipper.Proofs.Thm18.ASepModH

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP (mod I): the joint Hölder modulus of `muA0`

`energy_muA0_joint`: `|E(muA0 p ρ − muA0 p' ρ')| ≤ K (dist p p' + |ρ − ρ'|)^c` on
`([0,T] × [a₀,a₁]) × [0,1]`, by the interpolation of XFLOW-E1 / D33 (`D = dist p p' + |ρ − ρ'|`,
`r₀ = D^{α/48}`): radii `≥ r₀` by the mixture modulus (`energy_muA0_large`, `large_arith`),
otherwise the triangle bound through radius `0` (`energy_muA0_small`, `small_arith`), and the
uniform bound for `D ≥ 1/2`. Own bookkeeping (as `F1.flowE1Stmt_holds`).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace QuantumZipper
namespace ASep

open RegCont RegUnif B2 Thm18Asm.G4Core

/-- **Joint modulus of the A-sep family.** -/
theorem energy_muA0_joint {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T α CH : ℝ}
    (hT : 0 ≤ T) (hα : 0 < α) (hα1 : α ≤ 1) (hCH : 0 ≤ CH)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 →
      |W t - W t'| ≤ CH * |t - t'| ^ α)
    {d : ℂ} (hd : 0 ≤ d.im) {r : ℝ} (hr : 0 < r) {a₀ a₁ : ℝ} (ha₀ : 0 < a₀) (ha₀₁ : a₀ ≤ a₁)
    (hgood0 : ∀ a ∈ Icc a₀ a₁, ∀ w ∈ foldSph d r, ∃ u, IsForwardSol W ((a : ℂ) * w) T u)
    {m : ℝ} (hm : 0 < m)
    (hlow : ∀ z ∈ scaledSph d r a₀ a₁, ∀ s ∈ Icc (0 : ℝ) T, m ≤ ‖fwdMap W s z‖)
    {M : ℝ} (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ M) :
    ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧ ∀ p p' : Fin 2 → ℝ, p 0 ∈ Icc (0 : ℝ) T → p 1 ∈ Icc a₀ a₁ →
      p' 0 ∈ Icc (0 : ℝ) T → p' 1 ∈ Icc a₀ a₁ → ∀ ρ ∈ Icc (0 : ℝ) 1, ∀ ρ' ∈ Icc (0 : ℝ) 1,
      |kernelCov2 neumannH (muA0 W d r p ρ, muA0 W d r p' ρ')
        (muA0 W d r p ρ, muA0 W d r p' ρ')| ≤ K * (dist p p' + |ρ - ρ'|) ^ c := by
  obtain ⟨M₀, hM₀, h0⟩ := push0_muA0 hW hW0 hT hr ha₀ ha₀₁ hm hgood0 hlow hM
  obtain ⟨C₀, b, hC₀, hb, hz⟩ := energy_muA0_zero_le hW hW0 hd hr ha₀ hm hgood0 hlow
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
  have hDd0 : 0 < ‖d‖ + r := by positivity
  have hCΛ0 : 0 ≤ Real.exp (2 * T / m ^ 2) * (‖d‖ + r) + CH + 2 / m + 1 := by positivity
  have hc0 : 0 < min (α / 192) b := lt_min (by positivity) hb
  have hA0 : 0 ≤ (a₁ - a₀) * (‖d‖ + r) := mul_nonneg (by linarith) hDd0.le
  have hU0 : 0 ≤ 6 * M₀ + 4 * (C₀ * ((a₁ - a₀) * (‖d‖ + r)) ^ b) := by positivity
  refine ⟨(2 * |timeKs M T (a₁ * (‖d‖ + r) + M + 2 * T / m + 1) CH| +
      2 * |spaceKs M T (a₁ * (‖d‖ + r) + M + 2 * T / m + 1)| *
        (Real.exp (2 * T / m ^ 2) * (‖d‖ + r) + CH + 2 / m + 1) ^ (1 / 12 : ℝ)) +
      (6 * M₀ * 2 ^ (1 / 4 : ℝ) + 4 * C₀ * (‖d‖ + r) ^ b) +
      (6 * M₀ + 4 * (C₀ * ((a₁ - a₀) * (‖d‖ + r)) ^ b)) * 2 ^ min (α / 192) b,
    min (α / 192) b, by positivity, hc0, fun p p' hp0 hp1 hp0' hp1' ρ hρ ρ' hρ' => ?_⟩
  -- abstract the energy and the distance
  have hS := energy_muA0_small hW hW0 hr ha₀ hm hgood0 hlow hM hM₀ h0 hz hp0 hp1 hp0' hp1' hρ hρ'
  have hτD := abs_coord_sub_le_dist p p' 0
  have haD := abs_coord_sub_le_dist p p' 1
  have hEnn : 0 ≤ |kernelCov2 neumannH (muA0 W d r p ρ, muA0 W d r p' ρ')
      (muA0 W d r p ρ, muA0 W d r p' ρ')| := abs_nonneg _
  have hLg : ∀ r₀ : ℝ, 0 < r₀ → r₀ ≤ ρ → r₀ ≤ ρ' →
      |kernelCov2 neumannH (muA0 W d r p ρ, muA0 W d r p' ρ')
        (muA0 W d r p ρ, muA0 W d r p' ρ')| ≤
      2 * (timeK M T r₀ (a₁ * (‖d‖ + r) + M + 2 * T / m + 1) CH * |p 0 - p' 0| ^ (α / 12)) +
        2 * (spaceK M T r₀ (a₁ * (‖d‖ + r) + M + 2 * T / m + 1) *
          (Real.exp (2 * T / m ^ 2) * (|p 1 - p' 1| * (‖d‖ + r)) + |W (p 0) - W (p' 0)| +
            2 * |p 0 - p' 0| / m + |ρ - ρ'|) ^ (1 / 12 : ℝ)) :=
    fun r₀ hr₀ h1 h2 => energy_muA0_large hW hW0 hα hα1 hCH hH hr ha₀ hgood0 hm hlow hM hr₀
      hp0 hp1 hp0' hp1' h1 hρ.2 h2 hρ'.2
  have hWt : |p 0 - p' 0| ≤ 1 / 2 → |W (p 0) - W (p' 0)| ≤ CH * |p 0 - p' 0| ^ α :=
    fun h => hH _ hp0 _ hp0' h
  have haa : |p 1 - p' 1| ≤ a₁ - a₀ := by
    rw [abs_le]; constructor <;> linarith [hp1.1, hp1.2, hp1'.1, hp1'.2]
  have hDpp : dist p p' = 0 → ρ = ρ' → p = p' := fun h _ => dist_eq_zero.1 h
  clear h0 hz
  have hD0 : 0 ≤ dist p p' + |ρ - ρ'| := by positivity
  rcases hD0.eq_or_lt with hDz | hDpos
  · have hpp : dist p p' = 0 := by linarith [dist_nonneg (x := p) (y := p'), abs_nonneg (ρ - ρ')]
    have hrr : |ρ - ρ'| = 0 := by linarith [dist_nonneg (x := p) (y := p'), abs_nonneg (ρ - ρ')]
    have e2 : ρ = ρ' := by linarith [abs_eq_zero.1 hrr]
    have e1 : p = p' := hDpp hpp e2
    subst e1 e2
    have : kernelCov2 neumannH (muA0 W d r p ρ, muA0 W d r p ρ)
        (muA0 W d r p ρ, muA0 W d r p ρ) = 0 := by unfold kernelCov2; ring
    rw [this, abs_zero]; positivity
  generalize hE : |kernelCov2 neumannH (muA0 W d r p ρ, muA0 W d r p' ρ')
    (muA0 W d r p ρ, muA0 W d r p' ρ')| = E at hS hEnn hLg
  generalize hDdef : dist p p' + |ρ - ρ'| = D at hDpos
  have hτD' : |p 0 - p' 0| ≤ D := by rw [← hDdef]; linarith [abs_nonneg (ρ - ρ')]
  have haD' : |p 1 - p' 1| ≤ D := by rw [← hDdef]; linarith [abs_nonneg (ρ - ρ')]
  have hρD : |ρ - ρ'| ≤ D := by rw [← hDdef]; linarith [dist_nonneg (x := p) (y := p')]
  have hD0' := hDpos.le
  have hDc : 0 ≤ D ^ min (α / 192) b := Real.rpow_nonneg hD0' _
  set c := min (α / 192) b with hc
  have hcα : c ≤ α / 192 := min_le_left _ _
  have hcb : c ≤ b := min_le_right _ _
  set Dd := ‖d‖ + r with hDd
  set U := 6 * M₀ + 4 * (C₀ * ((a₁ - a₀) * Dd) ^ b) with hU
  set K1 := 2 * |timeKs M T (a₁ * Dd + M + 2 * T / m + 1) CH| +
      2 * |spaceKs M T (a₁ * Dd + M + 2 * T / m + 1)| *
        (Real.exp (2 * T / m ^ 2) * Dd + CH + 2 / m + 1) ^ (1 / 12 : ℝ) with hK1
  set K2 := 6 * M₀ * 2 ^ (1 / 4 : ℝ) + 4 * C₀ * Dd ^ b with hK2
  have hK10 : 0 ≤ K1 := by positivity
  have hK20 : 0 ≤ K2 := by positivity
  have hU2 : 0 ≤ U * 2 ^ c := by positivity
  by_cases hbig : 1 / 2 ≤ D
  · have hq4 : ∀ s ∈ Icc (0 : ℝ) 1, s ^ (1 / 4 : ℝ) ≤ 1 := fun s hs =>
      Real.rpow_le_one hs.1 hs.2 (by norm_num)
    have hbp : (|p 1 - p' 1| * Dd) ^ b ≤ ((a₁ - a₀) * Dd) ^ b :=
      Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_right haa hDd0.le) hb.le
    have e1 := mul_le_mul_of_nonneg_left (hq4 ρ hρ) hM₀
    have e2 := mul_le_mul_of_nonneg_left (hq4 ρ' hρ') hM₀
    have e3 := mul_le_mul_of_nonneg_left hbp hC₀
    have hEU : E ≤ U := by rw [hU]; linarith only [hS, e1, e2, e3]
    have h1 : 1 ≤ 2 ^ c * D ^ c := by
      rw [← Real.mul_rpow (by norm_num) hD0']
      exact Real.one_le_rpow (by linarith) hc0.le
    have h2 : U ≤ U * 2 ^ c * D ^ c := by
      have := mul_le_mul_of_nonneg_left h1 hU0
      linarith only [this]
    have h3 : 0 ≤ (K1 + K2) * D ^ c := by positivity
    nlinarith only [hEU, h2, h3]
  push Not at hbig
  have hD1 : D ≤ 1 := by linarith
  have hr₀ : 0 < D ^ (α / 48) := Real.rpow_pos_of_pos hDpos _
  have hr₀1 : D ^ (α / 48) ≤ 1 := Real.rpow_le_one hD0' hD1 (by positivity)
  have hDr₀ : D ≤ D ^ (α / 48) := by
    have := Real.rpow_le_rpow_of_exponent_ge' hD0' hD1 (by positivity)
      (show α / 48 ≤ 1 by linarith)
    rwa [Real.rpow_one] at this
  have hDα : D ≤ D ^ α := by
    have := Real.rpow_le_rpow_of_exponent_ge' hD0' hD1 hα.le hα1
    rwa [Real.rpow_one] at this
  by_cases hcase : D ^ (α / 48) ≤ ρ ∧ D ^ (α / 48) ≤ ρ'
  · have hL := hLg _ hr₀ hcase.1 hcase.2
    have hTK := timeK_mul_sq_le (R := a₁ * Dd + M + 2 * T / m + 1) hM0 hT hr₀ hr₀1 hCH
    have hSK := spaceK_mul_sq_le (R := a₁ * Dd + M + 2 * T / m + 1) hM0 hT hr₀ hr₀1
    have hWt' : |W (p 0) - W (p' 0)| ≤ CH * D ^ α :=
      (hWt (by linarith)).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (abs_nonneg _) hτD' hα.le) hCH)
    have hE0 := Real.exp_pos (2 * T / m ^ 2)
    have f1 : Real.exp (2 * T / m ^ 2) * (|p 1 - p' 1| * Dd) ≤
        Real.exp (2 * T / m ^ 2) * Dd * D ^ α := by
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hE0.le
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left (haD'.trans hDα) hDd0.le
    have f2 : 2 * |p 0 - p' 0| / m ≤ 2 / m * D ^ α := by
      rw [div_mul_eq_mul_div]
      gcongr
      exact hτD'.trans hDα
    have hsum : (Real.exp (2 * T / m ^ 2) * Dd + CH + 2 / m + 1) * D ^ α =
        Real.exp (2 * T / m ^ 2) * Dd * D ^ α + CH * D ^ α + 2 / m * D ^ α + D ^ α := by ring
    have hΛ : Real.exp (2 * T / m ^ 2) * (|p 1 - p' 1| * Dd) + |W (p 0) - W (p' 0)| +
        2 * |p 0 - p' 0| / m + |ρ - ρ'| ≤
        (Real.exp (2 * T / m ^ 2) * Dd + CH + 2 / m + 1) * D ^ α := by
      rw [hsum]; linarith only [f1, f2, hWt', hρD.trans hDα]
    have hΛ0 : 0 ≤ Real.exp (2 * T / m ^ 2) * (|p 1 - p' 1| * Dd) + |W (p 0) - W (p' 0)| +
        2 * |p 0 - p' 0| / m + |ρ - ρ'| := by positivity
    have hEK := large_arith hL hTK hSK rfl hDpos hD1 hα (abs_nonneg _) hτD' hΛ0 hΛ hCΛ0 hc0
      (by linarith)
    have : K1 * D ^ c ≤ (K1 + K2 + U * 2 ^ c) * D ^ c :=
      mul_le_mul_of_nonneg_right (by linarith) hDc
    exact hEK.trans this
  · have hboth : ρ ≤ 2 * D ^ (α / 48) ∧ ρ' ≤ 2 * D ^ (α / 48) := by
      have h1 := abs_le.1 hρD
      rcases not_and_or.1 hcase with h | h <;> push Not at h <;> constructor <;> linarith
    have hEK := small_arith hS hM₀ hC₀ hb hDd0.le hρ.1 hρ'.1 hboth.1 hboth.2 rfl hDpos hD1
      (abs_nonneg _) haD' hc0 hcα hcb
    have : K2 * D ^ c ≤ (K1 + K2 + U * 2 ^ c) * D ^ c :=
      mul_le_mul_of_nonneg_right (by linarith) hDc
    exact hEK.trans this

end ASep
end QuantumZipper
