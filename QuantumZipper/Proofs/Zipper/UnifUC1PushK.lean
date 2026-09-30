import QuantumZipper.Proofs.Zipper.UnifRC3Split
import QuantumZipper.Proofs.GFF.CoordRegEnergyBasic

/-!
# UNIF-RC3-PUSH0 (decision D33), part 1: explicit constants in `CoordReg.abs_energy_push_le`

`CoordReg.abs_hK_le` and `CoordReg.abs_energy_push_le` state their constants existentially. The
uniform (in the time parameters) bound PUSH0 needs them explicitly. This file restates both with
the constants exposed; the proofs are the proofs of those two lemmas (`CoordRegHarm.lean`,
`CoordRegEnergyBasic.lean`), copied with the constants turned into hypotheses:

* `abs_hK_le_explicit`: `|hK W T u v| ≤ |log M| + 2|log B| + 3(|log Im u| + |log Im v|)` for any
  `M ≥ √(R² + 4T)`, `B ≥ 2 Bf, 2R` (and `R ≥ 1`), where `Bf` bounds `‖revMap W T‖` on `ℍ ∩ closedBall 0 R`;
* `abs_energy_push_le_explicit`: the energy of `f_* ν_r − f_* ν` is
  `≤ 2(C r^α/α)·ν(ℂ) + 2·M₁·c r^γ`, `M₁ = 2(K m + 3(C₀ m + L)) + 3m(C₀ + 2)` (`m = ν(ℂ)`,
  `L = ∫ |log Im| dν`).

Sources: as for `CoordReg.abs_energy_push_le` (own argument there; the energy estimate is the
Loewner-transported analogue of Hu–Miller–Peres, Ann. Probab. 38 (2010), Prop. 2.1).
-/

noncomputable section

open MeasureTheory Filter Metric Set
open scoped ENNReal Real ComplexConjugate Topology

namespace QuantumZipper
namespace RegUnif

open CircleFubini FrostmanReg SmoothConv CoordReg

/-- `CoordReg.abs_hK_le` with explicit constants. -/
theorem abs_hK_le_explicit {W : ℝ → ℝ} {T : ℝ} (hW : Continuous W) (hT : 0 ≤ T) {R Bf M B : ℝ}
    (hBf : ∀ z ∈ H, ‖z‖ ≤ R → ‖revMap W T z‖ ≤ Bf) (hM : Real.sqrt (R ^ 2 + 4 * T) ≤ M)
    (hB2 : 2 * Bf ≤ B) (hBR : 2 * R ≤ B) (hR1 : 1 ≤ R) :
    ∀ u ∈ H, ∀ v ∈ H, ‖u‖ ≤ R → ‖v‖ ≤ R →
      |CoordReg.hK W T u v| ≤
        (|Real.log M| + 2 * |Real.log B|) + 3 * (|Real.log u.im| + |Real.log v.im|) := by
  intro u hu v hv huR hvR
  have hu0 : 0 < u.im := hu
  have hv0 : 0 < v.im := hv
  have hfu := TwoPoint.im_revMap_pos hW hu hT
  have hfv := TwoPoint.im_revMap_pos hW hv hT
  have hIu : u.im ≤ (revMap W T u).im := im_le_im_revMap W hW u hu hT
  have hIv : v.im ≤ (revMap W T v).im := im_le_im_revMap W hW v hv hT
  have hMu : (revMap W T u).im ≤ M := by
    have h1 := TwoPoint.im_revMap_sq_le hW hu hT
    have h2 : u.im ≤ R := (Complex.im_le_norm u).trans huR
    exact (Real.le_sqrt_of_sq_le (by nlinarith)).trans hM
  have hMv : (revMap W T v).im ≤ M := by
    have h1 := TwoPoint.im_revMap_sq_le hW hv hT
    have h2 : v.im ≤ R := (Complex.im_le_norm v).trans hvR
    exact (Real.le_sqrt_of_sq_le (by nlinarith)).trans hM
  -- term 1
  have t1 : |Real.log ‖dslope (revMap W T) v u‖| ≤
      |Real.log M| + |Real.log u.im| + |Real.log v.im| := by
    by_cases h : u = v
    · subst h
      rw [dslope_same]
      have := TwoPoint.abs_log_norm_deriv_revMap_le hW hT hu
        ((Complex.im_le_norm u).trans huR)
      have hsq1 : 1 ≤ Real.sqrt (R ^ 2 + 4 * T) := Real.le_sqrt_of_sq_le (by nlinarith)
      have hlm : |Real.log (Real.sqrt (R ^ 2 + 4 * T))| ≤ |Real.log M| := by
        rw [abs_of_nonneg (Real.log_nonneg hsq1), abs_of_nonneg (Real.log_nonneg (hsq1.trans hM))]
        exact Real.log_le_log (by linarith) hM
      linarith [abs_nonneg (Real.log u.im)]
    · have hd1 : revMap W T u - revMap W T v ≠ 0 :=
        sub_ne_zero.2 fun e => h (injOn_revMap W hW hT hu hv e)
      have hd2 : u - v ≠ 0 := sub_ne_zero.2 h
      have n1 : 0 < ‖revMap W T u - revMap W T v‖ := norm_pos_iff.2 hd1
      have n2 : 0 < ‖u - v‖ := norm_pos_iff.2 hd2
      rw [dslope_of_ne _ h, slope_def_field, norm_div, Real.log_div n1.ne' n2.ne']
      have lo := TwoPoint.twoPoint_lower_sq hW hu hv hT
      have up := TwoPoint.twoPoint_upper_sq hW hu hv hT
      have L1 := Real.log_le_log (mul_pos (pow_pos n2 2) (mul_pos hu0 hv0)) lo
      have L2 := Real.log_le_log (mul_pos (pow_pos n1 2) (mul_pos hu0 hv0)) up
      have e1 : Real.log (‖u - v‖ ^ 2 * (u.im * v.im)) =
          2 * Real.log ‖u - v‖ + (Real.log u.im + Real.log v.im) := by
        rw [Real.log_mul (pow_ne_zero 2 n2.ne') (mul_pos hu0 hv0).ne', Real.log_pow,
          Real.log_mul hu0.ne' hv0.ne']; push_cast; ring
      have e2 : Real.log (‖revMap W T u - revMap W T v‖ ^ 2 * (u.im * v.im)) =
          2 * Real.log ‖revMap W T u - revMap W T v‖ + (Real.log u.im + Real.log v.im) := by
        rw [Real.log_mul (pow_ne_zero 2 n1.ne') (mul_pos hu0 hv0).ne', Real.log_pow,
          Real.log_mul hu0.ne' hv0.ne']; push_cast; ring
      have e3 : Real.log (‖u - v‖ ^ 2 * ((revMap W T u).im * (revMap W T v).im)) =
          2 * Real.log ‖u - v‖ + (Real.log (revMap W T u).im + Real.log (revMap W T v).im) := by
        rw [Real.log_mul (pow_ne_zero 2 n2.ne') (mul_pos hfu hfv).ne', Real.log_pow,
          Real.log_mul hfu.ne' hfv.ne']; push_cast; ring
      have e4 : Real.log (‖revMap W T u - revMap W T v‖ ^ 2 *
          ((revMap W T u).im * (revMap W T v).im)) =
          2 * Real.log ‖revMap W T u - revMap W T v‖ +
            (Real.log (revMap W T u).im + Real.log (revMap W T v).im) := by
        rw [Real.log_mul (pow_ne_zero 2 n1.ne') (mul_pos hfu hfv).ne', Real.log_pow,
          Real.log_mul hfu.ne' hfv.ne']; push_cast; ring
      rw [e1, e4] at L1
      rw [e2, e3] at L2
      have a1 := Real.log_le_log hu0 hIu
      have a2 := Real.log_le_log hv0 hIv
      have a3 := Real.log_le_log hfu hMu
      have a4 := Real.log_le_log hfv hMv
      rw [abs_le]
      constructor <;>
        linarith [le_abs_self (Real.log M), neg_abs_le (Real.log M), le_abs_self (Real.log u.im),
          neg_abs_le (Real.log u.im), le_abs_self (Real.log v.im), neg_abs_le (Real.log v.im)]
  -- term 2
  have t2 : |Real.log ‖revMap W T u - conj (revMap W T v)‖| ≤ |Real.log u.im| + |Real.log B| := by
    refine abs_log_le_of_mem' hu0 ?_ ?_
    · have := im_add_im_le_norm_sub_conj' (revMap W T u) (revMap W T v)
      linarith
    · calc ‖revMap W T u - conj (revMap W T v)‖ ≤ ‖revMap W T u‖ + ‖conj (revMap W T v)‖ :=
            norm_sub_le _ _
        _ ≤ 2 * Bf := by rw [Complex.norm_conj]; linarith [hBf u hu huR, hBf v hv hvR]
        _ ≤ B := hB2
  -- term 3
  have t3 : |Real.log ‖u - conj v‖| ≤ |Real.log u.im| + |Real.log B| := by
    refine abs_log_le_of_mem' hu0 ?_ ?_
    · have := im_add_im_le_norm_sub_conj' u v
      linarith
    · calc ‖u - conj v‖ ≤ ‖u‖ + ‖conj v‖ := norm_sub_le _ _
        _ ≤ 2 * R := by rw [Complex.norm_conj]; linarith
        _ ≤ B := hBR
  have b1 := abs_le.1 t1
  have b2 := abs_le.1 t2
  have b3 := abs_le.1 t3
  unfold CoordReg.hK
  rw [abs_le]
  constructor <;>
    linarith [abs_nonneg (Real.log u.im), abs_nonneg (Real.log v.im),
      abs_nonneg (Real.log M), abs_nonneg (Real.log B)]

/-- `CoordReg.abs_energy_push_le` with explicit constants. -/
theorem abs_energy_push_le_explicit {W : ℝ → ℝ} {T : ℝ} (hW : Continuous W) (hT : 0 ≤ T)
    {R α C c γ K C₀ : ℝ} {ν : Measure ℂ} [IsFiniteMeasure ν] (hK0 : 0 ≤ K)
    (hKb : ∀ u ∈ H, ∀ v ∈ H, ‖u‖ ≤ R + 1 → ‖v‖ ≤ R + 1 →
      |CoordReg.hK W T u v| ≤ K + 3 * (|Real.log u.im| + |Real.log v.im|))
    (hC₀ : 0 ≤ C₀) (hLA : ∀ z ∈ H, ‖z‖ ≤ R + 1 → ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∫ u, |Real.log u.im| ∂foldedCircle z r ≤ C₀ + |Real.log z.im|)
    (hsupp : ν (closedBall 0 R ∩ Hbar)ᶜ = 0) (hνH : ∀ᵐ z ∂ν, z ∈ H)
    (hF : QuantumZipper.IsFrostman ν α C) (hα : 0 < α)
    (hlν : Integrable (fun z : ℂ => |Real.log z.im|) ν) (hS : CoordReg.StripBound ν c γ)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    |kernelCov2 neumannH
        ((ν.bind fun z => foldedCircle z r).map (revMap W T), ν.map (revMap W T))
        ((ν.bind fun z => foldedCircle z r).map (revMap W T), ν.map (revMap W T))| ≤
      2 * (C * r ^ α / α) * (ν Set.univ).toReal +
        2 * (2 * (K * ν.real univ + 3 * (C₀ * ν.real univ + ∫ z, |Real.log z.im| ∂ν)) +
          3 * ν.real univ * (C₀ + 2)) * (c * r ^ γ) := by
  set m := ν.real univ with hm
  set L := ∫ z, |Real.log z.im| ∂ν with hL
  have hm0 : 0 ≤ m := measureReal_nonneg
  have hL0 : 0 ≤ L := integral_nonneg fun _ => abs_nonneg _
  set M₁ := 2 * (K * m + 3 * (C₀ * m + L)) + 3 * m * (C₀ + 2) with hM₁
  have := isFiniteMeasure_bind_circle (r := r) ν
  set νr := ν.bind fun z => foldedCircle z r with hνr
  have hν : ∀ᵐ z ∂ν, z ∈ H ∧ ‖z‖ ≤ R := by
    filter_upwards [ae_mem_of_compl_null_frostman hsupp, hνH] with z h1 h2
    exact ⟨h2, by simpa using h1.1⟩
  have hν1 : ∀ᵐ z ∂ν, z ∈ H ∧ ‖z‖ ≤ R + 1 := hν.mono fun z hz => ⟨hz.1, by linarith [hz.2]⟩
  have hνr1 : ∀ᵐ u ∂νr, u ∈ H ∧ ‖u‖ ≤ R + 1 := by
    filter_upwards [bind_fc_mem_H_norm ν hr (hν.mono fun z hz => hz.2)] with u hu
    exact ⟨hu.1, by linarith [hu.2]⟩
  have hLA' : ∀ z ∈ H, ‖z‖ ≤ R → ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∫ u, |Real.log u.im| ∂foldedCircle z r ≤ C₀ + |Real.log z.im| :=
    fun z hz hzR => hLA z hz (by linarith)
  obtain ⟨hlr, hlr'⟩ := integrable_abs_log_im_bind hC₀ hLA' hν hlν hr hr1
  have hA0 := isAdmissibleH_of_frostman hsupp hF hα
  have hA1 := isAdmissibleH_bind_fc_of_supp hsupp hr
  have hmr : νr.real univ = m := by
    rw [hm]; simp only [Measure.real, hνr, bind_fc_univ]
  have e11 := kernelCov_map_revMap_eq hW hT hA1 hA1 hνr1 hνr1 hlr hlr
  have e10 := kernelCov_map_revMap_eq hW hT hA1 hA0 hνr1 hν1 hlr hlν
  have e01 := kernelCov_map_revMap_eq hW hT hA0 hA1 hν1 hνr1 hlν hlr
  have e00 := kernelCov_map_revMap_eq hW hT hA0 hA0 hν1 hν1 hlν hlν
  have hsym := integral_PhiK_symm hW hT hν1 hνr1 hlν hlr
  have hN := abs_energy_frostman_le hsupp hF hα hr
  have b1 := abs_integral_PhiK_bind_sub_le hW hT hK0 hKb hC₀ hLA hν hlν hS hνr1 hlr hr hr1
  have b0 := abs_integral_PhiK_bind_sub_le hW hT hK0 hKb hC₀ hLA hν hlν hS hν1 hlν hr hr1
  have hcr := strip_nonneg hS hr hr1
  have hM1 : (2 * (K * νr.real univ + 3 * ∫ v, |Real.log v.im| ∂νr) +
      3 * νr.real univ * (C₀ + 2)) ≤ M₁ := by
    rw [hmr, hM₁]; nlinarith
  have hM0 : (2 * (K * ν.real univ + 3 * ∫ v, |Real.log v.im| ∂ν) +
      3 * ν.real univ * (C₀ + 2)) ≤ M₁ := by
    rw [hM₁]; nlinarith [mul_nonneg hC₀ hm0]
  have b1' := b1.trans (mul_le_mul_of_nonneg_right hM1 hcr)
  have b0' := b0.trans (mul_le_mul_of_nonneg_right hM0 hcr)
  unfold kernelCov2 at hN ⊢
  simp only at hN ⊢
  rw [e11, e10, e01, e00]
  rw [abs_le] at hN b1' b0' ⊢
  constructor <;> linarith [hN.1, hN.2, b1'.1, b1'.2, b0'.1, b0'.2]

end RegUnif
end QuantumZipper
