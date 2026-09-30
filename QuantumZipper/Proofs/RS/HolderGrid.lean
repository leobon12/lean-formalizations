import QuantumZipper.Proofs.RS.TailBounds

/-!
# RS RH1: the derivative bound on the Whitney grid at a fixed time

Blueprint `blueprint/EXT_RS_BLUEPRINT.md`, §5, node RH1.

## Main statement

* `RS.ae_rsGrid_bound`: for `0 < κ ≤ 12`, `κ ≠ 4`, `T ≥ 0`, and the deterministic exponent
  `α = rsHolderExp κ ∈ (0, 1]`, almost surely, for every box half-width `M : ℕ`, for all large
  `n` and all `j : ℤ` with `|j| ≤ M 2^n`,
  `‖(revMap (drive κ B ω) T)' (z_{j,n})‖ ≤ (2^{-n})^{α-1}`, where `z_{j,n} = (j + i) 2^{-n}`
  (`rsGrid j n`).

This is (5.2) of Rohde–Schramm (with `h = α`), for the reverse map at a fixed time. The project
needs `κ < 4` (`Blueprint.RevMapHolder`); the range proved here is `κ ∈ (0,12] \ {4}`, which is
RS's first case (`b = 1/4 + 1/κ`). RS's second case (`κ > 12`, `b = 4/κ`) is not formalized.

## Proof (RS Thm 5.2 proof, p. 22)

RS Cor 3.5 (project: E2 `rs_tail_bound`, with `r = rsR2 κ = 1/4 + 1/κ` and `β = α`) gives
`P(|u_T'(z_{j,n})| > 2^{-n(α-1)}) ≤ (|z|/Im z)^{2r} 2^{-n(1-α)(λ+ζ)}`, and
`|z_{j,n}|/Im z_{j,n} = |j + i| ≤ (M+1) 2^n`. Summing over the `2M2^n + 1` values of `j` gives
`≤ (2M+1)(M+1)^{2r} 2^{n(1 + 2r - (1-α)(λ+ζ))}`, summable since `λ + ζ - 2r > 1` (`κ ≠ 4`,
`one_lt_rsLam_add_rsZeta_sub_rsR2`) and `α` is small. Borel–Cantelli
(`MeasureTheory.ae_eventually_notMem`) concludes. RS index the grid by the box `[-1,1]×(0,1]`
after scaling; we keep `T` and use boxes of every integer half-width `M` instead (no scaling
needed, since E2 holds for every `T` and `z`).

Literature: S. Rohde, O. Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005), Thm 5.2 and
its proof (pp. 21–22), (5.2); G. Lawler, *Conformally Invariant Processes in the Plane*, AMS
2005, Prop 7.7 (p. 157).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace QuantumZipper
namespace RS

/-- Whitney grid point `z_{j,n} = (j + i) 2^{-n}` (RS Thm 5.2 proof, p. 21). -/
def rsGrid (j : ℤ) (n : ℕ) : ℂ := ((j : ℂ) + Complex.I) * ((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ)

theorem rsGrid_im (j : ℤ) (n : ℕ) : (rsGrid j n).im = ((2 : ℝ) ^ n)⁻¹ := by
  simp only [rsGrid, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.intCast_re, Complex.intCast_im, Complex.I_re,
    Complex.I_im]
  ring

theorem rsGrid_re (j : ℤ) (n : ℕ) : (rsGrid j n).re = (j : ℝ) * ((2 : ℝ) ^ n)⁻¹ := by
  simp only [rsGrid, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.intCast_re, Complex.intCast_im, Complex.I_re,
    Complex.I_im]
  ring

theorem rsGrid_mem (j : ℤ) (n : ℕ) : rsGrid j n ∈ H := by
  show 0 < (rsGrid j n).im
  rw [rsGrid_im]; positivity

theorem norm_rsGrid_div_im_le (j : ℤ) (n : ℕ) :
    ‖rsGrid j n‖ / (rsGrid j n).im ≤ |(j : ℝ)| + 1 := by
  have hpos : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := by positivity
  rw [rsGrid_im, rsGrid, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos.le,
    mul_div_assoc, div_self hpos.ne', mul_one]
  calc ‖(j : ℂ) + Complex.I‖ ≤ ‖(j : ℂ)‖ + ‖Complex.I‖ := norm_add_le _ _
    _ = |(j : ℝ)| + 1 := by rw [Complex.norm_intCast, Complex.norm_I]

/-- The RH1 exponent: `α = min 1 (d / (2s))` with `s = λ + ζ` and `d = s − 2r − 1 > 0` at
`r = rsR2 κ` (RS's `h < (κ−4)²/((κ+4)(κ+12))`, p. 22, up to the choice of constant). -/
def rsHolderExp (κ : ℝ) : ℝ :=
  min 1 ((rsLam κ (rsR2 κ) + rsZeta κ (rsR2 κ) - 2 * rsR2 κ - 1) /
    (2 * (rsLam κ (rsR2 κ) + rsZeta κ (rsR2 κ))))

theorem rsHolderExp_spec {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≠ 4) :
    0 < rsHolderExp κ ∧ rsHolderExp κ ≤ 1 ∧
      1 + 2 * rsR2 κ - (1 - rsHolderExp κ) * (rsLam κ (rsR2 κ) + rsZeta κ (rsR2 κ)) < 0 := by
  have hd := one_lt_rsLam_add_rsZeta_sub_rsR2 hκ hκ4
  have hr := rsR2_nonneg hκ
  set s := rsLam κ (rsR2 κ) + rsZeta κ (rsR2 κ)
  set r := rsR2 κ
  have hs : 0 < s := by linarith
  have hq : 0 < (s - 2 * r - 1) / (2 * s) := div_pos (by linarith) (by linarith)
  refine ⟨lt_min one_pos hq, min_le_left _ _, ?_⟩
  have hαs : rsHolderExp κ * s ≤ (s - 2 * r - 1) / 2 := by
    calc rsHolderExp κ * s ≤ (s - 2 * r - 1) / (2 * s) * s :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hs.le
      _ = (s - 2 * r - 1) / 2 := by field_simp
  nlinarith

/-- Per-point bound: `(|z|/Im z)^{2r} (Im z)^c ≤ (M+1)^{2r} (2^{2r-c})^n` on the grid. -/
theorem rsGrid_term_le {M : ℕ} {n : ℕ} {j : ℤ} (hj : |(j : ℝ)| ≤ M * 2 ^ n) {r c : ℝ}
    (hr : 0 ≤ r) :
    (‖rsGrid j n‖ / (rsGrid j n).im) ^ (2 * r) * (rsGrid j n).im ^ c ≤
      ((M : ℝ) + 1) ^ (2 * r) * ((2 : ℝ) ^ (2 * r - c)) ^ n := by
  have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hq : 0 ≤ ‖rsGrid j n‖ / (rsGrid j n).im :=
    div_nonneg (norm_nonneg _) (rsGrid_mem j n).le
  have hle : ‖rsGrid j n‖ / (rsGrid j n).im ≤ ((M : ℝ) + 1) * 2 ^ n := by
    have := norm_rsGrid_div_im_le j n
    nlinarith
  have h1 : (‖rsGrid j n‖ / (rsGrid j n).im) ^ (2 * r) ≤ (((M : ℝ) + 1) * 2 ^ n) ^ (2 * r) :=
    Real.rpow_le_rpow hq hle (by linarith)
  have h2 : (((M : ℝ) + 1) * 2 ^ n) ^ (2 * r) * (rsGrid j n).im ^ c =
      ((M : ℝ) + 1) ^ (2 * r) * ((2 : ℝ) ^ (2 * r - c)) ^ n := by
    rw [rsGrid_im, Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (by positivity),
      ← Real.rpow_pow_comm (by norm_num), ← Real.rpow_pow_comm (by norm_num),
      Real.rpow_sub (by norm_num), div_pow]
    ring
  rw [← h2]
  exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (rsGrid_mem j n).le _)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **RH1 (RS Thm 5.2 proof, (5.2), p. 22).** Almost surely, on every box `|Re| ≤ M`, the
derivative of the reverse map at the level-`n` grid points is at most `(2^{-n})^{α−1}` for all
large `n`. -/
theorem ae_rsGrid_bound (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≠ 4)
    (hκ12 : κ ≤ 12) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ M : ℕ, ∀ᶠ n in atTop, ∀ j : ℤ, |(j : ℝ)| ≤ M * 2 ^ n →
      ‖deriv (revMap (drive κ B ω) T) (rsGrid j n)‖ ≤ ((2 : ℝ) ^ n)⁻¹ ^ (rsHolderExp κ - 1) := by
  obtain ⟨-, -, hneg⟩ := rsHolderExp_spec hκ hκ4
  set α := rsHolderExp κ
  set r := rsR2 κ
  set s := rsLam κ r + rsZeta κ r
  have hr : 0 ≤ r := rsR2_nonneg hκ
  rw [ae_all_iff]
  intro M
  let E : ℤ → ℕ → Set Ω := fun j n =>
    {ω | (rsGrid j n).im ^ (α - 1) < ‖deriv (revMap (drive κ B ω) T) (rsGrid j n)‖}
  let N : ℕ → ℤ := fun n => ((M * 2 ^ n : ℕ) : ℤ)
  let A : ℕ → Set Ω := fun n => ⋃ j ∈ Finset.Icc (-N n) (N n), E j n
  set q : ℝ := (2 : ℝ) ^ (2 * r - (1 - α) * s)
  set K : ℝ := (2 * M + 1) * ((M : ℝ) + 1) ^ (2 * r)
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have h2q : 2 * q < 1 := by
    have : 2 * q = (2 : ℝ) ^ (1 + 2 * r - (1 - α) * s) := by
      rw [show 1 + 2 * r - (1 - α) * s = 1 + (2 * r - (1 - α) * s) by ring,
        Real.rpow_add (by norm_num), Real.rpow_one]
    rw [this]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hneg
  have hK : 0 ≤ K := by positivity
  have hlevel : ∀ n, P (A n) ≤ ENNReal.ofReal (K * (2 * q) ^ n) := by
    intro n
    have hpt : ∀ j ∈ Finset.Icc (-N n) (N n),
        P (E j n) ≤ ENNReal.ofReal (((M : ℝ) + 1) ^ (2 * r) * q ^ n) := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      have hjR : |(j : ℝ)| ≤ M * 2 ^ n := by
        rw [abs_le]
        have h1 : ((-N n : ℤ) : ℝ) ≤ j := by exact_mod_cast hj.1
        have h2 : (j : ℝ) ≤ ((N n : ℤ) : ℝ) := by exact_mod_cast hj.2
        simp only [N] at h1 h2
        push_cast at h1 h2
        constructor <;> linarith
      refine (rs_tail_bound hB hκ hr hT (rsGrid_mem j n) (rsLam_rsR2_nonneg hκ)
        (rsZeta_rsR2_nonneg hκ hκ12) α).trans (ENNReal.ofReal_le_ofReal ?_)
      exact rsGrid_term_le hjR hr
    have hcard : (((Finset.Icc (-N n) (N n)).card : ℕ) : ℝ) = 2 * (M * 2 ^ n) + 1 := by
      have : (((Finset.Icc (-N n) (N n)).card : ℕ) : ℤ) = 2 * N n + 1 := by
        rw [Int.card_Icc, Int.toNat_of_nonneg (by simp only [N]; omega)]; ring
      have h' : ((((Finset.Icc (-N n) (N n)).card : ℕ) : ℤ) : ℝ) = ((2 * N n + 1 : ℤ) : ℝ) := by
        rw [this]
      simp only [N] at h'
      push_cast at h'
      exact_mod_cast h'
    calc P (A n) ≤ ∑ j ∈ Finset.Icc (-N n) (N n), P (E j n) := measure_biUnion_finset_le _ _
      _ ≤ ∑ j ∈ Finset.Icc (-N n) (N n), ENNReal.ofReal (((M : ℝ) + 1) ^ (2 * r) * q ^ n) :=
          Finset.sum_le_sum hpt
      _ = ENNReal.ofReal ((((Finset.Icc (-N n) (N n)).card : ℕ) : ℝ) *
            (((M : ℝ) + 1) ^ (2 * r) * q ^ n)) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (K * (2 * q) ^ n) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hcard, mul_pow]
          have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
          have hA : 0 ≤ ((M : ℝ) + 1) ^ (2 * r) * q ^ n := by positivity
          have hc : 2 * ((M : ℝ) * 2 ^ n) + 1 ≤ (2 * M + 1) * 2 ^ n := by nlinarith
          calc (2 * ((M : ℝ) * 2 ^ n) + 1) * (((M : ℝ) + 1) ^ (2 * r) * q ^ n)
              ≤ (2 * M + 1) * 2 ^ n * (((M : ℝ) + 1) ^ (2 * r) * q ^ n) :=
                mul_le_mul_of_nonneg_right hc hA
            _ = K * (2 ^ n * q ^ n) := by simp only [K]; ring
  have hsum : ∑' n, P (A n) ≠ ∞ := by
    have hsm : Summable fun n : ℕ => K * (2 * q) ^ n :=
      (summable_geometric_of_lt_one (by positivity) h2q).mul_left K
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' n, K * (2 * q) ^ n)) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsm]
    exact ENNReal.tsum_le_tsum hlevel
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with n hn j hj
  have hjmem : j ∈ Finset.Icc (-N n) (N n) := by
    rw [Finset.mem_Icc]
    obtain ⟨h1, h2⟩ := abs_le.1 hj
    have hN : ((N n : ℤ) : ℝ) = (M : ℝ) * 2 ^ n := by simp only [N]; push_cast; ring
    constructor
    · have : ((-N n : ℤ) : ℝ) ≤ (j : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · have : (j : ℝ) ≤ ((N n : ℤ) : ℝ) := by linarith
      exact_mod_cast this
  have hnot : ω ∉ E j n := fun h => hn (Set.mem_biUnion hjmem h)
  simp only [E, Set.mem_ofPred_eq, not_lt] at hnot
  rwa [rsGrid_im] at hnot

end RS
end QuantumZipper
