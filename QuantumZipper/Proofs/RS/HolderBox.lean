import QuantumZipper.Proofs.RS.HolderGrid
import QuantumZipper.Proofs.RS.HardyLittlewood
import QuantumZipper.Proofs.RS.SmallStep
import QuantumZipper.Proofs.Complex.KoebeHalfPlane

/-!
# RS RH2: Hölder continuity of the reverse map on bounded sets (RS Thm 5.2)

Blueprint `blueprint/EXT_RS_BLUEPRINT.md`, §5, node RH2.

## Main statements

* `RS.norm_deriv_revMap_le_of_grid` (deterministic): if the derivative of `revMap W T` obeys the
  grid bound `‖f'(z_{j,n})‖ ≤ (2^{-n})^{α-1}` for `n ≥ N` and `|j| ≤ M 2^n` with `R + 3 ≤ M`, then
  `‖f' p‖ ≤ C (min 1 (Im p))^{α-1}` on `H ∩ closedBall 0 (R+2)`, with
  `C = max (√(1+4T) 2^N) (4^{C₂})`.
* `RS.ae_revMap_holder_of_ne_four`: for `0 < κ ≤ 12`, `κ ≠ 4`, `T ≥ 0`, there is a deterministic
  `α > 0` such that a.s. `revMap (drive κ B ω) T` is `α`-Hölder on `H ∩ closedBall 0 ρ` for
  every `ρ`.
* `RS.ae_revMap_holder`: the blueprint statement (κ ∈ (0,4), `T > 0`).

## Proof (RS Thm 5.2 proof, last paragraph, p. 22)

"From the Koebe distortion theorem and (5.2)": every `p` with `2^{-n-1} < Im p ≤ 2^{-n}` lies
within `(3/4) 2^{-n}` of a grid point `c = z_{j,n}`, and `ball c (Im c) ⊆ ℍ`, so the Koebe
distortion theorem (`CA.Koebe.norm_deriv_le_distortion`, non-sharp exponent `C₂`; Garnett–Marshall
Thm I.4.5) gives `‖f' p‖ ≤ 4^{C₂} ‖f' c‖ ≤ 4^{C₂} (Im p)^{α-1}`. Points with `Im p ≥ 2^{-N}` use
`‖f' p‖ ≤ √(Im p² + 4T)/Im p` (D3 `norm_deriv_revMap_le_sqrt`). The Hölder bound then follows by
integrating `f'` (D2 `hardyLittlewood_holder`; Pommerenke, *Boundary Behaviour of Conformal
Maps*, §4.6 eq. (7), p. 92). RS use the hyperbolic geodesic; D2 uses the path
`z → z + it → w + it → w`, the standard Hardy–Littlewood argument (Duren Thm 5.1).

Literature: S. Rohde, O. Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005), Thm 5.2
(p. 21) and its proof (p. 22); G. Lawler, *Conformally Invariant Processes in the Plane*, AMS
2005, Prop 7.7 (p. 157).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace QuantumZipper
namespace RS

/-- `√(y² + 4T)/y ≤ √(1+4T) 2^N` when `y ≥ 2^{-N}`. -/
theorem sqrt_div_le_of_two_pow {T y : ℝ} (hT : 0 ≤ T) (hy : 0 < y) {N : ℕ}
    (hyN : ((2 : ℝ) ^ N)⁻¹ ≤ y) :
    Real.sqrt (y ^ 2 + 4 * T) / y ≤ Real.sqrt (1 + 4 * T) * 2 ^ N := by
  have h2N : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
  have hpos : (0 : ℝ) < 2 ^ N := by positivity
  have hyN' : 1 ≤ 2 ^ N * y := by
    have := mul_le_mul_of_nonneg_left hyN hpos.le
    rwa [mul_inv_cancel₀ hpos.ne'] at this
  rw [div_le_iff₀ hy, Real.sqrt_le_left]
  · rw [show (Real.sqrt (1 + 4 * T) * 2 ^ N * y) ^ 2 = (1 + 4 * T) * (2 ^ N * y) ^ 2 by
      rw [mul_assoc, mul_pow, Real.sq_sqrt (by linarith)]]
    have h1 : 1 ≤ (2 ^ N * y) ^ 2 := by nlinarith
    have h2 : y ^ 2 ≤ (2 ^ N * y) ^ 2 := by
      rw [mul_pow]; exact le_mul_of_one_le_left (sq_nonneg y) (one_le_pow₀ h2N)
    nlinarith [mul_nonneg hT (sub_nonneg.2 h1)]
  · positivity

/-- **KD step (RS Thm 5.2 proof, p. 22: "from the Koebe distortion theorem and (5.2)").**
Deterministic passage from the grid bound to the Hardy–Littlewood hypothesis. -/
theorem norm_deriv_revMap_le_of_grid {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T)
    {α : ℝ} (hα1 : α ≤ 1) {R : ℝ} {M N : ℕ} (hM : R + 3 ≤ M)
    (hgrid : ∀ n ≥ N, ∀ j : ℤ, |(j : ℝ)| ≤ M * 2 ^ n →
      ‖deriv (revMap W T) (rsGrid j n)‖ ≤ ((2 : ℝ) ^ n)⁻¹ ^ (α - 1)) :
    ∀ p ∈ H, ‖p‖ ≤ R + 2 → ‖deriv (revMap W T) p‖ ≤
      max (Real.sqrt (1 + 4 * T) * 2 ^ N) ((1 / 4 : ℝ) ^ (-CA.Koebe.koebeDistExp)) *
        (min 1 p.im) ^ (α - 1) := by
  intro p hp hpR
  have hy : 0 < p.im := hp
  set K := Real.sqrt (1 + 4 * T) * 2 ^ N
  set D := (1 / 4 : ℝ) ^ (-CA.Koebe.koebeDistExp)
  have hmin1 : 1 ≤ (min 1 p.im) ^ (α - 1) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (lt_min one_pos hy) (min_le_left _ _)
      (by linarith)
  have hKD : 0 ≤ max K D := le_max_of_le_left (by positivity)
  rcases le_or_gt ((2 : ℝ) ^ N)⁻¹ p.im with hyN | hyN
  · -- far from the boundary: the crude bound.
    calc ‖deriv (revMap W T) p‖ ≤ Real.sqrt (p.im ^ 2 + 4 * T) / p.im :=
          norm_deriv_revMap_le_sqrt hW hT hp
      _ ≤ K := sqrt_div_le_of_two_pow hT hy hyN
      _ ≤ max K D := le_max_left _ _
      _ = max K D * 1 := (mul_one _).symm
      _ ≤ max K D * (min 1 p.im) ^ (α - 1) := mul_le_mul_of_nonneg_left hmin1 hKD
  · -- near the boundary: the nearest grid point and Koebe distortion.
    have h2N : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
    have hy1 : p.im < 1 := hyN.trans_le (inv_le_one_of_one_le₀ h2N)
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near_of_lt_one hy hy1.le (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num)
    simp only [one_div, inv_pow] at hn1 hn2
    set e : ℝ := ((2 : ℝ) ^ n)⁻¹ with he
    have he0 : 0 < e := by positivity
    have hsucc : ((2 : ℝ) ^ (n + 1))⁻¹ = e / 2 := by rw [pow_succ, mul_inv]; ring
    rw [hsucc] at hn1
    have hye : p.im ≤ e := hn2
    have hnN : N ≤ n := by
      by_contra hlt
      rw [not_le] at hlt
      have : ((2 : ℝ) ^ N)⁻¹ ≤ ((2 : ℝ) ^ (n + 1))⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hlt)
      rw [hsucc] at this
      linarith
    set j : ℤ := round (p.re * 2 ^ n)
    have hround := abs_sub_round (p.re * 2 ^ n)
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    have he2 : e * 2 ^ n = 1 := inv_mul_cancel₀ h2n.ne'
    set c := rsGrid j n
    have hcre : c.re = (j : ℝ) * e := rsGrid_re j n
    have hcim : c.im = e := rsGrid_im j n
    -- |Re p − Re c| ≤ e/2
    have hre : |p.re - c.re| ≤ e / 2 := by
      have : p.re - c.re = (p.re * 2 ^ n - j) * e := by
        rw [hcre]; linear_combination (-p.re) * he2
      rw [this, abs_mul, abs_of_pos he0]
      nlinarith
    have him : |p.im - c.im| ≤ e / 2 := by
      rw [hcim, abs_le]; constructor <;> linarith
    have hdist : dist p c ≤ 3 / 4 * e := by
      rw [Complex.dist_eq]
      have hsq : ‖p - c‖ ^ 2 ≤ (3 / 4 * e) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
        have h1 := sq_abs (p.re - c.re)
        have h2 := sq_abs (p.im - c.im)
        have h3 : |p.re - c.re| ^ 2 ≤ (e / 2) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hre 2
        have h4 : |p.im - c.im| ^ 2 ≤ (e / 2) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) him 2
        nlinarith
      nlinarith [norm_nonneg (p - c)]
    have hball : ball c c.im ⊆ H := CA.Koebe.ball_im_subset_upperHalfPlane
    have hpc : p ∈ ball c c.im := by
      rw [mem_ball, hcim]; linarith
    have hK := CA.Koebe.norm_deriv_le_distortion
      ((differentiableOn_revMap W hW hT).mono hball) ((injOn_revMap W hW hT).mono hball) hpc
    have hbase : 1 / 4 ≤ 1 - dist p c / c.im := by
      rw [hcim, le_sub_comm, div_le_iff₀ he0]; linarith
    have hfac : (1 - dist p c / c.im) ^ (-CA.Koebe.koebeDistExp) ≤ D :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hbase
        (neg_nonpos.2 CA.Koebe.koebeDistExp_pos.le)
    -- the grid point is in range
    have hj : |(j : ℝ)| ≤ M * 2 ^ n := by
      have hre' : |p.re| ≤ R + 2 := (Complex.abs_re_le_norm p).trans hpR
      have : |(j : ℝ)| ≤ |p.re * 2 ^ n| + 1 / 2 := by
        have := abs_sub_abs_le_abs_sub (j : ℝ) (p.re * 2 ^ n)
        rw [abs_sub_comm] at this; linarith
      rw [abs_mul, abs_of_pos h2n] at this
      nlinarith
    have hgc := hgrid n hnN j hj
    have hey : e ^ (α - 1) ≤ p.im ^ (α - 1) :=
      Real.rpow_le_rpow_of_nonpos hy hye (by linarith)
    have hmin : min 1 p.im = p.im := min_eq_right hy1.le
    have hD0 : 0 ≤ D := by positivity
    calc ‖deriv (revMap W T) p‖
        ≤ ‖deriv (revMap W T) c‖ * (1 - dist p c / c.im) ^ (-CA.Koebe.koebeDistExp) := hK
      _ ≤ e ^ (α - 1) * D :=
          mul_le_mul hgc hfac (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg he0.le _)
      _ ≤ p.im ^ (α - 1) * D := mul_le_mul_of_nonneg_right hey hD0
      _ ≤ max K D * (min 1 p.im) ^ (α - 1) := by
          rw [hmin, mul_comm]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **RH2 for `κ ∈ (0,12] \ {4}` (RS Thm 5.2, p. 21).** -/
theorem ae_revMap_holder_of_ne_four (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ ≠ 4) (hκ12 : κ ≤ 12) {T : ℝ} (hT : 0 ≤ T) :
    ∃ α > (0 : ℝ), α ≤ 1 ∧ ∀ᵐ ω ∂P, ∀ ρ : ℝ, ∃ C, ∀ z ∈ H, ∀ w ∈ H, ‖z‖ ≤ ρ → ‖w‖ ≤ ρ →
      ‖revMap (drive κ B ω) T z - revMap (drive κ B ω) T w‖ ≤ C * ‖z - w‖ ^ α := by
  obtain ⟨hα0, hα1, -⟩ := rsHolderExp_spec hκ hκ4
  refine ⟨rsHolderExp κ, hα0, hα1, ?_⟩
  filter_upwards [ae_rsGrid_bound hB hκ hκ4 hκ12 hT, hB.cont] with ω hgrid hcont
  intro ρ
  have hW : Continuous (drive κ B ω) := drive_continuous hcont
  set R := max ρ 0
  obtain ⟨M, hM⟩ := exists_nat_ge (R + 3)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hgrid M)
  have hbd := norm_deriv_revMap_le_of_grid hW hT hα1 hM hN
  obtain ⟨C', -, hC'⟩ := hardyLittlewood_holder (differentiableOn_revMap _ hW hT)
    (le_max_of_le_left (by positivity)) hα0 hα1 hbd
  refine ⟨C', fun z hz w hw hzρ hwρ => hC' z hz w hw ?_ ?_⟩
  · exact hzρ.trans (le_max_left _ _)
  · exact hwρ.trans (le_max_left _ _)

/-- **RH2 (blueprint statement; RS Thm 5.2, p. 21, for the reverse map at a fixed time).** -/
theorem ae_revMap_holder (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {T : ℝ}
    (hT : 0 < T) :
    ∃ α > (0 : ℝ), ∀ᵐ ω ∂P, ∀ ρ : ℝ, ∃ C, ∀ z ∈ H, ∀ w ∈ H, ‖z‖ ≤ ρ → ‖w‖ ≤ ρ →
      ‖revMap (drive κ B ω) T z - revMap (drive κ B ω) T w‖ ≤ C * ‖z - w‖ ^ α := by
  obtain ⟨α, hα0, -, h⟩ := ae_revMap_holder_of_ne_four hB hκ hκ4.ne (by linarith) hT.le
  exact ⟨α, hα0, h⟩

end RS
end QuantumZipper
