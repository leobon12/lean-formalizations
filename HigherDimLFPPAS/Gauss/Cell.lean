import HigherDimLFPPAS.Gauss.FieldProc
import HigherDimLFPPAS.Gauss.CubeSup
import HigherDimLFPPAS.Gauss.Lattice

/-!
# The cell process of (2.7) (packet F2b)

For `n ∈ ℕ` and `k ∈ ℤ^d`, the cell process on `[0,1]^{1+d}` (coordinates `p = (s, v)`) is
`X_{n,k}(s, v) = H_{n+s}(e^{-n}(k + v)) - H_n(e^{-n} k)` with `H_t(x) = h ∗ K_{e^{-t}}(x)`
(`cellProcF2b`). By P4.1′ its increments satisfy `E (X_p - X_q)² ≤ L² ‖p - q‖_∞` with `L` depending
only on `d, κ`, and `Var X_p ≤ L²` (planning audit MA3, Details P4.2; the law invariance P4.3 is
not needed: the bounds are uniform). The cube tail `cube_sup_tail_F2b` then gives a Gaussian tail of
`sup |X_{n,k}|`, uniform in `(n, k)` (`cell_sup_tail_F2b`).
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

/-- The spatial coordinates `v` of a point `p = (s, v)` of `[0,1]^{1+d}`. -/
def cubeSpaceF2b (p : Fin (d + 1) → unitInterval) : Fin d → ℝ := fun i => (p i.succ : ℝ)

lemma continuous_cubeSpaceF2b : Continuous (cubeSpaceF2b (d := d)) :=
  continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i.succ)

lemma cubeSpaceF2b_zero : cubeSpaceF2b (0 : Fin (d + 1) → unitInterval) = 0 := by
  funext i
  simp [cubeSpaceF2b]

lemma abs_sub_le_cubeCoord (p q : Fin (d + 1) → unitInterval) (i : Fin (d + 1)) :
    |(p i : ℝ) - (q i : ℝ)| ≤ ‖cubeCoordF2b p - cubeCoordF2b q‖ := by
  have h := norm_le_pi_norm (cubeCoordF2b p - cubeCoordF2b q) i
  simpa only [cubeCoordF2b, Pi.sub_apply, Real.norm_eq_abs] using h

lemma norm_cubeSpace_sub_le (p q : Fin (d + 1) → unitInterval) :
    ‖cubeSpaceF2b p - cubeSpaceF2b q‖ ≤ ‖cubeCoordF2b p - cubeCoordF2b q‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  simpa only [cubeSpaceF2b, Pi.sub_apply, Real.norm_eq_abs] using abs_sub_le_cubeCoord p q i.succ

/-- The top index `(n + s, e^{-n}(k + v))` of the cell process. -/
def cellTopF2b (n : ℕ) (k : Fin d → ℤ) (p : Fin (d + 1) → unitInterval) : ℝ × Rd d :=
  ((n : ℝ) + (p 0 : ℝ), cellPtF2b (Real.exp (-(n : ℝ))) k (cubeSpaceF2b p))

/-- The base index `(n, e^{-n} k)` of the cell process. -/
def cellBaseF2b (n : ℕ) (k : Fin d → ℤ) : ℝ × Rd d :=
  ((n : ℝ), cellPtF2b (Real.exp (-(n : ℝ))) k 0)

lemma cellTopF2b_zero (n : ℕ) (k : Fin d → ℤ) :
    cellTopF2b n k 0 = cellBaseF2b n k := by
  simp only [cellTopF2b, cellBaseF2b, cubeSpaceF2b_zero]
  congr 1
  simp

lemma continuous_cellTopF2b (n : ℕ) (k : Fin d → ℤ) : Continuous (cellTopF2b (d := d) n k) :=
  (continuous_const.add (continuous_subtype_val.comp (continuous_apply 0))).prodMk
    ((continuous_cellPtF2b _ k).comp continuous_cubeSpaceF2b)

/-- **The cell process** `X_{n,k}(s, v) = H_{n+s}(e^{-n}(k + v)) - H_n(e^{-n} k)`. -/
def cellProcF2b (κ : Rd d → ℝ) (h : Ω → DistRd d) (n : ℕ) (k : Fin d → ℤ)
    (p : Fin (d + 1) → unitInterval) (ω : Ω) : ℝ :=
  fieldF2b κ h (cellTopF2b n k p) ω - fieldF2b κ h (cellBaseF2b n k) ω

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
lemma cellProcF2b_zero (n : ℕ) (k : Fin d → ℤ) (ω : Ω) : cellProcF2b κ h n k 0 ω = 0 := by
  simp only [cellProcF2b, cellTopF2b_zero, sub_self]

/-- The uniform increment constant of the cell processes. -/
theorem exists_cell_increment_F2b (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    ∃ L : ℝ, 0 < L ∧ ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, IsNormalizedLGF h P → ∀ (n : ℕ) (k : Fin d → ℤ)
        (p q : Fin (d + 1) → unitInterval),
        ∫ ω, (cellProcF2b κ h n k p ω - cellProcF2b κ h n k q ω) ^ 2 ∂P ≤
          L ^ 2 * ‖cubeCoordF2b p - cubeCoordF2b q‖ := by
  obtain ⟨C₃, hC₃0, hC₃⟩ := exists_integral_sq_convMollify_sub_le_F2b hd hκ
  refine ⟨√(C₃ * (1 + 3 * √d) + 1), Real.sqrt_pos.2 (by positivity),
    fun {Ω} _ {P} _ {h} hh n k p q => ?_⟩
  rw [Real.sq_sqrt (by positivity)]
  set Δ := ‖cubeCoordF2b p - cubeCoordF2b q‖ with hΔ
  have hΔ0 : 0 ≤ Δ := norm_nonneg _
  have he : (fun ω => (cellProcF2b κ h n k p ω - cellProcF2b κ h n k q ω) ^ 2) =
      fun ω => (convMollify κ (Real.exp (-((n : ℝ) + (p 0 : ℝ)))) (h ω)
          (cellPtF2b (Real.exp (-(n : ℝ))) k (cubeSpaceF2b p)) -
        convMollify κ (Real.exp (-((n : ℝ) + (q 0 : ℝ)))) (h ω)
          (cellPtF2b (Real.exp (-(n : ℝ))) k (cubeSpaceF2b q))) ^ 2 := by
    funext ω
    simp only [cellProcF2b, fieldF2b, cellTopF2b]
    ring
  have h0 : |((n : ℝ) + (p 0 : ℝ)) - ((n : ℝ) + (q 0 : ℝ))| ≤ Δ := by
    rw [add_sub_add_left_eq_sub]
    exact abs_sub_le_cubeCoord p q 0
  have h01 : |((n : ℝ) + (p 0 : ℝ)) - ((n : ℝ) + (q 0 : ℝ))| ≤ 1 := by
    rw [add_sub_add_left_eq_sub, abs_le]
    constructor <;> linarith [(p 0).2.1, (p 0).2.2, (q 0).2.1, (q 0).2.2]
  rw [he]
  refine (hC₃ hh _ _ h01 _ _).trans ?_
  have hmax : max ((n : ℝ) + (p 0 : ℝ)) ((n : ℝ) + (q 0 : ℝ)) ≤ (n : ℝ) + 1 :=
    max_le (by linarith [(p 0).2.2]) (by linarith [(q 0).2.2])
  have hx := norm_cellPtF2b_sub_le (Real.exp_pos (-(n : ℝ))).le k (cubeSpaceF2b p)
    (cubeSpaceF2b q)
  have hsp := norm_cubeSpace_sub_le p q
  have hexp : Real.exp (max ((n : ℝ) + (p 0 : ℝ)) ((n : ℝ) + (q 0 : ℝ))) *
      Real.exp (-(n : ℝ)) ≤ 3 := by
    rw [← Real.exp_add]
    calc Real.exp (max ((n : ℝ) + (p 0 : ℝ)) ((n : ℝ) + (q 0 : ℝ)) + -(n : ℝ))
        ≤ Real.exp 1 := Real.exp_le_exp.2 (by linarith)
      _ ≤ 3 := by have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
  have hsd : 0 ≤ √(d : ℝ) := Real.sqrt_nonneg _
  have hE : 0 ≤ Real.exp (max ((n : ℝ) + (p 0 : ℝ)) ((n : ℝ) + (q 0 : ℝ))) := (Real.exp_pos _).le
  have hspace : Real.exp (max ((n : ℝ) + (p 0 : ℝ)) ((n : ℝ) + (q 0 : ℝ))) *
      ‖cellPtF2b (Real.exp (-(n : ℝ))) k (cubeSpaceF2b p) -
        cellPtF2b (Real.exp (-(n : ℝ))) k (cubeSpaceF2b q)‖ ≤ 3 * √d * Δ := by
    calc Real.exp (max ((n : ℝ) + (p 0 : ℝ)) ((n : ℝ) + (q 0 : ℝ))) *
          ‖cellPtF2b (Real.exp (-(n : ℝ))) k (cubeSpaceF2b p) -
            cellPtF2b (Real.exp (-(n : ℝ))) k (cubeSpaceF2b q)‖
        ≤ Real.exp (max ((n : ℝ) + (p 0 : ℝ)) ((n : ℝ) + (q 0 : ℝ))) *
          (√d * (Real.exp (-(n : ℝ)) * Δ)) := by
          refine mul_le_mul_of_nonneg_left (hx.trans ?_) hE
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsp (Real.exp_pos _).le) hsd
      _ = (Real.exp (max ((n : ℝ) + (p 0 : ℝ)) ((n : ℝ) + (q 0 : ℝ))) *
          Real.exp (-(n : ℝ))) * (√d * Δ) := by ring
      _ ≤ 3 * (√d * Δ) := mul_le_mul_of_nonneg_right hexp (by positivity)
      _ = 3 * √d * Δ := by ring
  calc C₃ * (|((n : ℝ) + (p 0 : ℝ)) - ((n : ℝ) + (q 0 : ℝ))| +
        Real.exp (max ((n : ℝ) + (p 0 : ℝ)) ((n : ℝ) + (q 0 : ℝ))) *
          ‖cellPtF2b (Real.exp (-(n : ℝ))) k (cubeSpaceF2b p) -
            cellPtF2b (Real.exp (-(n : ℝ))) k (cubeSpaceF2b q)‖)
      ≤ C₃ * (Δ + 3 * √d * Δ) := mul_le_mul_of_nonneg_left (add_le_add h0 hspace) hC₃0
    _ ≤ (C₃ * (1 + 3 * √d) + 1) * Δ := by nlinarith

/-- **Uniform Gaussian tail of the cell suprema.** -/
theorem exists_cell_sup_tail_F2b (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    ∃ L : ℝ, 0 < L ∧ ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, IsNormalizedLGF h P → ∀ (n : ℕ) (k : Fin d → ℤ) {x : ℝ}, 0 ≤ x →
        P.real {ω | x ≤ ⨆ p, |cellProcF2b κ h n k p ω|} ≤
          2 * Real.exp ((20 * √5 * L * √((((d + 1 : ℕ) : ℝ) + 1) * 1)) ^ 2 / (2 * L ^ 2)) *
            Real.exp (-x ^ 2 / (2 * (2 * L ^ 2))) := by
  obtain ⟨L, hL0, hL⟩ := exists_cell_increment_F2b hd hκ
  refine ⟨L, hL0, fun {Ω} _ {P} _ {h} hh n k x hx => ?_⟩
  have hG : IsGaussianProcess (cellProcF2b κ h n k) P :=
    isGaussianProcess_fieldDiff_F2b hd hκ hh (cellTopF2b n k) (fun _ => cellBaseF2b n k)
  have h0 : ∀ p, ∫ ω, cellProcF2b κ h n k p ω ∂P = 0 := fun p =>
    integral_fieldDiff_F2b hd hκ hh _ _
  have hc : ∀ᵐ ω ∂P, Continuous fun p => cellProcF2b κ h n k p ω := by
    filter_upwards [ae_continuous_fieldF2b hd hκ hh] with ω hω
    exact (hω.comp (continuous_cellTopF2b n k)).sub continuous_const
  have hvar : ∀ p, Var[cellProcF2b κ h n k p; P] ≤ L ^ 2 := by
    intro p
    refine (variance_le_expectation_sq (hG.aemeasurable p).aestronglyMeasurable).trans ?_
    have he : (fun ω => (cellProcF2b κ h n k p ^ 2) ω) =
        fun ω => (cellProcF2b κ h n k p ω - cellProcF2b κ h n k 0 ω) ^ 2 := by
      funext ω
      simp only [Pi.pow_apply, cellProcF2b_zero, sub_zero]
    calc ∫ ω, (cellProcF2b κ h n k p ^ 2) ω ∂P
        = ∫ ω, (cellProcF2b κ h n k p ω - cellProcF2b κ h n k 0 ω) ^ 2 ∂P := by rw [he]
      _ ≤ L ^ 2 * ‖cubeCoordF2b p - cubeCoordF2b 0‖ := hL hh n k p 0
      _ ≤ L ^ 2 * 1 := mul_le_mul_of_nonneg_left (norm_cubeCoordF2b_sub_le_one p 0)
          (sq_nonneg L)
      _ = L ^ 2 := mul_one _
  exact cube_sup_tail_F2b hG h0 hc hL0.le (hL hh n k) hvar hx

end HigherDimLFPPAS.Gauss
