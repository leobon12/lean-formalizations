import HigherDimLQGMetric.Sharp.W3Gaussian
import HigherDimLQGMetric.Sharp.W3ShellTail
import HigherDimLQGMetric.Sharp.W3Grid

/-! Summing polynomial shell tails over all dyadic grid points. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set MeasureTheory
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

private theorem w3_grid_power_identity {A ζ p : ℝ} (hA : 0 < A) (n d : ℕ) :
    (2 : ℝ) ^ (d * n) * (A * (2 : ℝ) ^ (ζ * n)) ^ (-p) =
      A ^ (-p) * ((2 : ℝ) ^ ((d : ℝ) - ζ * p)) ^ n := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h2n : 0 ≤ (2 : ℝ) ^ (ζ * n) := (Real.rpow_pos_of_pos h2 _).le
  rw [Real.mul_rpow hA.le h2n]
  have hleft : (2 : ℝ) ^ (d * n) = (2 : ℝ) ^ ((d : ℝ) * n) := by
    rw [Real.rpow_mul h2.le (d : ℝ) (n : ℝ), Real.rpow_natCast,
      Real.rpow_natCast]
    rw [← pow_mul]
  rw [hleft, ← Real.rpow_mul h2.le (ζ * n) (-p)]
  have he : ((d : ℝ) * n) + (ζ * n) * (-p) = ((d : ℝ) - ζ * p) * n := by ring
  calc
    (2 : ℝ) ^ ((d : ℝ) * n) *
        (A ^ (-p) * (2 : ℝ) ^ ((ζ * n) * (-p))) =
      A ^ (-p) * ((2 : ℝ) ^ ((d : ℝ) * n) *
        (2 : ℝ) ^ ((ζ * n) * (-p))) := by ring
    _ = A ^ (-p) * (2 : ℝ) ^ (((d : ℝ) * n) + (ζ * n) * (-p)) := by
      rw [Real.rpow_add h2]
    _ = A ^ (-p) * ((2 : ℝ) ^ ((d : ℝ) - ζ * p)) ^ n := by
      rw [he, Real.rpow_mul h2.le, Real.rpow_natCast]

/-- A finite grid whose cardinality grows like `2^(dn)` can be union-bounded
over every dyadic level whenever the pointwise polynomial order beats the
grid-growth exponent. -/
theorem w3_dyadic_failure_bound {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ → Finset (Rd d)) {CG B A ζ p : ℝ}
    (hCG : 0 ≤ CG) (hB : 0 ≤ B) (hA : 1 ≤ A) (_hζ : 0 < ζ) (_hp : 0 < p)
    (hgap : (d : ℝ) < ζ * p)
    (hcard : ∀ n, ((G n).card : ℝ) ≤ CG * 2 ^ (d * n))
    (F : ℕ → Rd d → Ω → Prop)
    (hpoint : ∀ n, ∀ w ∈ G n,
      P {ω | F n w ω} ≤
        ENNReal.ofReal (B * (A * (2 : ℝ) ^ (ζ * n)) ^ (-p))) :
    P {ω | ∃ n : ℕ, ∃ w ∈ G n, F n w ω} ≤
      ENNReal.ofReal ((CG * B / (1 - (2 : ℝ) ^ ((d : ℝ) - ζ * p))) * A ^ (-p)) := by
  let s : ℝ := (2 : ℝ) ^ ((d : ℝ) - ζ * p)
  have hs0 : 0 ≤ s := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hs1 : s < 1 := by
    exact (Real.rpow_lt_one_iff (by norm_num : (0 : ℝ) ≤ 2)).2
      (Or.inr (Or.inl ⟨by norm_num, by linarith⟩))
  have hAp : 0 ≤ A ^ (-p) := (Real.rpow_pos_of_pos (by linarith) _).le
  let E : ℕ → Set Ω := fun n => {ω | ∃ w ∈ G n, F n w ω}
  have hE : {ω | ∃ n : ℕ, ∃ w ∈ G n, F n w ω} = ⋃ n, E n := by
    ext ω
    simp [E]
  have hlevel (n : ℕ) : P (E n) ≤
      ENNReal.ofReal (CG * B * A ^ (-p) * s ^ n) := by
    have he : E n = ⋃ w ∈ G n, {ω | F n w ω} := by
      ext ω
      simp [E]
    rw [he]
    calc
      P (⋃ w ∈ G n, {ω | F n w ω}) ≤
          ∑ w ∈ G n, P {ω | F n w ω} := measure_biUnion_finset_le _ _
      _ ≤ ∑ _w ∈ G n,
          ENNReal.ofReal (B * (A * (2 : ℝ) ^ (ζ * n)) ^ (-p)) := by
            exact Finset.sum_le_sum fun w hw => hpoint n w hw
      _ = ENNReal.ofReal (((G n).card : ℝ) *
          (B * (A * (2 : ℝ) ^ (ζ * n)) ^ (-p))) := by
            simp only [Finset.sum_const, nsmul_eq_mul]
            rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
            simp
      _ ≤ ENNReal.ofReal (CG * B * A ^ (-p) * s ^ n) := by
        apply ENNReal.ofReal_le_ofReal
        have hpow : 0 ≤ (A * (2 : ℝ) ^ (ζ * n)) ^ (-p) := by positivity
        have hc := mul_le_mul_of_nonneg_right (hcard n) (mul_nonneg hB hpow)
        have hpw := w3_grid_power_identity (by linarith : 0 < A) n d
          (ζ := ζ) (p := p)
        dsimp [s]
        calc
          ((G n).card : ℝ) * (B * (A * (2 : ℝ) ^ (ζ * n)) ^ (-p)) ≤
              (CG * 2 ^ (d * n)) *
                (B * (A * (2 : ℝ) ^ (ζ * n)) ^ (-p)) := hc
          _ = CG * B * (2 ^ (d * n) *
                (A * (2 : ℝ) ^ (ζ * n)) ^ (-p)) := by ring
          _ = CG * B * (A ^ (-p) * ((2 : ℝ) ^ ((d : ℝ) - ζ * p)) ^ n) := by
            rw [hpw]
          _ = CG * B * A ^ (-p) * ((2 : ℝ) ^ ((d : ℝ) - ζ * p)) ^ n := by ring
  have hsum : Summable (fun n : ℕ => CG * B * A ^ (-p) * s ^ n) :=
    (summable_geometric_of_lt_one hs0 hs1).mul_left _
  rw [hE]
  calc
    P (⋃ n, E n) ≤ ∑' n, P (E n) := measure_iUnion_le _
    _ ≤ ∑' n, ENNReal.ofReal (CG * B * A ^ (-p) * s ^ n) :=
      ENNReal.tsum_le_tsum hlevel
    _ = ENNReal.ofReal (∑' n, CG * B * A ^ (-p) * s ^ n) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum).symm
    _ = ENNReal.ofReal ((CG * B / (1 - s)) * A ^ (-p)) := by
      congr 1
      rw [tsum_mul_left, tsum_geometric_of_lt_one hs0 hs1]
      ring

end HigherDimLQGMetric
