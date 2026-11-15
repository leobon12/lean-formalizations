/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.sleLambda
import QuantumZipper.Common.Basic

/-!
# Proposition GB6: the conditional counterflow word on the exposed flow sides

Packet PROVE-JORDANCPL. Supplement §8.6, Proposition GB6 (`source/spec/p481-528.md` L929–L943, pp. 518–519), first
paragraph of the proof:

> "Put `Λ = π/√k` and `A = k/2 − 2`, so that `λ/Λ = k/4` and `πχ/Λ = A`. An exposed own flow piece of angle `θ` has
> `h`-heights `−λ − θχ` and `λ − θχ` on its two sides. After the specified inversion and centering, the terminal
> counterflow side partial sums on those pieces are respectively `S_L = k/4 + (1 − θ/π)A − 1`,
> `S_R = k/4 + (1 + θ/π)A − 1`. Both are at least `c = k/2 − 2` for the stipulated angle range."

Here `κ ∈ (0, 4)` is the flow parameter, `k = 16/κ`, `λ = sleLambda κ`, `χ = chiC κ`, `Λ = sleLambda k`.

**The heights after inversion and centering** (`rightValue_eq`, `leftValue_eq`). The counterflow frame is
`F = −h − πχ`, read in the inversion `I(z) = −1/z` with coefficient `χ(k) = −χ` (`chiC_sixteen_div`) and the
compatible inverse lift `Im(2πi − 2 Log w) = 2π − 2 arg w`, which is `2π` on the positive ray and `0` on the negative
ray. The coordinate rule (1.4) adds `−χ(k) · (2π − 2 arg w)`, i.e. `2πχ` on the positive ray and `0` on the negative
ray. So the left flow flank (`h = −λ − θχ`) becomes the positive (right) counterflow ray with value
`λ + θχ − πχ + 2πχ = Λ(1 + S_R)`, and the right flow flank (`h = λ − θχ`) becomes the negative (left) counterflow ray
with value `−λ + θχ − πχ = −Λ(1 + S_L)` (the frozen `forceBoundaryData` convention: `Λ(1 + S)` on the right,
`−Λ(1 + S)` on the left).

## Main results

* `lambda_div_Lambda`, `pi_chi_div_Lambda`, `chiC_sixteen_div` (the parameter identities);
* `rightValue_eq`, `leftValue_eq` (the heights after inversion and centering);
* **`protLevel_le_sumR`, `protLevel_le_sumL`**: `c ≤ S_R` for `θ ≥ −π/2` and `c ≤ S_L` for `θ ≤ π/2`, with the exact
  differences `S_R − c = (1/2 + θ/π)A`, `S_L − c = (1/2 − θ/π)A`; and `neg_two_lt_protLevel` (`c > −2`). Hence the
  exposed flow-side groups of the conditional counterflow word are admissible and GB5-protected.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Real

namespace InteractingSLE

namespace Supp8

namespace GB6

/-- `Λ = π/√k`, `k = 16/κ`. -/
def bigLambda (κ : ℝ) : ℝ := sleLambda (16 / κ)

/-- `A = k/2 − 2`, `k = 16/κ`. -/
def bigA (κ : ℝ) : ℝ := 16 / κ / 2 - 2

/-- `c = k/2 − 2` (the GB5 protection level; equal to `A`). -/
def protLevel (κ : ℝ) : ℝ := 16 / κ / 2 - 2

/-- The terminal right counterflow side partial sum on an exposed flow piece of angle `θ`. -/
def sumR (κ θ : ℝ) : ℝ := 16 / κ / 4 + (1 + θ / π) * bigA κ - 1

/-- The terminal left counterflow side partial sum on an exposed flow piece of angle `θ`. -/
def sumL (κ θ : ℝ) : ℝ := 16 / κ / 4 + (1 - θ / π) * bigA κ - 1

variable {κ : ℝ}

theorem sqrt_sixteen_div (hκ : 0 < κ) : Real.sqrt (16 / κ) = 4 / Real.sqrt κ := by
  rw [Real.sqrt_div' _ hκ.le, show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `χ(16/κ) = −χ(κ)`. -/
theorem chiC_sixteen_div (hκ : 0 < κ) : QuantumZipper.chiC (16 / κ) = -QuantumZipper.chiC κ := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  unfold QuantumZipper.chiC
  rw [sqrt_sixteen_div hκ]
  field_simp
  ring

theorem bigLambda_eq (hκ : 0 < κ) : bigLambda κ = π * Real.sqrt κ / 4 := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  unfold bigLambda sleLambda
  rw [sqrt_sixteen_div hκ]
  field_simp

theorem bigLambda_pos (hκ : 0 < κ) : 0 < bigLambda κ := by
  rw [bigLambda_eq hκ]
  have := Real.sqrt_pos.2 hκ
  positivity

/-- `λ/Λ = k/4`. -/
theorem lambda_div_Lambda (hκ : 0 < κ) : sleLambda κ / bigLambda κ = 16 / κ / 4 := by
  rw [bigLambda_eq hκ]
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ κ = s ^ 2 := ⟨√κ, Real.sqrt_pos.2 hκ, (Real.sq_sqrt hκ.le).symm⟩
  unfold sleLambda
  rw [Real.sqrt_sq hs.le]
  field_simp
  ring

/-- `πχ/Λ = A`. -/
theorem pi_chi_div_Lambda (hκ : 0 < κ) : π * QuantumZipper.chiC κ / bigLambda κ = bigA κ := by
  rw [bigLambda_eq hκ]
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ κ = s ^ 2 := ⟨√κ, Real.sqrt_pos.2 hκ, (Real.sq_sqrt hκ.le).symm⟩
  unfold QuantumZipper.chiC bigA
  rw [Real.sqrt_sq hs.le]
  field_simp
  ring

/-- `A = c`. -/
theorem bigA_eq_protLevel (κ : ℝ) : bigA κ = protLevel κ := rfl

/-- **The positive (right) counterflow ray**: the left flow flank `h = −λ − θχ`, in the frame `F = −h − πχ`, plus
the inverse-lift term `−χ(k) · 2π`, has the value `Λ(1 + S_R)`. -/
theorem rightValue_eq (hκ : 0 < κ) (θ : ℝ) :
    -(-sleLambda κ - θ * QuantumZipper.chiC κ) - π * QuantumZipper.chiC κ -
        QuantumZipper.chiC (16 / κ) * (2 * π) = bigLambda κ * (1 + sumR κ θ) := by
  have hΛ := (bigLambda_pos hκ).ne'
  have h1 := lambda_div_Lambda hκ
  have h2 := pi_chi_div_Lambda hκ
  rw [chiC_sixteen_div hκ]
  unfold sumR
  rw [← h1, ← h2]
  field_simp
  ring

/-- **The negative (left) counterflow ray**: the right flow flank `h = λ − θχ`, in the frame `F = −h − πχ` (inverse
lift `0` there), has the value `−Λ(1 + S_L)`. -/
theorem leftValue_eq (hκ : 0 < κ) (θ : ℝ) :
    -(sleLambda κ - θ * QuantumZipper.chiC κ) - π * QuantumZipper.chiC κ =
      -(bigLambda κ * (1 + sumL κ θ)) := by
  have hΛ := (bigLambda_pos hκ).ne'
  have h1 := lambda_div_Lambda hκ
  have h2 := pi_chi_div_Lambda hκ
  unfold sumL
  rw [← h1, ← h2]
  field_simp
  ring

theorem bigA_pos (hκ : 0 < κ) (hκ4 : κ < 4) : 0 < bigA κ := by
  unfold bigA
  have : 4 < 16 / κ := by rw [lt_div_iff₀ hκ]; linarith
  linarith

/-- `S_R − c = (1/2 + θ/π) A`. -/
theorem sumR_sub_protLevel (κ θ : ℝ) : sumR κ θ - protLevel κ = (1 / 2 + θ / π) * bigA κ := by
  unfold sumR protLevel bigA
  ring

/-- `S_L − c = (1/2 − θ/π) A`. -/
theorem sumL_sub_protLevel (κ θ : ℝ) : sumL κ θ - protLevel κ = (1 / 2 - θ / π) * bigA κ := by
  unfold sumL protLevel bigA
  ring

/-- **`S_R ≥ c` for `θ ≥ −π/2`.** -/
theorem protLevel_le_sumR (hκ : 0 < κ) (hκ4 : κ < 4) {θ : ℝ} (hθ : -(π / 2) ≤ θ) :
    protLevel κ ≤ sumR κ θ := by
  have hA := bigA_pos hκ hκ4
  have h : 0 ≤ 1 / 2 + θ / π := by
    have : -(1 / 2 : ℝ) ≤ θ / π := by
      rw [le_div_iff₀ pi_pos]
      linarith
    linarith
  have := sumR_sub_protLevel κ θ
  nlinarith

/-- **`S_L ≥ c` for `θ ≤ π/2`.** -/
theorem protLevel_le_sumL (hκ : 0 < κ) (hκ4 : κ < 4) {θ : ℝ} (hθ : θ ≤ π / 2) :
    protLevel κ ≤ sumL κ θ := by
  have hA := bigA_pos hκ hκ4
  have h : 0 ≤ 1 / 2 - θ / π := by
    have : θ / π ≤ 1 / 2 := by
      rw [div_le_iff₀ pi_pos]
      linarith
    linarith
  have := sumL_sub_protLevel κ θ
  nlinarith

/-- `c > −2` (indeed `c > 0`): the protected groups are admissible. -/
theorem neg_two_lt_protLevel (hκ : 0 < κ) (hκ4 : κ < 4) : -2 < protLevel κ := by
  have := bigA_pos hκ hκ4
  rw [← bigA_eq_protLevel]
  linarith

end GB6

end Supp8

end InteractingSLE
