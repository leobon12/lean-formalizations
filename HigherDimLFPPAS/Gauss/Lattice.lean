import HigherDimLFPP.Frozen.Rd
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Pi
import Mathlib.Topology.UnitInterval
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Lattice covers of balls by cubes (packet F2b)

For a mesh `ℓ > 0`, every point of the closed ball `B̄_R ⊂ ℝ^d` lies in a cube `ℓ (k + [0,1]^d)`
with `k` in the integer box `{‖k‖_∞ ≤ ⌈R/ℓ⌉}` of cardinality `(2⌈R/ℓ⌉ + 1)^d`
(`exists_cell_F2b`, `card_boxF2b`). These are the cube decompositions of the planning audit MA3,
Details P5 and P6.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLFPPAS.Gauss

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The vector of `ℝ^d` (Euclidean norm) with coordinates `f`. -/
def vecF2b (f : Fin d → ℝ) : Rd d := WithLp.toLp 2 f

@[simp] lemma vecF2b_apply (f : Fin d → ℝ) (i : Fin d) : vecF2b f i = f i := rfl

lemma vecF2b_sub (f g : Fin d → ℝ) : vecF2b f - vecF2b g = vecF2b (f - g) := rfl

lemma continuous_vecF2b : Continuous (vecF2b (d := d)) := PiLp.continuous_toLp 2 _

/-- The Euclidean norm is at most `√d` times a bound on the coordinates. -/
lemma norm_vecF2b_le (f : Fin d → ℝ) {M : ℝ} (hM : 0 ≤ M) (hf : ∀ i, |f i| ≤ M) :
    ‖vecF2b f‖ ≤ √d * M := by
  rw [EuclideanSpace.norm_eq]
  calc √(∑ i, ‖vecF2b f i‖ ^ 2) ≤ √(∑ _i : Fin d, M ^ 2) := by
        refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
        rw [vecF2b_apply, Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hf i) 2
    _ = √d * M := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hM]

/-- The box of integer vectors of sup norm at most `N`. -/
def boxF2b (d N : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N

lemma card_boxF2b (d N : ℕ) : (boxF2b d N).card = (2 * N + 1) ^ d := by
  simp only [boxF2b, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  congr 1
  omega

lemma mem_boxF2b {N : ℕ} {k : Fin d → ℤ} (hk : k ∈ boxF2b d N) (i : Fin d) :
    -(N : ℤ) ≤ k i ∧ k i ≤ N := by
  simp only [boxF2b, Fintype.mem_piFinset, Finset.mem_Icc] at hk
  exact hk i

/-- The point `ℓ (k + v)`. -/
def cellPtF2b (ℓ : ℝ) (k : Fin d → ℤ) (v : Fin d → ℝ) : Rd d :=
  vecF2b fun i => ℓ * ((k i : ℝ) + v i)

lemma cellPtF2b_sub (ℓ : ℝ) (k : Fin d → ℤ) (v w : Fin d → ℝ) :
    cellPtF2b ℓ k v - cellPtF2b ℓ k w = vecF2b fun i => ℓ * (v i - w i) := by
  rw [cellPtF2b, cellPtF2b, vecF2b_sub]
  congr 1
  funext i
  simp only [Pi.sub_apply]
  ring

lemma continuous_cellPtF2b (ℓ : ℝ) (k : Fin d → ℤ) : Continuous (cellPtF2b ℓ k) :=
  continuous_vecF2b.comp (continuous_pi fun i =>
    continuous_const.mul (continuous_const.add (continuous_apply i)))

/-- `‖ℓ (k + v) - ℓ (k + w)‖ ≤ √d ℓ ‖v - w‖_∞`. -/
lemma norm_cellPtF2b_sub_le {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (k : Fin d → ℤ) (v w : Fin d → ℝ) :
    ‖cellPtF2b ℓ k v - cellPtF2b ℓ k w‖ ≤ √d * (ℓ * ‖v - w‖) := by
  rw [cellPtF2b_sub]
  refine norm_vecF2b_le _ (by positivity) fun i => ?_
  rw [abs_mul, abs_of_nonneg hℓ]
  refine mul_le_mul_of_nonneg_left ?_ hℓ
  have h := norm_le_pi_norm (v - w) i
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using h

/-- Bound on the lattice points of the box. -/
lemma norm_cellPtF2b_zero_le {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R) {k : Fin d → ℤ}
    (hk : k ∈ boxF2b d ⌈R / ℓ⌉₊) : ‖cellPtF2b ℓ k 0‖ ≤ √d * (R + ℓ) := by
  refine norm_vecF2b_le _ (by positivity) fun i => ?_
  obtain ⟨h1, h2⟩ := mem_boxF2b hk i
  have hc : (⌈R / ℓ⌉₊ : ℝ) ≤ R / ℓ + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hki : |(k i : ℝ)| ≤ R / ℓ + 1 := by
    rw [abs_le]
    constructor
    · have : (-(⌈R / ℓ⌉₊ : ℤ) : ℝ) ≤ (k i : ℝ) := by exact_mod_cast h1
      push_cast at this
      linarith
    · have : (k i : ℝ) ≤ ((⌈R / ℓ⌉₊ : ℤ) : ℝ) := by exact_mod_cast h2
      push_cast at this
      linarith
  simp only [Pi.zero_apply, add_zero, abs_mul, abs_of_pos hℓ]
  calc ℓ * |(k i : ℝ)| ≤ ℓ * (R / ℓ + 1) := mul_le_mul_of_nonneg_left hki hℓ.le
    _ = R + ℓ := by field_simp

/-- **The cube cover.** Every `x` with `‖x‖ ≤ R` is `ℓ (k + v)` with `k` in the box
`{‖k‖_∞ ≤ ⌈R/ℓ⌉}` and `v ∈ [0,1]^d`. -/
theorem exists_cell_F2b {R ℓ : ℝ} (hℓ : 0 < ℓ) {x : Rd d} (hx : ‖x‖ ≤ R) :
    ∃ k ∈ boxF2b d ⌈R / ℓ⌉₊, ∃ v : Fin d → unitInterval,
      x = cellPtF2b ℓ k fun i => (v i : ℝ) := by
  refine ⟨fun i => ⌊x i / ℓ⌋, ?_, fun i => ⟨Int.fract (x i / ℓ), Int.fract_nonneg _,
    (Int.fract_lt_one _).le⟩, ?_⟩
  · simp only [boxF2b, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have hxi : |x i| ≤ R := (PiLp.norm_apply_le x i).trans hx
    have hy : |x i / ℓ| ≤ R / ℓ := by
      rw [abs_div, abs_of_pos hℓ]
      exact div_le_div_of_nonneg_right hxi hℓ.le
    have hc : R / ℓ ≤ (⌈R / ℓ⌉₊ : ℝ) := Nat.le_ceil _
    obtain ⟨hy1, hy2⟩ := abs_le.mp hy
    constructor
    · rw [Int.le_floor]
      push_cast
      linarith
    · have h := Int.floor_le (x i / ℓ)
      have : (⌊x i / ℓ⌋ : ℝ) ≤ ((⌈R / ℓ⌉₊ : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
  · ext i
    simp only [cellPtF2b, vecF2b_apply, Int.floor_add_fract]
    field_simp

/-- `(2⌈y⌉ + 1)^d ≤ (2y + 3)^d` for `y ≥ 0`. -/
lemma card_boxF2b_le {y : ℝ} (hy : 0 ≤ y) :
    ((boxF2b d ⌈y⌉₊).card : ℝ) ≤ (2 * y + 3) ^ d := by
  rw [card_boxF2b]
  push_cast
  have hc : (⌈y⌉₊ : ℝ) ≤ y + 1 := (Nat.ceil_lt_add_one hy).le
  exact pow_le_pow_left₀ (by positivity) (by linarith) d

end HigherDimLFPPAS.Gauss
