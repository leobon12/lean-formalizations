import HigherDimLQGMetric.ScaleBin.Basic

/-!
# A Gaussian bound for a single scale-bin point

The Chernoff estimate below uses the fixed moment parameters `2` and `-2`, so it also
handles a Gaussian with zero variance without a division by its variance.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric.ScaleBin

universe u

open MeasureTheory ProbabilityTheory
open HigherDimLFPP (Rd)
open scoped ENNReal NNReal

/-- Fixed-parameter two-sided Chernoff bound for a centred Gaussian. -/
theorem gaussian_abs_tail_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : HasGaussianLaw X P)
    (h0 : ∫ ω, X ω ∂P = 0) {V A : ℝ} (hV : Var[X; P] ≤ V) :
    P.real {ω | A ≤ |X ω|} ≤ 2 * Real.exp (-2 * A + 2 * V) := by
  let v : ℝ≥0 := (Var[X; P]).toNNReal
  have hLaw : HasLaw X (gaussianReal 0 v) P :=
    GaussianLQG.hasLaw_of_hasGaussianLaw hX h0
  have hv : (v : ℝ) = Var[X; P] := by
    exact Real.coe_toNNReal _ (variance_nonneg X P)
  have hpos : P.real {ω | A ≤ X ω} ≤ Real.exp (-2 * A + 2 * V) := by
    have h := measure_ge_le_exp_mul_mgf (X := X) (μ := P) (t := (2 : ℝ)) A
      (by norm_num) (GaussianLQG.integrable_exp_mul_of_hasLaw_gaussianReal hLaw 2)
    rw [mgf_gaussianReal hLaw, zero_mul, zero_add, ← Real.exp_add] at h
    exact h.trans (Real.exp_le_exp.mpr (by rw [hv]; nlinarith))
  have hneg : P.real {ω | X ω ≤ -A} ≤ Real.exp (-2 * A + 2 * V) := by
    have h := measure_le_le_exp_mul_mgf (X := X) (μ := P) (t := (-2 : ℝ)) (-A)
      (by norm_num) (GaussianLQG.integrable_exp_mul_of_hasLaw_gaussianReal hLaw (-2))
    rw [mgf_gaussianReal hLaw, zero_mul, zero_add, ← Real.exp_add] at h
    exact h.trans (Real.exp_le_exp.mpr (by rw [hv]; nlinarith))
  have hsub : {ω | A ≤ |X ω|} ⊆ {ω | A ≤ X ω} ∪ {ω | X ω ≤ -A} := by
    intro ω hω
    change A ≤ |X ω| at hω
    rcases le_abs'.1 hω with h | h
    · exact Or.inr (by simpa only [Set.mem_ofPred_eq] using h)
    · exact Or.inl h
  calc
    P.real {ω | A ≤ |X ω|} ≤
        P.real ({ω | A ≤ X ω} ∪ {ω | X ω ≤ -A}) := measureReal_mono hsub
    _ ≤ P.real {ω | A ≤ X ω} + P.real {ω | X ω ≤ -A} := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-2 * A + 2 * V) := by linarith only [hpos, hneg]

/-- A variance constant uniform over LGFs, macroscopic radii, and centres in `B(0,5R)`. -/
theorem exists_point_variance_bound {d : ℕ} (hd : 2 ≤ d) :
    ∃ D : ℝ, 1 ≤ D ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d},
        IsWholeSpaceLGF h P → ∀ {r R : ℝ}, 0 < r → r ≤ R →
        ∀ z : Rd d, ‖z‖ < 5 * R →
          Var[fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) (8 * R) 0; P] ≤
            D * (1 + Real.log (R / r)) := by
  obtain ⟨K, hK⟩ := exists_abs_variance_sphereAvg_sub_sub_log_le hd 1
  refine ⟨|K| + Real.log 8 + 2, ?_, ?_⟩
  · have hlog : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    linarith [abs_nonneg K]
  intro Ω _ P h hh r R hr hrR z hz
  have hR : 0 < R := hr.trans_le hrR
  have h8R : 0 < 8 * R := by positivity
  have hr8R : r ≤ 8 * R := by linarith
  have hzr : ‖z - (0 : Rd d)‖ ≤ 1 * (8 * R) := by
    simpa only [sub_zero, one_mul] using (show ‖z‖ ≤ 8 * R by linarith)
  have hv := hK hh hr hr8R z (0 : Rd d) hzr
  have hlog : 0 ≤ Real.log (R / r) :=
    Real.log_nonneg (by apply (one_le_div hr).2; exact hrR)
  have hlog8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hsplit : Real.log (8 * R / r) = Real.log 8 + Real.log (R / r) := by
    rw [show 8 * R / r = 8 * (R / r) by ring,
      Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (by positivity : R / r ≠ 0)]
  rw [hsplit] at hv
  have hpart : 0 ≤ (|K| + Real.log 8 + 1) * Real.log (R / r) :=
    mul_nonneg (by linarith [abs_nonneg K]) hlog
  have hKabs : K ≤ |K| := le_abs_self K
  have hv' := (abs_le.mp hv).2
  nlinarith only [hv', hlog, hlog8, hpart, hKabs]

/-- Exponential of an integer multiple of a logarithmic scale ratio. -/
theorem exp_neg_nat_log_div (n : ℕ) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    Real.exp (-(n : ℝ) * Real.log (R / r)) = (r / R) ^ n := by
  have hratio : 0 < R / r := div_pos hR hr
  calc
    Real.exp (-(n : ℝ) * Real.log (R / r)) =
        Real.exp ((n : ℝ) * (-Real.log (R / r))) := by simp only [mul_neg, neg_mul]
    _ = (Real.exp (-Real.log (R / r))) ^ n := by rw [Real.exp_nat_mul]
    _ = (r / R) ^ n := by rw [Real.exp_neg, Real.exp_log hratio, inv_div]

/-- Polynomial tail at one lattice point, with a power stronger than its spatial count. -/
theorem point_tail_le {d : ℕ} (hd : 2 ≤ d) {D : ℝ}
    (hvar : ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d},
      IsWholeSpaceLGF h P → ∀ {r R : ℝ}, 0 < r → r ≤ R →
      ∀ z : Rd d, ‖z‖ < 5 * R →
        Var[fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) (8 * R) 0; P] ≤
          D * (1 + Real.log (R / r)))
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P) {r R : ℝ} (hr : 0 < r)
    (hrR : r ≤ R) (z : Rd d) (hz : ‖z‖ < 5 * R) :
    P.real {ω | (D + (d : ℝ) + 2) * (1 + Real.log (R / r)) ≤
      |sphereAvg (h ω) r z - sphereAvg (h ω) (8 * R) 0|} ≤
        2 * (r / R) ^ (2 * (d + 2)) := by
  have hR : 0 < R := hr.trans_le hrR
  have hL : 0 ≤ Real.log (R / r) :=
    Real.log_nonneg ((one_le_div hr).2 hrR)
  have hGauss := hh.hasGaussianLaw_sphereAvg_sub hd hr (by positivity : 0 < 8 * R) z 0
  have hv := hvar hh hr hrR z hz
  have ht := gaussian_abs_tail_le hGauss.1 hGauss.2 hv
    (A := (D + (d : ℝ) + 2) * (1 + Real.log (R / r)))
  calc
    P.real {ω | (D + (d : ℝ) + 2) * (1 + Real.log (R / r)) ≤
      |sphereAvg (h ω) r z - sphereAvg (h ω) (8 * R) 0|} ≤
        2 * Real.exp (-2 * ((D + (d : ℝ) + 2) * (1 + Real.log (R / r))) +
          2 * (D * (1 + Real.log (R / r)))) := ht
    _ ≤ 2 * Real.exp (-(2 * (d + 2) : ℕ) * Real.log (R / r)) := by
      gcongr
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) d]
    _ = 2 * (r / R) ^ (2 * (d + 2)) := by rw [exp_neg_nat_log_div _ hr hR]

end HigherDimLQGMetric.ScaleBin
