import HigherDimLQGMetric.LGF.FTC
import HigherDimLQGMetric.LGF.Density
import HigherDimLQGMetric.Field.Bump
import HigherDimLFPP.Field.WhiteNoise
import HigherDimLFPP.Field.Version
import LQGMetric.Field.WhiteNoiseC1Proc

/-!
# The antiderivative field of the white-noise LGF and its continuous version
(packet F2, target 1, part 4)

For `q ∈ ℝ^d` (coordinates `Fin d → ℝ`) let `boxDens q = 1_{[0,q]} − (∏ᵢ qᵢ) θ` with the mean-one
bump `θ = ψ_{0,0}` (F1's `bumpTest 0 0`). It is bounded, boundedly supported, and has mean zero, so
`G(q) = W(gramVec (boxDens q))` is the pairing of the LGF (normalized by `⟨h, θ⟩ = 0`) with
`1_{[0,q]}`: the antiderivative field. This file proves

* `isBddSupp_boxDens`, `integral_boxDens` (mean zero);
* `integral_boxIndF_rd`: `∫ 1_{[0,q]} = ∏ᵢ qᵢ` on `ℝ^d`;
* `norm_gramVec_boxDens_sub_sq_le`: on every box `|qᵢ|, |q'ᵢ| ≤ R`,
  `‖gramVec (boxDens q) − gramVec (boxDens q')‖² ≤ C_R ‖q − q'‖` (sup norm), from the Gram identity,
  the quadratic bound `abs_logCovF_self_le` and the `L¹` bound `integral_abs_boxIndF_sub_le`;
* `exists_continuous_boxField`: a version of `x ↦ W(gramVec (boxDens x))` that is continuous for
  every `ω` (Kolmogorov–Čentsov with moments of order `2(d+1)`, as in HigherDimLFPP's
  `exists_isBandVersion`; LQGMetric `exists_meas_continuous_modification_N`).

Port of LQGMetric's `Field/ExistRect.lean`, `ExistField.lean`, `ExistKolm.lean` (planar rectangles,
heat-kernel vectors) to `ℝ^d` with HigherDimLFPP's white-noise vectors (ruling M10).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped RealInnerProductSpace

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ## Box integrals on `ℝ^d` -/

theorem integral_comp_ofLp (F : (Fin d → ℝ) → ℝ) :
    ∫ u : Rd d, F u.ofLp = ∫ q : Fin d → ℝ, F q := by
  have hmp := PiLp.volume_preserving_toLp (Fin d)
  rw [← hmp.integral_comp (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding]

theorem integral_boxIndF_rd (q : Fin d → ℝ) : ∫ u : Rd d, boxIndF q u.ofLp = ∏ i, q i := by
  rw [integral_comp_ofLp (boxIndF q), integral_boxIndF]

theorem integral_abs_boxIndF_rd_sub_le {q q' : Fin d → ℝ} {R : ℝ} (hq : ∀ i, |q i| ≤ R)
    (hq' : ∀ i, |q' i| ≤ R) :
    ∫ u : Rd d, |boxIndF q u.ofLp - boxIndF q' u.ofLp| ≤ max (2 * R) 1 ^ d * ∑ i, |q i - q' i| := by
  rw [integral_comp_ofLp (fun v => |boxIndF q v - boxIndF q' v|)]
  exact integral_abs_boxIndF_sub_le hq hq'

/-- Points of a sup-norm box `|uᵢ| ≤ R` have Euclidean norm at most `d R + 1`. -/
theorem norm_le_of_abs_le {u : Rd d} {R : ℝ} (hR : 0 ≤ R) (hu : ∀ i, |u i| ≤ R) :
    ‖u‖ ≤ d * R + 1 := by
  have h1 : ‖u.ofLp‖ ≤ R := (pi_norm_le_iff_of_nonneg hR).2 fun i => by
    rw [Real.norm_eq_abs]; exact hu i
  have h2 := HigherDimLFPP.norm_toLp_sq_le_dim_mul u.ofLp
  rw [WithLp.toLp_ofLp] at h2
  have hd : (0 : ℝ) ≤ (d : ℝ) * ((d : ℝ) - 1) := by
    rcases Nat.eq_zero_or_pos d with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ d := by exact_mod_cast h
      nlinarith
  have h3 : ‖u‖ ^ 2 ≤ ((d : ℝ) * R + 1) ^ 2 := by
    have h4 : ‖u.ofLp‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h5 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith [mul_nonneg hd (sq_nonneg R)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3

theorem isBddSupp_boxIndF {q : Fin d → ℝ} {R : ℝ} (hR : 0 ≤ R) (hq : ∀ i, |q i| ≤ R) :
    IsBddSupp (fun u : Rd d => boxIndF q u.ofLp) 1 (d * R + 1) := by
  refine ⟨(measurable_boxIndF q).comp (PiLp.continuous_ofLp 2 _).measurable,
    fun u => abs_boxIndF_le_one q u.ofLp, fun u hu => ?_⟩
  by_contra hne
  have hall : ∀ i, |u i| ≤ R := fun i => by
    by_contra hi
    exact hne (boxIndF_eq_zero ((hq i).trans_lt (not_le.1 hi)))
  exact absurd (norm_le_of_abs_le hR hall) (not_le.2 hu)

/-! ## The mean-one bump and the box densities -/

/-- The mean-one bump `θ = ψ_{0,0}` (F1's `bumpTest 0 0`). -/
abbrev theta (d : ℕ) : TestRd d := bumpTest 0 0

theorem exists_theta_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Rd d, |theta d u| ≤ C := by
  obtain ⟨C, hC⟩ := (theta d).continuous.bounded_above_of_compact_support
    (theta d).hasCompactSupport
  exact ⟨max C 0, le_max_right _ _, fun u => (by simpa only [Real.norm_eq_abs] using hC u :
    |theta d u| ≤ C).trans (le_max_left _ _)⟩

theorem theta_eq_zero {u : Rd d} (hu : 1 ≤ ‖u‖) : theta d u = 0 :=
  bumpTest_eq_zero (by simpa using hu)

theorem integral_theta : ∫ u, theta d u = 1 := integral_bumpTest 0 0

/-- The density `1_{[0,q]} − (∏ᵢ qᵢ) θ` of the antiderivative field (mean zero). -/
def boxDens (q : Fin d → ℝ) (u : Rd d) : ℝ := boxIndF q u.ofLp - (∏ i, q i) * theta d u

theorem abs_prod_le_pow {q : Fin d → ℝ} {R : ℝ} (hq : ∀ i, |q i| ≤ R) :
    |∏ i, q i| ≤ max R 1 ^ d := by
  rw [Finset.abs_prod]
  calc ∏ i, |q i| ≤ ∏ _i : Fin d, max R 1 :=
        Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => (hq i).trans (le_max_left _ _)
    _ = max R 1 ^ d := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Uniform bounds for the box densities over a box of corners. -/
theorem exists_isBddSupp_boxDens {R : ℝ} (hR : 0 ≤ R) :
    ∃ M : ℝ, ∀ q : Fin d → ℝ, (∀ i, |q i| ≤ R) → IsBddSupp (boxDens q) M (d * R + 1) := by
  obtain ⟨C, hC0, hC⟩ := exists_theta_bound (d := d)
  refine ⟨1 + max R 1 ^ d * C, fun q hq => ?_⟩
  have h1 := isBddSupp_boxIndF hR hq
  refine ⟨h1.measurable.sub (measurable_const.mul (theta d).continuous.measurable),
    fun u => ?_, fun u hu => ?_⟩
  · calc |boxDens q u| ≤ |boxIndF q u.ofLp| + |∏ i, q i| * |theta d u| := by
          rw [boxDens, ← abs_mul]; exact abs_sub _ _
      _ ≤ 1 + max R 1 ^ d * C := add_le_add (abs_boxIndF_le_one _ _)
          (mul_le_mul (abs_prod_le_pow hq) (hC u) (abs_nonneg _) (pow_nonneg
            (zero_le_one.trans (le_max_right _ _)) _))
  · have hu1 : 1 ≤ ‖u‖ := le_trans (by
      have : (0 : ℝ) ≤ d * R := mul_nonneg (Nat.cast_nonneg d) hR
      linarith) hu.le
    rw [boxDens, h1.eq_zero u hu, theta_eq_zero hu1, mul_zero, sub_zero]

theorem integral_boxDens (q : Fin d → ℝ) : ∫ u, boxDens q u = 0 := by
  have hR : 0 ≤ ‖q‖ := norm_nonneg q
  have hq : ∀ i, |q i| ≤ ‖q‖ := fun i => by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm q i
  have h1 := (isBddSupp_boxIndF hR hq).integrable
  have h2 : Integrable fun u : Rd d => (∏ i, q i) * theta d u := (integrable_testOn _).const_mul _
  unfold boxDens
  rw [integral_sub h1 h2, integral_boxIndF_rd, integral_const_mul, integral_theta, mul_one,
    sub_self]

/-! ## The increment bound -/

theorem abs_boxDens_sub_le (q q' : Fin d → ℝ) (u : Rd d) :
    |boxDens q u - boxDens q' u| ≤
      |boxIndF q u.ofLp - boxIndF q' u.ofLp| + |∏ i, q i - ∏ i, q' i| * theta d u := by
  have e : boxDens q u - boxDens q' u =
      (boxIndF q u.ofLp - boxIndF q' u.ofLp) - (∏ i, q i - ∏ i, q' i) * theta d u := by
    simp only [boxDens]; ring
  rw [e]
  calc |(boxIndF q u.ofLp - boxIndF q' u.ofLp) - (∏ i, q i - ∏ i, q' i) * theta d u|
      ≤ |boxIndF q u.ofLp - boxIndF q' u.ofLp| + |(∏ i, q i - ∏ i, q' i) * theta d u| :=
        abs_sub _ _
    _ = _ := by rw [abs_mul, abs_of_nonneg (bumpTest_nonneg 0 0 u)]

theorem integral_abs_boxDens_sub_le {q q' : Fin d → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hq : ∀ i, |q i| ≤ R) (hq' : ∀ i, |q' i| ≤ R) :
    ∫ u, |boxDens q u - boxDens q' u| ≤
      (max (2 * R) 1 ^ d + max R 1 ^ d) * ∑ i, |q i - q' i| := by
  have hb := isBddSupp_boxIndF hR hq
  have hb' := isBddSupp_boxIndF hR hq'
  have hθi : Integrable fun u : Rd d => theta d u := integrable_testOn _
  have hP : |∏ i, q i - ∏ i, q' i| ≤ max R 1 ^ d * ∑ i, |q i - q' i| := by
    classical
    have := abs_prod_sub_prod_le_pow Finset.univ q q' (C := R) (fun i _ => hq i) (fun i _ => hq' i)
    rwa [Finset.card_univ, Fintype.card_fin] at this
  have hint1 : Integrable fun u : Rd d => |boxIndF q u.ofLp - boxIndF q' u.ofLp| :=
    (hb.integrable.sub hb'.integrable).abs
  have hint2 : Integrable fun u : Rd d =>
      |boxIndF q u.ofLp - boxIndF q' u.ofLp| + |∏ i, q i - ∏ i, q' i| * theta d u :=
    hint1.add (hθi.const_mul _)
  have h1 : ∫ u, |boxDens q u - boxDens q' u| ≤
      ∫ u : Rd d, (|boxIndF q u.ofLp - boxIndF q' u.ofLp| + |∏ i, q i - ∏ i, q' i| * theta d u) :=
    integral_mono_of_nonneg (ae_of_all _ fun u => abs_nonneg _) hint2
      (ae_of_all _ fun u => abs_boxDens_sub_le q q' u)
  have h2 : ∫ u : Rd d, (|boxIndF q u.ofLp - boxIndF q' u.ofLp| +
        |∏ i, q i - ∏ i, q' i| * theta d u) =
      (∫ u : Rd d, |boxIndF q u.ofLp - boxIndF q' u.ofLp|) + |∏ i, q i - ∏ i, q' i| := by
    rw [integral_add hint1 (hθi.const_mul _), integral_const_mul, integral_theta, mul_one]
  have h3 := integral_abs_boxIndF_rd_sub_le hq hq'
  calc ∫ u, |boxDens q u - boxDens q' u|
      ≤ (∫ u : Rd d, |boxIndF q u.ofLp - boxIndF q' u.ofLp|) + |∏ i, q i - ∏ i, q' i| :=
        h1.trans h2.le
    _ ≤ max (2 * R) 1 ^ d * ∑ i, |q i - q' i| + max R 1 ^ d * ∑ i, |q i - q' i| :=
        add_le_add h3 hP
    _ = (max (2 * R) 1 ^ d + max R 1 ^ d) * ∑ i, |q i - q' i| := by ring

theorem sum_abs_sub_le_card_mul_norm (q q' : Fin d → ℝ) :
    ∑ i, |q i - q' i| ≤ d * ‖q - q'‖ := by
  calc ∑ i, |q i - q' i| ≤ ∑ _i : Fin d, ‖q - q'‖ :=
        Finset.sum_le_sum fun i _ => by
          rw [← Real.norm_eq_abs, ← Pi.sub_apply]; exact norm_le_pi_norm (q - q') i
    _ = d * ‖q - q'‖ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Increment bound** (`d ≥ 1`): on every box of corners, the white-noise vectors of the box
densities are `½`-Hölder in `L²`: `‖gramVec (boxDens q) − gramVec (boxDens q')‖² ≤ C ‖q − q'‖`. -/
theorem exists_norm_gramVec_boxDens_sub_sq_le [NeZero d] {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q q' : Fin d → ℝ, (∀ i, |q i| ≤ R) → (∀ i, |q' i| ≤ R) →
      ‖gramVec (boxDens q) - gramVec (boxDens q')‖ ^ 2 ≤ C * ‖q - q'‖ := by
  obtain ⟨M, hM⟩ := exists_isBddSupp_boxDens (d := d) hR
  set A : ℝ := max (2 * R) 1 ^ d + max R 1 ^ d with hA
  have hA0 : 0 ≤ A := by positivity
  set N₀ : ℝ := A * (d * (2 * R)) with hN₀
  set D : ℝ := d * R + 1 with hD
  set K : ℝ := (M + M) * volBall d + N₀ * (1 + max 0 (Real.log (2 * D))) with hK
  have hL0 : 0 ≤ max 0 (Real.log (2 * D)) := le_max_left _ _
  refine ⟨A * d * K, ?_, fun q q' hq hq' => ?_⟩
  · have hM0 : 0 ≤ M := (hM 0 fun i => by simpa using hR).nonneg
    have := volBall_nonneg (d := d)
    positivity
  have hf := (hM q hq).sub (hM q' hq')
  have hS : ∑ i, |q i - q' i| ≤ d * (2 * R) := by
    calc ∑ i, |q i - q' i| ≤ ∑ _i : Fin d, 2 * R := Finset.sum_le_sum fun i _ => by
          calc |q i - q' i| ≤ |q i| + |q' i| := abs_sub _ _
            _ ≤ 2 * R := by linarith [hq i, hq' i]
      _ = d * (2 * R) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hN : ∫ u, |(boxDens q - boxDens q') u| ≤ A * ∑ i, |q i - q' i| :=
    integral_abs_boxDens_sub_le hR hq hq'
  have hN' : ∫ u, |(boxDens q - boxDens q') u| ≤ N₀ :=
    hN.trans (mul_le_mul_of_nonneg_left hS hA0)
  have hN0 : 0 ≤ ∫ u, |(boxDens q - boxDens q') u| := integral_nonneg fun u => abs_nonneg _
  rw [norm_gramVec_sub_sq (hM q hq) (integral_boxDens q) (hM q' hq') (integral_boxDens q')]
  have hb := abs_logCovF_self_le hf
  have hM0 : 0 ≤ M + M := hf.nonneg
  calc logCovF (boxDens q - boxDens q') (boxDens q - boxDens q')
      ≤ |logCovF (boxDens q - boxDens q') (boxDens q - boxDens q')| := le_abs_self _
    _ ≤ (∫ u, |(boxDens q - boxDens q') u|) *
          ((M + M) * volBall d + (∫ u, |(boxDens q - boxDens q') u|) *
            (1 + max 0 (Real.log (2 * D)))) := hb
    _ ≤ (A * ∑ i, |q i - q' i|) * K := by
        refine mul_le_mul hN ?_ (by have := volBall_nonneg (d := d); positivity)
          (mul_nonneg hA0 (Finset.sum_nonneg fun i _ => abs_nonneg _))
        rw [hK]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hN'
          (by positivity : (0 : ℝ) ≤ 1 + max 0 (Real.log (2 * D))))
    _ ≤ (A * (d * ‖q - q'‖)) * K := by
        have hK0 : 0 ≤ K := by have := volBall_nonneg (d := d); positivity
        gcongr
        exact sum_abs_sub_le_card_mul_norm q q'
    _ = A * d * K * ‖q - q'‖ := by ring

/-! ## The continuous antiderivative field (Kolmogorov–Čentsov) -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : HigherDimLFPP.WN d → Ω → ℝ}

/-- **Continuous version of the antiderivative field** (`d ≥ 1`): `x ↦ W(gramVec (boxDens x))` has a
version that is continuous for every `ω` and measurable at every point. -/
theorem exists_continuous_boxField [NeZero d] (hW : HigherDimLFPP.IsWhiteNoise P W) :
    ∃ Y : Rd d → Ω → ℝ, (∀ ω, Continuous fun x => Y x ω) ∧ (∀ x, Measurable (Y x)) ∧
      ∀ x, (fun ω => Y x ω) =ᵐ[P] W (gramVec (boxDens x.ofLp)) := by
  set Z : (Fin d → ℝ) → Ω → ℝ := fun q => W (gramVec (boxDens q)) with hZ
  have hZm : ∀ q, Measurable (Z q) := fun q => hW.measurable _
  set M : ℝ := QuantumZipper.gaussianAbsMoment (2 * (d + 1)) with hMdef
  have hM0 : 0 ≤ M := QuantumZipper.gaussianAbsMoment_nonneg _
  have hmom : ∀ R : ℕ, ∃ K, 0 ≤ K ∧
      QuantumZipper.KolmG.MomentBoundG Z P (2 * (d + 1)) ((d + 1 : ℕ) : ℝ) K R := by
    intro R
    obtain ⟨C, hC0, hC⟩ := exists_norm_gramVec_boxDens_sub_sq_le (d := d) (Nat.cast_nonneg R)
    refine ⟨C ^ (d + 1) * M, by positivity, fun q hq q' hq' => ?_⟩
    have hlaw := hW.hasLaw_sub (gramVec (boxDens q)) (gramVec (boxDens q'))
    have hE := QuantumZipper.KolmG.lintegral_pow_two_mul_of_map_eq (P := P)
      ((hW.measurable _).sub (hW.measurable _)) (d + 1) hlaw.map_eq
    simp only [Pi.sub_apply] at hE
    simp only [hZ]
    rw [hE]
    refine ENNReal.ofReal_le_ofReal ?_
    set v : ℝ := ‖gramVec (boxDens q) - gramVec (boxDens q')‖ ^ 2 with hv
    have hv0 : 0 ≤ v := sq_nonneg _
    have hvc : v ≤ C * ‖q - q'‖ := hC q q' hq hq'
    have hcoe : ((v.toNNReal : NNReal) : ℝ) = v := Real.coe_toNNReal _ hv0
    rw [hcoe, Real.rpow_natCast]
    calc v ^ (d + 1) * M ≤ (C * ‖q - q'‖) ^ (d + 1) * M := by gcongr
      _ = C ^ (d + 1) * M * ‖q - q'‖ ^ (d + 1) := by ring
  have hpos : (d : ℝ) < ((d + 1 : ℕ) : ℝ) := by push_cast; linarith
  obtain ⟨Y, hYc, hYm, hYZ⟩ := LQGMetric.WhiteNoise.exists_meas_continuous_modification_N
    (P := P) (Z := Z) hZm (p := 2 * (d + 1)) (by omega) hpos hmom
  refine ⟨fun x ω => Y x.ofLp ω, fun ω => (hYc ω).comp (PiLp.continuous_ofLp 2 _),
    fun x => hYm _, fun x => ?_⟩
  exact hYZ x.ofLp

end HigherDimLQGMetric
