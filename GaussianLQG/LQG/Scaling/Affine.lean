import GaussianLQG.LQG.Scaling.Measurability
import GaussianLQG.Field.Pairing.Circle

/-!
# The rescaled metric of (S4) and deterministic dilation bounds

For a `Setup` and `a ≠ 0`, `Setup.rescaled γ z a ω` is the random continuous function
`(u, v) ↦ |a|^{-ξQ} e^{-ξ h_{|a|}(z)} D(z + a u, z + a v)` of (S4), which has the law of `D`
(`Setup.map_rescaled`). It is measurable (`Setup.measurable_rescaled`), so integrals of
measurable functionals transfer (`Setup.lintegral_comp_rescaled`).

Deterministic facts (blueprint Lemma `lem:scaling`(c),(d)): if `d'(u, v) = c d(R u, R v)`, then
`A_d(B̄_R) ≤ c⁻¹ R^{-1/2} A_{d'}(B̄_1)` (`holderConst_closedBall_le_of_rescale`) and
`L_R(d)⁻¹ ≤ c L_1(d')⁻¹` (`annulusCross_inv_le_of_rescale`); moreover `I_d(B̄_2, 1) ≤ L_1(d)`
(`sepInf_le_annulusCross_one`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace GaussianLQG

/-! ## Continuous metrics are positive off the diagonal -/

theorem contMetric_nonneg (D : LQGMetric.ContMetric) (z w : ℂ) : 0 ≤ D.1 (z, w) := by
  have h1 := D.2.triangle z w z
  rw [D.2.self_eq_zero z, D.2.symm w z] at h1
  linarith

theorem contMetric_pos (D : LQGMetric.ContMetric) {z w : ℂ} (hzw : z ≠ w) : 0 < D.1 (z, w) :=
  lt_of_le_of_ne (contMetric_nonneg D z w) fun h => hzw (D.2.eq_of_eq_zero z w h.symm)

/-! ## Comparisons of `D(z, w)` with `A(K)` and `I(K, δ)` -/

theorem ofReal_div_le_holderConst (d : ℂ × ℂ → ℝ) {K : Set ℂ} {z w : ℂ} (hz : z ∈ K)
    (hw : w ∈ K) (hzw : z ≠ w) :
    ENNReal.ofReal (d (z, w) / ‖z - w‖ ^ (1 / 2 : ℝ)) ≤ holderConst d K :=
  le_iSup₂_of_le z hz (le_iSup₂_of_le w hw (le_iSup_of_le hzw le_rfl))

theorem sepInf_le_ofReal (d : ℂ × ℂ → ℝ) {K : Set ℂ} {δ : ℝ} {z w : ℂ} (hz : z ∈ K)
    (hw : w ∈ K) (hδ : δ ≤ ‖z - w‖) : sepInf d K δ ≤ ENNReal.ofReal (d (z, w)) :=
  iInf₂_le_of_le z hz (iInf₂_le_of_le w hw (iInf_le_of_le hδ le_rfl))

/-- `I(B̄_2, 1) ≤ L_1`: a pair on the circles of radii `1` and `2` is `1`-separated in `B̄_2`. -/
theorem sepInf_le_annulusCross_one (d : ℂ × ℂ → ℝ) :
    sepInf d (closedBall (0 : ℂ) 2) 1 ≤ annulusCross d 1 := by
  refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => sepInf_le_ofReal d ?_ ?_ ?_
  · rw [mem_closedBall, dist_zero_right, (mem_sphere_zero_iff_norm).1 hx]; norm_num
  · rw [mem_closedBall, dist_zero_right, (mem_sphere_zero_iff_norm).1 hy]; norm_num
  · have h1 := norm_sub_norm_le y x
    rw [(mem_sphere_zero_iff_norm).1 hx, (mem_sphere_zero_iff_norm).1 hy, norm_sub_rev] at h1
    linarith

/-! ## Deterministic dilation bounds -/

theorem norm_div_ofReal {R : ℝ} (hR : 0 < R) (z : ℂ) : ‖z / (R : ℂ)‖ = ‖z‖ / R := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]

theorem ofReal_mul_div_ofReal {R : ℝ} (hR : 0 < R) (z : ℂ) : (R : ℂ) * (z / (R : ℂ)) = z := by
  have : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  field_simp

/-- `A_d(B̄_R) ≤ c⁻¹ R^{-1/2} A_{d'}(B̄_1)` when `d'(u, v) = c d(R u, R v)`. -/
theorem holderConst_closedBall_le_of_rescale {d d' : ℂ × ℂ → ℝ} {R c : ℝ} (hR : 0 < R)
    (hc : 0 < c) (hdd' : ∀ u v : ℂ, d' (u, v) = c * d ((R : ℂ) * u, (R : ℂ) * v)) :
    holderConst d (closedBall 0 R) ≤
      ENNReal.ofReal (c⁻¹ * (R ^ (1 / 2 : ℝ))⁻¹) * holderConst d' (closedBall 0 1) := by
  refine iSup₂_le fun z hz => iSup₂_le fun w hw => iSup_le fun hzw => ?_
  set x : ℂ := z / (R : ℂ)
  set y : ℂ := w / (R : ℂ)
  have hR' : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  have hx : x ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall, dist_zero_right, norm_div_ofReal hR, div_le_one hR]
    simpa using hz
  have hy : y ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall, dist_zero_right, norm_div_ofReal hR, div_le_one hR]
    simpa using hw
  have hxy : x ≠ y := fun h => hzw (by
    have := congrArg (fun t => (R : ℂ) * t) h
    simpa only [x, y, ofReal_mul_div_ofReal hR] using this)
  have hd' : d' (x, y) = c * d (z, w) := by
    rw [hdd', ofReal_mul_div_ofReal hR, ofReal_mul_div_ofReal hR]
  have hnorm : ‖x - y‖ = ‖z - w‖ / R := by
    rw [show x - y = (z - w) / (R : ℂ) by ring, norm_div_ofReal hR]
  have hzw0 : 0 < ‖z - w‖ := norm_pos_iff.2 (sub_ne_zero.2 hzw)
  have hR2 : 0 < R ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hR _
  have hzw2 : 0 < ‖z - w‖ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hzw0 _
  have key : ENNReal.ofReal (d (z, w) / ‖z - w‖ ^ (1 / 2 : ℝ)) =
      ENNReal.ofReal (c⁻¹ * (R ^ (1 / 2 : ℝ))⁻¹) *
        ENNReal.ofReal (d' (x, y) / ‖x - y‖ ^ (1 / 2 : ℝ)) := by
    rw [← ENNReal.ofReal_mul (by positivity), hd', hnorm,
      Real.div_rpow hzw0.le hR.le]
    congr 1
    field_simp
  rw [key]
  exact mul_le_mul_right (ofReal_div_le_holderConst d' hx hy hxy) _

/-- `c⁻¹ L_1(d') ≤ L_R(d)` when `d'(u, v) = c d(R u, R v)`. -/
theorem ofReal_inv_mul_annulusCross_le_of_rescale {d d' : ℂ × ℂ → ℝ} {R c : ℝ} (hR : 0 < R)
    (hc : 0 < c) (hdd' : ∀ u v : ℂ, d' (u, v) = c * d ((R : ℂ) * u, (R : ℂ) * v)) :
    ENNReal.ofReal c⁻¹ * annulusCross d' 1 ≤ annulusCross d R := by
  refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
  have hx' : x / (R : ℂ) ∈ sphere (0 : ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_div_ofReal hR, (mem_sphere_zero_iff_norm).1 hx,
      div_self hR.ne']
  have hy' : y / (R : ℂ) ∈ sphere (0 : ℂ) (2 * 1) := by
    rw [mem_sphere_zero_iff_norm, norm_div_ofReal hR, (mem_sphere_zero_iff_norm).1 hy]
    field_simp
  have hd' : d (x, y) = c⁻¹ * d' (x / (R : ℂ), y / (R : ℂ)) := by
    rw [hdd', ofReal_mul_div_ofReal hR, ofReal_mul_div_ofReal hR]
    field_simp
  rw [hd', ENNReal.ofReal_mul (inv_nonneg.2 hc.le)]
  exact mul_le_mul_right (iInf₂_le_of_le _ hx' (iInf₂_le_of_le _ hy' le_rfl)) _

/-- `L_R(d)⁻¹ ≤ c L_1(d')⁻¹` when `d'(u, v) = c d(R u, R v)`. -/
theorem annulusCross_inv_le_of_rescale {d d' : ℂ × ℂ → ℝ} {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hdd' : ∀ u v : ℂ, d' (u, v) = c * d ((R : ℂ) * u, (R : ℂ) * v)) :
    (annulusCross d R)⁻¹ ≤ ENNReal.ofReal c * (annulusCross d' 1)⁻¹ := by
  have h := ENNReal.inv_le_inv.2 (ofReal_inv_mul_annulusCross_le_of_rescale hR hc hdd')
  rwa [ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne')
    (Or.inl ENNReal.ofReal_ne_top), ← ENNReal.ofReal_inv_of_pos (inv_pos.2 hc), inv_inv] at h

/-! ## The rescaled metric of (S4) -/

namespace Setup

variable (S : Setup)

/-- The factor `|a|^{-ξQ} e^{-ξ h_{|a|}(z)}` of (S4). -/
def rescaleFactor (γ : ℝ) (z a : ℂ) (ω : Coord) : ℝ :=
  ‖a‖ ^ (-(S.ξ γ * LQGMetric.Q γ)) *
    Real.exp (-(S.ξ γ) * pairing S.e (circleMeasure z ‖a‖) ω)

/-- The rescaled metric `(u, v) ↦ |a|^{-ξQ} e^{-ξ h_{|a|}(z)} D(z + a u, z + a v)` of (S4). -/
def rescaled (γ : ℝ) (z a : ℂ) (ω : Coord) : C(ℂ × ℂ, ℝ) :=
  S.rescaleFactor γ z a ω • (S.D γ ω).1.comp (affinePair z a)

theorem rescaled_apply (γ : ℝ) (z a : ℂ) (ω : Coord) (u v : ℂ) :
    S.rescaled γ z a ω (u, v) = S.rescaleFactor γ z a ω * (S.D γ ω).1 (z + a * u, z + a * v) :=
  rfl

theorem rescaleFactor_pos (γ : ℝ) (z : ℂ) {a : ℂ} (ha : a ≠ 0) (ω : Coord) :
    0 < S.rescaleFactor γ z a ω :=
  mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.2 ha) _) (Real.exp_pos _)

theorem measurable_rescaleFactor (γ : ℝ) (z a : ℂ) : Measurable (S.rescaleFactor γ z a) :=
  measurable_const.mul (Real.measurable_exp.comp ((measurable_pairing S.e _).const_mul _))

theorem measurable_rescaled (γ : ℝ) (z a : ℂ) : Measurable (S.rescaled γ z a) := by
  rw [ContinuousMap.measurable_iff_eval]
  intro p
  exact (S.measurable_rescaleFactor γ z a).mul (S.measurable_D_apply γ _)

/-- (S4): the rescaled metric has the law of `D`. -/
theorem map_rescaled {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (z : ℂ) {a : ℂ} (ha : a ≠ 0) :
    stdP.map (S.rescaled γ z a) = stdP.map fun ω => (S.D γ ω).1 :=
  S.S4 γ hγ hγ2 z a ha

/-- Transfer of integrals of measurable functionals along (S4). -/
theorem lintegral_comp_rescaled {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (z : ℂ) {a : ℂ} (ha : a ≠ 0)
    {F : C(ℂ × ℂ, ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (S.rescaled γ z a ω) ∂stdP = ∫⁻ ω, F (S.D γ ω).1 ∂stdP := by
  rw [← lintegral_map hF (S.measurable_rescaled γ z a), S.map_rescaled hγ hγ2 z ha,
    lintegral_map hF (S.measurable_coe_D γ)]

/-- Transfer of laws of measurable real functionals along (S4). -/
theorem map_comp_rescaled {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (z : ℂ) {a : ℂ} (ha : a ≠ 0)
    {F : C(ℂ × ℂ, ℝ) → ℝ} (hF : Measurable F) :
    stdP.map (fun ω => F (S.rescaled γ z a ω)) = stdP.map fun ω => F (S.D γ ω).1 := by
  calc stdP.map (fun ω => F (S.rescaled γ z a ω))
      = (stdP.map (S.rescaled γ z a)).map F :=
        (Measure.map_map hF (S.measurable_rescaled γ z a)).symm
    _ = (stdP.map fun ω => (S.D γ ω).1).map F := by rw [S.map_rescaled hγ hγ2 z ha]
    _ = stdP.map fun ω => F (S.D γ ω).1 := Measure.map_map hF (S.measurable_coe_D γ)

/-! ## Compatibility names (cleanup W15) -/

alias measurable_holderConst_D := measurable_holderConst

alias measurable_sepInf_D := measurable_sepInf

end Setup

end GaussianLQG
