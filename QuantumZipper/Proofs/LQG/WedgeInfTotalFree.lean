import QuantumZipper.Proofs.LQG.WedgeInfTotalScale
import QuantumZipper.Proofs.LQG.WedgeCanonical4
import QuantumZipper.Proofs.LQG.WedgeGood
import QuantumZipper.Proofs.LQG.GoodTransforms

/-!
# WEDGE-INF-2: infinite weighted lateral area of the free field near `∞`

For the free field `X` on `ℍ` modulo constants, `γ ∈ (0,2)` and `a < Q = Qc γ`, almost surely
`∫_{‖z‖ ≥ 1, z ∈ ℍ} ‖z‖^{−γa} e^{−γ h_{‖z‖}(0)} dμ_X(z) = ∞` (`ae_lateral_weighted_eq_top`),
where `h_r(0) = radAvgReg X r` is the radial part of `X`.

Proof (own argument; Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §1.6,
p. 21 only asserts that the wedge has "an infinite amount [of mass] in each neighborhood of ∞").
Put `R₀ = {1 < ‖z‖ < 2} ∩ ℍ`, `Φ(y) = e^{−γ sup_{q ∈ ℚ∩[1,2]} h_q(0)} μ_y(R₀)`.
* `Φ` is a measurable function of the full normalized coordinates `normCF` (it is invariant
  under adding constants), and `Φ(X) > 0` a.s. (positivity of `μ_X` on open sets).
* Deterministic scaling: with `X_n = rescale X Q 2ⁿ`, the window `2ⁿ R₀` contributes at least
  `c_n Φ(X_n)`, `c_n = 2^{−γa} 2^{γ(Q−a)n} → ∞` (for `a ≥ 0`; the general case is monotone in `a`).
* `normCF(X_n) =_d normCF(X)` (`map_normCF_rescale`), hence
  `P(total < K) ≤ P(c_n Φ(X) < K) → P(Φ(X) = 0) = 0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace QuantumZipper

namespace WedgeInf

open Factorization CoordsFull InfMass

/-! ## 1. The functional `Φ` -/

/-- Rational points of `[1,2]`. -/
abbrev Iq : Type := {q : ℚ // (1 : ℚ) ≤ q ∧ q ≤ 2}

instance : Nonempty Iq := ⟨⟨1, le_rfl, by norm_num⟩⟩

/-- `sup_{q ∈ ℚ ∩ [1,2]} h_q(0)`. -/
def radSup (y : FieldSample) : ℝ := ⨆ q : Iq, radAvgReg y (q.1 : ℝ)

theorem measurable_radSup : Measurable radSup :=
  Measurable.iSup fun _ => WedgeTK.measurable_radAvgReg₂.comp
    (measurable_id.prodMk measurable_const)

/-- The window `R₀ = {1 < ‖z‖ < 2} ∩ ℍ`. -/
def R0 : Set ℂ := {z | 1 < ‖z‖ ∧ ‖z‖ < 2} ∩ H

theorem isOpen_R0 : IsOpen R0 :=
  ((isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)).inter isOpen_H

open Classical in
/-- `Φ(y) = e^{−γ radSup y} μ_y(R₀)` (with the measurable global area measure). -/
def Phi (γ : ℝ) (y : FieldSample) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(γ * radSup y))) *
    (if IsLQGGood γ y then qAreaMeasure γ y else 0) R0

theorem measurable_Phi (γ : ℝ) : Measurable (Phi γ) := by
  classical
  unfold Phi
  exact (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    ((measurable_radSup.const_mul γ).neg))).mul
    ((Measure.measurable_coe isOpen_R0.measurableSet).comp
      (GoodMeas.measurable_qAreaMeasure_global γ))

theorem Phi_congr {γ : ℝ} {x x' : FieldSample} (h : coordsFull x = coordsFull x') :
    Phi γ x = Phi γ x' := by
  classical
  have hs : radSup x = radSup x' := by
    unfold radSup
    congr 1; funext q
    exact radAvgReg_congr_full h (by exact_mod_cast (show (0 : ℚ) ≤ q.1 by linarith [q.2.1]))
  have hc : coords x = coords x' := by
    rw [← WedgeCan4.piC_coordsFull, h, WedgeCan4.piC_coordsFull]
  have hg := WedgeGood.isLQGGood_congr_coords (γ := γ) hc
  have hq := qAreaMeasure_congr (avgReg_congr_full h) γ
  unfold Phi
  rw [hs, hq]
  by_cases hx : IsLQGGood γ x
  · rw [if_pos hx, if_pos (hg.1 hx)]
  · rw [if_neg hx, if_neg (fun h' => hx (hg.2 h'))]

/-- `Φ` read on the full coordinates. -/
def PsiF (γ : ℝ) (c : ℕ → ℝ) : ℝ≥0∞ := Phi γ (reconF c)

theorem measurable_PsiF (γ : ℝ) : Measurable (PsiF γ) :=
  (measurable_Phi γ).comp measurable_reconF

theorem PsiF_coordsFull (γ : ℝ) (x : FieldSample) : PsiF γ (coordsFull x) = Phi γ x :=
  Phi_congr (coordsFull_reconF x)

/-! ## 2. `radSup` along a radial limit -/

theorem RadLim.bddAbove {y : FieldSample} {f : ℝ → ℝ} (h : RadLim y f) :
    BddAbove (range fun q : Iq => radAvgReg y (q.1 : ℝ)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).bddAbove_image
    (h.1.mono fun s (hs : s ∈ Icc (1 : ℝ) 2) => (show (0 : ℝ) < s by linarith [hs.1]))
  refine ⟨C, ?_⟩
  rintro _ ⟨q, rfl⟩
  have h1 : (1 : ℝ) ≤ q.1 := by exact_mod_cast q.2.1
  have h2 : (q.1 : ℝ) ≤ 2 := by exact_mod_cast q.2.2
  show radAvgReg y (q.1 : ℝ) ≤ C
  rw [h.radAvgReg_eq (by linarith)]
  exact hC ⟨_, ⟨h1, h2⟩, rfl⟩

theorem RadLim.le_radSup {y : FieldSample} {f : ℝ → ℝ} (h : RadLim y f) {s : ℝ}
    (hs : s ∈ Icc (1 : ℝ) 2) : f s ≤ radSup y := by
  refine GoodMeas.le_of_rat_Icc (h.1.mono fun t (ht : t ∈ Icc (1 : ℝ) 2) =>
    (show (0 : ℝ) < t by linarith [ht.1])) (fun q h1 h2 => ?_) hs
  rw [← h.radAvgReg_eq (by linarith)]
  have hq : (1 : ℚ) ≤ q ∧ q ≤ 2 := ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  exact le_ciSup h.bddAbove (⟨q, hq⟩ : Iq)

theorem RadLim.radSup_addConst {y : FieldSample} {f : ℝ → ℝ} (h : RadLim y f) (c : ℝ) :
    radSup (addConst y c) = radSup y + c := by
  unfold radSup
  have e : (fun q : Iq => radAvgReg (addConst y c) (q.1 : ℝ)) =
      fun q : Iq => radAvgReg y (q.1 : ℝ) + c := by
    funext q
    have h1 : (0 : ℝ) < q.1 := by
      have : (1 : ℝ) ≤ q.1 := by exact_mod_cast q.2.1
      linarith
    rw [(h.add_const c).radAvgReg_eq h1, h.radAvgReg_eq h1]
  rw [e]
  exact (Monotone.map_ciSup_of_continuousAt (f := fun t : ℝ => t + c)
    (continuous_id.add continuous_const).continuousAt (fun _ _ hst => by simpa using hst) h.bddAbove).symm

theorem Phi_addConst {γ : ℝ} {y : FieldSample} {f : ℝ → ℝ} (hy : IsLQGGood γ y)
    (h : RadLim y f) (c : ℝ) : Phi γ (addConst y c) = Phi γ y := by
  unfold Phi
  rw [if_pos (hy.addConst c), if_pos hy, h.radSup_addConst, GoodSample.qAreaMeasure_addConst hy,
    Measure.smul_apply, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add]
  congr 4
  ring

theorem PsiF_normCF {γ : ℝ} {y : FieldSample} {f : ℝ → ℝ} (hy : IsLQGGood γ y)
    (h : RadLim y f) : PsiF γ (normCF y) = Phi γ y := by
  rw [normCF_eq, PsiF_coordsFull, Phi_addConst hy h]

/-! ## 3. The weighted mass and its dyadic windows -/

/-- The weighted lateral mass outside the unit disc,
`∫_{‖z‖ ≥ 1, z ∈ ℍ} ‖z‖^{−γa} e^{−γ h_{‖z‖}(0)} dμ_y`. -/
def latW (γ a : ℝ) (y : FieldSample) : ℝ≥0∞ :=
  ∫⁻ z in {z : ℂ | 1 ≤ ‖z‖} ∩ H, ENNReal.ofReal (‖z‖ ^ (-(γ * a)) *
    Real.exp (-(γ * radAvgReg y ‖z‖))) ∂qAreaMeasure γ y

/-- The window constant `c_n = (2·2ⁿ)^{−γa} (2ⁿ)^{γQ}`. -/
def cst (γ a : ℝ) (n : ℕ) : ℝ :=
  (2 * (2 : ℝ) ^ n) ^ (-(γ * a)) * Real.exp (γ * Qc γ * Real.log ((2 : ℝ) ^ n))

theorem cst_eq (γ a : ℝ) (n : ℕ) :
    cst γ a n = Real.exp (γ * (Qc γ - a) * Real.log 2 * n + -(γ * a * Real.log 2)) := by
  unfold cst
  rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_add,
    Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  congr 1; ring

theorem cst_pos (γ a : ℝ) (n : ℕ) : 0 < cst γ a n := by
  rw [cst_eq]; exact Real.exp_pos _

theorem latW_ge {γ a : ℝ} (hγ : 0 < γ) (ha : 0 ≤ a) {y : FieldSample} {F : ℂ × ℝ → ℝ}
    (hy : IsLQGGood γ y) (hF : WedgeTK.GoodRad y F) (n : ℕ) :
    ENNReal.ofReal (cst γ a n) * Phi γ (rescale y (Qc γ) ((2 : ℝ) ^ n)) ≤ latW γ a y := by
  have hcst : cst γ a n = (2 * (2 : ℝ) ^ n) ^ (-(γ * a)) *
      Real.exp (γ * Qc γ * Real.log ((2 : ℝ) ^ n)) := rfl
  set b : ℝ := (2 : ℝ) ^ n with hb_def
  have hb : 0 < b := by positivity
  have hb1 : 1 ≤ b := one_le_pow₀ (by norm_num)
  set yn := rescale y (Qc γ) b with hyn_def
  have hyn : IsLQGGood γ yn := hy.rescale hγ hb
  have hR := radLim_rescale hF.1 (Qc γ) hb
  set Rn : Set ℂ := (fun z : ℂ => z / (b : ℂ)) ⁻¹' R0 with hRn
  have hmeas : Measurable fun z : ℂ => z / (b : ℂ) := measurable_id.div_const _
  have hRnm : MeasurableSet Rn := hmeas isOpen_R0.measurableSet
  have hμ : qAreaMeasure γ yn R0 = qAreaMeasure γ y Rn := by
    rw [GoodTransforms.qAreaMeasure_rescale hy hγ hb,
      Measure.map_apply hmeas isOpen_R0.measurableSet]
  have hmem : ∀ z ∈ Rn, 1 < ‖z / (b : ℂ)‖ ∧ ‖z / (b : ℂ)‖ < 2 ∧
      ‖z‖ = b * ‖z / (b : ℂ)‖ ∧ z ∈ H := by
    intro z hz
    obtain ⟨⟨h1, h2⟩, h3⟩ := hz
    refine ⟨h1, h2, ?_, ?_⟩
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]; field_simp
    · have h3' : 0 < (z / (b : ℂ)).im := h3
      rw [Complex.div_ofReal_im] at h3'
      exact (div_pos_iff_of_pos_right hb).1 h3'
  have hsub : Rn ⊆ {z : ℂ | 1 ≤ ‖z‖} ∩ H := fun z hz => by
    obtain ⟨h1, -, h3, h4⟩ := hmem z hz
    refine ⟨?_, h4⟩
    show 1 ≤ ‖z‖
    rw [h3]; nlinarith
  have hpt : ∀ z ∈ Rn, ENNReal.ofReal (cst γ a n * Real.exp (-(γ * radSup yn))) ≤
      ENNReal.ofReal (‖z‖ ^ (-(γ * a)) * Real.exp (-(γ * radAvgReg y ‖z‖))) := by
    intro z hz
    obtain ⟨h1, h2, h3, -⟩ := hmem z hz
    refine ENNReal.ofReal_le_ofReal ?_
    have hzpos : 0 < ‖z‖ := by rw [h3]; exact mul_pos hb (by linarith)
    have hrad : radAvgReg y ‖z‖ ≤ radSup yn - Qc γ * Real.log b := by
      have := hR.le_radSup ⟨h1.le, h2.le⟩
      rw [hF.radAvgReg_eq hzpos, h3]
      linarith
    have hpow : (2 * b) ^ (-(γ * a)) ≤ ‖z‖ ^ (-(γ * a)) :=
      Real.rpow_le_rpow_of_nonpos hzpos (by rw [h3]; nlinarith) (by nlinarith)
    rw [hcst]
    calc (2 * b) ^ (-(γ * a)) * Real.exp (γ * Qc γ * Real.log b) * Real.exp (-(γ * radSup yn))
        = (2 * b) ^ (-(γ * a)) * Real.exp (-(γ * (radSup yn - Qc γ * Real.log b))) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ ‖z‖ ^ (-(γ * a)) * Real.exp (-(γ * radAvgReg y ‖z‖)) := by
          refine mul_le_mul hpow (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (by positivity)
          nlinarith
  calc ENNReal.ofReal (cst γ a n) * Phi γ yn
      = ENNReal.ofReal (cst γ a n * Real.exp (-(γ * radSup yn))) * qAreaMeasure γ y Rn := by
        unfold Phi
        rw [if_pos hyn, hμ, ← mul_assoc, ← ENNReal.ofReal_mul (cst_pos γ a n).le]
    _ = ∫⁻ _ in Rn, ENNReal.ofReal (cst γ a n * Real.exp (-(γ * radSup yn))) ∂qAreaMeasure γ y :=
        (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ z in Rn, ENNReal.ofReal (‖z‖ ^ (-(γ * a)) * Real.exp (-(γ * radAvgReg y ‖z‖)))
          ∂qAreaMeasure γ y := setLIntegral_mono' hRnm hpt
    _ ≤ latW γ a y := lintegral_mono_set hsub

theorem latW_anti {γ a a' : ℝ} (hγ : 0 ≤ γ) (h : a ≤ a') (y : FieldSample) :
    latW γ a' y ≤ latW γ a y := by
  unfold latW
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem ((measurableSet_le measurable_const measurable_norm).inter
    isOpen_H.measurableSet)] with z hz
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  exact Real.rpow_le_rpow_of_exponent_le hz.1 (by nlinarith)

end WedgeInf

end QuantumZipper
