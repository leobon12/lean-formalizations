import QuantumZipper.Proofs.Thm18.G2AgreeReg
import QuantumZipper.Proofs.LQG.LogSingGood
import QuantumZipper.Proofs.LQG.GoodTransforms
import QuantumZipper.Proofs.Section5.Prop17PalmCSetup

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 identification nodes: goodness of the Palm field

`g2PalmGoodStmt_holds`: for `0 < γ < 2`, `G2PalmGoodStmt γ` holds: for every real `x`, a.s. the
Palm field `h_x = normField γ (X₀ + ψ_x)` is `γ`-good.

Sources. Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, arXiv:0808.1560, §3.3, and
Sheffield, arXiv:1012.4797, §5.4 (proof of Prop. 5.5, p. 66): under the rooted measure at `x`
the field is a free-boundary GFF plus `γ(−log|· − x|)` plus a function that is continuous near
`x`; since `γ < Q` this is a.s. good. The formal route (own assembly, AGENT_GUIDE cost rule):

* on folded circles `h_x = ofFun G + addConst X₀ c` with
  `G = −γ log|· − x| + (2/γ) log|·| + γ log⁺|·|` (`normField_xPalm_fc`);
* the free field translated by `x` is a free field (`isFreeGFFModConstH_translate`), so
  a.s. it plus `γ(−log|·|)` is good (`LogSingGood.logSingGoodAS_holds`, M4-P4, `γ < Q`);
  translating back by `−x` keeps goodness (`IsLQGGood.translate`, M4-T2);
* the pole at `0` has **negative** strength `α = −2/γ` (boundary density factor
  `max(r,|t|)^{1}`), so the uniform smallness needed by `LogSingGood.hasBdryLimit_add_Lf` is
  elementary (`tight_Lf_neg`, own proof: the factor is `≤ δ` near `0` and the approximate
  masses of `[−1, 1]` are eventually bounded by the vague limit);
* the continuous part `γ log⁺|·|` and the constant are M4-T1;
* the resulting model agrees with `h_x` at all dyadic folded circles a.s. (RC1 for the
  translated free field with one logarithmic pole, `palmC_ae_evalReg_logAdd`), and goodness only
  depends on these coordinates (`WedgeGood.isLQGGood_congr_coords`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

open S5.FieldLaw.Raw GoodSample LogSingGood

local notation "Ω₀" => gffBase.Ω

/-! ## A boundary log singularity of negative strength -/

/-- The bump `max 0 (min 1 (2 − |t|))`. -/
def g2Bump (t : ℝ) : ℝ := max 0 (min 1 (2 - |t|))

theorem continuous_g2Bump : Continuous g2Bump := by
  unfold g2Bump; fun_prop

theorem g2Bump_nonneg (t : ℝ) : 0 ≤ g2Bump t := le_max_left _ _

theorem hasCompactSupport_g2Bump : HasCompactSupport g2Bump := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (-2 : ℝ)) (b := 2)) fun t ht => ?_
  have h2 : 2 < |t| := by
    by_contra h
    exact ht (abs_le.1 (not_lt.1 h))
  unfold g2Bump
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

theorem g2Bump_eq_one {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : g2Bump t = 1 := by
  have : |t| ≤ 1 := abs_le.2 ht
  unfold g2Bump
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem bdryR_Icc_le_bump {γ : ℝ} {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    {r : ℝ} (hr : 0 < r) :
    bdryR γ x r (Icc (-1) 1) ≤ ENNReal.ofReal (∫ t, g2Bump t ∂bdryR γ x r) := by
  have : IsFiniteMeasureOnCompacts (bdryR γ x r) := ⟨fun K hK => bdryR_lt_top γ hF hr hK⟩
  rw [ofReal_integral_eq_lintegral_ofReal
    (continuous_g2Bump.integrable_of_hasCompactSupport hasCompactSupport_g2Bump)
    (ae_of_all _ g2Bump_nonneg), ← lintegral_indicator_one measurableSet_Icc]
  refine lintegral_mono fun t => ?_
  by_cases ht : t ∈ Icc (-1 : ℝ) 1
  · rw [indicator_of_mem ht, Pi.one_apply, g2Bump_eq_one ht, ENNReal.ofReal_one]
  · rw [indicator_of_notMem ht]; exact zero_le

/-- Near `0`, a pole of nonpositive strength only lowers the approximate boundary measure. -/
theorem bdryR_add_Lf_Ioo_le {γ α : ℝ} {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith x F) (he : 0 ≤ -(α * γ / 2)) {r δ : ℝ} (hr : 0 < r) (hrδ : r ≤ δ) :
    bdryR γ (x + ofFun (Lf α)) r (Ioo (-δ) δ) ≤
      ENNReal.ofReal (δ ^ (-(α * γ / 2))) * bdryR γ x r (Ioo (-δ) δ) := by
  simp only [bdryR, withDensity_apply _ measurableSet_Ioo]
  rw [← lintegral_const_mul' (ENNReal.ofReal (δ ^ (-(α * γ / 2)))) _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
  rw [bdryDens_add_Lf hF γ α hr t, ← ENNReal.ofReal_mul (Real.rpow_nonneg (hr.le.trans hrδ) _)]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (bdryDens_nonneg γ x hr t))
  exact Real.rpow_le_rpow (lt_max_of_lt_left hr).le (max_le hrδ (abs_lt.2 ht).le) he

/-- **Uniform smallness near `0` for a pole of negative strength** (own elementary proof). -/
theorem tight_Lf_neg {γ α : ℝ} {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    {ν : Measure ℝ} (hν : HasBdryLimit γ x ν) (he : 0 < -(α * γ / 2)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ᶠ i in goodFilter,
      bdryR γ (x + ofFun (Lf α)) (goodRad i) (Ioo (-δ) δ) ≤ ENNReal.ofReal ε := by
  intro ε hε
  have hK0 : 0 < (∫ t, g2Bump t ∂ν) + 1 := by
    have : 0 ≤ ∫ t, g2Bump t ∂ν := integral_nonneg fun t => g2Bump_nonneg t
    linarith
  have hT := hν.2 g2Bump continuous_g2Bump hasCompactSupport_g2Bump
  set K := (∫ t, g2Bump t ∂ν) + 1 with hK
  set e := -(α * γ / 2) with he_def
  set δ := min 1 ((ε / K) ^ e⁻¹) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (Real.rpow_pos_of_pos (div_pos hε hK0) _)
  have hδe : δ ^ e * K ≤ ε := by
    have h1 : δ ^ e ≤ ε / K := by
      calc δ ^ e ≤ ((ε / K) ^ e⁻¹) ^ e :=
            Real.rpow_le_rpow hδ0.le (min_le_right _ _) he.le
        _ = ε / K := Real.rpow_inv_rpow (div_pos hε hK0).le he.ne'
    calc δ ^ e * K ≤ ε / K * K := mul_le_mul_of_nonneg_right h1 hK0.le
      _ = ε := div_mul_cancel₀ ε hK0.ne'
  refine ⟨δ, hδ0, ?_⟩
  filter_upwards [hT.eventually (gt_mem_nhds (lt_add_one (∫ t, g2Bump t ∂ν))),
    tendsto_goodRad.eventually (Ioo_mem_nhdsGT hδ0)] with i hi hr
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hB : bdryR γ x (goodRad i) (Ioo (-δ) δ) ≤ ENNReal.ofReal K :=
    calc bdryR γ x (goodRad i) (Ioo (-δ) δ) ≤ bdryR γ x (goodRad i) (Icc (-1) 1) :=
          measure_mono (Ioo_subset_Icc_self.trans (Icc_subset_Icc (by linarith) hδ1))
      _ ≤ ENNReal.ofReal (∫ t, g2Bump t ∂bdryR γ x (goodRad i)) := bdryR_Icc_le_bump hF hr.1
      _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal hi.le
  calc bdryR γ (x + ofFun (Lf α)) (goodRad i) (Ioo (-δ) δ)
      ≤ ENNReal.ofReal (δ ^ e) * bdryR γ x (goodRad i) (Ioo (-δ) δ) :=
        bdryR_add_Lf_Ioo_le hF he.le hr.1 hr.2.le
    _ ≤ ENNReal.ofReal (δ ^ e) * ENNReal.ofReal K := by gcongr
    _ = ENNReal.ofReal (δ ^ e * K) := (ENNReal.ofReal_mul (Real.rpow_nonneg hδ0.le _)).symm
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hδe

/-- **A good sample plus a boundary pole of negative strength at `0` is good.** -/
theorem isLQGGood_add_Lf_neg {γ α : ℝ} {z : FieldSample} (hz : IsLQGGood γ z)
    (he : 0 < -(α * γ / 2)) : IsLQGGood γ (z + ofFun (Lf α)) := by
  obtain ⟨⟨F, hF⟩, ⟨ν, hν⟩, ⟨μ, hμ⟩⟩ := hz
  exact ⟨⟨_, regular_add_Lf hF α⟩, ⟨_, hasBdryLimit_add_Lf hF hν (tight_Lf_neg hF hν he)⟩,
    ⟨_, hasAreaLimit_add_Lf hF hμ α⟩⟩

/-! ## The model of the Palm field -/

/-- The model: the free field translated by `x` plus `γ(−log|·|)`, translated back by `−x`,
plus the pole `(2/γ) log|·|` at `0`, the continuous part `γ log⁺|·|` and the Palm constant. -/
def g2PalmModel (γ x : ℝ) (ω : Ω₀) : FieldSample :=
  addConst (translate (ofFun (Lf γ) + palmCField gffBase.X x ω) ((-x : ℝ) : ℂ) +
    ofFun (Lf (-(2 / γ))) + ofFun (fun v => γ * Real.posLog ‖v‖)) (g2PalmConst γ x ω)

theorem g2_isFree_palmCField (x : ℝ) :
    IsFreeGFFModConstH (palmCField gffBase.X x) gffBase.P :=
  isFreeGFFModConstH_translate gffBase.gff x

theorem g2_continuousOn_posLog (γ : ℝ) : ContinuousOn (fun v : ℂ => γ * Real.posLog ‖v‖) Hbar := by
  have : Continuous fun v : ℂ => γ * Real.posLog ‖v‖ := by fun_prop
  exact this.continuousOn

/-- **The model is a.s. good.** -/
theorem ae_isLQGGood_g2PalmModel {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (x : ℝ) :
    ∀ᵐ ω ∂gffBase.P, IsLQGGood γ (g2PalmModel γ x ω) := by
  have hQ : γ < Qc γ := by
    unfold Qc
    have h : γ / 2 < 2 / γ := by
      rw [div_lt_div_iff₀ two_pos hγ]; nlinarith
    linarith
  have he : 0 < -((-(2 / γ)) * γ / 2) := by
    have h0 : γ ≠ 0 := hγ.ne'
    rw [show -((-(2 / γ)) * γ / 2) = (1 : ℝ) by field_simp]
    exact one_pos
  filter_upwards [LogSingGood.logSingGoodAS_holds hγ hγ2 hQ Ω₀ _ gffBase.P _ inferInstance
    (g2_isFree_palmCField x)] with ω hω
  have h1 : IsLQGGood γ (translate (ofFun (Lf γ) + palmCField gffBase.X x ω) ((-x : ℝ) : ℂ)) := by
    rw [add_comm]; exact hω.translate (-x)
  exact ((isLQGGood_add_Lf_neg h1 he).add_ofFun (g2_continuousOn_posLog γ)).addConst _

/-- **The model agrees with the Palm field at a fixed folded circle, a.s.** -/
theorem g2PalmModel_fc_ae {γ : ℝ} (hγ : 0 < γ) (x : ℝ) (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᵐ ω ∂gffBase.P, normField γ (xPalm γ x) ω (foldedCircle c ρ) =
      g2PalmModel γ x ω (foldedCircle c ρ) := by
  set d : ℂ := c + ((-x : ℝ) : ℂ) with hd
  have hsupp : foldedCircle d ρ (Metric.closedBall 0 (‖d‖ + ρ) ∩ Hbar)ᶜ = 0 :=
    CircleFubini.foldedCircle_support hρ.le le_rfl
  filter_upwards [palmC_ae_evalReg_logAdd (g2_isFree_palmCField x) hsupp
    (Cor15Group.isFrostman_fc d hρ) one_pos (-γ) 0 (g₁ := fun _ => 0) continuousOn_const]
    with ω hω
  have eL : (fun v : ℂ => -γ * Real.log ‖v - ((0 : ℝ) : ℂ)‖ + (fun _ => (0 : ℝ)) v) = Lf γ := by
    funext v; simp only [Lf, Complex.ofReal_zero, sub_zero, add_zero]; ring
  rw [eL] at hω
  have hT : translate (ofFun (Lf γ) + palmCField gffBase.X x ω) ((-x : ℝ) : ℂ)
      (foldedCircle c ρ) = (∫ z, Lf γ z ∂foldedCircle d ρ) + gffBase.X ω (foldedCircle c ρ) := by
    show evalReg _ ((foldedCircle c ρ).map (· + ((-x : ℝ) : ℂ))) = _
    rw [palmC_fc_map_add_real, ← hd, hω]
    congr 1
    show gffBase.X ω ((foldedCircle d ρ).map (· + (x : ℂ))) = _
    rw [palmC_fc_map_add_real, hd, show c + ((-x : ℝ) : ℂ) + (x : ℂ) = c by push_cast; ring]
  have hmL : Measurable (Lf γ) :=
    ((Real.measurable_log.comp measurable_norm).neg).const_mul γ
  have hInt : ∫ z, Lf γ z ∂foldedCircle d ρ =
      ∫ v, -γ * Real.log ‖v - (x : ℂ)‖ ∂foldedCircle c ρ := by
    rw [hd, ← palmC_fc_map_add_real c ρ (-x),
      integral_map (measurable_add_const _).aemeasurable hmL.aestronglyMeasurable]
    congr 1; funext v
    simp only [Lf]
    rw [show v + ((-x : ℝ) : ℂ) = v - (x : ℂ) by push_cast; ring]
    ring
  have i1 : Integrable (fun v => -γ * Real.log ‖v - (x : ℂ)‖) (foldedCircle c ρ) :=
    (palmC_integrable_log_sub_fc c x ρ).const_mul (-γ)
  have i2 : Integrable (Lf (-(2 / γ))) (foldedCircle c ρ) :=
    (CoordReg.integrable_log_norm_foldedCircle c ρ).neg.const_mul (-(2 / γ))
  have i3 : Integrable (fun v : ℂ => γ * Real.posLog ‖v‖) (foldedCircle c ρ) :=
    RegClosure.integrable_fc (g2_continuousOn_posLog γ) c hρ.le
  have eG : g2PalmG γ x = fun v => -γ * Real.log ‖v - (x : ℂ)‖ +
      (Lf (-(2 / γ)) v + γ * Real.posLog ‖v‖) := by
    funext v
    simp only [g2PalmG, Lf, Real.sqrt_sq hγ.le, Complex.ofReal_zero, sub_zero]
    ring
  have i23 : Integrable (fun v => Lf (-(2 / γ)) v + γ * Real.posLog ‖v‖) (foldedCircle c ρ) :=
    i2.add i3
  have h12 := integral_add i1 i23
  have h23 := integral_add i2 i3
  beta_reduce at h12 h23
  rw [normField_xPalm_fc γ x ω c hρ]
  simp only [g2PalmModel, addConst, Pi.add_apply]
  rw [hT]
  simp only [ofFun, measure_univ, ENNReal.toReal_one, mul_one]
  rw [eG]
  beta_reduce
  rw [h12, h23, hInt]
  ring

/-- **`G2PalmGoodStmt γ` holds** for `0 < γ < 2` (for every real `x`, a.s. the Palm field is
good). -/
theorem g2PalmGoodStmt_holds {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : G2PalmGoodStmt γ := by
  intro x _ _
  have hc : ∀ i : ℕ, ∀ᵐ ω ∂gffBase.P,
      normField γ (xPalm γ x) ω (foldedCircle (Factorization.dyadicIndex i).1
        (radius (Factorization.dyadicIndex i).2)) =
      g2PalmModel γ x ω (foldedCircle (Factorization.dyadicIndex i).1
        (radius (Factorization.dyadicIndex i).2)) :=
    fun i => g2PalmModel_fc_ae hγ x _ (radius_pos _)
  filter_upwards [ae_isLQGGood_g2PalmModel hγ hγ2 x, ae_all_iff.2 hc] with ω hg hco
  refine (WedgeGood.isLQGGood_congr_coords (x := normField γ (xPalm γ x) ω)
    (y := g2PalmModel γ x ω) ?_).2 hg
  funext i
  exact hco i

end Thm18Asm
end QuantumZipper
