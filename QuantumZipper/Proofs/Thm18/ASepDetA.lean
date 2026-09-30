import QuantumZipper.Proofs.Thm18.ASepDetGeo
import QuantumZipper.Proofs.Thm18.ASepModJ
import QuantumZipper.Proofs.Thm18.G4SepUC2Det
import QuantumZipper.Proofs.Thm18.G4SepUC2Ident
import QuantumZipper.Proofs.Zipper.XFlowUCLog
import QuantumZipper.Proofs.Zipper.JointModDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP-DET (a): the deterministic integrand `Gdet` of the unzipped field

The deterministic part `G4Core.detGen W τ a' g₁ Q ν j` of the smoothed pairing identity
`G4Core.ae_ident_fwdMapInv_gen` is the `ν`-integral of folded-circle means of
`Gdet_τ(v) = a' log ‖ψ_τ(v)‖ + g₁(ψ_τ(v)) + Q log ‖ψ_τ'(v)‖` (`ψ_τ = fwdMapInv W τ`):

* `Dfun_eq_integral_Gdet`, `detGen_eq_Gdet`: this identity;
* `continuousOn_Gdet_joint`: joint continuity on `[0,T] × ℍ`;
* `Gdet_logBound`: `|Gdet_t(v)| ≤ A + B |log Im v|` on bounded parts of `ℍ`, uniformly in
  `t ∈ [0,T]`.

Own elementary bookkeeping (as `F1.xFlowLogUCStmt_holds`, XFlowUCLog.lean).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace ASep

open RegCont TwoPoint CoordReg RegUnif UnzipInvariance F1

/-- The deterministic integrand of the unzipped field at time `t`. -/
def Gdet (W : ℝ → ℝ) (a' : ℝ) (g₁ : ℂ → ℝ) (Q : ℝ) (t : ℝ) (v : ℂ) : ℝ :=
  a' * Real.log ‖fwdMapInv W t v‖ + g₁ (fwdMapInv W t v) +
    Q * Real.log ‖deriv (fwdMapInv W t) v‖

/-- The limit of the deterministic part for the A-sep family at `τ' = 0`. -/
def detLimA0 (W : ℝ → ℝ) (a' : ℝ) (g₁ : ℂ → ℝ) (Q : ℝ) (d : ℂ) (r : ℝ) (p : Fin 2 → ℝ) : ℝ :=
  ∫ z, Gdet W a' g₁ Q (p 0) z ∂((foldedCircle d r).map fun w => fwdMap W (p 0) ((p 1 : ℂ) * w))

/-- Folded-circle means of `Gdet` are the `Dfun` of the time-reversed driver. -/
theorem Dfun_eq_integral_Gdet {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {τ : ℝ}
    (hτ : 0 ≤ τ) (a' : ℝ) {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁) (Q : ℝ) (z : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) :
    Dfun (fun s => W (τ - s) - W τ) τ a' g₁ Q (z, ρ) =
      ∫ v, Gdet W a' g₁ Q τ v ∂foldedCircle z ρ := by
  set V : ℝ → ℝ := fun s => W (τ - s) - W τ with hVdef
  have hV : Continuous V := (hW.comp (continuous_const.sub continuous_id)).sub continuous_const
  have h1 := (logBounded_log_norm_revMap (W := V) (T := τ) hV hτ).integrable z hρ
  have h2 := (logBounded_comp_revMap (W := V) (T := τ) hV hτ hg₁).integrable z hρ
  have h3 := (logBounded_log_norm_deriv_revMap (W := V) (T := τ) hV hτ).integrable z hρ
  have e : ∫ v, Gdet W a' g₁ Q τ v ∂foldedCircle z ρ =
      ∫ u, (a' * Real.log ‖revMap V τ u‖ + g₁ (revMap V τ u) +
        Q * Real.log ‖deriv (revMap V τ) u‖) ∂foldedCircle z ρ := by
    refine integral_congr_ae ?_
    filter_upwards [foldedCircle_ae_mem_H z hρ] with u hu
    simp only [Gdet]
    rw [deriv_fwdMapInv_eq hW hW0 hτ hu, fwdMapInv_eq_revMap_timeRev W hW hW0 hτ hu]
  have i1 : Integrable (fun u => a' * Real.log ‖revMap V τ u‖ + g₁ (revMap V τ u))
      (foldedCircle z ρ) := (h1.const_mul a').add h2
  rw [e, integral_add i1 (h3.const_mul Q), integral_add (h1.const_mul a') h2,
    integral_const_mul, integral_const_mul]
  rfl

/-- **The deterministic part as a double integral of `Gdet`.** -/
theorem detGen_eq_Gdet {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {τ : ℝ} (hτ : 0 ≤ τ)
    (a' : ℝ) {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁) (Q : ℝ) (ν : Measure ℂ) (j : ℕ) :
    Thm18Asm.G4Core.detGen W τ a' g₁ Q ν j =
      ∫ z, (∫ v, Gdet W a' g₁ Q τ v ∂foldedCircle z (radius j)) ∂ν := by
  unfold Thm18Asm.G4Core.detGen
  exact integral_congr_ae (Eventually.of_forall fun z =>
    Dfun_eq_integral_Gdet hW hW0 hτ a' hg₁ Q z (radius_pos j))

/-- Measurability (indeed continuity) of the folded-circle means of `Gdet`. -/
theorem continuous_integral_Gdet {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {τ : ℝ}
    (hτ : 0 ≤ τ) (a' : ℝ) {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁) (Q : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    Continuous fun z => ∫ v, Gdet W a' g₁ Q τ v ∂foldedCircle z ρ := by
  set V : ℝ → ℝ := fun s => W (τ - s) - W τ with hVdef
  have hV : Continuous V := (hW.comp (continuous_const.sub continuous_id)).sub continuous_const
  have hc : Continuous fun z : ℂ => Dfun V τ a' g₁ Q (z, ρ) :=
    (continuousOn_Dfun (W := V) (T := τ) hV hτ a' hg₁ Q).comp_continuous
      (continuous_id.prodMk continuous_const) fun _ => hρ
  refine hc.congr fun z => ?_
  exact Dfun_eq_integral_Gdet hW hW0 hτ a' hg₁ Q z hρ

/-- **Joint continuity of `Gdet` on `[0,T] × ℍ`.** -/
theorem continuousOn_Gdet_joint {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) (T : ℝ)
    (a' : ℝ) {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁) (Q : ℝ) :
    ContinuousOn (fun q : ℝ × ℂ => Gdet W a' g₁ Q q.1 q.2) (Icc 0 T ×ˢ H) := by
  obtain ⟨M, hM⟩ := exists_abs_le_on_Icc hW T
  have hj := continuousOn_fwdMapInv_joint hW hW0 T
  have hlog : ContinuousOn (fun q : ℝ × ℂ => Real.log ‖fwdMapInv W q.1 q.2‖)
      (Icc 0 T ×ˢ H) :=
    hj.norm.log fun q hq => by
      have h0 : 0 < (fwdMapInv W q.1 q.2).im :=
        (fwdMapInv_mem_H_bound hW hW0 hM hq.1.1 hq.1.2 hq.2 le_rfl).1
      exact norm_ne_zero_iff.2 fun h => by rw [h, Complex.zero_im] at h0; exact lt_irrefl _ h0
  exact ((continuousOn_const.mul hlog).add (hg₁.comp_continuousOn hj)).add
    (continuousOn_const.mul (continuousOn_log_deriv_fwdMapInv_joint hW hW0 T))

/-- **Logarithmic bound for `Gdet`**, uniform in `t ∈ [0,T]`. -/
theorem Gdet_logBound {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) (T R : ℝ) (hT : 0 ≤ T)
    (a' : ℝ) {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁) (Q : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ v ∈ H, ‖v‖ ≤ R →
      |Gdet W a' g₁ Q t v| ≤ A + (|a'| + |Q|) * |Real.log v.im| := by
  obtain ⟨A1, hA10, hA1⟩ := xfl_abs_log_fwdMapInv_le hW hW0 T R
  obtain ⟨M, hM⟩ := exists_abs_le_on_Icc hW T
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) (revBound (2 * M) T R)).exists_bound_of_continuousOn
    hg₁.continuousOn
  set R2 : ℝ := |R| + 1 with hR2
  have hR21 : 1 ≤ R2 := by linarith [abs_nonneg R]
  set Ld : ℝ := Real.log (Real.sqrt (R2 ^ 2 + 4 * T)) with hLd
  have hLd0 : 0 ≤ Ld := Real.log_nonneg (by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith))
  refine ⟨|a'| * A1 + max C 0 + |Q| * Ld, by positivity, fun t ht v hv hvR => ?_⟩
  have e1 := hA1 t ht v hv hvR
  have hb := fwdMapInv_mem_H_bound hW hW0 hM ht.1 ht.2 hv hvR
  have e2 : |g₁ (fwdMapInv W t v)| ≤ max C 0 := by
    have := hC _ (by rw [Metric.mem_closedBall, dist_zero_right]; exact hb.2)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hvim : v.im ≤ R2 := by
    linarith [Complex.im_le_norm v, le_abs_self R]
  have e3 := abs_log_norm_deriv_revMap_le (continuous_vRev hW t) ht.1 hv hvim
  rw [← deriv_fwdMapInv_eq hW hW0 ht.1 hv] at e3
  have h1s : (1 : ℝ) ≤ Real.sqrt (R2 ^ 2 + 4 * t) := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [ht.1])
  have e4 : |Real.log (Real.sqrt (R2 ^ 2 + 4 * t))| ≤ Ld := by
    rw [abs_of_nonneg (Real.log_nonneg h1s)]
    exact Real.log_le_log (by linarith) (Real.sqrt_le_sqrt (by nlinarith [ht.2]))
  unfold Gdet
  have k1 : |a' * Real.log ‖fwdMapInv W t v‖| ≤ |a'| * (A1 + |Real.log v.im|) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left e1 (abs_nonneg _)
  have k3 : |Q * Real.log ‖deriv (fwdMapInv W t) v‖| ≤ |Q| * (Ld + |Real.log v.im|) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  calc _ ≤ |a' * Real.log ‖fwdMapInv W t v‖ + g₁ (fwdMapInv W t v)| +
        |Q * Real.log ‖deriv (fwdMapInv W t) v‖| := abs_add_le _ _
    _ ≤ |a' * Real.log ‖fwdMapInv W t v‖| + |g₁ (fwdMapInv W t v)| +
        |Q * Real.log ‖deriv (fwdMapInv W t) v‖| := by gcongr; exact abs_add_le _ _
    _ ≤ _ := by nlinarith [abs_nonneg a', abs_nonneg Q]

end ASep
end QuantumZipper
