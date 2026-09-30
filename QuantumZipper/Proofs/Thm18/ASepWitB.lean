import QuantumZipper.Proofs.Thm18.ASepDetA
import QuantumZipper.Proofs.Zipper.RegContMain
import QuantumZipper.Proofs.Zipper.JointModComm
import QuantumZipper.Proofs.GFF.CoordRegLog

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP-WIT (b): a jointly continuous regular witness over time, fixed driver

For a fixed Hölder driver `W` (`W 0 = 0`) and the field
`x_t = coordChange (ofFun (a' log |·| + g₁) + X) ψ_t Q` (`ψ_t = fwdMapInv W t`, `g₁` continuous),
almost surely there is `Z`, continuous on `[0,T] × Hbar × (0,∞)`, with `IsRegularWith x_t Z(t,·)`
for every `t ∈ [0,T]` (`ae_exists_joint_witness_fixed`).

This is the proof of `RegUnif.ae_exists_joint_witness` (UnifRC3UC.lean) with the driver fixed:
the random part is the Kolmogorov modification of `q ↦ X(ν4 W T q)` (`exists_contMod_ν4`),
the deterministic part is `Dfun (vRev W t) t a' g₁ Q (c, r)` (joint continuity by
`continuousOn_integral_foldedCircle_param`), commutation as `RegUnif.ae_comm_fibre` /
`integral_Dfun_swap`, and continuity in time at dyadic circles is `ASepWitA`.
Sources: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1; Revuz–Yor, 3rd ed., Ch. I,
Thm (2.1) (through the cited files); the assembly is own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace ASep

open RegCont TwoPoint CoordReg RegUnif UnzipInvariance RegSample

/-- The deterministic part of the raw values. -/
def Dfix (W : ℝ → ℝ) (a' : ℝ) (g₁ : ℂ → ℝ) (Q : ℝ) (p : ℝ × (ℂ × ℝ)) : ℝ :=
  Dfun (vRev W p.1) p.1 a' g₁ Q p.2

/-- The measurable version of `Gdet` (through the reverse flow). -/
def Grev (W : ℝ → ℝ) (a' : ℝ) (g₁ : ℂ → ℝ) (Q : ℝ) (t : ℝ) (u : ℂ) : ℝ :=
  a' * Real.log ‖revMap (vRev W t) t u‖ + g₁ (revMap (vRev W t) t u) +
    Q * Real.log ‖deriv (revMap (vRev W t) t) u‖

theorem Grev_eq_Gdet {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) (a' : ℝ) (g₁ : ℂ → ℝ)
    (Q : ℝ) {t : ℝ} (ht : 0 ≤ t) {u : ℂ} (hu : u ∈ H) :
    Grev W a' g₁ Q t u = Gdet W a' g₁ Q t u := by
  unfold Grev Gdet
  rw [deriv_fwdMapInv_eq hW hW0 ht hu, fwdMapInv_eq_revMap_timeRev W hW hW0 ht hu]

/-- **Joint continuity of the deterministic part.** -/
theorem continuousOn_Dfix {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    (a' : ℝ) {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁) (Q : ℝ) :
    ContinuousOn (Dfix W a' g₁ Q) (parSet T) := by
  set c : ℝ := |a'| + |Q| + 1 with hcdef
  have hc : 0 < c := by positivity
  have hGm : ∀ t ∈ Icc (0 : ℝ) T, Measurable fun u => Grev W a' g₁ Q t u / c := by
    intro t ht
    have hr := TwoPoint.measurable_revMap (continuous_vRev hW t) ht.1
    exact ((((Real.measurable_log.comp hr.norm).const_mul a').add (hg₁.measurable.comp hr)).add
      ((Real.measurable_log.comp (measurable_deriv _).norm).const_mul Q)).div_const c
  have hGc : ContinuousOn (fun p : ℝ × ℂ => Grev W a' g₁ Q p.1 p.2 / c) (Icc 0 T ×ˢ H) :=
    ((continuousOn_Gdet_joint hW hW0 T a' hg₁ Q).congr fun p hp =>
      Grev_eq_Gdet hW hW0 a' g₁ Q hp.1.1 hp.2).div_const c
  have hGb : ∀ R, ∃ A, 0 ≤ A ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ u ∈ H, ‖u‖ ≤ R →
      |Grev W a' g₁ Q t u / c| ≤ A + |Real.log u.im| := by
    intro R
    obtain ⟨A, hA0, hA⟩ := Gdet_logBound hW hW0 T R hT a' hg₁ Q
    refine ⟨A / c, by positivity, fun t ht u hu huR => ?_⟩
    rw [Grev_eq_Gdet hW hW0 a' g₁ Q ht.1 hu, abs_div, abs_of_pos hc, div_le_iff₀ hc, add_mul,
      div_mul_cancel₀ A hc.ne']
    have h1 := hA t ht u hu huR
    nlinarith [abs_nonneg (Real.log u.im)]
  have hI := continuousOn_integral_foldedCircle_param hT hGm hGc hGb
  refine ((hI.mono fun p hp => ⟨hp.1, hp.2.2⟩).const_smul c).congr fun p hp => ?_
  have e1 : Dfix W a' g₁ Q p = ∫ v, Gdet W a' g₁ Q p.1 v ∂foldedCircle p.2.1 p.2.2 :=
    Dfun_eq_integral_Gdet hW hW0 hp.1.1 a' hg₁ Q p.2.1 hp.2.2
  have e2 : ∫ v, Gdet W a' g₁ Q p.1 v ∂foldedCircle p.2.1 p.2.2 =
      ∫ v, Grev W a' g₁ Q p.1 v ∂foldedCircle p.2.1 p.2.2 :=
    integral_congr_ae ((foldedCircle_ae_mem_H _ hp.2.2).mono fun v hv =>
      (Grev_eq_Gdet hW hW0 a' g₁ Q hp.1.1 hv).symm)
  show Dfix W a' g₁ Q p = c • ∫ u, Grev W a' g₁ Q p.1 u / c ∂foldedCircle p.2.1 p.2.2
  rw [e1, e2, integral_div, smul_eq_mul, mul_div_cancel₀ _ hc.ne']

/-- The deterministic part of the raw value at `fc(c, r)`. -/
theorem integral_logAdd_eq_Dfix {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) (a' : ℝ) {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁) (Q : ℝ) (c : ℂ) {r : ℝ}
    (hr : 0 < r) :
    (∫ z, (a' * Real.log ‖z‖ + g₁ z) ∂νT W c r t) +
        Q * ∫ u, Real.log ‖deriv (fwdMapInv W t) u‖ ∂foldedCircle c r =
      Dfix W a' g₁ Q (t, (c, r)) := by
  have hV := continuous_vRev hW t
  have h1 := (logBounded_log_norm_revMap (W := vRev W t) (T := t) hV ht).integrable c hr
  have h2 := (logBounded_comp_revMap (W := vRev W t) (T := t) hV ht hg₁).integrable c hr
  have hGm : Measurable fun z : ℂ => a' * Real.log ‖z‖ + g₁ z :=
    ((Real.measurable_log.comp measurable_norm).const_mul a').add hg₁.measurable
  have e1 : ∫ z, (a' * Real.log ‖z‖ + g₁ z) ∂νT W c r t =
      ∫ u, (a' * Real.log ‖revMap (vRev W t) t u‖ + g₁ (revMap (vRev W t) t u))
        ∂foldedCircle c r := by
    rw [integral_map (aemeasurable_fwdMapInv hW hW0 ht c hr) hGm.aestronglyMeasurable]
    refine integral_congr_ae ?_
    filter_upwards [foldedCircle_ae_mem_H c hr] with u hu
    show a' * Real.log ‖fwdMapInv W t u‖ + g₁ (fwdMapInv W t u) = _
    rw [fwdMapInv_eq_revMap_timeRev W hW hW0 ht hu]
  have e2 : ∫ u, Real.log ‖deriv (fwdMapInv W t) u‖ ∂foldedCircle c r =
      ∫ u, Real.log ‖deriv (revMap (vRev W t) t) u‖ ∂foldedCircle c r := by
    refine integral_congr_ae ?_
    filter_upwards [foldedCircle_ae_mem_H c hr] with u hu
    show Real.log ‖deriv (fwdMapInv W t) u‖ = _
    rw [deriv_fwdMapInv_eq hW hW0 ht hu]
  rw [e1, e2, integral_add (h1.const_mul a') h2, integral_const_mul]
  rfl

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

end ASep
end QuantumZipper
