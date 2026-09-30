import QuantumZipper.Proofs.Thm18.A1RS2Prof
import QuantumZipper.Proofs.GFF.CoordRegLog

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS2 (11): continuity of the logarithmic profile against the smeared-loop family

**`continuousOn_integral_log_smearFam`**: for a good driver, `(p, ρ) ↦ ∫ log ‖w‖ dν_{p,ρ}` is
continuous on `smearU × [0, 1]`, including `ρ = 0`. This is the logarithmic part (the
`α₀(−log|·|)` of `Z = X + α₀(−log|·|) + G`) of the continuity of `ρ ↦ evalReg Z ν_{p,ρ}` at `0⁺`.

Truncation `log max(ε, ‖w‖)` (continuous: `continuousOn_integral_smearFam`) with the error
`∫ log⁺(ε/‖w‖) dν ≤ 2 C ε^α / α` uniform over a parameter box, from the uniform Frostman bound
`isFrostman_a1rfNu_unif` and the layer-cake bound `FrostmanReg.integral_logNeg_le_frostman`.
Own elementary argument.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm

/-- Probability, support and Frostman facts for the members of the family over a box. -/
theorem smearFam_box_facts {W : ℝ → ℝ} (hG : G1zDrvGood W) (left : Bool) {t₀ T : ℝ}
    (ht₀ : 0 < t₀) (hT : t₀ ≤ T) (R : ℕ) :
    ∃ (α CF Rs : ℝ), 0 < α ∧ ∀ p ∈ smearBox t₀ T R, ∀ ρ ∈ Icc (0 : ℝ) 1,
      IsProbabilityMeasure (smearFam W left p ρ) ∧
      smearFam W left p ρ (closedBall (0 : ℂ) Rs ∩ Hbar)ᶜ = 0 ∧
      IsFrostman (smearFam W left p ρ) α CF := by
  have hT0 : 0 < T := ht₀.trans_le hT
  obtain ⟨α, CF, hα, -, -, hFr⟩ := isFrostman_a1rfNu_unif hG left hT0 R
  obtain ⟨R₁, Cm, hR₁, -, hbox⟩ := a1rMu_box_facts hG left hT0 R
  obtain ⟨Ci, hCi, hinv⟩ := norm_fwdMapInv_le_unif hG.1 hG.2.1 hT0
  refine ⟨α, CF, R₁ + 1 + Ci, hα, fun p hp ρ hρ => ?_⟩
  have hpt : p 0 ∈ Ioc (0 : ℝ) T := ⟨ht₀.trans_le hp.1.1, hp.1.2⟩
  obtain ⟨hP, hsp, -⟩ := hbox (p 0) hpt (parD p) hp.2.1 (p 3) hp.2.2.1 hp.2.2.2
  have hFm : Measurable fun q : ℂ × ℝ => fwdMapInv W (p 0) (foldH (circleMap q.1 ρ q.2)) :=
    A1RF.measurable_smear (RTBeur.measurable_fwdMapInv_rt hG.1 hG.2.1 hpt.1.le) ρ
  have hcl : MeasurableSet (closedBall (0 : ℂ) (R₁ + 1 + Ci) ∩ Hbar) :=
    isClosed_closedBall.measurableSet.inter isClosed_Hbar.measurableSet
  have hs : ∀ᵐ z ∂smearFam W left p ρ, z ∈ closedBall (0 : ℂ) (R₁ + 1 + Ci) ∩ Hbar := by
    unfold smearFam a1rfNu
    refine (ae_map_iff hFm.aemeasurable hcl).2 ?_
    have hfst := Measure.quasiMeasurePreserving_fst (μ := a1rMu W (p 0) left (parD p) (p 3))
      (ν := E6.XAreaPC.angMeas) |>.ae hsp
    filter_upwards [hfst] with q hq
    refine ⟨?_, F1.fwdMapInv_mem_Hbar W _ _⟩
    rw [mem_closedBall, dist_zero_right]
    refine (hinv (p 0) hpt _).trans ?_
    rw [TwoPoint.norm_foldH]
    have := TwoPoint.norm_circleMap_le_add q.1 hρ.1 q.2
    linarith [hq.2, hρ.2]
  exact ⟨(Measure.isProbabilityMeasure_map_iff hFm.aemeasurable).2 inferInstance, ae_iff.1 hs,
    hFr (p 0) hpt (parD p) hp.2.1 (p 3) hp.2.2.1 hp.2.2.2 ρ hρ⟩

/-- The truncation error of the logarithm against a Frostman probability measure. -/
theorem abs_integral_log_sub_trunc_le {ν : Measure ℂ} [IsProbabilityMeasure ν] {Rs α CF : ℝ}
    (hsupp : ν (closedBall (0 : ℂ) Rs ∩ Hbar)ᶜ = 0) (hF : IsFrostman ν α CF) (hα : 0 < α)
    {ε : ℝ} (hε : 0 < ε) :
    |(∫ w, Real.log ‖w‖ ∂ν) - ∫ w, Real.log (max ε ‖w‖) ∂ν| ≤ 2 * (CF * ε ^ α / α) := by
  have hint := CoordReg.integrable_log_norm_frostman hsupp hF hα
  have hmem : ∀ᵐ w ∂ν, w ∈ closedBall (0 : ℂ) Rs ∩ Hbar := ae_iff.2 hsupp
  have hcm : Continuous fun w : ℂ => Real.log (max ε ‖w‖) :=
    Continuous.log (continuous_const.max continuous_norm) fun w =>
      (hε.trans_le (le_max_left _ _)).ne'
  have hint2 : Integrable (fun w : ℂ => Real.log (max ε ‖w‖)) ν := by
    refine Integrable.of_bound (C := |Real.log ε| + |Real.log (max ε Rs)|)
      hcm.aestronglyMeasurable ?_
    filter_upwards [hmem] with w hw
    have hwR : ‖w‖ ≤ Rs := by simpa using hw.1
    have h1 : Real.log ε ≤ Real.log (max ε ‖w‖) := Real.log_le_log hε (le_max_left _ _)
    have h2 : Real.log (max ε ‖w‖) ≤ Real.log (max ε Rs) :=
      Real.log_le_log (hε.trans_le (le_max_left _ _)) (max_le_max le_rfl hwR)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [neg_abs_le (Real.log ε), le_abs_self (Real.log (max ε Rs)),
      abs_nonneg (Real.log ε), abs_nonneg (Real.log (max ε Rs))]
  have hdiff : (∫ w, Real.log (max ε ‖w‖) ∂ν) - ∫ w, Real.log ‖w‖ ∂ν =
      ∫ w, (ENNReal.ofReal (-Real.log (‖w - 0‖ / ε))).toReal ∂ν := by
    rw [← integral_sub hint2 hint]
    refine integral_congr_ae ?_
    filter_upwards [FrostmanReg.ae_ne_frostman hF hα 0] with w hw
    have hw0 : 0 < ‖w‖ := norm_pos_iff.2 hw
    rw [FrostmanReg.log_max_sub_log_frostman hε hw0, sub_zero, ENNReal.toReal_ofReal', max_comm]
  have hnn : 0 ≤ ∫ w, (ENNReal.ofReal (-Real.log (‖w - 0‖ / ε))).toReal ∂ν :=
    integral_nonneg fun _ => ENNReal.toReal_nonneg
  have hle := FrostmanReg.integral_logNeg_le_frostman hF hα 0 hε
  rw [integral_const_mul] at hle
  rw [abs_sub_comm, abs_of_nonneg (by rw [hdiff]; exact hnn), hdiff]
  linarith

/-- **Continuity of the logarithmic profile against the smeared-loop family.** -/
theorem continuousOn_integral_log_smearFam {W : ℝ → ℝ} (hG : G1zDrvGood W) (left : Bool) :
    ContinuousOn (fun x : (Fin 4 → ℝ) × ℝ => ∫ w, Real.log ‖w‖ ∂(smearFam W left x.1 x.2))
      (smearU ×ˢ Icc 0 1) := by
  intro x₀ hx₀
  have hx₀D := hx₀
  obtain ⟨⟨ht₀, hs₀⟩, hρ₀⟩ := hx₀
  have ht₀' : 0 < x₀.1 0 := ht₀
  have hs₀' : 0 < x₀.1 3 := hs₀
  set D : Set ((Fin 4 → ℝ) × ℝ) := smearU ×ˢ Icc 0 1 with hD
  obtain ⟨R, hR⟩ := exists_nat_ge (‖parD x₀.1‖ + 1 + |Real.log (x₀.1 3 / 2)| + 2 * x₀.1 3)
  obtain ⟨α, CF, Rs, hα, hfacts⟩ := smearFam_box_facts hG left (t₀ := x₀.1 0 / 2)
    (T := 2 * x₀.1 0) (by positivity) (by linarith) R
  have c0 : Continuous fun x : (Fin 4 → ℝ) × ℝ => x.1 0 := (continuous_apply 0).comp continuous_fst
  have c3 : Continuous fun x : (Fin 4 → ℝ) × ℝ => x.1 3 := (continuous_apply 3).comp continuous_fst
  have cd : Continuous fun x : (Fin 4 → ℝ) × ℝ => ‖parD x.1‖ :=
    continuous_norm.comp (continuous_parD.comp continuous_fst)
  set N : Set ((Fin 4 → ℝ) × ℝ) := {x | x.1 0 ∈ Ioo (x₀.1 0 / 2) (2 * x₀.1 0) ∧
    ‖parD x.1‖ < ‖parD x₀.1‖ + 1 ∧ x.1 3 ∈ Ioo (x₀.1 3 / 2) (2 * x₀.1 3)} with hN
  have hNo : IsOpen N :=
    (isOpen_Ioo.preimage c0).inter ((isOpen_lt cd continuous_const).inter (isOpen_Ioo.preimage c3))
  have hx₀N : x₀ ∈ N := ⟨⟨by linarith, by linarith⟩, by linarith, ⟨by linarith, by linarith⟩⟩
  have hNbox : ∀ x ∈ N, x.1 ∈ smearBox (x₀.1 0 / 2) (2 * x₀.1 0) R := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := hx
    refine ⟨⟨h1.1.le, h1.2.le⟩, by linarith [abs_nonneg (Real.log (x₀.1 3 / 2))], ?_, ?_⟩
    · have hle : -(R : ℝ) ≤ Real.log (x₀.1 3 / 2) := by
        linarith [neg_abs_le (Real.log (x₀.1 3 / 2)), norm_nonneg (parD x₀.1)]
      calc Real.exp (-(R : ℝ)) ≤ Real.exp (Real.log (x₀.1 3 / 2)) := Real.exp_le_exp.2 hle
        _ = x₀.1 3 / 2 := Real.exp_log (by positivity)
        _ ≤ x.1 3 := h3.1.le
    · have := Real.add_one_le_exp (R : ℝ)
      linarith [h3.2, norm_nonneg (parD x₀.1), abs_nonneg (Real.log (x₀.1 3 / 2))]
  set S : Set ((Fin 4 → ℝ) × ℝ) := D ∩ N with hS
  set I : (Fin 4 → ℝ) × ℝ → ℝ := fun x => ∫ w, Real.log ‖w‖ ∂(smearFam W left x.1 x.2) with hI
  set In : ℕ → (Fin 4 → ℝ) × ℝ → ℝ := fun n x =>
    ∫ w, Real.log (max (1 / ((n : ℝ) + 1)) ‖w‖) ∂(smearFam W left x.1 x.2) with hIn
  have hInc : ∀ n : ℕ, ContinuousOn (In n) S := by
    intro n
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hcm : Continuous fun w : ℂ => Real.log (max (1 / ((n : ℝ) + 1)) ‖w‖) :=
      Continuous.log (continuous_const.max continuous_norm) fun w =>
        (hε.trans_le (le_max_left _ _)).ne'
    exact (continuousOn_integral_smearFam hG left hcm.continuousOn hcm.measurable).mono
      fun x hx => ⟨hx.1.1, show (0 : ℝ) ≤ x.2 from hx.1.2.1⟩
  have hbd : Tendsto (fun n : ℕ => 2 * (CF * (1 / ((n : ℝ) + 1)) ^ α / α)) atTop (𝓝 0) := by
    have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat).rpow_const (p := α) (Or.inr hα.le)
    rw [Real.zero_rpow hα.ne'] at h1
    have h2 := ((h1.const_mul CF).div_const α).const_mul 2
    simpa using h2
  have hunif : TendstoUniformlyOn In I atTop S := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hbd.eventually (gt_mem_nhds hε)] with n hn x hx
    obtain ⟨hP, hsupp, hF⟩ := hfacts x.1 (hNbox x hx.2) x.2 hx.1.2
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (abs_integral_log_sub_trunc_le hsupp hF hα (by positivity)) hn
  have hIc : ContinuousOn I S :=
    hunif.continuousOn (Eventually.frequently (Eventually.of_forall hInc))
  exact (hIc x₀ ⟨hx₀D, hx₀N⟩).mono_of_mem_nhdsWithin
    (inter_mem_nhdsWithin D (hNo.mem_nhds hx₀N))

end A1RS
end R18
end QuantumZipper
