import QuantumZipper.Proofs.Thm18.G3Pl4Cpl
import QuantumZipper.Proofs.LQG.WedgeRestriction

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T, (G-b), part (b): the coupling with a normalized free field

Strengthening of `g3pl4_wedge_fcAgree`: the free field `V` of the wedge decomposition is
normalized, `V(S) = 0` a.s. on the unit semicircle `S` (the radial part of the wedge starts at
`A_0 = 0` and the lateral part has mean zero on `S`; Sheffield, arXiv:1012.4797, §1.6). Hence
`V + (γ − 2/γ)(−log|·|)` has the full law of `h_C = normField + (−γ log|·|)`
(`fieldLawFull_eq_of_normalized`), and it agrees with the unscaled wedge on every folded circle in
the unit disc, on the same probability space. Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace R18

open Thm18Asm Prop16Area.G WedgeUnzip.WDec

/-- **The wedge near the root is a normalized free field plus the log singularity.** -/
theorem g3pl4_wedge_fcAgree_norm {γ : ℝ} (hγ : 0 < γ) {Ω' : Type} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ}
    (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P')
    (hI : IndepFun X (fun ω t => A t ω) P') :
    ∃ V : Ω' → FieldSample, IsFreeGFFModConstH V P' ∧
      (∀ᵐ ω ∂P', V ω (foldedCircle 0 1) = 0) ∧
      ∀ᵐ ω ∂P', FcAgree (ball (0 : ℂ) 1) (F2.zU γ X A ω) (V ω + F2.logSingField (γ ^ 2)) := by
  have hs : Real.sqrt (γ ^ 2) = γ := Real.sqrt_sq hγ.le
  have hA' : IsWedgeProcess (Real.sqrt (γ ^ 2) - 2 / Real.sqrt (γ ^ 2)) (Qc (Real.sqrt (γ ^ 2)))
      A P' := by rwa [hs]
  obtain ⟨B, B', hBm, hB'm, -, hAe⟩ := id hA'
  obtain ⟨Bt, hBtm, hBtc, hBtB⟩ := WedgeRes.exists_good_version hBm
  have hAB := wedge_hAB hAe
  have hBtpre : IsPreBrownianReal Bt P' :=
    hBm.toIsPreBrownianReal.congr fun s => hBtB.mono fun ω h => (h s).symm
  have hVfree := isFree_PhiF_of_indep hX hBtm hBtpre (indep_lat_Bt hI hAB hBtB)
  have hmain := ae_pathwise (κ := γ ^ 2) hX hA' hAe hBm hBtc hBtB
  obtain ⟨G, hG⟩ := WedgeTK.exists_isRegVersion hX
  have hnorm : ∀ᵐ u ∂foldedCircle 0 1, ‖u‖ = 1 := by
    simpa using WedgeTK.fc_ae_norm (r := 1) one_pos
  refine ⟨fun ω => PhiF ((latW (X ω), nPath (X ω)), pathOf Bt ω), hVfree, ?_, ?_⟩
  · filter_upwards [hmain, hG.ae_good, WedgeTK.ae_evalReg_fc hG 0 one_pos,
      hBm.eval_zero_ae_eq_zero] with ω hω hgood hev hB0
    obtain ⟨-, hG0, hfc⟩ := hω
    have e := hfc 0 (by simp [Hbar]) 1 one_pos
    rw [hs] at e
    simp only [Pi.add_apply] at e
    -- the three terms at `S`
    have hlog : F2.logSingField (γ ^ 2) (foldedCircle 0 1) = 0 := by
      unfold F2.logSingField ofFun
      refine integral_eq_zero_of_ae (hnorm.mono fun u hu => ?_)
      simp [hu]
    have hcorr : ofFun (corrField (γ - 2 / γ) (Qc γ) (fun t => A t ω) (nPath (X ω)))
        (foldedCircle 0 1) = 0 := by
      unfold ofFun
      refine integral_eq_zero_of_ae (hnorm.mono fun u hu => ?_)
      have := hG0 u hu.le
      rw [hs] at this
      exact this
    have hrad : radAvgReg (X ω) 1 = X ω (foldedCircle 0 1) := by
      rw [hgood.radAvgReg_eq one_pos]
      have h := hgood.2 0 0
      have e0 : WedgeTK.dyRad 0 0 = 1 := by simp [WedgeTK.dyRad]
      rw [e0] at h
      exact h.symm
    have hA0 : A 0 ω = 0 := by
      have h := hAB ω 0
      simp only [NNReal.coe_zero, mul_zero, add_zero] at h
      rw [h, hB0, mul_zero]
    have hzU : F2.zU γ X A ω (foldedCircle 0 1) = 0 := by
      simp only [F2.zU, wedgeField, lateralPart]
      have i1 : ∫ z, radAvgReg (X ω) ‖z‖ ∂foldedCircle 0 1 = radAvgReg (X ω) 1 := by
        rw [integral_congr_ae (hnorm.mono fun u hu => by rw [hu])]
        simp
      have i2 : ∫ z, (Qc γ * -Real.log ‖z‖ + A (-Real.log ‖z‖) ω) ∂foldedCircle 0 1 = 0 := by
        refine integral_eq_zero_of_ae (hnorm.mono fun u hu => ?_)
        simp [hu, hA0]
      rw [i1, i2, hev, hrad]
      ring
    rw [hlog, hcorr, hzU] at e
    simpa using e.symm
  · filter_upwards [hmain] with ω hω
    obtain ⟨-, hG0, hfc⟩ := hω
    intro d hd r hr hsub
    have e := hfc d hd r hr
    rw [hs] at e
    rw [e]
    simp only [Pi.add_apply]
    have hG' : ofFun (corrField (γ - 2 / γ) (Qc γ) (fun t => A t ω) (nPath (X ω)))
        (foldedCircle d r) = 0 := by
      unfold ofFun
      refine integral_eq_zero_of_ae ?_
      filter_upwards [ae_fc_mem_ball_inter hd hr] with u hu
      have hu1 := hsub hu
      rw [mem_ball, dist_zero_right] at hu1
      have := hG0 u hu1.le
      rw [hs] at this
      exact this
    rw [hG', add_zero]

end R18
end QuantumZipper
