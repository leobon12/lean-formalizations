import QuantumZipper.Proofs.Thm18.RTHmpMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1R2 (Y growth): log growth of the regularized circle averages of the Theorem 1.8 field at
all radii

Continuous-radius form of `R18.RTHmp.circAvgLogGrowth_of_free` (same proof: realization of the
`P_*` sample, wedge decomposition, free-field bound `RTHmp.freeCircLogGrowthStmt_holds` at all
radii, Hu–Miller–Peres, Ann. Probab. 38 (2010), Prop. 2.1): a.s., on bounded sets,
`|evalReg Y (fc(c, ρ))| ≤ C (1 + |log ρ|)` for all `0 < ρ ≤ R`. Own bookkeeping (copy).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace R18
namespace A1R2

open Thm18Asm

/-- **Continuous-radius log growth of the Theorem 1.8 field.** -/
theorem a1r2_ae_evalReg_growth {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (hI : Thm18Inputs γ P B Y) :
    ∀ᵐ ω ∂P, ∀ Rr : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ Hbar, ‖c‖ ≤ Rr → ∀ ρ : ℝ, 0 < ρ → ρ ≤ Rr →
      |evalReg (Y ω) (foldedCircle c ρ)| ≤ C * (1 + |Real.log ρ|) := by
  have hF : RTHmp.FreeCircLogGrowthStmt := RTHmp.freeCircLogGrowthStmt_holds
  have hP := isPStarSample_of_setting hS
  obtain ⟨hκ, hκ4, -⟩ := id hP
  obtain ⟨Ω₂, _, Q, _, X', A, B'', hX, hA, hInd, hB, hIB, hae⟩ :=
    WedgeUnzip.pStarRealizeStmt_holds (γ ^ 2) P Y B hP
  obtain ⟨Ω₃, _, Q₃, _, X'', G, hX'', -, -, hdec⟩ :=
    WedgeUnzip.WDec.wedgeDecompStmt_holds (γ ^ 2) hκ hκ4 (P.prod Q) X' A B'' hX hA hInd hB hIB
  have hγ' : 0 < Real.sqrt (γ ^ 2) := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt (γ ^ 2) < 2 := F2.sqrt_lt_two_of' hκ hκ4
  have hα := F2.alpha_lt_Qc' hγ' hγ2
  have hspec := Wire2.ae_wedge_canonical_spec hγ' hγ2 hα hX hA hInd
  have lift2 : ∀ {p : Ω × Ω₂ → Prop}, (∀ᵐ ω ∂(P.prod Q), p ω) →
      ∀ᵐ ω ∂((P.prod Q).prod Q₃), p ω.1 := fun h =>
    ae_of_ae_map measurable_fst.aemeasurable (by rw [measurePreserving_fst.map_eq]; exact h)
  have lift1 : ∀ {p : Ω → Prop}, (∀ᵐ ω ∂P, p ω) → ∀ᵐ ω ∂((P.prod Q).prod Q₃), p ω.1.1 :=
    fun h => lift2 (ae_of_ae_map measurable_fst.aemeasurable
      (by rw [measurePreserving_fst.map_eq]; exact h))
  refine WedgeUnzip.ae_of_ae_prod_fst (Q := Q) (WedgeUnzip.ae_of_ae_prod_fst (Q := Q₃) ?_)
  filter_upwards [lift1 hI.1, lift2 hae, lift2 hspec, hdec, hF _ X'' hX'',
    RegSample.ae_isRegularSample hX''] with ω hYg hR hsp hD hFX hXreg
  intro Rr
  obtain ⟨havg, -⟩ := hR
  obtain ⟨FY, hFY⟩ := hYg.1.1
  obtain ⟨hGc, -, hZfc⟩ := hD
  obtain ⟨FX, hFXw⟩ := hXreg
  set s := Real.sqrt (γ ^ 2) with hs
  set α := s - 2 / s with hαdef
  set Z := F2.zU s X' A ω.1 with hZ
  set b := scaleParam s Z with hbdef
  have hb : 0 < b := hsp.1
  have hW1 := hFXw.add_ofFun_log' α 0
  have e1 : (X'' ω + ofFun fun v => α * -Real.log ‖v - ((0 : ℝ) : ℂ)‖) =
      X'' ω + F2.logSingField (γ ^ 2) := by
    simp [F2.logSingField, hαdef, hs]
  rw [e1] at hW1
  have hW2 := hW1.add_ofFun' hGc.continuousOn
  have hZw := RTHmp.isRegularWith_of_fc_eq hW2 hZfc
  set R₁ := b * (|Rr| + 2) with hR₁
  have hR₁b : b ≤ R₁ := by
    have : (1 : ℝ) ≤ |Rr| + 2 := by linarith [abs_nonneg Rr]
    nlinarith
  obtain ⟨C₁, hC₁, hC₁b⟩ := hFX R₁
  obtain ⟨MG, hMG⟩ := (isCompact_closedBall (0 : ℂ) (2 * R₁)).exists_bound_of_continuousOn
    hGc.continuousOn
  have hMG0 : 0 ≤ MG := (norm_nonneg _).trans (hMG 0 (mem_closedBall_self (by positivity)))
  set L := |Real.log b| with hL
  set A0 := C₁ * (1 + L) + |α| * (L + |Real.log R₁|) + MG + |Qc s * Real.log b| with hA0
  have hA0n : 0 ≤ A0 := by positivity
  refine ⟨A0 + (C₁ + |α|), by positivity, fun d hdH hdR ρ₀ hρ₀ hρ₀R => ?_⟩
  set ρ := b * ρ₀ with hρdef
  have hρ : 0 < ρ := mul_pos hb hρ₀
  have hcH : (b : ℂ) * d ∈ Hbar := by
    show 0 ≤ ((b : ℂ) * d).im
    rw [Complex.im_ofReal_mul]
    exact mul_nonneg hb.le hdH
  have hval : evalReg (Y ω.1.1) (foldedCircle d ρ₀) =
      (FX ((b : ℂ) * d, ρ) + α * (CircleCont.circPot ρ ((b : ℂ) * d) ((0 : ℝ) : ℂ) / 2) +
        ∫ v, G ω v ∂foldedCircle ((b : ℂ) * d) ρ) + (Qc s * Real.log b + 0) := by
    rw [F1.evalReg_fc_of_avgReg_rescale ⟨_, hZw⟩ (Qc s) hb 0 ?_ hdH hρ₀,
      hZw.evalReg_fc_of_mem hcH hρ]
    rw [havg]
    congr 1
    funext μ
    simp [addConst]
    rfl
  have hnd : ‖d‖ ≤ |Rr| + 2 := by linarith [le_abs_self Rr]
  have hnc : ‖(b : ℂ) * d‖ ≤ R₁ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]
    exact mul_le_mul_of_nonneg_left hnd hb.le
  have hρR : ρ ≤ R₁ := by
    have : ρ₀ ≤ |Rr| + 2 := by linarith [le_abs_self Rr]
    exact mul_le_mul_of_nonneg_left this hb.le
  have hmax : max ρ ‖(b : ℂ) * d‖ ≤ R₁ := max_le hρR hnc
  have hlogρ : |Real.log ρ| ≤ L + |Real.log ρ₀| := by
    rw [hρdef, Real.log_mul hb.ne' hρ₀.ne']
    exact abs_add_le _ _
  have hbX : |FX ((b : ℂ) * d, ρ)| ≤ C₁ * (1 + |Real.log ρ|) := by
    rw [← hFXw.evalReg_fc_of_mem hcH hρ]
    exact hC₁b _ hcH hnc ρ hρ hρR
  have hbP := RTHmp.abs_circPot_zero_le hρ hmax
  have hbG : |∫ v, G ω v ∂foldedCircle ((b : ℂ) * d) ρ| ≤ MG :=
    RTHmp.abs_integral_fc_le hMG hcH hρ.le (by linarith)
  rw [hval]
  have hl0 : (0 : ℝ) ≤ |Real.log ρ₀| := abs_nonneg _
  have hsum : |FX ((b : ℂ) * d, ρ) + α * (CircleCont.circPot ρ ((b : ℂ) * d) ((0 : ℝ) : ℂ) / 2) +
        ∫ v, G ω v ∂foldedCircle ((b : ℂ) * d) ρ + (Qc s * Real.log b + 0)| ≤
      C₁ * (1 + (L + |Real.log ρ₀|)) + |α| * ((L + |Real.log ρ₀|) + |Real.log R₁|) + MG +
        |Qc s * Real.log b| := by
    have t1 := abs_add_le (FX ((b : ℂ) * d, ρ) +
      α * (CircleCont.circPot ρ ((b : ℂ) * d) ((0 : ℝ) : ℂ) / 2) +
        ∫ v, G ω v ∂foldedCircle ((b : ℂ) * d) ρ) (Qc s * Real.log b + 0)
    have t2 := abs_add_le (FX ((b : ℂ) * d, ρ) +
      α * (CircleCont.circPot ρ ((b : ℂ) * d) ((0 : ℝ) : ℂ) / 2))
        (∫ v, G ω v ∂foldedCircle ((b : ℂ) * d) ρ)
    have t3 := abs_add_le (FX ((b : ℂ) * d, ρ))
      (α * (CircleCont.circPot ρ ((b : ℂ) * d) ((0 : ℝ) : ℂ) / 2))
    rw [abs_mul] at t3
    have t4 : |Qc s * Real.log b + 0| = |Qc s * Real.log b| := by rw [add_zero]
    have u1 : C₁ * (1 + |Real.log ρ|) ≤ C₁ * (1 + (L + |Real.log ρ₀|)) := by gcongr
    have u2 : |α| * |CircleCont.circPot ρ ((b : ℂ) * d) ((0 : ℝ) : ℂ) / 2| ≤
        |α| * ((L + |Real.log ρ₀|) + |Real.log R₁|) := by gcongr; linarith
    linarith
  refine hsum.trans ?_
  have hαn := abs_nonneg α
  nlinarith

end A1R2
end R18
end QuantumZipper
