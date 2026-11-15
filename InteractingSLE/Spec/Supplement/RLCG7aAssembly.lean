/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowLocalityGenTop
import InteractingSLE.Spec.Restart.FlowLocalityGenKernel
import InteractingSLE.Spec.Supplement.RLCRealCompletionG7a

/-!
# Corollary G7a and the source-form G3 from flow locality with a general agreement set

Packet PROVE-G7A-LOC. `RLC.G7aChartStatement` (PROVE-G3RESTART's named input; Corollary G7a in the chart,
supplement p. 499: one Cameron–Martin density, both fresh curves stopped on exiting one buffer `V` whose real
points lie in the agreement set `O`) from the general explicit-shift (L1)
`Restart.FlowLocalityGen.FlowLineStopIdentGStatement`: the shift is constructed as in
`RLC.g3SourceStatement_of_CMIV` — the cutoff `F` of `exists_cmCut` around the compact set `closure V`, the
pairing `Λ = F.pair ∘ H₀`, the density `Z = e^{−Λ} / E[e^{−Λ}]` and the field `H₀ + (q − F.f)` — and the
per-curve agreement is `Restart.FlowLocalityGen.ae_stoppedAgree_of_G` (no interval is needed: a curve may swallow
real points outside `O` into a retained pocket).

* **`g7aChartStatement_of_G`**, `g3SourceStatement_of_G` (the general (L1) also gives the source-form G3);
* **`g7aChartStatement_of_kernel`**, `g3SourceStatement_of_kernel`: from the per-stop identification with retained
  pockets (`Restart.FlowLocalityGen.ShiftKernelGenStatement`) and PROVE-L1-CMIC's Gaussian hull-limit input;
* **`g7aChartStatement_of_meanIdent`**, `g3SourceStatement_of_meanIdent`: the per-stop identification proved from the
  deterministic pocket mean identity (`Restart.FlowLocalityGen.PocketMeanIdentStatement`).

R43/R48: Theorems 1.2–1.3 are hypotheses; these results serve Theorem 1.5 only.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
namespace InteractingSLE.RLC
open Restart.FlowStopIdentCM Restart.FlowStopIdentCMI Restart.FlowLocalityGen
open QuantumZipper (H)
open SupercriticalConformalCovariance.GM24 (smoothDist)

/-- **Corollary G7a from the general explicit-shift (L1)**, the WFS kernel target for `0 < κ < 4` and Theorems 1.2
(param) / 1.3. -/
theorem g7aChartStatement_of_G (hCM : FlowLineStopIdentGStatement.{0})
    (hT : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ThroughKernelStatement.{0, 0} κ)
    (h12p : Exist.Staged.Theorem12ParamStatement.{0}) (h13 : Exist.Theorem13Statement.{0}) :
    G7aChartStatement.{0} := by
  classical
  intro κ hκ hκ4 θ₁ θ₂ y₂ y₁ ε _hθ _hy hε _hε2 b bR J Ĵ hb hbR _gL₂ _gR₂ _gL₁ _gR₁ _hĴ₂ _hĴ₁ O hO hO₂ _hO₁ hbO
    _hJO V hV hVb hVO S _ Q₀ _ H₀ hH Γ₁ Γ₂ U₁ U₂ h₁ h₂
  have hext : ∀ κ : ℝ, 0 < κ → κ < 4 → Restart.StoppedExtendWF.StoppedHullExtendGKStatement.{0} κ :=
    fun κ hκ hκ4 => WFS.stoppedHullExtendGKStatement_of_through hκ (hT κ hκ hκ4)
  have hy₀ : y₂ ∈ O := hO₂ ⟨by linarith, by linarith⟩
  -- the harmonic extension of `bR − b`
  obtain ⟨u, hu, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  obtain ⟨uR, huR, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hbR
  have hq : IsBoundedHarmonicExtension (fun x => bR x - b x) ((J ∪ Ĵ : Finset ℝ) : Set ℝ)
      fun z => uR z - u z :=
    isBoundedHarmonicExtension_mono' (isBoundedHarmonicExtension_sub huR hu)
      (by simp only [Finset.coe_union]; exact (union_comm _ _).subset)
  -- the cutoff around the closed buffer
  obtain ⟨N, F, hNo, hKN, hNO, hFq, hFΔ⟩ := exists_cmCut hb hbR hO hbO hq hy₀ hVb.isCompact_closure hVO
  -- the pairing and the density
  have huc : ContinuousOn u H := fun z hz => ((hu.1 z hz).1.continuousAt).continuousWithinAt
  obtain ⟨C, hC⟩ := hu.2.1
  have hΛ := F.ae_tendsto_pair huc hC (hH.2 u hu)
  have hΛm : Measurable fun x => F.pair (H₀ x) := F.measurable_pair.comp hH.1
  have hint := integrable_exp_neg_of_isGFF hb hH F F.abs_testSeq_le hΛm hΛ
  set E : ℝ := ∫ x, Real.exp (-F.pair (H₀ x)) ∂Q₀ with hE
  have hE0 : 0 < E := integral_exp_pos hint
  set k : ℝ := E⁻¹ with hk
  have hk0 : 0 < k := inv_pos.2 hE0
  set Z : S → ℝ := fun x => k * Real.exp (-F.pair (H₀ x)) with hZ
  have hZint : Integrable Z Q₀ := hint.const_mul k
  have hZ1 : ∫ x, Z x ∂Q₀ = 1 := by
    rw [hZ, integral_const_mul, ← hE, hk, inv_mul_cancel₀ hE0.ne']
  have hprob : IsProbabilityMeasure (Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-F.pair (H₀ x)))) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hZint (ae_of_all _ fun x => (mul_pos hk0 (Real.exp_pos _)).le)]
    show ENNReal.ofReal (∫ x, Z x ∂Q₀) = 1
    rw [hZ1, ENNReal.ofReal_one]
  have hĤ := isGFFWithBoundaryData_shift hb F hq hH F.abs_testSeq_le F.tendsto_testSeq hΛm hΛ hint hk0 hprob
  obtain ⟨α₁, ζ₁, hα₁⟩ := exists_isFlowLine_of_param h12p h13 hκ hbR y₁ θ₁ hĤ
  obtain ⟨α₂, ζ₂, hα₂⟩ := exists_isFlowLine_of_param h12p h13 hκ hbR y₂ θ₂ hĤ
  refine ⟨Z, _, α₁, α₂, ζ₁, ζ₂, hZint.aemeasurable, ae_of_all _ fun x => mul_pos hk0 (Real.exp_pos _), hZ1,
    hĤ, hα₁, hα₂, ?_⟩
  filter_upwards [ae_stoppedAgree_of_G hCM hext h12p h13 hκ hκ4 hb hbR hO hbO hNo hNO hV hVb hKN
      hq hFq hFΔ y₁ θ₁ hH F.abs_testSeq_le F.tendsto_testSeq hΛm hΛ hk0 hprob h₁ hα₁,
    ae_stoppedAgree_of_G hCM hext h12p h13 hκ hκ4 hb hbR hO hbO hNo hNO hV hVb hKN
      hq hFq hFΔ y₂ θ₂ hH F.abs_testSeq_le F.tendsto_testSeq hΛm hΛ hk0 hprob h₂ hα₂] with x hx₁ hx₂
  exact ⟨hx₁, hx₂⟩

/-- **The source-form G3 from the general explicit-shift (L1)** (through its interval form). -/
theorem g3SourceStatement_of_G (hCM : FlowLineStopIdentGStatement.{0})
    (hT : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ThroughKernelStatement.{0, 0} κ)
    (h12p : Exist.Staged.Theorem12ParamStatement.{0}) (h13 : Exist.Theorem13Statement.{0}) :
    G3SourceStatement.{0} :=
  g3SourceStatement_of_CMIV (flowLineStopIdentCMIVStatement_of_G hCM) hT h12p h13

/-- **Corollary G7a** from the per-stop identification with retained pockets, PROVE-L1-CMIC's Gaussian hull-limit
input, the WFS kernel target and Theorems 1.2 (param) / 1.3. -/
theorem g7aChartStatement_of_kernel (hK : ShiftKernelGenStatement.{0})
    (hlimit : CMIXHullLocalityLimitStatement.{0})
    (hT : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ThroughKernelStatement.{0, 0} κ)
    (h12p : Exist.Staged.Theorem12ParamStatement.{0}) (h13 : Exist.Theorem13Statement.{0}) :
    G7aChartStatement.{0} :=
  g7aChartStatement_of_G (flowLineStopIdentGStatement_of_kernel hK hlimit) hT h12p h13

/-- **The source-form G3** from the same inputs. -/
theorem g3SourceStatement_of_kernel (hK : ShiftKernelGenStatement.{0})
    (hlimit : CMIXHullLocalityLimitStatement.{0})
    (hT : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ThroughKernelStatement.{0, 0} κ)
    (h12p : Exist.Staged.Theorem12ParamStatement.{0}) (h13 : Exist.Theorem13Statement.{0}) :
    G3SourceStatement.{0} :=
  g3SourceStatement_of_G (flowLineStopIdentGStatement_of_kernel hK hlimit) hT h12p h13

/-- **Corollary G7a** from the deterministic pocket mean identity, PROVE-L1-CMIC's Gaussian hull-limit input, the WFS
kernel target and Theorems 1.2 (param) / 1.3. -/
theorem g7aChartStatement_of_meanIdent (hM : PocketMeanIdentStatement)
    (hlimit : CMIXHullLocalityLimitStatement.{0})
    (hT : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ThroughKernelStatement.{0, 0} κ)
    (h12p : Exist.Staged.Theorem12ParamStatement.{0}) (h13 : Exist.Theorem13Statement.{0}) :
    G7aChartStatement.{0} :=
  g7aChartStatement_of_kernel (shiftKernelGenStatement_of_meanIdent hM) hlimit hT h12p h13

/-- **The source-form G3** from the same inputs. -/
theorem g3SourceStatement_of_meanIdent (hM : PocketMeanIdentStatement)
    (hlimit : CMIXHullLocalityLimitStatement.{0})
    (hT : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ThroughKernelStatement.{0, 0} κ)
    (h12p : Exist.Staged.Theorem12ParamStatement.{0}) (h13 : Exist.Theorem13Statement.{0}) :
    G3SourceStatement.{0} :=
  g3SourceStatement_of_kernel (shiftKernelGenStatement_of_meanIdent hM) hlimit hT h12p h13

end InteractingSLE.RLC
