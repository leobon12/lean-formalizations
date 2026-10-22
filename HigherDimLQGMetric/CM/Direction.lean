import HigherDimLQGMetric.CM.Basic
import LQGMetric.Field.MarkovZB
import QuantumZipper.Proofs.LQG.PalmNorm
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Gaussian Hilbert-space direction for Cameron–Martin shifts

We represent finite linear combinations of mean-zero pairings in `L²` and extend the bounded
shift functional through their closed span.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace ENNReal NNReal
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ}

/-- Integration as a continuous linear functional on test functions. -/
private def cmIntegralCLM : TestRd d →L[ℝ] ℝ :=
  TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ) volume (fun _ => 1)

private theorem cmIntegralCLM_apply (φ : TestRd d) : cmIntegralCLM φ = ∫ x, φ x := by
  rw [cmIntegralCLM, TestFunction.integralAgainstBilinCLM_eq_integral
    (locallyIntegrableOn_const (1 : ℝ))]
  change (∫ x, φ x * 1) = ∫ x, φ x
  simp only [mul_one]

/-- A finite real linear combination of mean-zero test functions is mean zero. -/
def cmTestSum (c : TestRd0 d →₀ ℝ) : TestRd0 d := by
  refine ⟨c.sum fun φ a => a • φ.1, ?_⟩
  rw [← cmIntegralCLM_apply]
  rw [Finsupp.sum, map_sum]
  refine Finset.sum_eq_zero (fun φ _ => ?_)
  rw [map_smul, cmIntegralCLM_apply, φ.2, smul_zero]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistRd d}

/-- A mean-zero pairing as an element of `L²(P)`. -/
private def cmPairL2 (hh : IsWholeSpaceLGF h P) (φ : TestRd0 d) : Lp ℝ 2 P :=
  ((hh.gaussian.hasGaussianLaw_eval φ).memLp_two).toLp (fun ω => h ω φ.1)

/-- The finite linear combinations of the Gaussian coordinates. -/
private def cmPairLin (hh : IsWholeSpaceLGF h P) :
    (TestRd0 d →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 P :=
  Finsupp.linearCombination ℝ (cmPairL2 hh)

omit [IsProbabilityMeasure P] in
private theorem cmPairLin_eq (hh : IsWholeSpaceLGF h P) (c : TestRd0 d →₀ ℝ) :
    cmPairLin hh c = cmPairL2 hh (cmTestSum c) := by
  apply Lp.ext
  have hsum := Lp.coeFn_fun_finsetSum (μ := P) (p := 2) c.support
    (fun φ => c φ • cmPairL2 hh φ)
  have hterms : ∀ᵐ ω ∂P, ∀ φ ∈ c.support,
      ((c φ • cmPairL2 hh φ : Lp ℝ 2 P) : Ω → ℝ) ω = c φ * h ω φ.1 := by
    apply (ae_ball_iff c.support.countable_toSet).2
    intro φ _
    filter_upwards [Lp.coeFn_smul (c φ) (cmPairL2 hh φ),
      ((hh.gaussian.hasGaussianLaw_eval φ).memLp_two).coeFn_toLp] with ω ha hb
    calc
      ((c φ • cmPairL2 hh φ : Lp ℝ 2 P) : Ω → ℝ) ω =
          c φ * (cmPairL2 hh φ : Ω → ℝ) ω := by rw [ha]; rfl
      _ = c φ * h ω φ.1 := congrArg (fun x => c φ * x) (by simpa only [cmPairL2] using hb)
  filter_upwards [hsum, hterms,
    ((hh.gaussian.hasGaussianLaw_eval (cmTestSum c)).memLp_two).coeFn_toLp] with ω ha hb hc
  change ((∑ φ ∈ c.support, c φ • cmPairL2 hh φ : Lp ℝ 2 P) : Ω → ℝ) ω = _
  rw [ha]
  rw [Finset.sum_congr rfl (fun φ hφ => hb φ hφ)]
  rw [show (cmPairL2 hh (cmTestSum c) : Ω → ℝ) ω = h ω (cmTestSum c).1 from
    (by simpa only [cmPairL2] using hc)]
  simp only [cmTestSum, Finsupp.sum, map_sum, map_smul, smul_eq_mul]

/-- The covariance norm of a finite combination of pairings. -/
private theorem cmPairLin_norm (hh : IsWholeSpaceLGF h P) (c : TestRd0 d →₀ ℝ) :
    ‖cmPairLin hh c‖ = logNorm (cmTestSum c).1 := by
  have hM := (hh.gaussian.hasGaussianLaw_eval (cmTestSum c)).memLp_two
  have hcov : ‖cmPairLin hh c‖ ^ 2 = logCovRd (cmTestSum c).1 (cmTestSum c).1 := by
    rw [cmPairLin_eq, ← real_inner_self_eq_norm_sq]
    exact (LQGMetric.MarkovZB.inner_toLp_eq_cov hM hM (hh.centered (cmTestSum c))).trans
      (hh.covariance_eq (cmTestSum c) (cmTestSum c))
  have hnn : 0 ≤ logCovRd (cmTestSum c).1 (cmTestSum c).1 := by
    rw [← hcov]; positivity
  have hsq : (logNorm (cmTestSum c).1) ^ 2 =
      logCovRd (cmTestSum c).1 (cmTestSum c).1 := Real.sq_sqrt hnn
  nlinarith [norm_nonneg (cmPairLin hh c), logNorm_nonneg (cmTestSum c).1]

/-- The deterministic shift pairing as a continuous functional on test functions. -/
private def cmShiftCLM (F : C(Rd d, ℝ)) : TestRd d →L[ℝ] ℝ :=
  TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ) volume F

private theorem cmShiftCLM_apply (F : C(Rd d, ℝ)) (φ : TestRd d) :
    cmShiftCLM F φ = ∫ x, F x * φ x := by
  rw [cmShiftCLM, TestFunction.integralAgainstBilinCLM_eq_integral
    (F.continuous.locallyIntegrable.locallyIntegrableOn _)]
  change (∫ x, φ x * F x) = ∫ x, F x * φ x
  congr 1
  funext x
  exact mul_comm _ _

private def cmShiftLin (F : C(Rd d, ℝ)) : (TestRd0 d →₀ ℝ) →ₗ[ℝ] ℝ :=
  (cmShiftCLM F).toLinearMap.comp (Finsupp.linearCombination ℝ (fun φ : TestRd0 d => φ.1))

private theorem cmShiftLin_apply (F : C(Rd d, ℝ)) (c : TestRd0 d →₀ ℝ) :
    cmShiftLin F c = ∫ x, F x * (cmTestSum c).1 x := by
  rw [cmShiftLin, LinearMap.comp_apply, Finsupp.linearCombination_apply]
  exact cmShiftCLM_apply F _

private def cmGaussSpace (hh : IsWholeSpaceLGF h P) : Submodule ℝ (Lp ℝ 2 P) :=
  LQGMetric.MarkovGauss.gaussSpace (fun (φ : TestRd0 d) (ω : Ω) => h ω φ.1)
    (fun φ => (hh.gaussian.hasGaussianLaw_eval φ).memLp_two)

omit [IsProbabilityMeasure P] in
private theorem cmPairLin_mem (hh : IsWholeSpaceLGF h P) (c : TestRd0 d →₀ ℝ) :
    cmPairLin hh c ∈ cmGaussSpace hh := by
  rw [cmPairLin_eq]
  exact LQGMetric.MarkovGauss.toLp_mem_gaussSpace
    (fun φ : TestRd0 d => (hh.gaussian.hasGaussianLaw_eval φ).memLp_two) (cmTestSum c)

private def cmPairLinG (hh : IsWholeSpaceLGF h P) :
    (TestRd0 d →₀ ℝ) →ₗ[ℝ] cmGaussSpace hh :=
  (cmPairLin hh).codRestrict (cmGaussSpace hh) (cmPairLin_mem hh)

private theorem cmShiftLin_ker (hh : IsWholeSpaceLGF h P) (F : C(Rd d, ℝ))
    {C : ℝ} (hF : IsCMBounded F C) :
    LinearMap.ker (cmPairLinG hh) ≤ LinearMap.ker (cmShiftLin F) := by
  intro c hc
  have hzero : cmPairLin hh c = 0 := by
    have := LinearMap.mem_ker.mp hc
    exact Subtype.ext_iff.mp this
  have hnorm : logNorm (cmTestSum c).1 = 0 := by
    rw [← cmPairLin_norm hh c, hzero, norm_zero]
  have hb := hF (cmTestSum c)
  rw [hnorm, mul_zero] at hb
  have hz : (∫ x, F x * (cmTestSum c).1 x) = 0 :=
    abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
  exact LinearMap.mem_ker.mpr ((cmShiftLin_apply F c).trans hz)

/-- The shift functional on the finite Gaussian span. -/
private def cmRangeLin (hh : IsWholeSpaceLGF h P) (F : C(Rd d, ℝ))
    {C : ℝ} (hF : IsCMBounded F C) :
    LinearMap.range (cmPairLinG hh) →ₗ[ℝ] ℝ :=
  ((LinearMap.ker (cmPairLinG hh)).liftQ (cmShiftLin F) (cmShiftLin_ker hh F hF)).comp
    (cmPairLinG hh).quotKerEquivRange.symm.toLinearMap

private theorem cmRangeLin_apply (hh : IsWholeSpaceLGF h P) (F : C(Rd d, ℝ))
    {C : ℝ} (hF : IsCMBounded F C) (c : TestRd0 d →₀ ℝ) :
    cmRangeLin hh F hF ⟨cmPairLinG hh c, LinearMap.mem_range_self _ c⟩ =
      cmShiftLin F c := by
  simp only [cmRangeLin, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

private theorem cmRangeLin_bound (hh : IsWholeSpaceLGF h P) (F : C(Rd d, ℝ))
    {C : ℝ} (hF : IsCMBounded F C) (v : LinearMap.range (cmPairLinG hh)) :
    ‖cmRangeLin hh F hF v‖ ≤ |C| * ‖v‖ := by
  obtain ⟨v, hv⟩ := v
  obtain ⟨c, rfl⟩ := hv
  rw [cmRangeLin_apply, Real.norm_eq_abs, cmShiftLin_apply]
  have hb := hF (cmTestSum c)
  have hc : C * logNorm (cmTestSum c).1 ≤ |C| * logNorm (cmTestSum c).1 :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (logNorm_nonneg _)
  have hn : ‖(⟨cmPairLinG hh c, LinearMap.mem_range_self _ c⟩ :
      LinearMap.range (cmPairLinG hh))‖ = logNorm (cmTestSum c).1 :=
    cmPairLin_norm hh c
  rw [hn]
  exact hb.trans hc

/-- Hahn–Banach extends the bounded functional from the finite Gaussian span. -/
private theorem cmExistsDual (hh : IsWholeSpaceLGF h P) (F : C(Rd d, ℝ))
    {C : ℝ} (hF : IsCMBounded F C) :
    ∃ L : StrongDual ℝ (cmGaussSpace hh),
      (∀ v, ‖L v‖ ≤ |C| * ‖v‖) ∧
      ∀ c : TestRd0 d →₀ ℝ, L (cmPairLinG hh c) = cmShiftLin F c := by
  let sm : SMul NNReal (Seminorm ℝ (cmGaussSpace hh)) := Seminorm.instSMul
  let q : Seminorm ℝ (cmGaussSpace hh) :=
    sm.smul (⟨|C|, abs_nonneg C⟩ : NNReal) (normSeminorm ℝ (cmGaussSpace hh))
  have hqval (v : cmGaussSpace hh) : q v = |C| * ‖v‖ := rfl
  have hq : Continuous q := by
    have heq : (q : cmGaussSpace hh → ℝ) = fun v => |C| * ‖v‖ :=
      funext hqval
    rw [heq]
    exact continuous_norm.const_mul _
  have hbound : ∀ v : LinearMap.range (cmPairLinG hh),
      ‖cmRangeLin hh F hF v‖ ≤ q v := by
    intro v
    rw [hqval, Submodule.norm_coe]
    exact cmRangeLin_bound hh F hF v
  obtain ⟨L, hL, hLb⟩ := Module.Dual.exists_continuous_extension_of_le_seminorm
    (LinearMap.range (cmPairLinG hh)) (cmRangeLin hh F hF) hq hbound
  refine ⟨L, ?_, fun c => ?_⟩
  · intro v
    have hb := hLb v
    rw [hqval] at hb
    exact hb
  · exact (hL ⟨cmPairLinG hh c, LinearMap.mem_range_self _ c⟩).trans
      (cmRangeLin_apply hh F hF c)

omit [IsProbabilityMeasure P] in
private theorem cmGaussComplete (hh : IsWholeSpaceLGF h P) :
    CompleteSpace (cmGaussSpace hh) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- Riesz representative of the deterministic shift on the Gaussian Hilbert space. -/
private theorem cmExistsVec (hh : IsWholeSpaceLGF h P) (F : C(Rd d, ℝ))
    {C : ℝ} (hF : IsCMBounded F C) :
    ∃ y : cmGaussSpace hh, ‖y‖ ≤ |C| ∧
      ∀ φ : TestRd0 d, ⟪y, (⟨cmPairL2 hh φ,
        LQGMetric.MarkovGauss.toLp_mem_gaussSpace
          (fun ψ : TestRd0 d => (hh.gaussian.hasGaussianLaw_eval ψ).memLp_two) φ⟩ :
        cmGaussSpace hh)⟫ = ∫ x, F x * φ.1 x := by
  haveI : CompleteSpace (cmGaussSpace hh) := cmGaussComplete hh
  obtain ⟨L, hLb, hL⟩ := cmExistsDual hh F hF
  let y : cmGaussSpace hh := (InnerProductSpace.toDual ℝ (cmGaussSpace hh)).symm L
  have hy : ‖y‖ ≤ |C| := by
    have heq : ⟪y, y⟫ = L y := InnerProductSpace.toDual_symm_apply
    have hb := hLb y
    rw [← heq, real_inner_self_eq_norm_sq, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)] at hb
    by_cases hz : ‖y‖ = 0
    · simpa only [hz] using abs_nonneg C
    · have hpos : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      by_contra hn
      have ha : |C| < ‖y‖ := lt_of_not_ge hn
      have hm : 0 < ‖y‖ * (‖y‖ - |C|) := mul_pos hpos (sub_pos.mpr ha)
      nlinarith only [hb, hm]
  refine ⟨y, hy, fun φ => ?_⟩
  have hsingle := hL (Finsupp.single φ 1)
  have hp : cmPairLinG hh (Finsupp.single φ 1) =
      (⟨cmPairL2 hh φ, LQGMetric.MarkovGauss.toLp_mem_gaussSpace
        (fun ψ : TestRd0 d => (hh.gaussian.hasGaussianLaw_eval ψ).memLp_two) φ⟩ :
        cmGaussSpace hh) := by
    apply Subtype.ext
    simp only [cmPairLinG, LinearMap.codRestrict_apply, cmPairLin,
      Finsupp.linearCombination_single, one_smul]
  have hs : cmShiftLin F (Finsupp.single φ 1) = ∫ x, F x * φ.1 x := by
    simp only [cmShiftLin, LinearMap.comp_apply, Finsupp.linearCombination_single, one_smul]
    exact cmShiftCLM_apply F φ.1
  rw [hp, hs] at hsingle
  exact (InnerProductSpace.toDual_symm_apply).trans hsingle

/-- A measurable representative of the Riesz vector, with its second moment and shift covariance. -/
private theorem cmExistsY (hh : IsWholeSpaceLGF h P) (F : C(Rd d, ℝ))
    {C : ℝ} (hF : IsCMBounded F C) :
    ∃ Y : Ω → ℝ, Measurable Y ∧
      ∫ ω, Y ω ^ 2 ∂P ≤ C ^ 2 ∧
      (∀ φ : TestRd0 d, ∫ ω, Y ω * h ω φ.1 ∂P = ∫ x, F x * φ.1 x) ∧
      IsGaussianProcess (Sum.elim (fun _ : Unit => Y)
        (fun φ : TestRd0 d => fun ω => h ω φ.1)) P ∧
      (∫ ω, Y ω ∂P = 0) := by
  obtain ⟨y, hy, hyφ⟩ := cmExistsVec hh F hF
  let yL2 : Lp ℝ 2 P := y.1
  let Y : Ω → ℝ := (Lp.aestronglyMeasurable yL2).mk (yL2 : Ω → ℝ)
  have hYm : Measurable Y := (Lp.aestronglyMeasurable yL2).measurable_mk
  have hYae : (yL2 : Ω → ℝ) =ᵐ[P] Y := (Lp.aestronglyMeasurable yL2).ae_eq_mk
  have hY2 : ∫ ω, Y ω ^ 2 ∂P = ‖yL2‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hYae] with ω hω
    rw [← hω]
    simp [pow_two]
  have hYY : ∫ ω, Y ω ^ 2 ∂P ≤ C ^ 2 := by
    rw [hY2]
    have hn : ‖yL2‖ ≤ |C| := by simpa only [yL2, Submodule.norm_coe] using hy
    nlinarith only [sq_nonneg (|C| - ‖yL2‖), hn, norm_nonneg yL2, abs_nonneg C,
      sq_abs C]
  have hYgp0 : IsGaussianProcess (Sum.elim (fun _ : Unit => (yL2 : Ω → ℝ))
      (fun φ : TestRd0 d => fun ω => h ω φ.1)) P := by
    refine LQGMetric.MarkovGauss.isGaussianProcess_sumElim hh.gaussian hh.centered
      (fun φ => (hh.gaussian.hasGaussianLaw_eval φ).memLp_two)
      (fun _ : Unit => yL2) (fun _ => y.2) id
  have hYgp : IsGaussianProcess (Sum.elim (fun _ : Unit => Y)
      (fun φ : TestRd0 d => fun ω => h ω φ.1)) P := by
    apply hYgp0.congr
    intro i
    cases i with
    | inl u => exact hYae
    | inr φ => exact EventuallyEq.rfl
  have hYzero : ∫ ω, Y ω ∂P = 0 := by
    rw [← integral_congr_ae hYae]
    exact (LQGMetric.MarkovGauss.isCGauss_of_mem_gaussSpace hh.gaussian hh.centered
      (fun φ => (hh.gaussian.hasGaussianLaw_eval φ).memLp_two) y.2).2
  refine ⟨Y, hYm, hYY, ?_, hYgp, hYzero⟩
  intro φ
  have hinner := hyφ φ
  rw [Submodule.coe_inner] at hinner
  rw [L2.inner_def] at hinner
  have hpair : (cmPairL2 hh φ : Ω → ℝ) =ᵐ[P] fun ω => h ω φ.1 :=
    ((hh.gaussian.hasGaussianLaw_eval φ).memLp_two).coeFn_toLp
  calc
    (∫ ω, Y ω * h ω φ.1 ∂P) =
        ∫ ω, inner ℝ (yL2 ω) ((cmPairL2 hh φ : Ω → ℝ) ω) ∂P := by
          apply integral_congr_ae
          filter_upwards [hYae, hpair] with ω ha hb
          rw [← ha, hb]
          simp [mul_comm]
    _ = ∫ x, F x * φ.1 x := hinner

theorem cmPair0_addFun (g : DistRd d) (F : C(Rd d, ℝ)) (φ : TestRd0 d) :
    pair0Rd (addFun g F) φ = pair0Rd g φ + ∫ x, F x * φ.1 x := by
  rw [pair0Rd, pair0Rd, addFun_apply]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => mul_comm _ _

private theorem cmCovShift (hh : IsWholeSpaceLGF h P) (F : C(Rd d, ℝ))
    {Y : Ω → ℝ}
    (hYcov : ∀ φ : TestRd0 d, ∫ ω, Y ω * h ω φ.1 ∂P = ∫ x, F x * φ.1 x)
    (hYgp : IsGaussianProcess (Sum.elim (fun _ : Unit => Y)
        (fun φ : TestRd0 d => fun ω => h ω φ.1)) P)
    (hYzero : ∫ ω, Y ω ∂P = 0) (φ : TestRd0 d) :
    QuantumZipper.CameronMartin.covShift
      (Sum.elim (fun _ : Unit => Y) (fun φ : TestRd0 d => fun ω => h ω φ.1)) P
      (Finsupp.single (Sum.inl ()) 1) (Sum.inr φ) = ∫ x, F x * φ.1 x := by
  have hYL2 : MemLp Y 2 P := (hYgp.hasGaussianLaw_eval (Sum.inl ())).memLp_two
  have hφL2 : MemLp (fun ω => h ω φ.1) 2 P := (hh.gaussian.hasGaussianLaw_eval φ).memLp_two
  simp only [QuantumZipper.CameronMartin.covShift,
    QuantumZipper.CameronMartin.covK,
    Finsupp.support_single _ one_ne_zero, Finset.sum_singleton,
    Finsupp.single_eq_same, one_mul]
  change cov[fun ω => h ω φ.1, Y; P] = _
  rw [covariance_eq_sub hφL2 hYL2, hYzero, mul_zero, sub_zero]
  rw [← hYcov φ]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => by simp only [Pi.mul_apply, mul_comm]

private theorem cmCovNorm (_hh : IsWholeSpaceLGF h P) {Y : Ω → ℝ}
    (hYgp : IsGaussianProcess (Sum.elim (fun _ : Unit => Y)
        (fun φ : TestRd0 d => fun ω => h ω φ.1)) P)
    (hYzero : ∫ ω, Y ω ∂P = 0) :
    QuantumZipper.CameronMartin.covNorm
      (Sum.elim (fun _ : Unit => Y) (fun φ : TestRd0 d => fun ω => h ω φ.1)) P
      (Finsupp.single (Sum.inl ()) 1) = ∫ ω, Y ω ^ 2 ∂P := by
  have hYL2 : MemLp Y 2 P := (hYgp.hasGaussianLaw_eval (Sum.inl ())).memLp_two
  simp only [QuantumZipper.CameronMartin.covNorm,
    QuantumZipper.CameronMartin.covShift, QuantumZipper.CameronMartin.covK,
    Finsupp.support_single _ one_ne_zero, Finset.sum_singleton,
    Finsupp.single_eq_same, one_mul]
  change cov[Y, Y; P] = _
  rw [covariance_eq_sub hYL2 hYL2, hYzero, zero_mul, sub_zero]
  congr 1
  funext ω
  simp only [Pi.mul_apply, pow_two]

/-- Cameron–Martin formula with the augmented centered Gaussian process exposed. -/
theorem lgf_cameronMartin_aug {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P)
    (F : C(Rd d, ℝ)) {C : ℝ} (hF : IsCMBounded F C) :
    ∃ Y : Ω → ℝ, Measurable Y ∧ ∫ ω, Y ω ^ 2 ∂P ≤ C ^ 2 ∧
      (∀ φ : TestRd0 d, ∫ ω, Y ω * h ω φ.1 ∂P = ∫ x, F x * φ.1 x) ∧
      IsGaussianProcess (Sum.elim (fun _ : Unit => Y)
        (fun φ : TestRd0 d => fun ω => h ω φ.1)) P ∧
      (∫ ω, Y ω ∂P = 0) ∧
      ∀ Φ : (TestRd0 d → ℝ) → ℝ≥0∞, Measurable Φ →
        ∫⁻ ω, Φ (pair0Rd (addFun (h ω) F)) ∂P =
          ∫⁻ ω, Φ (pair0Rd (h ω)) *
            ENNReal.ofReal (Real.exp (Y ω - (∫ ω', Y ω' ^ 2 ∂P) / 2)) ∂P := by
  obtain ⟨Y, hYm, hY2, hYcov, hYgp, hYzero⟩ := cmExistsY hh F hF
  refine ⟨Y, hYm, hY2, hYcov, hYgp, hYzero, ?_⟩
  let X : Sum Unit (TestRd0 d) → Ω → ℝ :=
    Sum.elim (fun _ : Unit => Y) (fun φ : TestRd0 d => fun ω => h ω φ.1)
  have hXm : ∀ i, Measurable (X i) := by
    intro i
    cases i with
    | inl u => exact hYm
    | inr φ => exact (measurable_distOn_apply φ.1).comp hh.measurable
  have hX0 : ∀ i, ∫ ω, X i ω ∂P = 0 := by
    intro i
    cases i with
    | inl u => exact hYzero
    | inr φ => exact hh.centered φ
  let σ : Sum Unit (TestRd0 d) →₀ ℝ := Finsupp.single (Sum.inl ()) 1
  intro Φ hΦ
  let Ψ : (Sum Unit (TestRd0 d) → ℝ) → ℝ≥0∞ :=
    fun a => Φ (fun φ => a (Sum.inr φ))
  have hΨ : Measurable Ψ := hΦ.comp (measurable_pi_iff.mpr fun φ => measurable_pi_apply _)
  have ht := QuantumZipper.PalmNorm.lintegral_mul_tiltDensity hYgp hXm hX0 σ Ψ hΨ
  have eBase (ω : Ω) : Ψ (fun j => X j ω) = Φ (pair0Rd (h ω)) := rfl
  have eDensity (ω : Ω) : QuantumZipper.CameronMartin.tiltDensity X P σ ω =
      Real.exp (Y ω - (∫ ω', Y ω' ^ 2 ∂P) / 2) := by
    rw [QuantumZipper.CameronMartin.tiltDensity]
    change Real.exp (QuantumZipper.CameronMartin.comb X σ ω -
      QuantumZipper.CameronMartin.covNorm X P σ / 2) = _
    rw [show QuantumZipper.CameronMartin.covNorm X P σ = ∫ ω', Y ω' ^ 2 ∂P from
      cmCovNorm hh hYgp hYzero]
    simp only [QuantumZipper.CameronMartin.comb, σ,
      Finsupp.support_single _ one_ne_zero, Finset.sum_singleton,
      Finsupp.single_eq_same, one_mul]
    rfl
  have eShift (ω : Ω) :
      Ψ (fun j => X j ω + QuantumZipper.CameronMartin.covShift X P σ j) =
      Φ (pair0Rd (addFun (h ω) F)) := by
    change Φ (fun φ => X (Sum.inr φ) ω +
      QuantumZipper.CameronMartin.covShift X P σ (Sum.inr φ)) = _
    apply congrArg Φ
    funext φ
    change h ω φ.1 + QuantumZipper.CameronMartin.covShift X P σ (Sum.inr φ) =
      pair0Rd (addFun (h ω) F) φ
    rw [show QuantumZipper.CameronMartin.covShift X P σ (Sum.inr φ) =
      ∫ x, F x * φ.1 x from cmCovShift hh F hYcov hYgp hYzero φ]
    exact (cmPair0_addFun (h ω) F φ).symm
  calc
    (∫⁻ ω, Φ (pair0Rd (addFun (h ω) F)) ∂P) =
        ∫⁻ ω, Ψ (fun j => X j ω + QuantumZipper.CameronMartin.covShift X P σ j) ∂P := by
          apply lintegral_congr
          intro ω
          exact (eShift ω).symm
    _ = ∫⁻ ω, Ψ (fun j => X j ω) *
          ENNReal.ofReal (QuantumZipper.CameronMartin.tiltDensity X P σ ω) ∂P := ht.symm
    _ = ∫⁻ ω, Φ (pair0Rd (h ω)) *
          ENNReal.ofReal (Real.exp (Y ω - (∫ ω', Y ω' ^ 2 ∂P) / 2)) ∂P := by
          apply lintegral_congr
          intro ω
          rw [eBase, eDensity]

/-- Cameron–Martin formula for the whole-space LGF modulo constants. -/
theorem lgf_cameronMartin {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P)
    (F : C(Rd d, ℝ)) {C : ℝ} (hF : IsCMBounded F C) :
    ∃ Y : Ω → ℝ, Measurable Y ∧ ∫ ω, Y ω ^ 2 ∂P ≤ C ^ 2 ∧
      (∀ φ : TestRd0 d, ∫ ω, Y ω * h ω φ.1 ∂P = ∫ x, F x * φ.1 x) ∧
      ∀ Φ : (TestRd0 d → ℝ) → ℝ≥0∞, Measurable Φ →
        ∫⁻ ω, Φ (pair0Rd (addFun (h ω) F)) ∂P =
          ∫⁻ ω, Φ (pair0Rd (h ω)) *
            ENNReal.ofReal (Real.exp (Y ω - (∫ ω', Y ω' ^ 2 ∂P) / 2)) ∂P := by
  obtain ⟨Y, hYm, hY2, hYcov, _, _, hformula⟩ := lgf_cameronMartin_aug hh F hF
  exact ⟨Y, hYm, hY2, hYcov, hformula⟩

end HigherDimLQGMetric
