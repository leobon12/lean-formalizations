import SupercriticalConformalCovariance.Markov.HilbertProjection
import LQGMetric.Field.HarmLocA
import QuantumZipper.Proofs.GFF.K3.MixedM7D2

/-!
# A global Dirichlet representative for smooth whole-plane tests

An interior test of mass one anchors constants. The mean-zero remainder is represented by the
orthogonal projection of its whole-plane GFF pairing. This works on arbitrary admissible open
sets, including those meeting every Euclidean circle in their complement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace
open scoped RealInnerProductSpace

namespace SupercriticalConformalCovariance.Markov

open LQGMetric LQGMetric.MarkovZB LQGMetric.MarkovGerm QuantumZipper QuantumZipper.K3

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC} {V : Opens ℂ}

set_option maxHeartbeats 1000000 in
/-- Every smooth compactly supported whole-plane density has a finite Dirichlet dual
representative on `V`, after anchoring constants by one interior unit-mass test. -/
theorem exists_riesz_test_of_unit (hh : IsWholePlaneGFF h P) (hV : ZBAdmissible V)
    (hpos : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g)
    (β : TestOn V) (hβ : ∫ x, β x = 1) (φ : TestC) :
    ∃ u : gradClosure (V : Set ℂ) (zeroSpace V),
      ∀ f ∈ zeroSpace V, ⟪(u : GradSpace V), gradFeat V f⟫ = ∫ x, φ x * f x := by
  let m : ℝ := ∫ x, φ x
  have hext : ∫ x, (extC V β : TestC) x = 1 := by
    rw [show ((extC V β : TestC) : ℂ → ℝ) = β from coe_extC β]
    exact hβ
  have hiφ : Integrable (φ : ℂ → ℝ) := φ.continuous.integrable_of_hasCompactSupport
    φ.hasCompactSupport
  have hiβ : Integrable ((extC V β : TestC) : ℂ → ℝ) :=
    (extC V β).continuous.integrable_of_hasCompactSupport (extC V β).hasCompactSupport
  let ψ : TestC0 := ⟨φ - m • extC V β, by
    change ∫ x, (φ x - m * (extC V β : TestC) x) = 0
    rw [integral_sub hiφ (hiβ.const_mul m), integral_const_mul, hext]
    simp [m]⟩
  obtain ⟨v, hv⟩ := projectedPair_mem_cmRange hh V ψ
  let b : gradClosure (V : Set ℂ) (zeroSpace V) := ⟨zbRiesz V β, zbRiesz_mem β⟩
  refine ⟨v + m • b, fun f hf => ?_⟩
  have hpair := inner_projectedPair_gradLin hh V ψ ⟨f, hf⟩
  change cmIso hh V v = projectedPair hh V ψ at hv
  rw [← hv] at hpair
  change ⟪cmIso hh V v, cmIso hh V (gradLin V ⟨f, hf⟩)⟫ = _ at hpair
  rw [LinearIsometry.inner_map_map, Submodule.coe_inner] at hpair
  have hbpair := inner_zbRiesz_gradFeat hV hpos β hf
  have hfi : Integrable f := hf.1.continuous.integrable_of_hasCompactSupport hf.2.1
  have hφfi : Integrable (fun x => φ x * f x) :=
    (φ.continuous.mul hf.1.continuous).integrable_of_hasCompactSupport
      φ.hasCompactSupport.mul_right
  have hβfi : Integrable (fun x => β x * f x) :=
    (β.continuous.mul hf.1.continuous).integrable_of_hasCompactSupport
      β.hasCompactSupport.mul_right
  have hψeq : ∫ x, ψ.1 x * f x =
      (∫ x, φ x * f x) - m * ∫ x, β x * f x := by
    have e : (fun x => ψ.1 x * f x) =
        fun x => φ x * f x - m * (β x * f x) := by
      funext x
      simp only [ψ, TestFunction.coe_sub, Pi.sub_apply, TestFunction.coe_smul,
        Pi.smul_apply, smul_eq_mul]
      rw [show (extC V β : TestC) x = β x from congrFun (coe_extC β) x]
      ring
    rw [e, integral_sub hφfi (hβfi.const_mul m), integral_const_mul]
  change ⟪(v : GradSpace V), gradFeat V f⟫ = ∫ x, ψ.1 x * f x at hpair
  simp only [Submodule.coe_add, Submodule.coe_smul, inner_add_left, real_inner_smul_left]
  rw [hpair, hψeq]
  have heq : ∫ x, f x * β x = ∫ x, β x * f x :=
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  rw [hbpair, heq]
  ring

/-- Finite dual Dirichlet energy for a nonnegative smooth global density restricted to `V`.
The restriction may meet the boundary of `V`. -/
theorem dualNormSq_pos_indicator_test_lt_top (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V) (hpos : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g)
    (β : TestOn V) (hβ : ∫ x, β x = 1) (φ : TestC)
    (hφ : ∀ x, 0 ≤ φ x) :
    dualNormSq V (zeroSpace V) (testMeasPos ((V : Set ℂ).indicator φ)) < ⊤ := by
  obtain ⟨u, hu⟩ := exists_riesz_test_of_unit hh hV hpos β hβ φ
  have hρm : Measurable ((V : Set ℂ).indicator (φ : ℂ → ℝ)) :=
    φ.continuous.measurable.indicator V.isOpen.measurableSet
  have hρ0 : ∀ x, 0 ≤ (V : Set ℂ).indicator (φ : ℂ → ℝ) x :=
    fun x => indicator_nonneg (fun _ _ => hφ _) _
  have hpair : ∀ f ∈ zeroSpace V,
      ⟪(u : GradSpace V), gradFeat V f⟫ =
        ∫ x, f x ∂testMeasPos ((V : Set ℂ).indicator φ) := by
    intro f hf
    rw [hu f hf, integral_testMeasPos_K3 hρm]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change φ x * f x = max ((V : Set ℂ).indicator (φ : ℂ → ℝ) x) 0 * f x
    rw [max_eq_left (hρ0 x)]
    by_cases hx : x ∈ (V : Set ℂ)
    · rw [indicator_of_mem hx, mul_comm]
    · have hf0 : f x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hx' => hx (hf.2.2 hx'))
      rw [indicator_of_notMem hx, hf0]
      ring
  rw [dualNormSq_eq_of_pairing (isDNSpace_zeroSpace (V : Set ℂ)) u.2 hpair]
  exact ENNReal.ofReal_lt_top

/-- The smooth positive-density energy bound needs no chosen anchor on a nonempty domain. -/
theorem dualNormSq_pos_indicator_test_lt_top_of_nonempty (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V) (hne : (V : Set ℂ).Nonempty) (φ : TestC)
    (hφ : ∀ x, 0 ≤ φ x) :
    dualNormSq V (zeroSpace V) (testMeasPos ((V : Set ℂ).indicator φ)) < ⊤ := by
  obtain ⟨β, hβV, hβ1⟩ := LQGMetric.HarmLoc.exists_unit_test V.isOpen hne
  let βV : TestOn V := ⟨β, β.contDiff, β.hasCompactSupport, hβV⟩
  have hβ1' : ∫ x, βV x = 1 := hβ1
  exact dualNormSq_pos_indicator_test_lt_top hh hV
    (exists_pos_energy_zeroSpace_m7d V.isOpen hne) βV hβ1' φ hφ

end SupercriticalConformalCovariance.Markov
