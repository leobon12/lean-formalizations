import MatedCRTHarmonic.GMS4c.LocalAreaMeasurable
import QuantumZipper.Proofs.LQG.MeasurabilityAE

/-!
# A Borel version of a local dyadic GMC limit

This is the measure-theoretic selection step. The domain law supplies the
almost-sure vague convergence and local integrability of the approximations;
The selected map is Borel on the entire space of restricted fields.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4c

open LQGMetric QuantumZipper
attribute [local instance] Classical.propDecidable

/-- A local dyadic sample on which the vague limit exists, is finite on `V`,
and continuous compactly supported tests are integrable at all sufficiently
fine scales. Vague convergence is unchanged by finitely many coarse scales. -/
def LocalDyadicGood (γ : ℝ) (V : TopologicalSpace.Opens ℂ) (δ : ℝ)
    (T : DistOn (thickOpen V δ)) : Prop :=
  (∃ μ : Measure ℂ, IsVagueLimitOn V (localAreaApproxDy γ V δ T) μ ∧ μ V < ⊤) ∧
    ∀ (f : ℂ → ℝ), Continuous f → HasCompactSupport f →
      tsupport f ⊆ V → ∀ᶠ k : ℕ in atTop,
        Integrable f (localAreaApproxDy γ V δ T k)

/-- The selected vague limit, with zero junk off the existence locus. -/
def localAreaVagueSelection (γ : ℝ) (V : TopologicalSpace.Opens ℂ) (δ : ℝ)
    (T : DistOn (thickOpen V δ)) : Measure ℂ :=
  if h : ∃ μ : Measure ℂ,
      IsVagueLimitOn V (localAreaApproxDy γ V δ T) μ ∧ μ V < ⊤
  then h.choose else 0

theorem localAreaVagueSelection_spec {γ : ℝ} {V : TopologicalSpace.Opens ℂ}
    {δ : ℝ} {T : DistOn (thickOpen V δ)}
    (h : LocalDyadicGood γ V δ T) :
    IsVagueLimitOn V (localAreaApproxDy γ V δ T)
      (localAreaVagueSelection γ V δ T) ∧
    (localAreaVagueSelection γ V δ T) V < ⊤ := by
  simpa [localAreaVagueSelection, h.1] using
    (Classical.choose_spec h.1)

/-- Under any law giving almost-sure local vague convergence and finite
approximants, the selected limit has a Borel version equal almost surely. -/
theorem exists_measurable_localAreaVagueSelection
    (γ : ℝ) (V : TopologicalSpace.Opens ℂ) (δ : ℝ)
    (ν : Measure (DistOn (thickOpen V δ)))
    (hgood : ∀ᵐ T ∂ν, LocalDyadicGood γ V δ T) :
    ∃ F : DistOn (thickOpen V δ) → Measure ℂ,
      Measurable F ∧
      F =ᵐ[ν] localAreaVagueSelection γ V δ := by
  classical
  obtain ⟨S, hSm, hSp, hS0⟩ :=
    QuantumZipper.LQGMeasAE.exists_measurableSet_subset_ae hgood
  let A : DistOn (thickOpen V δ) → Measure ℂ :=
    fun T => if T ∈ S then localAreaVagueSelection γ V δ T else 0
  let aFun : (ℂ → ℝ) → DistOn (thickOpen V δ) → ℝ :=
    fun f T => liminf (fun k =>
      (∫⁻ z, ENNReal.ofReal (f z) ∂localAreaApproxDy γ V δ T k).toReal) atTop
  have haFun {f : ℂ → ℝ} (hf : Continuous f) : Measurable (aFun f) := by
    exact Measurable.liminf fun k => ENNReal.measurable_toReal.comp
      ((Measure.measurable_lintegral
        (ENNReal.measurable_ofReal.comp hf.measurable)).comp
        (measurable_localAreaApproxDy γ V δ k))
  have hAm : Measurable A := by
    refine QuantumZipper.LQGMeas.measurable_measure_of_open A
      (fun N : ℕ => ball (0 : ℂ) ((N : ℝ) + 1))
      (fun _ => measurableSet_ball) ?_ (fun T => ?_) (fun T N => ?_)
      (fun U N hU => ?_)
    · intro m n hmn
      exact ball_subset_ball (by exact_mod_cast Nat.add_le_add_right hmn 1)
    · have hcover : (⋃ N : ℕ, ball (0 : ℂ) ((N : ℝ) + 1)) = univ := by
        refine eq_univ_of_forall fun z => mem_iUnion.2 ?_
        obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
        refine ⟨N, ?_⟩
        rw [mem_ball, dist_zero_right]
        linarith
      rw [hcover, compl_univ, measure_empty]
    · by_cases hT : T ∈ S
      · simp only [A, hT, ite_true]
        have hg := (localAreaVagueSelection_spec (hSp T hT))
        rw [← measure_inter_conull hg.1.1]
        exact (lt_of_le_of_lt (measure_mono (inter_subset_right :
          ball (0 : ℂ) ((N : ℝ) + 1) ∩ V ⊆ V)) hg.2).ne
      · simp [A, hT]
    · set W := U ∩ ball (0 : ℂ) ((N : ℝ) + 1) ∩ V
      have hWo : IsOpen W := (hU.inter isOpen_ball).inter V.isOpen
      have hWb : Bornology.IsBounded W :=
        isBounded_ball.subset (inter_subset_left.trans inter_subset_right)
      have hWc : Wᶜ.Nonempty := by
        refine ⟨(((N : ℝ) + 2 : ℝ) : ℂ), ?_⟩
        simp only [mem_compl_iff, W, mem_inter_iff]
        intro hz
        have hb := hz.1.2
        rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity)] at hb
        linarith
      have key : ∀ T, A T (U ∩ ball (0 : ℂ) ((N : ℝ) + 1)) =
          S.indicator (fun T => ⨆ j : ℕ, ENNReal.ofReal
            (aFun (QuantumZipper.LQGMeas.openBump W j) T)) T := by
        intro T
        by_cases hT : T ∈ S
        · simp only [A, hT, ite_true, indicator_of_mem hT]
          have hg := localAreaVagueSelection_spec (hSp T hT)
          have hrestrict : (localAreaVagueSelection γ V δ T)
              (U ∩ ball (0 : ℂ) ((N : ℝ) + 1)) =
              (localAreaVagueSelection γ V δ T) W := by
            rw [show W = (U ∩ ball (0 : ℂ) ((N : ℝ) + 1)) ∩ V by rfl]
            exact (measure_inter_conull hg.1.1).symm
          rw [hrestrict, QuantumZipper.LQGMeas.measure_open_eq_iSup _ hWo hWc]
          congr 1
          funext j
          have hc := QuantumZipper.LQGMeas.continuous_openBump W j
          have hcs := QuantumZipper.LQGMeas.hasCompactSupport_openBump hWb j
          have hsupp : tsupport (QuantumZipper.LQGMeas.openBump W j) ⊆ V :=
            (QuantumZipper.LQGMeas.tsupport_openBump_subset W j).trans
              (inter_subset_right : W ⊆ V)
          have hint : ∀ᶠ k : ℕ in atTop,
              Integrable (QuantumZipper.LQGMeas.openBump W j)
                (localAreaApproxDy γ V δ T k) :=
            (hSp T hT).2 _ hc hcs hsupp
          have heq : (fun k =>
              (∫⁻ z, ENNReal.ofReal (QuantumZipper.LQGMeas.openBump W j z)
                ∂localAreaApproxDy γ V δ T k).toReal) =ᶠ[atTop]
              (fun k =>
              ∫ z, QuantumZipper.LQGMeas.openBump W j z
                ∂localAreaApproxDy γ V δ T k) := by
            filter_upwards [hint] with k hk
            rw [← ofReal_integral_eq_lintegral_ofReal hk
              (ae_of_all _ fun z => QuantumZipper.LQGMeas.openBump_nonneg W j z)]
            exact ENNReal.toReal_ofReal
              (integral_nonneg_of_ae
                (ae_of_all _ fun z => QuantumZipper.LQGMeas.openBump_nonneg W j z))
          have hlim := (hg.1.2.2 _ hc hcs hsupp).congr' heq.symm
          simp only [aFun]
          rw [hlim.liminf_eq,
            ofReal_integral_eq_lintegral_ofReal
              (QuantumZipper.GoodSample.integrable_of_tsupport hg.1.2.1 hc hcs hsupp)
              (ae_of_all _ fun z => QuantumZipper.LQGMeas.openBump_nonneg W j z)]
        · simp [A, hT]
      simp_rw [key]
      exact (Measurable.iSup fun j => ENNReal.measurable_ofReal.comp
        (haFun (QuantumZipper.LQGMeas.continuous_openBump W j))).indicator hSm
  refine ⟨A, hAm, ?_⟩
  refine measure_mono_null (fun T hT => ?_) hS0
  by_contra h
  exact hT (by simp [A, show T ∈ S from not_not.1 h])

/-- A single Borel version works for two local-field laws whenever the
dyadic vague-limit conditions hold almost surely under each law. -/
theorem exists_measurable_localAreaVagueSelection_twoLaws
    (γ : ℝ) (V : TopologicalSpace.Opens ℂ) (δ : ℝ)
    (νγ ν₀ : Measure (DistOn (thickOpen V δ)))
    (hγ : ∀ᵐ T ∂νγ, LocalDyadicGood γ V δ T)
    (h₀ : ∀ᵐ T ∂ν₀, LocalDyadicGood γ V δ T) :
    ∃ F : DistOn (thickOpen V δ) → Measure ℂ,
      Measurable F ∧
      F =ᵐ[νγ] localAreaVagueSelection γ V δ ∧
      F =ᵐ[ν₀] localAreaVagueSelection γ V δ := by
  obtain ⟨F, hF, hEq⟩ := exists_measurable_localAreaVagueSelection
    γ V δ (νγ + ν₀) (ae_add_measure_iff.mpr ⟨hγ, h₀⟩)
  exact ⟨F, hF, (ae_add_measure_iff.mp hEq).1,
    (ae_add_measure_iff.mp hEq).2⟩

end MatedCRTHarmonic.GMS4c

