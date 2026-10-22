import HigherDimLQGMetric.Locality.TruncInternal
import HigherDimLQGMetric.Locality.StageData

/-!
# Independence of localized truncated LFPP internal metrics

This is the finite-scale conditional-independence input. The Markov theorem
provides the independence and the exterior agreement required here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_indep_truncInternal_stage {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 < ε) (ξ : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (h h' : Ω → DistRd d) (V U₁ W W' : TopologicalSpace.Opens (Rd d))
    (hWc : IsPreconnected (W : Set (Rd d)))
    (hW'c : IsPreconnected (W' : Set (Rd d)))
    (f f' : C(Rd d, ℝ))
    (hfW : ∀ z ∈ W, f z = 1)
    (hfV : ∀ z ∈ Function.support f, Metric.closedBall z (Real.sqrt ε) ⊆ V)
    (hfW' : ∀ z ∈ W', f' z = 1)
    (hfU₁ : ∀ z ∈ Function.support f', Metric.closedBall z (Real.sqrt ε) ⊆ U₁)
    (O : TopologicalSpace.Opens (Rd d)) (hU₁O : U₁ ≤ O)
    (R : Ω → DistOn O)
    (hind : Indep (MeasurableSpace.comap R inferInstance) (fieldSigmaRd h V) P)
    (hres : ∀ ω, restrictTo U₁ (h' ω) = restrictOn hU₁O (R ω)) :
    Indep
      (fieldSigmaRd h V ⊔ MeasurableSpace.comap
        (fun ω => internalC (fieldLfppMetric ξ ⟨truncMollify κ ε (h ω),
          l2c_continuous_truncMollify hd hκ hε (h ω)⟩)
          (fieldLfppMetric_isLength ξ ⟨truncMollify κ ε (h ω),
            l2c_continuous_truncMollify hd hκ hε (h ω)⟩) W.isOpen hWc) inferInstance)
      (MeasurableSpace.comap R inferInstance ⊔ MeasurableSpace.comap
        (fun ω => internalC (fieldLfppMetric ξ ⟨truncMollify κ ε (h' ω),
          l2c_continuous_truncMollify hd hκ hε (h' ω)⟩)
          (fieldLfppMetric_isLength ξ ⟨truncMollify κ ε (h' ω),
            l2c_continuous_truncMollify hd hκ hε (h' ω)⟩) W'.isOpen hW'c) inferInstance) P := by
  have hleft := l7a_measurable_truncInternalC hd hκ hε ξ V W hWc f hfW hfV h
  have hright := l7a_measurable_truncInternalC hd hκ hε ξ U₁ W' hW'c f' hfW' hfU₁ h'
  have hfield : fieldSigmaRd h' U₁ ≤ MeasurableSpace.comap R inferInstance := by
    letI : MeasurableSpace Ω := MeasurableSpace.comap R inferInstance
    change MeasurableSpace.comap (fun ω => restrictTo U₁ (h' ω)) inferInstance ≤
      MeasurableSpace.comap R inferInstance
    apply measurable_iff_comap_le.mp
    have hm : Measurable (fun ω => restrictOn hU₁O (R ω)) :=
      (measurable_restrictOn hU₁O).comp (comap_measurable R)
    convert hm using 1
    funext ω
    exact hres ω
  have hA : fieldSigmaRd h V ⊔ MeasurableSpace.comap
      (fun ω => internalC (fieldLfppMetric ξ ⟨truncMollify κ ε (h ω),
        l2c_continuous_truncMollify hd hκ hε (h ω)⟩)
        (fieldLfppMetric_isLength ξ ⟨truncMollify κ ε (h ω),
          l2c_continuous_truncMollify hd hκ hε (h ω)⟩) W.isOpen hWc) inferInstance ≤
      fieldSigmaRd h V := sup_le le_rfl hleft.comap_le
  have hB : MeasurableSpace.comap R inferInstance ⊔ MeasurableSpace.comap
      (fun ω => internalC (fieldLfppMetric ξ ⟨truncMollify κ ε (h' ω),
        l2c_continuous_truncMollify hd hκ hε (h' ω)⟩)
        (fieldLfppMetric_isLength ξ ⟨truncMollify κ ε (h' ω),
          l2c_continuous_truncMollify hd hκ hε (h' ω)⟩) W'.isOpen hW'c) inferInstance ≤
      MeasurableSpace.comap R inferInstance :=
    sup_le le_rfl (hright.comap_le.trans hfield)
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hind.symm hA) hB

/-- The Markov residual supplies the exterior field in the finite-scale
independence theorem. The cutoff is one throughout `U₁`, so the restricted
perturbed distribution is exactly the residual restricted to `U₁`. -/
theorem l7a_indep_markov_truncInternal_stage {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 < ε) (ξ : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (g : Ω → DistRd d) (V U₁ W W' : TopologicalSpace.Opens (Rd d))
    (hU₁ : U₁ ≤ extOpen V)
    (hWc : IsPreconnected (W : Set (Rd d)))
    (hW'c : IsPreconnected (W' : Set (Rd d)))
    (f f' φ : C(Rd d, ℝ))
    (hfW : ∀ z ∈ W, f z = 1)
    (hfV : ∀ z ∈ Function.support f, Metric.closedBall z (Real.sqrt ε) ⊆ V)
    (hfW' : ∀ z ∈ W', f' z = 1)
    (hfU₁ : ∀ z ∈ Function.support f', Metric.closedBall z (Real.sqrt ε) ⊆ U₁)
    (hφ1 : ∀ z ∈ U₁, φ z = 1)
    (hφsup : tsupport φ ⊆ extOpen V)
    (H : Ω → Rd d → ℝ)
    (hHc : ∀ ω, ContinuousOn (H ω) (extOpen V))
    (hind : Indep
      (MeasurableSpace.comap (fun ω => restrictTo (extOpen V) (g ω) -
        ofFunOn (extOpen V) (H ω)) inferInstance)
      (fieldSigmaRd g V) P) :
    Indep
      (fieldSigmaRd g V ⊔ MeasurableSpace.comap
        (fun ω => internalC (fieldLfppMetric ξ ⟨truncMollify κ ε (g ω),
          l2c_continuous_truncMollify hd hκ hε (g ω)⟩)
          (fieldLfppMetric_isLength ξ ⟨truncMollify κ ε (g ω),
            l2c_continuous_truncMollify hd hκ hε (g ω)⟩) W.isOpen hWc) inferInstance)
      (MeasurableSpace.comap (fun ω => restrictTo (extOpen V) (g ω) -
        ofFunOn (extOpen V) (H ω)) inferInstance ⊔ MeasurableSpace.comap
        (fun ω => internalC (fieldLfppMetric ξ
          ⟨truncMollify κ ε
            (g ω - ofCont ⟨fun z => φ z * H ω z,
              l7a_continuous_cutoffH (extOpen V).isOpen φ (H ω) (hHc ω) hφsup⟩),
            l2c_continuous_truncMollify hd hκ hε _⟩)
          (fieldLfppMetric_isLength ξ
            ⟨truncMollify κ ε
              (g ω - ofCont ⟨fun z => φ z * H ω z,
                l7a_continuous_cutoffH (extOpen V).isOpen φ (H ω) (hHc ω) hφsup⟩),
              l2c_continuous_truncMollify hd hκ hε _⟩) W'.isOpen hW'c)
          inferInstance) P := by
  let g' : Ω → DistRd d := fun ω => g ω - ofCont ⟨fun z => φ z * H ω z,
    l7a_continuous_cutoffH (extOpen V).isOpen φ (H ω) (hHc ω) hφsup⟩
  let R : Ω → DistOn (extOpen V) := fun ω => restrictTo (extOpen V) (g ω) -
    ofFunOn (extOpen V) (H ω)
  exact l7a_indep_truncInternal_stage hd hκ hε ξ P g g' V U₁ W W' hWc hW'c
    f f' hfW hfV hfW' hfU₁ (extOpen V) hU₁ R hind
    (fun ω => l7a_cutoff_residual_restrict V U₁ hU₁ φ (H ω) (hHc ω)
      hφsup hφ1 (g ω))

end HigherDimLQGMetric
