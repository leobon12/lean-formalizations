import HigherDimLQGMetric.Locality.StageScaled
import HigherDimLQGMetric.Locality.MarkovFixed
import HigherDimLQGMetric.Locality.IndepVersion

/-! Finite-stage independence with a fixed Markov witness and measurable
versions of its cutoff and residual. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_stage_finite_with_versions {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    (V : TopologicalSpace.Opens (Rd d)) (z₀ : Rd d) (ρ : ℝ)
    {ι κ' : Type*} (S : Finset ι) (T : Finset κ')
    (W : ι → TopologicalSpace.Opens (Rd d))
    (W' : κ' → TopologicalSpace.Opens (Rd d))
    (hWc : ∀ i ∈ S, IsPreconnected (W i : Set (Rd d)))
    (hW'c : ∀ j ∈ T, IsPreconnected (W' j : Set (Rd d)))
    (hWcomp : ∀ i ∈ S, IsCompact (closure (W i : Set (Rd d))))
    (hW'comp : ∀ j ∈ T, IsCompact (closure (W' j : Set (Rd d))))
    (hWV : ∀ i ∈ S, closure (W i : Set (Rd d)) ⊆ V)
    (hW'U : ∀ j ∈ T, closure (W' j : Set (Rd d)) ⊆ extOpen V)
    (H : Ω → Rd d → ℝ)
    (hHc : ∀ ω, ContinuousOn (H ω) (extOpen V))
    (hHm : ∃ G : Ω → Rd d → ℝ,
      Measurable[fieldSigmaRd
        (fun ω => addConst (h ω) (-sphereAvg (h ω) ρ z₀)) V] G ∧
      H =ᵐ[P] G)
    (hind : Indep (MeasurableSpace.comap
      (fun ω => restrictTo (extOpen V)
        (addConst (h ω) (-sphereAvg (h ω) ρ z₀)) -
          ofFunOn (extOpen V) (H ω)) inferInstance)
      (fieldSigmaRd (fun ω => addConst (h ω)
        (-sphereAvg (h ω) ρ z₀)) V) P) :
    let g : Ω → DistRd d := fun ω =>
      addConst (h ω) (-sphereAvg (h ω) ρ z₀)
    ∃ (φ : C(Rd d, ℝ)), tsupport φ ⊆ extOpen V ∧
      HasCompactSupport φ ∧
      ∃ K : Set (Rd d), IsCompact K ∧
      ∃ F : Ω → C(Rd d, ℝ),
        Measurable[fieldSigmaRd g V] F ∧
        (∀ ω, tsupport (F ω) ⊆ K) ∧
        (∀ ω, ∃ B : ℝ, ∀ x, |F ω x| ≤ B) ∧
      ∃ R : Ω → DistOn (extOpen V),
        Measurable[mΩ] R ∧
      (fun ω => restrictTo (extOpen V) (g ω) -
        ofFunOn (extOpen V) (H ω)) =ᵐ[P] R ∧
      ∃ Φ : (CoordJ → ℝ) → C(Rd d, ℝ) × DistOn (extOpen V),
        Measurable Φ ∧
        (fun ω => (F ω, R ω)) = Φ ∘ (fun ω => pairJ ⊤ (h ω)) ∧
      ∃ m : ℕ, ∀ k : ℕ,
        Indep
          (fieldSigmaRd g V ⊔ ⨆ i ∈ S,
            MeasurableSpace.comap (fun ω => internalC
              (l7a_truncScaledMetric hd κ hκ ξ (hεs (k + m)) (g ω))
              (l7a_truncScaledMetric_isLength hd κ hκ ξ
                (hεs (k + m)) (g ω))
              (W i).isOpen (hWc i ‹i ∈ S›)) inferInstance)
          (MeasurableSpace.comap R inferInstance ⊔ ⨆ j ∈ T,
            MeasurableSpace.comap (fun ω => internalC
              (l7a_truncScaledMetric hd κ hκ ξ (hεs (k + m))
                (g ω - ofCont (F ω)))
              (l7a_truncScaledMetric_isLength hd κ hκ ξ
                (hεs (k + m)) (g ω - ofCont (F ω)))
              (W' j).isOpen (hW'c j ‹j ∈ T›)) inferInstance) P := by
  dsimp only
  let g : Ω → DistRd d := fun ω =>
    addConst (h ω) (-sphereAvg (h ω) ρ z₀)
  obtain ⟨φ, hφsup, hφc, m, hm⟩ :=
    l7a_indep_stage_finite hd hκ ξ hεs hεt P g V
      S T W W' hWc hW'c hWcomp hW'comp hWV hW'U H hHc hind
  obtain ⟨K, hK, F, hFm, hFsup, hFb, hFae,
    R, _, hRm, hRae, _, Φ, hΦm, hΦeq⟩ :=
    l7a_markov_fixed_measurable_versions P h hh V z₀ ρ H
      hHc hHm hind φ hφsup hφc
  refine ⟨φ, hφsup, hφc, K, hK, F, hFm, hFsup, hFb,
    R, hRm, hRae, Φ, hΦm, hΦeq, m, fun k => ?_⟩
  let gRaw : Ω → DistRd d := fun ω => g ω - ofCont
    ⟨fun z => φ z * H ω z,
      l7a_continuous_cutoffH (extOpen V).isOpen φ (H ω)
        (hHc ω) hφsup⟩
  let gNew : Ω → DistRd d := fun ω => g ω - ofCont (F ω)
  have hRawEq : gRaw =ᵐ[P] gNew := by
    filter_upwards [hFae] with ω he
    dsimp only [gRaw, gNew]
    rw [he]
  have hBae (j : κ') (hj : j ∈ T) :
      (fun ω => internalC
        (l7a_truncScaledMetric hd κ hκ ξ (hεs (k + m)) (gRaw ω))
        (l7a_truncScaledMetric_isLength hd κ hκ ξ
          (hεs (k + m)) (gRaw ω))
        (W' j).isOpen (hW'c j hj)) =ᵐ[P]
      (fun ω => internalC
        (l7a_truncScaledMetric hd κ hκ ξ (hεs (k + m)) (gNew ω))
        (l7a_truncScaledMetric_isLength hd κ hκ ξ
          (hεs (k + m)) (gNew ω))
        (W' j).isOpen (hW'c j hj)) := by
    filter_upwards [hRawEq] with ω he
    rw [he]
  have hscaled := l7a_indep_scaled_of_unscaled hd κ hκ ξ
    (hεs (k + m)) P (fieldSigmaRd g V)
    (MeasurableSpace.comap
      (fun ω => restrictTo (extOpen V) (g ω) -
        ofFunOn (extOpen V) (H ω)) inferInstance)
    S T g gRaw W W' hWc hW'c (hm k)
  exact l7a_indep_of_ae_right_versions P
    (fieldSigmaRd g V ⊔ ⨆ i ∈ S,
      MeasurableSpace.comap (fun ω => internalC
        (l7a_truncScaledMetric hd κ hκ ξ (hεs (k + m)) (g ω))
        (l7a_truncScaledMetric_isLength hd κ hκ ξ
          (hεs (k + m)) (g ω))
        (W i).isOpen (hWc i ‹i ∈ S›)) inferInstance)
    T
    (fun ω => restrictTo (extOpen V) (g ω) -
      ofFunOn (extOpen V) (H ω)) R
    (fun j hj ω => internalC
      (l7a_truncScaledMetric hd κ hκ ξ (hεs (k + m)) (gRaw ω))
      (l7a_truncScaledMetric_isLength hd κ hκ ξ
        (hεs (k + m)) (gRaw ω))
      (W' j).isOpen (hW'c j hj))
    (fun j hj ω => internalC
      (l7a_truncScaledMetric hd κ hκ ξ (hεs (k + m)) (gNew ω))
      (l7a_truncScaledMetric_isLength hd κ hκ ξ
        (hεs (k + m)) (gNew ω))
      (W' j).isOpen (hW'c j hj))
    hRae (fun j hj => hBae j hj) hscaled

end HigherDimLQGMetric
