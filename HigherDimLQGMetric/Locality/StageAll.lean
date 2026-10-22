import HigherDimLQGMetric.Locality.StageIndep

/-! The finite-scale independence statement with all spatial cutoffs and the
eventual `√ε` margin chosen from two compact domains. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_indep_stage_eventually {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {εs : ℕ → ℝ} (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (g : Ω → DistRd d) (V W W' : TopologicalSpace.Opens (Rd d))
    (hWc : IsPreconnected (W : Set (Rd d)))
    (hW'c : IsPreconnected (W' : Set (Rd d)))
    (hWcomp : IsCompact (closure (W : Set (Rd d))))
    (hW'comp : IsCompact (closure (W' : Set (Rd d))))
    (hWV : closure (W : Set (Rd d)) ⊆ V)
    (hW'U : closure (W' : Set (Rd d)) ⊆ extOpen V)
    (H : Ω → Rd d → ℝ)
    (hHcont : ∀ ω, ContinuousOn (H ω) (extOpen V))
    (hind : Indep
      (MeasurableSpace.comap (fun ω => restrictTo (extOpen V) (g ω) -
        ofFunOn (extOpen V) (H ω)) inferInstance)
      (fieldSigmaRd g V) P) :
    ∃ (φ : C(Rd d, ℝ)) (hφsup : tsupport φ ⊆ extOpen V),
      HasCompactSupport φ ∧ ∃ m : ℕ, ∀ k : ℕ,
      let ε := εs (k + m)
      Indep
        (fieldSigmaRd g V ⊔ MeasurableSpace.comap
          (fun ω => internalC (fieldLfppMetric ξ
            ⟨truncMollify κ ε (g ω),
              l2c_continuous_truncMollify hd hκ (hεs (k + m)) (g ω)⟩)
            (fieldLfppMetric_isLength ξ ⟨truncMollify κ ε (g ω),
              l2c_continuous_truncMollify hd hκ (hεs (k + m)) (g ω)⟩)
            W.isOpen hWc) inferInstance)
        (MeasurableSpace.comap (fun ω => restrictTo (extOpen V) (g ω) -
          ofFunOn (extOpen V) (H ω)) inferInstance ⊔ MeasurableSpace.comap
          (fun ω => internalC (fieldLfppMetric ξ
            ⟨truncMollify κ ε
              (g ω - ofCont ⟨fun z => φ z * H ω z,
                l7a_continuous_cutoffH (extOpen V).isOpen φ (H ω)
                  (hHcont ω) hφsup⟩),
              l2c_continuous_truncMollify hd hκ (hεs (k + m)) _⟩)
            (fieldLfppMetric_isLength ξ ⟨truncMollify κ ε
              (g ω - ofCont ⟨fun z => φ z * H ω z,
                l7a_continuous_cutoffH (extOpen V).isOpen φ (H ω)
                  (hHcont ω) hφsup⟩),
              l2c_continuous_truncMollify hd hκ (hεs (k + m)) _⟩)
            W'.isOpen hW'c) inferInstance) P := by
  obtain ⟨φ, U₁, _, hφcomp, hφsup, hU₁open, hW'U₁, hφ1, _, _⟩ :=
    l7a_exists_cutoff_of_isCompact hW'comp (extOpen V).isOpen hW'U
  have hU₁ext : U₁ ⊆ extOpen V := by
    intro z hz
    apply hφsup
    apply subset_tsupport
    change φ z ≠ 0
    rw [hφ1 z hz]
    norm_num
  let U₁o : TopologicalSpace.Opens (Rd d) := ⟨U₁, hU₁open⟩
  obtain ⟨f, _, _, hfcomp, hfsup, _, hWf, hf1, _, _⟩ :=
    l7a_exists_cutoff_of_isCompact hWcomp V.isOpen hWV
  obtain ⟨f', _, _, hf'comp, hf'sup, _, hW'f', hf'1, _, _⟩ :=
    l7a_exists_cutoff_of_isCompact hW'comp hU₁open hW'U₁
  obtain ⟨m₁, hm₁⟩ := l7a_eventually_sqrt_margin
    hfcomp.isCompact V.isOpen hfsup hεt
  obtain ⟨m₂, hm₂⟩ := l7a_eventually_sqrt_margin
    hf'comp.isCompact hU₁open hf'sup hεt
  refine ⟨φ, hφsup, hφcomp, m₁ + m₂, fun k => ?_⟩
  have hleft : ∀ z ∈ Function.support f,
      Metric.closedBall z (Real.sqrt (εs (k + (m₁ + m₂)))) ⊆ V := by
    intro z hz
    have hz' : z ∈ tsupport f := subset_tsupport _ hz
    simpa only [show k + (m₁ + m₂) = (k + m₂) + m₁ by omega] using
      hm₁ (k + m₂) z hz'
  have hright : ∀ z ∈ Function.support f',
      Metric.closedBall z (Real.sqrt (εs (k + (m₁ + m₂)))) ⊆ U₁o := by
    intro z hz
    have hz' : z ∈ tsupport f' := subset_tsupport _ hz
    change Metric.closedBall z (Real.sqrt (εs (k + (m₁ + m₂)))) ⊆ U₁
    simpa only [show k + (m₁ + m₂) = (k + m₁) + m₂ by omega] using
      hm₂ (k + m₁) z hz'
  have hfW : ∀ z ∈ W, f z = 1 := fun z hz =>
    hf1 z (hWf (subset_closure hz))
  have hfW' : ∀ z ∈ W', f' z = 1 := fun z hz =>
    hf'1 z (hW'f' (subset_closure hz))
  exact l7a_indep_markov_truncInternal_stage hd hκ (hεs (k + (m₁ + m₂)))
    ξ P g V U₁o W W' hU₁ext hWc hW'c f f' φ hfW hleft hfW' hright
    hφ1 hφsup H hHcont hind

end HigherDimLQGMetric
