import HigherDimLQGMetric.Markov.Residual

/-! The continuous measurable harmonic part and independent residual of the Markov split. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace Filter
open scoped RealInnerProductSpace Topology
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}

/-- Core of D-M: continuity, measurability from the interior, and independence of the
distribution-valued exterior residual. -/
theorem markov_exists_decomp_core (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    (V : Opens (Rd d)) (z : Rd d) (r : ℝ)
    (hVb : Bornology.IsBounded (V : Set (Rd d)))
    (hr : 0 < r) (hVr : Metric.sphere z r ⊆ V) :
    ∃ H : Ω → Rd d → ℝ,
      (∀ ω, ContinuousOn (H ω) (extOpen V)) ∧
      (∃ G : Ω → Rd d → ℝ,
        Measurable[fieldSigmaRd (markovSphereField h z r) V] G ∧ H =ᵐ[P] G) ∧
      Indep (MeasurableSpace.comap
        (fun ω => restrictTo (extOpen V) (markovSphereField h z r ω) -
          ofFunOn (extOpen V) (H ω)) inferInstance)
        (fieldSigmaRd (markovSphereField h z r) V) P := by
  have hdr : 1 ≤ d := by omega
  have hVr' : Metric.sphere z |r| ⊆ V := by
    simpa only [abs_of_pos hr] using hVr
  obtain ⟨ρ, hρ, hρV⟩ := markov_exists_inner_normalizer hdr V z r hVr'
  obtain ⟨Y, hYc, hYm, hYae⟩ :=
    markov_exists_pointVersion hdr hh V hVb hρ hρV
  let q : Ω → ℝ := markovSphereCorrection h z r ρ
  let H : Ω → Rd d → ℝ := markovSphereHarmonic V Y q
  let R : Ω → DistOn (extOpen V) := markovSphereResidual (h := h) V z r ρ Y
  have hHc (ω : Ω) : ContinuousOn (H ω) (extOpen V) :=
    markovSphereHarmonic_continuousOn V Y q hYc ω
  have hH0 (ω : Ω) (x : Rd d) (hx : x ∉ extOpen V) : H ω x = 0 := by
    classical
    simp [H, markovSphereHarmonic, hx]
  have hqm : Measurable[fieldSigmaRd (markovSphereField h z r) V] q :=
    markov_measurable_sphereCorrection V z r hρV
  have hHpoint (x : Rd d) (hx : x ∈ extOpen V) :
      AEStronglyMeasurable[fieldSigmaRd (markovSphereField h z r) V]
        (fun ω => H ω x) P := by
    have hp : AEStronglyMeasurable[fieldSigmaRd (markovSphereField h z r) V]
        (fun ω => Y ω x) P :=
      (markov_pointVec_ae_sphereMeas hdr hh V hVb z r hρ hρV x hx).congr
        (hYae x hx).symm
    have hs : AEStronglyMeasurable[fieldSigmaRd (markovSphereField h z r) V]
        (fun ω => Y ω x + q ω) P := hp.add hqm.aestronglyMeasurable
    exact hs.congr (Filter.Eventually.of_forall fun ω => by
      classical
      simp [H, markovSphereHarmonic, hx])
  obtain ⟨G, hGm, hHGeq⟩ := markov_exists_measurable_contVersion P
    (fieldSigmaRd (markovSphereField h z r) V) (extOpen V) H hHc hH0 hHpoint
  have hRm : Measurable R :=
    markov_measurable_sphereResidual hh V z r ρ Y hYc hYm
  have hRpair (ψ : TestOn (extOpen V)) :
      (fun ω => R ω ψ) =ᵐ[P] (markovResidualVec hh V hρ ψ : Ω → ℝ) :=
    markov_sphereResidual_pair_ae hdr hh V hVb hρ hρV Y hYc hYm hYae z r ψ
  have hind : Indep (MeasurableSpace.comap R inferInstance)
      (fieldSigmaRd (markovSphereField h z r) V) P := by
    exact markov_indep_residual_sphere_field hd hh V z hr hVr hρ R hRm hRpair
  refine ⟨H, hHc, ⟨G, hGm, hHGeq⟩, ?_⟩
  exact hind

end HigherDimLQGMetric
