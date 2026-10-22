import HigherDimLQGMetric.Determ.LawTransfer

/-! Tight centered metric laws transfer to canonical copies. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

/-- The centered scaled metric is Borel as a function of the field–metric pair. -/
theorem determ_measurable_scaledPair {d : ℕ} (ξ : ℝ) (c : ℝ → ℝ)
    (r : ℝ) (z : Rd d) : Measurable
      (fun t : DistRd d × ContMetric d => scaledField ξ (fun _ => t.2) c r z t.1) := by
  have h1 : Measurable fun t : DistRd d × ContMetric d =>
      t.2.1.comp ⟨fun p : Rd d × Rd d =>
        (r • p.1 + z, r • p.2 + z), by fun_prop⟩ :=
    (ContinuousMap.continuous_precomp _).measurable.comp
      (measurable_subtype_coe.comp measurable_snd)
  have h2 : Measurable fun t : DistRd d × ContMetric d =>
      (c r)⁻¹ * Real.exp (-ξ * sphereAvg t.1 r z) :=
    measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul ((measurable_sphereAvg_left r z).comp measurable_fst)))
  exact h2.smul h1

/-- Equal field–metric laws give equal laws for every centered scaled metric. -/
theorem determ_scaled_law_transfer {d : ℕ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    (h : Ω → DistRd d) (D : Ω → ContMetric d)
    (h' : Ω' → DistRd d) (D' : Ω' → ContMetric d)
    (hh : Measurable h) (hD : Measurable D)
    (hh' : Measurable h') (hD' : Measurable D')
    (hlaw : P.map (fun ω => (h ω, D ω)) = P'.map (fun ω => (h' ω, D' ω)))
    (ξ : ℝ) (c : ℝ → ℝ) (r : ℝ) (z : Rd d) :
    P.map (fun ω => scaledField ξ (fun _ => D ω) c r z (h ω)) =
      P'.map (fun ω => scaledField ξ (fun _ => D' ω) c r z (h' ω)) := by
  let F : DistRd d × ContMetric d → C(Rd d × Rd d, ℝ) :=
    fun t => scaledField ξ (fun _ => t.2) c r z t.1
  have hF : Measurable F := determ_measurable_scaledPair ξ c r z
  calc
    P.map (fun ω => scaledField ξ (fun _ => D ω) c r z (h ω)) =
        (P.map (fun ω => (h ω, D ω))).map F := by
          rw [Measure.map_map hF (hh.prodMk hD)]
          rfl
    _ = (P'.map (fun ω => (h' ω, D' ω))).map F := by rw [hlaw]
    _ = P'.map (fun ω => scaledField ξ (fun _ => D' ω) c r z (h' ω)) := by
          rw [Measure.map_map hF (hh'.prodMk hD')]
          rfl

/-- TightFamily only depends on the measurable marginal laws of its members. -/
theorem determ_tightFamily_law_transfer {d : ℕ} {ι Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    (X : ι → Ω → C(Rd d × Rd d, ℝ))
    (Y : ι → Ω' → C(Rd d × Rd d, ℝ)) (S : Set ι)
    (hT : TightFamily P X S)
    (hYm : ∀ i ∈ S, AEMeasurable (Y i) P')
    (hLaw : ∀ i ∈ S, P.map (X i) = P'.map (Y i)) :
    TightFamily P' Y S := by
  have hset : {μ | ∃ i ∈ S, μ = P.map (X i)} =
      {μ | ∃ i ∈ S, μ = P'.map (Y i)} := by
    ext μ
    constructor
    · rintro ⟨i, hi, hμ⟩
      exact ⟨i, hi, by rw [← hLaw i hi]; exact hμ⟩
    · rintro ⟨i, hi, hμ⟩
      exact ⟨i, hi, by rw [hLaw i hi]; exact hμ⟩
  have hprob : {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
        ∃ i ∈ S, (ν : Measure C(Rd d × Rd d, ℝ)) = P.map (X i)} =
      {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
        ∃ i ∈ S, (ν : Measure C(Rd d × Rd d, ℝ)) = P'.map (Y i)} := by
    ext ν
    constructor
    · rintro ⟨i, hi, hν⟩
      exact ⟨i, hi, by rw [← hLaw i hi]; exact hν⟩
    · rintro ⟨i, hi, hν⟩
      exact ⟨i, hi, by rw [hLaw i hi]; exact hν⟩
  refine ⟨hYm, ?_, ?_⟩
  · rw [← hset]
    exact hT.2.1
  · intro μ hμ
    exact hT.2.2 μ (by simpa only [hprob] using hμ)

end HigherDimLQGMetric
