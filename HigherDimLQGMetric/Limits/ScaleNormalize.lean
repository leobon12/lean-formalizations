import HigherDimLQGMetric.Limits.ScaleProper

/-! Median normalization of a fixed-radius limit law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

/-- At every positive radius the median-normalized limit law is in one compact
family of positive scalar multiples of the original LFPP limit laws. -/
theorem l6c_normalizedScale_law_in_compact
    (hL6a : ∀ d ξ κ, L6a_tight d ξ κ)
    {d : ℕ} (ξ : ℝ) (κ : Rd d → ℝ)
    (hB2 : ∃ Q : ℝ, DGZ.DGZHyp d κ ξ Q ∧ DGZ.RealEpsAdapterShape d κ ξ Q)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n) (hεt : Tendsto εs atTop (𝓝 0))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (Dh : Ω → ContMetric d)
    (hh : IsNormalizedLGF h P) (hDh : Measurable Dh)
    (hstable : StablyTendstoLU P h
      (fun n ω => lfppSeq κ ξ εs (h ω) n) (fun ω => (Dh ω).1)) :
    let K : Set (ProbabilityMeasure C(Rd d × Rd d, ℝ)) :=
      closure {ν | ∃ ε ∈ Ioo (0 : ℝ) 1,
        (ν : Measure C(Rd d × Rd d, ℝ)) =
          P.map (fun ω => toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)))}
    let c : ℝ → ℝ := fun r => lowerMedian P (fun ω =>
      Real.exp (-ξ * sphereAvg (h ω) r 0) * (Dh ω).1 (0, r • e₁ d))
    ∃ m₀ : ℝ, 0 < m₀ ∧ ∀ r : ℝ, 0 < r →
      ∃ ρ : ProbabilityMeasure C(Rd d × Rd d, ℝ),
        (ρ : Measure C(Rd d × Rd d, ℝ)) =
          P.map (fun ω => normalizedAtScale ξ (fun _ => Dh ω) c (h ω) r) ∧
        ∃ s ∈ Set.Icc 1 m₀⁻¹, ∃ ν ∈ K,
          ρ = ν.map (fun D => s • D) := by
  let _ : PolishSpace C(Rd d × Rd d, ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  intro K c
  obtain ⟨m₀, hm₀, hmK⟩ := l6c_uniform_lfppMedian_pos hL6a ξ κ hB2 P h hh
  refine ⟨m₀, hm₀, ?_⟩
  intro r hr
  have hc : 0 < c r := l6c_scaleMedian_pos (by
    obtain ⟨_, hQ, _⟩ := hB2
    exact lt_of_lt_of_le (by norm_num : 0 < 2) hQ.dim) ξ P h hh.1.measurable Dh hDh hr
  let Z : Ω → C(Rd d × Rd d, ℝ) := fun ω =>
    Real.exp (-ξ * sphereAvg (h ω) r 0) •
      (Dh ω).1.comp ⟨fun p : Rd d × Rd d => (r • p.1, r • p.2), by fun_prop⟩
  have hZm : Measurable Z := by
    have hs : Measurable (fun ω => Real.exp (-ξ * sphereAvg (h ω) r 0)) :=
      Real.measurable_exp.comp (measurable_const.mul
        ((measurable_sphereAvg_left r 0).comp hh.1.measurable))
    exact hs.smul ((ContinuousMap.continuous_precomp _).measurable.comp
      (measurable_subtype_coe.comp hDh))
  obtain ⟨η, hη, β, hβ, hν⟩ :=
    l6c_scaleLimit_law_in_closure hL6a ξ κ hB2 εs hεs hεt P h Dh hh hDh hstable hr
  let ν := η.map (fun D => β • D)
  have hmedη : lowerMedian (η : Measure C(Rd d × Rd d, ℝ))
      (fun D => D (0, e₁ d)) = c r := by
    rw [hη]
    rw [l6c_lowerMedian_map hZm.aemeasurable (continuous_eval_const _).measurable]
    congr 1
    funext ω
    simp [Z]
  have hmedν : lowerMedian (ν : Measure C(Rd d × Rd d, ℝ))
      (fun D => D (0, e₁ d)) = β * c r := by
    rw [l6c_lowerMedian_law_smul η hβ, hmedη]
  have hmlo : m₀ ≤ β * c r := by rw [←hmedν]; exact hmK ν hν
  have hmhi : β * c r ≤ 1 := by
    rw [←hmedν]
    exact l6c_lfppMedian_le_one hL6a ξ κ hB2 P h hh ν hν
  let s := (β * c r)⁻¹
  have hprod : 0 < β * c r := mul_pos hβ hc
  have hs : s ∈ Set.Icc 1 m₀⁻¹ := by
    dsimp [s]
    constructor
    · exact one_le_inv_iff₀.mpr ⟨hprod, hmhi⟩
    · exact (inv_le_inv₀ hprod hm₀).mpr hmlo
  let ρ := ν.map (fun D => s • D)
  have hmap : (ρ : Measure C(Rd d × Rd d, ℝ)) =
      P.map (fun ω => normalizedAtScale ξ (fun _ => Dh ω) c (h ω) r) := by
    dsimp only [ρ, ν]
    rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
      Measure.map_map, hη, Measure.map_map]
    · apply Measure.map_congr
      filter_upwards with ω
      ext p
      have hsc : s * β = (c r)⁻¹ := by
        dsimp [s]
        field_simp
      change s * (β * (Real.exp (-ξ * sphereAvg (h ω) r 0) *
        (Dh ω).1 (r • p.1, r • p.2))) =
        ((c r)⁻¹ * Real.exp (-ξ * sphereAvg (h ω) r 0)) *
          (Dh ω).1 (r • p.1, r • p.2)
      rw [← mul_assoc, hsc, mul_assoc]
    · fun_prop
    · exact hZm
    · fun_prop
    · fun_prop
  exact ⟨ρ, hmap, s, hs, ν, hν, rfl⟩

end HigherDimLQGMetric
