import HigherDimLQGMetric.Limits.ScaleNormalize

/-! Corrected Lemma 3.7: tightness after lower-median normalization. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

theorem l6f_tightScales (hL6a : ∀ d ξ κ, L6a_tight d ξ κ)
    (_hL6b : ∀ d ξ κ, L6b_cross d ξ κ) (_hL2c : L2c_trunc) :
    ∀ d ξ κ, L6f_tightScales d ξ κ := by
  intro d ξ κ hB2 εs hεs hεt Ω _ P _ h Dh hh hDh hstable
  let _ : PolishSpace C(Rd d × Rd d, ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  let _ := TopologicalSpace.upgradeIsCompletelyMetrizable C(Rd d × Rd d, ℝ)
  let c : ℝ → ℝ := fun r => lowerMedian P (fun ω =>
    Real.exp (-ξ * sphereAvg (h ω) r 0) * (Dh ω).1 (0, r • e₁ d))
  let K : Set (ProbabilityMeasure C(Rd d × Rd d, ℝ)) :=
    closure {ν | ∃ ε ∈ Ioo (0 : ℝ) 1,
      (ν : Measure C(Rd d × Rd d, ℝ)) =
        P.map (fun ω => toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)))}
  obtain ⟨m₀, hm₀, hscale⟩ :=
    l6c_normalizedScale_law_in_compact hL6a ξ κ hB2 εs hεs hεt P h Dh hh hDh hstable
  have hpos : ∀ r : ℝ, 0 < r → 0 < c r := by
    intro r hr
    apply l6c_scaleMedian_pos
      (by obtain ⟨_, hQ, _⟩ := hB2
          exact lt_of_lt_of_le (by norm_num : 0 < 2) hQ.dim)
      ξ P h hh.1.measurable Dh hDh hr
  let S : Set (ProbabilityMeasure C(Rd d × Rd d, ℝ)) :=
    {ρ | ∃ r ∈ Ioi (0 : ℝ),
      (ρ : Measure C(Rd d × Rd d, ℝ)) =
        P.map (fun ω => normalizedAtScale ξ (fun _ => Dh ω) c (h ω) r)}
  let K' : Set (ProbabilityMeasure C(Rd d × Rd d, ℝ)) :=
    {ρ | ∃ s ∈ Icc 1 m₀⁻¹, ∃ ν ∈ K, ρ = ν.map (fun D => s • D)}
  have hA := (hL6a d ξ κ) hB2 P h hh.1.isLGFPlusBddCont
  have hK : IsCompact K := by
    apply isCompact_closure_of_isTightMeasureSet
    refine hA.2.2.1.subset ?_
    rintro μ ⟨ν, hν, rfl⟩
    exact hν
  have hK' : IsCompact K' := l6c_isCompact_scaled_laws K hK 1 m₀⁻¹
  have hS : S ⊆ K' := by
    intro ρ hρ
    obtain ⟨r, hr, hρ⟩ := hρ
    obtain ⟨ρ', hρ', s, hs, ν, hν, heq⟩ := hscale r hr
    have : ρ = ρ' := Subtype.ext (hρ.trans hρ'.symm)
    rw [this, heq]
    exact ⟨s, hs, ν, hν, rfl⟩
  have hgoodK' : ∀ ρ ∈ K',
      ∀ᵐ D ∂(ρ : Measure C(Rd d × Rd d, ℝ)),
        IsContinuousMetric D ∧ IsProperFn D := by
    intro ρ hρ
    obtain ⟨s, hs, ν, hν, rfl⟩ := hρ
    have hsp : 0 < s := lt_of_lt_of_le zero_lt_one hs.1
    let e : C(Rd d × Rd d, ℝ) ≃ᵐ C(Rd d × Rd d, ℝ) :=
      (Homeomorph.smulOfNeZero s hsp.ne').toMeasurableEquiv
    have hgood : ∀ᵐ D ∂(ν : Measure C(Rd d × Rd d, ℝ)),
        IsContinuousMetric (e D) ∧ IsProperFn (e D) := by
      filter_upwards [hA.2.2.2 ν hν] with D hD
      exact l6c_good_smul D hD hsp
    change {D : C(Rd d × Rd d, ℝ) |
      IsContinuousMetric D ∧ IsProperFn D} ∈
      ae ((ν : Measure C(Rd d × Rd d, ℝ)).map (e : _ → _))
    rw [← e.map_ae]
    exact Filter.eventually_map.mpr hgood
  refine ⟨hpos, ?_, ?_, ?_⟩
  · intro r hr
    have hs : Measurable (fun ω =>
        (c r)⁻¹ * Real.exp (-ξ * sphereAvg (h ω) r 0)) :=
      measurable_const.mul (Real.measurable_exp.comp
        (measurable_const.mul ((measurable_sphereAvg_left r 0).comp hh.1.measurable)))
    exact (hs.smul ((ContinuousMap.continuous_precomp _).measurable.comp
      (measurable_subtype_coe.comp hDh))).aemeasurable
  · have hcomp : IsCompact (closure S) :=
      hK'.of_isClosed_subset isClosed_closure (closure_minimal hS hK'.isClosed)
    have htight := isTightMeasureSet_of_isCompact_closure hcomp
    refine htight.subset ?_
    rintro μ ⟨r, hr, rfl⟩
    obtain ⟨ρ, hρ, _, _, _, _, _⟩ := hscale r hr
    exact ⟨ρ, ⟨r, hr, hρ⟩, hρ⟩
  · intro μ hμ
    exact hgoodK' μ (closure_minimal hS hK'.isClosed hμ)

end HigherDimLQGMetric
