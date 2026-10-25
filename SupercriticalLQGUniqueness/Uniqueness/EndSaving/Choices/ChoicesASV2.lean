import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.ChoicesV2




 











set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Finset Filter
open scoped ENNReal Topology

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices

open LQGMetric (DistC TestC)

 

def UniqueGeodesicEventV2 {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1) (R : EndSaving.Interfaces.AdmissibleRadii)
    (family : ∀ z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii →
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar z r)
    (b : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ) (ω : Ω) : Prop :=
  (∃ P : ℝ → ℂ, ∃ T : ℝ, EndSaving.FiniteEvents.UniqueSetGeodesic (D (h ω)) K₁ K₂ P T) ∧
    ∀ (r : Set.Ioi (0 : ℝ)) (hr : r.1 ∈ R.radii) (W : Finset (ℤ × ℤ)),
      EndSaving.Interfaces.Configuration r b K₁ K₂ W → W.Nonempty → ∃ P : ℝ → ℂ, ∃ T : ℝ,
        EndSaving.FiniteEvents.UniqueSetGeodesic (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r
          (fun i => family (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r hr) W (h ω))) K₁ K₂ P T

 
theorem prop_choices_of_uniqueGeodesics_v2 (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (par : EndSaving.Interfaces.Parameters ξ) (η : Set.Ioo (0 : ℝ) 1) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ k : ℕ, 0 < k → ∃ εstar : ℝ, 0 < εstar ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h μ →
      ∀ (D D' : DistC → LSCMetric), IsWeakLQGMetric ξ Q D →
      ∀ (cMid : ℝ) (cPlus : ℝ≥0∞) (pbar : Set.Ioo (0 : ℝ) 1) (R : EndSaving.Interfaces.AdmissibleRadii)
        (family : ∀ z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii →
          EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar z r)
        (b : Set.Ioi (0 : ℝ)) (ε : ℝ) (hε : 0 < ε), ε ≤ εstar →
      ∀ K₁ K₂ : Set ℂ, IsCompact K₁ → IsCompact K₂ → Disjoint K₁ K₂ →
        K₁ ⊆ ball (0 : ℂ) (2 * (b : ℝ)) → K₂ ⊆ ball (0 : ℂ) (2 * (b : ℝ)) →
        ENNReal.ofReal ((η : ℝ) * (b : ℝ)) ≤ EndSaving.Interfaces.euclidSetDist K₁ K₂ →
        ENNReal.ofReal ((η : ℝ) * (b : ℝ)) ≤ EndSaving.Interfaces.euclidSetDist K₁ (sphere (0 : ℂ) b) →
        ∀ᵐ ω ∂μ, ω ∈ EndSaving.InterfaceV2.PrintedCountingBadEventV2 h D D' ξ Q cPlus R
            (fun z r hr => (family z r hr).E) b ⟨ε, hε⟩ K₁ K₂ →
          UniqueGeodesicEventV2 μ h D D' ξ Q cMid par pbar R family b K₁ K₂ ω →
          ∃ (r : Set.Ioi (0 : ℝ)) (hr : r.1 ∈ R.radii),
            ε ^ 2 * (b : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) ≤ ε * (b : ℝ) ∧
            ∃ q : Set.Ioi (0 : ℝ), EndSaving.Interfaces.IsDyadicSize (q : ℝ) ∧
              (1 / 2) * ε ^ (2 * (ξ : ℝ) * (Q + 3)) ≤ (q : ℝ) ∧
              (q : ℝ) ≤ ε ^ ((ξ : ℝ) * (Q - 3)) ∧
              ∃ 𝓕 : Finset (Finset (ℤ × ℤ)),
                (∀ Z ∈ 𝓕, Z.card ≤ k ∧ EndSaving.FiniteEvents.FV2 μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂
                  (fun i => family (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r hr) Z (h ω)) ∧
                ε ^ (-(c₁ * k)) ≤ (𝓕.card : ℝ) := by
  have hcs := cSub_pos ξ par
  refine ⟨cSub ξ par / 2, by positivity, ?_⟩
  intro k hk
  set ck := ckConst k (cSub ξ par) with hck
  have hck0 : 0 < ck := ckConst_pos k (cSub ξ par)
  have hkpos : (0 : ℝ) < cSub ξ par * k := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  set a₀ := (1 / ck) ^ ((cSub ξ par * k)⁻¹) with ha₀
  have ha₀0 : 0 ≤ a₀ := Real.rpow_nonneg (by positivity) _
  set A := max (2 * k : ℝ) a₀ + 1 with hA
  have hA1 : 1 ≤ A := by
    have h1 := le_max_left (2 * k : ℝ) a₀
    have h2 : (0 : ℝ) ≤ 2 * k := by positivity
    linarith
  have hA2k : (2 * k : ℝ) ≤ A := by have := le_max_left (2 * k : ℝ) a₀; linarith
  have hAc : 1 / ck ≤ A ^ (cSub ξ par * k) := by
    have hle : a₀ ≤ A := by have := le_max_right (2 * k : ℝ) a₀; linarith
    calc 1 / ck = a₀ ^ (cSub ξ par * k) := by
          rw [ha₀, Real.rpow_inv_rpow (by positivity) hkpos.ne']
      _ ≤ A ^ (cSub ξ par * k) := Real.rpow_le_rpow ha₀0 hle hkpos.le
  by_cases hQ : 0 < Q
  · obtain ⟨x₀, hx₀1, hfib⟩ := fiber_bound_eventually ξ.property hQ η.property.1 A
      (by linarith)
    refine ⟨min ((η : ℝ) / 1000) x₀⁻¹, lt_min (by have := η.property.1; positivity)
      (by positivity), ?_⟩
    intro Ω _ μ _ h hh D D' hD cMid cPlus pbar R family b ε hε hεs K₁ K₂ hK₁ _ _ hball₁ _
      hsep₁₂ hsep₁b
    have hregR : ∀ᵐ ω ∂μ, ∀ (r : Set.Ioi (0 : ℝ)) (hr : r ∈ {r : Set.Ioi (0 : ℝ) | r.1 ∈ R.radii}),
        SampleRegularV2 μ h D D' ξ Q cMid par pbar r
          (fun i => family (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r hr) ω := by
      rw [ae_ball_iff (admissible_countable R)]
      intro r hr
      exact ae_sampleRegularV2 μ h hh D D' ξ Q cMid hD par pbar r _
    filter_upwards [ae_regularAt_self hD μ h hh, hregR] with ω hreg0 hreg hG hU
    have hεη : ε ≤ (η : ℝ) / 1000 := hεs.trans (min_le_left _ _)
    have hεx : x₀ ≤ ε⁻¹ := by
      have h1 : ε ≤ x₀⁻¹ := hεs.trans (min_le_right _ _)
      have hx₀0 : 0 < x₀ := lt_of_lt_of_le one_pos hx₀1
      exact (le_inv_comm₀ hx₀0 hε).mpr h1
    obtain ⟨r, hr, hrlo, hrhi, q, hqd, hqlo, hqhi, 𝓕, h𝓕, hcount⟩ :=
      prop_choices_pathwise μ h D D' ξ Q cMid cPlus par pbar R family η k hk A hA1 hA2k hAc
        x₀ hfib b ε hε hεη hεx K₁ K₂ hK₁ hball₁ hsep₁₂ hsep₁b ω hG hreg0
        (fun r hr => hreg r hr) hU.1 hU.2
    refine ⟨r, hr, hrlo, hrhi, q, hqd, hqlo, hqhi, 𝓕, h𝓕, ?_⟩
    rw [Real.rpow_neg hε.le, ← Real.inv_rpow hε.le]
    exact hcount
  · refine ⟨1, one_pos, ?_⟩
    intro Ω _ μ _ h hh D D' hD
    exact absurd (EndSaving.InterfaceV2.q_pos_of_weak_metric ξ Q D hD) hQ


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices
