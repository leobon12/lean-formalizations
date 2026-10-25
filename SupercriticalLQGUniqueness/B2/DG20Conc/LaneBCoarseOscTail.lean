import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBCoarseCutoffCost

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

 
theorem laneB_coarse_hatBox_oscillation_tail
    (Q : PsiParams) :
    ∃ C σ2 : ℝ, 0 < C ∧ 0 < σ2 ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (_hW : IsWhiteNoise P W)
        (K : ℕ) (_hK : 6 ≤ K) (x : ℝ) (_hx : 0 ≤ x),
      P.real {ω | ∃ b ∈ j1SourceIdx K (j1SourceRadius Q K),
        ∃ z ∈ T20D.hatBox K b,
          3 * x < |phiMN W P 0 K z ω -
            phiMN W P 0 K (T20.dyCenter K b) ω|} ≤
        C * 4 ^ K * Real.exp (-x ^ 2 / (2 * σ2)) := by
  obtain ⟨C, σ2, hC, hσ2, htail⟩ := j1_phiMN_nearby_oscillation_bad_event
  refine ⟨C, σ2, hC, hσ2, ?_⟩
  intro Ω _ P W hW K hK x hx
  let I := j1SourceIdx K (j1SourceRadius Q K)
  let ι := {b : ℤ × ℤ // b ∈ I}
  have hr : 3 * (2 : ℝ)⁻¹ ^ K ≤ 1 := by
    have hp : (2 : ℝ)⁻¹ ^ K ≤ (2 : ℝ)⁻¹ ^ 2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    norm_num at hp
    linarith
  have hv : ∀ i : ι, T20.dyCenter K i.1 ∈ j1NearbyBox := by
    intro i
    exact j1_nearbyIdx_center
      (j1_sourceIdx_subset_nearbyIdx K (j1SourceRadius Q K) i.property)
  have hA : ∀ i : ι, T20D.hatBox K i.1 ⊆
      closedBall (T20.dyCenter K i.1) (3 * (2 : ℝ)⁻¹ ^ K) := by
    intro i
    exact laneB_hatBox_subset_center_ball K i.1
  have hbound := htail hW K (fun i : ι => T20D.hatBox K i.1)
    (fun i : ι => T20.dyCenter K i.1)
    (3 * (2 : ℝ)⁻¹ ^ K) 3 x hr (by norm_num) hx le_rfl hv hA
  convert hbound using 1
  congr 1
  ext ω
  constructor
  · rintro ⟨b, hb, z, hz, hbad⟩
    exact ⟨⟨b, hb⟩, z, hz, hbad⟩
  · rintro ⟨i, z, hz, hbad⟩
    exact ⟨i.1, i.property, z, hz, hbad⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
