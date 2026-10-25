import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBGlueBoxGeometry

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric MeasureTheory

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

theorem laneB_glueBox_coarse_oscillation_tail :
    ∃ C σ2 : ℝ, 0 < C ∧ 0 < σ2 ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
        {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
      ∀ K : ℕ, 3 ≤ K → ∀ x : ℝ, 0 ≤ x →
      P.real {ω | ∃ b ∈ T20.blkIdx K,
        ∃ z ∈ S6U.glueBox K b,
          7 * x < |phiMN W P 0 K z ω -
            phiMN W P 0 K (T20.dyCenter K b) ω|} ≤
        C * 4 ^ K * Real.exp (-x ^ 2 / (2 * σ2)) := by
  obtain ⟨C, σ2, hC, hσ2, htail⟩ :=
    j1_phiMN_nearby_oscillation_bad_event
  refine ⟨C, σ2, hC, hσ2, ?_⟩
  intro Ω _ P W hW K hK x hx
  have hK2 : 2 ≤ K := by omega
  have hr : 7 * (2 : ℝ)⁻¹ ^ K ≤ 1 := by
    have hpow : (2 : ℝ)⁻¹ ^ K ≤ (2 : ℝ)⁻¹ ^ 3 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hK
    norm_num at hpow
    nlinarith
  let ι := {b : ℤ × ℤ // b ∈ T20.blkIdx K}
  let A : ι → Set ℂ := fun b => S6U.glueBox K b.1
  let v : ι → ℂ := fun b => T20.dyCenter K b.1
  have h := htail hW K A v (7 * (2 : ℝ)⁻¹ ^ K) 7 x hr
    (by norm_num) hx (by rfl)
    (fun b => laneB_blkIdx_center_nearby hK2 b.2)
    (fun b => laneB_glueBox_subset_center_ball hK2 b.2)
  have heq : {ω : Ω | ∃ b ∈ T20.blkIdx K,
      ∃ z ∈ S6U.glueBox K b,
        7 * x < |phiMN W P 0 K z ω -
          phiMN W P 0 K (T20.dyCenter K b) ω|} =
      {ω : Ω | ∃ i : ι, ∃ z ∈ A i,
        7 * x < |phiMN W P 0 K z ω - phiMN W P 0 K (v i) ω|} := by
    ext ω
    constructor
    · rintro ⟨b, hb, z, hz, hd⟩
      exact ⟨⟨b, hb⟩, z, hz, hd⟩
    · rintro ⟨⟨b, hb⟩, z, hz, hd⟩
      exact ⟨b, hb, z, hz, hd⟩
  rw [heq]
  exact h

end SupercriticalLQGUniqueness.B2.DG20Conc
