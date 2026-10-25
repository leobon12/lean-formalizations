import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPhysicalUpperLeft
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPhysicalScaleWitness
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCLargeKScale
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCVerticalEndpoint

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise
universe u

theorem laneC_largeK_upper_left_resampling_le_source_around
    (Q : PsiParams) (hR : Q.r₀ ≤ (1 : ℝ) / 100)
    (hε : Q.ε₀ ≤ (1 : ℝ) / 100) (ξ : ℝ) :
    ∃ K₀ : ℕ, ∀ {Ω : Type u} [MeasurableSpace Ω]
      (P : Measure Ω) (W : WNSpace → Ω → ℝ),
      ∀ hW : IsWhiteNoise P W, ∀ n K m : ℕ,
      K₀ ≤ K → K ≤ n → m + 1 ≤ K →
      (2 : ℝ) ^ ((m : ℝ) - 1) < (K : ℝ) ^ Q.ε₀ →
      (K : ℝ) ^ Q.ε₀ ≤ (2 : ℝ) ^ m →
      ∀ᵐ z ∂(P.prod P), ∀ b ∈ T20B.nearIdx K,
        let c := T20.dyCenter K b
        let r := LaneCInputs.sourceRadius K m
        0 ≤ c.re → c.re ≤ r →
        c.im ≤ 1 → 1 - c.im ≤ r →
        2 * r ≤ c.im → c.re + 2 * r ≤ 1 →
        ∀ γ : ℝ → ℂ,
        AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁
          (rectAB 1 1).side₂ γ →
        lfppLen ξ (fun x => psiMN Q W P 0 n x z.1) γ ≠ ⊤ →
        ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → dist (γ t) c ≤ r →
        let D := lfppContMetric ξ (fun x => psiMN Q W P 0 n x z.1)
          ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont z.1)
        D.aroundDist (LaneCInputs.sourceAround K m b)
          (LaneCInputs.sourceInner K m b)
          (LaneCInputs.sourceOuter K m b) ≠ ⊤ →
        (rectLen ξ (fun x => psiMN Q W P 0 n x z.1 -
          T20B.blkKn Q W P K n b x z.1 +
            T20B.blkKn Q W P K n b x z.2) (rectAB 1 1)).toReal ≤
          (lfppLen ξ (fun x => psiMN Q W P 0 n x z.1) γ).toReal +
            (D.aroundDist (LaneCInputs.sourceAround K m b)
              (LaneCInputs.sourceInner K m b)
              (LaneCInputs.sourceOuter K m b)).toReal := by
  obtain ⟨Kσ, hKσ⟩ := laneC_eventual_physical_scale_witness Q hR hε
  refine ⟨max 8 Kσ, ?_⟩
  intro Ω _ P W hW n K m hK hKn hmK hmLo hmHi
  obtain ⟨s, hσ, hr⟩ := hKσ K m n (le_trans (le_max_right _ _) hK)
    hKn hmK hmHi
  have hr0 : 0 < LaneCInputs.sourceRadius K m := by
    unfold LaneCInputs.sourceRadius
    positivity
  filter_upwards [laneC_physical_upper_left_resampling_le_around
      hW Q ξ hKn hσ hr hr0] with z hz
  intro b hb
  dsimp only
  intro hc0 hcr hci hct hcb hcright γ hγ hγfin t ht hmid hfinite
  have hγside : γ 1 ∈ (rectAB 1 1).side₂ := by
    obtain ⟨_, _, z₁, hz₁, hpath, _⟩ := hγ
    simpa only [hpath.target] using hz₁
  exact hz b hb hc0 hcr hci hct hcb hcright γ hγ hγfin t ht hmid
    (laneC_right_endpoint_outer_of_center_buffer hcright hγside) hfinite

end SupercriticalLQGUniqueness.B2.DG20Conc
