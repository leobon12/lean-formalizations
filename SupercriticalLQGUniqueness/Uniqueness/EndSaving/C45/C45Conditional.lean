import SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45.GridPowerArithmetic




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2

 

theorem c45_corrected_nonempty_of_ae_unique_geodesics
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hGFF : IsNormalizedWholePlaneGFF h P)
    (cMinus cPlus : ℝ≥0∞)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (hstrict : cMinus < cPlus)
    (pbar : Set.Ioo (0 : ℝ) 1) (R : EndSaving.Interfaces.AdmissibleRadii)
    (par : EndSaving.Interfaces.Parameters ξ)
    (family : ∀ z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii →
      ObjectAtV2 P h D D' ξ Q (EndSaving.Interfaces.midpoint cMinus cPlus) par pbar z r)
    (hUnique : ∀ (b : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ),
      K₁.Nonempty → K₂.Nonempty → IsCompact K₁ → IsCompact K₂ →
      Disjoint K₁ K₂ →
      ∀ᵐ ω ∂P, EndSaving.Choices.UniqueGeodesicEventV2 P h D D' ξ Q
        (EndSaving.Interfaces.midpoint cMinus cPlus) par pbar R family b K₁ K₂ ω) :
    C45CorrectedNonemptyInternal P h ξ Q D D' hD hD' hGFF
      cMinus cPlus hMinus hPlus hstrict pbar R par family := by
  intro μ η
  obtain ⟨Ccard, hCcard, hCard⟩ :=
    uniform_fixed_scale_raw_probability_budget P h hGFF D D' ξ Q
      hD hD' cMinus cPlus hstrict hPlus par pbar
  obtain ⟨c₁, hc₁, hChoicesAll⟩ :=
    EndSaving.CorrectedChoices.prop_choices_corrected_of_uniqueGeodesics_v2 ξ Q par η
  obtain ⟨k, hkgt⟩ := exists_nat_gt (((μ : ℝ) + 1 / 2) / c₁)
  have hk : 0 < k := by
    have hμpos : 0 < (μ : ℝ) := μ.property
    have hquot : 0 < ((μ : ℝ) + 1 / 2) / c₁ := by
      exact div_pos (by linarith) hc₁
    exact_mod_cast (lt_trans hquot hkgt)
  have hexp : (μ : ℝ) + 1 / 2 ≤ c₁ * k := by
    have hdiv := (div_lt_iff₀ hc₁).mp hkgt
    linarith
  obtain ⟨εstar, hεstar, hChoices⟩ := hChoicesAll k hk
  have hQ : 0 < Q := EndSaving.InterfaceV2.q_pos_of_weak_metric ξ Q D hD
  obtain ⟨x₀, hx₀, hGrid⟩ := windowGrid_card_le_half_power ξ Q hQ
  let Cterm : ℝ := (max par.Crn 1) ^ k * (Ccard ^ k : ℕ)
  have hCterm : 0 < Cterm := by
    dsimp [Cterm]
    have hbase : 0 < max par.Crn 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hnat : 0 < Ccard ^ k := pow_pos (by omega) _
    exact mul_pos (pow_pos hbase _) (by exact_mod_cast hnat)
  let ε₀real := min (min εstar x₀⁻¹) (1 / 2 : ℝ)
  have hε₀pos : 0 < ε₀real := by
    dsimp [ε₀real]
    exact lt_min (lt_min hεstar (inv_pos.mpr (lt_of_lt_of_le one_pos hx₀))) (by norm_num)
  have hε₀one : ε₀real < 1 :=
    lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  refine ⟨⟨Cterm, hCterm⟩, ⟨ε₀real, hε₀pos, hε₀one⟩, ?_⟩
  intro ε hε hε₀ b K₁ K₂ hK₁ne hK₂ne hK₁ hK₂ hdisj hball₁ hball₂ hsep₁₂ hsep₁b
  have hεstarApply : ε ≤ εstar := hε₀.trans (min_le_left _ _) |>.trans (min_le_left _ _)
  have hε1 : ε ≤ 1 := le_trans hε₀ (le_trans (min_le_right _ _) (by norm_num))
  have hεx : x₀ ≤ ε⁻¹ := by
    have hle : ε ≤ x₀⁻¹ := hε₀.trans (min_le_left _ _) |>.trans (min_le_right _ _)
    exact (le_inv_comm₀ (lt_of_lt_of_le one_pos hx₀) hε).mpr hle
  let G : Set Ω := CountingBadEventV2 h D D' ξ Q cPlus R
    (fun z r hr => (family z r hr).E) b ⟨ε, hε⟩ K₁ K₂
  have hchoice := hChoices P h hGFF D D' hD
    (EndSaving.Interfaces.midpoint cMinus cPlus) cPlus pbar R family b ε hε hεstarApply
    K₁ K₂ hK₁ hK₂ hdisj hball₁ hball₂ hsep₁₂ hsep₁b
  have hchoices : ∀ᵐ ω ∂P, ω ∈ G →
      ∃ (r : Set.Ioi (0 : ℝ)) (hr : r.1 ∈ R.radii),
        ε ^ 2 * (b : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) ≤ ε * (b : ℝ) ∧
        ∃ q : Set.Ioi (0 : ℝ), EndSaving.Interfaces.IsDyadicSize (q : ℝ) ∧
          (1 / 2) * ε ^ (2 * (ξ : ℝ) * (Q + 3)) ≤ (q : ℝ) ∧
          (q : ℝ) ≤ ε ^ ((ξ : ℝ) * min (Q - 3) (2 * (Q - 3))) ∧
          ∃ 𝓕 : Finset (Finset (ℤ × ℤ)),
            (∀ Z ∈ 𝓕, Z.card ≤ k ∧ EndSaving.FiniteEvents.FV2 P h D D' ξ Q
              (EndSaving.Interfaces.midpoint cMinus cPlus) cPlus par pbar r b q K₁ K₂
              (fun i => family (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r hr)
              Z (h ω)) ∧
            ε ^ (-(c₁ * k)) ≤ (𝓕.card : ℝ) := by
    filter_upwards [hchoice, hUnique b K₁ K₂ hK₁ne hK₂ne hK₁ hK₂ hdisj]
      with ω hc hu hG
    exact hc hG hu
  have hbudget (r : Set.Ioi (0 : ℝ)) (hr : r.1 ∈ R.radii)
      (q : Set.Ioi (0 : ℝ)) :
      (∑' Z : Finset (ℤ × ℤ),
        P {ω | EndSaving.Interfaces.Configuration r b K₁ K₂ Z ∧ Z.card ≤ k ∧
          EndSaving.FiniteEvents.FV2 P h D D' ξ Q (EndSaving.Interfaces.midpoint cMinus cPlus) cPlus par pbar
            r b q K₁ K₂
            (fun i => family (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r hr)
            Z (h ω)}) ≤ ENNReal.ofReal Cterm := by
    have hs := hCard r b q K₁ K₂ hK₁ hK₂
      (fun i => family (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r hr) k
    have hfactor : 0 ≤ (max par.Crn 1) ^ k := by positivity
    have hEq : ENNReal.ofReal Cterm =
        ENNReal.ofReal ((max par.Crn 1) ^ k) * (Ccard ^ k : ℕ) := by
      dsimp [Cterm]
      rw [ENNReal.ofReal_mul hfactor]
      simp
    rw [hEq]
    exact hs
  have hcount := counting_event_le_grid_budget_of_choices P h hGFF D D' ξ Q
    (EndSaving.Interfaces.midpoint cMinus cPlus) cPlus hD hD' par pbar R family b
    K₁ K₂ hK₁ hK₂ ε hε hε1 k c₁ hc₁ (ENNReal.ofReal Cterm)
    hbudget G hchoices
  have hgrid := hGrid R b ε hε hεx
  have hpower := grid_budget_le_power hε hε1 hCterm.le hexp hgrid
  exact hcount.trans hpower

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45
