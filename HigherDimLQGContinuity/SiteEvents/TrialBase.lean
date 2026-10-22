import HigherDimLQGContinuity.SiteEvents.RefsLocal
import HigherDimLQGContinuity.Favorable.Lemma34
import HigherDimLQGContinuity.Caps.ShellEvents

/-! The favorable seed event before spatial recentering. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory Set Metric
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

def seedTrialEvent (D E : DistRd d → ContMetric d)
    (v H₀ σ₀ β₀ m M Hsd σsd : ℝ) : Set (DistRd d) :=
  Hdown D E (1 + 2 * v) ∩
    {g | SeedRefs H₀ σ₀ β₀ m M Hsd σsd (rho D g) (rho E g)}

/-- Both extra doubled-ball failures cost at most `pstar/8` in total. -/
theorem seedTrial_base_prob (_hd : 2 ≤ d) {ξ η ξbar v pstar v₀ C₄ c₄ H₀ σ₀ β₀ m M Hsd σsd : ℝ}
    (hpstar : 0 < pstar)
    (hmain : ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ η ∈ Ioc (0 : ℝ) ξbar,
      ∀ D E : DistRd d → ContMetric d,
      IsStrongExpMetric d ξ (distExp d ξ) D →
      IsStrongExpMetric d η (distExp d η) E →
      ∀ v : ℝ, 0 < v → v < v₀ → |η - ξ| ≤ c₄ * v ^ C₄ →
        ENNReal.ofReal (pstar / 2) ≤
          pinLaw d 1 (Hdown D E (1 + 2 * v) ∩ PairRefs D E H₀ σ₀ β₀ m M))
    (hDUp : ∀ ζ ∈ Ioc (0 : ℝ) ξbar, ∀ F : DistRd d → ContMetric d,
      IsStrongExpMetric d ζ (distExp d ζ) F →
        pinLaw d 1 {g | ¬ DUpper (rho F g) (siteA d) Hsd σsd} ≤
          ENNReal.ofReal (pstar / 16))
    (hξ : ξ ∈ Ioc (0 : ℝ) ξbar) (hη : η ∈ Ioc (0 : ℝ) ξbar)
    (D E : DistRd d → ContMetric d)
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    (hE : IsStrongExpMetric d η (distExp d η) E)
    (hv : 0 < v) (hvv : v < v₀) (hτ : |η - ξ| ≤ c₄ * v ^ C₄) :
    ENNReal.ofReal (pstar / 4) ≤
      pinLaw d 1 (seedTrialEvent D E v H₀ σ₀ β₀ m M Hsd σsd) := by
  have h2 := hmain ξ hξ η hη D E hD hE v hv hvv hτ
  have h3 := p8a_measure_inter_ge (pinLaw d 1) (by positivity) h2
    (hDUp ξ hξ D hD)
  have h4 := p8a_measure_inter_ge (pinLaw d 1) (by positivity) h3
    (hDUp η hη E hE)
  refine le_trans (ENNReal.ofReal_le_ofReal (by linarith)) (h4.trans (measure_mono ?_))
  rintro g ⟨⟨⟨hdn, hR⟩, hDD⟩, hDE⟩
  exact ⟨hdn, hR.1, hR.2, hDD, hDE⟩

/-- The seed event is local to the larger annulus required in Part B. -/
theorem seedTrial_base_local (hd : 2 ≤ d) {ξ η v H₀ σ₀ β₀ m M Hsd σsd : ℝ}
    (hξ : 0 < ξ) (hη : 0 < η)
    {D E : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    (hE : IsStrongExpMetric d η (distExp d η) E)
    (hHsd : 0 ≤ Hsd) (hσsd : 0 ≤ σsd) :
    AEEventIn (pinLaw d 1) (fieldSigma0 id (ann (0 : Rd d) (1 / 2) 4))
      (seedTrialEvent D E v H₀ σ₀ β₀ m M Hsd σsd) := by
  obtain ⟨hdn, _, hrefs⟩ := local_events_aeEventIn_of_subset hd hξ hη hD hE
    one_pos (isOpen_ann _ _ _) q10_siteA_subset_ann4
      q10_pinSphere_subset_ann4 (1 + 2 * v) H₀ σ₀ β₀ m M
  have hdupD := dupper_aeEventIn hd hξ hD hHsd hσsd
  have hdupE := dupper_aeEventIn hd hη hE hHsd hσsd
  have hset : seedTrialEvent D E v H₀ σ₀ β₀ m M Hsd σsd =
      (Hdown D E (1 + 2 * v) ∩ PairRefs D E H₀ σ₀ β₀ m M) ∩
        ({g | DUpper (rho D g) (siteA d) Hsd σsd} ∩
          {g | DUpper (rho E g) (siteA d) Hsd σsd}) := by
    ext g
    simp only [seedTrialEvent, PairRefs, SeedRefs, mem_inter_iff, mem_ofPred_eq]
    tauto
  rw [hset]
  exact p5b_aeEventIn_inter (p5b_aeEventIn_inter hdn hrefs)
    (p5b_aeEventIn_inter hdupD hdupE)

theorem seedTrial_base_nullMeasurable (hd : 2 ≤ d)
    {ξ η v H₀ σ₀ β₀ m M Hsd σsd : ℝ}
    {D E : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    (hE : IsStrongExpMetric d η (distExp d η) E)
    (hHsd : 0 ≤ Hsd) (hσsd : 0 ≤ σsd) :
    NullMeasurableSet (seedTrialEvent D E v H₀ σ₀ β₀ m M Hsd σsd)
      (pinLaw d 1) := by
  have := isProbabilityMeasure_pinLaw hd (1 : ℝ)
  have hlD := p5b_ae_isLength_rho hd hD one_pos
  have hlE := p5b_ae_isLength_rho hd hE one_pos
  have hdn := p5b_nullMeasurableSet_hdown hD.measurable hE.measurable
    (pinLaw d 1) hlD hlE (1 + 2 * v)
  have href := p5b_nullMeasurableSet_pairRefs hD.measurable hE.measurable
    (pinLaw d 1) hlD hlE H₀ σ₀ β₀ m M
  have hdupD := q10_nullMeasurableSet_dUpper hD.measurable (pinLaw d 1)
    hlD (W := siteA d) hHsd hσsd
  have hdupE := q10_nullMeasurableSet_dUpper hE.measurable (pinLaw d 1)
    hlE (W := siteA d) hHsd hσsd
  have hset : seedTrialEvent D E v H₀ σ₀ β₀ m M Hsd σsd =
      (Hdown D E (1 + 2 * v) ∩ PairRefs D E H₀ σ₀ β₀ m M) ∩
        ({g | DUpper (rho D g) (siteA d) Hsd σsd} ∩
          {g | DUpper (rho E g) (siteA d) Hsd σsd}) := by
    ext g
    simp only [seedTrialEvent, PairRefs, SeedRefs, mem_inter_iff, mem_ofPred_eq]
    tauto
  rw [hset]
  exact (hdn.inter href).inter (hdupD.inter hdupE)

theorem seedTrial_base_fail_prob (hd : 2 ≤ d)
    {ξ η v H₀ σ₀ β₀ m M Hsd σsd pstar : ℝ}
    {D E : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    (hE : IsStrongExpMetric d η (distExp d η) E)
    (hHsd : 0 ≤ Hsd) (hσsd : 0 ≤ σsd)
    (hpstar : 0 < pstar)
    (hgood : ENNReal.ofReal (pstar / 4) ≤
      pinLaw d 1 (seedTrialEvent D E v H₀ σ₀ β₀ m M Hsd σsd)) :
    pinLaw d 1 (seedTrialEvent D E v H₀ σ₀ β₀ m M Hsd σsd)ᶜ ≤
      ENNReal.ofReal (1 - pstar / 4) := by
  have := isProbabilityMeasure_pinLaw hd (1 : ℝ)
  let T := seedTrialEvent D E v H₀ σ₀ β₀ m M Hsd σsd
  have hT : NullMeasurableSet T (pinLaw d 1) :=
    seedTrial_base_nullMeasurable hd (v := v) (H₀ := H₀) (σ₀ := σ₀)
      (β₀ := β₀) (m := m) (M := M) hD hE hHsd hσsd
  change pinLaw d 1 Tᶜ ≤ _
  rw [measure_compl₀ hT (measure_ne_top (pinLaw d 1) T), measure_univ]
  calc
    1 - pinLaw d 1 T ≤ 1 - ENNReal.ofReal (pstar / 4) :=
      tsub_le_tsub_left hgood 1
    _ = ENNReal.ofReal (1 - pstar / 4) := by
      rw [ENNReal.ofReal_sub 1 (by positivity)]
      norm_num

end HigherDimLQGContinuity
