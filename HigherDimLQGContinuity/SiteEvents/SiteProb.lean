import HigherDimLQGContinuity.SiteEvents.SiteEvent
import HigherDimLQGContinuity.Caps.Gaussian

/-! A finite Gaussian cap and the probability of the whole-site event. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory Set Metric ProbabilityTheory
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Every fixed finite family of positive-radius pinned averages has a high-probability cap. -/
theorem sitePinCap_prob (hd : 2 ≤ d) (F : Finset (ℝ × Rd d))
    (hF : ∀ p ∈ F, 0 < p.1) {p : ℝ} (hp : 0 < p) :
    ∃ Kpin : ℝ, 0 ≤ Kpin ∧
      pinLaw d 1 {g | ∃ a ∈ F, Kpin < |sphereAvg g a.1 a.2|} ≤
        ENNReal.ofReal p := by
  classical
  let V : ℝ := ∑ a ∈ F,
    |Var[fun g : DistRd d => sphereAvg g a.1 a.2; pinLaw d 1]|
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hV (a : ℝ × Rd d) (ha : a ∈ F) :
      Var[fun g : DistRd d => sphereAvg g a.1 a.2; pinLaw d 1] ≤ V :=
    (le_abs_self _).trans
      (Finset.single_le_sum (f := fun a : ℝ × Rd d =>
        |Var[fun g : DistRd d => sphereAvg g a.1 a.2; pinLaw d 1]|)
        (fun _ _ => abs_nonneg _) ha)
  let b : ℝ := Real.exp (-1)
  have hb1 : b < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hden : 0 < (F.card : ℝ) * 2 + 1 := by positivity
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hp hden) hb1
  let Kpin : ℝ := V / 2 + N
  have hKpin : 0 ≤ Kpin := by dsimp [Kpin]; positivity
  refine ⟨Kpin, hKpin, ?_⟩
  have htail := p4_cap_finite hd one_pos F (by simpa using hF)
    (fun a ha => by simpa only [one_mul] using hV a ha)
    (show (0 : ℝ) ≤ 1 by norm_num) (s := 1) (T := Kpin)
  have hexp : Real.exp (-Kpin + V / 2) = b ^ N := by
    have harg : -Kpin + V / 2 = (N : ℝ) * (-1) := by dsimp [Kpin]; ring
    rw [harg, Real.exp_nat_mul]
  have hreal : (F.card : ℝ) * (2 * b ^ N) ≤ p := by
    rw [lt_div_iff₀ hden] at hN
    have hbN : 0 ≤ b ^ N := pow_nonneg (Real.exp_nonneg _) _
    nlinarith only [hN, hbN]
  have htail' : pinLaw d 1 {g | ∃ a ∈ F, Kpin < |sphereAvg g a.1 a.2|} ≤
      ENNReal.ofReal ((F.card : ℝ) * (2 * b ^ N)) := by
    simpa only [one_mul, one_pow, neg_one_mul, hexp] using htail
  exact htail'.trans (ENNReal.ofReal_le_ofReal hreal)

/-- A cap for all seed radii and edge centres. -/
theorem sitePinCap_trials_prob (hd : 2 ≤ d) {ι : Type}
    (F : Finset ι) (c : ι → Rd d) {L : ℝ} (hL : 0 < L) (Ntr : ℕ)
    {p : ℝ} (hp : 0 < p) :
    ∃ Kpin : ℝ, 0 ≤ Kpin ∧
      pinLaw d 1 {g | ∃ e ∈ F, ∃ j ∈ Finset.range Ntr,
        Kpin < |sphereAvg g (seedTrialRadius L j) (c e)|} ≤
          ENNReal.ofReal p := by
  classical
  let P : Finset (ℝ × Rd d) :=
    (F.product (Finset.range Ntr)).image
      (fun ej => (seedTrialRadius L ej.2, c ej.1))
  have hP (a : ℝ × Rd d) (ha : a ∈ P) : 0 < a.1 := by
    obtain ⟨ej, _, rfl⟩ := Finset.mem_image.mp ha
    exact seedTrialRadius_pos hL ej.2
  obtain ⟨Kpin, hKpin, hcap⟩ := sitePinCap_prob hd P hP hp
  refine ⟨Kpin, hKpin, ?_⟩
  have hsub : {g : DistRd d | ∃ e ∈ F, ∃ j ∈ Finset.range Ntr,
      Kpin < |sphereAvg g (seedTrialRadius L j) (c e)|} ⊆
      {g | ∃ a ∈ P, Kpin < |sphereAvg g a.1 a.2|} := by
    rintro g ⟨e, he, j, hj, hbad⟩
    refine ⟨(seedTrialRadius L j, c e), ?_, hbad⟩
    exact Finset.mem_image.mpr ⟨(e, j), Finset.mem_product.mpr ⟨he, hj⟩, rfl⟩
  exact (measure_mono hsub).trans hcap

/-- The three components of the whole-site event each spend at most one quarter of the budget. -/
theorem siteEvent_prob_of_bounds {ι : Type} (D E : DistRd d → ContMetric d)
    (F : Finset ι) (c : ι → Rd d) (L : ℝ) (Ntr : ℕ)
    (v H₀ σ₀ β₀ m M Hsd σsd Hup σ Hlo β mc A0 Kpin p : ℝ)
    (hp : 0 ≤ p)
    (href : pinLaw d 1 {g | ¬ SiteRefs Hup σ Hlo β mc A0 (rho D g)} ≤
      ENNReal.ofReal (p / 4))
    (htrial : pinLaw d 1 {g | ∃ e ∈ F, ∀ j ∈ Finset.range Ntr,
      recentre 1 (seedTrialRadius L j) (c e) g ∉
        seedTrialEvent D E v H₀ σ₀ β₀ m M Hsd σsd} ≤ ENNReal.ofReal (p / 4))
    (hpin : pinLaw d 1 {g | ∃ e ∈ F, ∃ j ∈ Finset.range Ntr,
      Kpin < |sphereAvg g (seedTrialRadius L j) (c e)|} ≤
        ENNReal.ofReal (p / 4)) :
    pinLaw d 1
      (siteEvent D E F c L Ntr v H₀ σ₀ β₀ m M Hsd σsd Hup σ Hlo β mc A0 Kpin)ᶜ ≤
        ENNReal.ofReal p := by
  classical
  let B₁ : Set (DistRd d) := {g | ¬ SiteRefs Hup σ Hlo β mc A0 (rho D g)}
  let B₂ : Set (DistRd d) := {g | ∃ e ∈ F, ∀ j ∈ Finset.range Ntr,
    recentre 1 (seedTrialRadius L j) (c e) g ∉
      seedTrialEvent D E v H₀ σ₀ β₀ m M Hsd σsd}
  let B₃ : Set (DistRd d) := {g | ∃ e ∈ F, ∃ j ∈ Finset.range Ntr,
    Kpin < |sphereAvg g (seedTrialRadius L j) (c e)|}
  have hsub : (siteEvent D E F c L Ntr v H₀ σ₀ β₀ m M Hsd σsd
      Hup σ Hlo β mc A0 Kpin)ᶜ ⊆ B₁ ∪ (B₂ ∪ B₃) := by
    intro g hg
    change ¬ (SiteRefs Hup σ Hlo β mc A0 (rho D g) ∧
      (∀ e ∈ F, ∃ j ∈ Finset.range Ntr,
        recentre 1 (seedTrialRadius L j) (c e) g ∈
          seedTrialEvent D E v H₀ σ₀ β₀ m M Hsd σsd) ∧
      (∀ e ∈ F, ∀ j ∈ Finset.range Ntr,
        |sphereAvg g (seedTrialRadius L j) (c e)| ≤ Kpin)) at hg
    by_cases hR : SiteRefs Hup σ Hlo β mc A0 (rho D g)
    · by_cases hS : ∀ e ∈ F, ∃ j ∈ Finset.range Ntr,
        recentre 1 (seedTrialRadius L j) (c e) g ∈
          seedTrialEvent D E v H₀ σ₀ β₀ m M Hsd σsd
      · have hC : ¬ ∀ e ∈ F, ∀ j ∈ Finset.range Ntr,
          |sphereAvg g (seedTrialRadius L j) (c e)| ≤ Kpin :=
          fun hc => hg ⟨hR, hS, hc⟩
        simp only [not_forall, not_le] at hC
        obtain ⟨e, he, j, hj, hbad⟩ := hC
        exact Or.inr (Or.inr (show g ∈ B₃ from ⟨e, he, j, hj, hbad⟩))
      · simp only [not_forall, not_exists] at hS
        obtain ⟨e, he, hbad⟩ := hS
        exact Or.inr (Or.inl ⟨e, he, fun j hj hgood => hbad j ⟨hj, hgood⟩⟩)
    · exact Or.inl hR
  calc
    pinLaw d 1 _ ≤ pinLaw d 1 (B₁ ∪ (B₂ ∪ B₃)) := measure_mono hsub
    _ ≤ pinLaw d 1 B₁ + (pinLaw d 1 B₂ + pinLaw d 1 B₃) := by
      exact (measure_union_le _ _).trans (by gcongr; exact measure_union_le B₂ B₃)
    _ ≤ ENNReal.ofReal (p / 4) +
        (ENNReal.ofReal (p / 4) + ENNReal.ofReal (p / 4)) :=
      add_le_add href (add_le_add htrial hpin)
    _ ≤ ENNReal.ofReal p := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      linarith

/-- Lemma `b:lem-siteevent`: choose fixed reference, trial, and pin-cap constants so that
the whole-site event has the prescribed high probability and is local to the unit annulus. -/
theorem siteEvent_prob (hd : 2 ≤ d) {ξbar : ℝ}
    (hU : ∀ s ∈ Icc (1 : ℝ) 10, UniformEstimates d ξbar s)
    {ι : Type} (F : Finset ι) (c : ι → Rd d) {L p : ℝ}
    (hL : 0 < L) (hp : 0 < p)
    (hbox : ∀ e ∈ F, closedBall (c e) L ⊆ siteC d) :
    ∃ pstar v₀ C₄ c₄ H₀ σ₀ β₀ m M Hsd σsd K
      Hup σ Hlo β mc A0 : ℝ, ∃ Ntr : ℕ, ∃ Kpin : ℝ,
      0 < pstar ∧ pstar < 1 ∧ 0 < v₀ ∧ v₀ ≤ 1 / 2 ∧ 0 < C₄ ∧ 0 < c₄ ∧
      0 < σ₀ ∧ σ₀ < 1 ∧ 1 < β₀ ∧ 0 < m ∧ m < M ∧ 1 ≤ H₀ ∧
      1 ≤ Hsd ∧ 0 < σsd ∧ σsd ≤ 1 ∧ 1 ≤ K ∧
      1 ≤ Hup ∧ 0 < σ ∧ σ ≤ 1 ∧ 1 ≤ Hlo ∧ 1 ≤ β ∧ 0 < mc ∧ Hlo⁻¹ ≤ A0 ∧
      0 ≤ Kpin ∧
      ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ η ∈ Ioc (0 : ℝ) ξbar,
        ∀ D E : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
        IsStrongExpMetric d η (distExp d η) E →
        ∀ v : ℝ, 0 < v → v < v₀ → |η - ξ| ≤ c₄ * v ^ C₄ →
          pinLaw d 1
            (siteEvent D E F c L Ntr v H₀ σ₀ β₀ m M Hsd σsd
              Hup σ Hlo β mc A0 Kpin)ᶜ ≤ ENNReal.ofReal p ∧
          AEEventIn (pinLaw d 1) (fieldSigma0 id (ann (0 : Rd d) (1 / 2) 4))
            (siteEvent D E F c L Ntr v H₀ σ₀ β₀ m M Hsd σsd
              Hup σ Hlo β mc A0 Kpin) := by
  classical
  obtain ⟨pstar, v₀, C₄, c₄, H₀, σ₀, β₀, m, M, Hsd, σsd, K,
    hpstar, hpstar1, hv₀, hv₀1, hC₄, hc₄, hσ₀, hσ₀1, hβ₀,
    hm, hmM, hH₀, hHsd, hσsd, hσsd1, hK, htrials⟩ := seedTrials_prob hd hU
  obtain ⟨Hup, σ, Hlo, β, mc, A0, hHup, hσ, hσ1, hHlo, hβ,
    hmc, hA0, hrefs⟩ :=
      siteRefs_prob hd (hU 1 (by norm_num))
        (show 0 < p / 4 by positivity)
  obtain ⟨Ntr, htrial⟩ := htrials F c (show 0 < p / 4 by positivity) hL
  obtain ⟨Kpin, hKpin, hpin⟩ := sitePinCap_trials_prob hd F c hL Ntr
    (show 0 < p / 4 by positivity)
  refine ⟨pstar, v₀, C₄, c₄, H₀, σ₀, β₀, m, M, Hsd, σsd, K,
    Hup, σ, Hlo, β, mc, A0, Ntr, Kpin,
    hpstar, hpstar1, hv₀, hv₀1, hC₄, hc₄, hσ₀, hσ₀1, hβ₀,
    hm, hmM, hH₀, hHsd, hσsd, hσsd1, hK,
    hHup, hσ, hσ1, hHlo, hβ, hmc, hA0, hKpin, ?_⟩
  intro ξ hξ η hη D E hD hE v hv hvv hτ
  have href := (hrefs ξ hξ D hD).1
  have htrial' := htrial ξ hξ η hη D E hD hE v hv hvv hτ
  have hprob := siteEvent_prob_of_bounds D E F c L Ntr v H₀ σ₀ β₀ m M Hsd σsd
    Hup σ Hlo β mc A0 Kpin p hp.le href htrial' hpin
  have hlocal : AEEventIn (pinLaw d 1)
      (fieldSigma0 id (ann (0 : Rd d) (1 / 2) 4))
      (siteEvent D E F c L Ntr v H₀ σ₀ β₀ m M Hsd σsd
        Hup σ Hlo β mc A0 Kpin) :=
    siteEvent_aeEventIn hd hξ.1 hη.1 hD hE F c hL hbox Ntr
      (by linarith) hσsd.le (by linarith) hσ.le
  exact ⟨hprob, hlocal⟩

end HigherDimLQGContinuity
