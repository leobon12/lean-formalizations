import HigherDimLQGMetric.Amplify.Pushforward
import HigherDimLQGMetric.WNSplit.Local

/-!
# Independence of local fine-field trials

The shell locality of a trial and the finite-range clause of a white-noise
split put each trial in its own noise sigma algebra, up to a null set.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory ProbabilityTheory Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- The fine trial is measurable modulo null sets in the noise sigma-algebra
of its enlarged spatial neighborhood. -/
theorem amplify_aeEventIn_trial_noise
    (hd : 2 ≤ d) (𝒢 : Set (Rd d) → ℝ → MeasurableSpace Ω) (Rk : ℝ)
    (F : ℝ → Ω → DistRd d) (g : ℝ → Ω → C(Rd d, ℝ))
    (hwhole : ∀ b, 0 < b → Measurable (F b) ∧ Measurable (g b) ∧
      IsWholeSpaceLGF (fun ω => F b ω + ofCont (g b ω)) P)
    (hrange : ∀ b, 0 < b → ∀ (w : Rd d) (ρ : ℝ), 0 < ρ →
      fieldSigmaOn (F b) (Metric.ball w ρ) ≤
        𝒢 (Metric.ball w (ρ + Rk * b)) b)
    {b s : ℝ} (hb : 0 < b) (hs : 0 < s) (w : Rd d)
    {ξ Q : ℝ} {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (cs c1 ℓ δ : ℝ) :
    AEEventIn P (𝒢 (Metric.ball w (5 * s + Rk * b)) b)
      ((F b) ⁻¹' TrialEvent D Dt ξ Q cs c1 ℓ δ s w) := by
  have hwh := hwhole b hb
  have htrial := amplify_aeEventIn_trialEvent_of_split P (F b) (g b)
    hwh.1 hwh.2.1 hwh.2.2 hD hDt hd cs c1 ℓ δ hs w
  have hsub : ann w (s / 2) (5 * s) ⊆ Metric.ball w (5 * s) := by
    intro x hx
    exact hx.2
  exact wns_aeEventIn_mono
    ((wns_fieldSigma0_le_fieldSigmaOn (F b) _).trans
      ((wns_fieldSigmaOn_mono (F b) hsub).trans
        (hrange b hb w (5 * s) (by positivity)))) htrial

/-- Trial events of a fine field are independent when their enlarged noise
balls are disjoint. -/
theorem amplify_measure_biInter_trials
    (hd : 2 ≤ d) (𝒢 : Set (Rd d) → ℝ → MeasurableSpace Ω) (Rk : ℝ)
    (F : ℝ → Ω → DistRd d) (g : ℝ → Ω → C(Rd d, ℝ))
    (hwhole : ∀ b, 0 < b → Measurable (F b) ∧ Measurable (g b) ∧
      IsWholeSpaceLGF (fun ω => F b ω + ofCont (g b ω)) P)
    (hrange : ∀ b, 0 < b → ∀ (w : Rd d) (ρ : ℝ), 0 < ρ →
      fieldSigmaOn (F b) (Metric.ball w ρ) ≤
        𝒢 (Metric.ball w (ρ + Rk * b)) b)
    (hindep : ∀ b, 0 < b → ∀ (n : ℕ) (S : Fin n → Set (Rd d)),
      Pairwise (fun i j => Disjoint (S i) (S j)) →
        iIndep (fun i => 𝒢 (S i) b) P)
    {b s : ℝ} (hb : 0 < b) (hs : 0 < s) {n : ℕ}
    (w : Fin n → Rd d)
    (hdisj : Pairwise (fun i j => Disjoint
      (Metric.ball (w i) (5 * s + Rk * b))
      (Metric.ball (w j) (5 * s + Rk * b))))
    {ξ Q : ℝ} {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (cs c1 ℓ δ : ℝ) (t : Finset (Fin n)) :
    P (⋂ i ∈ t, (F b) ⁻¹' TrialEvent D Dt ξ Q cs c1 ℓ δ s (w i)) =
      ∏ i ∈ t, P ((F b) ⁻¹' TrialEvent D Dt ξ Q cs c1 ℓ δ s (w i)) := by
  have hwh := hwhole b hb
  have hlocal (i : Fin n) :
      AEEventIn P (𝒢 (Metric.ball (w i) (5 * s + Rk * b)) b)
        ((F b) ⁻¹' TrialEvent D Dt ξ Q cs c1 ℓ δ s (w i)) := by
    have htrial := amplify_aeEventIn_trialEvent_of_split P (F b) (g b)
      hwh.1 hwh.2.1 hwh.2.2 hD hDt hd cs c1 ℓ δ hs (w i)
    have hsub : ann (w i) (s / 2) (5 * s) ⊆ Metric.ball (w i) (5 * s) := by
      intro x hx
      exact hx.2
    exact wns_aeEventIn_mono
      ((wns_fieldSigma0_le_fieldSigmaOn (F b) _).trans
        ((wns_fieldSigmaOn_mono (F b) hsub).trans
          (hrange b hb (w i) (5 * s) (by positivity)))) htrial
  exact wns_measure_biInter_of_aeEventIn (hindep b hb n
    (fun i => Metric.ball (w i) (5 * s + Rk * b)) hdisj) t
    (fun i _ => hlocal i)

omit [IsProbabilityMeasure P] in
/-- The probability that every event in a finite independent family fails. -/
theorem amplify_all_fail_le_pow {ι : Type*} {m : ι → MeasurableSpace Ω}
    (hm : iIndep m P) {E : ι → Set Ω} (t : Finset ι)
    (hE : ∀ i ∈ t, AEEventIn P (m i) (E i))
    {q : ℝ≥0∞} (hq : ∀ i ∈ t, P ((E i)ᶜ) ≤ q) :
    P (⋂ i ∈ t, (E i)ᶜ) ≤ q ^ t.card := by
  rw [wns_measure_biInter_of_aeEventIn hm t
    (fun i hi => wns_aeEventIn_compl (hE i hi))]
  exact Finset.prod_le_pow_card t (fun i => P ((E i)ᶜ)) q hq

end HigherDimLQGMetric
