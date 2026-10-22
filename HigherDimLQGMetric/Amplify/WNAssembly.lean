import HigherDimLQGMetric.Amplify.GoodProb
import HigherDimLQGMetric.Amplify.TrialSuccess
import HigherDimLQGMetric.Amplify.OscMeas
import HigherDimLQGMetric.Amplify.PlaceScale
import HigherDimLQGMetric.Amplify.BackEventTrial

/-! Amplification on a fixed white-noise realization and at one outer scale. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory ProbabilityTheory Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
  [IsProbabilityMeasure P]

/-- The complete white-noise probability estimate at a fixed macroscopic
radius. Only the geometric placement, coarse and Gaussian bounds remain as
parameters. -/
theorem amplify_goodTrial_whiteNoise
    (hd : 2 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ)
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (𝒢 : Set (Rd d) → ℝ → MeasurableSpace Ω) (Rk : ℝ)
    (F : ℝ → Ω → DistRd d) (g : ℝ → Ω → C(Rd d, ℝ))
    (hwhole : ∀ b, 0 < b → Measurable (F b) ∧ Measurable (g b) ∧
      IsWholeSpaceLGF (fun ω => F b ω + ofCont (g b ω)) P)
    (hrange : ∀ b, 0 < b → ∀ (w : Rd d) (ρ : ℝ), 0 < ρ →
      fieldSigmaOn (F b) (Metric.ball w ρ) ≤
        𝒢 (Metric.ball w (ρ + Rk * b)) b)
    (hindep : ∀ b, 0 < b → ∀ (n : ℕ) (S : Fin n → Set (Rd d)),
      Pairwise (fun i j => Disjoint (S i) (S j)) →
        iIndep (fun i => 𝒢 (S i) b) P)
    {M N : ℕ} (w : Fin M → Fin N → Rd d)
    {ρ r L : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hL : 0 < L)
    (hplace : Pairwise (fun p q : Fin M × Fin N => Disjoint
      (Metric.ball (w p.1 p.2) ((5 + Rk * L) * ρ))
      (Metric.ball (w q.1 q.2) ((5 + Rk * L) * ρ))))
    (cs a A₀ ℓ β₀ c1 δ pstar η ηG p Kcut : ℝ)
    (hc1 : 0 < c1) (hℓ : 0 < ℓ) (hpstar : 0 < pstar)
    (hpstar1 : pstar ≤ 1)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hη0 : 0 ≤ η)
    (hηsmall : η ≤ pstar / 2) (hηG0 : 0 ≤ ηG)
    (hbudget : (M : ℝ) * (1 - pstar / 2) ^ N +
      ((M * N : ℕ) : ℝ) * η + ηG ≤ 1 - p)
    (hcoarse : ∀ v : Rd d,
      P {ω | ∃ x ∈ Metric.ball v (5 * (ρ * r)),
        ∃ y ∈ Metric.ball v (5 * (ρ * r)),
          δ < |g (L * (ρ * r)) ω x - g (L * (ρ * r)) ω y|} ≤
        ENNReal.ofReal η)
    (hWit : ∀ i k, ENNReal.ofReal pstar ≤
      P ((fun ω => F (L * (ρ * r)) ω + ofCont (g (L * (ρ * r)) ω)) ⁻¹'
        WitEvent Dt D ξ Q cs⁻¹ a A₀ ℓ β₀ c1⁻¹ (ρ * r) (r • w i k)))
    (hGaussian :
      P {ω | ∃ i : Fin M, ∃ k : Fin N,
        Kcut < |sphereAvg
          (F (L * (ρ * r)) ω + ofCont (g (L * (ρ * r)) ω))
          (ρ * r) (r • w i k) -
          sphereAvg (F (L * (ρ * r)) ω + ofCont (g (L * (ρ * r)) ω)) r 0|} ≤
          ENNReal.ofReal ηG) :
    ENNReal.ofReal p ≤
      P ((fun ω => F (L * (ρ * r)) ω + ofCont (g (L * (ρ * r)) ω)) ⁻¹'
        AmpGoodTrial D Dt ξ Q cs c1 ℓ (2 * δ) (ρ * r) r Kcut w) := by
  let s := ρ * r
  let b := L * s
  let H : Ω → DistRd d := fun ω => F b ω + ofCont (g b ω)
  have hs : 0 < s := mul_pos hρ hr
  have hb : 0 < b := mul_pos hL hs
  have hwh := hwhole b hb
  have hFine : IsLGFPlusCont (F b) P := by
    refine ⟨hwh.1, fun ω => -g b ω, hwh.2.1.neg, ?_⟩
    convert hwh.2.2 using 1
    funext ω
    simp only [ofCont_neg, sub_neg_eq_add]
  let E : Fin M → Fin N → Set Ω := fun i k =>
    (F b) ⁻¹' TrialEvent D Dt ξ Q cs c1 ℓ δ s (r • w i k)
  let B : Fin M → Fin N → Set Ω := fun i k =>
    {ω | ∃ x ∈ Metric.ball (r • w i k) (5 * s),
      ∃ y ∈ Metric.ball (r • w i k) (5 * s),
        δ < |g b ω x - g b ω y|}
  let G : Set Ω := {ω | ∃ i : Fin M, ∃ k : Fin N,
    Kcut < |sphereAvg (H ω) s (r • w i k) - sphereAvg (H ω) r 0|}
  let m : Fin M → Fin N → MeasurableSpace Ω := fun i k =>
    𝒢 (Metric.ball (r • w i k) (5 * s + Rk * b)) b
  have hrad : 5 * s + Rk * b = r * ((5 + Rk * L) * ρ) := by
    dsimp [s, b]
    ring
  have hpair : Pairwise (fun p q : Fin M × Fin N => Disjoint
      (Metric.ball (r • w p.1 p.2) (5 * s + Rk * b))
      (Metric.ball (r • w q.1 q.2) (5 * s + Rk * b))) := by
    simpa only [hrad] using
      amplify_scaled_balls_disjoint (fun p : Fin M × Fin N => w p.1 p.2)
        ((5 + Rk * L) * ρ) hr hplace
  have hm (i : Fin M) : iIndep (m i) P := by
    exact hindep b hb N
      (fun k => Metric.ball (r • w i k) (5 * s + Rk * b))
      (fun k l hkl => hpair (i := (i, k)) (j := (i, l)) (by
        intro heq
        exact hkl (congrArg Prod.snd heq)))
  have hE (i : Fin M) (k : Fin N) : AEEventIn P (m i k) (E i k) :=
    amplify_aeEventIn_trial_noise hd 𝒢 Rk F g hwhole hrange hb hs
      (r • w i k) hD hDt cs c1 ℓ δ
  have hEnull (i : Fin M) (k : Fin N) : NullMeasurableSet (E i k) P :=
    amplify_nullMeasurableSet_trialEvent P (F b) hFine hD hDt
      cs c1 ℓ δ s (r • w i k)
  have hBmeas (i : Fin M) (k : Fin N) : MeasurableSet (B i k) :=
    amplify_measurableSet_badOsc (g b) hwh.2.1 (r • w i k) s δ
  have hGmeas : MeasurableSet G := by
    have heqG : G = ⋃ i : Fin M, ⋃ k : Fin N,
        {ω | Kcut < |sphereAvg (H ω) s (r • w i k) - sphereAvg (H ω) r 0|} := by
      ext ω
      simp only [G, mem_ofPred_eq, mem_iUnion]
    rw [heqG]
    apply MeasurableSet.iUnion
    intro i
    apply MeasurableSet.iUnion
    intro k
    exact measurableSet_lt measurable_const
      ((((measurable_sphereAvg_left s (r • w i k)).comp hwh.2.2.measurable).sub
        ((measurable_sphereAvg_left r 0).comp hwh.2.2.measurable)).abs)
  have hfail (i : Fin M) (k : Fin N) :
      P ((E i k)ᶜ) ≤ ENNReal.ofReal (1 - pstar / 2) := by
    have htrans := amplify_wit_probability_le_trial_add_osc hd hξ hD hDt
      (F b) (g b) hwh.1 hwh.2.1 hwh.2.2
      cs a A₀ ℓ β₀ c1 δ hc1 hℓ hs (r • w i k)
    exact (amplify_trial_success_le_compl P
      (H ⁻¹' WitEvent Dt D ξ Q cs⁻¹ a A₀ ℓ β₀ c1⁻¹ s (r • w i k))
      (E i k) (B i k) (hEnull i k) hpstar hηsmall
      (hWit i k) htrans (hcoarse (r • w i k))).2
  have hBbound (i : Fin M) (k : Fin N) :
      P (B i k) ≤ ENNReal.ofReal η := hcoarse (r • w i k)
  have hback := amplify_ae_back_of_trial hd hξ hD hDt
    (F b) (g b) hwh.1 hwh.2.1 hwh.2.2 cs c1 ℓ δ hc1
  have htransfer : ∀ᵐ ω ∂P, ∀ i k,
      ω ∈ E i k → ω ∉ B i k →
      H ω ∈ TrialEvent D Dt ξ Q cs c1 ℓ (2 * δ) s (r • w i k) := by
    filter_upwards [hback] with ω hw
    intro i k hEik hBik
    apply (amplify_backEvent_iff_trial D Dt ξ Q cs c1 ℓ δ s (r • w i k)
      (H ω)).1
    exact hw s hs (r • w i k) (by
      intro x hx y hy
      exact le_of_not_gt (fun hgt => hBik ⟨x, hx, y, hy, hgt⟩)) hEik
  have hq0 : 0 ≤ 1 - pstar / 2 := by linarith
  exact amplify_goodTrial_of_failure_data P H D Dt ξ Q cs c1 ℓ δ s r Kcut w
    m E B G hm hE hEnull hBmeas hGmeas rfl hp hp1 hq0 hη0 hηG0
    hbudget hfail hBbound hGaussian htransfer

end HigherDimLQGMetric
