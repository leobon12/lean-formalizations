import HigherDimLQGMetric.Amplify.WNAssembly
import HigherDimLQGMetric.Amplify.TrialFamilyLaw
import HigherDimLQGMetric.Amplify.ArcBox
import HigherDimLQGMetric.Amplify.Choices
import HigherDimLQGMetric.Amplify.Gaussian
import HigherDimLQGMetric.Amplify.WitLaw
import HigherDimLQGMetric.Proper.Proper
import HigherDimLQGMetric.WNSplit.Split

/-! [S] Lemma 6.1: fine-field amplification for the lower metric pair. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory ProbabilityTheory Set Filter Topology
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- **[S] Lemma 6.1.** A lower sharp-weak pair with a deterministic lower
comparison amplifies any positive local witness probability into a prescribed
probability below one of simple improving arcs in all compact boxes. -/
theorem fineFieldAmplification_of_lower_pair
    (hd : 3 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ)
    (hQ : Real.sqrt (2 * d) < Q)
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    {cs c1 c2 a A₀ ℓ β₀ pstar : ℝ}
    (hcs : 0 < cs) (hc1 : 0 < c1) (hℓ : 0 < ℓ)
    (hc12 : c1 < c2) (hpstar : 0 < pstar) (hpstar1 : pstar ≤ 1)
    (hcomp : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistRd d),
      IsWholeSpaceLGF h P → ∀ᵐ ω ∂P, ∀ u v : Rd d,
        cs * (D (h ω)).1 (u, v) ≤ (Dt (h ω)).1 (u, v)) :
    FineFieldAmplification d ξ Q D Dt cs c1 c2 a A₀ ℓ β₀ pstar := by
  have hd2 : 2 ≤ d := by omega
  obtain ⟨δ, hδ, hc2, hδsmall⟩ := amplify_exists_delta hξ hc1 hc12
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, 𝒢, Rk, F, g,
    hRk, hwhole, hrange, hindep, hosc⟩ := whiteNoiseSplit hd2
  letI : MeasurableSpace Ω₀ := mΩ₀
  letI : IsProbabilityMeasure P₀ := hP₀
  intro M O K hO hK hKO hKint hOann hOpair p hp
  by_cases hp0 : p ≤ 0
  · refine ⟨0, 1, 2, by norm_num, by norm_num, ?_⟩
    intro Ω _ P _ h hh r hr hW
    simp only [ENNReal.ofReal_eq_zero.mpr hp0]
    exact bot_le
  have hpPos : 0 < p := lt_of_not_ge hp0
  have hp1 : p ≤ 1 := hp.le
  obtain ⟨N, hNpos, hNsmall⟩ :=
    amplify_exists_trial_count M hpstar hpstar1 hp
  let n : ℝ := (M * N : ℕ)
  let ε : ℝ := (1 - p) / 4
  let η : ℝ := min (pstar / 2) (ε / (n + 1))
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hn0 : 0 ≤ n := by dsimp [n]; positivity
  have hη : 0 < η := by
    dsimp [η]
    apply lt_min
    · linarith
    · exact div_pos hε (by linarith)
  have hηsmall : η ≤ pstar / 2 := min_le_left _ _
  have hηbudget : n * η ≤ ε := by
    have hupper : η ≤ ε / (n + 1) := min_le_right _ _
    have hden : 0 < n + 1 := by linarith
    have hclear := (le_div_iff₀ hden).1 hupper
    nlinarith [mul_nonneg hη.le (show 0 ≤ (1 : ℝ) by norm_num)]
  have hbudget : (M : ℝ) * (1 - pstar / 2) ^ N +
      ((M * N : ℕ) : ℝ) * η + ε ≤ 1 - p := by
    dsimp [n] at hηbudget
    dsimp [ε] at hηbudget hNsmall ⊢
    linarith
  obtain ⟨L₀, hL₀, hOsc⟩ := hosc η δ hη hδ
  let L : ℝ := max L₀ 1
  have hL : 0 < L := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hLlarge : L₀ ≤ L := le_max_left _ _
  obtain ⟨m, w, hρ, hρ1, hplaceBall, hplaceDisj⟩ :=
    amplify_exists_trial_scale (by omega : 1 ≤ d) O K hKint hKO hOpair
      Rk L hRk hL (N := N)
  let ρ : ℝ := ((64 : ℝ)⁻¹) ^ m
  let wflat : Fin (M * N) → Rd d := fun j =>
    w (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  have hnormW (j : Fin (M * N)) : ‖wflat j‖ ≤ 3 := by
    have hw := hplaceBall (finProdFinEquiv.symm j).1
      (finProdFinEquiv.symm j).2
    have hmem : wflat j ∈ K (finProdFinEquiv.symm j).1 := by
      apply hw
      exact Metric.mem_ball_self (by
        positivity)
    have hann := hOann _ (hKO _ hmem)
    exact (by simpa only [sub_zero] using hann.2.le)
  obtain ⟨Kcut, hKcut0, hGaussian⟩ :=
    amplify_exists_nonneg_gaussian_trial_bound hd2 hρ hρ1
      wflat hnormW hε
  let al : ℝ := Real.exp (-2 * ξ * δ) * (ℓ / (2 * c1))
  let au : ℝ := cs⁻¹ * Real.exp (2 * ξ * δ) * ℓ
  let a₁ : ℝ := al * (ρ ^ (ξ * Q) * Real.exp (-ξ * Kcut))
  let A₁ : ℝ := a₁ + au * (ρ ^ (ξ * Q) * Real.exp (ξ * Kcut)) + 1
  have hal : 0 < al := by dsimp [al]; positivity
  have hau : 0 < au := by dsimp [au]; positivity
  have ha₁ : 0 < a₁ := by dsimp [a₁]; positivity
  have hA₁ : a₁ < A₁ := by
    have hterm : 0 < au * (ρ ^ (ξ * Q) * Real.exp (ξ * Kcut)) := by
      positivity
    dsimp [A₁]
    linarith
  have hAupper : au * (ρ ^ (ξ * Q) * Real.exp (ξ * Kcut)) ≤ A₁ := by
    dsimp [A₁]
    linarith [ha₁]
  refine ⟨m, a₁, A₁, ha₁, hA₁, ?_⟩
  intro Ω _ P _ h hh r hr hW
  let s : ℝ := ρ * r
  let b : ℝ := L * s
  let H : Ω₀ → DistRd d := fun ω => F b ω + ofCont (g b ω)
  have hs : 0 < s := mul_pos hρ hr
  have hb : 0 < b := mul_pos hL hs
  have hH : IsWholeSpaceLGF H P₀ := (hwhole b hb).2.2
  have hWit (i : Fin M) (k : Fin N) : ENNReal.ofReal pstar ≤
      P₀ (H ⁻¹' WitEvent Dt D ξ Q cs⁻¹ a A₀ ℓ β₀ c1⁻¹ s (r • w i k)) := by
    rw [amplify_wit_probability_center_eq hDt hD hd2 hH hh
      cs⁻¹ a A₀ ℓ β₀ c1⁻¹ hs (r • w i k)]
    exact hW
  have hCoarse (v : Rd d) :
      P₀ {ω | ∃ x ∈ Metric.ball v (5 * s),
        ∃ y ∈ Metric.ball v (5 * s), δ < |g b ω x - g b ω y|} ≤
        ENNReal.ofReal η := hOsc L hLlarge s hs v
  have hGauss :
      P₀ {ω | ∃ i : Fin M, ∃ k : Fin N,
        Kcut < |sphereAvg (H ω) s (r • w i k) - sphereAvg (H ω) r 0|} ≤
        ENNReal.ofReal ε := by
    have hbnd := hGaussian hH hr
    apply (measure_mono ?_).trans hbnd
    rintro ω ⟨i, k, hk⟩
    exact ⟨finProdFinEquiv (i, k), by simpa only [wflat,
      Equiv.symm_apply_apply] using hk⟩
  have hWN : ENNReal.ofReal p ≤
      P₀ (H ⁻¹' AmpGoodTrial D Dt ξ Q cs c1 ℓ (2 * δ) s r Kcut w) :=
    amplify_goodTrial_whiteNoise P₀ hd2 hξ hD hDt 𝒢 Rk F g
      hwhole hrange hindep w hρ hr hL hplaceDisj
      cs a A₀ ℓ β₀ c1 δ pstar η ε p Kcut
      hc1 hℓ hpstar hpstar1 hpPos.le hp1 hη.le hηsmall hε.le
      hbudget hCoarse hWit hGauss
  have hLaw := amplify_goodTrial_law_eq P₀ P H h hH hh hD hDt hd2
    cs c1 ℓ (2 * δ) hs hr Kcut w
  have hCert : ENNReal.ofReal p ≤
      P (h ⁻¹' AmpGoodTrial D Dt ξ Q cs c1 ℓ (2 * δ) s r Kcut w) := by
    rw [← hLaw]
    exact hWN
  have hArcAE : ∀ᵐ ω ∂P,
      ω ∈ h ⁻¹' AmpGoodTrial D Dt ξ Q cs c1 ℓ (2 * δ) s r Kcut w →
      ∀ i : Fin M, ∃ γ : ℝ → Rd d, IsSimpleArc γ ∧
        (∀ τ ∈ Icc (0 : ℝ) 1, γ τ ∈ (fun x => r • x) '' K i) ∧
        (Dt (h ω)).len γ 0 1 ≤ ENNReal.ofReal (c2 * (D (h ω)).1 (γ 0, γ 1)) ∧
        a₁ * sNorm ξ Q (h ω) r 0 ≤ (D (h ω)).1 (γ 0, γ 1) ∧
        (D (h ω)).len γ 0 1 ≤ ENNReal.ofReal (A₁ * sNorm ξ Q (h ω) r 0) := by
    filter_upwards [hD.length P h hh.isLGFPlusCont,
      hDt.length P h hh.isLGFPlusCont,
      lemma27_proper hd hξ hQ hD P h hh,
      lemma27_proper hd hξ hQ hDt P h hh,
      hcomp P h hh] with ω hlenD hlenDt hproperD hproperDt hcmp
    intro hgood i
    obtain ⟨k, htrial⟩ := hgood.1 i
    have hbox : Metric.ball (w i k) (5 * ρ) ⊆ K i := by
      have hrad : 5 * ρ ≤ (5 + Rk * L) * ρ := by
        have : 0 ≤ Rk * L := mul_nonneg hRk.le hL.le
        nlinarith [hρ]
      exact (Metric.ball_subset_ball hrad).trans (hplaceBall i k)
    have hback : AmplifyBackEvent (D (h ω)) (Dt (h ω)) ξ Q cs c1 ℓ δ s
        (r • w i k) (h ω) :=
      (amplify_backEvent_iff_trial D Dt ξ Q cs c1 ℓ δ s (r • w i k)
        (h ω)).2 htrial
    haveI : ProperSpace (D (h ω)).Space := hproperD
    haveI : ProperSpace (Dt (h ω)).Space := hproperDt
    exact amplify_arc_in_box (D (h ω)) (Dt (h ω)) hlenD hlenDt
      hξ hcs hc1 hℓ hδ.le hδsmall hc2 hρ hr (w i k) (h ω) (K i)
      hbox (hgood.2 i k) (by exact le_rfl) (by simpa only [au] using hAupper)
      hcmp hback
  exact hCert.trans (measure_mono_ae hArcAE)

end HigherDimLQGMetric
