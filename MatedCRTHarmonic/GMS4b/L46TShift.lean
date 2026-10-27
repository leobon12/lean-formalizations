import MatedCRTHarmonic.GMS4b.L46SCount
import MatedCRTHarmonic.GMS4b.L46STail
import MatedCRTHarmonic.GMS4b.L46SWindow
import MatedCRTHarmonic.MoTInput.CellModel
import MatedCRTHarmonic.MoTInput.CurveAdapters
import MatedCRTHarmonic.GMS4b.L46SCoverageTail
import MatedCRTHarmonic.GMS4b.L46SPolylog
import MatedCRTHarmonic.MoTInput.Segments
import MatedCRTHarmonic.MoTInput.AreaDominates
import MatedCRTHarmonic.GMCFacts.LowerTail
import MatedCRTHarmonic.GMS4b.L46SAsymptotic
import MatedCRTHarmonic.GMS4b.Window

/-!
# Translation of the gamma-cone estimates

For the local law comparison the gamma-cone singularity is placed outside the
observation disk. Translation does not change the quantum-time mesh or the
localized degree.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4b

open MatedCRTHarmonic.GMSLemma27

/-- Translate a curve while leaving its time parameter unchanged. -/
def l46tTranslateCurve (z₀ : ℂ) (c : ℝ → ℂ) : ℝ → ℂ :=
  fun t => c t + z₀

theorem l46t_hitTime_translate (z₀ : ℂ) (c : ℝ → ℂ) (z : ℂ) :
    hitTime (l46tTranslateCurve z₀ c) (z + z₀) = hitTime c z := by
  unfold hitTime
  congr 1
  ext t
  simp only [Set.mem_ofPred_eq, l46tTranslateCurve]
  exact add_right_cancel_iff

/-- Spatial translation preserves the inner degree at the translated root. -/
theorem l46t_degreeIn_translate (z₀ : ℂ) (c : ℝ → ℂ) (ε : ℝ) (z : ℂ) :
    degreeIn ε (l46tTranslateCurve z₀ c) (z + z₀) = degreeIn ε c z := by
  rw [degreeIn, l46t_hitTime_translate, degreeIn]
  have hcurve : l46tTranslateCurve z₀ c = simC 1 z₀ one_ne_zero ∘ c := by
    funext t
    simp [l46tTranslateCurve, simC_apply]
  rw [hcurve]
  exact locDegIn_simC 1 z₀ one_ne_zero c ε (hitTime c z)

/-- The degree ball translates with the curve. -/
theorem l46t_locBall_translate (z₀ : ℂ) (c : ℝ → ℂ) (ε t : ℝ) :
    locBall ε (l46tTranslateCurve z₀ c) t =
      (fun z : ℂ => z + z₀) '' locBall ε c t := by
  have hcurve : l46tTranslateCurve z₀ c = simC 1 z₀ one_ne_zero ∘ c := by
    funext u
    simp [l46tTranslateCurve, simC_apply]
  rw [hcurve, locBall_simC]
  congr 1
  funext z
  simp [simC_apply]

/-- The corrected gamma-cone Lemma 4.6 remains valid after moving its root
to a fixed point `z₀`. -/
theorem l46t_innerDegreeBoundPolylog_translate {γ : ℝ}
    (M : GMSLemma27.CellModel γ) (k : ℕ)
    (hin : InnerDegreeBoundPolylog M k) (z₀ : ℂ)
    {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    {ζ : ℝ} (hζ : ζ ∈ Ioo (0 : ℝ) 1) (s : ℝ) :
    ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
      M.P {ω | ∃ z ∈ ball z₀ ρ,
        ENNReal.ofReal (Real.log ε⁻¹ ^ ((k : ℝ) * (1 + ζ) + 1)) <
          ((degreeIn ε (l46tTranslateCurve z₀ (M.curve ω)) z : ℕ∞) : ℝ≥0∞)} ≤
        ENNReal.ofReal (C * ε ^ s) := by
  obtain ⟨C, hC⟩ := hin ρ hρ ζ hζ s
  refine ⟨C, fun ε hε => (measure_mono ?_).trans (hC ε hε)⟩
  rintro ω ⟨z, hz, hbad⟩
  refine ⟨z - z₀, ?_, ?_⟩
  · simpa [Metric.mem_ball, dist_eq_norm] using hz
  · have heq : z - z₀ + z₀ = z := sub_add_cancel z z₀
    rw [← heq, l46t_degreeIn_translate] at hbad
    exact hbad

/-- A smaller observation disk can be placed away from the translated
cone's root. This is the form of Lemma 2.7 needed by (4.16). -/
theorem l46t_localization_shifted_disk {γ : ℝ}
    (M : GMSLemma27.CellModel γ) (hγ : 0 < γ)
    (hSLE : GMSLemma27.SegmentsContainBalls M)
    (hGMC : GMSLemma27.GMCLowerTail γ)
    (hdom : GMSLemma27.AreaDominatesWholePlaneGFF M)
    (z₀ w : ℂ) {ρ r R : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (hsub : ball w r ⊆ ball z₀ ρ) (hrR : r < R) (s : ℝ) :
    ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
      M.P {ω | ∃ t : ℝ,
        l46tTranslateCurve z₀ (M.curve ω) t ∈ ball w r ∧
        ¬ locBall ε (l46tTranslateCurve z₀ (M.curve ω)) t ⊆ ball w R} ≤
        ENNReal.ofReal (C * ε ^ s) := by
  obtain ⟨q, hq0, hq1, hsα⟩ := l46s_exists_lemma27_q_for_power hγ s
  obtain ⟨C, hC⟩ := GMSLemma27.lemma27_segments M hSLE hGMC hdom hγ
    hq0 hq1 hρ.1 hρ.2 hsα
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ q < (R - r) / 8 :=
    eventually_rpow_lt hq0 (by linarith)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      M.P {ω | ∃ t : ℝ,
        l46tTranslateCurve z₀ (M.curve ω) t ∈ ball w r ∧
        ¬ locBall ε (l46tTranslateCurve z₀ (M.curve ω)) t ⊆ ball w R} ≤
        ENNReal.ofReal (C * ε ^ s) := by
    filter_upwards [hsmall, self_mem_nhdsWithin,
      eventually_lt_nhdsGT_zero one_pos] with ε hsmall hε0 hε1
    have hbad : {ω | ∃ t : ℝ,
        l46tTranslateCurve z₀ (M.curve ω) t ∈ ball w r ∧
        ¬ locBall ε (l46tTranslateCurve z₀ (M.curve ω)) t ⊆ ball w R} ≤ᵐ[M.P]
        (GMSLemma27.segmentDiamGood M ε q ρ)ᶜ := by
      filter_upwards [M.ae_continuous_curve] with ω hc
      rintro ⟨t, ht, hnot⟩ hgood
      apply hnot
      have htz₀ : l46tTranslateCurve z₀ (M.curve ω) t ∈ ball z₀ ρ := hsub ht
      have htc : M.curve ω t ∈ ball (0 : ℂ) ρ := by
        simpa [Metric.mem_ball, dist_eq_norm, l46tTranslateCurve] using htz₀
      have hd := diam_locWindow_le_two_mul hε0.le
        (fun a b hab hmeet => hgood a b hab hmeet) htc
      intro z hz
      rw [l46t_locBall_translate] at hz
      obtain ⟨u, hu, rfl⟩ := hz
      have hdist : dist u (M.curve ω t) ≤ 4 * diam (locWindow ε (M.curve ω) t) := hu
      have hroot : dist (l46tTranslateCurve z₀ (M.curve ω) t) w < r := ht
      rw [Metric.mem_ball]
      calc
        dist (u + z₀) w ≤ dist (u + z₀) (l46tTranslateCurve z₀ (M.curve ω) t) +
            dist (l46tTranslateCurve z₀ (M.curve ω) t) w := dist_triangle _ _ _
        _ < R := by
          have heq : dist (u + z₀) (l46tTranslateCurve z₀ (M.curve ω) t) =
              dist u (M.curve ω t) := by
            simp [l46tTranslateCurve, dist_add_right]
          rw [heq]
          linarith
    exact (measure_mono_ae hbad).trans (hC ε ⟨hε0, hε1⟩)
  exact exists_bound_of_eventually (fun _ => prob_le_one) hev

end MatedCRTHarmonic.GMS4b
