import HigherDimLQGMetric.Determ.StableProb
import HigherDimLQGMetric.Select.MetricBorel
import LQGMetric.Prob.PolishContinuousMap

/-!
# Stable metric convergence with a field-determined limit

The local-uniform version of DFGPS Lemma 1.3. The target space is restricted
to a compact ball square before applying the stable convergence lemma.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

private abbrev determSqR {d : ℕ} (R : ℝ) : Set (Rd d × Rd d) :=
  Metric.closedBall (0 : Rd d) R ×ˢ Metric.closedBall (0 : Rd d) R

private instance {d : ℕ} (R : ℝ) : CompactSpace (determSqR (d := d) R) :=
  isCompact_iff_compactSpace.1 ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))

/-- Stable convergence to an `h`-measurable continuous metric implies local-uniform convergence
in probability. The prelimit only needs almost-sure measurability as a continuous map. -/
theorem determ_tendstoInProbLU_of_stable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (X : ℕ → Ω → C(Rd d × Rd d, ℝ)) (Y : Ω → C(Rd d × Rd d, ℝ))
    (hh : Measurable h) (hX : ∀ n, AEMeasurable (X n) P)
    (hstable : StablyTendstoLU P h X Y)
    (hdet : LQGMetric.AEDeterminedBy Y h P) :
    TendstoInProbLU P (fun n ω => X n ω) atTop (fun ω => Y ω) := by
  intro R _ δ hδ
  let ρ : C(Rd d × Rd d, ℝ) → C(determSqR (d := d) R, ℝ) :=
    fun u => u.restrict (determSqR (d := d) R)
  have hρ : Continuous ρ := ContinuousMap.continuous_restrict _
  let L : ℕ → Ω → C(Rd d × Rd d, ℝ) := fun n => (hX n).mk _
  have hL : ∀ n, Measurable (L n) := fun n => (hX n).measurable_mk
  have hLe : ∀ n, X n =ᵐ[P] L n := fun n => (hX n).ae_eq_mk
  have hdetρ : LQGMetric.AEDeterminedBy (fun ω => ρ (Y ω)) h P := by
    obtain ⟨f, hf, hYf⟩ := hdet
    refine ⟨ρ ∘ f, hρ.measurable.comp hf, ?_⟩
    filter_upwards [hYf] with ω hω
    exact congrArg ρ hω
  have hstableρ : ∀ F : DistRd d → ℝ, Measurable F →
      (∃ C, ∀ x, |F x| ≤ C) →
      ∀ Θ : C(determSqR (d := d) R, ℝ) → ℝ, Continuous Θ →
        (∃ C, ∀ y, |Θ y| ≤ C) →
        Tendsto (fun n => ∫ ω, F (h ω) * Θ (ρ (L n ω)) ∂P) atTop
          (𝓝 (∫ ω, F (h ω) * Θ (ρ (Y ω)) ∂P)) := by
    intro F hF hFb Θ hΘ hΘb
    have ht := hstable F hF hFb (fun u => Θ (ρ u))
      (hΘ.comp hρ) ⟨Classical.choose hΘb, fun u => Classical.choose_spec hΘb (ρ u)⟩
    refine (tendsto_congr fun n => integral_congr_ae ?_).1 ht
    filter_upwards [hLe n] with ω hω
    rw [hω]
  letI : PolishSpace C(determSqR (d := d) R, ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  have key := determ_tendstoInMeasure_of_stable P h (fun ω => ρ (Y ω))
    (fun n ω => ρ (L n ω)) hh (fun n => hρ.measurable.comp (hL n))
    hstableρ hdetρ
  have hk := key (ENNReal.ofReal δ) (ENNReal.ofReal_pos.2 hδ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hk
    (fun _ => zero_le) fun n => measure_mono_ae ?_
  filter_upwards [hLe n] with ω hω hmem
  change ENNReal.ofReal δ ≤ _ at hmem ⊢
  refine hmem.trans (iSup₂_le fun p hp => ?_)
  have h1 : X n ω p = ρ (L n ω) ⟨p, hp⟩ := by
    rw [hω]
    rfl
  have h2 : Y ω p = ρ (Y ω) ⟨p, hp⟩ := rfl
  rw [h1, h2, edist_dist, edist_dist]
  exact ENNReal.ofReal_le_ofReal (ContinuousMap.dist_apply_le_dist _)

end HigherDimLQGMetric
