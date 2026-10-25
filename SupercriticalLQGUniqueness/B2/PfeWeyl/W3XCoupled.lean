import SupercriticalLQGUniqueness.B2.Final.CouplingData
import SupercriticalLQGUniqueness.B2.PfeWeyl.W3Stochastic

 












set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC)

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 

theorem ae_weyl_scaling_coupled
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    {e : ℕ → Set.Ioi (0 : ℝ)} {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    {V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    {h' : Ω' → DistC} {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}
    (hB : Final.DG20CouplingData ξ Q m e c V P' h' hN L)
    (hSA : Final.CoupledSmallAnnuli ξ m e V P' hN L)
    (hAT : Final.CoupledAcrossTails P' L) :
    ∀ᵐ ω ∂P', ∀ (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ z, |f z| ≤ M),
      ∃ E : LSCMetric, (∀ p, E p = weylScale (ξ : ℝ) f (L ω) p) ∧
        Tendsto (fun n => normalizedLFPPMetric (ξ : ℝ) (m (e n))
          (V (e n) (hN n ω) + LQGMetric.LFPP.mollCont (e n : ℝ)
            (e n).property.ne' f M hM)) atTop (𝓝 E) := by
  filter_upwards [hB.metric_tendsto, hB.geometry,
    ae_acrossUnbounded_of_acrossTail P' L hAT,
    ae_all_iff.2 hSA] with ω hG hGeom hAcross hSmall f M hM
  exact weyl_scaling_sample (ξ : ℝ) (le_of_lt ξ.property)
    (fun n => m (e n)) (fun n => V (e n) (hN n ω)) (L ω)
    hG hGeom.1
    (B2.PfeLocal.continuous_euclidForget_of_small_metric _ hGeom.2.1)
    hAcross hSmall (fun n => (e n : ℝ))
    (fun n => (e n).property.ne') hB.scale_tendsto f M hM

 

theorem ae_weyl_scaling_coupled_of_identification
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    {e : ℕ → Set.Ioi (0 : ℝ)} {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    {V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    {h' : Ω' → DistC} {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}
    (hB : Final.DG20CouplingData ξ Q m e c V P' h' hN L)
    (hSA : Final.CoupledSmallAnnuli ξ m e V P' hN L)
    (hAT : Final.CoupledAcrossTails P' L)
    (Φ : DistC → LSCMetric) (hII : ∀ᵐ ω ∂P', L ω = Φ (h' ω)) :
    ∀ᵐ ω ∂P', ∀ (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ z, |f z| ≤ M),
      ∃ E : LSCMetric, (∀ p, E p = weylScale (ξ : ℝ) f (Φ (h' ω)) p) ∧
        Tendsto (fun n => normalizedLFPPMetric (ξ : ℝ) (m (e n))
          (V (e n) (hN n ω) + LQGMetric.LFPP.mollCont (e n : ℝ)
            (e n).property.ne' f M hM)) atTop (𝓝 E) := by
  filter_upwards [ae_weyl_scaling_coupled P' hB hSA hAT, hII] with ω hW hEq f M hM
  simpa only [hEq] using hW f M hM

end SupercriticalLQGUniqueness.B2.PfeWeyl
