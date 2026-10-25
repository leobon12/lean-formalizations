import SupercriticalLQGUniqueness.B2.PfeWeyl.R68S1TInputs
import SupercriticalLQGUniqueness.B2.PfeWeyl.W3Circle

 







set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 


theorem ae_coupled_weyl_rationalCircle_all_bounded
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (e : ℕ → Ioi (0 : ℝ)) (c : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (V : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    (h' : Ω' → DistC) (hN : ℕ → Ω' → DistC) (L : Ω' → LSCMetric)
    (hB : Final.DG20CouplingData ξ Q m e c V P' h' hN L)
    (hSA : Final.CoupledSmallAnnuli ξ m e V P' hN L)
    (hAT : Final.CoupledAcrossTails P' L)
    (hCirc : CoupledAllRationalCircles ξ m e V P' hN L) :
    ∀ᵐ ω ∂P', ∀ (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ z, |f z| ≤ M)
      (O O' : Set ℂ), IsRationalCircle O → IsRationalCircle O' →
      Tendsto (fun n => setDistance
        (normalizedLFPPMetric (ξ : ℝ) (m (e n))
          (V (e n) (hN n ω) +
            LQGMetric.LFPP.mollCont (e n : ℝ) (e n).property.ne' f M hM)) O O')
        atTop (𝓝 (setDistance (weylScale (ξ : ℝ) f (L ω)) O O')) := by
  have hlen : ∀ᵐ ω ∂P', (L ω).IsLengthSpace :=
    hB.geometry.mono fun _ hω => hω.1
  have hctrl : ∀ᵐ ω ∂P', ∀ u : ℂ, ∀ δ : ℝ, 0 < δ →
      ∃ η : ℝ, 0 < η ∧ ∀ v : ℂ,
        (L ω).1 (u, v) < ENNReal.ofReal η → dist u v < δ :=
    hB.geometry.mono fun _ hω => hω.2.1
  filter_upwards [hB.metric_tendsto, hlen, hctrl,
    ae_acrossUnbounded_of_acrossTail P' L hAT,
    ae_all_iff.2 hSA, hCirc] with ω hG hL hC hA hS hcirc f M hM O O' hO hO'
  have he0 : ∀ n, (e n : ℝ) ≠ 0 := fun n => (e n).property.ne'
  exact weyl_rationalCircle_tendsto hG
    (fun n => isLengthSpace_normalizedLFPPMetric (ξ : ℝ) (m (e n)) (V (e n) (hN n ω)))
    (fun n => PfeAxioms.continuous_euclidForget_normalizedLFPPMetric (ξ : ℝ) (m (e n)) _)
    (ξ : ℝ) (le_of_lt ξ.property) f
    (fun n => LQGMetric.LFPP.mollCont (e n : ℝ) (he0 n) f M hM)
    (fun K hK η hη => mollCont_fixed_tendsto_compact he0 hB.scale_tendsto f M hM K hK η hη)
    M hM (fun n z => abs_mollCont_le (he0 n) f M hM z) hL
    (B2.PfeLocal.continuous_euclidForget_of_small_metric _ hC) hA
    (fun n => normalizedLFPPMetric (ξ : ℝ) (m (e n))
      (V (e n) (hN n ω) + LQGMetric.LFPP.mollCont (e n : ℝ) (he0 n) f M hM))
    (fun n x y => normalizedLFPPMetric_add_eq_weylScale (ξ : ℝ) (m (e n)) _ _ (x, y))
    (fun n => PfeAxioms.continuous_euclidForget_normalizedLFPPMetric (ξ : ℝ) (m (e n)) _)
    hS hcirc hO hO'

end SupercriticalLQGUniqueness.B2.PfeWeyl
