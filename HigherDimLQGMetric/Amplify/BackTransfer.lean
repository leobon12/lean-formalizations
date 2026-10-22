import HigherDimLQGMetric.Amplify.BackRaw
import HigherDimLQGMetric.Amplify.NormWeyl
import HigherDimLQGMetric.Sphere.Cont

/-! Almost-sure return transfer for every trial scale and center. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Filter Topology
open HigherDimLFPP (Rd)

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- A fine trial plus a quiet coarse field supplies the full-field bounds (15).
The a.s. statement is simultaneous over scales and centers. -/
theorem amplify_ae_back_of_trial
    (hd : 2 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ)
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (F : Ω → DistRd d) (g : Ω → C(Rd d, ℝ))
    (hF : Measurable F) (hg : Measurable g)
    (hH : IsWholeSpaceLGF (fun ω => F ω + ofCont (g ω)) P)
    (cs c1 ℓ δ : ℝ) (hc1 : 0 < c1) :
    ∀ᵐ ω ∂P, ∀ (s : ℝ) (_hs : 0 < s) (w : Rd d),
      (∀ x ∈ Metric.ball w (5 * s), ∀ y ∈ Metric.ball w (5 * s),
        |g ω x - g ω y| ≤ δ) →
      F ω ∈ TrialEvent D Dt ξ Q cs c1 ℓ δ s w →
      AmplifyBackEvent (D (F ω + ofCont (g ω)))
        (Dt (F ω + ofCont (g ω))) ξ Q cs c1 ℓ δ s w
        (F ω + ofCont (g ω)) := by
  have hFine : IsLGFPlusCont F P := by
    refine ⟨hF, fun ω => -g ω, hg.neg, ?_⟩
    convert hH using 1
    funext ω
    simp only [ofCont_neg, sub_neg_eq_add]
  have hconv := hFine.ae_continuousOn_sphereAvg hd
  have hwD := hD.weyl P F hFine
  have hwDt := hDt.weyl P F hFine
  filter_upwards [hconv, hwD, hwDt] with ω hc hwd hwdt
  intro s hs w hosc htrial
  let J := ann w (s / 2) (5 * s)
  let O := ann w (3 * s / 4) (3 * s)
  have hJopen : IsOpen J := isOpen_ann w _ _
  have hOopen : IsOpen O := isOpen_ann w _ _
  have hJsub : J ⊆ Metric.ball w (5 * s) := fun _ hx => hx.2
  have hOsub : O ⊆ Metric.ball w (5 * s) := by
    intro x hx
    have hlt : ‖x - w‖ < 5 * s := by
      have : ‖x - w‖ < 3 * s := hx.2
      linarith
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hlt
  have hlim := hc.1 s hs w
  have hJd (u v : Rd d) := amplify_normInt_weyl_mem_Icc
    (by omega : 1 ≤ d) hξ Q hs w (F ω) (g ω) hlim hosc D
    (fun x y => (hwd (g ω) x y).symm) hJopen hJsub u v
  have hOd (u v : Rd d) := amplify_normInt_weyl_mem_Icc
    (by omega : 1 ≤ d) hξ Q hs w (F ω) (g ω) hlim hosc D
    (fun x y => (hwd (g ω) x y).symm) hOopen hOsub u v
  have hOdt (u v : Rd d) := amplify_normInt_weyl_mem_Icc
    (by omega : 1 ≤ d) hξ Q hs w (F ω) (g ω) hlim hosc Dt
    (fun x y => (hwdt (g ω) x y).symm) hOopen hOsub u v
  exact amplify_backEvent_of_norm D Dt ξ Q cs c1 ℓ δ hs w
    (F ω + ofCont (g ω))
    (amplify_back_norm_bounds D Dt ξ Q cs c1 ℓ δ hc1 hs w (F ω)
      (F ω + ofCont (g ω)) htrial
      (fun u _ v _ => by simpa only [neg_mul, addFun_def, J] using (hJd u v).1)
      (fun u v => by simpa only [neg_mul, addFun_def, O] using (hOd u v).1)
      (fun u v => by simpa only [addFun_def, O] using
        (amplify_reverse_exp_bounds (ξ * δ)
          (by simpa only [neg_mul] using (hOd u v).1) (hOd u v).2).2)
      (fun u v => by simpa only [addFun_def, O] using (hOdt u v).2))

end HigherDimLQGMetric
