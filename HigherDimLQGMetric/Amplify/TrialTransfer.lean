import HigherDimLQGMetric.Amplify.NormWeyl
import HigherDimLQGMetric.Amplify.TransferNorm
import HigherDimLQGMetric.Sphere.Cont

/-! Almost-sure transfer of a full-field witness to a fine-field trial. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Filter Topology
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- The Weyl comparison behind the first transfer of Lemma 6.1, valid
simultaneously for every trial centre and radius. -/
theorem amplify_ae_trial_of_wit
    (hd : 2 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ)
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (F : Ω → DistRd d) (g : Ω → C(Rd d, ℝ))
    (hF : Measurable F) (hg : Measurable g)
    (hH : IsWholeSpaceLGF (fun ω => F ω + ofCont (g ω)) P)
    (cs a A₀ ℓ β₀ c1 δ : ℝ) (hc1 : 0 < c1) (hℓ : 0 < ℓ) :
    ∀ᵐ ω ∂P, ∀ (s : ℝ) (_hs : 0 < s) (w : Rd d),
      (∀ x ∈ Metric.ball w (5 * s), ∀ y ∈ Metric.ball w (5 * s),
        |g ω x - g ω y| ≤ δ) →
      F ω + ofCont (g ω) ∈
        WitEvent Dt D ξ Q cs⁻¹ a A₀ ℓ β₀ c1⁻¹ s w →
      F ω ∈ TrialEvent D Dt ξ Q cs c1 ℓ δ s w := by
  let H : Ω → DistRd d := fun ω => F ω + ofCont (g ω)
  have hFine : IsLGFPlusCont F P := by
    refine ⟨hF, fun ω => -g ω, hg.neg, ?_⟩
    convert hH using 1
    funext ω
    simp only [ofCont_neg, sub_neg_eq_add]
  have hconv := hFine.ae_continuousOn_sphereAvg hd
  have hwD := hD.weyl P F hFine
  have hwDt := hDt.weyl P F hFine
  filter_upwards [hconv, hwD, hwDt] with ω hc hwd hwdt
  intro s hs w hosc hwit
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
  have hlim := (hc.1 s hs w)
  have hJd (u v : Rd d) := amplify_normInt_weyl_mem_Icc
    (by omega : 1 ≤ d) hξ Q hs w (F ω) (g ω) hlim hosc D
    (fun x y => (hwd (g ω) x y).symm) hJopen hJsub u v
  have hOd (u v : Rd d) := amplify_normInt_weyl_mem_Icc
    (by omega : 1 ≤ d) hξ Q hs w (F ω) (g ω) hlim hosc D
    (fun x y => (hwd (g ω) x y).symm) hOopen hOsub u v
  have hOdt (u v : Rd d) := amplify_normInt_weyl_mem_Icc
    (by omega : 1 ≤ d) hξ Q hs w (F ω) (g ω) hlim hosc Dt
    (fun x y => (hwdt (g ω) x y).symm) hOopen hOsub u v
  have hDj (u v : Rd d) :=
    (amplify_reverse_exp_bounds (ξ * δ)
      (by simpa only [neg_mul] using (hJd u v).1) (hJd u v).2).1
  have hDol (u v : Rd d) :=
    (amplify_reverse_exp_bounds (ξ * δ)
      (by simpa only [neg_mul] using (hOd u v).1) (hOd u v).2).1
  have hDoh (u v : Rd d) := (hOd u v).2
  have hDtt (u v : Rd d) :=
    (amplify_reverse_exp_bounds (ξ * δ)
      (by simpa only [neg_mul] using (hOdt u v).1) (hOdt u v).2).2
  exact amplify_trial_of_wit_norm_bounds D Dt ξ Q cs a A₀ ℓ β₀ c1 δ
    hc1 hℓ hs w (H ω) (F ω) hwit
    (fun u _ v _ => by simpa only [neg_mul, H, addFun_def, J] using hDj u v)
    (fun u v => by simpa only [neg_mul, H, addFun_def, O] using hDol u v)
    (fun u v => by simpa only [H, addFun_def, O] using hDoh u v)
    (fun u v => by simpa only [H, addFun_def, O] using hDtt u v)

end HigherDimLQGMetric
