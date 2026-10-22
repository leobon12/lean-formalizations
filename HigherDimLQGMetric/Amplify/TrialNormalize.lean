import HigherDimLQGMetric.Freq.ConstLaw
import HigherDimLQGMetric.Amplify.TrialLocal
import HigherDimLQGMetric.Amplify.ScaleRatio

/-! Constant-shift invariance for the finite family of full-field trials. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Filter Topology Set
open HigherDimLFPP (Rd)

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- A full-field trial is invariant almost surely under recentering by the
unit-sphere average. -/
theorem amplify_ae_trial_normalize
    {ξ Q : ℝ} {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (hd : 2 ≤ d) (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    (cs c1 ℓ δ : ℝ) {s : ℝ} (hs : 0 < s) (w : Rd d) :
    ∀ᵐ ω ∂P, h ω ∈ TrialEvent D Dt ξ Q cs c1 ℓ δ s w ↔
      addConst (h ω) (-sphereAvg (h ω) 1 0) ∈
        TrialEvent D Dt ξ Q cs c1 ℓ δ s w := by
  let N : Ω → DistRd d :=
    fun ω => addConst (h ω) (-sphereAvg (h ω) 1 0)
  filter_upwards [hD.ae_normInt_normalize P h hh hd hs w,
    hDt.ae_normInt_normalize P h hh hd hs w] with ω hDn hDtn
  have hJ (u : Rd d) (_ : u ∈ ann w (s / 2) (5 * s))
      (v : Rd d) (_ : v ∈ ann w (s / 2) (5 * s)) :
      normInt ξ Q D (h ω) s w (ann w (s / 2) (5 * s)) u v =
        normInt ξ Q D (N ω) s w (ann w (s / 2) (5 * s)) u v :=
    hDn _ (isOpen_ann _ _ _) u v
  have hO (u : Rd d) (_ : u ∈ ann w (3 * s / 4) (3 * s))
      (v : Rd d) (_ : v ∈ ann w (3 * s / 4) (3 * s)) :
      normInt ξ Q D (h ω) s w (ann w (3 * s / 4) (3 * s)) u v =
        normInt ξ Q D (N ω) s w (ann w (3 * s / 4) (3 * s)) u v :=
    hDn _ (isOpen_ann _ _ _) u v
  have hOt (u : Rd d) (_ : u ∈ ann w (3 * s / 4) (3 * s))
      (v : Rd d) (_ : v ∈ ann w (3 * s / 4) (3 * s)) :
      normInt ξ Q Dt (h ω) s w (ann w (3 * s / 4) (3 * s)) u v =
        normInt ξ Q Dt (N ω) s w (ann w (3 * s / 4) (3 * s)) u v :=
    hDtn _ (isOpen_ann _ _ _) u v
  constructor
  · exact amplify_trial_saturated D Dt ξ Q cs c1 ℓ δ hs w
      (h ω) (N ω) hJ hO hOt
  · exact amplify_trial_saturated D Dt ξ Q cs c1 ℓ δ hs w
      (N ω) (h ω)
      (fun u hu v hv => (hJ u hu v hv).symm)
      (fun u hu v hv => (hO u hu v hv).symm)
      (fun u hu v hv => (hOt u hu v hv).symm)

omit [IsProbabilityMeasure P] in
/-- The Gaussian spherical-average increment is likewise unchanged by any
constant recentering, simultaneously over all positive scales and centers. -/
theorem amplify_ae_increment_normalize
    (hd : 2 ≤ d) (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P) :
    ∀ᵐ ω ∂P, ∀ (s r : ℝ) (_hs : 0 < s) (_hr : 0 < r)
      (w : Rd d),
      sphereAvg (addConst (h ω) (-sphereAvg (h ω) 1 0)) s w -
        sphereAvg (addConst (h ω) (-sphereAvg (h ω) 1 0)) r 0 =
      sphereAvg (h ω) s w - sphereAvg (h ω) r 0 := by
  filter_upwards [hh.ae_continuousOn_sphereAvg hd] with ω hω
  intro s r hs hr w
  rw [sphereAvg_addConst_of_tendsto (by omega : 1 ≤ d) (hω.1 s hs w),
    sphereAvg_addConst_of_tendsto (by omega : 1 ≤ d) (hω.1 r hr 0)]
  ring

end HigherDimLQGMetric
