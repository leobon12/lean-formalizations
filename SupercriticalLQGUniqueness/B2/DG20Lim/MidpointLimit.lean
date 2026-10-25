import SupercriticalLQGUniqueness.B2.DG20Lim.MidpointLimitBound

 

set_option autoImplicit false
noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RData.midpoint_bounds_of_trapped_subseq
    (R : RData) (D : ℕ → LQGMetric.ContMetric)
    (hlen : ∀ n, (D n).IsLength)
    (hcircle : ∀ O P : RatCircle,
      Tendsto (fun n => LQGMetric.Blueprint.setDist (D n) O.toSet P.toSet)
        atTop (𝓝 (R.across O P)))
    (u v x : ℂ) (hfinite : R.DfromR u v ≠ ∞)
    (zn wn xn : ℕ → ℂ) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hzn : Tendsto zn atTop (𝓝 u))
    (hwn : Tendsto wn atTop (𝓝 v))
    (hx : Tendsto (xn ∘ φ) atTop (𝓝 x))
    (hdist : Tendsto (fun n => ENNReal.ofReal ((D n).1 (zn n, wn n)))
      atTop (𝓝 (R.DfromR u v)))
    (hmid : ∀ n,
      (D n).1 (zn n, xn n) ≤
        (D n).1 (zn n, wn n) / 2 + midpointError n ∧
      (D n).1 (wn n, xn n) ≤
        (D n).1 (zn n, wn n) / 2 + midpointError n) :
    R.DfromR u x ≤ ENNReal.ofReal ((R.DfromR u v).toReal / 2) ∧
    R.DfromR v x ≤ ENNReal.ofReal ((R.DfromR u v).toReal / 2) := by
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  let E : ℕ → LQGMetric.ContMetric := D ∘ φ
  have hlenE : ∀ n, (E n).IsLength := fun n => hlen (φ n)
  have hcircleE : ∀ O P : RatCircle,
      Tendsto (fun n => LQGMetric.Blueprint.setDist (E n) O.toSet P.toSet)
        atTop (𝓝 (R.across O P)) := by
    intro O P
    exact (hcircle O P).comp hφtop
  let zE : ℕ → ℂ := zn ∘ φ
  let wE : ℕ → ℂ := wn ∘ φ
  let xE : ℕ → ℂ := xn ∘ φ
  have hzE : Tendsto zE atTop (𝓝 u) := hzn.comp hφtop
  have hwE : Tendsto wE atTop (𝓝 v) := hwn.comp hφtop
  have hxE : Tendsto xE atTop (𝓝 x) := hx
  have hdistE : Tendsto (fun n => ENNReal.ofReal ((E n).1 (zE n, wE n)))
      atTop (𝓝 (R.DfromR u v)) := hdist.comp hφtop
  have hδE : Tendsto (midpointError ∘ φ) atTop (𝓝 0) :=
    midpointError_tendsto.comp hφtop
  have hb : ∀ n, 0 ≤ (E n).1 (zE n, wE n) := by
    intro n
    rw [← (E n).dist_pt]
    exact dist_nonneg
  have hleft := R.le_liminf_pointDist E hlenE hcircleE zE xE hzE hxE
  have hright := R.le_liminf_pointDist E hlenE hcircleE wE xE hwE hxE
  constructor
  · exact hleft.trans (liminf_approx_midpoint_le_half
      (fun n => (E n).1 (zE n, xE n))
      (fun n => (E n).1 (zE n, wE n)) (midpointError ∘ φ) hb
      (R.DfromR u v) hfinite hdistE hδE (fun n => (hmid (φ n)).1))
  · exact hright.trans (liminf_approx_midpoint_le_half
      (fun n => (E n).1 (wE n, xE n))
      (fun n => (E n).1 (zE n, wE n)) (midpointError ∘ φ) hb
      (R.DfromR u v) hfinite hdistE hδE (fun n => (hmid (φ n)).2))

end SupercriticalLQGUniqueness.B2.DG20Lim
