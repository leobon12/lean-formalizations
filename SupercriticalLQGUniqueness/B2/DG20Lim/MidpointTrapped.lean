import SupercriticalLQGUniqueness.B2.DG20Lim.MidpointSubsequence

 


set_option autoImplicit false
noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RData.exists_trapped_approx_midpoints
    (R : RData)
    (hlarge : ∀ N : ℕ, ∃ r : {r : ℚ // 1 < r},
      (N : ℝ) < (r : ℚ) ∧
      ENNReal.ofReal ((N : ℝ) + 1) ≤ R.across
        (centeredInnerCircle 0 0 r.1 (lt_trans zero_lt_one r.property))
        (centeredOuterCircle 0 0 r.1 (lt_trans zero_lt_one r.property)))
    (D : ℕ → LQGMetric.ContMetric) (hlen : ∀ n, (D n).IsLength)
    (hcircle : ∀ O P : RatCircle,
      Tendsto (fun n => LQGMetric.Blueprint.setDist (D n) O.toSet P.toSet)
        atTop (𝓝 (R.across O P)))
    (u v : ℂ) (hfinite : R.DfromR u v ≠ ∞)
    (zn wn : ℕ → ℂ)
    (hzn : Tendsto zn atTop (𝓝 u))
    (_hwn : Tendsto wn atTop (𝓝 v))
    (hdist : Tendsto (fun n => ENNReal.ofReal ((D n).1 (zn n, wn n)))
      atTop (𝓝 (R.DfromR u v))) :
    ∃ (xn : ℕ → ℂ) (φ : ℕ → ℕ) (x : ℂ),
      StrictMono φ ∧ Tendsto (xn ∘ φ) atTop (𝓝 x) ∧
      (∀ n, (D n).1 (zn n, xn n) ≤
        (D n).1 (zn n, wn n) / 2 + midpointError n ∧
        (D n).1 (wn n, xn n) ≤
          (D n).1 (zn n, wn n) / 2 + midpointError n) := by
  obtain ⟨O, P, hOP, huO, hgap⟩ := R.exists_large_circle_gap hlarge u v hfinite
  obtain ⟨xn, hmid⟩ := exists_finite_approx_midpoints D hlen zn wn
  have hshort : ∀ᶠ n in atTop,
      ENNReal.ofReal ((D n).1 (zn n, xn n)) ≤
        ENNReal.ofReal ((D n).1 (zn n, wn n)) + 1 :=
    Eventually.of_forall (fun n => approx_midpoint_short_left_leg
      D zn wn xn (fun n => (hmid n).1) n)
  have hbound := eventually_mem_outerDisk_of_short_left_leg
    R D hlen O P hOP huO zn wn xn hzn hdist (hcircle O P) hshort hgap
  obtain ⟨x, φ, hφ, hx⟩ :=
    exists_euclidean_subseq_of_eventually_closedDisk xn P hbound
  exact ⟨xn, φ, x, hφ, hx, hmid⟩

end SupercriticalLQGUniqueness.B2.DG20Lim
