import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaFinite

 








set_option autoImplicit false
noncomputable section

open Set Filter Topology

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem eventually_inside_annulus
    (A : EuclideanAnnulus) (z : ℂ)
    (hz : dist z A.center < A.innerRadius)
    {p : ℕ → ℂ} (hp : Tendsto p atTop (𝓝 z)) :
    ∀ᶠ n in atTop,
      p n ∈ Metric.closedBall A.center A.innerRadius := by
  have hzball : z ∈ Metric.ball A.center A.innerRadius := by
    simpa only [Metric.mem_ball, dist_comm] using hz
  exact (hp.eventually (Metric.isOpen_ball.mem_nhds hzball)).mono
    (fun _ hn => Metric.ball_subset_closedBall hn)

theorem eventually_outside_annulus
    (A : EuclideanAnnulus) (z w : ℂ)
    (hz : dist z A.center < A.innerRadius)
    (hfar : 2 * A.outerRadius < dist z w)
    {p : ℕ → ℂ} (hp : Tendsto p atTop (𝓝 w)) :
    ∀ᶠ n in atTop,
      p n ∉ Metric.ball A.center A.outerRadius := by
  have htri : dist z w ≤ dist z A.center + dist w A.center := by
    simpa only [dist_comm w A.center] using dist_triangle z A.center w
  have hwfar : A.outerRadius < dist w A.center := by
    have hrad : A.innerRadius ≤ A.outerRadius := A.2.2.le
    linarith
  have hwclosed : w ∉ Metric.closedBall A.center A.outerRadius := by
    simp only [Metric.mem_closedBall, not_le]
    simpa only [dist_comm] using hwfar
  have hopen : IsOpen (Metric.closedBall A.center A.outerRadius)ᶜ :=
    Metric.isClosed_closedBall.isOpen_compl
  exact (hp.eventually (hopen.mem_nhds hwclosed)).mono
    (fun _ hn hball => hn (Metric.ball_subset_closedBall hball))

end SupercriticalLQGUniqueness.B2.PfeAxioms
