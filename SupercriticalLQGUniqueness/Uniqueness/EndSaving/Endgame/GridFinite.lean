import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame.EndpointGeometry
import LQGMetric.Papers.CONF.S3L35




 
set_option autoImplicit false
noncomputable section
open Set
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame

 
def endpointSites (m b : ℝ) : Finset ℂ :=
  (LQGMetric.CONF.gridBox m b 0).image
    fun k => (⟨(k.1 : ℝ) * m, (k.2 : ℝ) * m⟩ : ℂ)

theorem gridPt_mem_endpointSites {m b : ℝ} (hm : 0 < m)
    {i : ℤ × ℤ} (hi : LQGMetric.GM.gridPt m i ∈ Metric.ball (0 : ℂ) b) :
    LQGMetric.GM.gridPt m i ∈ endpointSites m b := by
  have hgrid : LQGMetric.GM.gridPt m i ∈ LQGMetric.Blueprint.gridPts m := by
    refine ⟨i.1, i.2, ?_⟩
    apply Complex.ext <;> simp [LQGMetric.GM.gridPt] <;> ring
  obtain ⟨k, hk, heq⟩ := LQGMetric.CONF.grid_ball_subset hm 0 ⟨hgrid, hi⟩
  exact Finset.mem_image.mpr ⟨k, hk, heq⟩

theorem endpointSites_card_le (m b : ℝ) :
    (endpointSites m b).card ≤ (2 * ⌈b / m⌉₊ + 1) ^ 2 := by
  unfold endpointSites
  exact (Finset.card_image_le).trans
    (le_of_eq (LQGMetric.CONF.gridBox_card _ _ _))

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
