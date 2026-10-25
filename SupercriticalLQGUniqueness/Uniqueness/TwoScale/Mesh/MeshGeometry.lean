import LQGMetric.Papers.CONF.S3L35
import LQGMetric.Papers.CONF.S3L36D




 






set_option autoImplicit false
noncomputable section

open Set Metric Classical

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Mesh

open LQGMetric.Blueprint (annulus)

 
def mesh (m ρ : ℝ) (z₀ : ℂ) : Finset ℂ :=
  ((LQGMetric.CONF.gridBox m ρ z₀).image fun k =>
    (⟨(k.1 : ℝ) * m, (k.2 : ℝ) * m⟩ : ℂ)).filter fun z => z ∈ ball z₀ ρ

theorem mem_mesh_iff {m ρ : ℝ} (hm : 0 < m) (z₀ z : ℂ) :
    z ∈ mesh m ρ z₀ ↔
      z ∈ LQGMetric.Blueprint.gridPts m ∩ ball z₀ ρ := by
  constructor
  · intro hz
    obtain ⟨hzi, hzb⟩ := Finset.mem_filter.mp hz
    obtain ⟨⟨a, b⟩, -, rfl⟩ := Finset.mem_image.mp hzi
    exact ⟨⟨a, b, rfl⟩, hzb⟩
  · intro hz
    obtain ⟨k, hk, heq⟩ := LQGMetric.CONF.grid_ball_subset hm z₀ hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨k, hk, heq⟩, hz.2⟩

 
theorem exists_near_mesh {m ρ ρ' : ℝ} (hm : 0 < m)
    (hmargin : ρ + 2 * m ≤ ρ') (z₀ x : ℂ) (hx : x ∈ ball z₀ ρ) :
    ∃ z ∈ mesh m ρ' z₀, dist x z < 2 * m := by
  let z := LQGMetric.CONF.conf36Grid m x
  have hd : dist x z < 2 * m := by
    simpa only [dist_eq_norm] using LQGMetric.CONF.conf36Grid_norm_lt hm x
  have hzb : z ∈ ball z₀ ρ' := by
    rw [mem_ball] at hx ⊢
    calc
      dist z z₀ ≤ dist z x + dist x z₀ := dist_triangle _ _ _
      _ < 2 * m + ρ := by rw [dist_comm z x]; exact add_lt_add hd hx
      _ ≤ ρ' := by linarith
  exact ⟨z, (mem_mesh_iff hm z₀ z).2
    ⟨LQGMetric.CONF.conf36Grid_mem m x, hzb⟩, hd⟩

 
theorem mesh_card_le {m ρ : ℝ} (z₀ : ℂ) :
    (mesh m ρ z₀).card ≤ (2 * ⌈ρ / m⌉₊ + 1) ^ 2 := by
  exact (Finset.card_filter_le _ _).trans
    (Finset.card_image_le.trans (le_of_eq (LQGMetric.CONF.gridBox_card m ρ z₀)))

 

theorem mesh_annulus_subset {x z : ℂ} {ε r T : ℝ}
    (hnear : dist x z < ε / 2) (hinner : 2 * ε ≤ r)
    (houter : 2 * r + ε / 2 ≤ T) :
    (annulus z r (2 * r) : Set ℂ) ⊆ annulus x ε T := by
  intro w hw
  change r < ‖w - z‖ ∧ ‖w - z‖ < 2 * r at hw
  change ε < ‖w - x‖ ∧ ‖w - x‖ < T
  have htri₁ : dist w z ≤ dist w x + dist x z := dist_triangle _ _ _
  have htri₂ : dist w x ≤ dist w z + dist z x := dist_triangle _ _ _
  simp only [dist_eq_norm] at htri₁ htri₂
  rw [norm_sub_rev z x] at htri₂
  rw [dist_eq_norm] at hnear
  constructor <;> linarith

 
def scaleMesh (ε R : ℝ) (z₀ : ℂ) : Finset ℂ :=
  mesh (ε * R / 4) (3 * R) z₀

theorem exists_near_scaleMesh {ε R : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hR : 0 < R) (z₀ x : ℂ) (hx : x ∈ ball z₀ (2 * R)) :
    ∃ z ∈ scaleMesh ε R z₀, dist x z < ε * R / 2 := by
  have hm : 0 < ε * R / 4 := by positivity
  have hmargin : 2 * R + 2 * (ε * R / 4) ≤ 3 * R := by
    nlinarith [mul_le_mul_of_nonneg_right hε1 hR.le]
  simpa only [scaleMesh, show 2 * (ε * R / 4) = ε * R / 2 by ring] using
    exists_near_mesh hm hmargin z₀ x hx

theorem scaleMesh_card_le {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R)
    (z₀ : ℂ) :
    (scaleMesh ε R z₀).card ≤ (2 * ⌈12 / ε⌉₊ + 1) ^ 2 := by
  have hquot : (3 * R) / (ε * R / 4) = 12 / ε := by
    field_simp
    ring
  simpa only [scaleMesh, hquot] using
    (mesh_card_le (m := ε * R / 4) (ρ := 3 * R) z₀)

 
theorem scaleMesh_card_real_le {ε R : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hR : 0 < R) (z₀ : ℂ) :
    ((scaleMesh ε R z₀).card : ℝ) ≤ (27 / ε) ^ 2 := by
  have hcard : ((scaleMesh ε R z₀).card : ℝ) ≤
      (((2 * ⌈12 / ε⌉₊ + 1) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast scaleMesh_card_le hε hR z₀
  have hceil : (⌈12 / ε⌉₊ : ℝ) < 12 / ε + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hbase : ((2 * ⌈12 / ε⌉₊ + 1 : ℕ) : ℝ) ≤ 27 / ε := by
    push_cast
    have hinv : 1 ≤ 1 / ε := (le_div_iff₀ hε).2 (by linarith)
    simp only [div_eq_mul_inv] at hceil ⊢
    simp only [one_div] at hinv
    linarith
  calc
    ((scaleMesh ε R z₀).card : ℝ) ≤
        (((2 * ⌈12 / ε⌉₊ + 1) ^ 2 : ℕ) : ℝ) := hcard
    _ = (((2 * ⌈12 / ε⌉₊ + 1 : ℕ) : ℝ)) ^ 2 := by norm_cast
    _ ≤ (27 / ε) ^ 2 := by gcongr

 

theorem exists_mesh_annulus_at_hit {ε R r T : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R)
    (hrlo : 2 * (ε * R) ≤ r)
    (hrhi : 2 * r + ε * R / 2 ≤ T)
    (z₀ x : ℂ) (hx : x ∈ ball z₀ (2 * R)) :
    ∃ z ∈ scaleMesh ε R z₀, dist x z < ε * R / 2 ∧
      (annulus z r (2 * r) : Set ℂ) ⊆ annulus x (ε * R) T := by
  obtain ⟨z, hz, hnear⟩ := exists_near_scaleMesh hε hε1 hR z₀ x hx
  exact ⟨z, hz, hnear, mesh_annulus_subset hnear hrlo hrhi⟩


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Mesh
