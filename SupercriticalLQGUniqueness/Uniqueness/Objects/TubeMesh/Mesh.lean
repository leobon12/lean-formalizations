import SupercriticalLQGUniqueness.Uniqueness.Objects.TubeMesh.GridGeometry
import LQGMetric.Papers.CONF.S3D112L1b




 







set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.TubeMesh

open LQGMetric.Blueprint (confSq confSqIdx)
open LQGMetric.CONF (confCtr confGridRel)

 

theorem finite_connected_mesh {U : Set ℂ} (hOpen : IsOpen U)
    (hBounded : Bornology.IsBounded U) (hConn : IsPathConnected U)
    {R : ℝ} (hUann : U ⊆ LQGMetric.Blueprint.annulus 0 0 R)
    (γ : C(unitInterval, ℂ)) (hγ : range γ ⊆ U)
    {B E : Set ℂ} (hSep : LQGMetric.Disconnects (range γ) B E)
    {a : ℝ} (ha : 0 < a) :
    ∃ (ρ₀ : ℝ) (X : Finset ℂ),
      0 < ρ₀ ∧ ρ₀ ≤ a / 4 ∧ X.Nonempty ∧
      (∀ x ∈ X, closedBall x (2 * ρ₀) ⊆ U) ∧
      (∀ x ∈ X, ∀ y ∈ X,
        Relation.ReflTransGen
          (fun u v : ℂ => u ∈ X ∧ v ∈ X ∧ ρ₀ < dist u v ∧ dist u v < 2 * ρ₀) x y) ∧
      LQGMetric.Disconnects (⋃ x ∈ X, ball x ρ₀) B E ∧
      (∀ y ∈ closure U, ∃ x ∈ X, dist y x ≤ a / 2) := by
  classical
  obtain ⟨F, hF⟩ := finite_interior_cover hBounded ha
  let K := core hConn γ hγ F
  have hKcompact : IsCompact K := core_compact hConn γ hγ F
  have hKpre : IsPreconnected K := core_preconnected hConn γ hγ F
  have hKU : K ⊆ U := core_subset hConn γ hγ F
  obtain ⟨δ, hδpos, hδU⟩ := hKcompact.exists_cthickening_subset_open hOpen hKU
  let ρ₀ : ℝ := min (a / 4) (δ / 4)
  let ε : ℝ := 6 * ρ₀ / 5
  have hρpos : 0 < ρ₀ := lt_min (by linarith) (by linarith)
  have hρa : ρ₀ ≤ a / 4 := min_le_left _ _
  have hρδ : ρ₀ ≤ δ / 4 := min_le_right _ _
  have hεδ : 0 < ε := by dsimp [ε]; positivity
  have hεnear : 3 * ε / 4 < ρ₀ := by dsimp [ε]; linarith
  have hεedge : ρ₀ < ε ∧ ε < 2 * ρ₀ := by dsimp [ε]; constructor <;> linarith
  have h3ρδ : 3 * ρ₀ ≤ δ := by linarith
  have hKann : K ⊆ LQGMetric.Blueprint.annulus 0 0 R := by
    intro w hw
    exact hUann (hKU hw)
  have hIfin : (confSqIdx ε 0 K).Finite :=
    (LQGMetric.CONF.finite_confSqIdx_annulus hεδ 0 0 R).subset (by
      intro k hk
      obtain ⟨w, hwSq, hwK⟩ := hk
      exact ⟨w, hwSq, hKann hwK⟩)
  let I : Finset (ℤ × ℤ) := hIfin.toFinset
  let X : Finset ℂ := I.image (confCtr ε 0)
  have hI : ∀ {k : ℤ × ℤ}, k ∈ I ↔ k ∈ confSqIdx ε 0 K := by
    intro k
    exact hIfin.mem_toFinset
  have hsite : ∀ {k : ℤ × ℤ}, k ∈ confSqIdx ε 0 K → confCtr ε 0 k ∈ X := by
    intro k hk
    exact Finset.mem_image.mpr ⟨k, hI.mpr hk, rfl⟩
  have hnear : ∀ w ∈ K, ∃ x ∈ X, dist w x < ρ₀ := by
    intro w hw
    let k := LQGMetric.CONF.confFloorIdx ε 0 w
    have hwSq : w ∈ confSq ε 0 k := LQGMetric.CONF.confFloorIdx_mem hεδ 0 w
    have hk : k ∈ confSqIdx ε 0 K := ⟨w, hwSq, hw⟩
    refine ⟨confCtr ε 0 k, hsite hk, ?_⟩
    exact (dist_square_center_lt hεδ k hwSq).trans hεnear
  have hM1 : ∀ x ∈ X, closedBall x (2 * ρ₀) ⊆ U := by
    intro x hx y hy
    obtain ⟨k, hkI, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w, hwSq, hwK⟩ := (hI.mp hkI)
    have hwNear : dist w (confCtr ε 0 k) < ρ₀ :=
      (dist_square_center_lt hεδ k hwSq).trans hεnear
    have hyx : dist y (confCtr ε 0 k) ≤ 2 * ρ₀ := hy
    have hyw : dist y w ≤ δ := by
      calc dist y w ≤ dist y (confCtr ε 0 k) + dist (confCtr ε 0 k) w :=
          dist_triangle _ _ _
        _ ≤ δ := by rw [dist_comm (confCtr ε 0 k) w]; linarith
    exact hδU (mem_cthickening_of_dist_le y w δ K hwK hyw)
  have hM2 : ∀ x ∈ X, ∀ y ∈ X,
      Relation.ReflTransGen
        (fun u v : ℂ => u ∈ X ∧ v ∈ X ∧ ρ₀ < dist u v ∧ dist u v < 2 * ρ₀) x y := by
    intro x hx y hy
    obtain ⟨k, hkI, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k', hk'I, rfl⟩ := Finset.mem_image.mp hy
    have hconn := LQGMetric.CONF.confSqIdx_rtg_of_isPreconnected hεδ 0 hKpre
      (hI.mp hkI) (hI.mp hk'I)
    have hlift : ∀ {j j' : ℤ × ℤ},
        Relation.ReflTransGen (confGridRel (confSqIdx ε 0 K)) j j' →
        Relation.ReflTransGen
          (fun u v : ℂ => u ∈ X ∧ v ∈ X ∧ ρ₀ < dist u v ∧ dist u v < 2 * ρ₀)
          (confCtr ε 0 j) (confCtr ε 0 j') := by
      intro j j' h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail hab hbc ih =>
        apply Relation.ReflTransGen.tail ih
        have hd := dist_adjacent_centers hεδ hbc.1
        exact ⟨hsite hbc.2.1, hsite hbc.2.2,
          by rw [hd]; exact hεedge.1,
          by rw [hd]; exact hεedge.2⟩
    exact hlift hconn
  have hCover : range γ ⊆ ⋃ x ∈ X, ball x ρ₀ := by
    intro w hw
    obtain ⟨x, hx, hdist⟩ := hnear w ((spine_subset_core hConn γ hγ F) hw)
    exact mem_iUnion₂.mpr ⟨x, hx, by simpa only [mem_ball] using hdist⟩
  have hM3 : LQGMetric.Disconnects (⋃ x ∈ X, ball x ρ₀) B E :=
    hSep.mono hCover le_rfl le_rfl
  have hM4 : ∀ y ∈ closure U, ∃ x ∈ X, dist y x ≤ a / 2 := by
    intro y hy
    obtain ⟨c, hcF, hyc⟩ := hF y hy
    obtain ⟨x, hxX, hcx⟩ := hnear (c : ℂ) (mem_core_of_mem hConn γ hγ hcF)
    refine ⟨x, hxX, ?_⟩
    calc dist y x ≤ dist y (c : ℂ) + dist (c : ℂ) x := dist_triangle _ _ _
      _ ≤ a / 2 := by linarith
  have hXne : X.Nonempty := by
    obtain ⟨x, hx, -⟩ := hnear (γ 0) ((spine_subset_core hConn γ hγ F) ⟨0, rfl⟩)
    exact ⟨x, hx⟩
  exact ⟨ρ₀, X, hρpos, hρa, hXne, hM1, hM2, hM3, hM4⟩


end SupercriticalLQGUniqueness.Uniqueness.Objects.TubeMesh
