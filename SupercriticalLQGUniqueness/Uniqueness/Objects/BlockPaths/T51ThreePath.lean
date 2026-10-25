import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Mesh.InternalShortcut




 





set_option autoImplicit false
noncomputable section

open Set Metric LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockPaths

 


theorem internal_le_three_path_join (D : LSCMetric) (K : Set ℂ)
    (hK : IsCompact K) {α β π : ℝ → ℂ}
    {a b c d s t r R : ℝ} {z : ℂ}
    (hα : D.IsCurve α a b) (hαK : MapsTo α (Icc a b) K)
    (hβ : D.IsCurve β c d) (hβK : MapsTo β (Icc c d) K)
    (hπ : D.IsCurve π s t) (hπK : MapsTo π (Icc s t) K)
    (hrR : r ≤ R)
    (hsep : LQGMetric.Disconnects (π '' Icc s t) (sphere z r) (sphere z R))
    (hαouter : R ≤ dist (α a) z) (hαinner : dist (α b) z ≤ r)
    (hβinner : dist (β c) z ≤ r) (hβouter : R ≤ dist (β d) z) :
    D.internal K
      (⟨α a, hαK (left_mem_Icc.mpr hα.1)⟩,
       ⟨β c, hβK (left_mem_Icc.mpr hβ.1)⟩) ≤
      D.len α a b + D.len π s t + D.len β c d := by
  have hαcont : ContinuousOn α (Icc a b) := hα.continuousOn_of_mapsTo hK hαK
  have hβcont : ContinuousOn β (Icc c d) := hβ.continuousOn_of_mapsTo hK hβK
  have hsep' := LQGMetric.Disconnects.closedBall_compl_ball hrR hsep
  have hαa : α a ∈ (ball z R)ᶜ := by
    simpa only [mem_compl_iff, mem_ball, not_lt] using hαouter
  have hαb : α b ∈ closedBall z r := by
    simpa only [mem_closedBall] using hαinner
  have hβc : β c ∈ closedBall z r := by
    simpa only [mem_closedBall] using hβinner
  have hβd : β d ∈ (ball z R)ᶜ := by
    simpa only [mem_compl_iff, mem_ball, not_lt] using hβouter
  obtain ⟨u, hu, huπ⟩ :=
    TwoScale.Mesh.pathHit_time hα.1 hαcont hsep'.symm hαa hαb
  obtain ⟨v, hv, hvπ⟩ :=
    TwoScale.Mesh.pathHit_time hβ.1 hβcont hsep' hβc hβd
  have hαcost : internalEDist (D.pt '' K) (D.pt (α a)) (D.pt (α u)) ≤
      D.len α a b :=
    TwoScale.Mesh.internal_trace_le_len D K α hα hαK
      ⟨a, left_mem_Icc.mpr hα.1, rfl⟩ ⟨u, hu, rfl⟩
  have hπcost : internalEDist (D.pt '' K) (D.pt (α u)) (D.pt (β v)) ≤
      D.len π s t :=
    TwoScale.Mesh.internal_trace_le_len D K π hπ hπK huπ hvπ
  have hβcost : internalEDist (D.pt '' K) (D.pt (β v)) (D.pt (β c)) ≤
      D.len β c d :=
    TwoScale.Mesh.internal_trace_le_len D K β hβ hβK
      ⟨v, hv, rfl⟩ ⟨c, left_mem_Icc.mpr hβ.1, rfl⟩
  rw [D.internal_eq_internalEDist]
  calc
    internalEDist (D.pt '' K) (D.pt (α a)) (D.pt (β c)) ≤
        internalEDist (D.pt '' K) (D.pt (α a)) (D.pt (α u)) +
          internalEDist (D.pt '' K) (D.pt (α u)) (D.pt (β c)) :=
      internalEDist_triangle _ _ _ _
    _ ≤ internalEDist (D.pt '' K) (D.pt (α a)) (D.pt (α u)) +
        (internalEDist (D.pt '' K) (D.pt (α u)) (D.pt (β v)) +
          internalEDist (D.pt '' K) (D.pt (β v)) (D.pt (β c))) :=
      add_le_add_right (internalEDist_triangle _ _ _ _) _
    _ ≤ D.len α a b + (D.len π s t + D.len β c d) :=
      add_le_add hαcost (add_le_add hπcost hβcost)
    _ = D.len α a b + D.len π s t + D.len β c d := by rw [add_assoc]


end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockPaths
