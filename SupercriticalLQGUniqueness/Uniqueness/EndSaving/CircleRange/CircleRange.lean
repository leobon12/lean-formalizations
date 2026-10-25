import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces.Section4Interfaces
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.CircleRange.SizeWindowArithmetic
import LQGMetric.Papers.CONF.S3D114S4
import LQGMetric.Papers.CONF.S3D110A
import LQGMetric.Papers.GM.S3.DeterministicScale




 



set_option autoImplicit false
noncomputable section
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.CircleRange
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces

 

theorem exists_dyadic_size_bin {S : ℝ} (hS : 0 < S) :
    ∃ q : ℝ, IsDyadicSize q ∧ q ≤ S ∧ S < 2 * q := by
  obtain ⟨j, hj⟩ := exists_mem_Ico_zpow hS (by norm_num : (1 : ℝ) < 2)
  refine ⟨(2 : ℝ) ^ j, ⟨j, rfl⟩, hj.1, ?_⟩
  calc
    S < (2 : ℝ) ^ (j + 1) := hj.2
    _ = 2 * (2 : ℝ) ^ j := by rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]; ring

 

theorem offcentre_closed_annulus_strict_slack
    {z w x : ℂ} {r : ℝ} (hr : 0 < r)
    (hw : dist w z ≤ r / 50)
    (hxInner : r ≤ dist x w) (hxOuter : dist x w ≤ 4 * r) :
    (0.19 : ℝ) * (5 * r) < dist x z ∧
      dist x z < (0.81 : ℝ) * (5 * r) := by
  have ht₁ := dist_triangle x z w
  have ht₂ := dist_triangle x w z
  have hsym : dist z w = dist w z := dist_comm z w
  constructor <;> linarith only [hr, hw, hxInner, hxOuter, ht₁, ht₂, hsym]

 

theorem offcentre_closed_annulus_subset_open
    {z w : ℂ} {r : ℝ} (hr : 0 < r) (hw : dist w z ≤ r / 50) :
    {x : ℂ | r ≤ dist x w ∧ dist x w ≤ 4 * r} ⊆
      (LQGMetric.Blueprint.annulus z ((0.19 : ℝ) * (5 * r))
        ((0.81 : ℝ) * (5 * r)) : Set ℂ) := by
  intro x hx
  have h := offcentre_closed_annulus_strict_slack hr hw hx.1 hx.2
  change (0.19 : ℝ) * (5 * r) < ‖x - z‖ ∧
    ‖x - z‖ < (0.81 : ℝ) * (5 * r)
  simpa only [dist_eq_norm] using h

 

theorem closed_endpoint_balls_eligible
    {b s κ : ℝ} {z w : ℂ}
    (_hb : 0 < b) (hs : 0 ≤ s) (hsb : s < b)
    (hz : z ∈ Metric.ball (0 : ℂ) b)
    (hw : w ∈ Metric.ball (0 : ℂ) b)
    (hsep : κ * b ≤ dist z w) (hsmall : 2 * s < κ * b) :
    (Metric.closedBall z s).Nonempty ∧
    (Metric.closedBall w s).Nonempty ∧
    IsCompact (Metric.closedBall z s) ∧
    IsCompact (Metric.closedBall w s) ∧
    Disjoint (Metric.closedBall z s) (Metric.closedBall w s) ∧
    Metric.closedBall z s ⊆ Metric.ball (0 : ℂ) (2 * b) ∧
    Metric.closedBall w s ⊆ Metric.ball (0 : ℂ) (2 * b) := by
  have hcontain (c : ℂ) (hc : c ∈ Metric.ball (0 : ℂ) b) :
      Metric.closedBall c s ⊆ Metric.ball (0 : ℂ) (2 * b) := by
    intro x hx
    have htri := dist_triangle x c 0
    have hcx : dist x c ≤ s := Metric.mem_closedBall.mp hx
    have hc0 : dist c 0 < b := by simpa only [dist_comm] using (Metric.mem_ball.mp hc)
    apply Metric.mem_ball.mpr
    linarith only [htri, hcx, hc0, hsb]
  refine ⟨⟨z, Metric.mem_closedBall_self hs⟩,
    ⟨w, Metric.mem_closedBall_self hs⟩,
    isCompact_closedBall z s, isCompact_closedBall w s, ?_,
    hcontain z hz, hcontain w hw⟩
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hz' : dist z x ≤ s := by simpa only [dist_comm] using (Metric.mem_closedBall.mp hx)
  have hw' : dist x w ≤ s := Metric.mem_closedBall.mp hy
  have htri := dist_triangle z x w
  linarith only [hsep, hsmall, hz', hw', htri]

 


theorem strict_gap_after_five_paths
    {C c δ e d main endpoint : ℝ}
    (hd : 0 < d)
    (he : e < c * δ)
    (hmain : main ≤ (C - 2 * c * δ) * d)
    (hendpoint : endpoint ≤ e * d) :
    main + endpoint < (C - c * δ) * d := by
  have hslack : 0 < (c * δ - e) * d := mul_pos (sub_pos.mpr he) hd
  nlinarith only [hslack, hmain, hendpoint]

 

theorem fieldSigmaClosed0_le_recentered_open
    {Ω : Type} [MeasurableSpace Ω] (h : Ω → LQGMetric.DistC)
    (c : Ω → ℝ) (K : Set ℂ) (V : TopologicalSpace.Opens ℂ)
    (hK : IsCompact K) (hKV : K ⊆ (V : Set ℂ)) :
    LQGMetric.Blueprint.fieldSigmaClosed0 h K ≤
      LQGMetric.Blueprint.fieldSigma
        (fun ω => LQGMetric.addConst (h ω) (c ω)) V := by
  obtain ⟨ε, hε, hthick⟩ :=
    hK.exists_thickening_subset_open V.isOpen hKV
  let g : Ω → LQGMetric.DistC := fun ω => LQGMetric.addConst (h ω) (c ω)
  calc
    LQGMetric.Blueprint.fieldSigmaClosed0 h K =
        LQGMetric.Blueprint.fieldSigmaClosed0 g K := by
          exact (LQGMetric.CONF.fieldSigmaClosed0_addConst h c K).symm
    _ ≤ LQGMetric.Blueprint.fieldSigma0On g (V : Set ℂ) := by
      unfold LQGMetric.Blueprint.fieldSigmaClosed0
      exact (iInf_le _ ε).trans ((iInf_le _ hε).trans
        (LQGMetric.CONF.conf36_fieldSigma0On_mono g hthick))
    _ ≤ LQGMetric.Blueprint.fieldSigma g V :=
      LQGMetric.CONF.fieldSigma0On_le_fieldSigma g V.isOpen

 

theorem offcentre_fieldSigmaClosed0_le_centered_open
    {Ω : Type} [MeasurableSpace Ω] (h : Ω → LQGMetric.DistC)
    (c : Ω → ℝ) {z w : ℂ} {r : ℝ} (hr : 0 < r)
    (hw : dist w z ≤ r / 50) :
    LQGMetric.Blueprint.fieldSigmaClosed0 h
      {x : ℂ | r ≤ dist x w ∧ dist x w ≤ 4 * r} ≤
    LQGMetric.Blueprint.fieldSigma
      (fun ω => LQGMetric.addConst
        (LQGMetric.affineComp 1 z (h ω)) (c ω))
      (LQGMetric.Blueprint.annulus 0 ((0.19 : ℝ) * (5 * r))
        ((0.81 : ℝ) * (5 * r))) := by
  let K : Set ℂ := {x : ℂ | r ≤ dist x w ∧ dist x w ≤ 4 * r}
  let V := LQGMetric.Blueprint.annulus z ((0.19 : ℝ) * (5 * r))
    ((0.81 : ℝ) * (5 * r))
  let W := LQGMetric.Blueprint.annulus 0 ((0.19 : ℝ) * (5 * r))
    ((0.81 : ℝ) * (5 * r))
  have hKcompact : IsCompact K := by
    have hinner : IsClosed {x : ℂ | r ≤ dist x w} :=
      isClosed_le continuous_const (continuous_id.dist continuous_const)
    have houter : IsCompact {x : ℂ | dist x w ≤ 4 * r} := by
      simpa only [Metric.closedBall, dist_comm] using
        (isCompact_closedBall w (4 * r))
    exact houter.inter_left hinner
  have hKV : K ⊆ (V : Set ℂ) :=
    offcentre_closed_annulus_subset_open hr hw
  have hUV : ∀ y : ℂ, y ∈ W ↔ (1 : ℝ) • y + z ∈ V := by
    intro y
    change (0.19 : ℝ) * (5 * r) < ‖y - 0‖ ∧
      ‖y - 0‖ < (0.81 : ℝ) * (5 * r) ↔
      (0.19 : ℝ) * (5 * r) < ‖(1 : ℝ) • y + z - z‖ ∧
      ‖(1 : ℝ) • y + z - z‖ < (0.81 : ℝ) * (5 * r)
    simp only [one_smul, add_sub_cancel_right, sub_zero]
  have hbase := fieldSigmaClosed0_le_recentered_open h c K V hKcompact hKV
  have htrans := LQGMetric.GM.fieldSigma_le_affineComp one_pos hUV
    (fun ω => LQGMetric.addConst (h ω) (c ω))
  simpa only [LQGMetric.GM.affineComp_addConst one_pos] using hbase.trans htrans

 

theorem closed_endpoint_pair_distance_lower
    {z w x y : ℂ} {s κ b : ℝ}
    (hx : x ∈ Metric.closedBall z s)
    (hy : y ∈ Metric.closedBall w s)
    (hzw : κ * b ≤ dist z w) :
    κ * b - 2 * s ≤ dist x y := by
  have hzx : dist z x ≤ s := by
    simpa only [dist_comm] using (Metric.mem_closedBall.mp hx)
  have hyw : dist y w ≤ s := Metric.mem_closedBall.mp hy
  have htri₁ := dist_triangle z x y
  have htri₂ := dist_triangle z y w
  linarith only [hzw, hzx, hyw, htri₁, htri₂]

 

theorem closed_endpoint_sphere_distance_lower
    {z x y : ℂ} {s κ b : ℝ}
    (hx : x ∈ Metric.closedBall z s)
    (hy : y ∈ Metric.sphere (0 : ℂ) b)
    (hz : κ * b ≤ Metric.infDist z (Metric.sphere (0 : ℂ) b)) :
    κ * b - s ≤ dist x y := by
  have hzy : κ * b ≤ dist z y :=
    hz.trans (Metric.infDist_le_dist_of_mem hy)
  have hzx : dist z x ≤ s := by
    simpa only [dist_comm] using (Metric.mem_closedBall.mp hx)
  have htri := dist_triangle z x y
  linarith only [hzy, hzx, htri]

 
theorem euclidSetDist_closed_endpoint_balls_lower
    {z w : ℂ} {s κ b : ℝ} (hzw : κ * b ≤ dist z w) :
    ENNReal.ofReal (κ * b - 2 * s) ≤
      euclidSetDist (Metric.closedBall z s) (Metric.closedBall w s) := by
  unfold euclidSetDist
  refine le_iInf fun x => le_iInf fun hx => le_iInf fun y => le_iInf fun hy => ?_
  exact ENNReal.ofReal_le_ofReal (closed_endpoint_pair_distance_lower hx hy hzw)

 
theorem euclidSetDist_closed_endpoint_sphere_lower
    {z : ℂ} {s κ b : ℝ}
    (hz : κ * b ≤ Metric.infDist z (Metric.sphere (0 : ℂ) b)) :
    ENNReal.ofReal (κ * b - s) ≤
      euclidSetDist (Metric.closedBall z s) (Metric.sphere (0 : ℂ) b) := by
  unfold euclidSetDist
  refine le_iInf fun x => le_iInf fun hx => le_iInf fun y => le_iInf fun hy => ?_
  exact ENNReal.ofReal_le_ofReal (closed_endpoint_sphere_distance_lower hx hy hz)

 

theorem sizeWindow_of_circle_increment
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (ε b r : Set.Ioi (0 : ℝ)) (hε1 : (ε : ℝ) < 1)
    (hlow : (ε : ℝ) ^ 2 * (b : ℝ) ≤ (r : ℝ))
    (hup : (r : ℝ) ≤ (ε : ℝ) * (b : ℝ))
    (hbr hrz : ℝ)
    (hinc : |hrz - hbr| ≤ 3 * Real.log (((r : ℝ) / (b : ℝ))⁻¹)) :
    SizeWindow ξ Q ε b r hbr hrz := by
  have ht : 0 < (r : ℝ) / (b : ℝ) := div_pos r.property b.property
  have htlow : (ε : ℝ) ^ 2 ≤ (r : ℝ) / (b : ℝ) :=
    (le_div_iff₀ b.property).mpr hlow
  have htup : (r : ℝ) / (b : ℝ) ≤ (ε : ℝ) :=
    (div_le_iff₀ b.property).mpr hup
  obtain ⟨hSlo, hShi⟩ := normalized_size_window ε.property hε1 ht htlow htup
    ξ.property hQ hinc
  let A : ℝ := (b : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hbr)
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact le_of_lt (mul_pos (Real.rpow_pos_of_pos b.property _)
      (Real.exp_pos _))
  have hfac : (r : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hrz) =
      ((r : ℝ) / (b : ℝ)) ^ ((ξ : ℝ) * Q) *
        Real.exp ((ξ : ℝ) * (hrz - hbr)) * A := by
    have hb0 : (b : ℝ) ≠ 0 :=
      (show (0 : ℝ) < (b : ℝ) from b.property).ne'
    have hrEq : (r : ℝ) = ((r : ℝ) / (b : ℝ)) * (b : ℝ) := by
      field_simp [hb0]
    have hexp : Real.exp ((ξ : ℝ) * hrz) =
        Real.exp ((ξ : ℝ) * (hrz - hbr)) * Real.exp ((ξ : ℝ) * hbr) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      (r : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hrz) =
          (((r : ℝ) / (b : ℝ)) * (b : ℝ)) ^ ((ξ : ℝ) * Q) *
            Real.exp ((ξ : ℝ) * hrz) := by rw [← hrEq]
      _ = (((r : ℝ) / (b : ℝ)) ^ ((ξ : ℝ) * Q) *
          (b : ℝ) ^ ((ξ : ℝ) * Q)) *
          (Real.exp ((ξ : ℝ) * (hrz - hbr)) * Real.exp ((ξ : ℝ) * hbr)) := by
            rw [Real.mul_rpow ht.le b.property.le, hexp]
      _ = _ := by dsimp only [A]; ring
  unfold SizeWindow
  constructor
  · calc
      (ε : ℝ) ^ (2 * (ξ : ℝ) * (Q + 3)) * (b : ℝ) ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * hbr) =
          (ε : ℝ) ^ (2 * (ξ : ℝ) * (Q + 3)) * A := by ring
      _ ≤ ((r : ℝ) / (b : ℝ)) ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * (hrz - hbr)) * A :=
            mul_le_mul_of_nonneg_right hSlo hA
      _ = _ := hfac.symm
  · calc
      (r : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hrz) =
          ((r : ℝ) / (b : ℝ)) ^ ((ξ : ℝ) * Q) *
            Real.exp ((ξ : ℝ) * (hrz - hbr)) * A := hfac
      _ ≤ (ε : ℝ) ^ ((ξ : ℝ) * min (Q - 3) (2 * (Q - 3))) * A :=
            mul_le_mul_of_nonneg_right hShi hA
      _ = _ := by ring

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.CircleRange
