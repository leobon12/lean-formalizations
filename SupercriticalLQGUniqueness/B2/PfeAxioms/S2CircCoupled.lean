import SupercriticalLQGUniqueness.B2.PfeAxioms.S2CircFinite
import SupercriticalLQGUniqueness.B2.DG20Lim.NestedGoodCostConv
import SupercriticalLQGUniqueness.B2.DG20Lim.RationalUpper
import SupercriticalLQGUniqueness.B2.DG20Lim.DfromR

 



















set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

open SupercriticalLQGUniqueness.B2.DG20Lim

 

theorem outer_closedDisk_subset_ball {A : RatAnnulus} {y : ℂ} (hy : A.inner.Surrounds y) :
    A.outer.closedDisk ⊆ ball y (2 * (A.outer.radius : ℝ)) := by
  have hyo : y ∈ A.outer.openDisk :=
    A.nested.2 (ball_subset_closedBall hy.2)
  intro p hp
  rw [RatCircle.closedDisk, mem_closedBall] at hp
  rw [RatCircle.openDisk, mem_ball] at hyo
  rw [mem_ball]
  calc dist p y ≤ dist p A.outer.center + dist A.outer.center y := dist_triangle _ _ _
    _ < (A.outer.radius : ℝ) + A.outer.radius := by
        rw [dist_comm A.outer.center y]; linarith
    _ = 2 * (A.outer.radius : ℝ) := by ring

theorem toSet_subset_closedDisk (O : RatCircle) : O.toSet ⊆ O.closedDisk :=
  sphere_subset_closedBall

theorem toSet_subset_openDisk_compl (O : RatCircle) : O.toSet ⊆ O.openDiskᶜ := by
  intro p hp hp'
  rw [RatCircle.toSet, mem_sphere] at hp
  rw [RatCircle.openDisk, mem_ball] at hp'
  linarith

 
theorem toSet_subset_outer_compl_of_far {A : RatAnnulus} {y : ℂ} (hy : A.inner.Surrounds y)
    (X : RatCircle) (hfar : ∀ p ∈ X.toSet, 2 * (A.outer.radius : ℝ) ≤ dist p y) :
    X.toSet ⊆ A.outer.openDiskᶜ := by
  intro p hp hpo
  have h1 := outer_closedDisk_subset_ball hy (ball_subset_closedBall hpo)
  rw [mem_ball] at h1
  linarith [hfar p hp]

 
theorem exists_pos_dist_toSet (X : RatCircle) {y : ℂ} (hy : y ∉ X.toSet) :
    ∃ δ > 0, ∀ p ∈ X.toSet, δ ≤ dist p y := by
  have hc : IsCompact X.toSet := isCompact_sphere _ _
  have hne : X.toSet.Nonempty := NormedSpace.sphere_nonempty.2 (by exact_mod_cast X.radius_nonneg)
  obtain ⟨p₀, hp₀, hmin⟩ := hc.exists_isMinOn hne (continuous_id.dist continuous_const).continuousOn
  refine ⟨dist p₀ y, dist_pos.2 fun h => hy (h ▸ hp₀), fun p hp => hmin hp⟩

 
theorem eventually_toSet_subset_outer_compl {B : ℕ → RatAnnulus} {y : ℂ}
    (hB : ∀ n, (B n).inner.Surrounds y)
    (hr : Tendsto (fun n => ((B n).outer.radius : ℝ)) atTop (𝓝 0))
    (X : RatCircle) (hy : y ∉ X.toSet) :
    ∀ᶠ n in atTop, X.toSet ⊆ (B n).outer.openDiskᶜ := by
  obtain ⟨δ, hδ, hfar⟩ := exists_pos_dist_toSet X hy
  filter_upwards [hr.eventually (gt_mem_nhds (half_pos hδ))] with n hn
  exact toSet_subset_outer_compl_of_far (hB n) X fun p hp => by linarith [hfar p hp]

 
theorem exists_mem_sphere_of_isPreconnected {S : Set ℂ} (hS : IsPreconnected S) {c : ℂ} {r : ℝ}
    {y y' : ℂ} (hy : y ∈ S) (hyb : y ∈ ball c r) (hy' : y' ∈ S) (hy'b : y' ∉ ball c r) :
    ∃ p ∈ S, p ∈ sphere c r := by
  by_contra hnot
  have hnot' : ∀ p ∈ S, p ∉ sphere c r := fun p hp hps => hnot ⟨p, hp, hps⟩
  have hsub : S ⊆ ball c r ∪ (closedBall c r)ᶜ := by
    intro p hp
    by_cases h : dist p c < r
    · exact Or.inl h
    · refine Or.inr fun hpc => hnot' p hp ?_
      rw [mem_closedBall] at hpc
      rw [mem_sphere]
      linarith [not_lt.1 h]
  have hy'c : y' ∈ (closedBall c r)ᶜ := by
    intro hcl
    refine hnot' y' hy' ?_
    rw [mem_closedBall] at hcl
    rw [mem_ball, not_lt] at hy'b
    rw [mem_sphere]
    linarith
  obtain ⟨p, -, hp1, hp2⟩ := hS _ _ isOpen_ball isClosed_closedBall.isOpen_compl hsub
    ⟨y, hy, hyb⟩ ⟨y', hy', hy'c⟩
  exact hp2 (ball_subset_closedBall hp1)

 
theorem crossesAnn_of_small {O : RatCircle} {y : ℂ} (hy : y ∈ O.toSet) (hO : O.radius ≠ 0)
    {A : RatAnnulus} (hAy : A.inner.Surrounds y) (hsmall : (A.outer.radius : ℝ) < O.radius) :
    CrossesAnn O A := by
  have hρ : (0 : ℝ) < O.radius := by
    have : (0 : ℚ) < O.radius := lt_of_le_of_ne O.radius_nonneg (Ne.symm hO)
    exact_mod_cast this
  have hpc : IsPreconnected O.toSet := by
    unfold RatCircle.toSet
    exact (isPathConnected_sphere (by simp) O.center hρ.le).isConnected.isPreconnected
  
  set y' : ℂ := 2 * O.center - y with hy'
  have hy'O : y' ∈ O.toSet := by
    rw [RatCircle.toSet, mem_sphere] at hy ⊢
    rw [hy', dist_eq_norm, show 2 * O.center - y - O.center = -(y - O.center) by ring, norm_neg,
      ← dist_eq_norm, hy]
  have hdy' : dist y' y = 2 * (O.radius : ℝ) := by
    rw [RatCircle.toSet, mem_sphere] at hy
    rw [hy', dist_eq_norm, show 2 * O.center - y - y = -(2 : ℂ) * (y - O.center) by ring,
      norm_mul, norm_neg, ← dist_eq_norm, hy]
    simp
  have hy'out : y' ∉ A.outer.openDisk := by
    intro h
    have h1 := outer_closedDisk_subset_ball hAy (ball_subset_closedBall h)
    rw [mem_ball] at h1
    linarith
  have hyin : y ∈ A.inner.openDisk := hAy.2
  have hyout : y ∈ A.outer.openDisk := A.nested.2 (ball_subset_closedBall hyin)
  have hy'in : y' ∉ A.inner.openDisk := fun h =>
    hy'out (A.nested.2 (ball_subset_closedBall h))
  have hinr : (0 : ℝ) < A.inner.radius := by exact_mod_cast A.inner_pos
  have houtr : (0 : ℝ) < A.outer.radius := by exact_mod_cast A.nested.1
  refine ⟨?_, ?_⟩
  · obtain ⟨p, hpO, hpS⟩ := exists_mem_sphere_of_isPreconnected hpc hy hyin hy'O hy'in
    exact ⟨p, hpO, hpS⟩
  · obtain ⟨p, hpO, hpS⟩ := exists_mem_sphere_of_isPreconnected hpc hy hyout hy'O hy'out
    exact ⟨p, hpO, hpS⟩

 

 
theorem RData.across_le_inner_add (R : RData)
    (hcross : ∀ (A : RatAnnulus) (O₁ O₁' Q : RatCircle),
      A.OppositeSides O₁ O₁' → CrossesAnn Q A → R.across O₁ Q ≤ R.across O₁ O₁' + R.around A)
    (O : RatCircle) {y : ℂ} (hy : y ∈ O.toSet) (A : RatAnnulus) (hAy : A.inner.Surrounds y)
    (hcr : O.radius ≠ 0 → CrossesAnn O A) (X : RatCircle) (hX : X.toSet ⊆ A.outer.openDiskᶜ) :
    R.across O X ≤ R.across A.inner X +
      ((if O.radius = 0 then R.across O A.outer else 0) + R.around A) := by
  have hXin : A.OppositeSides X A.inner :=
    Or.inr ⟨toSet_subset_closedDisk A.inner, hX⟩
  by_cases h0 : O.radius = 0
  · simp only [h0, if_true]
    have hOy : O.toSet = {O.center} := RatCircle.toSet_eq_singleton_of_radius_zero O h0
    have hOpp : A.OppositeSides O A.outer := by
      refine Or.inl ⟨?_, toSet_subset_openDisk_compl A.outer⟩
      rw [hOy]
      intro p hp
      rw [mem_singleton_iff] at hp
      rw [hOy, mem_singleton_iff] at hy
      rw [hp, ← hy]
      exact ball_subset_closedBall hAy.2
    have h := R.around_upper A O A.outer X A.inner hOpp hXin
    calc R.across O X ≤ R.across O A.outer + R.across X A.inner + R.around A := h
      _ = R.across A.inner X + (R.across O A.outer + R.around A) := by
          rw [R.across_symm X A.inner]; ring
  · simp only [h0, if_false, zero_add]
    have h := hcross A X A.inner O hXin (hcr h0)
    rw [R.across_symm X O, R.across_symm X A.inner] at h
    exact h

 

 
theorem RData.across_le_DfromR_of_crossing (R : RData) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hcross : ∀ (A : RatAnnulus) (O₁ O₁' Q : RatCircle),
      A.OppositeSides O₁ O₁' → CrossesAnn Q A → R.across O₁ Q ≤ R.across O₁ O₁' + R.around A)
    (hinter : ∀ O Q : RatCircle, (O.toSet ∩ Q.toSet).Nonempty → R.across O Q = 0)
    (hGood : ∀ y : ℂ, ∃ B : ℕ → RatAnnulus,
      (∀ n, (B n).inner.Surrounds y ∧ R.around (B n) ≤ C * R.across (B n).inner (B n).outer) ∧
      (∀ n, (B n).inner.SurroundsCircle (B (n + 1)).outer) ∧
      Tendsto (fun n => (((B n).outer.radius : ℝ))) atTop (𝓝 0))
    (hvanish : ∀ Z : RatCircle, Z.radius = 0 → ∀ O : ℕ → RatCircle,
      (∀ᶠ n in atTop, (O n).Surrounds Z.center) →
      Tendsto (fun n => ((O n).radius : ℝ)) atTop (𝓝 0) →
      Tendsto (fun n => R.across Z (O n)) atTop (𝓝 0))
    (O Q : RatCircle) {z w : ℂ} (hz : z ∈ O.toSet) (hw : w ∈ Q.toSet) :
    R.across O Q ≤ R.DfromR z w := by
  by_cases hzQ : z ∈ Q.toSet
  · rw [hinter O Q ⟨z, hz, hzQ⟩]; exact zero_le
  by_cases hwO : w ∈ O.toSet
  · rw [hinter O Q ⟨w, hwO, hw⟩]; exact zero_le
  have hzw : z ≠ w := fun h => hzQ (h ▸ hw)
  by_cases hfin : R.DfromR z w = ∞
  · rw [hfin]; exact le_top
  obtain ⟨Bz, hBz, hBzn, hBzr⟩ := hGood z
  obtain ⟨Bw, hBw, hBwn, hBwr⟩ := hGood w
  have hcz := R.nested_good_annulus_costs_tendsto_zero Bz C hC z w hzw hfin hBz hBzn hBzr
  have hfin' : R.DfromR w z ≠ ∞ := by rw [R.DfromR_symm]; exact hfin
  have hcw := R.nested_good_annulus_costs_tendsto_zero Bw C hC w z hzw.symm hfin' hBw hBwn hBwr
  
  set εz : ℕ → ℝ≥0∞ := fun n =>
    (if O.radius = 0 then R.across O (Bz n).outer else 0) + R.around (Bz n) with hεz
  set εw : ℕ → ℝ≥0∞ := fun n =>
    (if Q.radius = 0 then R.across Q (Bw n).outer else 0) + R.around (Bw n) with hεw
  have hpt : ∀ (O' : RatCircle) {y : ℂ}, y ∈ O'.toSet → ∀ (B : ℕ → RatAnnulus),
      (∀ n, (B n).inner.Surrounds y) →
      Tendsto (fun n => (((B n).outer.radius : ℝ))) atTop (𝓝 0) →
      Tendsto (fun n => R.around (B n)) atTop (𝓝 0) →
      Tendsto (fun n => (if O'.radius = 0 then R.across O' (B n).outer else 0) + R.around (B n))
        atTop (𝓝 0) := by
    intro O' y hy B hB hBr hBa
    have h1 : Tendsto (fun n => if O'.radius = 0 then R.across O' (B n).outer else 0) atTop
        (𝓝 0) := by
      by_cases h0 : O'.radius = 0
      · simp only [h0, if_true]
        have hc : O'.center = y := by
          have := RatCircle.toSet_eq_singleton_of_radius_zero O' h0
          rw [this, mem_singleton_iff] at hy
          exact hy.symm
        refine hvanish O' h0 (fun n => (B n).outer) (Eventually.of_forall fun n => ?_) hBr
        refine ⟨(B n).nested.1, ?_⟩
        rw [hc]
        exact (B n).nested.2 (ball_subset_closedBall (hB n).2)
      · simp only [h0, if_false]
        exact tendsto_const_nhds
    simpa only [add_zero] using h1.add hBa
  have hεz0 : Tendsto εz atTop (𝓝 0) :=
    hpt O hz Bz (fun n => (hBz n).1) hBzr hcz.2
  have hεw0 : Tendsto εw atTop (𝓝 0) :=
    hpt Q hw Bw (fun n => (hBw n).1) hBwr hcw.2
  
  have hOpos : O.radius ≠ 0 → ∀ᶠ n in atTop, CrossesAnn O (Bz n) := by
    intro h0
    have hρ : (0 : ℝ) < O.radius := by
      have : (0 : ℚ) < O.radius := lt_of_le_of_ne O.radius_nonneg (Ne.symm h0)
      exact_mod_cast this
    filter_upwards [hBzr.eventually (gt_mem_nhds hρ)] with n hn
    exact crossesAnn_of_small hz h0 (hBz n).1 hn
  have hQpos : Q.radius ≠ 0 → ∀ᶠ n in atTop, CrossesAnn Q (Bw n) := by
    intro h0
    have hρ : (0 : ℝ) < Q.radius := by
      have : (0 : ℚ) < Q.radius := lt_of_le_of_ne Q.radius_nonneg (Ne.symm h0)
      exact_mod_cast this
    filter_upwards [hBwr.eventually (gt_mem_nhds hρ)] with n hn
    exact crossesAnn_of_small hw h0 (hBw n).1 hn
  have hEO : ∀ᶠ n in atTop, O.radius ≠ 0 → CrossesAnn O (Bz n) := by
    by_cases h0 : O.radius = 0
    · exact Eventually.of_forall fun _ h => absurd h0 h
    · filter_upwards [hOpos h0] with n hn using fun _ => hn
  have hEQ : ∀ᶠ n in atTop, Q.radius ≠ 0 → CrossesAnn Q (Bw n) := by
    by_cases h0 : Q.radius = 0
    · exact Eventually.of_forall fun _ h => absurd h0 h
    · filter_upwards [hQpos h0] with n hn using fun _ => hn
  have hE2 := eventually_toSet_subset_outer_compl (fun n => (hBz n).1) hBzr Q hzQ
  
  have hd : (0 : ℝ) < dist z w := dist_pos.2 hzw
  have hsmallz := hBzr.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < dist z w / 4))
  have hsmallw := hBwr.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < dist z w / 4))
  have hE4 : ∀ᶠ n in atTop, (Bz n).inner.toSet ⊆ (Bw n).outer.openDiskᶜ := by
    filter_upwards [hsmallz, hsmallw] with n hn hn'
    refine toSet_subset_outer_compl_of_far (hBw n).1 _ fun p hp => ?_
    have hp' : p ∈ ball z (2 * ((Bz n).outer.radius : ℝ)) :=
      outer_closedDisk_subset_ball (hBz n).1
        ((Bz n).nested.2.trans ball_subset_closedBall (toSet_subset_closedDisk _ hp))
    rw [mem_ball] at hp'
    have := dist_triangle z p w
    rw [dist_comm z p] at this
    linarith
  have hE5 : ∀ᶠ n in atTop, Disjoint (Bz n).inner.closedDisk (Bw n).inner.closedDisk := by
    filter_upwards [hsmallz, hsmallw] with n hn hn'
    rw [Set.disjoint_left]
    intro p hpz hpw
    have h1 : p ∈ ball z (2 * ((Bz n).outer.radius : ℝ)) :=
      outer_closedDisk_subset_ball (hBz n).1 ((Bz n).nested.2.trans ball_subset_closedBall hpz)
    have h2 : p ∈ ball w (2 * ((Bw n).outer.radius : ℝ)) :=
      outer_closedDisk_subset_ball (hBw n).1 ((Bw n).nested.2.trans ball_subset_closedBall hpw)
    rw [mem_ball] at h1 h2
    have := dist_triangle z p w
    rw [dist_comm z p] at this
    linarith
  
  have hev : ∀ᶠ n in atTop, R.across O Q ≤ R.DfromR z w + (εz n + εw n) := by
    filter_upwards [hEO, hEQ, hE2, hE4, hE5] with n hn1 hn2 hn3 hn4 hn5
    have h1 := RData.across_le_inner_add R hcross O hz (Bz n) (hBz n).1 hn1 Q hn3
    have h2 := RData.across_le_inner_add R hcross Q hw (Bw n) (hBw n).1 hn2 (Bz n).inner hn4
    have h3 := DG20Lim.RData.across_le_DfromR R hzw (Bz n).inner (Bw n).inner (hBz n).1 (hBw n).1 hn5
    rw [R.across_symm Q (Bz n).inner, R.across_symm (Bw n).inner (Bz n).inner] at h2
    calc R.across O Q ≤ R.across (Bz n).inner Q + εz n := h1
      _ ≤ (R.across (Bz n).inner (Bw n).inner + εw n) + εz n := add_le_add h2 le_rfl
      _ ≤ (R.DfromR z w + εw n) + εz n := add_le_add (add_le_add h3 le_rfl) le_rfl
      _ = R.DfromR z w + (εz n + εw n) := by ring
  have hlim : Tendsto (fun n => R.DfromR z w + (εz n + εw n)) atTop (𝓝 (R.DfromR z w)) := by
    have := (tendsto_const_nhds (x := R.DfromR z w)).add (hεz0.add hεw0)
    simpa only [add_zero] using this
  exact ge_of_tendsto hlim hev

end SupercriticalLQGUniqueness.B2.PfeAxioms
