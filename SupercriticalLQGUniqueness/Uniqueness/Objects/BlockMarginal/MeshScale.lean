import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.Family
import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Family




 











set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Pointwise

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal

 
def MeshProps (U : Set ℂ) (r a ρ₀ : ℝ) (X : Finset ℂ) : Prop :=
  0 < ρ₀ ∧ ρ₀ ≤ a / 4 ∧ X.Nonempty ∧
  (∀ x ∈ X, closedBall x (2 * ρ₀) ⊆ U) ∧
  (∀ x ∈ X, ∀ y ∈ X, Relation.ReflTransGen
    (fun u v : ℂ => u ∈ X ∧ v ∈ X ∧ ρ₀ < dist u v ∧ dist u v < 2 * ρ₀) x y) ∧
  LQGMetric.Disconnects (⋃ x ∈ X, ball x ρ₀) (closedBall 0 (1.5 * r)) (ball 0 (2.5 * r))ᶜ ∧
  (∀ y ∈ closure U, ∃ x ∈ X, dist y x ≤ a / 2)

theorem spine_disconnects_unit (P : Objects.Tube.TubeParams) (hP : P.Good) :
    LQGMetric.Disconnects (range (P.spine 1))
      (closedBall 0 (1.5 * 1)) (ball 0 (2.5 * 1))ᶜ := by
  have hA : 100 * (P.sp * P.ρ / 100) ≤ P.sp * P.ρ := by linarith
  have hApos : 0 < P.sp * P.ρ / 100 := by have := hP.sp_pos; have := hP.ρ_pos; positivity
  have hG2 := (Objects.Tube.TubeParams.nbhd_and_thickening_subset_annulus (P := P) (r := 1) (Asup := P.sp * P.ρ / 100)
    hP one_pos hA).1
  have hsp : ∀ t, P.spine 1 t ∈ P.nbhd 1 (P.sp * P.ρ / 100) := by
    intro t
    exact self_subset_thickening (by positivity) _
      (Objects.Tube.TubeParams.spine_mem_tube hP one_pos t)
  exact Objects.TubeLoops.loop_disconnects _ (Objects.Tube.TubeParams.spine_closed hP)
    (Objects.Tube.TubeParams.spine_ne_zero hP one_pos)
    (by rw [Objects.Tube.TubeParams.spine_loopDeg hP one_pos]; norm_num)
    (fun t => by have := (hG2 (hsp t)).1; norm_num at this ⊢; exact this)
    (fun t => by have := (hG2 (hsp t)).2; norm_num at this ⊢; exact this)

 
theorem exists_unit_mesh (P : Objects.Tube.TubeParams) (hP : P.Good) {a : ℝ} (ha : 0 < a) :
    ∃ (ρ₀ : ℝ) (X : Finset ℂ), MeshProps (P.tube 1) 1 a ρ₀ X := by
  have hG1 := Objects.Tube.TubeParams.tube_open_bounded_pathConnected (P := P) (r := 1) hP one_pos
  have hBounded : Bornology.IsBounded (P.tube 1) :=
    (isBounded_ball (x := (0 : ℂ)) (r := 3 * 1)).subset hG1.2.1
  have hA : 100 * (P.sp * P.ρ / 100) ≤ P.sp * P.ρ := by linarith
  have hG2 := (Objects.Tube.TubeParams.nbhd_and_thickening_subset_annulus (P := P) (r := 1) (Asup := P.sp * P.ρ / 100)
    hP one_pos hA).1
  have hApos : 0 < P.sp * P.ρ / 100 := by have := hP.sp_pos; have := hP.ρ_pos; positivity
  have hAnn : P.tube 1 ⊆ LQGMetric.Blueprint.annulus 0 0 (3 * 1) := by
    intro x hx
    have hxV : x ∈ P.nbhd 1 (P.sp * P.ρ / 100) := self_subset_thickening (by positivity) _ hx
    have hb := hG2 hxV
    change 3 / 2 * 1 < ‖x‖ ∧ ‖x‖ < 5 / 2 * 1 at hb
    change (0 : ℝ) < ‖x - 0‖ ∧ ‖x - 0‖ < 3 * 1
    simp only [sub_zero]
    constructor <;> linarith
  obtain ⟨ρ₀, X, h1, h2, h3, h4, h5, h6, h7⟩ := Objects.TubeMesh.finite_connected_mesh hG1.1 hBounded
    hG1.2.2 hAnn (P.spine 1) (Objects.Tube.TubeParams.range_spine_subset_tube hP one_pos)
    (spine_disconnects_unit P hP) ha
  exact ⟨ρ₀, X, h1, h2, h3, h4, h5, h6, h7⟩

theorem smul_eq_mul_complex (r : ℝ) (x : ℂ) : r • x = (r : ℂ) * x := by
  rw [Complex.real_smul]

 
theorem MeshProps.scale {P : Objects.Tube.TubeParams} {r a ρ₀ : ℝ} {X : Finset ℂ} (hr : 0 < r)
    (h : MeshProps (P.tube 1) 1 a ρ₀ X) :
    MeshProps (P.tube r) r (a * r) (r * ρ₀) (X.image (fun x => (r : ℂ) * x)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hdist : ∀ u v : ℂ, dist ((r : ℂ) * u) ((r : ℂ) * v) = r * dist u v := by
    intro u v
    rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr]
  have hinv : ∀ y : ℂ, (r : ℂ) * ((r⁻¹ : ℝ) • y) = y := by
    intro y
    rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne',
      Complex.ofReal_one, one_mul]
  refine ⟨by positivity, by nlinarith, h3.image _, ?_, ?_, ?_, ?_⟩
  · intro x' hx' y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hx'
    rw [Objects.Tube.TubeParams.mem_tube_iff hr]
    apply h4 x hx
    rw [mem_closedBall] at hy ⊢
    have e : dist y ((r : ℂ) * x) = r * dist ((r⁻¹ : ℝ) • y) x := by
      rw [← hdist, hinv]
    have : dist ((r⁻¹ : ℝ) • y) x = r⁻¹ * dist y ((r : ℂ) * x) := by
      rw [e, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
    rw [this]
    rw [inv_mul_le_iff₀ hr]
    linarith
  · intro x' hx' y' hy'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hx'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hy'
    refine Relation.ReflTransGen.lift (fun u : ℂ => (r : ℂ) * u) ?_ x y (h5 x hx y hy)
    rintro u v ⟨hu, hv, hl, hr'⟩
    refine ⟨Finset.mem_image_of_mem _ hu, Finset.mem_image_of_mem _ hv, ?_, ?_⟩
    · rw [hdist]; exact mul_lt_mul_of_pos_left hl hr
    · rw [hdist]; nlinarith
  · intro x y γ hx hy
    have hx' : (r⁻¹ : ℝ) • x ∈ closedBall (0 : ℂ) (1.5 * 1) := by
      rw [mem_closedBall, dist_zero_right] at hx ⊢
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr), inv_mul_le_iff₀ hr]
      linarith
    have hy' : (r⁻¹ : ℝ) • y ∈ (ball (0 : ℂ) (2.5 * 1))ᶜ := by
      rw [mem_compl_iff, mem_ball, dist_zero_right, not_lt] at hy ⊢
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr), le_inv_mul_iff₀ hr]
      linarith
    obtain ⟨p, ⟨t, rfl⟩, hp⟩ :=
      h6 _ _ (γ.map (continuous_const_smul ((r⁻¹ : ℝ)) : Continuous fun z : ℂ => (r⁻¹ : ℝ) • z))
        hx' hy'
    refine ⟨γ t, ⟨t, rfl⟩, ?_⟩
    simp only [mem_iUnion, Finset.mem_image] at hp ⊢
    obtain ⟨x0, hx0, hball⟩ := hp
    refine ⟨(r : ℂ) * x0, ⟨x0, hx0, rfl⟩, ?_⟩
    rw [mem_ball] at hball ⊢
    rw [Path.map_coe, Function.comp_apply] at hball
    have : dist (γ t) ((r : ℂ) * x0) = r * dist ((r⁻¹ : ℝ) • γ t) x0 := by
      rw [← hdist, hinv]
    rw [this]
    exact mul_lt_mul_of_pos_left hball hr
  · intro y hy
    have hy1 : (r⁻¹ : ℝ) • y ∈ closure (P.tube 1) := by
      have hc : Continuous fun z : ℂ => (r⁻¹ : ℝ) • z := continuous_const_smul _
      have himg := image_closure_subset_closure_image hc ⟨y, hy, rfl⟩
      rwa [show (fun z : ℂ => (r⁻¹ : ℝ) • z) '' P.tube r = P.tube 1 by
        rw [← Objects.Tube.TubeParams.inv_smul_tube (P := P) hr]; rfl] at himg
    obtain ⟨x, hx, hd⟩ := h7 _ hy1
    refine ⟨(r : ℂ) * x, Finset.mem_image_of_mem _ hx, ?_⟩
    have : dist y ((r : ℂ) * x) = r * dist ((r⁻¹ : ℝ) • y) x := by
      rw [← hdist, hinv]
    rw [this]
    nlinarith

 
theorem dataMatch_of_mesh (C : Objects.CorrectedEvent.Constants) (P : Objects.Tube.TubeParams)
    (S : Objects.TubeMesh.TubeSelection C P) (hSupNar : C.A_sup < C.A_nar) (ρ₀ : ℝ) (X : Finset ℂ)
    (hM : MeshProps (P.tube C.r) C.r (C.A_set * C.r) ρ₀ X) :
    Objects.CorrectedEvent.DataMatch C (Objects.TubeBridge.tubeDataOf C P S.good (S.small hSupNar).1 ρ₀ X) := by
  let hP : P.Good := S.good
  let hSmall : 100 * C.A_sup ≤ P.sp * P.ρ := (S.small hSupNar).1
  obtain ⟨hρ₀, hρ₀le, hX, hM1, hM2, hM3, hM4⟩ := hM
  let T := Objects.TubeBridge.tubeDataOf C P hP hSmall ρ₀ X
  have hTube : Objects.CorrectedEvent.tubeSet T = P.tube C.r :=
    Objects.TubeBridge.tubeDataOf_tubeSet_eq C P hP hSmall ρ₀ X S.widthEq
  have hM1' : ∀ x ∈ X, closedBall x (2 * ρ₀) ⊆ Objects.CorrectedEvent.tubeSet T := by
    intro x hx
    rw [hTube]
    exact hM1 x hx
  have hM4' : ∀ y ∈ closure (Objects.CorrectedEvent.tubeSet T),
      ∃ x ∈ X, dist y x ≤ C.A_set * C.r / 2 := by
    intro y hy
    rw [hTube] at hy
    exact hM4 y hy
  have hMol := Objects.TubeBridge.tubeDataOf_mollifier_props C P hP hSmall ρ₀ X
  have hShape := Objects.TubeBridge.tubeDataOf_bump_shape C P hP hSmall ρ₀ X S.widthEq
  have hFormula := Objects.TubeBridge.tubeDataOf_bump_formula C P hP hSmall ρ₀ X S.widthEq
  have hBlock := S.blockRadius_bounds
  unfold Objects.CorrectedEvent.DataMatch
  change T.r = C.r ∧ T.rho = C.ρ ∧ T.lambda = C.lamConst ∧
    T.A_endpt = C.A_endpt ∧ T.alpha = C.K_ann ∧
    T.K = Nat.ceil (C.lamConst / (C.A_loc * C.ρ)) ∧
    T.orientation ^ 4 = 1 ∧
    T.psiU ∈ Icc (-Real.pi/2) (Real.pi/2) ∧
    T.psiV ∈ Icc (-Real.pi/2) (Real.pi/2) ∧
    C.A_endpt*C.ρ*C.r ≤ T.blockRadius ∧
    T.blockRadius ≤ Real.sqrt C.A_endpt*C.ρ*C.r ∧
    0 < T.netRadius ∧ T.netRadius ≤ C.A_set*C.r/4 ∧
    T.netSites.Nonempty ∧
    (∀ x ∈ T.netSites, closedBall x (2*T.netRadius) ⊆ Objects.CorrectedEvent.tubeSet T) ∧
    (∀ x ∈ T.netSites, ∀ y ∈ T.netSites,
      Relation.ReflTransGen
        (fun u v : ℂ => u ∈ T.netSites ∧ v ∈ T.netSites ∧
          T.netRadius < dist u v ∧ dist u v < 2*T.netRadius) x y) ∧
    LQGMetric.Disconnects
      (⋃ x ∈ T.netSites, ball x T.netRadius)
      (closedBall 0 (1.5*C.r)) (ball 0 (2.5*C.r))ᶜ ∧
    (∀ y ∈ closure (Objects.CorrectedEvent.tubeSet T),
      ∃ x ∈ T.netSites, dist y x ≤ C.A_set*C.r/2) ∧
    (∀ x, 0 ≤ T.mollifier x) ∧
    (∀ x, C.A_sup*C.r/4 ≤ dist x 0 → T.mollifier x = 0) ∧
    (∫ x : ℂ, T.mollifier x) = 1 ∧
    (∀ x, T.bump x = Objects.CorrectedEvent.bumpFormula T C.A_max C.A_sup x) ∧
    (∀ x, 0 ≤ T.bump x ∧ T.bump x ≤ C.A_max) ∧
    (∀ x ∈ closure (Objects.CorrectedEvent.tubeSet T), T.bump x = C.A_max) ∧
    (∀ x ∉ Objects.CorrectedEvent.tubeV T C.A_sup, T.bump x = 0)
  exact ⟨rfl, S.rhoEq, rfl, rfl, S.alphaEq, S.countEq,
    S.orientFourth, (by simpa only [T, Objects.TubeBridge.tubeDataOf, neg_div] using S.angleU),
    (by simpa only [T, Objects.TubeBridge.tubeDataOf, neg_div] using S.angleV),
    hBlock.1, hBlock.2, hρ₀, hρ₀le, hX,
    hM1', hM2, hM3, hM4', hMol.1, hMol.2.1, hMol.2.2,
    hFormula, hShape.1, hShape.2.1, hShape.2.2⟩

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal
