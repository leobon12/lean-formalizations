import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.G1
import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Glue
import SupercriticalLQGUniqueness.Uniqueness.Objects.TubeLoops.Loop




 










set_option autoImplicit false

noncomputable section

open Complex Set Metric Real QuantumZipper.CA.Topo

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Tube

namespace TubeParams

variable {P : TubeParams} {r : ℝ}

 
abbrev uMinus (P : TubeParams) (r : ℝ) (k : ℤ) : ℂ := P.modMap r k (pol (P.α - 3 * P.sp / 4) P.ψu)

 
def modSpine (P : TubeParams) (r : ℝ) (k : ℤ) : Path (P.uMinus r k) (P.uMinus r (k + 1)) :=
  ((blockSpine P.α P.sp P.ψu P.ψv).map (P.continuous_modMap r k)).trans (P.connPath r k)

 
def spine (P : TubeParams) (r : ℝ) : C(unitInterval, ℂ) :=
  ⟨fun t => glue (P.uMinus r) (P.modSpine r) (P.K * (t : ℝ)),
    (continuous_glue _ _).comp (continuous_const.mul continuous_subtype_val)⟩

theorem spine_apply (t : unitInterval) :
    P.spine r t = glue (P.uMinus r) (P.modSpine r) (P.K * (t : ℝ)) := rfl

theorem range_modSpine (k : ℤ) :
    range (P.modSpine r k) =
      P.modMap r k '' range (blockSpine P.α P.sp P.ψu P.ψv) ∪ P.conn r k := by
  rw [modSpine, Path.trans_range, range_path_map]
  rfl

section Spine

variable (hP : P.Good) (hr : 0 < r)
include hP hr

omit hr in
theorem spine_closed : P.spine r 0 = P.spine r 1 := by
  simp only [spine_apply, Set.Icc.coe_zero, Set.Icc.coe_one, mul_zero, mul_one]
  have h0 := glue_int (P.uMinus r) (P.modSpine r) 0
  have hK := glue_int (P.uMinus r) (P.modSpine r) (P.K : ℤ)
  push_cast at h0 hK
  rw [h0, hK]
  unfold uMinus
  have := modMap_add_K (P := P) (r := r) hP.K_ne 0 (pol (P.α - 3 * P.sp / 4) P.ψu)
  rw [zero_add] at this
  exact this.symm

theorem modSpine_subset_tube (k : ℤ) : range (P.modSpine r k) ⊆ P.tube r := by
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  have hw : 0 < P.w r := by unfold w; have := hP.wp_pos; have := hP.ρ_pos; positivity
  rw [range_modSpine]
  intro x hx
  simp only [tube, mem_iUnion]
  refine ⟨k, ?_⟩
  rcases hx with ⟨ζ, hζ, rfl⟩ | hx
  · rcases blockSpine_mem hP.α_gt hP.α_lt hP.sp_pos (by linarith [hP.sp_le, hP.sp_pos]) hP.ψu_mem hP.ψv_mem hζ
      with h | h | h
    · left; left; right
      rw [mem_ball] at h ⊢
      unfold uC
      rw [dist_modMap' hP hr, show P.s r = P.ρ * r * P.sp by unfold s; ring]
      exact mul_lt_mul_of_pos_left h hm
    · left; left; left
      exact ⟨ζ, h, rfl⟩
    · left; right
      rw [mem_ball] at h ⊢
      unfold vC
      rw [dist_modMap' hP hr, show P.s r = P.ρ * r * P.sp by unfold s; ring]
      exact mul_lt_mul_of_pos_left h hm
  · right
    exact self_subset_thickening hw _ hx

theorem spine_mem_tube (t : unitInterval) : P.spine r t ∈ P.tube r := by
  rw [spine_apply]
  exact modSpine_subset_tube hP hr _ (glue_mem_range _ _ _)

theorem dist_site_succ (k : ℤ) : dist (P.site r (k + 1)) (P.site r k) ≤ 2 * r * (2 * π / P.K) := by
  rw [Complex.dist_eq]
  unfold site
  rw [ω_add_one hP.K_ne]
  have := norm_pol_sub_pol_le (2 * r) (P.ω k + 2 * π / P.K) (P.ω k)
  rw [abs_of_nonneg (by linarith), show P.ω k + 2 * π / P.K - P.ω k = 2 * π / P.K
    by ring, abs_of_nonneg (by have := hP.K_pos; positivity)] at this
  exact this

 
theorem dist_modSpine_site (k : ℤ) {x : ℂ} (hx : x ∈ range (P.modSpine r k)) :
    dist x (P.site r k) ≤ 4 * (P.ρ * r) + 2 * r * (2 * π / P.K) := by
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  have hd := dist_site_succ hP hr k
  have hpos : 0 ≤ 2 * r * (2 * π / P.K) := by have := hP.K_pos; positivity
  rw [range_modSpine] at hx
  rcases hx with ⟨ζ, hζ, rfl⟩ | hx
  · have hn := norm_le_of_mem_blockSpine hP.α_gt hP.α_lt hP.sp_pos
      (by linarith [hP.sp_le, hP.sp_pos]) hP.ψu_mem hP.ψv_mem hζ
    have := dist_modMap_site_le hP hr k hn
    have hsp := hP.sp_le'
    nlinarith
  · rw [conn_eq] at hx
    rcases hx with (hx | hx) | hx
    · have := dist_outA_site hP hr hx; linarith
    · rw [range_corridor_eq] at hx
      have hconv : Convex ℝ (closedBall (P.site r k) (4 * (P.ρ * r) + 2 * r * (2 * π / P.K))) :=
        convex_closedBall _ _
      have h1 : P.gatePlus r k ∈ closedBall (P.site r k) (4 * (P.ρ * r) + 2 * r * (2 * π / P.K)) := by
        rw [mem_closedBall, gatePlus_eq hP.n_norm, Complex.dist_eq, add_sub_cancel_left, norm_mul,
          norm_tangent, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mul_pos (mul_pos four_pos hP.ρ_pos) hr).le]
        linarith
      have h2 : P.gateMinus r (k + 1) ∈
          closedBall (P.site r k) (4 * (P.ρ * r) + 2 * r * (2 * π / P.K)) := by
        rw [mem_closedBall]
        have e : dist (P.gateMinus r (k + 1)) (P.site r (k + 1)) = 4 * (P.ρ * r) := by
          rw [gateMinus_eq hP.n_norm, Complex.dist_eq, sub_sub_cancel_left, norm_neg, norm_mul,
            norm_tangent, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (mul_pos (mul_pos four_pos hP.ρ_pos) hr).le]
          ring
        linarith [dist_triangle (P.gateMinus r (k + 1)) (P.site r (k + 1)) (P.site r k)]
      exact mem_closedBall.mp (hconv.segment_subset h1 h2 hx)
    · have := dist_inA_site hP hr hx
      linarith [dist_triangle x (P.site r (k + 1)) (P.site r k)]

theorem spine_norm_bounds (t : unitInterval) : r < ‖P.spine r t‖ ∧ ‖P.spine r t‖ < 3 * r := by
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  have h := tube_near_circle hP hr (spine_mem_tube hP hr t)
  have hw : P.w r ≤ P.ρ * r := by
    unfold w; have := hP.wp_le; have := hP.sp_le'; have := hP.wp_pos; nlinarith
  have hρ := hP.ρ_le
  rw [abs_le] at h
  constructor <;> nlinarith

theorem spine_ne_zero (t : unitInterval) : P.spine r t ≠ 0 := by
  intro h
  have := (spine_norm_bounds hP hr t).1
  rw [h, norm_zero] at this
  linarith

 
theorem spine_leash (t : unitInterval) : ‖P.spine r t - circleLoop (2 * r) t‖ < 2 * r := by
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  have hK := hP.K_pos
  have hKge := hP.K_ge
  set x := (P.K : ℝ) * (t : ℝ) with hx
  set k := ⌊x⌋ with hk
  have hxk : x ∈ Ico (k : ℝ) (k + 1) := Int.floor_eq_iff.mp hk.symm
  have h1 : dist (P.spine r t) (P.site r k) ≤ 4 * (P.ρ * r) + 2 * r * (2 * π / P.K) := by
    rw [spine_apply]
    exact dist_modSpine_site hP hr k (glue_mem_range _ _ _)
  have hc : circleLoop (2 * r) t = pol (2 * r) (2 * π * (t : ℝ)) := by
    simp only [circleLoop, ContinuousMap.coe_mk, circleMap, zero_add, pol, ex]
  have h2 : dist (P.site r k) (circleLoop (2 * r) t) ≤ 2 * r * (2 * π / P.K) := by
    rw [hc, Complex.dist_eq]
    unfold site
    have := norm_pol_sub_pol_le (2 * r) (P.ω k) (2 * π * (t : ℝ))
    rw [abs_of_nonneg (by linarith)] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    have e : P.ω k - 2 * π * (t : ℝ) = -(2 * π / P.K) * (x - k) := by
      unfold ω; rw [hx]; field_simp; ring
    rw [e, abs_mul, abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg (by linarith [hxk.1])]
    have : x - k ≤ 1 := by linarith [hxk.2]
    nlinarith [show 0 ≤ 2 * π / P.K by positivity]
  have h3 := dist_triangle (P.spine r t) (P.site r k) (circleLoop (2 * r) t)
  have hD : 0 ≤ 2 * r * (2 * π / P.K) := by positivity
  rw [← Complex.dist_eq]
  have hsmall : 4 * (P.ρ * r) + 4 * (2 * r * (2 * π / P.K)) < 2 * r := by
    have hρ := hP.ρ_le
    have : 2 * π / P.K ≤ 2 * π / 100 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hKge
    nlinarith [Real.pi_lt_d2]
  linarith

 
theorem spine_loopDeg : loopDeg (P.spine r) (spine_ne_zero hP hr) = 1 :=
  Objects.TubeLoops.loopDeg_eq_one_of_near_circle _ (spine_closed hP) _ (by linarith) (spine_leash hP hr)

 

theorem spine_disconnects :
    LQGMetric.Disconnects (range (P.spine r)) (closedBall 0 r) (ball 0 (3 * r))ᶜ :=
  Objects.TubeLoops.loop_disconnects _ (spine_closed hP) (spine_ne_zero hP hr)
    (by rw [spine_loopDeg hP hr]; norm_num) (fun t => (spine_norm_bounds hP hr t).1)
    (fun t => (spine_norm_bounds hP hr t).2)

theorem range_spine_subset_tube : range (P.spine r) ⊆ P.tube r := by
  rintro _ ⟨t, rfl⟩; exact spine_mem_tube hP hr t

 
theorem tube_disconnects :
    LQGMetric.Disconnects (P.tube r) (sphere 0 r) (sphere 0 (3 * r)) :=
  (spine_disconnects hP hr).mono (range_spine_subset_tube hP hr) sphere_subset_closedBall
    (fun y hy => by rw [mem_sphere] at hy; rw [mem_compl_iff, mem_ball, hy]; exact lt_irrefl _)

 
theorem nbhd_disconnects {Asup : ℝ} (hA0 : 0 < Asup) :
    LQGMetric.Disconnects (P.nbhd r Asup) (sphere 0 r) (sphere 0 (3 * r)) :=
  (tube_disconnects hP hr).mono (self_subset_thickening (mul_pos hA0 hr) _) le_rfl le_rfl

end Spine

end TubeParams

end SupercriticalLQGUniqueness.Uniqueness.Objects.Tube
