import QuantumZipper.Proofs.Complex.TopoDegree
import LQGMetric.Topo.Disconnect




 















set_option autoImplicit false

open Set Metric QuantumZipper.CA.Topo

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.TubeLoops

 
theorem loop_sep (L : C(unitInterval, ℂ)) (hc : L 0 = L 1) (hne : ∀ t, L t ≠ 0)
    (hdeg : loopDeg L hne ≠ 0) {a b : ℂ} (ha : ∀ t, ‖a‖ < ‖L t‖) (hb : ∀ t, ‖L t‖ < ‖b‖)
    (γ : Path a b) : (range γ ∩ range L).Nonempty := by
  by_contra hemp
  have hH : ∀ p : unitInterval × unitInterval, L p.1 - γ p.2 ≠ 0 := by
    intro p hp
    exact hemp ⟨γ p.2, ⟨p.2, rfl⟩, ⟨p.1, (sub_eq_zero.mp hp)⟩⟩
  let H : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun p => L p.1 - γ p.2, by fun_prop⟩
  have hH' : ∀ p, H p ≠ 0 := hH
  have hcH : ∀ s, H (0, s) = H (1, s) := fun s => by simp [H, hc]
  have key := loopDeg_homotopy H hH' hcH
  
  have h0 : loopDeg (slice H 0) (fun _ => hH' _) = loopDeg L hne := by
    apply loopDeg_eq_of_norm_sub_lt (slice H 0) L (fun _ => hH' _) hne
      (by simp [slice, H, hc]) hc
    intro t
    simp only [slice, H, ContinuousMap.coe_mk, Path.source]
    rw [show L t - a - L t = -a by ring, norm_neg]
    exact ha t
  
  have hb0 : (-b) ≠ 0 := by
    intro h
    have := hb 0
    rw [neg_eq_zero.mp h, norm_zero] at this
    exact (not_lt.mpr (norm_nonneg _)) this
  have h1 : loopDeg (slice H 1) (fun _ => hH' _) =
      loopDeg (ContinuousMap.const unitInterval (-b)) (fun _ => hb0) := by
    apply loopDeg_eq_of_norm_sub_lt (slice H 1) (ContinuousMap.const unitInterval (-b))
      (fun _ => hH' _) (fun _ => hb0) (by simp [slice, H, hc]) rfl
    intro t
    simp only [slice, H, ContinuousMap.coe_mk, Path.target, ContinuousMap.const_apply]
    rw [show L t - b - -b = L t by ring, norm_neg]
    exact hb t
  rw [h0, h1, loopDeg_const] at key
  exact hdeg key

 

theorem loop_disconnects (L : C(unitInterval, ℂ)) (hc : L 0 = L 1) (hne : ∀ t, L t ≠ 0)
    (hdeg : loopDeg L hne ≠ 0) {r R : ℝ} (hr : ∀ t, r < ‖L t‖) (hR : ∀ t, ‖L t‖ < R) :
    LQGMetric.Disconnects (range L) (closedBall 0 r) (ball 0 R)ᶜ := by
  intro x y γ hx hy
  have hx' : ‖x‖ ≤ r := by simpa using hx
  have hy' : R ≤ ‖y‖ := by simpa using hy
  exact loop_sep L hc hne hdeg (fun t => lt_of_le_of_lt hx' (hr t))
    (fun t => lt_of_lt_of_le (hR t) hy') γ

 
theorem loopDeg_eq_one_of_near_circle (L : C(unitInterval, ℂ)) (hc : L 0 = L 1)
    (hne : ∀ t, L t ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) (h : ∀ t, ‖L t - circleLoop ρ t‖ < ρ) :
    loopDeg L hne = 1 := by
  have hcc : circleLoop ρ 0 = circleLoop ρ 1 := by
    simp only [circleLoop, ContinuousMap.coe_mk, Set.Icc.coe_zero, Set.Icc.coe_one]
    simpa using (periodic_circleMap 0 ρ 0).symm
  have hnorm : ∀ t, ‖circleLoop ρ t‖ = ρ := fun t => by
    simp only [circleLoop, ContinuousMap.coe_mk]
    rw [norm_circleMap_zero, abs_of_pos hρ]
  rw [loopDeg_eq_of_norm_sub_lt L (circleLoop ρ) hne (circleLoop_ne_zero hρ.ne') hc hcc
    (fun t => by rw [hnorm t]; exact h t)]
  exact loopDeg_circle hρ.ne'

 
theorem subpath {p₀ p₁ : ℂ} (γ : Path p₀ p₁) (s s' : unitInterval) :
    ∃ σ : Path (γ s) (γ s'), range σ ⊆ range γ := by
  rcases le_total (s : ℝ) s' with h | h
  · refine ⟨(γ.truncateOfLE h).cast (γ.extend_extends' s).symm (γ.extend_extends' s').symm, ?_⟩
    intro w ⟨u, hu⟩
    apply γ.truncate_range
    refine ⟨u, ?_⟩
    rw [← hu]
    rfl
  · refine ⟨((γ.truncateOfLE h).cast (γ.extend_extends' s').symm
      (γ.extend_extends' s).symm).symm, ?_⟩
    rw [Path.symm_range]
    intro w ⟨u, hu⟩
    apply γ.truncate_range
    refine ⟨u, ?_⟩
    rw [← hu]
    rfl

 
def radPath (c e : ℂ) (a b : ℝ) : Path (c + (a : ℂ) * e) (c + (b : ℂ) * e) where
  toFun t := c + ((a + (t : ℝ) * (b - a) : ℝ) : ℂ) * e
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

theorem radPath_apply (c e : ℂ) (a b : ℝ) (t : unitInterval) :
    radPath c e a b t = c + ((a + (t : ℝ) * (b - a) : ℝ) : ℂ) * e := rfl

 


theorem loops_meet {x x' : ℂ} {δ : ℝ} (hδ : 0 < δ) (hd1 : δ ≤ dist x x')
    (hd2 : dist x x' ≤ 2 * δ) {K : Set ℂ}
    (hK : LQGMetric.Disconnects K (sphere x δ) (sphere x (2 * δ)))
    {p₀ p₁ : ℂ} (π' : Path p₀ p₁)
    (hA : ∀ t, δ < dist (π' t) x' ∧ dist (π' t) x' < 2 * δ)
    (hD : LQGMetric.Disconnects (range π') (sphere x' δ) (sphere x' (2 * δ))) :
    (K ∩ range π').Nonempty := by
  set d := dist x x' with hd
  have hdpos : 0 < d := lt_of_lt_of_le hδ hd1
  have hne : x - x' ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [hd, h, dist_self] at hdpos
    exact lt_irrefl _ hdpos
  set e : ℂ := (x - x') / (d : ℂ) with he
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hnd : ‖x - x'‖ = d := by rw [hd, dist_eq_norm]
  have hen : ‖e‖ = 1 := by
    rw [he, norm_div, hnd, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdpos,
      div_self hdpos.ne']
  have hxe : x = x' + (d : ℂ) * e := by
    rw [he]; field_simp; ring
  
  have hdist_ray : ∀ ρ : ℝ, dist (x' + (ρ : ℂ) * e) x' = |ρ| := fun ρ => by
    rw [dist_eq_norm, show x' + (ρ : ℂ) * e - x' = (ρ : ℂ) * e by ring, norm_mul, hen,
      mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hdist_x : ∀ ρ : ℝ, dist (x' + (ρ : ℂ) * e) x = |ρ - d| := fun ρ => by
    rw [dist_eq_norm, hxe, show x' + (ρ : ℂ) * e - (x' + (d : ℂ) * e) = ((ρ - d : ℝ) : ℂ) * e by
      push_cast; ring, norm_mul, hen, mul_one, Complex.norm_real, Real.norm_eq_abs]
  
  obtain ⟨p, ⟨tp, htp⟩, hpπ⟩ := hD _ _ (radPath x' e δ (2 * δ))
    (by rw [mem_sphere, hdist_ray, abs_of_pos hδ])
    (by rw [mem_sphere, hdist_ray, abs_of_pos (by linarith)])
  
  obtain ⟨q, ⟨tq, htq⟩, hqπ⟩ := hD _ _ (radPath x' (-e) δ (2 * δ))
    (by
      rw [mem_sphere, show x' + (δ : ℂ) * -e = x' + ((-δ : ℝ) : ℂ) * e by push_cast; ring,
        hdist_ray, abs_neg, abs_of_pos hδ])
    (by
      rw [mem_sphere, show x' + ((2 * δ : ℝ) : ℂ) * -e = x' + ((-(2 * δ) : ℝ) : ℂ) * e by
        push_cast; ring, hdist_ray, abs_neg, abs_of_pos (by linarith)])
  set ρp : ℝ := δ + (tp : ℝ) * (2 * δ - δ) with hρp
  set ρq : ℝ := δ + (tq : ℝ) * (2 * δ - δ) with hρq
  have hp_eq : p = x' + (ρp : ℂ) * e := by rw [← htp, radPath_apply]
  have hq_eq : q = x' + ((-ρq : ℝ) : ℂ) * e := by
    rw [← htq, radPath_apply, hρq]; push_cast; ring
  obtain ⟨sp, hsp⟩ := hpπ
  obtain ⟨sq, hsq⟩ := hqπ
  have hρp_bounds : δ < ρp ∧ ρp < 2 * δ := by
    have := hA sp
    rw [hsp, hp_eq, hdist_ray] at this
    have hρp0 : 0 ≤ ρp := by
      rw [hρp]
      have := tp.2.1
      nlinarith
    rwa [abs_of_nonneg hρp0] at this
  have hρq_bounds : δ < ρq ∧ ρq < 2 * δ := by
    have := hA sq
    rw [hsq, hq_eq, hdist_ray, abs_neg] at this
    have hρq0 : 0 ≤ ρq := by
      rw [hρq]
      have := tq.2.1
      nlinarith
    rwa [abs_of_nonneg hρq0] at this
  have hp_in : π' sp ∈ closedBall x δ := by
    rw [mem_closedBall, hsp, hp_eq, hdist_x]
    rw [abs_le]
    constructor <;> linarith [hρp_bounds.1, hρp_bounds.2, hd1, hd2]
  have hq_out : π' sq ∈ (ball x (2 * δ))ᶜ := by
    rw [mem_compl_iff, mem_ball, not_lt, hsq, hq_eq, hdist_x]
    rw [show -ρq - d = -(ρq + d) by ring, abs_neg, abs_of_pos (by linarith [hρq_bounds.1])]
    linarith [hρq_bounds.1, hd1]
  obtain ⟨σ, hσ⟩ := subpath π' sp sq
  obtain ⟨w, hwσ, hwK⟩ := hK.closedBall_compl_ball (by linarith) _ _ σ hp_in hq_out
  exact ⟨w, hwK, hσ hwσ⟩

end SupercriticalLQGUniqueness.Uniqueness.Objects.TubeLoops

