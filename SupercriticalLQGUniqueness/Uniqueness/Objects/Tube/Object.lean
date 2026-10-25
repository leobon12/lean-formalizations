import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Conn
import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Family




 
















set_option autoImplicit false

noncomputable section

open Complex Set Metric Real QuantumZipper.CA.Topo
open scoped Pointwise

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Tube

 

def IsAnnularTubeA12 (z : ℂ) (r : ℝ) (U : Set ℂ) : Prop :=
  IsOpen U ∧ U ⊆ {x : ℂ | r < dist x z ∧ dist x z < 3 * r} ∧
    LQGMetric.Disconnects U (sphere z r) (sphere z (3 * r))

theorem image_add_sphere (z : ℂ) (ρ : ℝ) : (· + z) '' sphere (0 : ℂ) ρ = sphere z ρ := by
  ext x
  simp only [mem_image, mem_sphere, dist_zero_right]
  constructor
  · rintro ⟨y, hy, rfl⟩; rw [dist_eq_norm, add_sub_cancel_right]; exact hy
  · intro hx; exact ⟨x - z, by rw [← dist_eq_norm]; exact hx, sub_add_cancel x z⟩

 
theorem disconnects_translate {X E F : Set ℂ} (h : LQGMetric.Disconnects X E F) (z : ℂ) :
    LQGMetric.Disconnects ((· + z) '' X) ((· + z) '' E) ((· + z) '' F) := by
  intro x y γ hx hy
  obtain ⟨e, he, rfl⟩ := hx
  obtain ⟨f, hf, rfl⟩ := hy
  have γ' : Path e f := ((γ.map (continuous_sub_right z)).cast (by simp) (by simp))
  set γ'' : Path e f := (γ.map (continuous_sub_right z)).cast (by simp) (by simp) with hγ''
  obtain ⟨p, ⟨t, ht⟩, hpX⟩ := h e f γ'' he hf
  refine ⟨γ t, ⟨t, rfl⟩, p, hpX, ?_⟩
  rw [← ht, hγ'']
  simp

namespace TubeParams

variable {P : TubeParams} {r : ℝ}

 
def tubeAt (P : TubeParams) (r : ℝ) (z : ℂ) : Set ℂ := (· + z) '' P.tube r

 
def nbhdAt (P : TubeParams) (r Asup : ℝ) (z : ℂ) : Set ℂ := (· + z) '' P.nbhd r Asup

 
def bumpAt (P : TubeParams) (r Amax : ℝ) (A : Set.Ioi (0 : ℝ)) (z x : ℂ) : ℝ :=
  P.bump r Amax A (x - z)

theorem mem_tubeAt {z x : ℂ} : x ∈ P.tubeAt r z ↔ x - z ∈ P.tube r := by
  constructor
  · rintro ⟨y, hy, rfl⟩; rwa [add_sub_cancel_right]
  · intro h; exact ⟨x - z, h, sub_add_cancel x z⟩

theorem mem_nbhdAt {Asup : ℝ} {z x : ℂ} : x ∈ P.nbhdAt r Asup z ↔ x - z ∈ P.nbhd r Asup := by
  constructor
  · rintro ⟨y, hy, rfl⟩; rwa [add_sub_cancel_right]
  · intro h; exact ⟨x - z, h, sub_add_cancel x z⟩

section Object

variable (hP : P.Good) (hr : 0 < r) {Asup : ℝ} (hA0 : 0 < Asup) (hA : 100 * Asup ≤ P.sp * P.ρ)
include hP hr

theorem annulus_of_nbhd (hA : 100 * Asup ≤ P.sp * P.ρ) {x : ℂ}
    (hx : x ∈ closure (P.nbhd r Asup)) : r < ‖x‖ ∧ ‖x‖ < 3 * r := by
  have := closure_nbhd_subset hP hr hA hx
  constructor <;> nlinarith [this.1, this.2]

 
theorem tubeAt_annular (hA0 : 0 < Asup) (hA : 100 * Asup ≤ P.sp * P.ρ) (z : ℂ) :
    IsAnnularTubeA12 z r (P.tubeAt r z) := by
  refine ⟨(isOpenMap_add_right z) _ (P.isOpen_tube_of r (mul_pos hP.ρ_pos hr).ne' hP.n_ne), ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have h := annulus_of_nbhd hP hr hA (subset_closure (self_subset_thickening (mul_pos hA0 hr) _ hy))
    show r < dist (y + z) z ∧ dist (y + z) z < 3 * r
    rw [dist_eq_norm, add_sub_cancel_right]
    exact h
  · have := disconnects_translate (tube_disconnects hP hr) z
    rwa [image_add_sphere, image_add_sphere] at this

 
theorem nbhdAt_annular (hA0 : 0 < Asup) (hA : 100 * Asup ≤ P.sp * P.ρ) (z : ℂ) :
    IsAnnularTubeA12 z r (P.nbhdAt r Asup z) := by
  refine ⟨(isOpenMap_add_right z) _ isOpen_thickening, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have h := annulus_of_nbhd hP hr hA (subset_closure hy)
    show r < dist (y + z) z ∧ dist (y + z) z < 3 * r
    rw [dist_eq_norm, add_sub_cancel_right]
    exact h
  · have := disconnects_translate (nbhd_disconnects hP hr hA0) z
    rwa [image_add_sphere, image_add_sphere] at this

omit hP in
 
theorem closure_tubeAt_subset (hA0 : 0 < Asup) (z : ℂ) :
    closure (P.tubeAt r z) ⊆ P.nbhdAt r Asup z := by
  unfold tubeAt nbhdAt
  have e : (fun x : ℂ => x + z) = ⇑(Homeomorph.addRight z) := (Homeomorph.coe_addRight z).symm
  rw [e, ← Homeomorph.image_closure]
  exact image_mono (closure_tube_subset_nbhd hr hA0)

 
theorem closure_nbhdAt_subset (hA : 100 * Asup ≤ P.sp * P.ρ) (z : ℂ) :
    closure (P.nbhdAt r Asup z) ⊆ {x : ℂ | r < dist x z ∧ dist x z < 3 * r} := by
  unfold nbhdAt
  have e : (fun x : ℂ => x + z) = ⇑(Homeomorph.addRight z) := (Homeomorph.coe_addRight z).symm
  rw [e, ← Homeomorph.image_closure]
  rintro _ ⟨y, hy, rfl⟩
  have h := annulus_of_nbhd hP hr hA hy
  show r < dist (Homeomorph.addRight z y) z ∧ dist (Homeomorph.addRight z y) z < 3 * r
  rw [Homeomorph.coe_addRight, dist_eq_norm, add_sub_cancel_right]
  exact h

omit hP hr in
theorem bumpAt_eq_on_tube (Amax : ℝ) (A : Set.Ioi (0 : ℝ)) (z : ℂ) {x : ℂ}
    (hx : x ∈ closure (P.tubeAt r z)) : P.bumpAt r Amax A z x = Amax := by
  unfold bumpAt tubeAt at *
  have e : (fun x : ℂ => x + z) = ⇑(Homeomorph.addRight z) := (Homeomorph.coe_addRight z).symm
  rw [e, ← Homeomorph.image_closure] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [Homeomorph.coe_addRight]
  simp only [add_sub_cancel_right]
  exact bump_eq_of_mem_closure Amax A hy

omit hP in
theorem bumpAt_eq_zero (Amax : ℝ) (A : Set.Ioi (0 : ℝ)) (z : ℂ) {x : ℂ}
    (hx : x ∉ P.nbhdAt r A z) : P.bumpAt r Amax A z x = 0 := by
  unfold bumpAt
  exact bump_eq_zero hr Amax A (fun h => hx (mem_nbhdAt.mpr h))

 
def bumpAtTest (P : TubeParams) (r Amax : ℝ) (A : Set.Ioi (0 : ℝ)) (z : ℂ) (hP : P.Good)
    (hr : 0 < r) (hA : 100 * (A : ℝ) ≤ P.sp * P.ρ) : LQGMetric.TestC :=
  ⟨P.bumpAt r Amax A z, (contDiff_bump Amax A).comp (contDiff_id.sub contDiff_const),
    (hasCompactSupport_bump hP hr Amax A hA).comp_homeomorph (Homeomorph.subRight z),
    subset_univ _⟩

 


theorem loop_disconnects_at (hA : 100 * Asup ≤ P.sp * P.ρ) (z : ℂ) (L : C(unitInterval, ℂ))
    (hc : L 0 = L 1) (hV : ∀ t, L t ∈ P.nbhdAt r Asup z) (hne : ∀ t, L t - z ≠ 0)
    (hdeg : loopDeg (L - ContinuousMap.const unitInterval z) hne ≠ 0) :
    LQGMetric.Disconnects (range L) (sphere z r) (sphere z (3 * r)) := by
  set L' : C(unitInterval, ℂ) := L - ContinuousMap.const unitInterval z with hL'
  have hc' : L' 0 = L' 1 := by simp [hL', hc]
  have hb : ∀ t, r < ‖L' t‖ ∧ ‖L' t‖ < 3 * r := fun t =>
    annulus_of_nbhd hP hr hA (subset_closure (mem_nbhdAt.mp (hV t)))
  have h0 := Objects.TubeLoops.loop_disconnects L' hc' hne hdeg (fun t => (hb t).1) (fun t => (hb t).2)
  have h1 := disconnects_translate h0 z
  have hrange : (· + z) '' range L' = range L := by
    ext x
    constructor
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, by simp [hL']⟩
    · rintro ⟨t, rfl⟩
      exact ⟨L' t, ⟨t, rfl⟩, by simp [hL']⟩
  rw [hrange] at h1
  refine h1.mono le_rfl ?_ ?_
  · intro x hx
    rw [mem_sphere] at hx
    exact ⟨x - z, by rw [mem_closedBall, dist_zero_right, ← dist_eq_norm, hx], sub_add_cancel x z⟩
  · intro x hx
    rw [mem_sphere] at hx
    refine ⟨x - z, ?_, sub_add_cancel x z⟩
    rw [mem_compl_iff, mem_ball, dist_zero_right, ← dist_eq_norm, hx]
    exact lt_irrefl _

 

 
theorem tube_open_bounded_pathConnected : IsOpen (P.tube r) ∧ P.tube r ⊆ ball 0 (3 * r) ∧ IsPathConnected (P.tube r) := by
  refine ⟨P.isOpen_tube_of r (mul_pos hP.ρ_pos hr).ne' hP.n_ne, fun x hx => ?_, isPathConnected_tube hP hr⟩
  have h := tube_near_circle hP hr hx
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  have hw : P.w r ≤ P.ρ * r := by
    have h1 := hP.wp_le; have h2 := hP.sp_le'
    calc P.w r = P.wp * (P.ρ * r) := by unfold w; ring
      _ ≤ 1 * (P.ρ * r) := mul_le_mul_of_nonneg_right (by linarith) hm.le
      _ = P.ρ * r := one_mul _
  have hρ := hP.ρ_le
  rw [abs_le] at h
  rw [mem_ball, dist_zero_right]
  nlinarith [hP.ρ_pos]

 
theorem nbhd_and_thickening_subset_annulus (hA : 100 * Asup ≤ P.sp * P.ρ) :
    P.nbhd r Asup ⊆ {x : ℂ | (3 / 2) * r < ‖x‖ ∧ ‖x‖ < (5 / 2) * r} ∧
    ∀ δ ≤ P.ρ * r, thickening δ (P.nbhd r Asup) ⊆ {x : ℂ | (3 / 2) * r < ‖x‖ ∧ ‖x‖ < 3 * r} := by
  refine ⟨fun x hx => near_closure_nbhd hP hr hA (subset_closure hx) (δ := 0)
    (by nlinarith [hP.ρ_pos]) (by rw [dist_self]), ?_⟩
  intro δ hδ x hx
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hx
  have := near_closure_nbhd hP hr hA (subset_closure hy) hδ hxy.le
  exact ⟨this.1, by linarith [this.2]⟩

 
theorem exists_unit_winding_loop_in_tube : ∃ (L : C(unitInterval, ℂ)) (_ : L 0 = L 1) (hne : ∀ t, L t ≠ 0),
    range L ⊆ P.tube r ∧ loopDeg L hne = 1 :=
  ⟨P.spine r, spine_closed hP, spine_ne_zero hP hr, range_spine_subset_tube hP hr,
    spine_loopDeg hP hr⟩

 

theorem block_balls_subset_tube_and_norm_bounds (k : ℤ) :
    ball (P.uC r k) (P.s r) ⊆ P.tube r ∧ ball (P.vC r k) (P.s r) ⊆ P.tube r ∧
    (2 - 2 * P.ρ) * r ≤ ‖P.uC r k‖ ∧ ‖P.uC r k‖ ≤ (2 + 2 * P.ρ) * r ∧
    (2 - 2 * P.ρ) * r ≤ ‖P.vC r k‖ ∧ ‖P.vC r k‖ ≤ (2 + 2 * P.ρ) * r := by
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  have hu := dist_uC_site hP hr k
  have hv := dist_vC_site hP hr k
  have hα1 := hP.α_lt
  have hα0 : 0 ≤ P.α := by linarith [hP.α_gt]
  obtain ⟨hu1, hu2⟩ := norm_bounds_of_near_site (P := P) hr k (le_of_eq hu)
  obtain ⟨hv1, hv2⟩ := norm_bounds_of_near_site (P := P) hr k (le_of_eq hv)
  refine ⟨fun x hx => mem_iUnion.mpr ⟨k, Or.inl (Or.inl (Or.inr hx))⟩,
    fun x hx => mem_iUnion.mpr ⟨k, Or.inl (Or.inr hx)⟩, ?_, ?_, ?_, ?_⟩ <;> nlinarith

 
theorem bump_smooth_compact_supported_and_bounds {Amax : ℝ} (hAmax : 0 ≤ Amax) (A : Set.Ioi (0 : ℝ))
    (hA : 100 * (A : ℝ) ≤ P.sp * P.ρ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (P.bump r Amax A) ∧ HasCompactSupport (P.bump r Amax A) ∧
    (∀ x, 0 ≤ P.bump r Amax A x ∧ P.bump r Amax A x ≤ Amax) ∧
    (∀ x ∈ closure (P.tube r), P.bump r Amax A x = Amax) ∧
    (∀ x ∉ P.nbhd r A, P.bump r Amax A x = 0) :=
  ⟨contDiff_bump Amax A, hasCompactSupport_bump hP hr Amax A hA,
    fun x => ⟨bump_nonneg hAmax A x, bump_le hAmax A x⟩,
    fun _ hx => bump_eq_of_mem_closure Amax A hx, fun _ hx => bump_eq_zero hr Amax A hx⟩

omit hP hr in
 
theorem centres_scale (k : ℤ) : P.uC r k = r • P.uC 1 k ∧ P.vC r k = r • P.vC 1 k :=
  ⟨modMap_scale k _, modMap_scale k _⟩

end Object

end TubeParams

end SupercriticalLQGUniqueness.Uniqueness.Objects.Tube
