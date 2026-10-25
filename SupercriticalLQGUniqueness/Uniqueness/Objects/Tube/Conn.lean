import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Spine




 







set_option autoImplicit false

noncomputable section

open Complex Set Metric Real

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Tube

namespace TubeParams

variable {P : TubeParams} {r : ℝ}

 
def spineSet (P : TubeParams) (r : ℝ) : Set ℂ := ⋃ k : ℤ, range (P.modSpine r k)

section Conn

variable (hP : P.Good) (hr : 0 < r)
include hP hr

theorem spineSet_subset_tube : P.spineSet r ⊆ P.tube r :=
  iUnion_subset fun k => modSpine_subset_tube hP hr k

omit hP hr in
theorem joinedIn_modSpine (k : ℤ) {p q : ℂ} (hp : p ∈ range (P.modSpine r k))
    (hq : q ∈ range (P.modSpine r k)) : JoinedIn (P.spineSet r) p q := by
  obtain ⟨s, rfl⟩ := hp
  obtain ⟨t, rfl⟩ := hq
  obtain ⟨σ, hσ⟩ := Objects.TubeLoops.subpath (P.modSpine r k) s t
  exact ⟨σ, fun u => mem_iUnion.mpr ⟨k, hσ ⟨u, rfl⟩⟩⟩

omit hP hr in
theorem uMinus_mem (k : ℤ) : P.uMinus r k ∈ range (P.modSpine r k) :=
  ⟨0, (P.modSpine r k).source⟩

omit hP hr in
theorem uMinus_mem_prev (k : ℤ) : P.uMinus r (k + 1) ∈ range (P.modSpine r k) :=
  ⟨1, (P.modSpine r k).target⟩

omit hP hr in
theorem joinedIn_uMinus_succ (k : ℤ) : JoinedIn (P.spineSet r) (P.uMinus r k) (P.uMinus r (k + 1)) :=
  joinedIn_modSpine k (uMinus_mem k) (uMinus_mem_prev k)

omit hP hr in
theorem joinedIn_uMinus_zero (k : ℤ) : JoinedIn (P.spineSet r) (P.uMinus r 0) (P.uMinus r k) := by
  induction k using Int.induction_on with
  | zero => exact JoinedIn.refl (by exact mem_iUnion.mpr ⟨0, uMinus_mem 0⟩)
  | succ m ih => exact ih.trans (joinedIn_uMinus_succ m)
  | pred m ih =>
    have h := joinedIn_uMinus_succ (P := P) (r := r) (-(m : ℤ) - 1)
    rw [show -(m : ℤ) - 1 + 1 = -m by ring] at h
    exact ih.trans h.symm

omit hP hr in
 
theorem joinedIn_spineSet {p : ℂ} (hp : p ∈ P.spineSet r) :
    JoinedIn (P.spineSet r) p (P.uMinus r 0) := by
  obtain ⟨k, hk⟩ := mem_iUnion.mp hp
  exact (joinedIn_modSpine k hk (uMinus_mem k)).trans (joinedIn_uMinus_zero k).symm

 
theorem joinedIn_of_convex {S : Set ℂ} (hS : Convex ℝ S) (hSU : S ⊆ P.tube r) {x p : ℂ}
    (hx : x ∈ S) (hp : p ∈ S) (hps : p ∈ P.spineSet r) : JoinedIn (P.tube r) x (P.uMinus r 0) :=
  (((hS.isPathConnected ⟨x, hx⟩).joinedIn x hx p hp).mono hSU).trans
    ((joinedIn_spineSet hps).mono (spineSet_subset_tube hP hr))

 
theorem joinedIn_tube {x : ℂ} (hx : x ∈ P.tube r) : JoinedIn (P.tube r) x (P.uMinus r 0) := by
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  have hsr : P.s r = P.ρ * r * P.sp := by unfold s; ring
  have hsp := hP.sp_pos
  have hsp' := hP.sp_le'
  have hα := hP.α_gt
  have hw : 0 < P.w r := by unfold w; have := hP.wp_pos; have := hP.ρ_pos; positivity
  simp only [tube, mem_iUnion] at hx
  obtain ⟨k, hx⟩ := hx
  have hsum : ∀ y ∈ P.block r k ∪ ball (P.uC r k) (P.s r) ∪ ball (P.vC r k) (P.s r) ∪
      thickening (P.w r) (P.conn r k), y ∈ P.tube r := fun y hy => mem_iUnion.mpr ⟨k, hy⟩
  rcases hx with ((hx | hx) | hx) | hx
  · 
    obtain ⟨ζ, hζ, rfl⟩ := hx
    set q : ℂ := pol (P.α + P.sp / 2) (clampAng P.sp P.ψu) with hq
    have hqspine : P.modMap r k q ∈ P.spineSet r := by
      refine mem_iUnion.mpr ⟨k, ?_⟩
      rw [range_modSpine]
      left
      refine ⟨q, ?_, rfl⟩
      simp only [blockSpine, Path.trans_range]
      right; right; left
      exact ⟨0, (polarPath (P.α + P.sp / 2) (1 - P.sp / 2) (clampAng P.sp P.ψu)
        (clampAng P.sp P.ψv)).source⟩
    have hζre : |Complex.arg ζ| < π / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hζ.2.2)
    have hcl := clampAng_mem (by linarith : P.sp ≤ 2) P.ψu
    have hpath : ∀ t, polarPath ‖ζ‖ (P.α + P.sp / 2) (Complex.arg ζ) (clampAng P.sp P.ψu) t ∈
        blockNorm P.α := by
      intro t
      obtain ⟨R, hR, φ, hφ, hpt⟩ := mem_range_polarPath (⟨t, rfl⟩ :
        polarPath ‖ζ‖ (P.α + P.sp / 2) (Complex.arg ζ) (clampAng P.sp P.ψu) t ∈ range _)
      rw [hpt]
      have hR' : P.α < R ∧ R < 1 := by
        rw [mem_uIcc] at hR
        have := hζ.1; have := hζ.2.1; have := hP.sp_le
        rcases hR with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
      have hφ' : |φ| < π / 2 := by
        rw [mem_uIcc] at hφ
        rw [abs_lt]
        have := abs_lt.mp hζre
        rcases hφ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith [hcl.1, hcl.2]
      refine ⟨by rw [norm_pol (by linarith)]; exact hR'.1, by rw [norm_pol (by linarith)]; exact hR'.2,
        ?_⟩
      rw [pol_re]
      exact mul_pos (by linarith) (Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le φ],
        by linarith [le_abs_self φ]⟩)
    have hJ : JoinedIn (P.tube r) (P.modMap r k ζ) (P.modMap r k q) := by
      refine ⟨((polarPath ‖ζ‖ (P.α + P.sp / 2) (Complex.arg ζ) (clampAng P.sp P.ψu)).map
        (P.continuous_modMap r k)).cast (by rw [pol_norm_arg]) rfl, fun t => ?_⟩
      exact hsum _ (Or.inl (Or.inl (Or.inl ⟨_, hpath t, rfl⟩)))
    exact hJ.trans ((joinedIn_spineSet hqspine).mono (spineSet_subset_tube hP hr))
  · 
    have hu : P.uMinus r k ∈ ball (P.uC r k) (P.s r) := by
      rw [mem_ball]; unfold uMinus uC
      rw [dist_modMap' hP hr, Complex.dist_eq, norm_pol_sub_pol_same_angle, hsr,
        show P.α - 3 * P.sp / 4 - P.α = -(3 * P.sp / 4) by ring, abs_neg, abs_of_pos (by positivity)]
      nlinarith
    exact joinedIn_of_convex hP hr (convex_ball _ _)
      (fun y hy => hsum y (Or.inl (Or.inl (Or.inr hy)))) hx hu
      (mem_iUnion.mpr ⟨k, uMinus_mem k⟩)
  · 
    have hvp : P.modMap r k (pol (1 + 3 * P.sp / 4) P.ψv) ∈ P.spineSet r := by
      refine mem_iUnion.mpr ⟨k, ?_⟩
      rw [range_modSpine]
      right
      exact ⟨0, (P.connPath r k).source⟩
    have hv : P.modMap r k (pol (1 + 3 * P.sp / 4) P.ψv) ∈ ball (P.vC r k) (P.s r) := by
      rw [mem_ball]; unfold vC
      rw [dist_modMap' hP hr, Complex.dist_eq, norm_pol_sub_pol_same_angle, hsr,
        show 1 + 3 * P.sp / 4 - 1 = 3 * P.sp / 4 by ring, abs_of_pos (by positivity)]
      nlinarith
    exact joinedIn_of_convex hP hr (convex_ball _ _)
      (fun y hy => hsum y (Or.inl (Or.inr hy))) hx hv hvp
  · 
    obtain ⟨ℓ, hℓ, hxℓ⟩ := mem_thickening_iff.mp hx
    have hℓs : ℓ ∈ P.spineSet r := by
      refine mem_iUnion.mpr ⟨k, ?_⟩
      rw [range_modSpine]; right; exact hℓ
    have hball : ball ℓ (P.w r) ⊆ P.tube r := by
      intro y hy
      exact hsum y (Or.inr (mem_thickening_iff.mpr ⟨ℓ, hℓ, hy⟩))
    exact joinedIn_of_convex hP hr (convex_ball _ _) hball (by rw [mem_ball]; exact hxℓ)
      (mem_ball_self hw) hℓs

 
theorem isPathConnected_tube : IsPathConnected (P.tube r) := by
  rw [isPathConnected_iff]
  refine ⟨⟨P.spine r 0, spine_mem_tube hP hr 0⟩, fun x hx y hy => ?_⟩
  exact (joinedIn_tube hP hr hx).trans (joinedIn_tube hP hr hy).symm

end Conn

end TubeParams

end SupercriticalLQGUniqueness.Uniqueness.Objects.Tube
