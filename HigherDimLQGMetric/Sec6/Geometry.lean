import HigherDimLQGMetric.Sec6.Defs

/-!
# [S] §6: elementary geometry of the trap at `(z, r)`

Packet S6a. The affine homeomorphism `x ↦ r • x + z` between the unit-scale configuration domain and the
annuli at `(z, r)`, and the facts about the sets of the proof of (T): the collector `V_{z,r} = z + rV`,
the trap annulus `A = A_{r,3r}(z)`, its closure inside the configuration domain
`W = A_{r/2,5r}(z) = z + r·A_{1/2,5}`, the ball `B_{4r}(z)`, and the sum of disjoint bumps.

All helpers live in the namespace `HigherDimLQGMetric.S6a`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

namespace S6a

open Set Metric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ### The affine homeomorphism -/

/-- The affine homeomorphism `x ↦ r • x + z` of `ℝ^d` (`r ≠ 0`). -/
def affHomeo (r : ℝ) (hr : r ≠ 0) (z : Rd d) : Rd d ≃ₜ Rd d where
  toFun x := r • x + z
  invFun y := r⁻¹ • (y - z)
  left_inv x := by
    simp only [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hr, one_smul]
  right_inv y := by
    simp only [smul_smul, mul_inv_cancel₀ hr, one_smul, sub_add_cancel]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem coe_affHomeo (r : ℝ) (hr : r ≠ 0) (z : Rd d) :
    ⇑(affHomeo r hr z) = fun x => r • x + z := rfl

theorem affine_pull {r : ℝ} (hr : r ≠ 0) (z y : Rd d) : r • (r⁻¹ • (y - z)) + z = y := by
  rw [smul_smul, mul_inv_cancel₀ hr, one_smul, sub_add_cancel]

theorem pull_affine {r : ℝ} (hr : r ≠ 0) (z x : Rd d) : r⁻¹ • (r • x + z - z) = x := by
  rw [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hr, one_smul]

theorem norm_affine_sub (r : ℝ) (z x : Rd d) : ‖r • x + z - z‖ = |r| * ‖x‖ := by
  rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs]

theorem norm_pull {r : ℝ} (hr : 0 < r) (z y : Rd d) : ‖r⁻¹ • (y - z)‖ = ‖y - z‖ / r := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_eq_div]

/-- Forward image of an open annulus at the origin. -/
theorem affine_mem_ann {r : ℝ} (hr : 0 < r) (z : Rd d) {a b : ℝ} {x : Rd d}
    (hx : x ∈ ann (0 : Rd d) a b) : r • x + z ∈ ann z (r * a) (r * b) := by
  have h1 : a < ‖x - 0‖ := hx.1
  have h2 : ‖x - 0‖ < b := hx.2
  rw [sub_zero] at h1 h2
  change r * a < ‖r • x + z - z‖ ∧ ‖r • x + z - z‖ < r * b
  rw [norm_affine_sub, abs_of_pos hr]
  exact ⟨mul_lt_mul_of_pos_left h1 hr, mul_lt_mul_of_pos_left h2 hr⟩

/-- Pull-back of an open annulus at `z`. -/
theorem pull_mem_ann {r : ℝ} (hr : 0 < r) (z : Rd d) {a b : ℝ} {y : Rd d}
    (hy : y ∈ ann z (r * a) (r * b)) : r⁻¹ • (y - z) ∈ ann (0 : Rd d) a b := by
  have h1 : r * a < ‖y - z‖ := hy.1
  have h2 : ‖y - z‖ < r * b := hy.2
  change a < ‖r⁻¹ • (y - z) - 0‖ ∧ ‖r⁻¹ • (y - z) - 0‖ < b
  rw [sub_zero, norm_pull hr]
  exact ⟨(lt_div_iff₀ hr).2 (by linarith), (div_lt_iff₀ hr).2 (by linarith)⟩

theorem image_ann_affine_eq {r : ℝ} (hr : 0 < r) (z : Rd d) (a b : ℝ) :
    (fun x : Rd d => r • x + z) '' ann (0 : Rd d) a b = ann z (r * a) (r * b) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact affine_mem_ann hr z hx
  · intro hy
    exact ⟨r⁻¹ • (y - z), pull_mem_ann hr z hy, affine_pull hr.ne' z y⟩

/-! ### The sets of the trap at `(z, r)` -/

/-- The unit-scale trap annulus sits in the configuration domain. -/
theorem ann13_subset_cfg : ann (0 : Rd d) 1 3 ⊆ ann (0 : Rd d) (1 / 2) 5 := by
  intro x hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem closure_ann_subset_annCl (z : Rd d) (a b : ℝ) : closure (ann z a b) ⊆ annCl z a b :=
  closure_minimal (ann_subset_annCl z a b) (isClosed_annCl z a b)

theorem annCl13_subset_cfg : annCl (0 : Rd d) 1 3 ⊆ ann (0 : Rd d) (1 / 2) 5 := by
  intro x hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- `A_{r,3r}(z) = z + r·A_{1,3}`. -/
theorem image_ann13 {r : ℝ} (hr : 0 < r) (z : Rd d) :
    (fun x : Rd d => r • x + z) '' ann (0 : Rd d) 1 3 = ann z r (3 * r) := by
  rw [image_ann_affine_eq hr z 1 3, mul_one, mul_comm]

theorem affine_mem_ann13 {r : ℝ} (hr : 0 < r) (z : Rd d) {x : Rd d}
    (hx : x ∈ ann (0 : Rd d) 1 3) : r • x + z ∈ ann z r (3 * r) := by
  rw [← image_ann13 hr z]
  exact ⟨x, hx, rfl⟩

/-- The realization of a configuration point lies in `A_{r/2,5r}(z)`. -/
theorem affine_mem_cfg {r : ℝ} (hr : 0 < r) (z : Rd d) {x : Rd d}
    (hx : x ∈ ann (0 : Rd d) (1 / 2) 5) : r • x + z ∈ ann z (r / 2) (5 * r) := by
  have h := affine_mem_ann hr z hx
  rwa [show r * (1 / 2) = r / 2 by ring, show r * 5 = 5 * r by ring] at h

theorem pull_mem_ann13 {r : ℝ} (hr : 0 < r) (z : Rd d) {y : Rd d} (hy : y ∈ ann z r (3 * r)) :
    r⁻¹ • (y - z) ∈ ann (0 : Rd d) 1 3 := by
  apply pull_mem_ann hr z
  rwa [mul_one, mul_comm]

theorem closure_ann_subset_cfg {r : ℝ} (hr : 0 < r) (z : Rd d) :
    closure (ann z r (3 * r)) ⊆ ann z (r / 2) (5 * r) := by
  intro x hx
  have h := closure_ann_subset_annCl z r (3 * r) hx
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem ann_subset_ball {r : ℝ} (hr : 0 < r) (z : Rd d) : ann z r (3 * r) ⊆ ball z (4 * r) := by
  intro x hx
  rw [mem_ball, dist_eq_norm]
  linarith [hx.2]

theorem closure_ann_subset_ball {r : ℝ} (hr : 0 < r) (z : Rd d) :
    closure (ann z r (3 * r)) ⊆ ball z (4 * r) := by
  intro x hx
  have h := closure_ann_subset_annCl z r (3 * r) hx
  rw [mem_ball, dist_eq_norm]
  linarith [h.2]

/-- The collector at `(z, r)` is open. -/
theorem isOpen_collector {r : ℝ} (hr : r ≠ 0) (z : Rd d) {V : Set (Rd d)} (hV : IsOpen V) :
    IsOpen ((fun x : Rd d => r • x + z) '' V) :=
  (affHomeo r hr z).isOpenMap V hV

/-- `closure (z + rV) = z + r·closure V`. -/
theorem closure_collector {r : ℝ} (hr : r ≠ 0) (z : Rd d) (V : Set (Rd d)) :
    closure ((fun x : Rd d => r • x + z) '' V) = (fun x : Rd d => r • x + z) '' closure V :=
  ((affHomeo r hr z).image_closure V).symm

theorem closure_collector_subset {r : ℝ} (hr : 0 < r) (z : Rd d) {V : Set (Rd d)}
    (hVA : closure V ⊆ ann (0 : Rd d) 1 3) :
    closure ((fun x : Rd d => r • x + z) '' V) ⊆ ann z r (3 * r) := by
  rw [closure_collector hr.ne' z V, ← image_ann13 hr z]
  exact image_mono hVA

/-- `frontier A_{r,3r}(z) = z + r·frontier A_{1,3}`. -/
theorem frontier_ann13 {r : ℝ} (hr : 0 < r) (z : Rd d) :
    frontier (ann z r (3 * r)) = (fun x : Rd d => r • x + z) '' frontier (ann (0 : Rd d) 1 3) := by
  rw [← image_ann13 hr z]
  exact ((affHomeo r hr.ne' z).image_frontier _).symm

/-- A point outside the collector pulls back outside `V`. -/
theorem pull_notMem_of_notMem_collector {r : ℝ} (hr : r ≠ 0) (z : Rd d) {V : Set (Rd d)}
    {y : Rd d} (hy : y ∉ (fun x : Rd d => r • x + z) '' V) : r⁻¹ • (y - z) ∉ V :=
  fun h => hy ⟨_, h, affine_pull hr z y⟩

/-- A function vanishing off `V` gives a bump vanishing off the collector. -/
theorem bumpAt_eq_zero_of_notMem {f : C(Rd d, ℝ)} {V : Set (Rd d)} (hfV : ∀ x, x ∉ V → f x = 0)
    {r : ℝ} (hr : r ≠ 0) (z : Rd d) {y : Rd d} (hy : y ∉ (fun x : Rd d => r • x + z) '' V) :
    bumpAt f r z y = 0 :=
  hfV _ (pull_notMem_of_notMem_collector hr z hy)

/-- **Disjoint bumps.** On `B_{4r}(z)` the sum of the bumps of a family of sites with pairwise disjoint
radius-`4r` balls, all supported in `A_{1,3}` at unit scale, is the bump of the site `(z, j)`. -/
theorem sum_bumpAt_eq {f : ℕ → C(Rd d, ℝ)} {J j : ℕ}
    (hsupp : ∀ i < J, tsupport (f i) ⊆ ann (0 : Rd d) 1 3) {r : ℝ} (hr : 0 < r) {z : Rd d}
    {Z : Finset (Rd d × ℕ)} (hzZ : (z, j) ∈ Z) (hJ : ∀ q ∈ Z, q.2 < J)
    (hdisj : (Z : Set (Rd d × ℕ)).Pairwise
      (fun q q' => Disjoint (ball q.1 (4 * r)) (ball q'.1 (4 * r))))
    {x : Rd d} (hx : x ∈ ball z (4 * r)) :
    (∑ q ∈ Z, bumpAt (f q.2) r q.1) x = bumpAt (f j) r z x := by
  rw [ContinuousMap.sum_apply]
  refine Finset.sum_eq_single (z, j) (fun q hq hne => ?_) (fun h => absurd hzZ h)
  -- elaborate the arguments first (an ascribed type makes unification of `?y.1 =?= z` blow up)
  have hd := hdisj hq hzZ hne
  have hxq : x ∉ ball q.1 (4 * r) := fun h => disjoint_left.1 hd h hx
  have hfar : 4 * r ≤ ‖x - q.1‖ := by
    rw [mem_ball, dist_eq_norm, not_lt] at hxq
    exact hxq
  rw [bumpAt_apply]
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hA := hsupp q.2 (hJ q hq) hmem
  have h2 : ‖r⁻¹ • (x - q.1) - 0‖ < 3 := hA.2
  rw [sub_zero, norm_pull hr, div_lt_iff₀ hr] at h2
  linarith

end S6a

end HigherDimLQGMetric
