import SmallGammaGeodesics.CC.Pullback

/-!
# Zoomed conformal maps and zoom conjugation of pullbacks (track CC, packet CC1; D1.6)

Source: Gwynne–Miller arXiv:1905.00384 ([3]) Lemma 2.6, corrected (ER2) in
`planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D1.6** and D8.

For `z ∈ ℂ` and `r ≠ 0` the **zoom** of `ϕ` at `z` and scale `r` is
`ϕ̃(w) = r⁻¹ (ϕ(z + r w) − ϕ(z))` (`zoomMap`), on the zoomed sets `S̃ = r⁻¹ (S − z)` (`zoomSet`).
The codomain is translated by `ϕ(z)`, not by `z` (erratum ER2 of [3]).

* `IsConfNbhd.zoom`: `(ϕ̃, W̃, Ṽ)` is again a conformal neighbourhood, with image
  `ϕ̃(Ṽ) = r⁻¹ (ϕ(V) − ϕ(z))` (`image_zoomMap_zoomSet`);
* `hasDerivAt_zoomMap`: `ϕ̃'(w) = ϕ'(z + r w)`;
* **zoom conjugation** `confPullFun_zoomMap`: `τ̃ g̃ ((x − z)/r) = τ (g̃((· − ϕ z)/r)) (x)`, and its
  test-function form `IsConfPull.zoom`: the affine pullbacks `testAffinePull r (ϕ z) g̃` and
  `testAffinePull r z τ̃` form a `ϕ`-pullback pair.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Function

namespace SmallGammaGeodesics.CC

open LQGMetric

/-- **The zoomed map** `ϕ̃(w) = r⁻¹ (ϕ(z + r w) − ϕ(z))` (D1.6, with ER2's translation by
`ϕ(z)`). -/
def zoomMap (ϕ : ℂ → ℂ) (z : ℂ) (r : ℝ) (w : ℂ) : ℂ := (r : ℂ)⁻¹ * (ϕ (z + r * w) - ϕ z)

/-- **The zoomed set** `r⁻¹ (S − z) = {w | z + r w ∈ S}`. -/
def zoomSet (z : ℂ) (r : ℝ) (S : Set ℂ) : Set ℂ := (fun w => z + (r : ℂ) * w) ⁻¹' S

section Zoom

variable {ϕ : ℂ → ℂ} {z : ℂ} {r : ℝ} {S W V : Set ℂ}

theorem mem_zoomSet {w : ℂ} : w ∈ zoomSet z r S ↔ z + r * w ∈ S := Iff.rfl

theorem continuous_zoomAff (z : ℂ) (r : ℝ) : Continuous fun w : ℂ => z + (r : ℂ) * w := by
  fun_prop

theorem zoomAff_div (hr : r ≠ 0) (z x : ℂ) : z + (r : ℂ) * ((x - z) / r) = x := by
  have : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  field_simp
  ring

theorem div_zoomAff (hr : r ≠ 0) (z w : ℂ) : (z + (r : ℂ) * w - z) / r = w := by
  have : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  field_simp
  ring

theorem mem_zoomSet_div (hr : r ≠ 0) {x : ℂ} : (x - z) / r ∈ zoomSet z r S ↔ x ∈ S := by
  rw [mem_zoomSet, zoomAff_div hr]

theorem isOpen_zoomSet (hS : IsOpen S) : IsOpen (zoomSet z r S) :=
  hS.preimage (continuous_zoomAff z r)

theorem isBounded_zoomSet (hr : r ≠ 0) (hS : Bornology.IsBounded S) :
    Bornology.IsBounded (zoomSet z r S) := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hS
  refine isBounded_iff_forall_norm_le.2 ⟨(C + ‖z‖) / |r|, fun w hw => ?_⟩
  have hr' : 0 < |r| := abs_pos.2 hr
  rw [le_div_iff₀ hr']
  have h1 : ‖(r : ℂ) * w‖ ≤ C + ‖z‖ := by
    have := hC _ hw
    calc ‖(r : ℂ) * w‖ = ‖(z + r * w) - z‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖z + r * w‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ C + ‖z‖ := by linarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h1
  linarith

theorem closure_zoomSet_subset : closure (zoomSet z r S) ⊆ zoomSet z r (closure S) :=
  (continuous_zoomAff z r).closure_preimage_subset S

/-- `ϕ̃(w) = r⁻¹ (ϕ(z + r w) − ϕ(z))` unfolds to `ϕ(z) + r ϕ̃(w) = ϕ(z + r w)`. -/
theorem zoomAff_zoomMap (hr : r ≠ 0) (w : ℂ) :
    ϕ z + (r : ℂ) * zoomMap ϕ z r w = ϕ (z + r * w) := by
  have : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  rw [zoomMap, ← mul_assoc, mul_inv_cancel₀ this, one_mul, add_sub_cancel]

theorem zoomMap_div (hr : r ≠ 0) (x : ℂ) :
    zoomMap ϕ z r ((x - z) / r) = (ϕ x - ϕ z) / r := by
  rw [zoomMap, zoomAff_div hr, div_eq_inv_mul]

/-- **The derivative of the zoom**: `ϕ̃'(w) = ϕ'(z + r w)`. -/
theorem hasDerivAt_zoomMap (hr : r ≠ 0) {w : ℂ} (hd : DifferentiableAt ℂ ϕ (z + r * w)) :
    HasDerivAt (zoomMap ϕ z r) (deriv ϕ (z + r * w)) w := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hA : HasDerivAt (fun w : ℂ => z + (r : ℂ) * w) r w := by
    simpa using ((hasDerivAt_id w).const_mul (r : ℂ)).const_add z
  have hB := (hd.hasDerivAt.comp w hA).sub_const (ϕ z)
  have hC := hB.const_mul ((r : ℂ)⁻¹)
  have e : (r : ℂ)⁻¹ * (deriv ϕ (z + r * w) * r) = deriv ϕ (z + r * w) := by
    field_simp
  rw [e] at hC
  exact hC

theorem deriv_zoomMap (hr : r ≠ 0) {w : ℂ} (hd : DifferentiableAt ℂ ϕ (z + r * w)) :
    deriv (zoomMap ϕ z r) w = deriv ϕ (z + r * w) :=
  (hasDerivAt_zoomMap hr hd).deriv

theorem differentiableOn_zoomMap (hr : r ≠ 0) (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) :
    DifferentiableOn ℂ (zoomMap ϕ z r) (zoomSet z r W) := fun _ hw =>
  (hasDerivAt_zoomMap hr (hd.differentiableAt (hW.mem_nhds hw))).differentiableAt
    |>.differentiableWithinAt

theorem injOn_zoomMap (hr : r ≠ 0) (hi : InjOn ϕ W) : InjOn (zoomMap ϕ z r) (zoomSet z r W) := by
  intro a ha b hb hab
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have h1 : ϕ (z + r * a) = ϕ (z + r * b) := by
    rw [← zoomAff_zoomMap (ϕ := ϕ) hr a, ← zoomAff_zoomMap (ϕ := ϕ) hr b, hab]
  have h2 := hi ha hb h1
  exact mul_left_cancel₀ hr' (add_left_cancel h2)

/-- `ϕ̃(r⁻¹(S − z)) = r⁻¹(ϕ(S) − ϕ(z))`. -/
theorem image_zoomMap_zoomSet (hr : r ≠ 0) :
    zoomMap ϕ z r '' zoomSet z r S = zoomSet (ϕ z) r (ϕ '' S) := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mem_zoomSet, zoomAff_zoomMap hr]
    exact mem_image_of_mem ϕ hw
  · intro hy
    obtain ⟨v, hv, hvy⟩ := hy
    refine ⟨(v - z) / r, (mem_zoomSet_div hr).2 hv, ?_⟩
    rw [zoomMap_div hr, hvy, div_zoomAff hr]

/-- **The zoomed conformal neighbourhood** (D1.6). -/
theorem IsConfNbhd.zoom (hϕ : IsConfNbhd ϕ W V) (z : ℂ) (hr : r ≠ 0) :
    IsConfNbhd (zoomMap ϕ z r) (zoomSet z r W) (zoomSet z r V) where
  isOpen_W := isOpen_zoomSet hϕ.isOpen_W
  isOpen_V := isOpen_zoomSet hϕ.isOpen_V
  isBounded_V := isBounded_zoomSet hr hϕ.isBounded_V
  closure_subset := closure_zoomSet_subset.trans (preimage_mono hϕ.closure_subset)
  differentiableOn := differentiableOn_zoomMap hr hϕ.isOpen_W hϕ.differentiableOn
  injOn := injOn_zoomMap hr hϕ.injOn

/-- **Zoom conjugation of the pullback** (D1.6): `τ̃ g̃ ((x − z)/r) = τ (g̃((· − ϕ z)/r)) (x)`,
where `τ̃` is the pullback by the zoomed map on the zoomed set. -/
theorem confPullFun_zoomMap (hr : r ≠ 0) (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W)
    (g : ℂ → ℝ) (x : ℂ) :
    confPullFun (zoomMap ϕ z r) (zoomSet z r W) g ((x - z) / r) =
      confPullFun ϕ W (fun y => g ((y - ϕ z) / r)) x := by
  by_cases hx : x ∈ W
  · rw [confPullFun_of_mem ((mem_zoomSet_div hr).2 hx), confPullFun_of_mem hx,
      deriv_zoomMap hr (by rw [zoomAff_div hr]; exact hd.differentiableAt (hW.mem_nhds hx)),
      zoomAff_div hr, zoomMap_div hr]
  · rw [confPullFun_of_notMem (fun h => hx ((mem_zoomSet_div hr).1 h)), confPullFun_of_notMem hx]

/-- `tsupport (g ((· − a)/r)) ⊆ a + r · tsupport g`. -/
private theorem tsupport_comp_div_subset (hr : r ≠ 0) (a : ℂ) {g : ℂ → ℝ}
    (hg : HasCompactSupport g) :
    tsupport (fun y => g ((y - a) / r)) ⊆ (fun u => a + (r : ℂ) * u) '' tsupport g := by
  refine closure_minimal (fun y hy => ⟨(y - a) / r, subset_tsupport g hy, zoomAff_div hr a y⟩) ?_
  exact (hg.isCompact.image (continuous_zoomAff a r)).isClosed

/-- **Zoom conjugation, test functions** (D1.6): if `τ̃` is the pullback of `g̃` by the zoomed map,
then `testAffinePull r z τ̃` is the `ϕ`-pullback of `testAffinePull r (ϕ z) g̃`, which is supported
in `ϕ '' V` when `g̃` is supported in `ϕ̃ '' Ṽ`. -/
theorem IsConfPull.zoom (hr : r ≠ 0) (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W)
    {g τg : TestC} (hτ : IsConfPull (zoomMap ϕ z r) (zoomSet z r W) g τg) :
    IsConfPull ϕ W (testAffinePull r (ϕ z) g) (testAffinePull r z τg) := by
  intro x
  rw [testAffinePull_apply r z hr, hτ, ← confPullFun, confPullFun_zoomMap hr hW hd]
  unfold confPullFun
  congr 1
  funext y
  rw [testAffinePull_apply r (ϕ z) hr]

theorem tsupport_testAffinePull_subset_zoom (hr : r ≠ 0) {g : TestC}
    (hg : tsupport (g : ℂ → ℝ) ⊆ zoomMap ϕ z r '' zoomSet z r V) :
    tsupport (testAffinePull r (ϕ z) g : ℂ → ℝ) ⊆ ϕ '' V := by
  have e : (testAffinePull r (ϕ z) g : ℂ → ℝ) = fun y => g ((y - ϕ z) / r) :=
    funext fun y => testAffinePull_apply r (ϕ z) hr g y
  rw [e]
  refine (tsupport_comp_div_subset hr (ϕ z) g.hasCompactSupport).trans ?_
  rintro _ ⟨u, hu, rfl⟩
  have hu' := hg hu
  rw [image_zoomMap_zoomSet hr] at hu'
  exact hu'

end Zoom

end SmallGammaGeodesics.CC
