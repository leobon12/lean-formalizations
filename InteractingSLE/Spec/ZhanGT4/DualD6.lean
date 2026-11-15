/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualColsFrozen
import InteractingSLE.Spec.ZhanGT4.TwoTime2Clock

/-!
# The two one-sided constructions of `M̃`: the own map of one view is the image chain of the other

Packet PROVE-ZHAN-GT4-A15, sub-steps (a), (b), (d) of `planning/handoffs/PROVE-ZHAN-GT4-A14.md` ("What remains" 1).
Source: Astra, *Follow-up proofs*, §A.1.1–A.1.2 (`source/external/AstraIG1/ig1_followup_proofs.txt` L190–L296, R38):
"For disjoint hulls `K₁(s), K₂(t)`, let `g_j` be the individual hydrodynamic maps and `G` the map of their union. Put
`h₁ = G ∘ g₁⁻¹`, `h₂ = G ∘ g₂⁻¹`, `A_{j,r} = h_j^{(r)}(W_j)`, `B_{m,r} = G^{(r)}(p_m)`."

Curve `1` (driver `W₁`, `W₁ 0 = 0`) and curve `2` (driver `W₂`, `c = W₂ 0`). Two one-sided constructions of the
factors of `M̃` exist (A7–A14):

* the **`s`-view** (curve `1` grows to time `x`, the hull `K₂(y)` frozen, chart `g₂,y = frzChart W₂ y`): A6's `OwnData`
  for `W₁` with image chain `(W', a)`; `h₁` is the reflected own map `ownExt W₁ W' a g₂,y x`, and `h₂` is the image
  chain `g̃_{a(x)} = fwdMap W' (a x) + W'(a x)`;
* the **`t`-view** (curve `2` grows to time `y`, `K₁(x)` frozen), set up after translating both drivers by `−c` so that
  the growing driver `U₂ = W₂ − c` starts at `0` (`OwnData` needs it): frozen hull `K_{U₁}(x)`, `U₁ = W₁ − c`, chart
  `frzChart U₁ x`, image chain `(W'', b)`.

This file proves that **each view's own map is the other view's image chain** near the driver
(`ownExt_eq_imgChain_s`, `ownExt_eq_imgChain_t`): both are holomorphic near the driver and agree on the upper half of a
disc, because both are mapping-out functions of the same image hull (A6's `OwnData.rate`, `IsMapOut.eqOn`), up to the
translation by `c`. Consequently all iterated derivatives agree there (`iterate_deriv_eq_of_eqOn_upper`).

It also contains the pure-analysis tool for (c): **Fubini for a non-negative separately continuous function on a
rectangle** (`intervalIntegral_swap_of_nonneg`), via Tonelli on lower integrals (no joint continuity is needed).

## Main results

* `iterate_deriv_eq_of_eqOn_upper`: holomorphic on a disc about a real point and equal on its upper half ⇒ equal
  iterated derivatives at the centre.
* `isMapOut_add_const`, `fwdMap_sub_const`, `fwdHull_sub_const`, `frzChart_sub_const`: translation.
* `OwnData.eqOn_ownExt_of_isMapOut`: the reflected own map equals every holomorphic mapping-out function of the image
  hull near the driver.
* `ownExt_eq_imgChain_s`, `ownExt_eq_imgChain_t` (sub-step (b)); `sView`, `tView` (the two views as `FrzData`);
  `sView_F_zero/one/succ`, `tView_F_zero/one/succ` (the driver factors `A_{j,k}` agree); `marks_agree` (`B_{m,0}` agree,
  `B_{m,1}` differ by `g₁'(p_m)/g₂'(p_m)`).
* `OwnData.frzRate_eq_schwarz`, `OwnData.re_schwarzFwd_eq_integral`, `sView_rate_eq`, `tView_rate_eq`: each view's
  rate of `log F` is `2∫ A₁₁²A₂₁²/E⁴` of the other view; `viewInt_agree` (the integrand agrees).
* `intervalIntegral_swap_of_nonneg` (Fubini for a non-negative separately continuous function).
* `TwoViewRect` (two-view data on a rectangle), `TwoViewRect.frzLogF_eq` (sub-step (c): the two `log F` agree),
  **`TwoViewRect.ell_sub_ell`** (the two `log M̃` differ by `Σ_m γ_m (log g₁'(p_m) − log g₂'(p_m))`),
  **`TwoViewRect.normLog_eq`** ((D6): the normalised density is the same in both views).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H Hbar IsForwardSol fwdMap fwdHull logDerivFwd)

/-! ### Holomorphic functions agreeing on the upper half of a disc -/

/-- **Two functions holomorphic on a disc about a real point that agree on its upper half have the same iterated
derivatives at the centre** (identity theorem). -/
theorem iterate_deriv_eq_of_eqOn_upper {F₁ F₂ : ℂ → ℂ} {x δ : ℝ} (hδ : 0 < δ)
    (h₁ : DifferentiableOn ℂ F₁ (ball (x : ℂ) δ)) (h₂ : DifferentiableOn ℂ F₂ (ball (x : ℂ) δ))
    (h : EqOn F₁ F₂ (ball (x : ℂ) δ ∩ H)) (k : ℕ) : deriv^[k] F₁ x = deriv^[k] F₂ x := by
  have hE := ConformalImageFull.eqOn_ball_of_eqOn_upper hδ h₁ h₂ h
  have hev : F₁ =ᶠ[𝓝 (x : ℂ)] F₂ :=
    Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds (mem_ball_self hδ)) hE
  exact (eventuallyEq_iterate_deriv hev k).eq_of_nhds

/-- Iterated derivatives commute with a translation of the variable and an added constant. -/
theorem iterate_deriv_comp_add_const (f : ℂ → ℂ) (c C : ℂ) (k : ℕ) (z : ℂ) :
    deriv^[k + 1] (fun w => f (w + c) + C) z = deriv^[k + 1] f (z + c) := by
  have h1 : deriv (fun w => f (w + c) + C) = fun w => deriv f (w + c) := by
    funext w
    rw [deriv_add_const, deriv_comp_add_const f c w]
  have h2 := iteratedDeriv_comp_add_const (n := k) (f := deriv f) (s := c)
  simp only [iteratedDeriv_eq_iterate] at h2
  rw [Function.iterate_succ_apply, h1, h2, ← Function.iterate_succ_apply]

/-! ### Translations -/

/-- A mapping-out function, translated by a real `x` (as `Sec7.isMapOut_translate`, restated to keep the import
closure small). -/
theorem isMapOut_add_const {K : Set ℂ} {g : ℂ → ℂ} (hg : IsMapOut K g) (x : ℝ) :
    IsMapOut ((fun z => z + (x : ℂ)) '' K) (fun w => g (w - x) + x) := by
  have h := hg.comp_affHomeo (r := 1) (x := x) one_pos
  have himg : affHomeo 1 one_pos x '' K = (fun z => z + (x : ℂ)) '' K := by
    congr 1; funext z; exact ConformalImageFull.affHomeo_one_apply x z
  have hfun : (fun w => affHomeo 1 one_pos x (g ((affHomeo 1 one_pos x).symm w))) =
      fun w => g (w - x) + x := by
    funext w
    rw [ConformalImageFull.affHomeo_one_apply, ConformalImageFull.affHomeo_one_symm_apply]
  rwa [himg, hfun] at h

/-- The centered map of the translated driver `W − c`. -/
theorem fwdMap_sub_const (W : ℝ → ℝ) (c σ : ℝ) (z : ℂ) :
    fwdMap (fun u => W u - c) σ z = fwdMap W σ (z + c) := by
  have h := ConformalImageFull.fwdMap_add_const (fun u => W u - c) c σ (z + c)
  have hW : (fun s => (fun u => W u - c) s + c) = W := by funext s; ring
  rw [hW, add_sub_cancel_right] at h
  exact h.symm

/-- The hull of the translated driver `W − c`. -/
theorem fwdHull_sub_const (W : ℝ → ℝ) (c t : ℝ) :
    fwdHull (fun u => W u - c) t = (fun z => z + ((-c : ℝ) : ℂ)) '' fwdHull W t := by
  have h := ConformalImageFull.fwdHull_add_const (fun u => W u - c) c t
  have hW : (fun s => (fun u => W u - c) s + c) = W := by funext s; ring
  rw [hW] at h
  rw [h, Set.image_image]
  have : ∀ z : ℂ, z + (c : ℂ) + ((-c : ℝ) : ℂ) = z := fun z => by push_cast; ring
  simp only [this, Set.image_id']

/-- The hydrodynamic map of the translated driver is the conjugate by the translation. -/
theorem frzChart_sub_const (W : ℝ → ℝ) (c y : ℝ) (z : ℂ) :
    frzChart (fun u => W u - c) y z = frzChart W y (z + c) - c := by
  simp only [frzChart, fwdMap_sub_const]
  push_cast; ring

/-! ### The reflected own map is every holomorphic mapping-out function of the image hull -/

namespace OwnData

variable {W : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : ℝ} {a W' : ℝ → ℝ} (h : OwnData W A φ T a W')
include h

/-- **The reflected own map near the driver is every mapping-out function `R` of the image hull `g_t(A)` that is
holomorphic near the driver**: they agree on a disc about `W_t`. -/
theorem eqOn_ownExt_of_isMapOut {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {R : ℂ → ℂ}
    (hR : IsMapOut ((fun z => fwdMap W t z + W t) '' A) R) {δ : ℝ} (hδ : 0 < δ)
    (hRd : DifferentiableOn ℂ R (ball (W t : ℂ) δ)) :
    ∃ ε > (0 : ℝ), EqOn (ownExt W W' a φ t) R (ball (W t : ℂ) ε) := by
  obtain ⟨ρ, hρ, hcl⟩ := h.exists_clearance
  obtain ⟨hd, -, -, -, -, hFR⟩ := h.ownExt_props ht (hcl t ht)
  set ε := min (ρ / 2) δ with hε
  have hε0 : 0 < ε := lt_min (by positivity) hδ
  have hsub1 : ball (W t : ℂ) ε ⊆ ball (W t : ℂ) (ρ / 2) := ball_subset_ball (min_le_left _ _)
  have hsub2 : ball (W t : ℂ) ε ⊆ ball (W t : ℂ) δ := ball_subset_ball (min_le_right _ _)
  refine ⟨ε, hε0, ConformalImageFull.eqOn_ball_of_eqOn_upper hε0 (hd.mono hsub1) (hRd.mono hsub2) ?_⟩
  intro z hz
  exact hFR R hR ⟨hsub1 hz.1, hz.2⟩

/-- The iterated derivatives of the reflected own map at the driver are those of every holomorphic mapping-out
function of the image hull. -/
theorem iterate_deriv_ownExt_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {R : ℂ → ℂ}
    (hR : IsMapOut ((fun z => fwdMap W t z + W t) '' A) R) {δ : ℝ} (hδ : 0 < δ)
    (hRd : DifferentiableOn ℂ R (ball (W t : ℂ) δ)) (k : ℕ) :
    deriv^[k] (ownExt W W' a φ t) (W t) = deriv^[k] R (W t) := by
  obtain ⟨ε, hε, hEq⟩ := h.eqOn_ownExt_of_isMapOut ht hR hδ hRd
  have hev : ownExt W W' a φ t =ᶠ[𝓝 (W t : ℂ)] R :=
    Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds (mem_ball_self hε)) hEq
  exact (eventuallyEq_iterate_deriv hev k).eq_of_nhds

end OwnData

/-! ### Fubini for a non-negative separately continuous function on a rectangle -/

/-- Clamping both variables into a rectangle. -/
def rectClamp (f : ℝ → ℝ → ℝ) {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (u v : ℝ) : ℝ :=
  f (projIcc 0 X hX u) (projIcc 0 Y hY v)

theorem rectClamp_eq (f : ℝ → ℝ → ℝ) {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) {u v : ℝ} (hu : u ∈ Icc 0 X)
    (hv : v ∈ Icc 0 Y) : rectClamp f hX hY u v = f u v := by
  simp [rectClamp, projIcc_of_mem _ hu, projIcc_of_mem _ hv]

theorem measurable_rectClamp {f : ℝ → ℝ → ℝ} {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hcu : ∀ u ∈ Icc 0 X, ContinuousOn (f u) (Icc 0 Y))
    (hcv : ∀ v ∈ Icc 0 Y, ContinuousOn (fun u => f u v) (Icc 0 X)) :
    Measurable (Function.uncurry (rectClamp f hX hY)) := by
  have hpX : Continuous fun u : ℝ => (projIcc 0 X hX u : ℝ) := continuous_subtype_val.comp continuous_projIcc
  have hpY : Continuous fun v : ℝ => (projIcc 0 Y hY v : ℝ) := continuous_subtype_val.comp continuous_projIcc
  refine measurable_uncurry_of_continuous_of_measurable (fun v => ?_) (fun u => ?_)
  · exact (hcv _ (projIcc 0 Y hY v).2).comp_continuous hpX fun u => (projIcc 0 X hX u).2
  · exact ((hcu _ (projIcc 0 X hX u).2).comp_continuous hpY fun v => (projIcc 0 Y hY v).2).measurable

/-- **Fubini for a non-negative separately continuous function on a rectangle.** If `f ≥ 0` on `[0, X] × [0, Y]` is
continuous in each variable separately and both iterated integrands are integrable, the two iterated integrals agree
(Tonelli on lower integrals; separate continuity gives joint measurability). -/
theorem intervalIntegral_swap_of_nonneg {f : ℝ → ℝ → ℝ} {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hf0 : ∀ u ∈ Icc 0 X, ∀ v ∈ Icc 0 Y, 0 ≤ f u v)
    (hcu : ∀ u ∈ Icc 0 X, ContinuousOn (f u) (Icc 0 Y))
    (hcv : ∀ v ∈ Icc 0 Y, ContinuousOn (fun u => f u v) (Icc 0 X))
    (h1 : IntervalIntegrable (fun u => ∫ v in (0 : ℝ)..Y, f u v) volume 0 X)
    (h2 : IntervalIntegrable (fun v => ∫ u in (0 : ℝ)..X, f u v) volume 0 Y) :
    ∫ u in (0 : ℝ)..X, ∫ v in (0 : ℝ)..Y, f u v = ∫ v in (0 : ℝ)..Y, ∫ u in (0 : ℝ)..X, f u v := by
  set F := rectClamp f hX hY with hFdef
  have hFm := measurable_rectClamp hX hY hcu hcv
  have hpX : Continuous fun u : ℝ => (projIcc 0 X hX u : ℝ) := continuous_subtype_val.comp continuous_projIcc
  have hpY : Continuous fun v : ℝ => (projIcc 0 Y hY v : ℝ) := continuous_subtype_val.comp continuous_projIcc
  have hF0 : ∀ u v, 0 ≤ F u v := fun u v => hf0 _ (projIcc 0 X hX u).2 _ (projIcc 0 Y hY v).2
  have hFu : ∀ u, Continuous (F u) := fun u =>
    (hcu _ (projIcc 0 X hX u).2).comp_continuous hpY fun v => (projIcc 0 Y hY v).2
  have hFv : ∀ v, Continuous fun u => F u v := fun v =>
    (hcv _ (projIcc 0 Y hY v).2).comp_continuous hpX fun u => (projIcc 0 X hX u).2
  set μ := volume.restrict (Ioc (0 : ℝ) X) with hμ
  set ν := volume.restrict (Ioc (0 : ℝ) Y) with hν
  -- replace `f` by `F` and the interval integrals by set integrals
  have eL : ∫ u in (0 : ℝ)..X, ∫ v in (0 : ℝ)..Y, f u v = ∫ u, ∫ v, F u v ∂ν ∂μ := by
    rw [intervalIntegral.integral_of_le hX]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    rw [intervalIntegral.integral_of_le hY]
    refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
    exact (rectClamp_eq f hX hY (Ioc_subset_Icc_self hu) (Ioc_subset_Icc_self hv)).symm
  have eR : ∫ v in (0 : ℝ)..Y, ∫ u in (0 : ℝ)..X, f u v = ∫ v, ∫ u, F u v ∂μ ∂ν := by
    rw [intervalIntegral.integral_of_le hY]
    refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
    rw [intervalIntegral.integral_of_le hX]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    exact (rectClamp_eq f hX hY (Ioc_subset_Icc_self hu) (Ioc_subset_Icc_self hv)).symm
  rw [eL, eR]
  -- inner integrability
  have hiu : ∀ u, Integrable (F u) ν := fun u =>
    ((hFu u).continuousOn.integrableOn_Icc (a := 0) (b := Y)).mono_set Ioc_subset_Icc_self
  have hiv : ∀ v, Integrable (fun u => F u v) μ := fun v =>
    ((hFv v).continuousOn.integrableOn_Icc (a := 0) (b := X)).mono_set Ioc_subset_Icc_self
  -- outer integrability
  have ho1 : Integrable (fun u => ∫ v, F u v ∂ν) μ := by
    have hI := h1.1
    refine hI.congr ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
    show ∫ v in (0 : ℝ)..Y, f u v = ∫ v, F u v ∂ν
    rw [intervalIntegral.integral_of_le hY]
    refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
    exact (rectClamp_eq f hX hY (Ioc_subset_Icc_self hu) (Ioc_subset_Icc_self hv)).symm
  have ho2 : Integrable (fun v => ∫ u, F u v ∂μ) ν := by
    have hI := h2.1
    refine hI.congr ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun v hv => ?_)
    show ∫ u in (0 : ℝ)..X, f u v = ∫ u, F u v ∂μ
    rw [intervalIntegral.integral_of_le hX]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    exact (rectClamp_eq f hX hY (Ioc_subset_Icc_self hu) (Ioc_subset_Icc_self hv)).symm
  have hn1 : 0 ≤ ∫ u, ∫ v, F u v ∂ν ∂μ :=
    integral_nonneg fun u => integral_nonneg fun v => hF0 u v
  have hn2 : 0 ≤ ∫ v, ∫ u, F u v ∂μ ∂ν :=
    integral_nonneg fun v => integral_nonneg fun u => hF0 u v
  rw [← ENNReal.ofReal_eq_ofReal_iff hn1 hn2,
    ofReal_integral_eq_lintegral_ofReal ho1 (Eventually.of_forall fun u => integral_nonneg fun v => hF0 u v),
    ofReal_integral_eq_lintegral_ofReal ho2 (Eventually.of_forall fun v => integral_nonneg fun u => hF0 u v)]
  have e1 : ∀ u, ENNReal.ofReal (∫ v, F u v ∂ν) = ∫⁻ v, ENNReal.ofReal (F u v) ∂ν := fun u =>
    ofReal_integral_eq_lintegral_ofReal (hiu u) (Eventually.of_forall fun v => hF0 u v)
  have e2 : ∀ v, ENNReal.ofReal (∫ u, F u v ∂μ) = ∫⁻ u, ENNReal.ofReal (F u v) ∂μ := fun v =>
    ofReal_integral_eq_lintegral_ofReal (hiv v) (Eventually.of_forall fun u => hF0 u v)
  simp_rw [e1, e2]
  exact lintegral_lintegral_swap (ENNReal.measurable_ofReal.comp hFm).aemeasurable

/-! ### The two views: each own map is the other view's image chain -/

/-- The image of curve `2`'s hull under curve `1`'s hydrodynamic map, written through the `t`-view's translated chart:
`(· + c) '' (g_{U₁,x} '' K_{U₂}(y)) = g_{W₁,x} '' K_{W₂}(y)` with `U_j = W_j − c`. -/
theorem image_add_frzChart_sub_const (W₁ W₂ : ℝ → ℝ) (c x y : ℝ) :
    (fun z => z + (c : ℂ)) '' (frzChart (fun u => W₁ u - c) x '' fwdHull (fun u => W₂ u - c) y) =
      (fun z => fwdMap W₁ x z + W₁ x) '' fwdHull W₂ y := by
  rw [fwdHull_sub_const, Set.image_image, Set.image_image]
  congr 1
  funext k
  rw [frzChart_sub_const]
  simp only [frzChart]
  push_cast; ring_nf

/-- The image of curve `1`'s hull under curve `2`'s translated hydrodynamic map:
`g_{U₂,y} '' K_{U₁}(x) = (· − c) '' (g_{W₂,y} '' K_{W₁}(x))`. -/
theorem image_fwdMap_sub_const (W₁ W₂ : ℝ → ℝ) (c x y : ℝ) :
    (fun z => fwdMap (fun u => W₂ u - c) y z + ((W₂ y - c : ℝ) : ℂ)) '' fwdHull (fun u => W₁ u - c) x =
      (fun z => z + ((-c : ℝ) : ℂ)) '' (frzChart W₂ y '' fwdHull W₁ x) := by
  rw [fwdHull_sub_const, Set.image_image, Set.image_image]
  congr 1
  funext k
  simp only [fwdMap_sub_const, frzChart]
  push_cast; ring_nf

/-- **The `s`-view own map is the `t`-view image chain** (`h₁ = G ∘ g₁⁻¹`, §A.1.1). With `c = W₂ 0`, the `s`-view data
`OwnData W₁ K₂(y) g₂,y S a W'` and the `t`-view data `OwnData (W₂ − c) K_{W₁−c}(x) g_{W₁−c,x} T b W''`, and the
translated tip `W₁ x − c` alive for `W''` up to `b T`, the reflected own map of curve `1` at time `x` equals
`z ↦ g̃''_{b(y)}(z − c) + c` on a disc about `W₁ x`. -/
theorem ownExt_eq_imgChain_s {W₁ W₂ : ℝ → ℝ} {x y S T : ℝ} {a W' b W'' : ℝ → ℝ}
    (hs : OwnData W₁ (fwdHull W₂ y) (frzChart W₂ y) S a W') (hx : x ∈ Icc (0 : ℝ) S)
    (ht : OwnData (fun u => W₂ u - W₂ 0) (fwdHull (fun u => W₁ u - W₂ 0) x) (frzChart (fun u => W₁ u - W₂ 0) x) T b
      W'') (hy : y ∈ Icc (0 : ℝ) T) {v : ℝ → ℂ} (hv : IsForwardSol W'' ((W₁ x - W₂ 0 : ℝ) : ℂ) (b T) v) :
    ∃ ε > (0 : ℝ), EqOn (ownExt W₁ W' a (frzChart W₂ y) x)
      (fun z => fwdMap W'' (b y) (z - W₂ 0) + (W'' (b y) + W₂ 0)) (ball (W₁ x : ℂ) ε) := by
  set c := W₂ 0 with hc
  have hby := ht.toImgData.mapsTo_clock_Icc hy
  have hbT : 0 ≤ b T := (ht.toImgData.mapsTo_clock_Icc ⟨ht.pos.le, le_rfl⟩).1
  -- the mapping-out property
  have hR0 := isMapOut_fwdMap_gen ht.contW' hby.1
  rw [ht.img y hy] at hR0
  have hR := isMapOut_add_const hR0 c
  rw [image_add_frzChart_sub_const] at hR
  have hfun : (fun w => fwdMap W'' (b y) (w - c) + W'' (b y) + c) =
      fun z => fwdMap W'' (b y) (z - c) + (W'' (b y) + c) := by
    funext z; ring
  simp only [hfun] at hR
  -- holomorphy near the driver
  obtain ⟨δ, hδ, hlow, -⟩ := exists_aliveDisc_self hv hbT
  have hd := differentiableOn_fwdMap_aliveDisc ht.contW' hv hδ hlow hby
  have hRd : DifferentiableOn ℂ (fun z => fwdMap W'' (b y) (z - c) + (W'' (b y) + c))
      (ball (W₁ x : ℂ) (aliveRad (b T) δ)) := by
    refine (hd.comp (differentiableOn_id.sub_const _) fun z hz => ?_).add_const _
    rw [mem_ball, dist_eq_norm] at hz ⊢
    convert hz using 2; simp only [id]; push_cast; ring
  exact hs.eqOn_ownExt_of_isMapOut hx hR (aliveRad_pos hδ) hRd

/-- **The `t`-view own map is the `s`-view image chain** (`h₂ = G ∘ g₂⁻¹`), in the translated coordinates of the
`t`-view: with the tip `W₂ y` alive for `W'` up to `a S`, the reflected own map of the translated curve `2` at time `y`
equals `z ↦ g̃'_{a(x)}(z + c) − c` on a disc about `W₂ y − c`. -/
theorem ownExt_eq_imgChain_t {W₁ W₂ : ℝ → ℝ} {x y S T : ℝ} {a W' b W'' : ℝ → ℝ}
    (hs : OwnData W₁ (fwdHull W₂ y) (frzChart W₂ y) S a W') (hx : x ∈ Icc (0 : ℝ) S)
    (ht : OwnData (fun u => W₂ u - W₂ 0) (fwdHull (fun u => W₁ u - W₂ 0) x) (frzChart (fun u => W₁ u - W₂ 0) x) T b
      W'') (hy : y ∈ Icc (0 : ℝ) T) {v : ℝ → ℂ} (hv : IsForwardSol W' ((W₂ y : ℝ) : ℂ) (a S) v) :
    ∃ ε > (0 : ℝ), EqOn (ownExt (fun u => W₂ u - W₂ 0) W'' b (frzChart (fun u => W₁ u - W₂ 0) x) y)
      (fun z => fwdMap W' (a x) (z + W₂ 0) + (W' (a x) - W₂ 0)) (ball ((W₂ y - W₂ 0 : ℝ) : ℂ) ε) := by
  set c := W₂ 0 with hc
  have hax := hs.toImgData.mapsTo_clock_Icc hx
  have haS : 0 ≤ a S := (hs.toImgData.mapsTo_clock_Icc ⟨hs.pos.le, le_rfl⟩).1
  have hR0 := isMapOut_fwdMap_gen hs.contW' hax.1
  rw [hs.img x hx] at hR0
  have hR := isMapOut_add_const hR0 (-c)
  rw [← image_fwdMap_sub_const] at hR
  have hfun : (fun w => fwdMap W' (a x) (w - ((-c : ℝ) : ℂ)) + W' (a x) + ((-c : ℝ) : ℂ)) =
      fun z => fwdMap W' (a x) (z + c) + (W' (a x) - c) := by
    funext z; push_cast; ring_nf
  simp only [hfun] at hR
  obtain ⟨δ, hδ, hlow, -⟩ := exists_aliveDisc_self hv haS
  have hd := differentiableOn_fwdMap_aliveDisc hs.contW' hv hδ hlow hax
  have hRd : DifferentiableOn ℂ (fun z => fwdMap W' (a x) (z + c) + (W' (a x) - c))
      (ball ((W₂ y - c : ℝ) : ℂ) (aliveRad (a S) δ)) := by
    refine (hd.comp (differentiableOn_id.add_const _) fun z hz => ?_).add_const _
    rw [mem_ball, dist_eq_norm] at hz ⊢
    convert hz using 2; simp only [id]; push_cast; ring
  exact ht.eqOn_ownExt_of_isMapOut hy hR (aliveRad_pos hδ) hRd

/-! ### The two views as frozen data, and the driver factors -/

/-- **The `s`-view at height `y`**: curve `1` grows (driver `W₁`), curve `2`'s hull `K₂(y)` is frozen with chart
`g₂,y = frzChart W₂ y`; image data `(as y, Ws y)` (the clock and the image driver at height `y`), reduced charges `r`,
the other source `ζ₀ = W₂ y` and the marks `ζ_m = g₂,y(p_m)`. This is the data of A14's `frzDens`. -/
def sView {n : ℕ} (κ : ℝ) (r : Fin n → ℝ) (W₁ W₂ : ℝ → ℝ) (as Ws : ℝ → ℝ → ℝ) (p : Fin n → ℝ) (y : ℝ) :
    FrzData n :=
  ⟨W₁, Ws y, as y, frzChart W₂ y, κ, r, W₂ y, frzMarks W₂ p y⟩

/-- **The `t`-view at height `x`**, in coordinates translated by `−c`, `c = W₂ 0`: curve `2` grows (driver
`W₂ − c`, starting at `0`), curve `1`'s hull is frozen with chart `frzChart (W₁ − c) x`; image data `(bt x, Wt x)`,
the dual parameter `16/κ`, the dual reduced charges `−(κ/4) r_m`, the other source `W₁ x − c` and the marks
`g₁,x(p_m) − c`. -/
def tView {n : ℕ} (κ : ℝ) (r : Fin n → ℝ) (W₁ W₂ : ℝ → ℝ) (bt Wt : ℝ → ℝ → ℝ) (p : Fin n → ℝ) (x : ℝ) :
    FrzData n :=
  ⟨fun u => W₂ u - W₂ 0, Wt x, bt x, frzChart (fun u => W₁ u - W₂ 0) x, 16 / κ, fun m => -(κ / 4) * r m,
    W₁ x - W₂ 0, frzMarks (fun u => W₁ u - W₂ 0) (fun m => p m - W₂ 0) x⟩

theorem iterate_deriv_eq_of_eqOn_ball {F₁ F₂ : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ} (hε : 0 < ε)
    (h : EqOn F₁ F₂ (ball z₀ ε)) (k : ℕ) : deriv^[k] F₁ z₀ = deriv^[k] F₂ z₀ :=
  (eventuallyEq_iterate_deriv (Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds (mem_ball_self hε)) h) k).eq_of_nhds

section Pointwise

variable {n : ℕ} {κ : ℝ} {r : Fin n → ℝ} {W₁ W₂ : ℝ → ℝ} {as Ws bt Wt : ℝ → ℝ → ℝ} {p : Fin n → ℝ} {x y S T : ℝ}

/-- **`A_{1,0}` agrees** (`s`-view own value = `t`-view image of the other tip, translated). -/
theorem sView_F_zero (hs : OwnData W₁ (fwdHull W₂ y) (frzChart W₂ y) S (as y) (Ws y)) (hx : x ∈ Icc (0 : ℝ) S)
    (ht : OwnData (fun u => W₂ u - W₂ 0) (fwdHull (fun u => W₁ u - W₂ 0) x) (frzChart (fun u => W₁ u - W₂ 0) x) T
      (bt x) (Wt x)) (hy : y ∈ Icc (0 : ℝ) T) {v : ℝ → ℂ}
    (hv : IsForwardSol (Wt x) ((W₁ x - W₂ 0 : ℝ) : ℂ) (bt x T) v) :
    (sView κ r W₁ W₂ as Ws p y).F 0 x (W₁ x) = (tView κ r W₁ W₂ bt Wt p x).A20 y + W₂ 0 := by
  obtain ⟨ε, hε, hEq⟩ := ownExt_eq_imgChain_s hs hx ht hy hv
  have h0 := hEq (mem_ball_self hε)
  simp only [FrzData.F, sView, Function.iterate_zero, id] at h0 ⊢
  rw [h0]
  simp only [FrzData.A20, tView, frzImg, add_re, ofReal_re]
  push_cast; ring

/-- **`A_{1,k}`, `k ≥ 1`, agree**: the `s`-view own derivatives are the derivatives of the `t`-view image chain at the
translated tip. -/
theorem sView_F_succ (hs : OwnData W₁ (fwdHull W₂ y) (frzChart W₂ y) S (as y) (Ws y)) (hx : x ∈ Icc (0 : ℝ) S)
    (ht : OwnData (fun u => W₂ u - W₂ 0) (fwdHull (fun u => W₁ u - W₂ 0) x) (frzChart (fun u => W₁ u - W₂ 0) x) T
      (bt x) (Wt x)) (hy : y ∈ Icc (0 : ℝ) T) {v : ℝ → ℂ}
    (hv : IsForwardSol (Wt x) ((W₁ x - W₂ 0 : ℝ) : ℂ) (bt x T) v) (k : ℕ) :
    deriv^[k + 1] (ownExt W₁ (Ws y) (as y) (frzChart W₂ y) x) (W₁ x) =
      deriv^[k + 1] (fwdMap (Wt x) (bt x y)) ((W₁ x - W₂ 0 : ℝ) : ℂ) := by
  obtain ⟨ε, hε, hEq⟩ := ownExt_eq_imgChain_s hs hx ht hy hv
  rw [iterate_deriv_eq_of_eqOn_ball hε hEq]
  have hfun : (fun z => fwdMap (Wt x) (bt x y) (z - W₂ 0) + (Wt x (bt x y) + W₂ 0 : ℂ)) =
      fun z => fwdMap (Wt x) (bt x y) (z + ((-W₂ 0 : ℝ) : ℂ)) + (Wt x (bt x y) + W₂ 0 : ℂ) := by
    funext z; push_cast; ring_nf
  rw [hfun, iterate_deriv_comp_add_const]
  push_cast; ring_nf

theorem sView_F_one (hs : OwnData W₁ (fwdHull W₂ y) (frzChart W₂ y) S (as y) (Ws y)) (hx : x ∈ Icc (0 : ℝ) S)
    (ht : OwnData (fun u => W₂ u - W₂ 0) (fwdHull (fun u => W₁ u - W₂ 0) x) (frzChart (fun u => W₁ u - W₂ 0) x) T
      (bt x) (Wt x)) (hy : y ∈ Icc (0 : ℝ) T) {v : ℝ → ℂ}
    (hv : IsForwardSol (Wt x) ((W₁ x - W₂ 0 : ℝ) : ℂ) (bt x T) v) :
    (sView κ r W₁ W₂ as Ws p y).F 1 x (W₁ x) = (tView κ r W₁ W₂ bt Wt p x).A21 y := by
  have h := sView_F_succ hs hx ht hy hv 0
  simp only [FrzData.F, sView, FrzData.A21, tView, frzImgD]
  simpa using congrArg Complex.re h

/-- **`A_{2,0}` agrees** (`t`-view own value = `s`-view image of the other tip, translated). -/
theorem tView_F_zero (hs : OwnData W₁ (fwdHull W₂ y) (frzChart W₂ y) S (as y) (Ws y)) (hx : x ∈ Icc (0 : ℝ) S)
    (ht : OwnData (fun u => W₂ u - W₂ 0) (fwdHull (fun u => W₁ u - W₂ 0) x) (frzChart (fun u => W₁ u - W₂ 0) x) T
      (bt x) (Wt x)) (hy : y ∈ Icc (0 : ℝ) T) {v : ℝ → ℂ}
    (hv : IsForwardSol (Ws y) ((W₂ y : ℝ) : ℂ) (as y S) v) :
    (tView κ r W₁ W₂ bt Wt p x).F 0 y (W₂ y - W₂ 0) = (sView κ r W₁ W₂ as Ws p y).A20 x - W₂ 0 := by
  obtain ⟨ε, hε, hEq⟩ := ownExt_eq_imgChain_t hs hx ht hy hv
  have h0 := hEq (mem_ball_self hε)
  simp only [FrzData.F, tView, Function.iterate_zero, id] at h0 ⊢
  rw [h0]
  simp only [FrzData.A20, sView, frzImg, add_re, sub_re, ofReal_re]
  push_cast; ring_nf

theorem tView_F_succ (hs : OwnData W₁ (fwdHull W₂ y) (frzChart W₂ y) S (as y) (Ws y)) (hx : x ∈ Icc (0 : ℝ) S)
    (ht : OwnData (fun u => W₂ u - W₂ 0) (fwdHull (fun u => W₁ u - W₂ 0) x) (frzChart (fun u => W₁ u - W₂ 0) x) T
      (bt x) (Wt x)) (hy : y ∈ Icc (0 : ℝ) T) {v : ℝ → ℂ}
    (hv : IsForwardSol (Ws y) ((W₂ y : ℝ) : ℂ) (as y S) v) (k : ℕ) :
    deriv^[k + 1] (ownExt (fun u => W₂ u - W₂ 0) (Wt x) (bt x) (frzChart (fun u => W₁ u - W₂ 0) x) y)
        ((W₂ y - W₂ 0 : ℝ) : ℂ) = deriv^[k + 1] (fwdMap (Ws y) (as y x)) ((W₂ y : ℝ) : ℂ) := by
  obtain ⟨ε, hε, hEq⟩ := ownExt_eq_imgChain_t hs hx ht hy hv
  rw [iterate_deriv_eq_of_eqOn_ball hε hEq]
  have hfun : (fun z => fwdMap (Ws y) (as y x) (z + W₂ 0) + (Ws y (as y x) - W₂ 0 : ℂ)) =
      fun z => fwdMap (Ws y) (as y x) (z + ((W₂ 0 : ℝ) : ℂ)) + (Ws y (as y x) - W₂ 0 : ℂ) := rfl
  rw [hfun, iterate_deriv_comp_add_const]
  push_cast; ring_nf

theorem tView_F_one (hs : OwnData W₁ (fwdHull W₂ y) (frzChart W₂ y) S (as y) (Ws y)) (hx : x ∈ Icc (0 : ℝ) S)
    (ht : OwnData (fun u => W₂ u - W₂ 0) (fwdHull (fun u => W₁ u - W₂ 0) x) (frzChart (fun u => W₁ u - W₂ 0) x) T
      (bt x) (Wt x)) (hy : y ∈ Icc (0 : ℝ) T) {v : ℝ → ℂ}
    (hv : IsForwardSol (Ws y) ((W₂ y : ℝ) : ℂ) (as y S) v) :
    (tView κ r W₁ W₂ bt Wt p x).F 1 y (W₂ y - W₂ 0) = (sView κ r W₁ W₂ as Ws p y).A21 x := by
  have h := tView_F_succ hs hx ht hy hv 0
  simp only [FrzData.F, tView, FrzData.A21, sView, frzImgD]
  simpa using congrArg Complex.re h

end Pointwise

/-! ### The mark factors: the two factorizations of `G` near a mark -/

/-- **A disc of holomorphy outside the hull around an alive point.** -/
theorem exists_ball_of_isForwardSol {W : ℝ → ℝ} (hW : Continuous W) {p : ℂ} {T : ℝ} (hT : 0 ≤ T) {u : ℝ → ℂ}
    (hu : IsForwardSol W p T u) :
    ∃ ε > (0 : ℝ), (∀ t ∈ Icc (0 : ℝ) T, DifferentiableOn ℂ (fwdMap W t) (ball p ε)) ∧
      ∀ z ∈ ball p ε, z ∈ H → z ∉ fwdHull W T := by
  obtain ⟨δ, hδ, hlow, -⟩ := exists_aliveDisc_self hu hT
  refine ⟨aliveRad T δ, aliveRad_pos hδ, fun t ht => differentiableOn_fwdMap_aliveDisc hW hu hδ hlow ht,
    fun z hz hzH => ?_⟩
  obtain ⟨v, hv, -⟩ := exists_sol_aliveDisc hW hu hδ hlow hz
  exact Ito.notMem_fwdHull_of_isForwardSol hW hzH hT hv

/-- The `t`-view image chain, translated, maps out `g₁,x(K₂(y))` (the `s`-view image hull). -/
theorem isMapOut_imgChain_s {W₁ W₂ : ℝ → ℝ} {x y T : ℝ} {b W'' : ℝ → ℝ}
    (ht : OwnData (fun u => W₂ u - W₂ 0) (fwdHull (fun u => W₁ u - W₂ 0) x) (frzChart (fun u => W₁ u - W₂ 0) x) T b
      W'') (hy : y ∈ Icc (0 : ℝ) T) :
    IsMapOut ((fun z => fwdMap W₁ x z + W₁ x) '' fwdHull W₂ y)
      (fun z => fwdMap W'' (b y) (z - W₂ 0) + (W'' (b y) + W₂ 0)) := by
  have hby := ht.toImgData.mapsTo_clock_Icc hy
  have hR0 := isMapOut_fwdMap_gen ht.contW' hby.1
  rw [ht.img y hy] at hR0
  have hR := isMapOut_add_const hR0 (W₂ 0)
  rw [image_add_frzChart_sub_const] at hR
  have hfun : (fun w => fwdMap W'' (b y) (w - W₂ 0) + W'' (b y) + W₂ 0) =
      fun z => fwdMap W'' (b y) (z - W₂ 0) + (W'' (b y) + W₂ 0) := by
    funext z; ring
  simpa only [hfun] using hR

theorem re_mul_of_im_eq_zero {a b : ℂ} (ha : a.im = 0) (hb : b.im = 0) : (a * b).re = a.re * b.re := by
  simp [mul_re, ha, hb]

section Marks

variable {n : ℕ} {κ : ℝ} {r : Fin n → ℝ} {W₁ W₂ : ℝ → ℝ} {as Ws bt Wt : ℝ → ℝ → ℝ} {p : Fin n → ℝ} {x y S T : ℝ}

/-- **The mark factors agree** (`B_{m,0} = G(p_m)` from both views; `B_{m,1} = G'(p_m)` up to the chart derivative
of the frozen curve: the `s`-view factor is `G'(p_m)/g₂'(p_m)`, the `t`-view one `G'(p_m)/g₁'(p_m)`). Both
factorizations `g̃_{a(x)} ∘ g₂,y` and `(g̃''_{b(y)} ∘ (g₁,x − c)) + c` of the mapping-out function of `K₁(x) ∪ K₂(y)` are
holomorphic near the mark (all four points alive) and agree on its upper half (A6's `OwnData.rate`). -/
theorem marks_agree (hW₁ : Continuous W₁) (hW₂ : Continuous W₂)
    (hs : OwnData W₁ (fwdHull W₂ y) (frzChart W₂ y) S (as y) (Ws y)) (hx : x ∈ Icc (0 : ℝ) S)
    (ht : OwnData (fun u => W₂ u - W₂ 0) (fwdHull (fun u => W₁ u - W₂ 0) x) (frzChart (fun u => W₁ u - W₂ 0) x) T
      (bt x) (Wt x)) (hy : y ∈ Icc (0 : ℝ) T) (m : Fin n) {w₁ w₂ v₃ v₄ : ℝ → ℂ}
    (hp1 : IsForwardSol W₁ ((p m : ℝ) : ℂ) x w₁) (hp2 : IsForwardSol W₂ ((p m : ℝ) : ℂ) y w₂)
    (hps : IsForwardSol (Ws y) ((frzMarks W₂ p y m : ℝ) : ℂ) (as y x) v₃)
    (hpt : IsForwardSol (Wt x) ((frzMarks (fun u => W₁ u - W₂ 0) (fun m => p m - W₂ 0) x m : ℝ) : ℂ) (bt x y) v₄) :
    (sView κ r W₁ W₂ as Ws p y).B0 x m = (tView κ r W₁ W₂ bt Wt p x).B0 y m + W₂ 0 ∧
      (sView κ r W₁ W₂ as Ws p y).B1 x m * (deriv (fwdMap W₂ y) (p m)).re =
        (tView κ r W₁ W₂ bt Wt p x).B1 y m * (deriv (fwdMap W₁ x) (p m)).re := by
  set c := W₂ 0 with hc
  set ζs : ℝ := frzMarks W₂ p y m with hζs
  set ζt : ℝ := frzMarks (fun u => W₁ u - c) (fun m => p m - c) x m with hζt
  have hax := hs.toImgData.mapsTo_clock_Icc hx
  have hby := ht.toImgData.mapsTo_clock_Icc hy
  have hax' : as y x ∈ Icc (0 : ℝ) (as y x) := ⟨hax.1, le_rfl⟩
  have hby' : bt x y ∈ Icc (0 : ℝ) (bt x y) := ⟨hby.1, le_rfl⟩
  have hxx : x ∈ Icc (0 : ℝ) x := ⟨hx.1, le_rfl⟩
  have hyy : y ∈ Icc (0 : ℝ) y := ⟨hy.1, le_rfl⟩
  -- the charts at the mark are real
  have hg2 : frzChart W₂ y (p m) = (ζs : ℂ) := by
    have him := fwdMap_real_im hW₂ hp2 hyy
    apply Complex.ext <;> simp [frzChart, hζs, frzMarks, him]
  have hg1 : frzChart W₁ x (p m) - c = (ζt : ℂ) := by
    have him := fwdMap_real_im hW₁ hp1 hxx
    have e : fwdMap (fun u => W₁ u - c) x ((p m : ℂ) - (c : ℂ)) = fwdMap W₁ x (p m) := by
      rw [fwdMap_sub_const]; ring_nf
    apply Complex.ext
    · simp [frzChart, hζt, frzMarks, e]; ring
    · simp [frzChart, hζt, frzMarks, him, e]
  -- the discs
  obtain ⟨ε₁, hε₁, hd₁, hK₁⟩ := exists_ball_of_isForwardSol hW₁ hx.1 hp1
  obtain ⟨ε₂, hε₂, hd₂, hK₂⟩ := exists_ball_of_isForwardSol hW₂ hy.1 hp2
  obtain ⟨ε₃, hε₃, hd₃, -⟩ := exists_ball_of_isForwardSol hs.contW' hax.1 hps
  obtain ⟨ε₄, hε₄, hd₄, -⟩ := exists_ball_of_isForwardSol ht.contW' hby.1 hpt
  have hg₂d : DifferentiableOn ℂ (frzChart W₂ y) (ball ((p m : ℝ) : ℂ) ε₂) := (hd₂ y hyy).add_const _
  have hg₁d : DifferentiableOn ℂ (fun z => frzChart W₁ x z - c) (ball ((p m : ℝ) : ℂ) ε₁) :=
    ((hd₁ x hxx).add_const _).sub_const _
  set U := (ball ((p m : ℝ) : ℂ) ε₁ ∩ (fun z => frzChart W₁ x z - c) ⁻¹' ball (ζt : ℂ) ε₄) ∩
    (ball ((p m : ℝ) : ℂ) ε₂ ∩ frzChart W₂ y ⁻¹' ball (ζs : ℂ) ε₃) with hU
  have hUo : IsOpen U :=
    (hg₁d.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_ball).inter
      (hg₂d.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_ball)
  have hpU : ((p m : ℝ) : ℂ) ∈ U := by
    refine ⟨⟨mem_ball_self hε₁, ?_⟩, ⟨mem_ball_self hε₂, ?_⟩⟩
    · show frzChart W₁ x (p m) - c ∈ ball (ζt : ℂ) ε₄; rw [hg1]; exact mem_ball_self hε₄
    · show frzChart W₂ y (p m) ∈ ball (ζs : ℂ) ε₃; rw [hg2]; exact mem_ball_self hε₃
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hUo _ hpU
  -- the two factorizations
  have hΦsd : DifferentiableOn ℂ (fun z => fwdMap (Ws y) (as y x) (frzChart W₂ y z) + Ws y (as y x))
      (ball ((p m : ℝ) : ℂ) ε) :=
    ((hd₃ _ hax').comp (hg₂d.mono fun z hz => (hεU hz).2.1) fun z hz => (hεU hz).2.2).add_const _
  have hΦtd : DifferentiableOn ℂ (fun z => fwdMap (Wt x) (bt x y) (frzChart W₁ x z - c) + (Wt x (bt x y) + c))
      (ball ((p m : ℝ) : ℂ) ε) :=
    ((hd₄ _ hby').comp (hg₁d.mono fun z hz => (hεU hz).1.1) fun z hz => (hεU hz).1.2).add_const _
  have hR := isMapOut_imgChain_s ht hy
  have hrate := (hs.rate x hx _ hR).1
  have hEq : EqOn (fun z => fwdMap (Ws y) (as y x) (frzChart W₂ y z) + Ws y (as y x))
      (fun z => fwdMap (Wt x) (bt x y) (frzChart W₁ x z - c) + (Wt x (bt x y) + c))
      (ball ((p m : ℝ) : ℂ) ε ∩ H) := by
    intro z hz
    have hzU := hεU hz.1
    have hz1 := hK₁ z hzU.1.1 hz.2
    have hz2 := hK₂ z hzU.2.1 hz.2
    have := hrate z ⟨hz.2, fun h => h.elim hz2 hz1⟩
    simp only
    rw [this]
    simp only [frzChart]
    rfl
  have e0 := iterate_deriv_eq_of_eqOn_upper hε hΦsd hΦtd hEq 0
  have e1 := iterate_deriv_eq_of_eqOn_upper hε hΦsd hΦtd hEq 1
  simp only [Function.iterate_zero, id, Function.iterate_one] at e0 e1
  refine ⟨?_, ?_⟩
  · -- values
    rw [hg2, hg1] at e0
    have := congrArg Complex.re e0
    simp only [add_re, ofReal_re] at this
    simp only [FrzData.B0, sView, tView, frzImg, ← hζs]
    linarith
  · -- derivatives (chain rule)
    have hpm₂ : ball ((p m : ℝ) : ℂ) ε₂ ∈ 𝓝 ((p m : ℝ) : ℂ) := ball_mem_nhds _ hε₂
    have hpm₁ : ball ((p m : ℝ) : ℂ) ε₁ ∈ 𝓝 ((p m : ℝ) : ℂ) := ball_mem_nhds _ hε₁
    have Dg₂ : HasDerivAt (frzChart W₂ y) (deriv (fwdMap W₂ y) (p m)) (p m) :=
      (((hd₂ y hyy).differentiableAt hpm₂).hasDerivAt).add_const _
    have Dg₁ : HasDerivAt (fun z => frzChart W₁ x z - c) (deriv (fwdMap W₁ x) (p m)) (p m) :=
      ((((hd₁ x hxx).differentiableAt hpm₁).hasDerivAt).add_const _).sub_const _
    have Df₃ : HasDerivAt (fwdMap (Ws y) (as y x)) (deriv (fwdMap (Ws y) (as y x)) (ζs : ℂ))
        (frzChart W₂ y (p m)) := by
      rw [hg2]
      exact ((hd₃ _ hax').differentiableAt (ball_mem_nhds _ hε₃)).hasDerivAt
    have Df₄ : HasDerivAt (fwdMap (Wt x) (bt x y)) (deriv (fwdMap (Wt x) (bt x y)) (ζt : ℂ))
        ((fun z => frzChart W₁ x z - c) (p m)) := by
      simp only; rw [hg1]
      exact ((hd₄ _ hby').differentiableAt (ball_mem_nhds _ hε₄)).hasDerivAt
    have hDs := ((Df₃.comp ((p m : ℝ) : ℂ) Dg₂).add_const (Ws y (as y x) : ℂ)).deriv
    have hDt := ((Df₄.comp ((p m : ℝ) : ℂ) Dg₁).add_const (Wt x (bt x y) + c : ℂ)).deriv
    simp only [Function.comp_def] at hDs hDt
    rw [hDs, hDt] at e1
    have := congrArg Complex.re e1
    rw [re_mul_of_im_eq_zero (deriv_fwdMap_real hs.contW' hps hax').1 (deriv_fwdMap_real hW₂ hp2 hyy).1,
      re_mul_of_im_eq_zero (deriv_fwdMap_real ht.contW' hpt hby').1 (deriv_fwdMap_real hW₁ hp1 hxx).1] at this
    simpa only [FrzData.B1, sView, tView, frzImgD, ← hζs, ← hζt] using this

end Marks

/-! ### The Schwarzian rate of one view is the integral of the other view's `2A²A²/E⁴` -/

namespace OwnData

variable {W : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : ℝ} {a W' : ℝ → ℝ} (h : OwnData W A φ T a W')
include h

/-- **The own-time rate of `log F` is `−⅙` of a Schwarzian** ((D5)): if the reflected own map at the driver has the
derivatives of order `1, 2, 3` of a Loewner map `f_τ` at a real alive point `ζ`, then
`¼(A₂/A₁)² − ⅙A₃/A₁ = −⅙ Re 𝒮f_τ(ζ)`. -/
theorem frzRate_eq_schwarz {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {V : ℝ → ℝ} (hV : Continuous V) {ζ τ τ₀ : ℝ}
    {v : ℝ → ℂ} (hv : IsForwardSol V ζ τ₀ v) (hτ : τ ∈ Icc (0 : ℝ) τ₀)
    (hd : ∀ k : ℕ, deriv^[k + 1] (ownExt W W' a φ t) (W t) = deriv^[k + 1] (fwdMap V τ) ζ) :
    frzRate W W' a φ t = -(1 / 6) * (schwarzFwd V τ ζ).re := by
  have hτ₀ : 0 ≤ τ₀ := hτ.1.trans hτ.2
  obtain ⟨δ, hδ, hlow, hζ⟩ := exists_aliveDisc_self hv hτ₀
  rw [schwarzFwd_eq_aliveDisc hV hv hδ hlow hζ hτ]
  have e : ∀ k : ℕ, deriv^[k + 1] (fwdMap V τ) ζ = ((frzA W W' a φ (k + 1) t : ℝ) : ℂ) := fun k => by
    rw [← hd k]
    apply Complex.ext
    · simp [frzA]
    · rw [ofReal_im]; exact h.iterDeriv_driver_im ht (k + 1)
  have e1 := e 0
  have e2 := e 1
  have e3 := e 2
  simp only [Function.iterate_succ_apply', Function.iterate_zero, id] at e1 e2 e3
  rw [e1, e2, e3]
  have h1 : frzA W W' a φ 1 t ≠ 0 := (h.frzA_one_pos ht).ne'
  have hre : (((frzA W W' a φ 3 t : ℝ) : ℂ) / (frzA W W' a φ 1 t : ℂ) -
      3 / 2 * (((frzA W W' a φ 2 t : ℝ) : ℂ) / (frzA W W' a φ 1 t : ℂ)) ^ 2).re =
      frzA W W' a φ 3 t / frzA W W' a φ 1 t - 3 / 2 * (frzA W W' a φ 2 t / frzA W W' a φ 1 t) ^ 2 := by
    rw [show (((frzA W W' a φ 3 t : ℝ) : ℂ) / (frzA W W' a φ 1 t : ℂ) -
      3 / 2 * (((frzA W W' a φ 2 t : ℝ) : ℂ) / (frzA W W' a φ 1 t : ℂ)) ^ 2) =
      ((frzA W W' a φ 3 t / frzA W W' a φ 1 t - 3 / 2 * (frzA W W' a φ 2 t / frzA W W' a φ 1 t) ^ 2 : ℝ) : ℂ) by
        push_cast; ring]
    exact ofReal_re _
  rw [hre, frzRate]
  ring

/-- **(D4)–(D5) in real form**: for a point `ζ` alive for the image chain on `[0, a(T)]` (the frozen tip),
`Re 𝒮g̃_{a(t)}(ζ) = −12 ∫₀ᵗ A_{j,1}² A_{k,1}²/E⁴` with `E = A_{k,0} − A_{j,0}` (A4's `schwarzFwd_eq_integral`). -/
theorem re_schwarzFwd_eq_integral {ζ : ℝ} {v : ℝ → ℂ} (hv : IsForwardSol W' ζ (a T) v) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    (schwarzFwd W' (a t) ζ).re = -12 * ∫ s in (0 : ℝ)..t,
      frzA W W' a φ 1 s ^ 2 * frzImgD W' a ζ s ^ 2 / (frzImg W' a ζ s - frzA W W' a φ 0 s) ^ 4 := by
  rw [h.schwarzFwd_eq_integral hv ht]
  have haT : 0 ≤ a T := (h.mapsTo_clock ⟨h.pos.le, le_rfl⟩).1
  obtain ⟨δ, hδ, hlow, hζ⟩ := exists_aliveDisc_self hv haT
  have hcongr : ∀ s ∈ uIcc (0 : ℝ) t, (((deriv (ownExt W W' a φ s) (W s)).re ^ 2 : ℝ) : ℂ) *
      -(12 * Complex.exp (logDerivFwd W' (a s) ζ) ^ 2 / fwdMap W' (a s) ζ ^ 4) =
      ((-12 * (frzA W W' a φ 1 s ^ 2 * frzImgD W' a ζ s ^ 2 /
        (frzImg W' a ζ s - frzA W W' a φ 0 s) ^ 4) : ℝ) : ℂ) := by
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
    have has := h.mapsTo_clock hsT
    rw [← deriv_fwdMap_aliveDisc h.contW' hv hδ hlow hζ has]
    have hd := deriv_fwdMap_real h.contW' hv has
    have hf := fwdMap_real_im h.contW' hv has
    have eD : deriv (fwdMap W' (a s)) (ζ : ℂ) = ((frzImgD W' a ζ s : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [frzImgD, hd.1]
    have eF : fwdMap W' (a s) (ζ : ℂ) = ((frzImg W' a ζ s - frzA W W' a φ 0 s : ℝ) : ℂ) := by
      rw [h.frzA_zero hsT]
      apply Complex.ext <;> simp [frzImg, hf]
    rw [eD, eF]
    simp only [frzA, Function.iterate_one]
    push_cast; ring
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_ofReal, ofReal_re,
    intervalIntegral.integral_const_mul]

end OwnData

section Rates

variable {n : ℕ} {κ : ℝ} {r : Fin n → ℝ} {W₁ W₂ : ℝ → ℝ} {as Ws bt Wt : ℝ → ℝ → ℝ} {p : Fin n → ℝ} {x y S T : ℝ}

/-- **The `s`-view rate at `(x, y)` is `2∫₀ʸ A₁₁²A₂₁²/E⁴` of the `t`-view at height `x`.** -/
theorem sView_rate_eq (hs : OwnData W₁ (fwdHull W₂ y) (frzChart W₂ y) S (as y) (Ws y)) (hx : x ∈ Icc (0 : ℝ) S)
    (ht : OwnData (fun u => W₂ u - W₂ 0) (fwdHull (fun u => W₁ u - W₂ 0) x) (frzChart (fun u => W₁ u - W₂ 0) x) T
      (bt x) (Wt x)) (hy : y ∈ Icc (0 : ℝ) T) {v : ℝ → ℂ}
    (hv : IsForwardSol (Wt x) ((W₁ x - W₂ 0 : ℝ) : ℂ) (bt x T) v) :
    frzRate W₁ (Ws y) (as y) (frzChart W₂ y) x = 2 * ∫ s in (0 : ℝ)..y,
      (tView κ r W₁ W₂ bt Wt p x).A 1 s ^ 2 * (tView κ r W₁ W₂ bt Wt p x).A21 s ^ 2 /
        ((tView κ r W₁ W₂ bt Wt p x).A20 s - (tView κ r W₁ W₂ bt Wt p x).A 0 s) ^ 4 := by
  have hby := ht.toImgData.mapsTo_clock_Icc hy
  rw [hs.frzRate_eq_schwarz hx ht.contW' hv hby (sView_F_succ hs hx ht hy hv),
    ht.re_schwarzFwd_eq_integral hv hy]
  simp only [FrzData.A, FrzData.A21, FrzData.A20, tView]
  ring

/-- **The `t`-view rate at `(x, y)` is `2∫₀ˣ A₁₁²A₂₁²/E⁴` of the `s`-view at height `y`.** -/
theorem tView_rate_eq (hs : OwnData W₁ (fwdHull W₂ y) (frzChart W₂ y) S (as y) (Ws y)) (hx : x ∈ Icc (0 : ℝ) S)
    (ht : OwnData (fun u => W₂ u - W₂ 0) (fwdHull (fun u => W₁ u - W₂ 0) x) (frzChart (fun u => W₁ u - W₂ 0) x) T
      (bt x) (Wt x)) (hy : y ∈ Icc (0 : ℝ) T) {v : ℝ → ℂ}
    (hv : IsForwardSol (Ws y) ((W₂ y : ℝ) : ℂ) (as y S) v) :
    frzRate (fun u => W₂ u - W₂ 0) (Wt x) (bt x) (frzChart (fun u => W₁ u - W₂ 0) x) y = 2 * ∫ s in (0 : ℝ)..x,
      (sView κ r W₁ W₂ as Ws p y).A 1 s ^ 2 * (sView κ r W₁ W₂ as Ws p y).A21 s ^ 2 /
        ((sView κ r W₁ W₂ as Ws p y).A20 s - (sView κ r W₁ W₂ as Ws p y).A 0 s) ^ 4 := by
  have hax := hs.toImgData.mapsTo_clock_Icc hx
  have hd : ∀ k : ℕ, deriv^[k + 1] (ownExt (fun u => W₂ u - W₂ 0) (Wt x) (bt x)
      (frzChart (fun u => W₁ u - W₂ 0) x) y) ((fun u => W₂ u - W₂ 0) y) =
      deriv^[k + 1] (fwdMap (Ws y) (as y x)) ((W₂ y : ℝ) : ℂ) := fun k => by
    have := tView_F_succ hs hx ht hy hv k
    simpa using this
  rw [ht.frzRate_eq_schwarz hy hs.contW' hv hax hd, hs.re_schwarzFwd_eq_integral hv hx]
  simp only [FrzData.A, FrzData.A21, FrzData.A20, sView]
  ring

end Rates

/-! ### The integrand `A₁₁²A₂₁²/E⁴` and the agreement of `log F` -/

/-- The integrand `A_{1,1}² A_{2,1}²/E⁴` of (D4) in a view: `frzA … 1 t² · g̃'(ζ)² / (g̃(ζ) − A_{j,0})⁴`. -/
def viewInt (W W' a : ℝ → ℝ) (φ : ℂ → ℂ) (ζ : ℝ) (t : ℝ) : ℝ :=
  frzA W W' a φ 1 t ^ 2 * frzImgD W' a ζ t ^ 2 / (frzImg W' a ζ t - frzA W W' a φ 0 t) ^ 4

theorem viewInt_nonneg (W W' a : ℝ → ℝ) (φ : ℂ → ℂ) (ζ t : ℝ) : 0 ≤ viewInt W W' a φ ζ t := by
  unfold viewInt; positivity

theorem OwnData.continuousOn_viewInt {W : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : ℝ} {a W' : ℝ → ℝ}
    (h : OwnData W A φ T a W') {ζ : ℝ} {v : ℝ → ℂ} (hv : IsForwardSol W' ζ (a T) v) :
    ContinuousOn (viewInt W W' a φ ζ) (Icc 0 T) := by
  have h1 := h.continuousOn_frzA 1
  have h0 := h.continuousOn_frzA 0
  have hI : ContinuousOn (frzImg W' a ζ) (Icc 0 T) := fun t ht =>
    (h.hasDerivWithinAt_frzImg hv ht).continuousWithinAt
  have hD : ContinuousOn (frzImgD W' a ζ) (Icc 0 T) := fun t ht =>
    (h.hasDerivWithinAt_frzImgD hv ht).continuousWithinAt
  exact ((h1.pow 2).mul (hD.pow 2)).div ((hI.sub h0).pow 4) fun t ht =>
    pow_ne_zero 4 (h.frzImg_sub_ne_zero hv ht)

section Integrand

variable {W₁ W₂ : ℝ → ℝ} {as Ws bt Wt : ℝ → ℝ → ℝ} {x y S T : ℝ}

/-- **The integrand of (D4) is the same in both views**: `A_{1,1}`, `A_{2,1}` agree and `E` changes sign. -/
theorem viewInt_agree (hs : OwnData W₁ (fwdHull W₂ y) (frzChart W₂ y) S (as y) (Ws y)) (hx : x ∈ Icc (0 : ℝ) S)
    (ht : OwnData (fun u => W₂ u - W₂ 0) (fwdHull (fun u => W₁ u - W₂ 0) x) (frzChart (fun u => W₁ u - W₂ 0) x) T
      (bt x) (Wt x)) (hy : y ∈ Icc (0 : ℝ) T) {v₁ v₂ : ℝ → ℂ}
    (hv₁ : IsForwardSol (Wt x) ((W₁ x - W₂ 0 : ℝ) : ℂ) (bt x T) v₁)
    (hv₂ : IsForwardSol (Ws y) ((W₂ y : ℝ) : ℂ) (as y S) v₂) :
    viewInt W₁ (Ws y) (as y) (frzChart W₂ y) (W₂ y) x =
      viewInt (fun u => W₂ u - W₂ 0) (Wt x) (bt x) (frzChart (fun u => W₁ u - W₂ 0) x) (W₁ x - W₂ 0) y := by
  have a1 := sView_F_one (n := 0) (κ := 1) (r := fun _ => 0) (p := fun _ => 0) hs hx ht hy hv₁
  have a0 := sView_F_zero (n := 0) (κ := 1) (r := fun _ => 0) (p := fun _ => 0) hs hx ht hy hv₁
  have b1 := tView_F_one (n := 0) (κ := 1) (r := fun _ => 0) (p := fun _ => 0) hs hx ht hy hv₂
  have b0 := tView_F_zero (n := 0) (κ := 1) (r := fun _ => 0) (p := fun _ => 0) hs hx ht hy hv₂
  simp only [FrzData.F, FrzData.A21, FrzData.A20, sView, tView] at a1 a0 b1 b0
  have a1' : frzA W₁ (Ws y) (as y) (frzChart W₂ y) 1 x = frzImgD (Wt x) (bt x) (W₁ x - W₂ 0) y := a1
  have a0' : frzA W₁ (Ws y) (as y) (frzChart W₂ y) 0 x = frzImg (Wt x) (bt x) (W₁ x - W₂ 0) y + W₂ 0 := a0
  have b1' : frzA (fun u => W₂ u - W₂ 0) (Wt x) (bt x) (frzChart (fun u => W₁ u - W₂ 0) x) 1 y =
      frzImgD (Ws y) (as y) (W₂ y) x := b1
  have b0' : frzA (fun u => W₂ u - W₂ 0) (Wt x) (bt x) (frzChart (fun u => W₁ u - W₂ 0) x) 0 y =
      frzImg (Ws y) (as y) (W₂ y) x - W₂ 0 := b0
  unfold viewInt
  rw [a1', a0', b1', b0']
  ring

end Integrand

/-! ### The two views on a rectangle, and the agreement of `log F` ((D4)–(D5), sub-step (c)) -/

/-- **Two-view data on the rectangle `[0, X] × [0, Y]`**: for every height `v ≤ Y` of curve `2`, `s`-view image data
`(as v, Ws v)` of curve `1` up to a horizon `≥ X`, with the frozen tip `W₂ v` alive for the image chain; for every
height `u ≤ X` of curve `1`, `t`-view image data `(bt u, Wt u)` of the translated curve `2` up to a horizon `≥ Y`, with
the translated frozen tip `W₁ u − W₂ 0` alive. (A9's `TwoCurveD9.alive₀` in each view.) -/
structure TwoViewRect (W₁ W₂ : ℝ → ℝ) (X Y : ℝ) (as Ws bt Wt : ℝ → ℝ → ℝ) : Prop where
  nonneg_X : 0 ≤ X
  nonneg_Y : 0 ≤ Y
  sOwn : ∀ v ∈ Icc (0 : ℝ) Y, ∃ S, X ≤ S ∧ OwnData W₁ (fwdHull W₂ v) (frzChart W₂ v) S (as v) (Ws v) ∧
    ∃ w, IsForwardSol (Ws v) ((W₂ v : ℝ) : ℂ) (as v S) w
  tOwn : ∀ u ∈ Icc (0 : ℝ) X, ∃ T, Y ≤ T ∧ OwnData (fun s => W₂ s - W₂ 0) (fwdHull (fun s => W₁ s - W₂ 0) u)
    (frzChart (fun s => W₁ s - W₂ 0) u) T (bt u) (Wt u) ∧ ∃ w, IsForwardSol (Wt u) ((W₁ u - W₂ 0 : ℝ) : ℂ) (bt u T) w

namespace TwoViewRect

variable {W₁ W₂ : ℝ → ℝ} {X Y : ℝ} {as Ws bt Wt : ℝ → ℝ → ℝ} (h : TwoViewRect W₁ W₂ X Y as Ws bt Wt)
include h

/-- The `s`-view integrand of (D4) at `(u, v)` equals the `t`-view one. -/
theorem viewInt_agree' {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) X) (hv : v ∈ Icc (0 : ℝ) Y) :
    viewInt W₁ (Ws v) (as v) (frzChart W₂ v) (W₂ v) u =
      viewInt (fun s => W₂ s - W₂ 0) (Wt u) (bt u) (frzChart (fun s => W₁ s - W₂ 0) u) (W₁ u - W₂ 0) v := by
  obtain ⟨S, hXS, hs, w, hw⟩ := h.sOwn v hv
  obtain ⟨T, hYT, ht, w', hw'⟩ := h.tOwn u hu
  exact viewInt_agree hs ⟨hu.1, hu.2.trans hXS⟩ ht ⟨hv.1, hv.2.trans hYT⟩ hw' hw

/-- **Sub-step (c): the two one-sided `log F` agree** at the corner of the rectangle: the `s`-view
`∫₀ˣ (¼(A₂/A₁)² − ⅙A₃/A₁)` (curve `1`'s own time, height `Y`) equals the `t`-view `∫₀ʸ (…)` (curve `2`'s own time,
height `X`); both are `2∫₀ˣ∫₀ʸ A₁₁²A₂₁²/E⁴`. -/
theorem frzLogF_eq :
    frzLogF W₁ (Ws Y) (as Y) (frzChart W₂ Y) X =
      frzLogF (fun s => W₂ s - W₂ 0) (Wt X) (bt X) (frzChart (fun s => W₁ s - W₂ 0) X) Y := by
  have hX := h.nonneg_X
  have hY := h.nonneg_Y
  obtain ⟨S, hXS, hsY, w, hw⟩ := h.sOwn Y ⟨hY, le_rfl⟩
  obtain ⟨T, hYT, htX, w', hw'⟩ := h.tOwn X ⟨hX, le_rfl⟩
  set f : ℝ → ℝ → ℝ := fun u v => viewInt W₁ (Ws v) (as v) (frzChart W₂ v) (W₂ v) u with hf
  -- the `s`-view rate as an integral of `f`
  have hrs : ∀ u ∈ Icc (0 : ℝ) X, frzRate W₁ (Ws Y) (as Y) (frzChart W₂ Y) u =
      2 * ∫ v in (0 : ℝ)..Y, f u v := by
    intro u hu
    obtain ⟨T', hYT', ht', w₁, hw₁⟩ := h.tOwn u hu
    have e := sView_rate_eq (n := 0) (κ := 1) (r := fun _ => 0) (p := fun _ => 0) hsY ⟨hu.1, hu.2.trans hXS⟩ ht'
      ⟨hY, hYT'⟩ hw₁
    rw [e]
    congr 1
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le hY] at hv
    exact (h.viewInt_agree' hu hv).symm
  -- the `t`-view rate as an integral of `f`
  have hrt : ∀ v ∈ Icc (0 : ℝ) Y, frzRate (fun s => W₂ s - W₂ 0) (Wt X) (bt X) (frzChart (fun s => W₁ s - W₂ 0) X) v =
      2 * ∫ u in (0 : ℝ)..X, f u v := by
    intro v hv
    obtain ⟨S', hXS', hs', w₂, hw₂⟩ := h.sOwn v hv
    exact tView_rate_eq (n := 0) (κ := 1) (r := fun _ => 0) (p := fun _ => 0) hs' ⟨hX, hXS'⟩ htX
      ⟨hv.1, hv.2.trans hYT⟩ hw₂
  -- continuity of the iterated integrands
  have hc1 : ContinuousOn (fun u => ∫ v in (0 : ℝ)..Y, f u v) (Icc 0 X) := by
    refine (((hsY.continuousOn_frzRate).mono (Icc_subset_Icc_right hXS)).div_const 2).congr fun u hu => ?_
    simp only [hrs u hu]; ring
  have hc2 : ContinuousOn (fun v => ∫ u in (0 : ℝ)..X, f u v) (Icc 0 Y) := by
    refine (((htX.continuousOn_frzRate).mono (Icc_subset_Icc_right hYT)).div_const 2).congr fun v hv => ?_
    simp only [hrt v hv]; ring
  have hswap := intervalIntegral_swap_of_nonneg (f := f) hX hY
    (fun u _ v _ => viewInt_nonneg _ _ _ _ _ _)
    (fun u hu => by
      obtain ⟨T', hYT', ht', w₁, hw₁⟩ := h.tOwn u hu
      exact ((ht'.continuousOn_viewInt hw₁).mono (Icc_subset_Icc_right hYT')).congr fun v hv =>
        h.viewInt_agree' hu hv)
    (fun v hv => by
      obtain ⟨S', hXS', hs', w₂, hw₂⟩ := h.sOwn v hv
      exact (hs'.continuousOn_viewInt hw₂).mono (Icc_subset_Icc_right hXS'))
    (by rw [← uIcc_of_le hX] at hc1; exact hc1.intervalIntegrable)
    (by rw [← uIcc_of_le hY] at hc2; exact hc2.intervalIntegrable)
  have eL : ∫ u in (0 : ℝ)..X, frzRate W₁ (Ws Y) (as Y) (frzChart W₂ Y) u =
      2 * ∫ u in (0 : ℝ)..X, ∫ v in (0 : ℝ)..Y, f u v := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun u hu => by rw [uIcc_of_le hX] at hu; exact hrs u hu
  have eR : ∫ v in (0 : ℝ)..Y,
      frzRate (fun s => W₂ s - W₂ 0) (Wt X) (bt X) (frzChart (fun s => W₁ s - W₂ 0) X) v =
      2 * ∫ v in (0 : ℝ)..Y, ∫ u in (0 : ℝ)..X, f u v := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun v hv => by rw [uIcc_of_le hY] at hv; exact hrt v hv
  unfold frzLogF
  rw [eL, eR, hswap]

end TwoViewRect

/-! ### The two views of `log M̃` differ by a separable term ((D6), sub-steps (a)–(b)) -/

namespace TwoViewRect

variable {W₁ W₂ : ℝ → ℝ} {X Y : ℝ} {as Ws bt Wt : ℝ → ℝ → ℝ} (h : TwoViewRect W₁ W₂ X Y as Ws bt Wt)
include h

/-- **The two one-sided `log M̃` at the corner `(X, Y)` differ by `Σ_m γ_m (log g₁,X'(p_m) − log g₂,Y'(p_m))`**, a sum of
a function of `X` alone and a function of `Y` alone (the mark-derivative factors `G'(p_m)/g₂'(p_m)` vs `G'(p_m)/g₁'(p_m)`);
every other factor agrees (with the dual parameter `16/κ` and the dual charges `−(κ/4) r_m` in the `t`-view). -/
theorem ell_sub_ell {n : ℕ} {κ : ℝ} (hκ : κ ≠ 0) (r : Fin n → ℝ) (p : Fin n → ℝ) (hW₁ : Continuous W₁)
    (hW₂ : Continuous W₂) (hp1 : ∀ m, ∃ w, IsForwardSol W₁ ((p m : ℝ) : ℂ) X w)
    (hp2 : ∀ m, ∃ w, IsForwardSol W₂ ((p m : ℝ) : ℂ) Y w)
    (hps : ∀ m, ∃ w, IsForwardSol (Ws Y) ((frzMarks W₂ p Y m : ℝ) : ℂ) (as Y X) w)
    (hpt : ∀ m, ∃ w, IsForwardSol (Wt X) ((frzMarks (fun u => W₁ u - W₂ 0) (fun m => p m - W₂ 0) X m : ℝ) : ℂ)
      (bt X Y) w) :
    (sView κ r W₁ W₂ as Ws p Y).ell X (W₁ X) - (tView κ r W₁ W₂ bt Wt p X).ell Y (W₂ Y - W₂ 0) =
      ∑ m, dualGamma κ (r m) * (Real.log (deriv (fwdMap W₁ X) (p m)).re -
        Real.log (deriv (fwdMap W₂ Y) (p m)).re) := by
  have hX := h.nonneg_X
  have hY := h.nonneg_Y
  obtain ⟨S, hXS, hs, w, hw⟩ := h.sOwn Y ⟨hY, le_rfl⟩
  obtain ⟨T, hYT, ht, w', hw'⟩ := h.tOwn X ⟨hX, le_rfl⟩
  have hx : X ∈ Icc (0 : ℝ) S := ⟨hX, hXS⟩
  have hy : Y ∈ Icc (0 : ℝ) T := ⟨hY, hYT⟩
  set d := sView κ r W₁ W₂ as Ws p Y with hd
  set e := tView κ r W₁ W₂ bt Wt p X with he
  set c := W₂ 0 with hc
  -- the factor identities
  have a1 : d.F 1 X (W₁ X) = e.A21 Y := sView_F_one hs hx ht hy hw'
  have a0 : d.F 0 X (W₁ X) = e.A20 Y + c := sView_F_zero hs hx ht hy hw'
  have b1 : e.F 1 Y (W₂ Y - c) = d.A21 X := tView_F_one hs hx ht hy hw
  have b0 : e.F 0 Y (W₂ Y - c) = d.A20 X - c := tView_F_zero hs hx ht hy hw
  have hL : frzLogF d.W d.W' d.a d.φ X = frzLogF e.W e.W' e.a e.φ Y := h.frzLogF_eq
  have hmk : ∀ m, d.B0 X m = e.B0 Y m + c ∧
      d.B1 X m * (deriv (fwdMap W₂ Y) (p m)).re = e.B1 Y m * (deriv (fwdMap W₁ X) (p m)).re := fun m => by
    obtain ⟨w₁, hw₁⟩ := hp1 m
    obtain ⟨w₂, hw₂⟩ := hp2 m
    obtain ⟨w₃, hw₃⟩ := hps m
    obtain ⟨w₄, hw₄⟩ := hpt m
    exact marks_agree hW₁ hW₂ hs hx ht hy m hw₁ hw₂ hw₃ hw₄
  -- positivity of the derivative factors
  have hax := hs.toImgData.mapsTo_clock_Icc hx
  have hby := ht.toImgData.mapsTo_clock_Icc hy
  have hB1s : ∀ m, 0 < d.B1 X m := fun m => by
    obtain ⟨w₃, hw₃⟩ := hps m
    exact (deriv_fwdMap_real hs.contW' hw₃ ⟨hax.1, le_rfl⟩).2
  have hB1t : ∀ m, 0 < e.B1 Y m := fun m => by
    obtain ⟨w₄, hw₄⟩ := hpt m
    exact (deriv_fwdMap_real ht.contW' hw₄ ⟨hby.1, le_rfl⟩).2
  have hg₁ : ∀ m, 0 < (deriv (fwdMap W₁ X) (p m)).re := fun m => by
    obtain ⟨w₁, hw₁⟩ := hp1 m
    exact (deriv_fwdMap_real hW₁ hw₁ ⟨hX, le_rfl⟩).2
  have hg₂ : ∀ m, 0 < (deriv (fwdMap W₂ Y) (p m)).re := fun m => by
    obtain ⟨w₂, hw₂⟩ := hp2 m
    exact (deriv_fwdMap_real hW₂ hw₂ ⟨hY, le_rfl⟩).2
  have hlogB : ∀ m, Real.log (d.B1 X m) = Real.log (e.B1 Y m) + Real.log (deriv (fwdMap W₁ X) (p m)).re -
      Real.log (deriv (fwdMap W₂ Y) (p m)).re := fun m => by
    have h1 := congrArg Real.log (hmk m).2
    rw [Real.log_mul (hB1s m).ne' (hg₂ m).ne', Real.log_mul (hB1t m).ne' (hg₁ m).ne'] at h1
    linarith
  -- the exponent identities
  have eα : dualAlpha (16 / κ) = (3 * κ - 8) / 16 := dualAlpha_dual hκ
  have eα' : (3 * (16 / κ) - 8) / 16 = dualAlpha κ := by unfold dualAlpha; field_simp; ring
  have eΛ : dualLambda (16 / κ) = dualLambda κ := dualLambda_dual hκ
  have er : ∀ m, -(16 / κ / 4) * (-(κ / 4) * r m) = r m := fun m => by field_simp; ring
  -- unfold both sides
  have hdκ : d.κ = κ := rfl
  have hdr : d.r = r := rfl
  have heκ : e.κ = 16 / κ := rfl
  have her : e.r = fun m => -(κ / 4) * r m := rfl
  simp only [FrzData.ell, FrzData.LT, FrzData.LS, dualLogTime, dualLogSpace]
  rw [a1, a0, b1, b0, hL, hdκ, hdr, heκ, her, eα, eα', eΛ]
  -- the pair sums agree
  have hpair : pairSum (fun m k => dualDelta κ (r m) (r k) * Real.log (d.B0 X m - d.B0 X k)) =
      pairSum (fun m k => dualDelta (16 / κ) (-(κ / 4) * r m) (-(κ / 4) * r k) * Real.log (e.B0 Y m - e.B0 Y k)) := by
    congr 1; funext m k
    rw [dualDelta_dual hκ, (hmk m).1, (hmk k).1]
    congr 2; ring
  -- the sums over the marks
  have hS : (∑ m, (dualGamma κ (r m) * Real.log (d.B1 X m) + -(κ / 4) * r m * Real.log (d.A20 X - d.B0 X m))) +
      (∑ m, r m * Real.log (e.A20 Y + c - d.B0 X m)) -
      (∑ m, (dualGamma (16 / κ) (-(κ / 4) * r m) * Real.log (e.B1 Y m) +
        -(16 / κ / 4) * (-(κ / 4) * r m) * Real.log (e.A20 Y - e.B0 Y m))) -
      (∑ m, -(κ / 4) * r m * Real.log (d.A20 X - c - e.B0 Y m)) =
      ∑ m, dualGamma κ (r m) * (Real.log (deriv (fwdMap W₁ X) (p m)).re -
        Real.log (deriv (fwdMap W₂ Y) (p m)).re) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hlogB m, (hmk m).1, dualGamma_dual hκ, er m]
    have l1 : Real.log (e.A20 Y + c - (e.B0 Y m + c)) = Real.log (e.A20 Y - e.B0 Y m) := by congr 1; ring
    have l2 : Real.log (d.A20 X - (e.B0 Y m + c)) = Real.log (d.A20 X - c - e.B0 Y m) := by congr 1; ring
    rw [l1, l2]
    ring
  have hE : Real.log (e.A20 Y + c - d.A20 X) = Real.log (d.A20 X - c - e.A20 Y) := by
    rw [← Real.log_neg_eq_log]; congr 1; ring
  rw [hpair, hE]
  linear_combination hS

end TwoViewRect

/-! ### The (D6)-normalised density is the same in both views -/

namespace TwoViewRect

variable {W₁ W₂ : ℝ → ℝ} {X Y : ℝ} {as Ws bt Wt : ℝ → ℝ → ℝ} (h : TwoViewRect W₁ W₂ X Y as Ws bt Wt)
include h

/-- Two-view data restrict to every sub-rectangle `[0, x] × [0, y]`. -/
theorem mono {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) X) (hy : y ∈ Icc (0 : ℝ) Y) : TwoViewRect W₁ W₂ x y as Ws bt Wt where
  nonneg_X := hx.1
  nonneg_Y := hy.1
  sOwn v hv := by
    obtain ⟨S, hXS, hs, hw⟩ := h.sOwn v ⟨hv.1, hv.2.trans hy.2⟩
    exact ⟨S, hx.2.trans hXS, hs, hw⟩
  tOwn u hu := by
    obtain ⟨T, hYT, ht, hw⟩ := h.tOwn u ⟨hu.1, hu.2.trans hx.2⟩
    exact ⟨T, hy.2.trans hYT, ht, hw⟩

/-- **(D6): the normalised density `M = M̃(x, y)M̃(0, 0)/(M̃(x, 0)M̃(0, y))` is the same in both views**, at every point
of the rectangle (log form, A13's `normLog`): the separable difference of `ell_sub_ell` cancels. The mark hypotheses
are the aliveness of the marks for both curves and for both image chains (A9's `TwoCurveD9.alive` in each view). -/
theorem normLog_eq {n : ℕ} {κ : ℝ} (hκ : κ ≠ 0) (r : Fin n → ℝ) (p : Fin n → ℝ) (hW₁ : Continuous W₁)
    (hW₂ : Continuous W₂) (hp1 : ∀ m, ∃ w, IsForwardSol W₁ ((p m : ℝ) : ℂ) X w)
    (hp2 : ∀ m, ∃ w, IsForwardSol W₂ ((p m : ℝ) : ℂ) Y w)
    (hps : ∀ v ∈ Icc (0 : ℝ) Y, ∀ u ∈ Icc (0 : ℝ) X, ∀ m, ∃ w,
      IsForwardSol (Ws v) ((frzMarks W₂ p v m : ℝ) : ℂ) (as v u) w)
    (hpt : ∀ u ∈ Icc (0 : ℝ) X, ∀ v ∈ Icc (0 : ℝ) Y, ∀ m, ∃ w,
      IsForwardSol (Wt u) ((frzMarks (fun s => W₁ s - W₂ 0) (fun m => p m - W₂ 0) u m : ℝ) : ℂ) (bt u v) w)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) X) (hy : y ∈ Icc (0 : ℝ) Y) :
    normLog (fun x y => (sView κ r W₁ W₂ as Ws p y).ell x (W₁ x)) x y =
      normLog (fun x y => (tView κ r W₁ W₂ bt Wt p x).ell y (W₂ y - W₂ 0)) x y := by
  have corner : ∀ x' ∈ Icc (0 : ℝ) X, ∀ y' ∈ Icc (0 : ℝ) Y,
      (sView κ r W₁ W₂ as Ws p y').ell x' (W₁ x') - (tView κ r W₁ W₂ bt Wt p x').ell y' (W₂ y' - W₂ 0) =
        (∑ m, dualGamma κ (r m) * Real.log (deriv (fwdMap W₁ x') (p m)).re) -
          ∑ m, dualGamma κ (r m) * Real.log (deriv (fwdMap W₂ y') (p m)).re := by
    intro x' hx' y' hy'
    rw [(h.mono hx' hy').ell_sub_ell hκ r p hW₁ hW₂
      (fun m => by obtain ⟨w, hw⟩ := hp1 m; exact ⟨w, Ito.isForwardSol_of_le hw hx'.1 hx'.2⟩)
      (fun m => by obtain ⟨w, hw⟩ := hp2 m; exact ⟨w, Ito.isForwardSol_of_le hw hy'.1 hy'.2⟩)
      (hps y' hy' x' hx') (hpt x' hx' y' hy'), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  have h0X : (0 : ℝ) ∈ Icc (0 : ℝ) X := ⟨le_rfl, h.nonneg_X⟩
  have h0Y : (0 : ℝ) ∈ Icc (0 : ℝ) Y := ⟨le_rfl, h.nonneg_Y⟩
  have c1 := corner x hx y hy
  have c2 := corner x hx 0 h0Y
  have c3 := corner 0 h0X y hy
  have c4 := corner 0 h0X 0 h0Y
  unfold normLog
  linarith

end TwoViewRect

end InteractingSLE.ZhanGT4
