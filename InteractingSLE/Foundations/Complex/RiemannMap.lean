import InteractingSLE.Foundations.Topology.SimplyConnected
import QuantumZipper.Proofs.Complex.BasicsAutomorphisms
import QuantumZipper.Proofs.GFF.K3.Conformal

/-!
# The normalized Riemann mapping theorem

Design `planning/INFRA-GEO.md` §3 (packet GEO-SC). Conformal maps are
`SupercriticalConformalCovariance.IsConformalBijection φ U V` (holomorphic on `U`, `BijOn φ U V`),
with `IsOpen U` as a separate hypothesis.

## Main results

* `exists_isConformalBijection_ball`: **Riemann mapping theorem**, normalized
  (`φ z₀ = 0`, `φ'(z₀) > 0`), for open connected simply connected proper subsets of `ℂ`
  (Ahlfors, *Complex Analysis*, 3rd ed., Ch. 6 §1.1, Theorem 1);
* `isConformalBijection_unique_of_deriv_pos`: uniqueness of the normalized map (ibid.);
* `exists_diskAutomorphism`, `exists_eqOn_mul_diskMobius_of_isConformalBijection`: the
  automorphisms of the unit disc are the maps `z ↦ u (z - a)/(1 - ā z)`, `‖u‖ = 1`, `‖a‖ < 1`, and
  they act transitively (R. B. Burckel, *Classical Analysis in the Complex Plane* (2021),
  Theorem 6.2 (ii), p. 399, the citation pinned in QuantumZipper's `BasicsAutomorphisms`);
* `isConformalBijection_iff_isConformalOnto`: the bridge to QuantumZipper's
  `QuantumZipper.K3.IsConformalOnto` on open sets.

The existence proof feeds `hasHoloSqrt_of_isSimplyConnected` into QuantumZipper's
`QuantumZipper.CA.RMT.riemann_mapping_of_hasHoloSqrt`, then normalizes with a disc automorphism and
a rotation. Uniqueness: `ψ ∘ φ⁻¹` is an automorphism of the disc fixing `0`, hence a rotation
(QuantumZipper `exists_rotation_of_bijOn_ball`), and the rotation is `1` because both derivatives
at `z₀` are positive.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper.CA (diskMobius)

namespace InteractingSLE

/-! ### Composition and disc automorphisms -/

/-- Conformal bijections compose. -/
theorem isConformalBijection_comp {f g : ℂ → ℂ} {U V W : Set ℂ}
    (hg : IsConformalBijection g V W) (hf : IsConformalBijection f U V) :
    IsConformalBijection (g ∘ f) U W :=
  ⟨hg.1.comp hf.1 hf.2.mapsTo, hg.2.comp hf.2⟩

/-- The disc Möbius map `z ↦ (z - a)/(1 - ā z)`, `‖a‖ < 1`, is a conformal automorphism of the
unit disc. -/
theorem isConformalBijection_diskMobius {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    IsConformalBijection (diskMobius a) (ball 0 1) (ball 0 1) := by
  have ha' : ‖a‖ < 1 := mem_ball_zero_iff.1 ha
  have hna : ‖-a‖ < 1 := by rwa [norm_neg]
  refine ⟨(QuantumZipper.CA.differentiableOn_diskMobius ha').mono ball_subset_closedBall,
    fun z hz => QuantumZipper.CA.diskMobius_mem_ball ha' hz, fun z hz w hw hzw => ?_,
    fun w hw => ⟨diskMobius (-a) w, QuantumZipper.CA.diskMobius_mem_ball hna hw, ?_⟩⟩
  · have hz' := QuantumZipper.CA.diskMobius_neg_diskMobius ha' (mem_ball_zero_iff.1 hz).le
    have hw' := QuantumZipper.CA.diskMobius_neg_diskMobius ha' (mem_ball_zero_iff.1 hw).le
    rw [← hz', ← hw', hzw]
  · have := QuantumZipper.CA.diskMobius_neg_diskMobius hna (mem_ball_zero_iff.1 hw).le
    rwa [neg_neg] at this

/-- The automorphisms of the unit disc act transitively: some automorphism sends `a` to `0`. -/
theorem exists_diskAutomorphism {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    ∃ m : ℂ → ℂ, IsConformalBijection m (ball 0 1) (ball 0 1) ∧ m a = 0 :=
  ⟨diskMobius a, isConformalBijection_diskMobius ha, QuantumZipper.CA.diskMobius_self a⟩

/-- A rotation `w ↦ u w`, `‖u‖ = 1`, is a conformal automorphism of the unit disc. -/
theorem isConformalBijection_const_mul_ball {u : ℂ} (hu : ‖u‖ = 1) :
    IsConformalBijection (fun w => u * w) (ball 0 1) (ball 0 1) := by
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu
    exact zero_ne_one hu
  refine ⟨(differentiable_id.const_mul u).differentiableOn, fun w hw => ?_,
    fun z _ w _ h => mul_left_cancel₀ hu0 h, fun w hw => ⟨u⁻¹ * w, ?_, ?_⟩⟩
  · rw [mem_ball_zero_iff, norm_mul, hu, one_mul]
    exact mem_ball_zero_iff.1 hw
  · rw [mem_ball_zero_iff, norm_mul, norm_inv, hu, inv_one, one_mul]
    exact mem_ball_zero_iff.1 hw
  · simp only
    rw [← mul_assoc, mul_inv_cancel₀ hu0, one_mul]

/-- **The automorphisms of the unit disc** (Burckel, Theorem 6.2 (ii)): every conformal
bijection of the unit disc onto itself is `z ↦ u (z - a)/(1 - ā z)` with `‖u‖ = 1`, `‖a‖ < 1`. -/
theorem exists_eqOn_mul_diskMobius_of_isConformalBijection {f : ℂ → ℂ}
    (hf : IsConformalBijection f (ball 0 1) (ball 0 1)) :
    ∃ u a : ℂ, ‖u‖ = 1 ∧ a ∈ ball (0 : ℂ) 1 ∧ EqOn f (fun z => u * diskMobius a z) (ball 0 1) := by
  obtain ⟨a, ha, hfa⟩ := hf.2.surjOn (mem_ball_self one_pos)
  have ha' : ‖a‖ < 1 := mem_ball_zero_iff.1 ha
  have hna : -a ∈ ball (0 : ℂ) 1 := by rwa [mem_ball_zero_iff, norm_neg]
  have hg := isConformalBijection_comp hf (isConformalBijection_diskMobius hna)
  have hg0 : (f ∘ diskMobius (-a)) 0 = 0 := by
    simp only [Function.comp_apply, diskMobius, zero_sub, neg_neg, mul_zero, sub_zero, div_one]
    exact hfa
  obtain ⟨u, hu, hrot⟩ := QuantumZipper.CA.exists_rotation_of_bijOn_ball hg.1 hg.2 hg0
  refine ⟨u, a, hu, ha, fun z hz => ?_⟩
  have hmz := QuantumZipper.CA.diskMobius_mem_ball ha' hz
  have := hrot hmz
  simp only [Function.comp_apply] at this
  rw [QuantumZipper.CA.diskMobius_neg_diskMobius ha' (mem_ball_zero_iff.1 hz).le] at this
  exact this

/-! ### The normalized Riemann map -/

/-- **Riemann mapping theorem**, normalized (Ahlfors, *Complex Analysis*, 3rd ed., Ch. 6 §1.1,
Theorem 1), from Mathlib's `IsSimplyConnected`: an open connected simply connected `U ≠ ℂ` and
`z₀ ∈ U` have a conformal bijection `φ : U → 𝔻` with `φ z₀ = 0` and `φ'(z₀) > 0`. -/
theorem exists_isConformalBijection_ball {U : Set ℂ} (hUo : IsOpen U) (hUc : IsConnected U)
    (hsc : IsSimplyConnected U) (hne : U ≠ univ) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∃ φ : ℂ → ℂ, IsConformalBijection φ U (ball 0 1) ∧ φ z₀ = 0 ∧
      0 < (deriv φ z₀).re ∧ (deriv φ z₀).im = 0 := by
  obtain ⟨φ₀, hbij, hd, -⟩ := QuantumZipper.CA.RMT.riemann_mapping_of_hasHoloSqrt hUo
    hUc.isPreconnected ⟨z₀, hz₀⟩ hne (hasHoloSqrt_of_isSimplyConnected hUo hsc)
  have hφ₀ : IsConformalBijection φ₀ U (ball 0 1) := ⟨hd, hbij⟩
  have ha : φ₀ z₀ ∈ ball (0 : ℂ) 1 := hbij.mapsTo hz₀
  -- move `φ₀ z₀` to `0`
  set φ₁ : ℂ → ℂ := diskMobius (φ₀ z₀) ∘ φ₀ with hφ₁def
  have hφ₁ : IsConformalBijection φ₁ U (ball 0 1) :=
    isConformalBijection_comp (isConformalBijection_diskMobius ha) hφ₀
  have hφ₁0 : φ₁ z₀ = 0 := QuantumZipper.CA.diskMobius_self _
  set d := deriv φ₁ z₀ with hd_def
  have hd0 : d ≠ 0 := QuantumZipper.CA.deriv_ne_zero_of_injOn hUo hφ₁.1 hφ₁.2.injOn hz₀
  have hdn : (0 : ℝ) < ‖d‖ := norm_pos_iff.2 hd0
  -- rotate the derivative to the positive axis
  set u : ℂ := conj d / (‖d‖ : ℂ) with hu_def
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hdn, div_self hdn.ne']
  refine ⟨(fun w => u * w) ∘ φ₁, isConformalBijection_comp
    (isConformalBijection_const_mul_ball hu) hφ₁, ?_, ?_⟩
  · simp only [Function.comp_apply, hφ₁0, mul_zero]
  have hder : deriv ((fun w => u * w) ∘ φ₁) z₀ = (‖d‖ : ℂ) := by
    have hdiff : DifferentiableAt ℂ φ₁ z₀ := hφ₁.1.differentiableAt (hUo.mem_nhds hz₀)
    have h1 : deriv ((fun w => u * w) ∘ φ₁) z₀ = u * d := by
      change deriv (fun z => u * φ₁ z) z₀ = u * d
      rw [deriv_const_mul _ hdiff]
    rw [h1, hu_def, div_mul_eq_mul_div, Complex.conj_mul', ← ofReal_pow, ← ofReal_div, sq,
      mul_div_assoc, div_self hdn.ne', mul_one]
  rw [hder, ofReal_re, ofReal_im]
  exact ⟨hdn, rfl⟩

/-- **Uniqueness of the normalized Riemann map** (Ahlfors, Ch. 6 §1.1, Theorem 1): two conformal
bijections `U → 𝔻` sending `z₀` to `0` with positive derivative at `z₀` agree on `U`. -/
theorem isConformalBijection_unique_of_deriv_pos {U : Set ℂ} (hUo : IsOpen U) {φ ψ : ℂ → ℂ}
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hφ : IsConformalBijection φ U (ball 0 1))
    (hψ : IsConformalBijection ψ U (ball 0 1)) (hφ0 : φ z₀ = 0) (hψ0 : ψ z₀ = 0)
    (hφre : 0 < (deriv φ z₀).re) (hφim : (deriv φ z₀).im = 0)
    (hψre : 0 < (deriv ψ z₀).re) (hψim : (deriv ψ z₀).im = 0) : EqOn φ ψ U := by
  set e := QuantumZipper.CA.univalentOPH hUo hφ.1 hφ.2.injOn with he
  have himg : φ '' U = ball 0 1 := hφ.2.image_eq
  have hed : DifferentiableOn ℂ e.symm (ball 0 1) := by
    have := QuantumZipper.CA.differentiableOn_univalentOPH_symm hUo hφ.1 hφ.2.injOn
    rwa [himg] at this
  have hleft : ∀ z ∈ U, e.symm (φ z) = z := fun z hz =>
    QuantumZipper.CA.univalentOPH_symm_apply_apply hUo hφ.1 hφ.2.injOn hz
  have hright : ∀ w ∈ ball (0 : ℂ) 1, φ (e.symm w) = w := fun w hw =>
    QuantumZipper.CA.univalentOPH_apply_symm_apply hUo hφ.1 hφ.2.injOn (himg ▸ hw)
  have hebij : BijOn e.symm (ball 0 1) U := by
    refine ⟨fun w hw => ?_, fun w₁ h₁ w₂ h₂ h => ?_, fun z hz => ⟨φ z, hφ.2.mapsTo hz, hleft z hz⟩⟩
    · have hw' : w ∈ e.target := by
        rw [he, QuantumZipper.CA.univalentOPH_target, himg]
        exact hw
      have := e.map_target hw'
      rwa [he, QuantumZipper.CA.univalentOPH_source] at this
    · rw [← hright w₁ h₁, ← hright w₂ h₂, h]
  -- `ψ ∘ φ⁻¹` is an automorphism of the disc fixing `0`: a rotation
  have hg : IsConformalBijection (ψ ∘ e.symm) (ball 0 1) (ball 0 1) :=
    isConformalBijection_comp hψ ⟨hed, hebij⟩
  have hg0 : (ψ ∘ e.symm) 0 = 0 := by
    have h0 : e.symm 0 = z₀ := by
      rw [← hφ0]
      exact hleft z₀ hz₀
    simp only [Function.comp_apply]
    rw [h0, hψ0]
  obtain ⟨u, hu, hrot⟩ := QuantumZipper.CA.exists_rotation_of_bijOn_ball hg.1 hg.2 hg0
  have hψu : ∀ z ∈ U, ψ z = u * φ z := fun z hz => by
    have := hrot (hφ.2.mapsTo hz)
    simp only [Function.comp_apply, hleft z hz] at this
    exact this
  -- comparing derivatives at `z₀` forces `u = 1`
  have hev : ψ =ᶠ[𝓝 z₀] fun z => u * φ z :=
    Filter.eventually_of_mem (hUo.mem_nhds hz₀) hψu
  have hdiff : DifferentiableAt ℂ φ z₀ := hφ.1.differentiableAt (hUo.mem_nhds hz₀)
  have hder : deriv ψ z₀ = u * deriv φ z₀ := by
    rw [hev.deriv_eq, deriv_const_mul _ hdiff]
  set p := deriv φ z₀ with hp
  set q := deriv ψ z₀ with hq
  have hpr : p = ((p.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hφim])
  have hqr : q = ((q.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hψim])
  have hu1 : u = 1 := by
    have hp0 : p ≠ 0 := fun h => by rw [h, zero_re] at hφre; exact lt_irrefl _ hφre
    have hueq : u = ((q.re / p.re : ℝ) : ℂ) := by
      rw [ofReal_div, ← hpr, ← hqr, hder, mul_div_assoc, div_self hp0, mul_one]
    have hpos : 0 < q.re / p.re := div_pos hψre hφre
    rw [hueq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos] at hu
    rw [hueq, hu, ofReal_one]
  intro z hz
  rw [hψu z hz, hu1, one_mul]

/-! ### Bridge to QuantumZipper's conformal maps -/

/-- On an open set, `IsConformalBijection` agrees with QuantumZipper's
`QuantumZipper.K3.IsConformalOnto` (whose derivative condition is automatic for injective
holomorphic maps, `QuantumZipper.CA.deriv_ne_zero_of_injOn`). -/
theorem isConformalBijection_iff_isConformalOnto {φ : ℂ → ℂ} {U V : Set ℂ} (hUo : IsOpen U) :
    IsConformalBijection φ U V ↔ QuantumZipper.K3.IsConformalOnto φ U V := by
  constructor
  · intro h
    exact ⟨hUo, h.1, h.2.injOn, h.2.image_eq, fun z hz =>
      QuantumZipper.CA.deriv_ne_zero_of_injOn hUo h.1 h.2.injOn hz⟩
  · intro h
    refine ⟨h.diffOn, ?_⟩
    have := h.injOn.bijOn_image
    rwa [h.image_eq] at this

end InteractingSLE
