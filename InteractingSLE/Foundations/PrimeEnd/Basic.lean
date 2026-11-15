import InteractingSLE.Foundations.Complex.RiemannMap
import QuantumZipper.Proofs.Complex.BasicsCayley
import QuantumZipper.Proofs.Complex.BasicsAutomorphisms
import QuantumZipper.Proofs.Complex.BasicsUnivalent
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# Prime ends through half-plane charts

Design `planning/INFRA-GEO.md` §3 "Prime ends and planar topology" (packet GEO-PE). The prime ends
of a domain `D ⊆ ℂ` are described through Carathéodory's prime-end theorem (Pommerenke, *Boundary
Behaviour of Conformal Maps*, 1992, Thm 2.15): every conformal map `ψ : D → ℍ` identifies them with
`ℝ ∪ {∞} = OnePoint ℝ`, and two charts differ by a real Möbius map `z ↦ (az + b)/(cz + d)`,
`ad - bc > 0`, acting on the boundary by `mobiusBdry`. `PrimeEnd D` is the quotient of
`HChart D × OnePoint ℝ` by this change of chart (Specification p. 2: "boundary markings used in
conformal maps are prime ends"; p. 10: "`ψ` sends them to `0` and `∞` in the prime-end
compactification").

## Main results

* `mobiusBdry_mobiusBdry`, `mobiusBdry_inv_apply`, `continuous_mobiusBdry`,
  `mobiusBdryHomeomorph`: the boundary action is Mathlib's `GL(2, ℝ)` action on `OnePoint ℝ`
  (`mobiusBdry_eq_smul`) and acts by homeomorphisms;
* `PrimeEnd.rel_equivalence`: change of chart is an equivalence relation, so
  `PrimeEnd.mk ψ x = PrimeEnd.mk φ y ↔ PrimeEnd.Rel D (ψ, x) (φ, y)` (`PrimeEnd.mk_eq_mk_iff`);
* `PrimeEnd.mk_injective` (any `D`) and `PrimeEnd.mk_bijective_of_isOpen`: each chart of an open
  domain describes every prime end exactly once (two charts differ by a real Möbius map:
  `HChart.exists_realMobius`, from QuantumZipper's classification of `Aut ℍ`);
* `PrimeEnd.topology_eq_coinduced`, `PrimeEnd.mkHomeomorph`: on an open domain the topology of
  `PrimeEnd D` is the one transported by any chart;
* `PrimeEnd.tendsto_realMobius_approachH`, `PrimeEnd.isRealizedAt_mk_iff`,
  `PrimeEnd.isRealizedAt_iff_of_isOpen`, `PrimeEnd.IsRealizedAt.unique`: the Euclidean realization
  of a prime end does not depend on the chart, and is unique.

## Deviation from the design: `IsOpen D`

`PrimeEnd.not_forall_bijective_mk` proves the counterexample below in Lean.

The design's `PrimeEnd.mk_bijective (ψ : HChart D) : Function.Bijective (mk ψ)` has no hypothesis
on `D`, and it is false for some non-open `D`: `IsConformalBijection ψ D ℍ` only asks for
differentiability *within* `D`, which is automatic at isolated points of `D`. For
`D = (ℍ \ {i, 2i}) ∪ {-i, -2i}` the maps `ψ₁` (identity off `{-i, -2i}`, `-i ↦ i`, `-2i ↦ 2i`)
and `ψ₂` (identity off `{-i, -2i}`, `-i ↦ 2i`, `-2i ↦ i`) are charts, but `ψ₂ = m ∘ ψ₁` on `D`
for no real Möbius `m` (it would fix `ℍ \ {i, 2i}`, hence be the identity, while
`ψ₂ (-i) ≠ ψ₁ (-i)`), so `mk ψ₁` misses `mk ψ₂ ∞`. The design (§1) keeps `IsOpen U` as a separate
hypothesis of conformal-map statements; the corrected statements add it
(`mk_bijective_of_isOpen`, `isRealizedAt_iff_of_isOpen`, whose statement refers to it). Injectivity
and the chart independence of the realization at a marked point hold for every `D`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Function
open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar)
open QuantumZipper.CA (realMobius)

namespace InteractingSLE

/-- The boundary action of the real Möbius map `z ↦ (az + b)/(cz + d)` on `ℝ ∪ {∞}`. -/
def mobiusBdry (a b c d : ℝ) (p : OnePoint ℝ) : OnePoint ℝ :=
  p.elim (if c = 0 then OnePoint.infty else ((a / c : ℝ) : OnePoint ℝ))
    fun x => if c * x + d = 0 then OnePoint.infty else (((a * x + b) / (c * x + d) : ℝ) : OnePoint ℝ)

section MobiusBdry

variable {a b c d : ℝ}

@[simp] theorem mobiusBdry_infty (a b c d : ℝ) :
    mobiusBdry a b c d OnePoint.infty =
      if c = 0 then OnePoint.infty else ((a / c : ℝ) : OnePoint ℝ) := rfl

@[simp] theorem mobiusBdry_coe (a b c d x : ℝ) :
    mobiusBdry a b c d (x : OnePoint ℝ) =
      if c * x + d = 0 then OnePoint.infty else (((a * x + b) / (c * x + d) : ℝ) : OnePoint ℝ) :=
  rfl

/-- The invertible matrix `[[a, b], [c, d]]`. -/
def mobiusGL (a b c d : ℝ) (h : a * d - b * c ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; c, d] (by rwa [Matrix.det_fin_two_of])

/-- `mobiusBdry` is Mathlib's action of `GL(2, ℝ)` on `OnePoint ℝ`. -/
theorem mobiusBdry_eq_smul (h : a * d - b * c ≠ 0) (p : OnePoint ℝ) :
    mobiusBdry a b c d p = mobiusGL a b c d h • p := by
  cases p with
  | infty =>
    simp [mobiusBdry, OnePoint.smul_infty_eq_ite, mobiusGL,
      Matrix.GeneralLinearGroup.mkOfDetNeZero]
  | coe x =>
    simp [mobiusBdry, OnePoint.smul_some_eq_ite, mobiusGL,
      Matrix.GeneralLinearGroup.mkOfDetNeZero]

private theorem mobius_det_mul_ne_zero {a' b' c' d' : ℝ} (h : a * d - b * c ≠ 0)
    (h' : a' * d' - b' * c' ≠ 0) :
    (a * a' + b * c') * (c * b' + d * d') - (a * b' + b * d') * (c * a' + d * c') ≠ 0 := by
  have : (a * a' + b * c') * (c * b' + d * d') - (a * b' + b * d') * (c * a' + d * c') =
      (a * d - b * c) * (a' * d' - b' * c') := by ring
  rw [this]; exact mul_ne_zero h h'

/-- Composition of boundary actions is the boundary action of the product matrix. -/
theorem mobiusBdry_mobiusBdry {a' b' c' d' : ℝ} (h : a * d - b * c ≠ 0)
    (h' : a' * d' - b' * c' ≠ 0) (p : OnePoint ℝ) :
    mobiusBdry a b c d (mobiusBdry a' b' c' d' p) =
      mobiusBdry (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') p := by
  rw [mobiusBdry_eq_smul h', mobiusBdry_eq_smul h,
    mobiusBdry_eq_smul (mobius_det_mul_ne_zero h h'), ← mul_smul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mobiusGL, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]

/-- Scaling the matrix does not change the boundary action. -/
theorem mobiusBdry_mul_left {k : ℝ} (hk : k ≠ 0) (a b c d : ℝ) :
    mobiusBdry (k * a) (k * b) (k * c) (k * d) = mobiusBdry a b c d := by
  funext p
  cases p with
  | infty =>
    simp only [mobiusBdry_infty, mul_eq_zero, hk, false_or]
    split_ifs with hc
    · rfl
    · rw [mul_div_mul_left _ _ hk]
  | coe x =>
    simp only [mobiusBdry_coe]
    have e1 : k * c * x + k * d = k * (c * x + d) := by ring
    have e2 : k * a * x + k * b = k * (a * x + b) := by ring
    rw [e1, e2]
    simp only [mul_eq_zero, hk, false_or]
    split_ifs with hc
    · rfl
    · rw [mul_div_mul_left _ _ hk]

@[simp] theorem mobiusBdry_one_zero_zero_one (p : OnePoint ℝ) : mobiusBdry 1 0 0 1 p = p := by
  cases p with
  | infty => simp
  | coe x => simp

/-- The boundary action of the inverse matrix undoes the boundary action. -/
theorem mobiusBdry_inv_apply (h : a * d - b * c ≠ 0) (p : OnePoint ℝ) :
    mobiusBdry d (-b) (-c) a (mobiusBdry a b c d p) = p := by
  have h' : d * a - (-b) * (-c) ≠ 0 := by
    rw [show d * a - (-b) * (-c) = a * d - b * c by ring]; exact h
  rw [mobiusBdry_mobiusBdry h' h]
  have e : mobiusBdry (d * a + -b * c) (d * b + -b * d) (-c * a + a * c) (-c * b + a * d) =
      mobiusBdry ((a * d - b * c) * 1) ((a * d - b * c) * 0) ((a * d - b * c) * 0)
        ((a * d - b * c) * 1) := by
    congr 1 <;> ring
  rw [e, mobiusBdry_mul_left h, mobiusBdry_one_zero_zero_one]

theorem mobiusBdry_apply_inv (h : a * d - b * c ≠ 0) (p : OnePoint ℝ) :
    mobiusBdry a b c d (mobiusBdry d (-b) (-c) a p) = p := by
  have h' : d * a - (-b) * (-c) ≠ 0 := by
    rw [show d * a - (-b) * (-c) = a * d - b * c by ring]; exact h
  have := mobiusBdry_inv_apply h' p
  simpa only [neg_neg] using this

theorem mobiusBdry_bijective (h : a * d - b * c ≠ 0) : Bijective (mobiusBdry a b c d) :=
  ⟨(LeftInverse.injective (g := mobiusBdry d (-b) (-c) a) (mobiusBdry_inv_apply h)),
    (RightInverse.surjective (g := mobiusBdry d (-b) (-c) a) (mobiusBdry_apply_inv h))⟩

/-- Along `cobounded ℝ`, the coercion into `OnePoint ℝ` tends to `∞`. -/
theorem tendsto_coe_cobounded_onePoint :
    Tendsto ((↑) : ℝ → OnePoint ℝ) (Bornology.cobounded ℝ) (𝓝 OnePoint.infty) := by
  rw [Metric.cobounded_eq_cocompact, ← Filter.coclosedCompact_eq_cocompact]
  exact OnePoint.tendsto_coe_infty

/-- A nonconstant affine map tends to infinity at infinity. -/
theorem tendsto_affine_cobounded {𝕜 : Type*} [NormedDivisionRing 𝕜] {α β : 𝕜} (hα : α ≠ 0) :
    Tendsto (fun x : 𝕜 => α * x + β) (Bornology.cobounded 𝕜) (Bornology.cobounded 𝕜) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  have h1 : Tendsto (fun x : 𝕜 => ‖α‖ * ‖x‖ - ‖β‖) (Bornology.cobounded 𝕜) atTop :=
    tendsto_atTop_add_const_right _ _
      (tendsto_norm_cobounded_atTop.const_mul_atTop (norm_pos_iff.2 hα))
  refine tendsto_atTop_mono (fun x => ?_) h1
  have h2 : ‖α * x‖ ≤ ‖α * x + β‖ + ‖β‖ := by simpa using norm_add_le (α * x + β) (-β)
  rw [norm_mul] at h2
  show ‖α‖ * ‖x‖ - ‖β‖ ≤ ‖α * x + β‖
  linarith

/-- The boundary action of a real Möbius map is continuous on `ℝ ∪ {∞}`. -/
theorem continuous_mobiusBdry (h : a * d - b * c ≠ 0) : Continuous (mobiusBdry a b c d) := by
  rw [OnePoint.continuous_iff]
  constructor
  · rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    by_cases hc : c = 0
    · subst hc
      have hd : d ≠ 0 := by rintro rfl; simp at h
      have ha : a ≠ 0 := by rintro rfl; simp at h
      simp only [mobiusBdry_coe, mobiusBdry_infty, zero_mul, zero_add, hd, ite_false, ite_true]
      have e : ∀ x : ℝ, (a * x + b) / d = a / d * x + b / d := fun x => by field_simp
      simp only [e]
      exact tendsto_coe_cobounded_onePoint.comp
        (tendsto_affine_cobounded (div_ne_zero ha hd))
    · simp only [mobiusBdry_infty, hc, ite_false]
      have hev : ∀ᶠ x : ℝ in Bornology.cobounded ℝ, c * x + d ≠ 0 ∧ x ≠ 0 := by
        have h2 : ({0}ᶜ : Set ℝ) ∈ Bornology.cobounded ℝ :=
          Bornology.isBounded_def.1 Bornology.isBounded_singleton
        have h1 := (tendsto_affine_cobounded (β := d) hc).eventually h2
        filter_upwards [h1, h2] with x hx1 hx2
        exact ⟨hx1, hx2⟩
      have hlim : Tendsto (fun x : ℝ => (a + b * x⁻¹) / (c + d * x⁻¹)) (Bornology.cobounded ℝ)
          (𝓝 (a / c)) := by
        have h0 := tendsto_inv₀_cobounded (α := ℝ)
        have := ((tendsto_const_nhds (x := a)).add (h0.const_mul b)).div
          ((tendsto_const_nhds (x := c)).add (h0.const_mul d)) (by simpa using hc)
        simp only [mul_zero, add_zero] at this
        exact this
      refine ((OnePoint.continuous_coe.tendsto _).comp hlim).congr' ?_
      filter_upwards [hev] with x hx
      simp only [Function.comp_apply, mobiusBdry_coe, hx.1, ite_false]
      congr 1
      field_simp [hx.2]
  · rw [continuous_iff_continuousAt]
    intro x₀
    by_cases hx : c * x₀ + d = 0
    · have hc : c ≠ 0 := by
        rintro rfl
        have : d = 0 := by simpa using hx
        subst this; simp at h
      have hn : a * x₀ + b ≠ 0 := by
        intro hn
        apply h
        have hd : d = -(c * x₀) := by linarith
        have hb : b = -(a * x₀) := by linarith
        rw [hd, hb]; ring
      rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
      simp only [mobiusBdry_coe, hx, ite_true]
      have hne : ∀ᶠ x in 𝓝[≠] x₀, c * x + d ≠ 0 := by
        filter_upwards [self_mem_nhdsWithin] with x hx'
        intro h0
        have : c * (x - x₀) = 0 := by linarith
        rcases mul_eq_zero.1 this with h1 | h1
        · exact hc h1
        · exact hx' (sub_eq_zero.1 h1)
      have hq : Tendsto (fun x : ℝ => (c * x + d) / (a * x + b)) (𝓝[≠] x₀) (𝓝[≠] 0) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · have : ContinuousAt (fun x : ℝ => (c * x + d) / (a * x + b)) x₀ := by
            fun_prop (disch := exact hn)
          have h2 := this.tendsto.mono_left (nhdsWithin_le_nhds (s := ({x₀}ᶜ : Set ℝ)))
          simpa [hx] using h2
        · have hn' : ∀ᶠ x in 𝓝[≠] x₀, a * x + b ≠ 0 := by
            have : ContinuousAt (fun x : ℝ => a * x + b) x₀ := by fun_prop
            exact nhdsWithin_le_nhds (this.eventually_ne hn)
          filter_upwards [hne, hn'] with x h1 h2
          exact div_ne_zero h1 h2
      have hinf := tendsto_coe_cobounded_onePoint.comp (tendsto_inv₀_nhdsNE_zero.comp hq)
      refine hinf.congr' ?_
      filter_upwards [hne] with x hx'
      simp only [Function.comp_apply, hx', ite_false, inv_div]
    · have hev : ∀ᶠ x in 𝓝 x₀, c * x + d ≠ 0 := by
        have : ContinuousAt (fun x : ℝ => c * x + d) x₀ := by fun_prop
        exact this.eventually_ne hx
      have hg : ContinuousAt (fun x : ℝ => (((a * x + b) / (c * x + d) : ℝ) : OnePoint ℝ)) x₀ :=
        OnePoint.continuous_coe.continuousAt.comp (f := fun x : ℝ => (a * x + b) / (c * x + d))
          (by fun_prop (disch := exact hx))
      refine hg.congr ?_
      filter_upwards [hev] with x hx'
      simp only [mobiusBdry_coe, hx', ite_false]

/-- The boundary action of a real Möbius map with nonzero determinant, as a homeomorphism of
`ℝ ∪ {∞}`; its inverse is the action of the inverse matrix. -/
def mobiusBdryHomeomorph (a b c d : ℝ) (h : a * d - b * c ≠ 0) : OnePoint ℝ ≃ₜ OnePoint ℝ where
  toFun := mobiusBdry a b c d
  invFun := mobiusBdry d (-b) (-c) a
  left_inv := mobiusBdry_inv_apply h
  right_inv := mobiusBdry_apply_inv h
  continuous_toFun := continuous_mobiusBdry h
  continuous_invFun := continuous_mobiusBdry (by
    rw [show d * a - (-b) * (-c) = a * d - b * c by ring]; exact h)

@[simp] theorem mobiusBdryHomeomorph_apply (h : a * d - b * c ≠ 0) (p : OnePoint ℝ) :
    mobiusBdryHomeomorph a b c d h p = mobiusBdry a b c d p := rfl

end MobiusBdry

/-! ### Real Möbius maps of the upper half-plane -/

section RealMobius

variable {a b c d : ℝ}

theorem realMobius_one_zero_zero_one (z : ℂ) : realMobius 1 0 0 1 z = z := by
  simp [QuantumZipper.CA.realMobius]

/-- Composition of real Möbius maps is the Möbius map of the product matrix (wherever the inner
denominator does not vanish). -/
theorem realMobius_realMobius {a' b' c' d' : ℝ} {z : ℂ} (hz : (c' : ℂ) * z + d' ≠ 0) :
    realMobius a b c d (realMobius a' b' c' d' z) =
      realMobius (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') z := by
  simp only [QuantumZipper.CA.realMobius]
  have hz' : (z * c' + d' : ℂ) ≠ 0 := by rwa [mul_comm]
  rw [show (a : ℂ) * ((a' * z + b') / (c' * z + d')) + b =
      (a * (a' * z + b') + b * (c' * z + d')) / (c' * z + d') by field_simp,
    show (c : ℂ) * ((a' * z + b') / (c' * z + d')) + d =
      (c * (a' * z + b') + d * (c' * z + d')) / (c' * z + d') by field_simp,
    div_div_div_cancel_right₀ hz]
  push_cast
  congr 1 <;> ring

/-- A real Möbius map with positive determinant that fixes every point of `ℍ` is a scalar
matrix. -/
theorem realMobius_eqOn_id (h : 0 < a * d - b * c) (hid : EqOn (realMobius a b c d) id H) :
    b = 0 ∧ c = 0 ∧ a = d := by
  have hI : I ∈ H := by show (0 : ℝ) < I.im; simp
  have h2I : 2 * I ∈ H := by show (0 : ℝ) < (2 * I).im; simp
  have e1 := hid hI
  have e2 := hid h2I
  simp only [QuantumZipper.CA.realMobius, id] at e1 e2
  rw [div_eq_iff (QuantumZipper.CA.realMobius_denom_ne_zero h hI)] at e1
  rw [div_eq_iff (QuantumZipper.CA.realMobius_denom_ne_zero h h2I)] at e2
  have r1 := congrArg Complex.re e1
  have i1 := congrArg Complex.im e1
  have r2 := congrArg Complex.re e2
  simp at r1 i1 r2
  refine ⟨by linarith, by linarith, by linarith⟩

/-- If a real Möbius map with positive determinant fixes `ℍ` pointwise, its boundary action is the
identity. -/
theorem mobiusBdry_eq_id_of_eqOn (h : 0 < a * d - b * c) (hid : EqOn (realMobius a b c d) id H) :
    mobiusBdry a b c d = id := by
  obtain ⟨rfl, rfl, rfl⟩ := realMobius_eqOn_id h hid
  have ha : a ≠ 0 := by rintro rfl; simp at h
  have := mobiusBdry_mul_left ha 1 0 0 1
  simp only [mul_one, mul_zero] at this
  rw [this]
  funext p
  exact mobiusBdry_one_zero_zero_one p

end RealMobius

/-! ### Half-plane charts -/

/-- Uniformizing half-plane charts of `D` (Specification p. 10: `ψ : D → ℍ`). -/
def HChart (D : Set ℂ) : Type := {ψ : ℂ → ℂ // IsConformalBijection ψ D H}

namespace HChart

variable {D : Set ℂ} (ψ : HChart D)

theorem differentiableOn : DifferentiableOn ℂ ψ.1 D := ψ.2.1

theorem bijOn : BijOn ψ.1 D H := ψ.2.2

theorem mapsTo : MapsTo ψ.1 D H := ψ.bijOn.mapsTo

theorem injOn : InjOn ψ.1 D := ψ.bijOn.injOn

theorem surjOn : SurjOn ψ.1 D H := ψ.bijOn.surjOn

theorem invFunOn_mem {ζ : ℂ} (hζ : ζ ∈ H) : invFunOn ψ.1 D ζ ∈ D :=
  (invFunOn_pos (ψ.surjOn hζ)).1

theorem apply_invFunOn {ζ : ℂ} (hζ : ζ ∈ H) : ψ.1 (invFunOn ψ.1 D ζ) = ζ :=
  (invFunOn_pos (ψ.surjOn hζ)).2

theorem invFunOn_apply {z : ℂ} (hz : z ∈ D) : invFunOn ψ.1 D (ψ.1 z) = z :=
  ψ.injOn.leftInvOn_invFunOn hz

/-- If `φ = m ∘ ψ` on `D` for a real Möbius `m`, the inverse charts satisfy
`ψ⁻¹ = φ⁻¹ ∘ m` on `ℍ`. -/
theorem invFunOn_eq_invFunOn_realMobius (φ : HChart D) {a b c d : ℝ}
    (hφ : EqOn φ.1 (realMobius a b c d ∘ ψ.1) D) {ζ : ℂ} (hζ : ζ ∈ H) :
    invFunOn ψ.1 D ζ = invFunOn φ.1 D (realMobius a b c d ζ) := by
  have hz := ψ.invFunOn_mem hζ
  have : realMobius a b c d ζ = φ.1 (invFunOn ψ.1 D ζ) := by
    rw [hφ hz, Function.comp_apply, ψ.apply_invFunOn hζ]
  rw [this, φ.invFunOn_apply hz]

/-- Two charts of an open domain differ by a real Möbius map of positive determinant. -/
theorem exists_realMobius (hD : IsOpen D) (φ : HChart D) :
    ∃ a b c d : ℝ, 0 < a * d - b * c ∧ EqOn φ.1 (realMobius a b c d ∘ ψ.1) D := by
  set e := QuantumZipper.CA.univalentOPH hD ψ.differentiableOn ψ.injOn
  have himg : ψ.1 '' D = H := ψ.bijOn.image_eq
  have hsymm_mem : ∀ ζ ∈ H, e.symm ζ ∈ D := fun ζ hζ => by
    have : ζ ∈ e.target := by
      rw [QuantumZipper.CA.univalentOPH_target, himg]; exact hζ
    exact e.map_target this
  have hψe : ∀ ζ ∈ H, ψ.1 (e.symm ζ) = ζ := fun ζ hζ =>
    QuantumZipper.CA.univalentOPH_apply_symm_apply hD ψ.differentiableOn ψ.injOn
      (by rw [himg]; exact hζ)
  have heψ : ∀ z ∈ D, e.symm (ψ.1 z) = z := fun z hz =>
    QuantumZipper.CA.univalentOPH_symm_apply_apply hD ψ.differentiableOn ψ.injOn hz
  have hdiff : DifferentiableOn ℂ (φ.1 ∘ e.symm) H := by
    have hs := QuantumZipper.CA.differentiableOn_univalentOPH_symm hD ψ.differentiableOn ψ.injOn
    rw [himg] at hs
    intro ζ hζ
    have h1 : DifferentiableAt ℂ φ.1 (e.symm ζ) :=
      φ.differentiableOn.differentiableAt (hD.mem_nhds (hsymm_mem ζ hζ))
    have h2 : DifferentiableAt ℂ e.symm ζ :=
      (hs ζ hζ).differentiableAt (QuantumZipper.isOpen_H.mem_nhds hζ)
    exact (h1.comp ζ h2).differentiableWithinAt
  have hbij : BijOn (φ.1 ∘ e.symm) H H := by
    refine ⟨fun ζ hζ => φ.mapsTo (hsymm_mem ζ hζ), fun ζ hζ ζ' hζ' hEq => ?_, fun w hw => ?_⟩
    · have := φ.injOn (hsymm_mem ζ hζ) (hsymm_mem ζ' hζ') hEq
      rw [← hψe ζ hζ, ← hψe ζ' hζ', this]
    · obtain ⟨z, hz, rfl⟩ := φ.surjOn hw
      exact ⟨ψ.1 z, ψ.mapsTo hz, by rw [Function.comp_apply, heψ z hz]⟩
  obtain ⟨a, b, c, d, hdet, hEq⟩ := QuantumZipper.CA.exists_realMobius_of_bijOn_H hdiff hbij
  refine ⟨a, b, c, d, hdet, fun z hz => ?_⟩
  have := hEq (ψ.mapsTo hz)
  rw [Function.comp_apply, heψ z hz] at this
  rw [Function.comp_apply, ← this]

end HChart

/-! ### Prime ends -/

/-- Two marked charts `(ψ, x)` and `(ψ', x')` mark the same prime end: `ψ' = m ∘ ψ` on `D` for a
real Möbius `m` whose boundary action sends `x` to `x'`. -/
def PrimeEnd.Rel (D : Set ℂ) (p q : HChart D × OnePoint ℝ) : Prop :=
  ∃ a b c d : ℝ, 0 < a * d - b * c ∧
    EqOn q.1.1 (QuantumZipper.CA.realMobius a b c d ∘ p.1.1) D ∧ mobiusBdry a b c d p.2 = q.2

/-- **Prime ends** of a simply connected proper domain, through their conformal-chart
description (Carathéodory's prime-end theorem: the prime ends of `D` correspond bijectively,
through any conformal `ψ : D → ℍ`, to `ℝ ∪ {∞}`; Pommerenke, *Boundary behaviour of conformal
maps*, Thm 2.15). Empty when `D` has no chart. Specification p. 2: "boundary markings used in
conformal maps are prime ends". -/
def PrimeEnd (D : Set ℂ) : Type := Quot (PrimeEnd.Rel D)

namespace PrimeEnd

variable {D : Set ℂ}

/-- The prime end marked by the boundary point `x` of the chart `ψ`. -/
def mk (ψ : HChart D) (x : OnePoint ℝ) : PrimeEnd D := Quot.mk _ (ψ, x)

theorem rel_refl (p : HChart D × OnePoint ℝ) : Rel D p p :=
  ⟨1, 0, 0, 1, by norm_num, fun z _ => by rw [Function.comp_apply, realMobius_one_zero_zero_one],
    mobiusBdry_one_zero_zero_one _⟩

theorem rel_symm {p q : HChart D × OnePoint ℝ} (h : Rel D p q) : Rel D q p := by
  obtain ⟨a, b, c, d, hdet, hEq, hx⟩ := h
  refine ⟨d, -b, -c, a, by linarith, fun z hz => ?_, ?_⟩
  · rw [Function.comp_apply, hEq hz, Function.comp_apply,
      QuantumZipper.CA.realMobius_inv_apply hdet (p.1.mapsTo hz)]
  · rw [← hx, mobiusBdry_inv_apply hdet.ne']

theorem rel_trans {p q r : HChart D × OnePoint ℝ} (h₁ : Rel D p q) (h₂ : Rel D q r) :
    Rel D p r := by
  obtain ⟨a, b, c, d, hdet, hEq, hx⟩ := h₁
  obtain ⟨a', b', c', d', hdet', hEq', hx'⟩ := h₂
  refine ⟨a' * a + b' * c, a' * b + b' * d, c' * a + d' * c, c' * b + d' * d, ?_,
    fun z hz => ?_, ?_⟩
  · have : (a' * a + b' * c) * (c' * b + d' * d) - (a' * b + b' * d) * (c' * a + d' * c) =
        (a' * d' - b' * c') * (a * d - b * c) := by ring
    rw [this]; exact mul_pos hdet' hdet
  · rw [hEq' hz, Function.comp_apply, hEq hz, Function.comp_apply, Function.comp_apply,
      realMobius_realMobius (QuantumZipper.CA.realMobius_denom_ne_zero hdet (p.1.mapsTo hz))]
  · rw [← hx', ← hx, mobiusBdry_mobiusBdry hdet'.ne' hdet.ne']

theorem rel_equivalence : Equivalence (Rel D) :=
  ⟨rel_refl, rel_symm, rel_trans⟩

theorem mk_eq_mk_iff {ψ φ : HChart D} {x y : OnePoint ℝ} :
    mk ψ x = mk φ y ↔ Rel D (ψ, x) (φ, y) :=
  ⟨fun h => rel_equivalence.eqvGen_iff.1 (Quot.eqvGen_exact h), fun h => Quot.sound h⟩

theorem mk_mobiusBdry {ψ φ : HChart D} {a b c d : ℝ} (hdet : 0 < a * d - b * c)
    (hEq : EqOn φ.1 (realMobius a b c d ∘ ψ.1) D) (x : OnePoint ℝ) :
    mk φ (mobiusBdry a b c d x) = mk ψ x :=
  (Quot.sound ⟨a, b, c, d, hdet, hEq, rfl⟩).symm

/-- Each chart describes distinct prime ends at distinct boundary points (any `D`). -/
theorem mk_injective (ψ : HChart D) : Injective (mk ψ) := by
  intro x y hxy
  obtain ⟨a, b, c, d, hdet, hEq, hx⟩ := mk_eq_mk_iff.1 hxy
  have hid : EqOn (realMobius a b c d) id H := by
    intro ζ hζ
    obtain ⟨z, hz, rfl⟩ := ψ.surjOn hζ
    exact (hEq hz).symm
  rw [mobiusBdry_eq_id_of_eqOn hdet hid] at hx
  exact hx

/-- On an open domain, each chart describes every prime end. -/
theorem mk_surjective_of_isOpen (hD : IsOpen D) (ψ : HChart D) : Surjective (mk ψ) := by
  rintro ⟨φ, y⟩
  obtain ⟨a, b, c, d, hdet, hEq⟩ := ψ.exists_realMobius hD φ
  refine ⟨mobiusBdry d (-b) (-c) a y, ?_⟩
  have := mk_mobiusBdry hdet hEq (mobiusBdry d (-b) (-c) a y)
  rw [mobiusBdry_apply_inv hdet.ne'] at this
  exact this.symm

/-- **Every chart describes every prime end exactly once** (open domains). This is the design's
`PrimeEnd.mk_bijective` with the hypothesis `IsOpen D` added: without it the statement is false
(see the module docstring). -/
theorem mk_bijective_of_isOpen (hD : IsOpen D) (ψ : HChart D) : Bijective (mk ψ) :=
  ⟨mk_injective ψ, mk_surjective_of_isOpen hD ψ⟩

/-- The final topology of all charts (all charts induce the same one). -/
instance : TopologicalSpace (PrimeEnd D) :=
  ⨅ ψ : HChart D, TopologicalSpace.coinduced (mk ψ) inferInstance

/-- On an open domain, any two charts coinduce the same topology. -/
theorem coinduced_mk_eq (hD : IsOpen D) (ψ φ : HChart D) :
    TopologicalSpace.coinduced (mk ψ) (inferInstance : TopologicalSpace (OnePoint ℝ)) =
      TopologicalSpace.coinduced (mk φ) inferInstance := by
  obtain ⟨a, b, c, d, hdet, hEq⟩ := ψ.exists_realMobius hD φ
  have hcomp : mk ψ = mk φ ∘ mobiusBdryHomeomorph a b c d hdet.ne' := by
    funext x
    exact (mk_mobiusBdry hdet hEq x).symm
  rw [hcomp, ← coinduced_compose, Homeomorph.coinduced_eq]

/-- On an open domain, the topology of `PrimeEnd D` is the one coinduced by any chart. -/
theorem topology_eq_coinduced (hD : IsOpen D) (ψ : HChart D) :
    (inferInstance : TopologicalSpace (PrimeEnd D)) =
      TopologicalSpace.coinduced (mk ψ) inferInstance :=
  le_antisymm (iInf_le _ ψ) (le_iInf fun φ => (coinduced_mk_eq hD ψ φ).le)

/-- On an open domain, every chart is a homeomorphism `ℝ ∪ {∞} ≃ₜ PrimeEnd D`. -/
def mkHomeomorph (hD : IsOpen D) (ψ : HChart D) : OnePoint ℝ ≃ₜ PrimeEnd D where
  toEquiv := Equiv.ofBijective (mk ψ) (mk_bijective_of_isOpen hD ψ)
  continuous_toFun := by
    rw [continuous_iff_coinduced_le]
    exact (topology_eq_coinduced hD ψ).ge
  continuous_invFun := by
    have key : @Continuous _ _ (TopologicalSpace.coinduced (mk ψ) inferInstance) _
        (Equiv.ofBijective (mk ψ) (mk_bijective_of_isOpen hD ψ)).symm := by
      rw [continuous_coinduced_dom]
      have : (Equiv.ofBijective (mk ψ) (mk_bijective_of_isOpen hD ψ)).symm ∘ mk ψ = id := by
        funext x
        exact (Equiv.ofBijective (mk ψ) (mk_bijective_of_isOpen hD ψ)).symm_apply_apply x
      rw [this]
      exact continuous_id
    rw [continuous_iff_coinduced_le] at key ⊢
    exact le_trans (le_of_eq (congrArg _ (topology_eq_coinduced hD ψ))) key

@[simp] theorem mkHomeomorph_apply (hD : IsOpen D) (ψ : HChart D) (x : OnePoint ℝ) :
    mkHomeomorph hD ψ x = mk ψ x := rfl

theorem continuous_mk (hD : IsOpen D) (ψ : HChart D) : Continuous (mk ψ) :=
  (mkHomeomorph hD ψ).continuous

/-- Without charts there are no prime ends. -/
theorem isEmpty_of_isEmpty_hChart (h : IsEmpty (HChart D)) : IsEmpty (PrimeEnd D) :=
  ⟨fun p => Quot.ind (β := fun _ => False) (fun q => h.elim q.1) p⟩

/-- The prime ends of an open domain form a compact space. -/
theorem compactSpace_of_isOpen (hD : IsOpen D) : CompactSpace (PrimeEnd D) := by
  rcases isEmpty_or_nonempty (HChart D) with h | ⟨⟨ψ⟩⟩
  · have := isEmpty_of_isEmpty_hChart h
    infer_instance
  · exact (mkHomeomorph hD ψ).compactSpace

/-- The prime ends of an open domain form a Hausdorff space. -/
theorem t2Space_of_isOpen (hD : IsOpen D) : T2Space (PrimeEnd D) := by
  rcases isEmpty_or_nonempty (HChart D) with h | ⟨⟨ψ⟩⟩
  · have := isEmpty_of_isEmpty_hChart h
    infer_instance
  · exact (mkHomeomorph hD ψ).symm.isEmbedding.t2Space

/-- The approach filter in `ℍ` to a boundary point of `ℍ` in `ℝ ∪ {∞}`. -/
def approachH (x : OnePoint ℝ) : Filter ℂ :=
  x.elim (Bornology.cobounded ℂ ⊓ 𝓟 H) fun r => 𝓝[H] (r : ℂ)

@[simp] theorem approachH_infty : approachH OnePoint.infty = Bornology.cobounded ℂ ⊓ 𝓟 H := rfl

@[simp] theorem approachH_coe (r : ℝ) : approachH (r : OnePoint ℝ) = 𝓝[H] (r : ℂ) := rfl

theorem H_mem_approachH (x : OnePoint ℝ) : H ∈ approachH x := by
  cases x with
  | infty => exact mem_inf_of_right (mem_principal_self H)
  | coe r => exact self_mem_nhdsWithin

/-- `w ∈ ℂ` is the **Euclidean realization** of the prime end `p`: the inverse of a chart extends
continuously at the marked point with value `w` (Specification p. 2: "their Euclidean
realizations require the stated boundary-extension hypotheses"). -/
def IsRealizedAt (p : PrimeEnd D) (w : ℂ) : Prop :=
  ∃ ψ : HChart D, ∃ x : OnePoint ℝ, mk ψ x = p ∧
    Tendsto (Function.invFunOn ψ.1 D) (approachH x) (𝓝 w)

/-- A real Möbius map of positive determinant carries the approach filter at `x` to the approach
filter at its boundary image `mobiusBdry a b c d x`. -/
theorem tendsto_realMobius_approachH {a b c d : ℝ} (hdet : 0 < a * d - b * c) (x : OnePoint ℝ) :
    Tendsto (realMobius a b c d) (approachH x) (approachH (mobiusBdry a b c d x)) := by
  have hH : ∀ᶠ z in approachH x, realMobius a b c d z ∈ H :=
    Filter.mem_of_superset (H_mem_approachH x) fun z hz =>
      QuantumZipper.CA.realMobius_mem_H hdet hz
  cases x with
  | infty =>
    by_cases hc : c = 0
    · subst hc
      have hd : d ≠ 0 := by rintro rfl; simp at hdet
      have ha : a ≠ 0 := by rintro rfl; simp at hdet
      simp only [mobiusBdry_infty, ite_true, approachH_infty]
      refine tendsto_inf.2 ⟨?_, tendsto_principal.2 hH⟩
      have e : realMobius a b 0 d = fun z => ((a / d : ℝ) : ℂ) * z + ((b / d : ℝ) : ℂ) := by
        funext z
        have hd' : (d : ℂ) ≠ 0 := ofReal_ne_zero.2 hd
        simp only [QuantumZipper.CA.realMobius, ofReal_zero, zero_mul, zero_add, ofReal_div]
        field_simp
      rw [e]
      exact (tendsto_affine_cobounded (ofReal_ne_zero.2 (div_ne_zero ha hd))).mono_left
        inf_le_left
    · simp only [mobiusBdry_infty, hc, ite_false, approachH_coe]
      refine tendsto_nhdsWithin_iff.2 ⟨?_, hH⟩
      have hc' : (c : ℂ) ≠ 0 := ofReal_ne_zero.2 hc
      have hlim : Tendsto (fun z : ℂ => ((a : ℂ) + b * z⁻¹) / (c + d * z⁻¹))
          (Bornology.cobounded ℂ) (𝓝 ((a / c : ℝ) : ℂ)) := by
        have h0 := tendsto_inv₀_cobounded (α := ℂ)
        have := ((tendsto_const_nhds (x := (a : ℂ))).add (h0.const_mul (b : ℂ))).div
          ((tendsto_const_nhds (x := (c : ℂ))).add (h0.const_mul (d : ℂ))) (by simpa using hc')
        simp only [mul_zero, add_zero] at this
        push_cast
        exact this
      refine (hlim.mono_left inf_le_left).congr' ?_
      have h2 : ({0}ᶜ : Set ℂ) ∈ Bornology.cobounded ℂ :=
        Bornology.isBounded_def.1 Bornology.isBounded_singleton
      filter_upwards [mem_inf_of_left h2, H_mem_approachH OnePoint.infty] with z hz hzH
      have hz0 : z ≠ 0 := hz
      have hden := QuantumZipper.CA.realMobius_denom_ne_zero hdet hzH
      simp only [QuantumZipper.CA.realMobius]
      field_simp
  | coe r =>
    simp only [mobiusBdry_coe, approachH_coe]
    by_cases hr : c * r + d = 0
    · simp only [hr, ite_true, approachH_infty]
      refine tendsto_inf.2 ⟨?_, tendsto_principal.2 hH⟩
      have hn : a * r + b ≠ 0 := by
        intro hn
        apply hdet.ne'
        have hd : d = -(c * r) := by linarith
        have hb : b = -(a * r) := by linarith
        rw [hd, hb]; ring
      have hn' : (a : ℂ) * r + b ≠ 0 := by exact_mod_cast hn
      have hq : Tendsto (fun z : ℂ => ((c : ℂ) * z + d) / (a * z + b)) (𝓝[H] (r : ℂ)) (𝓝[≠] 0) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · have hcont : ContinuousAt (fun z : ℂ => ((c : ℂ) * z + d) / (a * z + b)) (r : ℂ) := by
            fun_prop (disch := exact hn')
          have h2 := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := H))
          have hr' : (c : ℂ) * r + d = 0 := by exact_mod_cast hr
          simpa [hr'] using h2
        · have hn'' : ∀ᶠ z in 𝓝[H] (r : ℂ), (a : ℂ) * z + b ≠ 0 := by
            have : ContinuousAt (fun z : ℂ => (a : ℂ) * z + b) (r : ℂ) := by fun_prop
            exact nhdsWithin_le_nhds (this.eventually_ne hn')
          filter_upwards [hn'', self_mem_nhdsWithin] with z h1 hzH
          exact div_ne_zero (QuantumZipper.CA.realMobius_denom_ne_zero hdet hzH) h1
      refine (tendsto_inv₀_nhdsNE_zero.comp hq).congr' ?_
      filter_upwards with z
      simp only [Function.comp_apply, inv_div, QuantumZipper.CA.realMobius]
    · simp only [hr, ite_false, approachH_coe]
      refine tendsto_nhdsWithin_iff.2 ⟨?_, hH⟩
      have hr' : (c : ℂ) * r + d ≠ 0 := by exact_mod_cast hr
      have hcont : ContinuousAt (realMobius a b c d) (r : ℂ) := by
        unfold QuantumZipper.CA.realMobius
        fun_prop (disch := exact hr')
      have hval : realMobius a b c d (r : ℂ) = (((a * r + b) / (c * r + d) : ℝ) : ℂ) := by
        simp only [QuantumZipper.CA.realMobius]
        push_cast
        rfl
      rw [← hval]
      exact hcont.tendsto.mono_left nhdsWithin_le_nhds

/-- **Chart independence of the realization**, at a marked point of a given chart (any `D`). -/
theorem isRealizedAt_mk_iff (ψ : HChart D) (x : OnePoint ℝ) (w : ℂ) :
    (mk ψ x).IsRealizedAt w ↔ Tendsto (Function.invFunOn ψ.1 D) (approachH x) (𝓝 w) := by
  refine ⟨?_, fun h => ⟨ψ, x, rfl, h⟩⟩
  rintro ⟨φ, y, hφy, hT⟩
  obtain ⟨a, b, c, d, hdet, hEq, hxy⟩ := mk_eq_mk_iff.1 hφy.symm
  have hM := tendsto_realMobius_approachH hdet x
  rw [show mobiusBdry a b c d x = y from hxy] at hM
  refine (hT.comp hM).congr' ?_
  filter_upwards [H_mem_approachH x] with ζ hζ
  exact (ψ.invFunOn_eq_invFunOn_realMobius φ hEq hζ).symm

/-- **Chart independence of the realization** (open domains). This is the design's
`PrimeEnd.isRealizedAt_iff`, whose statement refers to `mk_bijective`; here it refers to
`mk_bijective_of_isOpen`. -/
theorem isRealizedAt_iff_of_isOpen (hD : IsOpen D) (p : PrimeEnd D) (w : ℂ) (ψ : HChart D) :
    p.IsRealizedAt w ↔
      Tendsto (Function.invFunOn ψ.1 D)
        (approachH ((mk_bijective_of_isOpen hD ψ).2 p).choose) (𝓝 w) := by
  conv_lhs => rw [← ((mk_bijective_of_isOpen hD ψ).2 p).choose_spec]
  exact isRealizedAt_mk_iff ψ _ w

/-- Every approach filter is nontrivial. -/
theorem approachH_neBot (x : OnePoint ℝ) : (approachH x).NeBot := by
  cases x with
  | infty =>
    rw [approachH_infty, inf_principal_neBot_iff]
    intro U hU
    obtain ⟨R, hR⟩ := (Bornology.isBounded_def.2 (by simpa using hU) :
      Bornology.IsBounded Uᶜ).subset_closedBall 0
    refine ⟨((|R| + 1 : ℝ) : ℂ) * I, ?_, ?_⟩
    · by_contra hmem
      have := hR hmem
      rw [mem_closedBall, dist_zero_right, norm_mul, norm_I, mul_one, norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)] at this
      linarith [le_abs_self R]
    · show (0 : ℝ) < (((|R| + 1 : ℝ) : ℂ) * I).im
      simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      positivity
  | coe r =>
    rw [approachH_coe, ← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
    intro ε hε
    refine ⟨r + ((ε / 2 : ℝ) : ℂ) * I, ?_, ?_⟩
    · show (0 : ℝ) < ((r : ℂ) + ((ε / 2 : ℝ) : ℂ) * I).im
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add]
      positivity
    · rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_mul, norm_I, mul_one, norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith

/-- A prime end has at most one Euclidean realization. -/
theorem IsRealizedAt.unique {p : PrimeEnd D} {w w' : ℂ} (hw : p.IsRealizedAt w)
    (hw' : p.IsRealizedAt w') : w = w' := by
  obtain ⟨ψ, x, rfl, hT⟩ := hw
  have := approachH_neBot x
  exact tendsto_nhds_unique hT ((isRealizedAt_mk_iff ψ x w').1 hw')

/-! ### The design's `mk_bijective` needs `IsOpen D` -/

/-- The non-open domain `(ℍ \ {i, 2i}) ∪ {-i, -2i}` of the counterexample. -/
def ceDomain : Set ℂ := (H \ {I, 2 * I}) ∪ {-I, -(2 * I)}

/-- A chart of `ceDomain`: the identity off `{-i, -2i}`, `-i ↦ i`, `-2i ↦ 2i`. -/
def ceChart₁ (w : ℂ) : ℂ := if w = -I then I else if w = -(2 * I) then 2 * I else w

/-- A second chart of `ceDomain`: the identity off `{-i, -2i}`, `-i ↦ 2i`, `-2i ↦ i`. -/
def ceChart₂ (w : ℂ) : ℂ := if w = -I then 2 * I else if w = -(2 * I) then I else w

private theorem I_mem_H' : I ∈ H := by show (0 : ℝ) < I.im; simp

private theorem two_I_mem_H : 2 * I ∈ H := by show (0 : ℝ) < (2 * I).im; simp

private theorem notMem_H_of_im_neg {z : ℂ} (hz : z.im < 0) : z ∉ H := fun h => by
  have : (0 : ℝ) < z.im := h; linarith

private theorem neg_I_notMem_H : -I ∉ H := notMem_H_of_im_neg (by simp)

private theorem neg_two_I_notMem_H : -(2 * I) ∉ H := notMem_H_of_im_neg (by simp)

/-- Differentiability within `ceDomain` of a map that is the identity off `{-i, -2i}`. -/
private theorem differentiableOn_ceDomain {f : ℂ → ℂ}
    (hf : ∀ w, w ≠ -I → w ≠ -(2 * I) → f w = w) :
    DifferentiableOn ℂ f ceDomain := by
  intro z hz
  rcases hz with ⟨hzH, -⟩ | hz
  · have hz1 : z ≠ -I := fun h => neg_I_notMem_H (h ▸ hzH)
    have hz2 : z ≠ -(2 * I) := fun h => neg_two_I_notMem_H (h ▸ hzH)
    have hU : ({-I, -(2 * I)}ᶜ : Set ℂ) ∈ 𝓝 z :=
      (Set.toFinite _).isClosed.isOpen_compl.mem_nhds (by simp [hz1, hz2])
    have : f =ᶠ[𝓝 z] id := Filter.mem_of_superset hU fun w hw => by
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hw
      exact hf w hw.1 hw.2
    exact (differentiableAt_id.congr_of_eventuallyEq this).differentiableWithinAt
  · -- isolated points: `ceDomain ∩ ball z (1/2) = {z}`
    have hiso : ceDomain ∩ ball z (1 / 2) ⊆ {z} := by
      rintro w ⟨hw, hwz⟩
      rw [mem_ball, dist_eq_norm] at hwz
      have him : |(w - z).im| < 1 / 2 := lt_of_le_of_lt (abs_im_le_norm _) hwz
      rcases hz with rfl | rfl <;> rcases hw with ⟨hwH, -⟩ | hw
      · have : (0 : ℝ) < w.im := hwH
        rw [sub_im, abs_lt] at him; simp at him; linarith
      · rcases hw with rfl | rfl
        · rfl
        · rw [abs_lt] at him; norm_num at him
      · have : (0 : ℝ) < w.im := hwH
        rw [sub_im, abs_lt] at him; simp at him; linarith
      · rcases hw with rfl | rfl
        · rw [abs_lt] at him; norm_num at him
        · rfl
    rw [← differentiableWithinAt_inter (ball_mem_nhds z (by norm_num : (0 : ℝ) < 1 / 2))]
    exact ((hasFDerivWithinAt_singleton f z).differentiableWithinAt).mono hiso

private theorem ceChart₁_spec (w : ℂ) (h1 : w ≠ -I) (h2 : w ≠ -(2 * I)) :
    ceChart₁ w = w := by
  simp [ceChart₁, h1, h2]

private theorem ceChart₂_spec (w : ℂ) (h1 : w ≠ -I) (h2 : w ≠ -(2 * I)) :
    ceChart₂ w = w := by
  simp [ceChart₂, h1, h2]

private theorem neg_I_ne_neg_two_I : -I ≠ -(2 * I) := by
  intro h; have := congrArg Complex.im h; norm_num at this

private theorem I_ne_two_I : I ≠ 2 * I := by
  intro h; have := congrArg Complex.im h; norm_num at this

private theorem ne_neg_I_of_mem_H {w : ℂ} (hw : w ∈ H) : w ≠ -I := fun h =>
  neg_I_notMem_H (h ▸ hw)

private theorem ne_neg_two_I_of_mem_H {w : ℂ} (hw : w ∈ H) : w ≠ -(2 * I) := fun h =>
  neg_two_I_notMem_H (h ▸ hw)

/-- A map that is the identity on `ℍ \ {i, 2i}` and sends `{-i, -2i}` bijectively onto `{i, 2i}`
is a bijection `ceDomain → ℍ`. -/
private theorem bijOn_ceDomain {f : ℂ → ℂ} (hf : ∀ w, w ≠ -I → w ≠ -(2 * I) → f w = w)
    {u v : ℂ} (hu : f (-I) = u) (hv : f (-(2 * I)) = v)
    (huv : (u = I ∧ v = 2 * I) ∨ (u = 2 * I ∧ v = I)) : BijOn f ceDomain H := by
  have hu' : u ∈ H := by rcases huv with ⟨rfl, -⟩ | ⟨rfl, -⟩; exacts [I_mem_H', two_I_mem_H]
  have hv' : v ∈ H := by rcases huv with ⟨-, rfl⟩ | ⟨-, rfl⟩; exacts [two_I_mem_H, I_mem_H']
  have huv' : u ≠ v := by
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exacts [I_ne_two_I, I_ne_two_I.symm]
  have huI : u = I ∨ u = 2 * I := by rcases huv with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  have hvI : v = I ∨ v = 2 * I := by rcases huv with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [h]
  have hoff : ∀ z ∈ H \ {I, 2 * I}, z ≠ u ∧ z ≠ v := by
    rintro z ⟨-, hz⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz
    exact ⟨fun h => by rcases huI with h' | h' <;> simp_all,
      fun h => by rcases hvI with h' | h' <;> simp_all⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro z (⟨hzH, -⟩ | rfl | rfl)
    · rw [hf z (ne_neg_I_of_mem_H hzH) (ne_neg_two_I_of_mem_H hzH)]; exact hzH
    · rw [hu]; exact hu'
    · rw [hv]; exact hv'
  · rintro z (hz | rfl | rfl) w (hw | rfl | rfl) hzw
    · rwa [hf z (ne_neg_I_of_mem_H hz.1) (ne_neg_two_I_of_mem_H hz.1),
        hf w (ne_neg_I_of_mem_H hw.1) (ne_neg_two_I_of_mem_H hw.1)] at hzw
    · rw [hf z (ne_neg_I_of_mem_H hz.1) (ne_neg_two_I_of_mem_H hz.1), hu] at hzw
      exact absurd hzw (hoff z hz).1
    · rw [hf z (ne_neg_I_of_mem_H hz.1) (ne_neg_two_I_of_mem_H hz.1), hv] at hzw
      exact absurd hzw (hoff z hz).2
    · rw [hf w (ne_neg_I_of_mem_H hw.1) (ne_neg_two_I_of_mem_H hw.1), hu] at hzw
      exact absurd hzw.symm (hoff w hw).1
    · rfl
    · rw [hu, hv] at hzw; exact absurd hzw huv'
    · rw [hf w (ne_neg_I_of_mem_H hw.1) (ne_neg_two_I_of_mem_H hw.1), hv] at hzw
      exact absurd hzw.symm (hoff w hw).2
    · rw [hu, hv] at hzw; exact absurd hzw.symm huv'
    · rfl
  · intro ζ hζ
    by_cases h1 : ζ = u
    · exact ⟨-I, Or.inr (Or.inl rfl), by rw [hu, h1]⟩
    by_cases h2 : ζ = v
    · exact ⟨-(2 * I), Or.inr (Or.inr rfl), by rw [hv, h2]⟩
    have hζ' : ζ ∉ ({I, 2 * I} : Set ℂ) := by
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [⟨h1, h2⟩, ⟨h2, h1⟩]
    exact ⟨ζ, Or.inl ⟨hζ, hζ'⟩, hf ζ (ne_neg_I_of_mem_H hζ) (ne_neg_two_I_of_mem_H hζ)⟩

/-- The first chart of the counterexample. -/
def ceHChart₁ : HChart ceDomain :=
  ⟨ceChart₁, differentiableOn_ceDomain ceChart₁_spec,
    bijOn_ceDomain ceChart₁_spec (by simp [ceChart₁])
      (by simp [ceChart₁, neg_I_ne_neg_two_I.symm]) (Or.inl ⟨rfl, rfl⟩)⟩

/-- The second chart of the counterexample. -/
def ceHChart₂ : HChart ceDomain :=
  ⟨ceChart₂, differentiableOn_ceDomain ceChart₂_spec,
    bijOn_ceDomain ceChart₂_spec (by simp [ceChart₂])
      (by simp [ceChart₂, neg_I_ne_neg_two_I.symm]) (Or.inr ⟨rfl, rfl⟩)⟩

/-- A real Möbius map with positive determinant fixing `3i` and `4i` is the identity on `i`. -/
private theorem realMobius_I_of_fix {a b c d : ℝ} (h : 0 < a * d - b * c)
    (h3 : realMobius a b c d (3 * I) = 3 * I) (h4 : realMobius a b c d (4 * I) = 4 * I) :
    realMobius a b c d I = I := by
  have h3H : 3 * I ∈ H := by show (0 : ℝ) < (3 * I).im; simp
  have h4H : 4 * I ∈ H := by show (0 : ℝ) < (4 * I).im; simp
  simp only [QuantumZipper.CA.realMobius] at h3 h4 ⊢
  rw [div_eq_iff (QuantumZipper.CA.realMobius_denom_ne_zero h h3H)] at h3
  rw [div_eq_iff (QuantumZipper.CA.realMobius_denom_ne_zero h h4H)] at h4
  have r3 := congrArg Complex.re h3
  have i3 := congrArg Complex.im h3
  have r4 := congrArg Complex.re h4
  simp at r3 i3 r4
  have hc : c = 0 := by linarith
  have hb : b = 0 := by linarith
  have had : a = d := by linarith
  subst hc hb had
  have ha : (a : ℂ) ≠ 0 := ofReal_ne_zero.2 (by rintro rfl; simp at h)
  simp only [ofReal_zero, add_zero, zero_mul, zero_add]
  field_simp

/-- **The design's `PrimeEnd.mk_bijective` is false without `IsOpen D`.** -/
theorem not_forall_bijective_mk :
    ¬ ∀ (D : Set ℂ) (ψ : HChart D), Bijective (mk ψ) := by
  intro hall
  obtain ⟨x, hx⟩ := (hall ceDomain ceHChart₁).2 (mk ceHChart₂ OnePoint.infty)
  obtain ⟨a, b, c, d, hdet, hEq, -⟩ := mk_eq_mk_iff.1 hx
  have hfix : ∀ z ∈ H \ {I, 2 * I}, realMobius a b c d z = z := by
    intro z hz
    have h := hEq (Or.inl hz)
    simp only [Function.comp_apply] at h
    rwa [show ceHChart₂.1 z = z from ceChart₂_spec z (ne_neg_I_of_mem_H hz.1)
        (ne_neg_two_I_of_mem_H hz.1),
      show ceHChart₁.1 z = z from ceChart₁_spec z (ne_neg_I_of_mem_H hz.1)
        (ne_neg_two_I_of_mem_H hz.1), eq_comm] at h
  have hmem : ∀ t : ℝ, 2 < t → (t : ℂ) * I ∈ H \ {I, 2 * I} := by
    intro t ht
    refine ⟨by show (0 : ℝ) < ((t : ℂ) * I).im; simp; linarith, ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    constructor <;> intro h <;> have := congrArg Complex.im h <;> simp at this <;> linarith
  have h3 := hfix _ (hmem 3 (by norm_num))
  have h4 := hfix _ (hmem 4 (by norm_num))
  push_cast at h3 h4
  have hI := realMobius_I_of_fix hdet h3 h4
  have h := hEq (Or.inr (Or.inl rfl))
  simp only [Function.comp_apply] at h
  rw [show ceHChart₂.1 (-I) = 2 * I by simp [ceHChart₂, ceChart₂],
    show ceHChart₁.1 (-I) = I by simp [ceHChart₁, ceChart₁], hI] at h
  exact I_ne_two_I h.symm

end PrimeEnd

end InteractingSLE
