/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Jordan.Chart
import InteractingSLE.GFF.PushforwardLaw
import InteractingSLE.Spec.Sec7.LocalExtDCov
import InteractingSLE.Frozen.Spec.IsLocalSet
import InteractingSLE.Frozen.Spec.IsBoundedHarmonicExtension
import InteractingSLE.Frozen.Spec.forceBoundaryData
import InteractingSLE.Frozen.Spec.forceJumpSet
import LQGMetric.Papers.CONF.S3D112M1

/-!
# Aux. lemma 126: the field under the dilation `z ↦ r z`

Packet PROVE-LEMMA725REF2. Specification §7.4, Aux. lemma 126's proof (`source/spec/p385-432.md` L251–L316,
pp. 401–402, "Universal field determination"):

> Dilation of a whole two-seed pair acts on its field by `H₀^{(a)}(z) = H₀(z/a)`. The derivative of `z ↦ z/a` is
> positive real, so its winding correction is zero. The two boundary constants and the zero-boundary GFF law are
> invariant under this dilation. Original optional hull locality and its Gaussian specification are preserved.

This file proves the field half of that sentence for a dilation `z ↦ r z`, `r > 0`, with the dilation chart
`Chart.dilation r` (`fwd = r ·`, `inv = · / r`, lift `0`) of `GFF/Pushforward` and `Spec/Jordan/Chart`:

* `dilField hr h = h(· / r)` (`Chart.pullField` of the dilation chart), tested against `φ ↦ r² φ(r ·)`
  (`pushTest_dilation_apply`), measurable, additive, with inverse `dilField (1/r)`;
* `measurable_image_dil`: `S ↦ r S` (`dil r z = r z`) is measurable for the hitting σ-algebra;
* `isHarmonicDistOn_dilField`, `isCondZeroBoundaryGFF_dilField` (the covariance on a subdomain is dilation invariant:
  `zeroGFFTestCov_dil`, from LQGMetric's `zeroGFFTestCov_affine_ind`);
* **`IsLocalSet.dilate`**: if `A` is a local set of `h`, then `r A` is a local set of `h(· / r)`;
* the force data and their bounded harmonic extensions under dilation (`forceBoundaryData_dil`,
  `isBoundedHarmonicExtension_comp_dil`, `isBoundedHarmonicExtension_force_comp_dil`), and the zero-boundary GFF clause
  (`isZBGFFProcess_dilField`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Sec7

namespace Lemma725RefFull

variable {r : ℝ}

/-! ### The dilated test functions and fields -/

theorem dilation_dom_eq (hr : 0 < r) : ((Chart.dilation r).dom : Set ℂ) = H := by
  rw [(Chart.isConformal_dilation hr).coe_dom, Chart.dilation_image_H hr]

theorem mul_mem_H_iff (hr : 0 < r) {z : ℂ} : (r : ℂ) * z ∈ H ↔ z ∈ H := by
  change 0 < ((r : ℂ) * z).im ↔ 0 < z.im
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  exact ⟨fun h => pos_of_mul_pos_right h hr.le, fun h => mul_pos hr h⟩

theorem test_mul_eq_zero_of_notMem (hr : 0 < r) (φ : TestOn upperHalfPlaneOpens) {z : ℂ} (hz : z ∉ H) :
    φ ((r : ℂ) * z) = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hz ((mul_mem_H_iff hr).1 (φ.tsupport_subset h))

theorem deriv_dilation (z : ℂ) : deriv (Chart.dilation r).1 z = r := by
  change deriv (fun z : ℂ => (r : ℂ) * z) z = r
  simp

/-- **The transported test function of the dilation chart** is `φ ↦ r² φ(r ·)`. -/
theorem pushTest_dilation_apply (hr : 0 < r) (φ : TestOn upperHalfPlaneOpens) (z : ℂ) :
    Chart.pushTest (Chart.isConformal_dilation hr) φ z = r ^ 2 * φ ((r : ℂ) * z) := by
  rw [Chart.coe_pushTest]
  by_cases hz : z ∈ H
  · rw [indicator_of_mem (by rw [dilation_dom_eq hr]; exact hz), deriv_dilation, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    rfl
  · rw [indicator_of_notMem (by rw [dilation_dom_eq hr]; exact hz), test_mul_eq_zero_of_notMem hr φ hz, mul_zero]

/-- The field `h(· / r)`: `h` read in the dilation chart `w ↦ r w`, i.e. tested against `φ ↦ r² φ(r ·)`. -/
def dilField (hr : 0 < r) (h : DistOn upperHalfPlaneOpens) : DistOn upperHalfPlaneOpens :=
  Chart.pullField (Chart.isConformal_dilation hr) h

theorem dilField_apply (hr : 0 < r) (h : DistOn upperHalfPlaneOpens) (φ : TestOn upperHalfPlaneOpens) :
    dilField hr h φ = h (Chart.pushTest (Chart.isConformal_dilation hr) φ) := rfl

theorem measurable_dilField (hr : 0 < r) : Measurable (dilField hr) :=
  LQGMetric.measurable_distOn_iff.2 fun φ =>
    LQGMetric.measurable_distOn_apply (Chart.pushTest (Chart.isConformal_dilation hr) φ)

theorem dilField_add (hr : 0 < r) (f g : DistOn upperHalfPlaneOpens) :
    dilField hr (f + g) = dilField hr f + dilField hr g := by
  ext φ
  simp only [dilField_apply, add_apply]

theorem pushTest_dilation_pushTest (hr : 0 < r) (φ : TestOn upperHalfPlaneOpens) :
    Chart.pushTest (Chart.isConformal_dilation hr)
        (Chart.pushTest (Chart.isConformal_dilation (inv_pos.2 hr)) φ) = φ := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  ext z
  rw [pushTest_dilation_apply hr, pushTest_dilation_apply (inv_pos.2 hr), ← mul_assoc, Complex.ofReal_inv,
    inv_mul_cancel_left₀ hr0,
    inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 hr.ne'), one_mul]

/-- `T ↦ T(· / r)` is inverted by `T ↦ T(r ·)`. -/
theorem dilField_inv_dilField (hr : 0 < r) (T : DistOn upperHalfPlaneOpens) :
    dilField (inv_pos.2 hr) (dilField hr T) = T := by
  ext φ
  rw [dilField_apply, dilField_apply, pushTest_dilation_pushTest hr]

/-- **Change of variables** `z = w / r`: `∫ u · r² φ(r ·) = ∫ u(· / r) φ`. -/
theorem integral_mul_pushTest_dilation (hr : 0 < r) (φ : TestOn upperHalfPlaneOpens) (u : ℂ → ℝ) :
    ∫ z, u z * Chart.pushTest (Chart.isConformal_dilation hr) φ z = ∫ w, u (w / r) * φ w :=
  Chart.integral_mul_pushTest (Chart.isConformal_dilation hr) φ u

/-- The support of `r² φ(r ·)` is `r⁻¹ supp φ`. -/
theorem tsupport_pushTest_dilation (hr : 0 < r) (φ : TestOn upperHalfPlaneOpens) :
    tsupport (Chart.pushTest (Chart.isConformal_dilation hr) φ) ⊆ (fun z : ℂ => (r : ℂ) * z) ⁻¹' tsupport φ := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have e : ⇑(Chart.pushTest (Chart.isConformal_dilation hr) φ) = fun z => r ^ 2 * φ ((r : ℂ) * z) :=
    funext (pushTest_dilation_apply hr φ)
  rw [e]
  refine (tsupport_mul_subset_right (f := fun _ : ℂ => r ^ 2)).trans ?_
  have h := tsupport_comp_eq_preimage (g := φ) (Homeomorph.mulLeft₀ (r : ℂ) hr0)
  exact h.le

/-! ### Sets under the dilation -/

/-- The dilation `z ↦ r z` of the plane. -/
def dil (r : ℝ) (z : ℂ) : ℂ := (r : ℂ) * z

theorem dil_apply (z : ℂ) : dil r z = (r : ℂ) * z := rfl

theorem continuous_dil : Continuous (dil r) := continuous_const.mul continuous_id

theorem dil_inv_dil (hr : 0 < r) (z : ℂ) : dil r⁻¹ (dil r z) = z := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  simp only [dil, Complex.ofReal_inv]
  field_simp

theorem dil_dil_inv (hr : 0 < r) (z : ℂ) : dil r (dil r⁻¹ z) = z := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  simp only [dil, Complex.ofReal_inv]
  field_simp

theorem dil_injective (hr : 0 < r) : Function.Injective (dil r) := fun x y e => by
  rw [← dil_inv_dil hr x, e, dil_inv_dil hr y]

/-- The dilation as a homeomorphism of `ℂ`. -/
def dilHomeo (hr : 0 < r) : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ (r : ℂ) (Complex.ofReal_ne_zero.2 hr.ne')

theorem coe_dilHomeo (hr : 0 < r) : ⇑(dilHomeo hr) = dil r := rfl

theorem dil_mem_H_iff (hr : 0 < r) {z : ℂ} : dil r z ∈ H ↔ z ∈ H := mul_mem_H_iff hr

theorem image_dil_image_dil (hr : 0 < r) (S : Set ℂ) : dil r⁻¹ '' (dil r '' S) = S := by
  rw [image_image]
  simp only [dil_inv_dil hr, image_id']

theorem image_dil_inv_image_dil (hr : 0 < r) (S : Set ℂ) : dil r '' (dil r⁻¹ '' S) = S := by
  rw [image_image]
  simp only [dil_dil_inv hr, image_id']

theorem isOpen_image_dil (hr : 0 < r) {U : Set ℂ} (hU : IsOpen U) : IsOpen (dil r '' U) :=
  (dilHomeo hr).isOpenMap U hU

theorem image_dil_subset_H (hr : 0 < r) {U : Set ℂ} (hU : U ⊆ H) : dil r '' U ⊆ H := by
  rintro _ ⟨w, hw, rfl⟩
  exact (dil_mem_H_iff hr).2 (hU hw)

/-- `ℍ \ r S = r (ℍ \ S)`. -/
theorem H_diff_image_dil (hr : 0 < r) (S : Set ℂ) : H \ dil r '' S = dil r '' (H \ S) := by
  ext z
  constructor
  · rintro ⟨hzH, hzS⟩
    refine ⟨dil r⁻¹ z, ⟨(dil_mem_H_iff hr).1 (by rw [dil_dil_inv hr]; exact hzH), fun h => hzS
      ⟨dil r⁻¹ z, h, dil_dil_inv hr z⟩⟩, dil_dil_inv hr z⟩
  · rintro ⟨w, ⟨hwH, hwS⟩, rfl⟩
    refine ⟨(dil_mem_H_iff hr).2 hwH, ?_⟩
    rintro ⟨v, hv, e⟩
    exact hwS (dil_injective hr e ▸ hv)

theorem image_dil_inter_nonempty_iff (S U : Set ℂ) :
    (dil r '' S ∩ U).Nonempty ↔ (S ∩ dil r ⁻¹' U).Nonempty := by
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, hzU⟩
    exact ⟨z, hz, hzU⟩
  · rintro ⟨z, hz, hzU⟩
    exact ⟨_, ⟨z, hz, rfl⟩, hzU⟩

/-- **`S ↦ r S` is measurable for the hitting σ-algebra.** -/
theorem measurable_image_dil (hr : 0 < r) :
    Measurable[hittingSigma, hittingSigma] fun S : Set ℂ => dil r '' S := by
  refine @measurable_generateFrom (Set ℂ) (Set ℂ) hittingSigma _ (fun S : Set ℂ => dil r '' S) ?_
  rintro _ ⟨U, hUo, hUH, rfl⟩
  have e : (fun S : Set ℂ => dil r '' S) ⁻¹' {A | (A ∩ U).Nonempty} = {A | (A ∩ dil r ⁻¹' U).Nonempty} := by
    ext S
    exact image_dil_inter_nonempty_iff S U
  rw [e]
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨dil r ⁻¹' U, hUo.preimage continuous_dil, fun z hz => (dil_mem_H_iff hr).1 (hUH hz), rfl⟩

/-- The comap of a measurable self-map with a measurable left inverse is the σ-algebra itself. -/
theorem comap_eq_of_comp_eq_id {α : Type*} {m : MeasurableSpace α} {f g : α → α}
    (hf : Measurable[m, m] f) (hg : Measurable[m, m] g) (hgf : g ∘ f = id) : m.comap f = m := by
  refine le_antisymm hf.comap_le ?_
  calc m = m.comap (g ∘ f) := by rw [hgf, MeasurableSpace.comap_id]
    _ = (m.comap g).comap f := (MeasurableSpace.comap_comp).symm
    _ ≤ m.comap f := MeasurableSpace.comap_mono hg.comap_le

theorem comap_image_dil (hr : 0 < r) :
    hittingSigma.comap (fun S : Set ℂ => dil r '' S) = hittingSigma :=
  comap_eq_of_comp_eq_id (measurable_image_dil hr) (measurable_image_dil (inv_pos.2 hr))
    (funext fun S => image_dil_image_dil hr S)

/-- The almost sure clause of a local set is preserved by the dilation. -/
theorem image_dil_relClosed (hr : 0 < r) {S : Set ℂ} (hS : S ⊆ H ∧ IsOpen (H \ S)) :
    dil r '' S ⊆ H ∧ IsOpen (H \ dil r '' S) := by
  refine ⟨image_dil_subset_H hr hS.1, ?_⟩
  rw [H_diff_image_dil hr]
  exact isOpen_image_dil hr hS.2

/-! ### The zero-boundary covariance on a subdomain under the dilation -/

open QuantumZipper (zeroGFFTestCov)

theorem comp_dil_eq_smul_pushTest (hr : 0 < r) (φ : TestOn upperHalfPlaneOpens) :
    (fun z => φ (dil r z)) = ⇑((r ^ 2)⁻¹ • Chart.pushTest (Chart.isConformal_dilation hr) φ) := by
  have hr2 : (r ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 hr.ne'
  funext z
  change φ (dil r z) = (r ^ 2)⁻¹ * Chart.pushTest (Chart.isConformal_dilation hr) φ z
  rw [pushTest_dilation_apply hr, ← mul_assoc, inv_mul_cancel₀ hr2, one_mul]
  rfl

/-- **The zero-boundary covariance is dilation invariant on every subdomain**: for `U ⊆ ℍ` open,
`Cov_U(φ', φ') = Cov_{rU}(φ, φ)` with `φ' = r² φ(r ·)` (LQGMetric's `zeroGFFTestCov_affine_ind` for the affine
map `x ↦ r x`, the indicators removed by `GFF.zeroGFFTestCov_indicator`, and bilinearity). -/
theorem zeroGFFTestCov_dil (hr : 0 < r) {U : Set ℂ} (hUo : IsOpen U) (hUH : U ⊆ H)
    (φ : TestOn upperHalfPlaneOpens) :
    zeroGFFTestCov U (Chart.pushTest (Chart.isConformal_dilation hr) φ)
        (Chart.pushTest (Chart.isConformal_dilation hr) φ) = zeroGFFTestCov (dil r '' U) φ φ := by
  set ψ := Chart.pushTest (Chart.isConformal_dilation hr) φ with hψ
  have hri : r⁻¹ ≠ 0 := inv_ne_zero hr.ne'
  let V : TopologicalSpace.Opens ℂ := ⟨dil r '' U, isOpen_image_dil hr hUo⟩
  let U' : TopologicalSpace.Opens ℂ := ⟨U, hUo⟩
  let φC : LQGMetric.TestC := GFF.testIncl upperHalfPlaneOpens ⊤ φ
  have hφC : ⇑φC = ⇑φ := GFF.coe_testIncl le_top φ
  have haff : ∀ x, LQGMetric.affMap r⁻¹ 0 x = dil r x := by
    intro x
    simp only [LQGMetric.affMap, inv_inv, neg_zero, add_zero, dil, Complex.real_smul]
  have hopens : (LQGMetric.affOpens r⁻¹ 0 V : Set ℂ) = U := by
    ext x
    change LQGMetric.affMap r⁻¹ 0 x ∈ dil r '' U ↔ x ∈ U
    rw [haff]
    exact ⟨fun ⟨y, hy, e⟩ => dil_injective hr e ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  have hpull : ⇑(LQGMetric.testAffinePull r⁻¹ 0 φC) = fun x => φ (dil r x) := by
    rw [LQGMetric.CONF.coe_testAffinePull_eq hri, hφC]
    funext x
    simp only [Function.comp_apply, haff]
  have key := LQGMetric.CONF.zeroGFFTestCov_affine_ind (z := 0) hri V φC φC
  rw [hopens, hpull, hφC] at key
  have hcont : Continuous fun x => φ (dil r x) := φ.continuous.comp continuous_dil
  have hcs : HasCompactSupport fun x => φ (dil r x) := φ.hasCompactSupport.comp_homeomorph (dilHomeo hr)
  have h1 := GFF.zeroGFFTestCov_indicator U' hcont hcs hcont hcs
  have h2 := GFF.zeroGFFTestCov_indicator V φ.continuous φ.hasCompactSupport φ.continuous φ.hasCompactSupport
  simp only [U', V, TopologicalSpace.Opens.coe_mk] at h1 h2 key
  rw [h1, h2, comp_dil_eq_smul_pushTest hr φ, LocalExt.zeroGFFTestCov_smul_left hUo hUH,
    LocalExt.zeroGFFTestCov_smul_right hUo hUH] at key
  have e : (r ^ 2)⁻¹ * ((r ^ 2)⁻¹ * zeroGFFTestCov U ψ ψ) = r⁻¹ ^ 4 * zeroGFFTestCov U ψ ψ := by ring
  rw [e] at key
  exact mul_left_cancel₀ (pow_ne_zero 4 hri) key

/-! ### Harmonic distributions, conditional GFFs and local sets under the dilation -/

/-- **Harmonic distributions under the dilation**: if `T` is harmonic on `U`, then `T(· / r)` is harmonic on `r U`,
with representative `v(· / r)`. -/
theorem isHarmonicDistOn_dilField (hr : 0 < r) {T : DistOn upperHalfPlaneOpens} {U : Set ℂ} (hUo : IsOpen U)
    (hT : IsHarmonicDistOn T U) : IsHarmonicDistOn (dilField hr T) (dil r '' U) := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  obtain ⟨v, hv, hrep⟩ := hT
  refine ⟨fun z => v (z / r), ?_, fun φ hφ => ?_⟩
  · refine LQGMetric.harmonicOnNhd_comp_holo hUo (isOpen_image_dil hr hUo) hv
      (differentiableOn_id.div_const (r : ℂ)) ?_
    rintro _ ⟨w, hw, rfl⟩
    change dil r w / r ∈ U
    rw [dil, mul_div_cancel_left₀ _ hr0]
    exact hw
  · have hsupp : tsupport (Chart.pushTest (Chart.isConformal_dilation hr) φ) ⊆ U := by
      refine (tsupport_pushTest_dilation hr φ).trans fun z hz => ?_
      obtain ⟨w, hw, e⟩ := hφ hz
      exact dil_injective hr e ▸ hw
    rw [dilField_apply, hrep _ hsupp, integral_mul_pushTest_dilation hr]

/-- **The conditional zero-boundary GFF under the dilation.** If, given `𝒢`, `X` is a zero-boundary GFF on `ℍ \ A`,
then `X(· / r)` is, given `𝒢`, a zero-boundary GFF on `ℍ \ r A`. -/
theorem isCondZeroBoundaryGFF_dilField (hr : 0 < r) {Ω : Type*} {𝒢 : MeasurableSpace Ω} [MeasurableSpace Ω]
    {P : Measure Ω} {A : Ω → Set ℂ} (hA : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) {X : Ω → DistOn upperHalfPlaneOpens}
    (hX : IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ A ω) X) :
    IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ dil r '' A ω) (fun ω => dilField hr (X ω)) := by
  intro φ
  have h := hX (Chart.pushTest (Chart.isConformal_dilation hr) φ)
  simp only [dilField_apply]
  refine h.trans (Eventually.of_forall fun ω => ?_)
  dsimp only
  rw [H_diff_image_dil hr, ← zeroGFFTestCov_dil hr (hA ω).2 sdiff_subset]

/-- **Local sets under the dilation.** If `A` is a local set of `h`, then `r A` is a local set of `h(· / r)`. -/
theorem IsLocalSet.dilate (hr : 0 < r) {Ω : Type u} [MeasurableSpace Ω] {A : Ω → Set ℂ}
    {h : Ω → DistOn upperHalfPlaneOpens} {P : Measure Ω} (hA : IsLocalSet A h P) :
    IsLocalSet (fun ω => dil r '' A ω) (fun ω => dilField hr (h ω)) P := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  obtain ⟨hm, hae, Ω', mΩ', P', hP', A', h₁, h₂, hA'm, hh₁, hh₂, hA'c, hhar, hcond, hlaw⟩ := hA
  have hF : Measurable fun p : Set ℂ × DistOn upperHalfPlaneOpens => (dil r '' p.1, dilField hr p.2) :=
    ((measurable_image_dil hr).comp measurable_fst).prodMk ((measurable_dilField hr).comp measurable_snd)
  have hFi : Measurable fun T : DistOn upperHalfPlaneOpens => dilField (inv_pos.2 hr) T :=
    measurable_dilField (inv_pos.2 hr)
  have hσ : MeasurableSpace.comap (fun ω' => dil r '' A' ω') hittingSigma ⊔
      MeasurableSpace.comap (fun ω' => dilField hr (h₁ ω')) inferInstance =
      MeasurableSpace.comap A' hittingSigma ⊔ MeasurableSpace.comap h₁ inferInstance := by
    have e1 : MeasurableSpace.comap (fun ω' => dil r '' A' ω') hittingSigma =
        MeasurableSpace.comap A' hittingSigma := by
      change MeasurableSpace.comap ((fun S : Set ℂ => dil r '' S) ∘ A') hittingSigma = _
      rw [← MeasurableSpace.comap_comp, comap_image_dil hr]
    have e2 : MeasurableSpace.comap (fun ω' => dilField hr (h₁ ω')) (inferInstance :
        MeasurableSpace (DistOn upperHalfPlaneOpens)) = MeasurableSpace.comap h₁ inferInstance := by
      change MeasurableSpace.comap (dilField hr ∘ h₁) _ = _
      rw [← MeasurableSpace.comap_comp, comap_eq_of_comp_eq_id (measurable_dilField hr) hFi
        (funext fun T => dilField_inv_dilField hr T)]
    rw [e1, e2]
  refine ⟨hF.comp_aemeasurable hm, hae.mono fun ω hω => image_dil_relClosed hr hω,
    Ω', mΩ', P', hP', fun ω' => dil r '' A' ω', fun ω' => dilField hr (h₁ ω'),
    fun ω' => dilField hr (h₂ ω'), (measurable_image_dil hr).comp hA'm, (measurable_dilField hr).comp hh₁,
    (measurable_dilField hr).comp hh₂, fun ω' => image_dil_relClosed hr (hA'c ω'), ?_, ?_, ?_⟩
  · filter_upwards [hhar] with ω' hω'
    rw [H_diff_image_dil hr]
    exact isHarmonicDistOn_dilField hr (hA'c ω').2 hω'
  · rw [hσ]
    exact isCondZeroBoundaryGFF_dilField hr hA'c hcond
  · have e : (fun ω' => (dil r '' A' ω', dilField hr (h₁ ω') + dilField hr (h₂ ω'))) =
        (fun p : Set ℂ × DistOn upperHalfPlaneOpens => (dil r '' p.1, dilField hr p.2)) ∘
          fun ω' => (A' ω', h₁ ω' + h₂ ω') := by
      funext ω'
      simp only [Function.comp_apply, dilField_add]
    have e' : (fun ω => (dil r '' A ω, dilField hr (h ω))) =
        (fun p : Set ℂ × DistOn upperHalfPlaneOpens => (dil r '' p.1, dilField hr p.2)) ∘
          fun ω => (A ω, h ω) := rfl
    have hm' : Measurable fun ω' => (A' ω', h₁ ω' + h₂ ω') :=
      hA'm.prodMk (LQGMetric.measurable_distOn_iff.2 fun φ => by
        simp only [add_apply]
        exact ((LQGMetric.measurable_distOn_apply φ).comp hh₁).add
          ((LQGMetric.measurable_distOn_apply φ).comp hh₂))
    rw [e, e', ← Measure.map_map hF hm', hlaw, AEMeasurable.map_map_of_aemeasurable hF.aemeasurable hm]

/-! ### Force data, harmonic extensions and the zero-boundary GFF clause under the dilation -/

theorem mul_lt_mul_iff_left' (hr : 0 < r) (a b : ℝ) : r * a < r * b ↔ a < b := mul_lt_mul_iff_of_pos_left hr

theorem mul_le_mul_iff_left' (hr : 0 < r) (a b : ℝ) : r * a ≤ r * b ↔ a ≤ b := mul_le_mul_iff_of_pos_left hr

/-- **The force data of the dilated word**: `g_{r x}(r y) = g_x(y)` (the data only see the order of the positions). -/
theorem forceBoundaryData_dil (hr : 0 < r) (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (x : ℝ) :
    forceBoundaryData κ ρL ρR (fun i => r * xL i) (fun i => r * xR i) (r * x) = forceBoundaryData κ ρL ρR xL xR x := by
  have h0 : r * x < 0 ↔ x < 0 := by
    have := mul_lt_mul_iff_left' hr x 0
    rwa [mul_zero] at this
  unfold forceBoundaryData
  simp only [h0, mul_lt_mul_iff_left' hr, mul_le_mul_iff_left' hr]

theorem mul_mem_forceJumpSet_iff (hr : 0 < r) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (x : ℝ) :
    r * x ∈ forceJumpSet (fun i => r * xL i) (fun i => r * xR i) ↔ x ∈ forceJumpSet xL xR := by
  simp only [forceJumpSet, mem_insert_iff, mem_union, mem_range, mul_eq_zero, hr.ne', false_or,
    mul_right_inj' hr.ne']

theorem tendsto_dil_nhdsWithin_H (hr : 0 < r) (x : ℝ) :
    Tendsto (dil r) (𝓝[H] (x : ℂ)) (𝓝[H] ((r * x : ℝ) : ℂ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz => (dil_mem_H_iff hr).2 hz⟩
  have := (continuous_dil (r := r).tendsto (x : ℂ)).mono_left (nhdsWithin_le_nhds (s := H))
  simpa [dil, Complex.ofReal_mul] using this

/-- **Bounded harmonic extensions under the dilation**: if `u` extends `g'` off `S'`, and `g'(r x) = g(x)`,
`r x ∉ S'` for `x ∉ S`, then `u(r ·)` extends `g` off `S`. -/
theorem isBoundedHarmonicExtension_comp_dil (hr : 0 < r) {g g' : ℝ → ℝ} {S S' : Set ℝ} {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension g' S' u) (hS : ∀ x, x ∉ S → r * x ∉ S')
    (hg : ∀ x, x ∉ S → g' (r * x) = g x) : IsBoundedHarmonicExtension g S fun z => u (dil r z) := by
  obtain ⟨hharm, ⟨C, hC⟩, hlim⟩ := hu
  refine ⟨LQGMetric.harmonicOnNhd_comp_holo QuantumZipper.isOpen_H QuantumZipper.isOpen_H hharm
    ((differentiable_id.const_mul (r : ℂ)).differentiableOn) fun z hz => (dil_mem_H_iff hr).2 hz,
    ⟨C, fun z hz => hC _ ((dil_mem_H_iff hr).2 hz)⟩, fun x hx => ?_⟩
  have h1 := hlim (r * x) (hS x hx)
  rw [hg x hx] at h1
  exact h1.comp (tendsto_dil_nhdsWithin_H hr x)

/-- The bounded harmonic extensions of the force data of the word and of its dilation correspond through
`u ↦ u(r ·)`. -/
theorem isBoundedHarmonicExtension_force_comp_dil (hr : 0 < r) {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR (fun i => r * xL i) (fun i => r * xR i))
      (forceJumpSet (fun i => r * xL i) (fun i => r * xR i)) u) :
    IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) fun z => u (dil r z) :=
  isBoundedHarmonicExtension_comp_dil hr hu (fun x hx h => hx ((mul_mem_forceJumpSet_iff hr xL xR x).1 h))
    fun x _ => forceBoundaryData_dil hr κ ρL ρR xL xR x

theorem dilation_opens_eq (hr : 0 < r) : (Chart.dilation r).dom = upperHalfPlaneOpens :=
  SetLike.coe_injective (dilation_dom_eq hr)

/-- **The zero-boundary GFF clause under the dilation** (for every bounded harmonic extension of the dilated data). -/
theorem isZBGFFProcess_dilField (hr : 0 < r) {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hgff : ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀ →
      LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => h ω φ - ∫ z, u₀ z * φ z) P)
    (u₀ : ℂ → ℝ) (hu₀ : IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => r * xL i) (fun i => r * xR i))
      (forceJumpSet (fun i => r * xL i) (fun i => r * xR i)) u₀) :
    LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => dilField hr (h ω) φ - ∫ z, u₀ z * φ z) P := by
  have hc := Chart.isConformal_dilation hr
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  set u : ℂ → ℝ := fun z => u₀ (dil r z) with hu
  have hZ := hgff u (isBoundedHarmonicExtension_force_comp_dil hr hu₀)
  have key : ∀ U : TopologicalSpace.Opens ℂ, U = upperHalfPlaneOpens → LQGMetric.IsZBGFFProcess U
      (fun ψ ω => h ω (GFF.testIncl U upperHalfPlaneOpens ψ) - ∫ z, u z * ψ z) P := by
    rintro U rfl
    have hid : ∀ ψ : TestOn upperHalfPlaneOpens,
        GFF.testIncl upperHalfPlaneOpens upperHalfPlaneOpens ψ = ψ := fun ψ => by
      ext z
      exact congrFun (GFF.coe_testIncl le_rfl ψ) z
    simp only [hid]
    exact hZ
  have hℓ : LocallyIntegrableOn (fun w => (Chart.dilation r).2.2 ((Chart.dilation r).2.1 w)) H :=
    locallyIntegrableOn_const 0
  have hZ' := Chart.isZBGFFProcess_chartTransport hc hℓ (m := u) 0 (key _ (dilation_opens_eq hr))
  convert hZ' using 2 with φ
  funext ω
  have e1 : ∀ w : ℂ, u ((Chart.dilation r).2.1 w) = u₀ w := fun w => by
    simp only [hu, Chart.dilation_inv, dil]
    rw [mul_div_cancel₀ w hr0]
  simp only [e1, zero_mul, add_zero, Chart.chartTransport_apply', one_mul, dilField_apply]

end Lemma725RefFull

end Sec7

end InteractingSLE
