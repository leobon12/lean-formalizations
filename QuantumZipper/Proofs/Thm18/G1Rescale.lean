import QuantumZipper.Proofs.Thm18.Assembly
import QuantumZipper.Proofs.Complex.UniformizerUnique
import QuantumZipper.Proofs.Complex.KoebeBasic
import QuantumZipper.Proofs.Zipper.B2Defs
import QuantumZipper.Proofs.GFF.CoordRegFwd
import QuantumZipper.Proofs.LQG.WedgeToolkit
import QuantumZipper.Proofs.Section5.Prop17Field

/-!
# G1, part 1: the choice of uniformizer is irrelevant after `canonical` (Theorem 1.8, node G1)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §1.6 (a quantum surface
is an equivalence class under `h ↦ h ∘ ψ + Q log|ψ'|`, and (1.8) fixes the scaling freedom) and
§5.4 (proof of Theorem 1.8). `componentSurface` uses the `Classical.epsilon`-chosen normalized
uniformizer `uniformizer D`; KT2 and the Palm-zoom argument of G1 use other normalizations
(e.g. `IsLeftUniformizer`, `φ(−1) = −1`). This file proves, deterministically, that the two
choices give the same canonical description, up to explicit regularity conditions on the
pulled-back field.

* `invFunOn_eqOn_of_eqOn_mul`: if `φ₂ = a φ₁` on `D` (both bijections `D → ℍ`), then
  `φ₂⁻¹ = φ₁⁻¹ ∘ (a⁻¹ ·)` on `ℍ`.
* `exists_invFunOn_uniformizer_eq`: with U6 (`normalizedUniformizer_unique_*`), the inverse of
  `uniformizer D` is `ψ ∘ (b ·)` on `ℍ`, `b > 0`, for the inverse `ψ` of any normalized
  uniformizer of a chord component `D`.
* `invFunOn_props`: the inverse of a normalized uniformizer of an open `D` is holomorphic on
  `ℍ` with non-vanishing derivative, measurable, and maps `ℍ` into `D`.
* `regEq_coordChange_comp_mul`: `h ∘ (ψ ∘ (b ·)) + Q log|(ψ ∘ (b ·))'|` and the rescaling by `b`
  of `h ∘ ψ + Q log|ψ'|` have the same regularized averages (`RegEq`), when the latter field's
  folded-circle values are its regularized ones (`hexact`, the RC3 property of
  `CoordReg.ae_evalReg_coordChange_revMap_fc`) and `log|ψ'|` is integrable on folded circles.
* `canonical_coordChange_eq_of_eqOn`, `coordsFull_canonical_coordChange_eq`: hence the canonical
  descriptions are *equal*, and their circle coordinates agree with those for `ψ`.

Own elementary arguments (chain rule, `Measure.map` of folded circles under dilations, the
`RegEq`-congruence of `canonical`); the mathematical content is the remark after (1.8) in
Sheffield §1.6. U6 is `CA.Uniformizer.normalizedUniformizer_unique` (Burckel Thm 6.2(ii)).
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1

/-! ## 1. Inverse uniformizers under rescaling (U6 bridge) -/

theorem mul_mem_H {b : ℝ} (hb : 0 < b) {w : ℂ} (hw : w ∈ H) : (b : ℂ) * w ∈ H := by
  show 0 < ((b : ℂ) * w).im
  rw [Complex.im_ofReal_mul]
  exact mul_pos hb hw

/-- If `φ₂ = a φ₁` on `D` (`a > 0`, both bijections `D → ℍ`), then `φ₂⁻¹ = φ₁⁻¹ ∘ (a⁻¹ ·)` on
`ℍ`. -/
theorem invFunOn_eqOn_of_eqOn_mul {D : Set ℂ} {φ₁ φ₂ : ℂ → ℂ} (h₁ : BijOn φ₁ D H)
    (h₂ : BijOn φ₂ D H) {a : ℝ} (ha : 0 < a) (heq : EqOn φ₂ (fun z => (a : ℂ) * φ₁ z) D) :
    EqOn (invFunOn φ₂ D) (fun w => invFunOn φ₁ D ((a⁻¹ : ℝ) * w)) H := by
  intro w hw
  have hw' : ((a⁻¹ : ℝ) : ℂ) * w ∈ H := mul_mem_H (inv_pos.2 ha) hw
  have hex₁ : ∃ z ∈ D, φ₁ z = ((a⁻¹ : ℝ) : ℂ) * w := h₁.surjOn hw'
  have hex₂ : ∃ z ∈ D, φ₂ z = w := h₂.surjOn hw
  apply h₂.injOn (invFunOn_mem hex₂) (invFunOn_mem hex₁)
  rw [invFunOn_eq hex₂, heq (invFunOn_mem hex₁)]
  beta_reduce
  rw [invFunOn_eq hex₁, ← mul_assoc,
    ← Complex.ofReal_mul, mul_inv_cancel₀ ha.ne', Complex.ofReal_one, one_mul]

/-- The two components of a simple chord are open. -/
theorem isOpen_component {η : ℝ → ℂ} (hη : IsSimpleChord η) (left : Bool) :
    IsOpen (if left then leftComponent η else rightComponent η) := by
  cases left
  · have hpre : rightComponent η =
        CA.Uniformizer.refl ⁻¹' leftComponent (CA.Uniformizer.refl ∘ η) := by
      ext z; exact CA.Uniformizer.mem_rightComponent_iff
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hpre]
    exact (CA.Uniformizer.isOpen_leftComponent (CA.Uniformizer.isSimpleChord_refl_comp hη)).preimage
      (Complex.continuous_conj.neg)
  · simp only [↓reduceIte]
    exact CA.Uniformizer.isOpen_leftComponent hη

/-- **U6 bridge.** For a component `D` of a simple chord and any normalized uniformizer `φ` of
`D`, the inverse of the chosen `uniformizer D` is `(invFunOn φ D) ∘ (b ·)` on `ℍ`, `b > 0`. -/
theorem exists_invFunOn_uniformizer_eq {η : ℝ → ℂ} (hη : IsSimpleChord η) (left : Bool)
    {φ : ℂ → ℂ}
    (hφ : IsNormalizedUniformizer (if left then leftComponent η else rightComponent η) φ)
    (hu : IsNormalizedUniformizer (if left then leftComponent η else rightComponent η)
      (uniformizer (if left then leftComponent η else rightComponent η))) :
    ∃ b : ℝ, 0 < b ∧
      EqOn (invFunOn (uniformizer (if left then leftComponent η else rightComponent η))
          (if left then leftComponent η else rightComponent η))
        (fun w => invFunOn φ (if left then leftComponent η else rightComponent η) ((b : ℂ) * w))
        H := by
  obtain ⟨a, ha, heq⟩ : ∃ a : ℝ, 0 < a ∧
      EqOn (uniformizer (if left then leftComponent η else rightComponent η))
        (fun z => (a : ℂ) * φ z) (if left then leftComponent η else rightComponent η) := by
    cases left
    · exact CA.Uniformizer.normalizedUniformizer_unique_rightComponent hη hφ hu
    · exact CA.Uniformizer.normalizedUniformizer_unique_leftComponent hη hφ hu
  exact ⟨a⁻¹, inv_pos.2 ha, invFunOn_eqOn_of_eqOn_mul hφ.1 hu.1 ha heq⟩

/-- The inverse of a normalized uniformizer of an open `D`: holomorphic on `ℍ` with non-vanishing
derivative, measurable, and `ℍ → D`. -/
theorem invFunOn_props {D : Set ℂ} (hD : IsOpen D) {φ : ℂ → ℂ}
    (hφ : IsNormalizedUniformizer D φ) :
    DifferentiableOn ℂ (invFunOn φ D) H ∧ (∀ w ∈ H, deriv (invFunOn φ D) w ≠ 0) ∧
      Measurable (invFunOn φ D) ∧ MapsTo (invFunOn φ D) H D := by
  obtain ⟨hb, hd, -, -⟩ := hφ
  have hder : ∀ w ∈ H, ∃ z ∈ D, φ z = w ∧
      HasDerivAt (invFunOn φ D) (deriv φ z)⁻¹ w ∧ deriv φ z ≠ 0 := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := hb.surjOn hw
    exact ⟨z, hz, rfl, CA.Koebe.hasDerivAt_invFunOn_of_injOn hD hd hb.injOn hz,
      CA.Koebe.deriv_ne_zero_of_injOn hD hd hb.injOn hz⟩
  have hdiff : DifferentiableOn ℂ (invFunOn φ D) H := fun w hw => by
    obtain ⟨z, -, -, h, -⟩ := hder w hw
    exact h.differentiableAt.differentiableWithinAt
  refine ⟨hdiff, fun w hw => ?_, ?_, fun w hw => invFunOn_mem (hb.surjOn hw)⟩
  · obtain ⟨z, -, -, h, hne⟩ := hder w hw
    rw [h.deriv]
    exact inv_ne_zero hne
  · classical
    have hc : ContinuousOn (invFunOn φ D) Hᶜ := by
      refine continuousOn_const (c := invFunOn φ D (-Complex.I)) |>.congr fun w hw => ?_
      have hn : ∀ v : ℂ, v ∉ H → ¬∃ z ∈ D, φ z = v := fun v hv ⟨z, hz, hzv⟩ =>
        hv (hzv ▸ hb.mapsTo hz)
      have hI : -Complex.I ∉ H := by
        show ¬ (0 < (-Complex.I).im); simp
      rw [invFunOn_neg (hn w hw), invFunOn_neg (hn _ hI)]
    have := ContinuousOn.measurable_piecewise hdiff.continuousOn hc isOpen_H.measurableSet
    rwa [Set.piecewise_same] at this

/-! ## 2. Coordinate change by `ψ ∘ (b ·)` versus rescaling -/

theorem deriv_mul_left_const (b : ℝ) (z : ℂ) : deriv (fun w : ℂ => (b : ℂ) * w) z = b := by
  simp

/-- Raw value at a folded circle: `coordChange y (ψ ∘ (b ·)) Q (fc(d,r)) =
coordChange y ψ Q (fc(b d, b r)) + Q log b`. -/
theorem coordChange_comp_mul_fc (y : FieldSample) (Q : ℝ) {ψ : ℂ → ℂ}
    (hψd : DifferentiableOn ℂ ψ H) (hψ0 : ∀ w ∈ H, deriv ψ w ≠ 0) (hψm : Measurable ψ)
    {b : ℝ} (hb : 0 < b) (d : ℂ) {r : ℝ} (hr : 0 < r)
    (hint : Integrable (fun z => Real.log ‖deriv ψ z‖) (foldedCircle ((b : ℂ) * d) (b * r))) :
    coordChange y (fun w => ψ ((b : ℂ) * w)) Q (foldedCircle d r) =
      coordChange y ψ Q (foldedCircle ((b : ℂ) * d) (b * r)) + Q * Real.log b := by
  have hFm : Measurable (fun w : ℂ => (b : ℂ) * w) := measurable_const_mul _
  have hmap := WedgeTK.fc_map_mul d r hb
  have hae := TwoPoint.foldedCircle_ae_mem_H d hr
  have hμ : (foldedCircle d r) Hᶜ = 0 := ae_iff.1 hae
  have hFH : MapsTo (fun w : ℂ => (b : ℂ) * w) H H := fun w hw => mul_mem_H hb hw
  have hi2 : Integrable (fun z => Real.log ‖deriv (fun w : ℂ => (b : ℂ) * w) z‖)
      (foldedCircle d r) := by
    simp only [deriv_mul_left_const]; exact integrable_const _
  have hint' : Integrable (fun z => Real.log ‖deriv ψ ((b : ℂ) * z)‖) (foldedCircle d r) := by
    rw [← hmap] at hint
    exact hint.comp_measurable hFm
  have hi1 : Integrable (fun z => Real.log ‖deriv (fun w => ψ ((b : ℂ) * w)) z‖)
      (foldedCircle d r) := by
    refine (hint'.add (integrable_const (Real.log b))).congr ?_
    filter_upwards [hae] with z hz
    rw [deriv_comp_mul_left, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb.le,
      Real.log_mul hb.ne' (norm_ne_zero_iff.2 (hψ0 _ (hFH hz)))]
    simp only [Pi.add_apply]
    ring
  rw [B2.coordChange_comp_of_eqOn y Q (Φ := fun w => ψ ((b : ℂ) * w)) (G := ψ)
    (F := fun w : ℂ => (b : ℂ) * w) (fun _ _ => rfl) hμ hFH (by fun_prop) hψd hψ0
    (fun z _ => by rw [deriv_mul_left_const]; exact_mod_cast hb.ne') hFm hψm hi1 hi2, hmap,
    RegClosure.integral_log_deriv_mul hb]

/-- The rescaling of `x` by `b` at a folded circle, with no regularity: its regularized value at
the dilated circle, plus `Q log b`. -/
theorem rescale_fc_apply (x : FieldSample) (Q : ℝ) {b : ℝ} (hb : 0 < b) (d : ℂ) (r : ℝ) :
    rescale x Q b (foldedCircle d r) =
      evalReg x (foldedCircle (foldH ((b : ℂ) * d)) (b * r)) + Q * Real.log b := by
  unfold rescale coordChange
  rw [WedgeTK.fc_map_mul d r hb, RegClosure.integral_log_deriv_mul hb, WedgeTK.fc_foldH_eq]

/-- **Coordinate change by `ψ ∘ (b ·)` is the rescaling by `b`**, up to `RegEq`, when `log|ψ'|`
is integrable on folded circles and the folded-circle values of `x = coordChange y ψ Q` are its
regularized ones. -/
theorem regEq_coordChange_comp_mul (y : FieldSample) (Q : ℝ) {ψ : ℂ → ℂ}
    (hψd : DifferentiableOn ℂ ψ H) (hψ0 : ∀ w ∈ H, deriv ψ w ≠ 0) (hψm : Measurable ψ)
    {b : ℝ} (hb : 0 < b)
    (hint : ∀ d ∈ Hbar, ∀ r > 0,
      Integrable (fun z => Real.log ‖deriv ψ z‖) (foldedCircle d r))
    (hexact : ∀ d ∈ Hbar, ∀ r > 0,
      evalReg (coordChange y ψ Q) (foldedCircle d r) = coordChange y ψ Q (foldedCircle d r)) :
    RegEq (coordChange y (fun w => ψ ((b : ℂ) * w)) Q) (rescale (coordChange y ψ Q) Q b) := by
  have key : ∀ d : ℂ, ∀ r > 0, coordChange y (fun w => ψ ((b : ℂ) * w)) Q (foldedCircle d r) =
      rescale (coordChange y ψ Q) Q b (foldedCircle d r) := by
    intro d r hr
    have hbr : 0 < b * r := mul_pos hb hr
    have hH := CircleFubini.foldH_mem_Hbar' ((b : ℂ) * d)
    have hint' := hint _ hH _ hbr
    rw [WedgeTK.fc_foldH_eq] at hint'
    rw [coordChange_comp_mul_fc y Q hψd hψ0 hψm hb d hr hint', rescale_fc_apply _ Q hb,
      hexact _ hH _ hbr, WedgeTK.fc_foldH_eq]
  intro k z
  unfold avgReg
  simp_rw [key _ _ (radius_pos k)]

/-! ## 3. Canonical descriptions -/

/-- If `ψ' = ψ ∘ (b ·)` on `ℍ`, the canonical description of `coordChange y ψ' Q` *equals* that of
the rescaling by `b` of `coordChange y ψ Q` (hypotheses of `regEq_coordChange_comp_mul`). -/
theorem canonical_coordChange_eq_of_eqOn (γ : ℝ) (y : FieldSample) (Q : ℝ) {ψ ψ' : ℂ → ℂ}
    (hψd : DifferentiableOn ℂ ψ H) (hψ0 : ∀ w ∈ H, deriv ψ w ≠ 0) (hψm : Measurable ψ)
    {b : ℝ} (hb : 0 < b) (heq : EqOn ψ' (fun w => ψ ((b : ℂ) * w)) H)
    (hint : ∀ d ∈ Hbar, ∀ r > 0,
      Integrable (fun z => Real.log ‖deriv ψ z‖) (foldedCircle d r))
    (hexact : ∀ d ∈ Hbar, ∀ r > 0,
      evalReg (coordChange y ψ Q) (foldedCircle d r) = coordChange y ψ Q (foldedCircle d r)) :
    canonical γ (coordChange y ψ' Q) = canonical γ (rescale (coordChange y ψ Q) Q b) := by
  have h1 : avgReg (coordChange y ψ' Q) = avgReg (coordChange y (fun w => ψ ((b : ℂ) * w)) Q) :=
    funext fun k => funext fun z => CoordReg.avgReg_coordChange_congr y heq Q k z
  have h2 := regEq_coordChange_comp_mul y Q hψd hψ0 hψm hb hint hexact
  rw [Factorization.canonical_congr h1, Factorization.canonical_congr
    (funext fun k => funext fun z => h2 k z)]

/-- The circle coordinates of the canonical description do not depend on the choice
`ψ` versus `ψ' = ψ ∘ (b ·)` (for a good pulled-back field with positive scale parameter). -/
theorem coordsFull_canonical_coordChange_eq {γ : ℝ} (hγ : 0 < γ) (y : FieldSample)
    {ψ ψ' : ℂ → ℂ}
    (hψd : DifferentiableOn ℂ ψ H) (hψ0 : ∀ w ∈ H, deriv ψ w ≠ 0) (hψm : Measurable ψ)
    {b : ℝ} (hb : 0 < b) (heq : EqOn ψ' (fun w => ψ ((b : ℂ) * w)) H)
    (hint : ∀ d ∈ Hbar, ∀ r > 0,
      Integrable (fun z => Real.log ‖deriv ψ z‖) (foldedCircle d r))
    (hexact : ∀ d ∈ Hbar, ∀ r > 0, evalReg (coordChange y ψ (Qc γ)) (foldedCircle d r) =
      coordChange y ψ (Qc γ) (foldedCircle d r))
    (hgood : IsLQGGood γ (coordChange y ψ (Qc γ)))
    (hs : 0 < scaleParam γ (coordChange y ψ (Qc γ))) :
    CoordsFull.coordsFull (canonical γ (coordChange y ψ' (Qc γ))) =
      CoordsFull.coordsFull (canonical γ (coordChange y ψ (Qc γ))) := by
  rw [canonical_coordChange_eq_of_eqOn γ y (Qc γ) hψd hψ0 hψm hb heq hint hexact]
  exact S5.FieldShift.coordsFull_canonical_rescale hγ hgood hb hs

/-! ## 4. Test pairings -/

/-- The signed-part measure `ρ dz` (positive part) used by `pairRaw`. -/
abbrev tmeas (ρ : ℂ → ℝ) : Measure ℂ := volume.withDensity fun z => ENNReal.ofReal (ρ z)

/-- **Scale consistency of the regularization** of `x` at the measure `ν`: regularizing the
rescaled field `rescale x Q b` at `ν` is regularizing `x` at the dilated measure, plus the
constant `Q log b` times the mass. For a regular sample this says that the limits of the
smoothed pairings along the radii `2^{-k}` and `b 2^{-k}` agree (cf.
`PairLim.ae_tendsto_scaled_radius` for the free field). -/
def ScaleConsistentAt (x : FieldSample) (Q b : ℝ) (ν : Measure ℂ) : Prop :=
  evalReg (rescale x Q b) ν =
    evalReg x (ν.map fun z => (b : ℂ) * z) + Q * Real.log b * ν.real univ

theorem integral_log_deriv_mul' {c : ℝ} (hc : 0 < c) (ν : Measure ℂ) :
    ∫ z, Real.log ‖deriv (fun z : ℂ => (c : ℂ) * z) z‖ ∂ν = ν.real univ * Real.log c := by
  simp only [deriv_mul_left_const, Complex.norm_real, Real.norm_of_nonneg hc.le, integral_const,
    smul_eq_mul]

/-- One signed part of the pairing of `canonical γ (rescale x Q b)`. -/
theorem canonical_rescale_apply_map {γ : ℝ} (hγ : 0 < γ) {x : FieldSample} (hx : IsLQGGood γ x)
    {b : ℝ} (hb : 0 < b) (hs : 0 < scaleParam γ x) (ν : Measure ℂ)
    (hsc : ScaleConsistentAt x (Qc γ) b (ν.map fun z => ((scaleParam γ x / b : ℝ) : ℂ) * z)) :
    canonical γ (rescale x (Qc γ) b) ν = canonical γ x ν := by
  have hsb : 0 < scaleParam γ x / b := div_pos hs hb
  unfold canonical
  rw [GoodTransforms.scaleParam_rescale hx hγ hb]
  unfold ScaleConsistentAt at hsc
  set x' := rescale x (Qc γ) b with hx'
  unfold rescale coordChange
  rw [integral_log_deriv_mul' hsb, integral_log_deriv_mul' hs]
  rw [hsc, Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
  have e : ((fun z : ℂ => (b : ℂ) * z) ∘ fun z : ℂ => ((scaleParam γ x / b : ℝ) : ℂ) * z) =
      fun z : ℂ => (scaleParam γ x : ℂ) * z := by
    funext z
    simp only [Function.comp]
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_div_cancel₀ _ hb.ne']
  have hm : (ν.map fun z => ((scaleParam γ x / b : ℝ) : ℂ) * z).real univ = ν.real univ := by
    simp only [measureReal_def]
    rw [Measure.map_apply (measurable_const_mul _) MeasurableSet.univ, preimage_univ]
  rw [e, hm, Real.log_div hs.ne' hb.ne']
  ring

/-- The raw test pairings of `canonical γ (rescale x Q b)` and `canonical γ x` agree, under
scale consistency at the two signed parts. -/
theorem pairRaw_canonical_rescale {γ : ℝ} (hγ : 0 < γ) {x : FieldSample} (hx : IsLQGGood γ x)
    {b : ℝ} (hb : 0 < b) (hs : 0 < scaleParam γ x) (ρ : ℂ → ℝ)
    (hsc : ∀ σ : ℂ → ℝ, (σ = ρ ∨ σ = fun z => -ρ z) →
      ScaleConsistentAt x (Qc γ) b ((tmeas σ).map fun z => ((scaleParam γ x / b : ℝ) : ℂ) * z)) :
    pairRaw (canonical γ (rescale x (Qc γ) b)) ρ = pairRaw (canonical γ x) ρ := by
  unfold pairRaw
  rw [canonical_rescale_apply_map hγ hx hb hs _ (hsc ρ (Or.inl rfl)),
    canonical_rescale_apply_map hγ hx hb hs _ (hsc _ (Or.inr rfl))]

/-- The regularity package of the pulled-back field `x = coordChange y ψ Q` used to compare
choices of uniformizer: `log|ψ'|` integrable on folded circles, folded-circle values equal to
regularized ones (RC3), goodness, positive scale parameter, and scale consistency at the
dilated test measures. -/
def ChoiceRegular (γ : ℝ) (y : FieldSample) (ψ : ℂ → ℂ) : Prop :=
  (∀ d ∈ Hbar, ∀ r > 0, Integrable (fun z => Real.log ‖deriv ψ z‖) (foldedCircle d r)) ∧
  (∀ d ∈ Hbar, ∀ r > 0, evalReg (coordChange y ψ (Qc γ)) (foldedCircle d r) =
      coordChange y ψ (Qc γ) (foldedCircle d r)) ∧
  IsLQGGood γ (coordChange y ψ (Qc γ)) ∧ 0 < scaleParam γ (coordChange y ψ (Qc γ)) ∧
  ∀ b : ℝ, 0 < b → ∀ c : ℝ, 0 < c → ∀ ρ : TestFun H, ∀ σ : ℂ → ℝ, (σ = ρ.1 ∨ σ = fun z => -ρ.1 z) →
    ScaleConsistentAt (coordChange y ψ (Qc γ)) (Qc γ) b
      ((tmeas σ).map fun z => (c : ℂ) * z)

/-- **Choice-independence of the canonical data.** If `ψ' = ψ ∘ (b ·)` on `ℍ` and the
pulled-back field of `ψ` is `ChoiceRegular`, the canonical descriptions for `ψ` and `ψ'` have
the same circle coordinates and the same raw test pairings (i.e. the same `fieldLawFull` data). -/
theorem data_canonical_coordChange_eq {γ : ℝ} (hγ : 0 < γ) (y : FieldSample) {ψ ψ' : ℂ → ℂ}
    (hψd : DifferentiableOn ℂ ψ H) (hψ0 : ∀ w ∈ H, deriv ψ w ≠ 0) (hψm : Measurable ψ)
    {b : ℝ} (hb : 0 < b) (heq : EqOn ψ' (fun w => ψ ((b : ℂ) * w)) H)
    (hreg : ChoiceRegular γ y ψ) :
    (CoordsFull.coordsFull (canonical γ (coordChange y ψ' (Qc γ))),
      fun ρ : TestFun H => pairRaw (canonical γ (coordChange y ψ' (Qc γ))) ρ.1) =
    (CoordsFull.coordsFull (canonical γ (coordChange y ψ (Qc γ))),
      fun ρ : TestFun H => pairRaw (canonical γ (coordChange y ψ (Qc γ))) ρ.1) := by
  obtain ⟨hint, hexact, hgood, hs, hsc⟩ := hreg
  have hc := canonical_coordChange_eq_of_eqOn γ y (Qc γ) hψd hψ0 hψm hb heq hint hexact
  have h1 := coordsFull_canonical_coordChange_eq hγ y hψd hψ0 hψm hb heq hint hexact hgood hs
  have h2 : ∀ ρ : TestFun H, pairRaw (canonical γ (coordChange y ψ' (Qc γ))) ρ.1 =
      pairRaw (canonical γ (coordChange y ψ (Qc γ))) ρ.1 := fun ρ => by
    rw [hc]
    exact pairRaw_canonical_rescale hγ hgood hb hs ρ.1 fun σ hσ =>
      hsc b hb _ (div_pos hs hb) ρ σ hσ
  exact Prod.ext h1 (funext h2)

end G1
end Thm18Asm
end QuantumZipper
