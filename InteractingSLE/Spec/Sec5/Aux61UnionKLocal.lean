/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61UnionKWire
import InteractingSLE.GFF.LocalSets.MarkedAvoidance

/-!
# One conditional local-set statement in the chart gives both the chart law and glued locality

Packet PROVE-AUX61-FIBK. Astra's follow-up 4 §1.1 (`source/external/AstraIG1/ig1_followup4_audited.txt` L68–L148,
ruling R71: "the field in each selected complementary component has the form `h_D = h⁰_D + M_D` conditionally, where
`h⁰_D` is a zero-boundary GFF and `M_D` is the retained harmonic mean") read in the restart chart, with Aux. lemma 61's
identity (1.1) for the mean (L150–L176).

**`IsChartLocalAt μ Z B Y q M h₁`** (on the glued space `X`, for one index of a cover with history `Z`, history event
`B`, code `Y` whose field component is the chart field): at the deterministic fibre time `q`, on `{Z ∈ B, q < life}`,
* `h₁` (measurable) is harmonic off the chart hull `K_q` and pairs there like `M`;
* conditionally on the marks `σ(Z) ∨ σ(raw code at q) ∨ σ(h₁)`, the chart field minus `h₁` is a zero-boundary GFF on
  `ℍ ∖ K_q` (its conditional characteristic functional at every test is `exp(−½ ‖φ‖²_{H⁻¹(ℍ∖K_q)})`).

This is the marked local-set decomposition of the chart field at the restarted chart hull — the content of
GlueK's (K-a) and of glued projection independence at once. Results:

* **`condExp_cexp_eq_cfVal_of_chartLocal`**: the conditional characteristic functional of the chart field at a test
  off `K_q` given the marks is `cfVal (∫ M ψ) (E_q(ψ))` (`E_q` the Loewner Green energy);
* **`fibreChart_of_chartLocal`**: hence `Wire.Dawn.FibreChart` with the marks as conditioning σ-algebras;
* **`setIntegral_cexp_lapTest_of_chartLocal`**, **`fibreLocal_of_chartLocal`**: the harmonic part annihilates the
  Dirichlet directions of balls off the hull, and the Gaussian shift rule of the zero-boundary GFF on `ℍ ∖ K_s ⊇ ⋃F`
  does not depend on the domain (`Coupling.norm_covVec_lapTest_add_sq`); so `Wire.Dawn.FibreLocal` holds — glued
  projection independence is NOT a separate input;
* **`HasFibreLocalCover`**, **`hasFibreKernelCover_of_localCover`**, **`GluedLocalCoverOn`**,
  **`dyCover_of_localCoverOn`**: the bundled cover whose only analytic leaf is `IsChartLocalAt` at every fibre time with
  the canonical (PC1) candidate mean (`Aux61UnionK.canonMean`), giving `DyActFibreCoverOn (¬ IsLargeGap) RefWin`.

Conditional helpers with distinct names; they replace no source theorem. R48/R77: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement`, any `*_of_param` result, or Astra's post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Function
open QuantumZipper (H chiC fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real RealInnerProductSpace

namespace InteractingSLE.Sec5.Aux61UnionK

open Aux61Fib (FibCode FibData PathGood fibW fibΓ fibU fibField)
open Aux61FibK (ratAvoid ratψ ratPi codeFiltration)
open Restart.DomainMarkov (RatIdx dyT safeEv ballsOpen)
open LocalExt (cfVal)

universe u

/-! ### The conditional local-set decomposition in the chart -/

section Local

variable {X : Type u} [mX : MeasurableSpace X] {β : Type*} [mβ : MeasurableSpace β]

/-- **The chart hull** of the code of `x` at fibre time `q` (the hull of its decoded driver). -/
def chartHull (Y : X → FibCode) (q : ℝ≥0) (x : X) : Set ℂ :=
  fwdHull (fun r : ℝ => FibCode.driver r.toNNReal (Y x)) q

/-- **The marks at fibre time `q`**: the history, the raw code σ-algebra at `q`, and the harmonic part `h₁`. -/
abbrev chartMarks (Z : X → β) (Y : X → FibCode) (q : ℝ≥0) (h₁ : X → DistOn upperHalfPlaneOpens) :
    MeasurableSpace X :=
  mβ.comap Z ⊔ (codeFiltration.{u} q).comap (fun x => ULift.up.{u} (Y x)) ⊔
    (inferInstance : MeasurableSpace (DistOn upperHalfPlaneOpens)).comap h₁

/-- **The conditional local-set decomposition of the chart field at fibre time `q`** (Astra §1.1 read in the chart,
with mean `M`): on `{Z ∈ B, q < life}`, `h₁` is harmonic off the chart hull `K_q` and pairs there like `M`, and given
the marks `σ(Z) ∨ σ(code at q) ∨ σ(h₁)` the chart field minus `h₁` is a zero-boundary GFF on `ℍ ∖ K_q`. -/
structure IsChartLocalAt (μ : Measure X) (Z : X → β) (B : Set β) (Y : X → FibCode) (q : ℝ≥0)
    (M : X → ℂ → ℝ) (h₁ : X → DistOn upperHalfPlaneOpens) : Prop where
  measurable : Measurable h₁
  harmonic : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → IsHarmonicDistOn (h₁ x) (H \ chartHull Y q x)
  mean : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → ∀ ψ : TestOn upperHalfPlaneOpens,
    Disjoint (tsupport ψ) (chartHull Y q x) → h₁ x ψ = ∫ z, M x z * ψ z
  gff : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life →
    μ[fun x' => Complex.exp (Complex.I * (((Y x').field φ - h₁ x' φ : ℝ) : ℂ)) | chartMarks Z Y q h₁] x =
      ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ chartHull Y q x) φ φ) : ℝ) : ℂ)

/-- **Splitting the leaf into (K-a) and (K-b)**: a local-set decomposition whose mean `M` satisfies Aux. lemma 61's
(PC1) (relative to the canonical reference extension, the data's correction and window) is the decomposition with the
canonical candidate mean, on codes with the path facts and a cutoff of the data's correction near the buffer. -/
theorem IsChartLocalAt.canon_of_isPC1 {μ : Measure X} {Z : X → β} {B : Set β} {Y : X → FibCode} {q : ℝ≥0}
    {M : X → ℂ → ℝ} {h₁ : X → DistOn upperHalfPlaneOpens} (hL : IsChartLocalAt μ Z B Y q M h₁)
    (d : β → FibData) (F₀ : β → Restart.FlowStopIdentCMI.CMCut) (N₀ : β → Set ℂ)
    (hcut : ∀ z ∈ B, Aux61Win.IsCutoffOn (F₀ z) (d z).q (N₀ z) (d z).O₀ ∧ (d z).buffer ⊆ N₀ z)
    (hgood : ∀ᵐ x ∂μ, Z x ∈ B → PathGood (d (Z x)) (Y x))
    (hPC : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life →
      Aux61Win.IsPC1 (d (Z x)).κ (Aux61FibK.canonExt (d (Z x)) (ULift.up.{u} (Y x)) q)
        (Ito.rpath fun r => fibW r (ULift.up.{u} (Y x))) q (d (Z x)).q (d (Z x)).O₀ (M x)) :
    IsChartLocalAt μ Z B Y q (fun x => canonMean (d (Z x)) (F₀ (Z x)) (ULift.up.{u} (Y x)) q) h₁ := by
  refine ⟨hL.measurable, hL.harmonic, ?_, hL.gff⟩
  filter_upwards [hL.mean, hgood, hPC] with x hm hg hpc hB hlt ψ hψ
  rw [hm hB hlt ψ hψ]
  exact integral_eq_canonMean_of_isPC1 (hcut _ hB).1 (hcut _ hB).2 (hg hB) hlt (hpc hB hlt) ψ hψ

omit [MeasurableSpace X] in
theorem isOpen_H_diff_chartHull (Y : X → FibCode) {q : ℝ≥0} {x : X} (hq : (q : ℝ≥0∞) < (Y x).life) :
    IsOpen (H \ chartHull Y q x) :=
  Coupling.MartMeans2.isOpen_H_diff_fwdHull_rpath (w := fun t => FibCode.driver t (Y x))
    (FibCode.continuous_driver (Y x)).continuousOn hq

theorem measurable_apply_of_measurable {h : X → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (φ : TestOn upperHalfPlaneOpens) : Measurable fun x => h x φ :=
  (measurable_pi_apply φ).comp ((LQGMetric.measurable_distEval _).comp hh)

theorem measurable_field_apply {Y : X → FibCode} (hY : Measurable Y) (φ : TestOn upperHalfPlaneOpens) :
    Measurable fun x => (Y x).field φ :=
  measurable_apply_of_measurable (FibCode.measurable_field.comp hY) φ

theorem chartMarks_le {Z : X → β} (hZ : Measurable Z) {Y : X → FibCode} (hY : Measurable Y) (q : ℝ≥0)
    {h₁ : X → DistOn upperHalfPlaneOpens} (hh : Measurable h₁) : chartMarks Z Y q h₁ ≤ mX := by
  have hY' : Measurable fun x => ULift.up.{u} (Y x) := measurable_up.comp hY
  refine sup_le (sup_le hZ.comap_le ?_) hh.comap_le
  exact (MeasurableSpace.comap_mono ((codeFiltration.{u}).le q)).trans hY'.comap_le

omit mX in
theorem measurable_marks_h₁ (Z : X → β) (Y : X → FibCode) (q : ℝ≥0) (h₁ : X → DistOn upperHalfPlaneOpens)
    (φ : TestOn upperHalfPlaneOpens) : Measurable[chartMarks Z Y q h₁] fun x => h₁ x φ := by
  have h : Measurable[(inferInstance : MeasurableSpace (DistOn upperHalfPlaneOpens)).comap h₁] h₁ :=
    comap_measurable h₁
  exact (measurable_apply_of_measurable (mX := _) h φ).mono le_sup_right le_rfl

omit mX in
theorem measurableSet_marks_Z (Z : X → β) (Y : X → FibCode) (q : ℝ≥0) (h₁ : X → DistOn upperHalfPlaneOpens)
    {B' : Set β} (hB' : MeasurableSet B') : MeasurableSet[chartMarks Z Y q h₁] (Z ⁻¹' B') :=
  (le_sup_left.trans le_sup_left : mβ.comap Z ≤ chartMarks Z Y q h₁) _ ⟨B', hB', rfl⟩

omit mX in
theorem measurableSet_marks_code (Z : X → β) (Y : X → FibCode) (q : ℝ≥0) (h₁ : X → DistOn upperHalfPlaneOpens)
    {S : Set (ULift.{u} FibCode)} (hS : MeasurableSet[codeFiltration.{u} q] S) :
    MeasurableSet[chartMarks Z Y q h₁] ((fun x => ULift.up.{u} (Y x)) ⁻¹' S) :=
  (le_sup_right.trans le_sup_left :
    (codeFiltration.{u} q).comap (fun x => ULift.up.{u} (Y x)) ≤ chartMarks Z Y q h₁) _ ⟨S, hS, rfl⟩

/-- A unit complex exponential is bounded by one. -/
theorem norm_cexp_I_mul_ofReal_le (a : ℝ) : ‖Complex.exp (Complex.I * (a : ℂ))‖ ≤ 1 :=
  (Complex.norm_exp_I_mul_ofReal a).le

/-- The pull-out step: on the marks, `e^{i field(φ)} = e^{i h₁(φ)} e^{i (field − h₁)(φ)}` and the first factor is
measurable for the marks, so the conditional characteristic functional is `e^{i h₁(φ)}` times that of `field − h₁`. -/
theorem condExp_cexp_field_eq {μ : Measure X} [IsFiniteMeasure μ] {Z : X → β} (hZ : Measurable Z)
    {Y : X → FibCode} (hY : Measurable Y) (q : ℝ≥0) {h₁ : X → DistOn upperHalfPlaneOpens} (hh : Measurable h₁)
    (φ : TestOn upperHalfPlaneOpens) :
    μ[fun x' => Complex.exp (Complex.I * ((Y x').field φ : ℂ)) | chartMarks Z Y q h₁] =ᵐ[μ]
      fun x => Complex.exp (Complex.I * (h₁ x φ : ℂ)) *
        μ[fun x' => Complex.exp (Complex.I * (((Y x').field φ - h₁ x' φ : ℝ) : ℂ)) | chartMarks Z Y q h₁] x := by
  have hm : chartMarks Z Y q h₁ ≤ mX := chartMarks_le hZ hY q hh
  have hG : StronglyMeasurable[chartMarks Z Y q h₁] fun x => Complex.exp (Complex.I * (h₁ x φ : ℂ)) :=
    (Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp (measurable_marks_h₁ Z Y q h₁ φ)))).stronglyMeasurable
  have hgm : Measurable fun x => Complex.exp (Complex.I * (((Y x).field φ - h₁ x φ : ℝ) : ℂ)) :=
    Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      ((measurable_field_apply hY φ).sub (measurable_apply_of_measurable hh φ))))
  have hg : Integrable (fun x => Complex.exp (Complex.I * (((Y x).field φ - h₁ x φ : ℝ) : ℂ))) μ :=
    Integrable.of_bound hgm.aestronglyMeasurable 1 (ae_of_all _ fun x => norm_cexp_I_mul_ofReal_le _)
  have h1 := condExp_stronglyMeasurable_bilin_of_bound (ContinuousLinearMap.mul ℝ ℂ) hm hG hg 1
    (ae_of_all _ fun x => norm_cexp_I_mul_ofReal_le _)
  have e : (fun x' => Complex.exp (Complex.I * ((Y x').field φ : ℂ))) = fun x =>
      (ContinuousLinearMap.mul ℝ ℂ) (Complex.exp (Complex.I * (h₁ x φ : ℂ)))
        (Complex.exp (Complex.I * (((Y x).field φ - h₁ x φ : ℝ) : ℂ))) := by
    funext x
    rw [ContinuousLinearMap.mul_apply', ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e]
  exact h1.trans (ae_of_all _ fun x => by simp only [ContinuousLinearMap.mul_apply'])

/-- **The chart law from the local-set decomposition**: at a test `ψ` off the chart hull, on `{Z ∈ B, q < life}`,
the conditional characteristic functional of the chart field given the marks is `cfVal (∫ M ψ) (E_q(ψ))`. -/
theorem condExp_cexp_eq_cfVal_of_chartLocal {μ : Measure X} [IsFiniteMeasure μ] {Z : X → β} (hZ : Measurable Z)
    {B : Set β} {Y : X → FibCode} (hY : Measurable Y) {q : ℝ≥0} {M : X → ℂ → ℝ}
    {h₁ : X → DistOn upperHalfPlaneOpens} (hL : IsChartLocalAt μ Z B Y q M h₁) (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → Disjoint (tsupport ψ) (chartHull Y q x) →
      μ[fun x' => Complex.exp (Complex.I * ((Y x').field ψ : ℂ)) | chartMarks Z Y q h₁] x =
        cfVal (∫ z, M x z * ψ z) (loewnerGreenEnergy (Ito.rpath fun r => FibCode.driver r (Y x)) q ψ) := by
  filter_upwards [condExp_cexp_field_eq (μ := μ) hZ hY q hL.measurable ψ, hL.mean, hL.gff ψ] with x h1 hmean hgff
    hB hlt hdis
  rw [h1, hgff hB hlt, hmean hB hlt ψ hdis]
  have he : loewnerGreenEnergy (Ito.rpath fun r => FibCode.driver r (Y x)) q ψ =
      zeroGFFTestCov (H \ chartHull Y q x) ψ ψ :=
    WholeField.loewnerGreenEnergy_rpath_eq_zeroGFFTestCov (w := fun t => FibCode.driver t (Y x))
      (FibCode.continuous_driver (Y x)).continuousOn (FibCode.driver_zero (Y x)) hlt ψ hdis
  rw [he, cfVal, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring


/-- **The Gaussian shift factor of a domain containing the balls**: for an open `D ⊆ ℍ` containing `V`, the
zero-boundary covariance of `D` in the direction `−Δf/2π + Ξ` splits off `projFactor V f Ξ`, which does not depend on
`D`. -/
theorem exp_zeroGFFTestCov_lapTest_add {D : Set ℂ} (hD : IsOpen D) (hDH : D ⊆ H) {V : TopologicalSpace.Opens ℂ}
    (hVD : (V : Set ℂ) ⊆ D) (f : LQGMetric.MarkovZB.zsSub (V : Set ℂ)) (Ξ Φ : TestOn upperHalfPlaneOpens)
    (hΦ : Φ = LocalSets.lapTest V f + Ξ) :
    ((Real.exp (-(1 / 2) * zeroGFFTestCov D Φ Φ) : ℝ) : ℂ) =
      Coupling.projFactor V f Ξ * ((Real.exp (-(1 / 2) * zeroGFFTestCov D Ξ Ξ) : ℝ) : ℂ) := by
  subst hΦ
  rw [LocalSets.zeroGFFTestCov_eq_inner_covVec hD hDH, LocalSets.zeroGFFTestCov_eq_inner_covVec hD hDH,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, Coupling.norm_covVec_lapTest_add_sq hD hDH hVD f Ξ,
    Coupling.projFactor, Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Glued projection independence from the local-set decomposition**: on a marks-measurable event `R` inside
`{Z ∈ B, s < life}` on which the open set `V` avoids the chart hull `K_s`, the chart field's characteristic functional
in the Dirichlet direction `−Δf/2π`, `f ∈ C_c^∞(V)`, carries the Gaussian factor of `H(V)`. -/
theorem setIntegral_cexp_lapTest_of_chartLocal {μ : Measure X} [IsFiniteMeasure μ] {Z : X → β}
    (hZ : Measurable Z) {B : Set β} {Y : X → FibCode} (hY : Measurable Y) {s : ℝ≥0} {M : X → ℂ → ℝ}
    {h₁ : X → DistOn upperHalfPlaneOpens} (hL : IsChartLocalAt μ Z B Y s M h₁) {V : TopologicalSpace.Opens ℂ}
    (hVH : (V : Set ℂ) ⊆ H) {R : Set X} (hR : MeasurableSet[chartMarks Z Y s h₁] R)
    (hRB : ∀ x ∈ R, Z x ∈ B ∧ (s : ℝ≥0∞) < (Y x).life ∧ (V : Set ℂ) ⊆ H \ chartHull Y s x)
    (f : LQGMetric.MarkovZB.zsSub (V : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) :
    ∫ x in R, Complex.exp (Complex.I * ((Y x).field (LocalSets.lapTest V f + Ξ) : ℂ)) ∂μ =
      Coupling.projFactor V f Ξ * ∫ x in R, Complex.exp (Complex.I * ((Y x).field Ξ : ℂ)) ∂μ := by
  have hm : chartMarks Z Y s h₁ ≤ mX := chartMarks_le hZ hY s hL.measurable
  have hRm : MeasurableSet R := hm R hR
  have hint : ∀ φ : TestOn upperHalfPlaneOpens,
      Integrable (fun x => Complex.exp (Complex.I * ((Y x).field φ : ℂ))) μ := fun φ =>
    Integrable.of_bound (Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp (measurable_field_apply hY φ)))).aestronglyMeasurable 1
      (ae_of_all _ fun x => norm_cexp_I_mul_ofReal_le _)
  set Φ : TestOn upperHalfPlaneOpens := LocalSets.lapTest V f + Ξ with hΦ
  rw [← setIntegral_condExp hm (hint Φ) hR, ← setIntegral_condExp hm (hint Ξ) hR, ← integral_const_mul]
  refine setIntegral_congr_ae hRm ?_
  filter_upwards [condExp_cexp_field_eq (μ := μ) hZ hY s hL.measurable Φ,
    condExp_cexp_field_eq (μ := μ) hZ hY s hL.measurable Ξ, hL.harmonic, hL.gff Φ, hL.gff Ξ] with
    x h1 h2 hharm hgΦ hgΞ hxR
  obtain ⟨hxB, hlt, hVK⟩ := hRB x hxR
  have hU := isOpen_H_diff_chartHull Y hlt
  have hlap : h₁ x (LocalSets.lapTest V f) = 0 :=
    LocalSets.IsHarmonicDistOn.apply_lapTest_eq_zero hU (hharm hxB hlt) hVH hVK f
  have hh₁ : h₁ x Φ = h₁ x Ξ := by rw [hΦ, map_add, hlap, zero_add]
  rw [h1, h2, hgΦ hxB hlt, hgΞ hxB hlt, hh₁,
    exp_zeroGFFTestCov_lapTest_add hU sdiff_subset hVK f Ξ Φ hΦ]
  ring

end Local

/-! ### The cover-level consequences -/

section Cover

open Sec4 Sec5.Aux61Cov Sec5.Prop51G Sec5.Aux61Kernel Sec5.Cond44Ref Sec5.Aux61Act
open WangWu WholeField LocalSets Restart Exist.StagedLaw LocalExt Coupling LawUnique

variable {X : Type u} [mX : MeasurableSpace X]

/-- The canonical (PC1) candidate mean of index `i` at fibre time `q`, as a function of the glued sample. -/
def canonMeanAt (D : Wire.Night.FibreRecords X) (i : D.ι) (q : ℝ≥0) (x : X) : ℂ → ℝ :=
  canonMean (D.data i (D.Z i x)) (D.cutoff i (D.Z i x)) (ULift.up.{u} (D.Y i x)) q

/-- **The kernel data of a cover from harmonic parts**: the canonical means, and as conditioning σ-algebras the marks
`σ(Z) ∨ σ(code at k/2ⁿ) ∨ σ(h₁)`. -/
def localKernelData (D : Wire.Night.FibreRecords X) (kappa : D.ι → ℝ) (boundary : D.ι → ℝ → ℝ)
    (jumps : D.ι → Finset ℝ) (h₁ : D.ι → ℝ≥0 → X → DistOn upperHalfPlaneOpens) : Wire.Dawn.FibreKernelData D :=
  canonKernelData D kappa boundary jumps fun i n k => chartMarks (D.Z i) (D.Y i) (dyT n k) (h₁ i (dyT n k))

/-- **`FibreChart` from the local-set decompositions at the dyadic fibre times.** -/
theorem fibreChart_of_chartLocal {μ : Measure X} [IsFiniteMeasure μ] {E : X → Prop}
    (D : Wire.Night.FibreRecords X) (hg : Wire.Night.FibreGeometry μ E D) (kappa : D.ι → ℝ)
    (boundary : D.ι → ℝ → ℝ) (jumps : D.ι → Finset ℝ) (h₁ : D.ι → ℝ≥0 → X → DistOn upperHalfPlaneOpens)
    (hL : ∀ i (q : ℝ≥0), IsChartLocalAt μ (D.Z i) (D.B i) (D.Y i) q (canonMeanAt D i q) (h₁ i q)) :
    Wire.Dawn.FibreChart μ D (localKernelData D kappa boundary jumps h₁) := by
  obtain ⟨hZ, hY, -⟩ := hg
  intro i n k p
  filter_upwards [condExp_cexp_eq_cfVal_of_chartLocal (hZ i) (hY i) (hL i (dyT n k)) (ratψ p)] with x hx hxB hxA
  exact hx hxB hxA.1 hxA.2

/-- **`FibreLocal` from the local-set decompositions at the rational fibre times** (glued projection independence is
a consequence, not an input). -/
theorem fibreLocal_of_chartLocal {μ : Measure X} [IsFiniteMeasure μ] {E : X → Prop}
    (D : Wire.Night.FibreRecords X) (hg : Wire.Night.FibreGeometry μ E D) (M : D.ι → ℝ≥0 → X → ℂ → ℝ)
    (h₁ : D.ι → ℝ≥0 → X → DistOn upperHalfPlaneOpens)
    (hL : ∀ i (q : ℝ≥0), IsChartLocalAt μ (D.Z i) (D.B i) (D.Y i) q (M i q) (h₁ i q)) :
    Wire.Dawn.FibreLocal μ D := by
  obtain ⟨hZ, hY, -⟩ := hg
  intro i r s hrs F hFH T B' hB' hB'B
  have hVH : ((ballsOpen F : TopologicalSpace.Opens ℂ) : Set ℂ) ⊆ H :=
    (Coupling.ballsU_subset_ballsK F).trans hFH
  have hY' : Measurable fun x => ULift.up.{u} (D.Y i x) := measurable_up.comp (hY i)
  have hfm : Measurable fun x => fibField (ULift.up.{u} (D.Y i x)) := FibCode.measurable_field.comp (hY i)
  -- the rectangle is an event of the marks at `s`
  have hrs' : ((r : ℝ≥0) : ℝ≥0) ≤ (s : ℝ≥0) := by exact_mod_cast hrs.le
  have hr : MeasurableSet[codeFiltration.{u} (r : ℝ≥0)] (ratPi fibW.{u} fibU (r : ℝ≥0) T) := by
    rw [Aux61GlueK.codeFiltration_eq_generateFrom r]
    exact MeasurableSpace.measurableSet_generateFrom ⟨T, rfl⟩
  have hS : MeasurableSet[codeFiltration.{u} (s : ℝ≥0)]
      (ratPi fibW.{u} fibU (r : ℝ≥0) T ∩ safeEv fibW.{u} fibU F (s : ℝ≥0)) :=
    ((codeFiltration.{u}).mono hrs' _ hr).inter (Aux61GlueK.measurableSet_safeEv_fib hFH (s : ℝ≥0))
  have hR : MeasurableSet[chartMarks (D.Z i) (D.Y i) (s : ℝ≥0) (h₁ i (s : ℝ≥0))]
      (D.Z i ⁻¹' B' ∩ (fun x => ULift.up.{u} (D.Y i x)) ⁻¹'
        (ratPi fibW.{u} fibU (r : ℝ≥0) T ∩ safeEv fibW.{u} fibU F (s : ℝ≥0))) :=
    (measurableSet_marks_Z _ _ _ _ hB').inter (measurableSet_marks_code _ _ _ _ hS)
  have hRB : ∀ x ∈ D.Z i ⁻¹' B' ∩ (fun x => ULift.up.{u} (D.Y i x)) ⁻¹'
      (ratPi fibW.{u} fibU (r : ℝ≥0) T ∩ safeEv fibW.{u} fibU F (s : ℝ≥0)),
      D.Z i x ∈ D.B i ∧ ((s : ℝ≥0) : ℝ≥0∞) < (D.Y i x).life ∧
        ((ballsOpen F : TopologicalSpace.Opens ℂ) : Set ℂ) ⊆ H \ chartHull (D.Y i) (s : ℝ≥0) x := by
    rintro x ⟨hxB, -, hxs⟩
    refine ⟨hB'B hxB, hxs.1, fun z hz => ⟨hVH hz, fun hzK => ?_⟩⟩
    exact Set.disjoint_left.1 hxs.2 (Coupling.ballsU_subset_ballsK F hz) hzK
  intro f Ξ
  have hev : ∀ φ : TestOn upperHalfPlaneOpens,
      AEStronglyMeasurable (fun y : DistOn upperHalfPlaneOpens => Complex.exp (Complex.I * (y φ : ℂ)))
        ((μ.restrict (D.Z i ⁻¹' B' ∩ (fun x => ULift.up.{u} (D.Y i x)) ⁻¹'
          (ratPi fibW.{u} fibU (r : ℝ≥0) T ∩ safeEv fibW.{u} fibU F (s : ℝ≥0)))).map
            fun x => fibField (ULift.up.{u} (D.Y i x))) := fun φ =>
    (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      (measurable_apply_of_measurable measurable_id φ)))).aestronglyMeasurable
  rw [integral_map hfm.aemeasurable (hev _), integral_map hfm.aemeasurable (hev _)]
  exact setIntegral_cexp_lapTest_of_chartLocal (hZ i) (hY i) (hL i (s : ℝ≥0)) hVH hR hRB f Ξ

/-- **The fibre-local cover**: countable records covering the event with fixed reference words and measurable data,
and at every fibre time a harmonic part `h₁` for which the chart field has the conditional local-set decomposition
with the canonical (PC1) mean. -/
def HasFibreLocalCover (μ : Measure X) (E : X → Prop) : Prop :=
  ∃ (D : Wire.Night.FibreRecords X) (kappa : D.ι → ℝ) (boundary : D.ι → ℝ → ℝ) (jumps : D.ι → Finset ℝ)
    (h₁ : D.ι → ℝ≥0 → X → DistOn upperHalfPlaneOpens), Wire.Night.FibreGeometry μ E D ∧
    Wire.Dawn.FibreDataMeas D (localKernelData D kappa boundary jumps h₁) ∧
    ∀ i (q : ℝ≥0), IsChartLocalAt μ (D.Z i) (D.B i) (D.Y i) q (canonMeanAt D i q) (h₁ i q)

/-- **The fibre-local cover gives the bundled fibre-kernel cover** (all of Dawn's chart, (PC1), σ-algebra and
locality leaves are discharged). -/
theorem hasFibreKernelCover_of_localCover {μ : Measure X} [IsFiniteMeasure μ] {E : X → Prop}
    (h : HasFibreLocalCover μ E) : HasFibreKernelCover μ E := by
  obtain ⟨D, kappa, boundary, jumps, h₁, hg, hm, hL⟩ := h
  have hZ := hg.1
  have hY := hg.2.1
  refine ⟨D, localKernelData D kappa boundary jumps h₁, hg, hm, ⟨fun i n k => ?_, fun i n k => ?_,
    fun i n k => ?_⟩, fibreChart_of_chartLocal D hg kappa boundary jumps h₁ hL, fibrePC1_canon D hg _ _ _ _,
    fibreLocal_of_chartLocal D hg _ h₁ hL⟩
  · exact chartMarks_le (hZ i) (hY i) _ (hL i _).measurable
  · exact le_sup_left.trans le_sup_left
  · exact le_sup_right.trans le_sup_left

/-- **The fibre-local cover gives FIB2's dyadic fibre cover.** -/
theorem hasDyActFibreCover_of_localCover {μ : Measure X} [IsFiniteMeasure μ] {E : X → Prop}
    (h : HasFibreLocalCover μ E) : HasDyActFibreCover μ E RefWin :=
  hasDyActFibreCover_of_kernelCover (hasFibreKernelCover_of_localCover h)

end Cover

/-! ### The small-gap window settings -/

open Sec4 Sec5.Aux61Cov Sec5.Prop51G Sec5.Aux61Kernel Sec5.Cond44Ref Sec5.Aux61Act
open WangWu WholeField LocalSets Restart Exist.StagedLaw LocalExt Coupling LawUnique in
/-- **The fibre-local cover in every small-gap window setting** (the binders of `DyActFibreCoverOn`). -/
def GluedLocalCoverOn : Prop :=
  ∀ (t : ℚ) (c : WinCode), 0 < t →
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ a b θ₁ θ₂ : ℝ, θ₁ < θ₂ → ¬ IsLargeGap κ θ₁ θ₂ →
    sleLambda κ - θ₁ * chiC κ ≤ b → sleLambda κ - Real.pi * chiC κ + θ₂ * chiC κ ≤ a →
    ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
      (hh : IsGFFWithBoundaryData P h (Sec7.prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ)),
      IsFlowLine κ (Sec7.prop74Data a b) {0} 0 θ₂ P h η ζ →
      ∀ {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
        (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
        IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂ →
        P.map (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = P₂.map h₂ →
        ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
          P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k →
          ∀ s : ℚ, 0 < s →
            HasFibreLocalCover.{u}
              (glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
                ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)))
              (fun p => RestartWindowEvent (Prop411Q.cfDrv p.2) s (fun u : ℝ => η p.1 u.toNNReal) t c)

/-- The fibre-local cover in every setting gives the bundled fibre-kernel cover in every setting. -/
theorem kernelCoverOn_of_localCoverOn (H : GluedLocalCoverOn.{u}) : GluedKernelCoverOn.{u} := by
  intro t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P hP h η ζ hh hfl Ω₂ mΩ₂ P₂ hP₂ h₂ W₂ ζ₂ hcf hlaw k hK hk s hs
  exact hasFibreKernelCover_of_localCover
    (H t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)

open Sec5.Aux61Act Sec5.Aux61Cov in
/-- **The fibre-local cover gives the corrected dyadic fibre cover** consumed by
`Aux61Act.fwdNoEastCrosscutTgtQOn_of_dyCover_refWin`. -/
theorem dyCover_of_localCoverOn (H : GluedLocalCoverOn.{u}) :
    DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) RefWin :=
  dyCover_of_kernelCoverOn (kernelCoverOn_of_localCoverOn H)

end InteractingSLE.Sec5.Aux61UnionK
