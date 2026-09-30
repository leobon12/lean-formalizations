import QuantumZipper.Proofs.Section5.Prop16MeasReduce
import QuantumZipper.Proofs.LQG.IndepParams
import QuantumZipper.Statements.Prop16

/-!
# Proposition 1.6, node D4-MEAS (part 2): the raw coordinates of the zoomed canonical fields

For Proposition 1.6's pre-limit fields
`Y C (ω, t) = canonicalOn γ (zoomField γ C (ofFun 𝔥₀ + X ω) t) (zoomDomain D t)`
we prove that their raw coordinates `coords (Y C ·)` (the input `hY` of
`areaConvergesInLawOn_of_tvLocal_coords`) are a.e.-measurable, for any measure on `Ω × ℝ`,
as soon as the scale parameter `scaleParamOn` of the zoomed field is:

* `measurable_coords_zoomField`: `(ω, t) ↦ coords (zoomField γ C (ofFun 𝔥₀ + X ω) t)` is
  measurable (joint measurability of translation, `IndepParams.measurable_coords_translate`);
* `measurable_rescale_apply_joint`: `(x, a) ↦ rescale x Q a ν` is measurable for s-finite `ν`;
* `aemeasurable_coords_canonicalOn`: `coords (canonicalOn γ (x p) (U p))` is a.e.-measurable if
  `coords (x p)` and `scaleParamOn γ (x p) (U p)` are (factorization through `coords`, A4).

Own elementary arguments (measurability plumbing; AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Area

open TV Factorization

theorem integral_log_deriv_const_mul (ν : Measure ℂ) (a : ℝ) :
    ∫ z, Real.log ‖deriv (fun z : ℂ => (a : ℂ) * z) z‖ ∂ν = ν.real univ • Real.log ‖(a : ℂ)‖ := by
  have h : ∀ z : ℂ, deriv (fun z : ℂ => (a : ℂ) * z) z = (a : ℂ) := fun z => by
    simp
  simp only [h, integral_const]

/-- Joint measurability of rescaling, `(x, a) ↦ rescale x Q a ν`, for s-finite `ν`. -/
theorem measurable_rescale_apply_joint (Q : ℝ) (ν : Measure ℂ) [SFinite ν] :
    Measurable fun p : FieldSample × ℝ => rescale p.1 Q p.2 ν := by
  have e : (fun p : FieldSample × ℝ => rescale p.1 Q p.2 ν) = fun p =>
      (limUnder atTop fun k : ℕ => ∫ w, avgReg p.1 k ((p.2 : ℂ) * w) ∂ν) +
        Q * (ν.real univ * Real.log ‖(p.2 : ℂ)‖) := by
    funext p
    simp only [rescale, coordChange, evalReg, integral_log_deriv_const_mul, smul_eq_mul]
    congr 2
    funext k
    have hs : Measurable fun w : ℂ => avgReg p.1 k w :=
      (measurable_avgReg k).comp (f := fun w : ℂ => (p.1, w)) (by fun_prop)
    rw [integral_map (φ := fun z : ℂ => (p.2 : ℂ) * z)
      (by fun_prop : Measurable fun z : ℂ => (p.2 : ℂ) * z).aemeasurable hs.aestronglyMeasurable]
  rw [e]
  have hf : ∀ k : ℕ, StronglyMeasurable
      fun p : FieldSample × ℝ => ∫ w, avgReg p.1 k ((p.2 : ℂ) * w) ∂ν := fun k =>
    StronglyMeasurable.integral_prod_right'
      (f := fun q : (FieldSample × ℝ) × ℂ => avgReg q.1.1 k ((q.1.2 : ℂ) * q.2))
      ((measurable_avgReg k).comp (by fun_prop :
        Measurable fun q : (FieldSample × ℝ) × ℂ => (q.1.1, (q.1.2 : ℂ) * q.2))).stronglyMeasurable
  refine (StronglyMeasurable.limUnder hf).measurable.add (Measurable.const_mul ?_ Q)
  exact measurable_const.mul (Real.measurable_log.comp (by fun_prop :
    Measurable fun p : FieldSample × ℝ => ‖(p.2 : ℂ)‖))

theorem rescale_reconstruct_coords (x : FieldSample) (Q a : ℝ) :
    rescale (reconstruct (coords x)) Q a = rescale x Q a := by
  funext μ
  simp only [rescale, coordChange]
  rw [evalReg_congr (avgReg_reconstruct_coords x)]

theorem measurable_coords_rescale_reconstruct (Q : ℝ) :
    Measurable fun p : (ℕ → ℝ) × ℝ => coords (rescale (reconstruct p.1) Q p.2) :=
  measurable_pi_iff.2 fun i =>
    Measurable.comp (g := fun q : FieldSample × ℝ =>
        rescale q.1 Q q.2 (foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2)))
      (f := fun p : (ℕ → ℝ) × ℝ => (reconstruct p.1, p.2))
      (measurable_rescale_apply_joint Q _)
      ((measurable_reconstruct.comp measurable_fst).prodMk measurable_snd)

theorem scaleParamOn_recon (γ : ℝ) (x : FieldSample) (U : Set ℂ) :
    scaleParamOn γ (recon x) U = scaleParamOn γ x U := by
  simp only [scaleParamOn, qAreaMeasureOn_recon]

/-- The raw coordinates of `canonicalOn γ (x p) (U p)` are a.e.-measurable if those of `x p` and
the scale parameter are. -/
theorem aemeasurable_coords_canonicalOn (γ : ℝ) {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (x : α → FieldSample) (U : α → Set ℂ)
    (hx : AEMeasurable (fun p => coords (x p)) μ)
    (ha : AEMeasurable (fun p => scaleParamOn γ (x p) (U p)) μ) :
    AEMeasurable (fun p => coords (canonicalOn γ (x p) (U p))) μ := by
  have e : (fun p => coords (canonicalOn γ (x p) (U p))) =
      fun p => coords (rescale (reconstruct (coords (x p))) (Qc γ) (scaleParamOn γ (x p) (U p))) := by
    funext p
    unfold canonicalOn
    rw [rescale_reconstruct_coords]
  rw [e]
  exact Measurable.comp_aemeasurable
    (g := fun q : (ℕ → ℝ) × ℝ => coords (rescale (reconstruct q.1) (Qc γ) q.2))
    (f := fun p => (coords (x p), scaleParamOn γ (x p) (U p)))
    (measurable_coords_rescale_reconstruct (Qc γ)) (hx.prodMk ha)

/-- The shifted sample `ofFun 𝔥₀ + X ω` is measurable when all coordinates of `X` are. -/
theorem measurable_ofFun_add {Ω : Type*} [MeasurableSpace Ω] (h0 : ℂ → ℝ)
    {X : Ω → FieldSample} (hX : ∀ μ : Measure ℂ, Measurable fun ω => X ω μ) :
    Measurable fun ω => ofFun h0 + X ω :=
  measurable_pi_iff.2 fun μ => measurable_const.add (hX μ)

/-- The raw coordinates of the zoomed field `h(· + t) + C/γ` are jointly measurable in `(ω, t)`. -/
theorem measurable_coords_zoomField {Ω : Type*} [MeasurableSpace Ω] (γ C : ℝ) (h0 : ℂ → ℝ)
    {X : Ω → FieldSample} (hX : ∀ μ : Measure ℂ, Measurable fun ω => X ω μ) :
    Measurable fun p : Ω × ℝ => coords (zoomField γ C (ofFun h0 + X p.1) p.2) := by
  have hT : Measurable fun p : Ω × ℝ => coords (translate (ofFun h0 + X p.1) (p.2 : ℂ)) :=
    Measurable.comp (g := fun q : FieldSample × ℝ => coords (translate q.1 (q.2 : ℂ)))
      (f := fun p : Ω × ℝ => (ofFun h0 + X p.1, p.2))
      IndepParams.measurable_coords_translate
      (((measurable_ofFun_add h0 hX).comp measurable_fst).prodMk measurable_snd)
  refine measurable_pi_iff.2 fun i => ?_
  have e : (fun p : Ω × ℝ => coords (zoomField γ C (ofFun h0 + X p.1) p.2) i) = fun p =>
      coords (translate (ofFun h0 + X p.1) (p.2 : ℂ)) i +
        C / γ * ((foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2)) univ).toReal := by
    funext p
    rfl
  rw [e]
  exact ((measurable_pi_apply i).comp hT).add measurable_const

/-- **`hY` for Proposition 1.6** (coordinate form), given a.e.-measurability of the scale
parameter of the zoomed field. -/
theorem aemeasurable_coords_prop16Y {Ω : Type*} [MeasurableSpace Ω] (γ C : ℝ) (h0 : ℂ → ℝ)
    (D : Set ℂ) {X : Ω → FieldSample} (hX : ∀ μ : Measure ℂ, Measurable fun ω => X ω μ)
    {μ : Measure (Ω × ℝ)}
    (ha : AEMeasurable (fun p : Ω × ℝ =>
      scaleParamOn γ (zoomField γ C (ofFun h0 + X p.1) p.2) (zoomDomain D p.2)) μ) :
    AEMeasurable (fun p : Ω × ℝ =>
      coords (canonicalOn γ (zoomField γ C (ofFun h0 + X p.1) p.2) (zoomDomain D p.2))) μ :=
  aemeasurable_coords_canonicalOn γ _ _
    (measurable_coords_zoomField γ C h0 hX).aemeasurable ha

end Prop16Area

end QuantumZipper
