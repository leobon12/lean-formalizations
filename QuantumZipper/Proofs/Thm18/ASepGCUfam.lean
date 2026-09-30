import QuantumZipper.Proofs.Thm18.ASepGCFwd
import QuantumZipper.Proofs.Thm18.ASepGCEval

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP-GC, part 5: the unzipped field as a Borel family of the codes

* `Ufam γ (v, (c, τ))`: the coordinate change of the realizable field `yC v` by the code
  unzipping map `Fz = fC ∘ selC` (with the code log-derivative `LDz`).
* **`unzippedField_eq_Ufam`**: for continuous `x`, `τ ≥ 0` and every measure `μ` carried by `ℍ`,
  `unzippedField γ (y, pathDrive γ² x) τ μ = Ufam γ (coordsFull y, (codeP x, τ)) μ`.
* `measurable_Ufam_map`, `measurable_avgReg_Ufam`, `measurable_evalReg_Ufam`,
  `measurable_rescaleUfam_map`, `measurable_evalReg_rescaleUfam`: the evaluations of `Ufam` and of
  its rescalings along parametrized pushforwards are measurable in the parameters.

Own bookkeeping (Carathéodory measurability of the code maps from `G4CMeas4Fld`, generic
parametric-integral lemmas of `ASepGCEval`).
-/

noncomputable section

open MeasureTheory Set Function Filter
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace ASep
namespace GC

open Thm18Asm Thm18Asm.G4Core

/-- The code unzipping map on all of `ℂ`. -/
@[irreducible] def Fz (κ : ℝ) (q : (ℕ → ℝ) × ℝ) (z : ℂ) : ℂ := fC κ q (selC z)

theorem Fz_def (κ : ℝ) (q : (ℕ → ℝ) × ℝ) (z : ℂ) : Fz κ q z = fC κ q (selC z) := by
  unfold Fz; rfl

/-- The code log-derivative. -/
@[irreducible] def LDz (κ : ℝ) (q : (ℕ → ℝ) × ℝ) (z : ℂ) : ℝ := LD (kcode κ q.1) q.2 z

theorem LDz_def (κ : ℝ) (q : (ℕ → ℝ) × ℝ) (z : ℂ) : LDz κ q z = LD (kcode κ q.1) q.2 z := by
  unfold LDz; rfl

theorem measurable_Fz (κ : ℝ) : Measurable fun s : ((ℕ → ℝ) × ℝ) × ℂ => Fz κ s.1 s.2 := by
  simp only [Fz_def]
  exact measurable_fC κ

theorem measurable_LDz (κ : ℝ) : Measurable fun s : ((ℕ → ℝ) × ℝ) × ℂ => LDz κ s.1 s.2 := by
  have h1 : Measurable fun s : ((ℕ → ℝ) × ℝ) × ℂ => ((kcode κ s.1.1, s.1.2), s.2) :=
    (((measurable_kcode κ).comp measurable_fst.fst).prodMk measurable_fst.snd).prodMk
      measurable_snd
  simp only [LDz_def]
  exact Measurable.comp (g := fun p : ((ℕ → ℝ) × ℝ) × ℂ => LD p.1.1 p.1.2 p.2)
    (f := fun s : ((ℕ → ℝ) × ℝ) × ℂ => ((kcode κ s.1.1, s.1.2), s.2)) measurable_LD h1

/-- The unzipped field read from (circle coordinates, path code, time). -/
@[irreducible] def Ufam (γ : ℝ) (p : (ℕ → ℝ) × ((ℕ → ℝ) × ℝ)) : FieldSample := fun μ =>
  evalReg (yC p.1) (μ.map (Fz (γ ^ 2) p.2)) + Qc γ * ∫ z, LDz (γ ^ 2) p.2 z ∂μ

theorem Ufam_def (γ : ℝ) (p : (ℕ → ℝ) × ((ℕ → ℝ) × ℝ)) (μ : Measure ℂ) :
    Ufam γ p μ = evalReg (yC p.1) (μ.map (Fz (γ ^ 2) p.2)) + Qc γ * ∫ z, LDz (γ ^ 2) p.2 z ∂μ := by
  unfold Ufam; rfl

theorem isOpen_H' : IsOpen H := isOpen_lt continuous_const Complex.continuous_im

/-- **The unzipped field is the code family on measures carried by `ℍ`.** -/
theorem unzippedField_eq_Ufam (γ : ℝ) {x : ℝ≥0 → ℝ} (hx : Continuous x) (y : FieldSample)
    {τ : ℝ} (hτ : 0 ≤ τ) {μ : Measure ℂ} (hμ : μ Hᶜ = 0) :
    unzippedField γ (y, pathDrive (γ ^ 2) x) τ μ =
      Ufam γ (CoordsFull.coordsFull y, (codeP x, τ)) μ := by
  have hav : avgReg y = avgReg (yC (CoordsFull.coordsFull y)) :=
    CoordsFull.avgReg_congr_full (coordsFull_yC (mem_C2 y)).symm
  have hEq : EqOn (fwdMapInv (pathDrive (γ ^ 2) x) τ) (Fz (γ ^ 2) (codeP x, τ)) H :=
    fun w hw => by rw [fwdMapInv_pathDrive_eq _ hx hτ hw, Fz_def, selC_of_mem hw]
  unfold unzippedField
  rw [Factorization.coordChange_congr hav,
    UnzipInvariance.coordChange_congr_of_eqOn hEq hμ]
  have hae : ∀ᵐ z ∂μ, z ∈ H := ae_iff.2 hμ
  rw [Ufam_def]
  unfold coordChange
  congr 1
  congr 1
  refine integral_congr_ae (hae.mono fun z hz => ?_)
  have hev : Fz (γ ^ 2) (codeP x, τ) =ᶠ[𝓝 z] fun w =>
      psiR (kcode (γ ^ 2) (codeP x)) τ w + ((Real.sqrt (γ ^ 2) * codeP x m0 : ℝ) : ℂ) := by
    filter_upwards [isOpen_H'.mem_nhds hz] with w hw
    simp only [Fz_def, fC, selC_of_mem hw]
  rw [LDz_def]
  show Real.log ‖deriv (Fz (γ ^ 2) (codeP x, τ)) z‖ = LD (kcode (γ ^ 2) (codeP x)) τ z
  rw [hev.deriv_eq, deriv_add_const, LD, selC_of_mem hz]

variable {P : Type*} [MeasurableSpace P]

/-- Parametric integrals against a fixed measure. -/
theorem measurable_integral_family (σ : Measure ℂ) [SFinite σ] (g : P → ℂ → ℝ)
    (hg : Measurable fun q : P × ℂ => g q.1 q.2) : Measurable fun p => ∫ z, g p z ∂σ :=
  (StronglyMeasurable.integral_prod_right' (f := fun q : P × ℂ => g q.1 q.2)
    hg.stronglyMeasurable).measurable

theorem Ufam_map_eq (γ : ℝ) (q : (ℕ → ℝ) × ((ℕ → ℝ) × ℝ)) {φ : ℂ → ℂ} (hφ : Measurable φ)
    (σ : Measure ℂ) :
    Ufam γ q (σ.map φ) = evalReg (yC q.1) (σ.map (Fz (γ ^ 2) q.2 ∘ φ)) +
      Qc γ * ∫ z, LDz (γ ^ 2) q.2 z ∂(σ.map φ) := by
  have hF : Measurable (Fz (γ ^ 2) q.2) :=
    Measurable.comp (g := fun s : ((ℕ → ℝ) × ℝ) × ℂ => Fz (γ ^ 2) s.1 s.2)
      (f := fun z : ℂ => (q.2, z)) (measurable_Fz _) (measurable_const.prodMk measurable_id)
  rw [Ufam_def, Measure.map_map hF hφ]

theorem measurable_Ufam_map (γ : ℝ) (g : P → (ℕ → ℝ) × ((ℕ → ℝ) × ℝ)) (hg : Measurable g)
    (σ : Measure ℂ) [SFinite σ] (φ : P → ℂ → ℂ) (hφ : Measurable fun q : P × ℂ => φ q.1 q.2) :
    Measurable fun p => Ufam γ (g p) (σ.map (φ p)) := by
  have hφp : ∀ p, Measurable (φ p) := fun p =>
    Measurable.comp (g := fun q : P × ℂ => φ q.1 q.2) (f := fun z : ℂ => (p, z)) hφ
      (measurable_const.prodMk measurable_id)
  have e : (fun p => Ufam γ (g p) (σ.map (φ p))) = fun p =>
      evalReg (yC (g p).1) (σ.map (Fz (γ ^ 2) (g p).2 ∘ φ p)) +
        Qc γ * ∫ z, LDz (γ ^ 2) (g p).2 z ∂(σ.map (φ p)) :=
    funext fun p => Ufam_map_eq γ (g p) (hφp p) σ
  rw [e]
  have hY : ∀ k : ℕ, Measurable fun q : P × ℂ => avgReg (yC (g q.1).1) k q.2 := fun k =>
    Measurable.comp (g := fun q : (ℕ → ℝ) × ℂ => avgReg (yC q.1) k q.2)
      (f := fun q : P × ℂ => ((g q.1).1, q.2)) (measurable_avgReg_yC k)
      ((hg.fst.comp measurable_fst).prodMk measurable_snd)
  have hφ' : Measurable fun q : P × ℂ => (Fz (γ ^ 2) (g q.1).2 ∘ φ q.1) q.2 :=
    Measurable.comp (g := fun s : ((ℕ → ℝ) × ℝ) × ℂ => Fz (γ ^ 2) s.1 s.2)
      (f := fun q : P × ℂ => ((g q.1).2, φ q.1 q.2)) (measurable_Fz _)
      ((hg.snd.comp measurable_fst).prodMk hφ)
  have h1 : Measurable fun p => evalReg (yC (g p).1) (σ.map (Fz (γ ^ 2) (g p).2 ∘ φ p)) :=
    measurable_evalReg_map_family (P := P) (fun p => yC (g p).1) hY σ
      (fun p => Fz (γ ^ 2) (g p).2 ∘ φ p) hφ'
  have hL : Measurable fun q : P × ℂ => LDz (γ ^ 2) (g q.1).2 q.2 :=
    Measurable.comp (g := fun s : ((ℕ → ℝ) × ℝ) × ℂ => LDz (γ ^ 2) s.1 s.2)
      (f := fun q : P × ℂ => ((g q.1).2, q.2)) (measurable_LDz _)
      ((hg.snd.comp measurable_fst).prodMk measurable_snd)
  have h2 : Measurable fun p => ∫ z, LDz (γ ^ 2) (g p).2 z ∂(σ.map (φ p)) :=
    measurable_integral_map_family (P := P) σ (fun p z => LDz (γ ^ 2) (g p).2 z) hL φ hφ
  exact h1.add (measurable_const.mul h2)

theorem measurable_avgReg_Ufam (γ : ℝ) (g : P → (ℕ → ℝ) × ((ℕ → ℝ) × ℝ)) (hg : Measurable g)
    (k : ℕ) : Measurable fun q : P × ℂ => avgReg (Ufam γ (g q.1)) k q.2 := by
  refine measurable_avgReg_family (fun p => Ufam γ (g p)) (fun d k' => ?_) k
  have h := measurable_Ufam_map γ g hg (foldedCircle d (radius k')) (fun _ z => z) measurable_snd
  simpa only [Measure.map_id'] using h

theorem measurable_evalReg_Ufam (γ : ℝ) (g : P → (ℕ → ℝ) × ((ℕ → ℝ) × ℝ)) (hg : Measurable g)
    (σ : Measure ℂ) [SFinite σ] (φ : P → ℂ → ℂ) (hφ : Measurable fun q : P × ℂ => φ q.1 q.2) :
    Measurable fun p => evalReg (Ufam γ (g p)) (σ.map (φ p)) :=
  measurable_evalReg_map_family _ (measurable_avgReg_Ufam γ g hg) σ φ hφ

theorem deriv_const_mul_id (a : ℝ) (z : ℂ) : deriv (fun w : ℂ => (a : ℂ) * w) z = a := by
  simp

theorem measurable_rescaleUfam_map (γ : ℝ) (g : P → (ℕ → ℝ) × ((ℕ → ℝ) × ℝ))
    (hg : Measurable g) (ga : P → ℝ) (hga : Measurable ga) (σ : Measure ℂ) [SFinite σ]
    (φ : P → ℂ → ℂ) (hφ : Measurable fun q : P × ℂ => φ q.1 q.2) :
    Measurable fun p => rescale (Ufam γ (g p)) (Qc γ) (ga p) (σ.map (φ p)) := by
  have hφp : ∀ p, Measurable (φ p) := fun p =>
    hφ.comp (f := fun z : ℂ => (p, z)) (measurable_const.prodMk measurable_id)
  have e : (fun p => rescale (Ufam γ (g p)) (Qc γ) (ga p) (σ.map (φ p))) = fun p =>
      evalReg (Ufam γ (g p)) (σ.map fun w => (ga p : ℂ) * φ p w) +
        Qc γ * ∫ _z, Real.log ‖((ga p : ℝ) : ℂ)‖ ∂(σ.map (φ p)) := by
    funext p
    simp only [rescale, coordChange, deriv_const_mul_id]
    rw [Measure.map_map (g := fun z : ℂ => (ga p : ℂ) * z) (by fun_prop) (hφp p)]
    rfl
  rw [e]
  refine Measurable.add ?_ (measurable_const.mul ?_)
  · exact measurable_evalReg_Ufam γ g hg σ _
      ((Complex.measurable_ofReal.comp (hga.comp measurable_fst)).mul hφ)
  · exact measurable_integral_map_family σ (fun p _ => Real.log ‖((ga p : ℝ) : ℂ)‖)
      (((Complex.measurable_ofReal.comp (hga.comp measurable_fst)).norm).log) φ hφ

theorem measurable_evalReg_rescaleUfam (γ : ℝ) (g : P → (ℕ → ℝ) × ((ℕ → ℝ) × ℝ))
    (hg : Measurable g) (ga : P → ℝ) (hga : Measurable ga) (σ : Measure ℂ) [SFinite σ]
    (φ : P → ℂ → ℂ) (hφ : Measurable fun q : P × ℂ => φ q.1 q.2) :
    Measurable fun p => evalReg (rescale (Ufam γ (g p)) (Qc γ) (ga p)) (σ.map (φ p)) := by
  refine measurable_evalReg_map_family _ (fun k => ?_) σ φ hφ
  refine measurable_avgReg_family (fun p => rescale (Ufam γ (g p)) (Qc γ) (ga p))
    (fun d k' => ?_) k
  have h := measurable_rescaleUfam_map γ g hg ga hga (foldedCircle d (radius k')) (fun _ z => z)
    measurable_snd
  simpa only [Measure.map_id'] using h

end GC
end ASep
end QuantumZipper
