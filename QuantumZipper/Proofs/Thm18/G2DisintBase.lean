import QuantumZipper.Proofs.Thm18.G2ConstBridge
import QuantumZipper.Proofs.Thm18.G2ClipNodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 disintegration, basic layer: the resampled field and the transfer to `law(Y) ⊗ N`

Sheffield (arXiv:1012.4797, proof of Prop. 5.5, p. 66) writes `h = α φ + h₀` with `α` Gaussian and
independent of `h₀` (`G2BumpDecompStmt`, proved as `g2BumpDecompStmt_holds`). This file sets up
the bookkeeping that turns that decomposition into a product disintegration:

* `g2Y φ α ω : AdmIdx → ℝ` is the bump-free normalized field `h₀` (`μ ↦ normX X ω μ − α ω ∫ φ dμ`);
* `g2Field γ φ y a : FieldSample` is `𝔥₀ + y + a φ` (junk `0` part off admissible measures);
  it is jointly measurable in `(y, a)` (`measurable_g2Field`);
* at `(y, a) = (g2Y ω, α ω)` it has the same regularized averages as `normField γ X ω`
  (`avgReg_g2Field`), hence the same boundary measure (`g3Hν_eq_g2Field`), measurable boundary
  measure (`bdryM_congr_avgReg`) and zoom law (`zoomLaw_eq_g2Field`);
* `lintegral_indep_transfer`: for `W ⊥ α`, `E K(W, α) = E ∫ K(W, a) N(da)`, `N = law α`;
* `outsideSigmaPalm_eq_comap` / `exists_outside_factor`: an event of the conditioning σ-algebra
  is a measurable function of the outside balanced differences and the length.

Own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

open Classical in
/-- `𝔥₀ + y + a φ` as a field sample (the part `y` is read on admissible measures only). -/
def g2Field (γ : ℝ) (φ : ℂ → ℝ) (y : AdmIdx → ℝ) (a : ℝ) : FieldSample := fun μ =>
  ofFun (h0rev (γ ^ 2)) μ + (if h : IsAdmissibleH μ then y ⟨μ, h⟩ else 0) + a * ∫ z, φ z ∂μ

theorem measurable_g2Field (γ : ℝ) (φ : ℂ → ℝ) :
    Measurable fun p : (AdmIdx → ℝ) × ℝ => g2Field γ φ p.1 p.2 := by
  refine measurable_pi_iff.2 fun μ => ?_
  classical
  by_cases h : IsAdmissibleH μ
  · simp only [g2Field, dif_pos h]
    exact (measurable_const.add ((measurable_pi_apply _).comp measurable_fst)).add
      (measurable_snd.mul_const _)
  · simp only [g2Field, dif_neg h]
    exact measurable_const.add (measurable_snd.mul_const _)

/-- The bump-free normalized field `h₀ = normX X − α φ`. -/
def g2Y (φ : ℂ → ℝ) (α : Ω₀ → ℝ) (ω : Ω₀) : AdmIdx → ℝ := fun μ =>
  normX gffBase.X ω μ.1 - α ω * ∫ z, φ z ∂μ.1

theorem g2Field_Y_prob (γ : ℝ) (φ : ℂ → ℝ) (α : Ω₀ → ℝ) (ω : Ω₀) (μ : Measure ℂ)
    [IsProbabilityMeasure μ] (hμ : IsAdmissibleH μ) :
    g2Field γ φ (g2Y φ α ω) (α ω) μ = normField γ gffBase.X ω μ := by
  rw [← normField_normX_of_prob γ gffBase.X ω μ]
  simp only [g2Field, dif_pos hμ, g2Y, normField, normX_refS, sub_zero]
  ring

theorem avgReg_g2Field (γ : ℝ) (φ : ℂ → ℝ) (α : Ω₀ → ℝ) (ω : Ω₀) :
    avgReg (g2Field γ φ (g2Y φ α ω) (α ω)) = avgReg (normField γ gffBase.X ω) := by
  funext k z
  unfold avgReg
  congr 1
  funext n
  exact g2Field_Y_prob γ φ α ω _ (D3Plus.isAdmissibleH_foldedCircle' _ (radius_pos k))

theorem zoomLaw_eq_g2Field (γ : ℝ) (φ : ℂ → ℝ) (α : Ω₀ → ℝ) (ω : Ω₀) (C x : ℝ) :
    zoomLaw γ C (normField γ gffBase.X ω) x =
      zoomLaw γ C (g2Field γ φ (g2Y φ α ω) (α ω)) x := by
  unfold zoomLaw zoomField
  rw [Factorization.translate_congr (avgReg_g2Field γ φ α ω)]

theorem bdryM_congr_avgReg {x x' : FieldSample} (h : avgReg x = avgReg x') (γ : ℝ) :
    bdryM γ x = bdryM γ x' := by
  unfold bdryM E1.M4.BCert
  rw [Factorization.bdryApprox_congr h, Factorization.qBoundaryMeasure_congr h]

/-- `h₀` is independent of the bump coefficient. -/
theorem indepFun_g2Y {φ : ℂ → ℝ} {α : Ω₀ → ℝ}
    (h : IndepFun α (fun ω (μ : AdmIdx) =>
      gffBase.X ω μ.1 - (μ.1 univ).toReal * gffBase.X ω refS - α ω * ∫ z, φ z ∂μ.1) gffBase.P) :
    IndepFun (g2Y φ α) α gffBase.P := h.symm

/-! ## Transfer to the product law -/

/-- **Independence as a product disintegration**: `E K(W, α) = E ∫ K(W, a) (law α)(da)`. -/
theorem lintegral_indep_transfer {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] {W : Ω → E} {α : Ω → ℝ} (hW : Measurable W)
    (hα : Measurable α) (hind : IndepFun W α P) {K : E × ℝ → ℝ≥0∞} (hK : Measurable K) :
    ∫⁻ ω, K (W ω, α ω) ∂P = ∫⁻ ω, ∫⁻ a, K (W ω, a) ∂(P.map α) ∂P := by
  have h := (indepFun_iff_map_prod_eq_prod_map_map hW.aemeasurable hα.aemeasurable).1 hind
  rw [← lintegral_map hK (hW.prodMk hα), h, lintegral_prod _ hK.aemeasurable,
    lintegral_map hK.lintegral_prod_right' hW]

/-! ## Events of the conditioning σ-algebra -/

/-- The outside balanced differences. -/
def g2OutV (X : Ω₀ → FieldSample) (t₁ r₁ t₂ r₂ : ℝ) (ω : Ω₀) : OutIdx2 t₁ r₁ t₂ r₂ → ℝ :=
  fun p => X ω p.1.1 - X ω p.1.2

theorem g2d_outsideSigma2_eq_comap (X : Ω₀ → FieldSample) (t₁ r₁ t₂ r₂ : ℝ) :
    outsideSigma2 X t₁ r₁ t₂ r₂ = MeasurableSpace.comap (g2OutV X t₁ r₁ t₂ r₂) inferInstance := by
  rw [show (inferInstance : MeasurableSpace (OutIdx2 t₁ r₁ t₂ r₂ → ℝ)) = MeasurableSpace.pi from rfl,
    MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  simp_rw [MeasurableSpace.comap_comp]
  rfl

theorem outsideSigmaPalm_eq_comap (X : Ω₀ → FieldSample) (t₁ r₁ t₂ r₂ : ℝ) :
    outsideSigmaPalm ℝ X t₁ r₁ t₂ r₂ =
      MeasurableSpace.comap (fun q : Ω₀ × ℝ => (g2OutV X t₁ r₁ t₂ r₂ q.1, q.2)) inferInstance := by
  rw [outsideSigmaPalm, g2d_outsideSigma2_eq_comap,
    show (inferInstance : MeasurableSpace ((OutIdx2 t₁ r₁ t₂ r₂ → ℝ) × ℝ)) =
      MeasurableSpace.comap Prod.fst inferInstance ⊔ MeasurableSpace.comap Prod.snd inferInstance
      from rfl, MeasurableSpace.comap_sup]
  simp_rw [MeasurableSpace.comap_comp]
  rfl

theorem exists_outside_factor {X : Ω₀ → FieldSample} {t₁ r₁ t₂ r₂ : ℝ} {G : Set (Ω₀ × ℝ)}
    (hG : MeasurableSet[outsideSigmaPalm ℝ X t₁ r₁ t₂ r₂] G) :
    ∃ G' : Set ((OutIdx2 t₁ r₁ t₂ r₂ → ℝ) × ℝ), MeasurableSet G' ∧
      G = (fun q : Ω₀ × ℝ => (g2OutV X t₁ r₁ t₂ r₂ q.1, q.2)) ⁻¹' G' := by
  rw [outsideSigmaPalm_eq_comap] at hG
  obtain ⟨G', hG', e⟩ := hG
  exact ⟨G', hG', e.symm⟩

/-- The outside differences read from `h₀` (`Ψ`). -/
def g2Psi (t₁ r₁ t₂ r₂ : ℝ) (y : AdmIdx → ℝ) : OutIdx2 t₁ r₁ t₂ r₂ → ℝ :=
  fun p => y ⟨p.1.1, p.2.1⟩ - y ⟨p.1.2, p.2.2.1⟩

theorem measurable_g2Psi (t₁ r₁ t₂ r₂ : ℝ) : Measurable (g2Psi t₁ r₁ t₂ r₂) :=
  measurable_pi_iff.2 fun _ => (measurable_pi_apply _).sub (measurable_pi_apply _)

/-- **The outside differences do not see the bump** (`φ = 0` on the two discs' complement
support condition: `tsupport φ ⊆ ball t₁ r₁`). -/
theorem g2OutV_eq_Psi {φ : ℂ → ℝ} {t₁ r₁ t₂ r₂ : ℝ}
    (hφ : ∀ z, z ∉ Metric.ball (t₁ : ℂ) r₁ → φ z = 0) (α : Ω₀ → ℝ) (ω : Ω₀) :
    g2OutV gffBase.X t₁ r₁ t₂ r₂ ω = g2Psi t₁ r₁ t₂ r₂ (g2Y φ α ω) := by
  funext p
  have hz : ∀ μ : Measure ℂ, μ (Metric.ball (t₁ : ℂ) r₁ ∪ Metric.ball (t₂ : ℂ) r₂) = 0 →
      ∫ z, φ z ∂μ = 0 := by
    intro μ hμ
    refine integral_eq_zero_of_ae ?_
    have h1 : μ (Metric.ball (t₁ : ℂ) r₁) = 0 := measure_mono_null subset_union_left hμ
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun z hz => ?_) h1
    by_contra hb
    exact hz (hφ z hb)
  simp only [g2OutV, g2Psi, g2Y, hz _ p.2.2.2.2.1, hz _ p.2.2.2.2.2, mul_zero, sub_zero]
  exact (normX_sub_of_mass_eq gffBase.X ω p.2.2.2.1).symm

end Thm18Asm
end QuantumZipper
