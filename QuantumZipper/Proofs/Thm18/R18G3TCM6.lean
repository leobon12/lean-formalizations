import QuantumZipper.Proofs.Thm18.R18G3TCM5
import QuantumZipper.Proofs.Thm18.R18G3TFidB

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 (R-a), part 6: the real Palm formula and the tail of the tilt

`g3pPalmLaw_cut_real`: `P_B(S_B ∩ G) = κ ∫_{S_A ∩ G'} D dP_A`, `κ = Z_A / Z_B`,
`D = cmTilt X₀ (g3wCut γ η)` (Berestycki–Powell, arXiv:2004.04720, Lemma 3.12, via
`lintegral_B_eq_tilt`); `D` is `P_A`-integrable with `E_A D = Z_B / Z_A`; the truncation tail
`E_A (D − min(D, K)) → 0` (dominated convergence). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal ComplexConjugate

namespace QuantumZipper
namespace R18

open Thm18Asm

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

section Palm

variable (γ : ℝ) (i : G3Idx)

theorem lintegral_g3PalmLaw_eq (hZ : 0 < g3Z γ i ∧ g3Z γ i < ⊤) {f : Ω₀ × ℝ → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ p, f p ∂(g3PalmLaw γ i) =
      (g3Z γ i)⁻¹ * ∫⁻ p, g3W0 γ i p * f p ∂(gffBase.P.prod L₀) := by
  have hWm : Measurable fun p => (g3W γ i p : ℝ≥0∞) :=
    ((measurable_g3W γ i).mono (sig_le_g3 i _ _) le_rfl).coe_nnreal_ennreal
  rw [g3PalmLaw, lintegral_withDensity_eq_lintegral_mul _ hWm hf,
    ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hZ.1.ne')]
  refine lintegral_congr fun p => ?_
  simp only [Pi.mul_apply, g3W, if_pos hZ]
  rw [ENNReal.coe_toNNReal (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hZ.1.ne')
    (g3W0_ne_top γ i p)), mul_assoc]

theorem measurable_cmTilt_fst (φ : ℂ → ℝ) :
    Measurable fun p : Ω₀ × ℝ => cmTilt X₀ φ p.1 :=
  (Real.measurable_exp.comp (((gffBase.gff.measurable_coord _).sub
    (gffBase.gff.measurable_coord _)).sub_const _)).comp measurable_fst

/-- `∫⁻ D dP_A = Z_B / Z_A`. -/
theorem lintegral_cmTilt_g3PalmLaw (hZA : 0 < g3Z γ i ∧ g3Z γ i < ⊤) :
    ∫⁻ p, ENNReal.ofReal (cmTilt X₀ (g3wCut γ i.η) p.1) ∂(g3PalmLaw γ i) =
      (g3Z γ i)⁻¹ * g3pZ γ (g3wCut γ i.η) i := by
  rw [lintegral_g3PalmLaw_eq γ i hZA
    (f := fun p => ENNReal.ofReal (cmTilt X₀ (g3wCut γ i.η) p.1))
    (ENNReal.measurable_ofReal.comp (measurable_cmTilt_fst _))]
  congr 1
  have h := lintegral_g3pField_eq_tilt γ (contDiff_g3wCut γ i.η i.hη)
    (hasCompactSupport_g3wCut γ i.η) (g3wCut_conj γ i.η) (g3wCut_unit γ i.η)
    (Φ := sW0 γ i) (measurable_sW0 γ i) (fun x x' s hxx => sW0_fc (fun c ρ hρ =>
      hxx _ (D3Plus.isAdmissibleH_foldedCircle' c hρ) measure_univ) γ i s)
  exact h.symm

theorem integrable_cmTilt_g3PalmLaw (hZA : 0 < g3Z γ i ∧ g3Z γ i < ⊤)
    (hZB : 0 < g3pZ γ (g3wCut γ i.η) i ∧ g3pZ γ (g3wCut γ i.η) i < ⊤) :
    Integrable (fun p : Ω₀ × ℝ => cmTilt X₀ (g3wCut γ i.η) p.1) (g3PalmLaw γ i) := by
  refine ⟨(measurable_cmTilt_fst _).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have e : ∀ p : Ω₀ × ℝ, ‖cmTilt X₀ (g3wCut γ i.η) p.1‖ₑ =
      ENNReal.ofReal (cmTilt X₀ (g3wCut γ i.η) p.1) := fun p =>
    Real.enorm_eq_ofReal (cmTilt_pos _ _).le
  simp only [e]
  rw [lintegral_cmTilt_g3PalmLaw γ i hZA]
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 hZA.1) hZB.2

/-- **The real Palm formula for the cut-off scheme.** -/
theorem g3pPalmLaw_cut_real (hZA : 0 < g3Z γ i ∧ g3Z γ i < ⊤)
    (hZB : 0 < g3pZ γ (g3wCut γ i.η) i ∧ g3pZ γ (g3wCut γ i.η) i < ⊤) {G : Set (Ω₀ × ℝ)}
    (hG : MeasurableSet[outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂] G) :
    ∃ G' : Set (Ω₀ × ℝ), MeasurableSet[outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂] G' ∧
      ∀ S : Set (FieldSample × ℝ), MeasurableSet S → IsLocS S →
        (g3pPalmLaw γ (g3wCut γ i.η) i).real
            ({p : Ω₀ × ℝ | (g3pField γ (g3wCut γ i.η) p.1, p.2) ∈ S} ∩ G) =
          ((g3pZ γ (g3wCut γ i.η) i)⁻¹ * g3Z γ i).toReal *
            ∫ p, ({p : Ω₀ × ℝ | (normField γ X₀ p.1, p.2) ∈ S} ∩ G').indicator
              (fun p => cmTilt X₀ (g3wCut γ i.η) p.1) p ∂(g3PalmLaw γ i) := by
  obtain ⟨G', hG', hT⟩ := lintegral_B_eq_tilt γ i hG
  refine ⟨G', hG', fun S hS hSl => ?_⟩
  have hSB : MeasurableSet {p : Ω₀ × ℝ | (g3pField γ (g3wCut γ i.η) p.1, p.2) ∈ S} :=
    (((measurable_g3pField γ _).comp measurable_fst).prodMk measurable_snd) hS
  have hSA : MeasurableSet {p : Ω₀ × ℝ | (normField γ X₀ p.1, p.2) ∈ S} :=
    (((measurable_normField_g3 γ).comp measurable_fst).prodMk measurable_snd) hS
  have hGm : MeasurableSet G := outsideSigmaPalm_le_g3 i _ hG
  have hG'm : MeasurableSet G' := outsideSigmaPalm_le_g3 i _ hG'
  set E' := {p : Ω₀ × ℝ | (normField γ X₀ p.1, p.2) ∈ S} ∩ G' with hE'
  have hE'm : MeasurableSet E' := hSA.inter hG'm
  set L := ∫⁻ p, E'.indicator (fun p => g3W0 γ i p *
    ENNReal.ofReal (cmTilt X₀ (g3wCut γ i.η) p.1)) p ∂(gffBase.P.prod L₀) with hL
  have hint := (integrable_cmTilt_g3PalmLaw γ i hZA hZB).indicator hE'm
  have hnn : 0 ≤ᵐ[g3PalmLaw γ i] E'.indicator (fun p => cmTilt X₀ (g3wCut γ i.η) p.1) :=
    ae_of_all _ fun p => indicator_nonneg (fun p _ => (cmTilt_pos _ _).le) p
  have hof := ofReal_integral_eq_lintegral_ofReal hint hnn
  have hlin : ∫⁻ p, ENNReal.ofReal (E'.indicator (fun p => cmTilt X₀ (g3wCut γ i.η) p.1) p)
      ∂(g3PalmLaw γ i) = (g3Z γ i)⁻¹ * L := by
    rw [lintegral_g3PalmLaw_eq γ i hZA
      (f := fun p => ENNReal.ofReal (E'.indicator (fun p => cmTilt X₀ (g3wCut γ i.η) p.1) p))
      (ENNReal.measurable_ofReal.comp ((measurable_cmTilt_fst _).indicator hE'm))]
    congr 1
    refine lintegral_congr fun p => ?_
    by_cases hp : p ∈ E' <;> simp [indicator, hp]
  rw [hlin] at hof
  have hI : ∫ p, E'.indicator (fun p => cmTilt X₀ (g3wCut γ i.η) p.1) p ∂(g3PalmLaw γ i) =
      ((g3Z γ i)⁻¹ * L).toReal := by
    rw [← hof, ENNReal.toReal_ofReal (integral_nonneg fun p =>
      indicator_nonneg (fun p _ => (cmTilt_pos _ _).le) p)]
  rw [hI, measureReal_def, g3pPalmLaw_apply hZB (hSB.inter hGm), hT S hS hSl, ← hL,
    ← ENNReal.toReal_mul]
  congr 1
  rw [mul_assoc, ← mul_assoc (g3Z γ i), ENNReal.mul_inv_cancel hZA.1.ne' hZA.2.ne, one_mul]

/-- **The tail of the truncated tilt vanishes.** -/
theorem tendsto_tail_cmTilt (hZA : 0 < g3Z γ i ∧ g3Z γ i < ⊤)
    (hZB : 0 < g3pZ γ (g3wCut γ i.η) i ∧ g3pZ γ (g3wCut γ i.η) i < ⊤) :
    Tendsto (fun K : ℝ => ∫ p, (cmTilt X₀ (g3wCut γ i.η) p.1 -
      min (cmTilt X₀ (g3wCut γ i.η) p.1) K) ∂(g3PalmLaw γ i)) atTop (𝓝 0) := by
  set D := fun p : Ω₀ × ℝ => cmTilt X₀ (g3wCut γ i.η) p.1 with hD
  have hDi : Integrable D (g3PalmLaw γ i) := integrable_cmTilt_g3PalmLaw γ i hZA hZB
  have hDm : Measurable D := measurable_cmTilt_fst _
  have h := tendsto_integral_filter_of_dominated_convergence (μ := g3PalmLaw γ i)
    (l := (atTop : Filter ℝ)) (F := fun K p => D p - min (D p) K) (f := fun _ => (0 : ℝ)) D
    (Eventually.of_forall fun K => (hDm.sub (hDm.min measurable_const)).aestronglyMeasurable)
    ((eventually_ge_atTop 0).mono fun K hK => ae_of_all _ fun p => by
      have h0 : 0 < D p := cmTilt_pos _ _
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 (min_le_left _ _))]
      have : 0 ≤ min (D p) K := le_min h0.le hK
      linarith)
    hDi (ae_of_all _ fun p => tendsto_const_nhds.congr'
      ((eventually_ge_atTop (D p)).mono fun K hK => by simp [min_eq_left hK]))
  simpa using h

end Palm

end R18
end QuantumZipper
