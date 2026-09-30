import QuantumZipper.Proofs.Thm18.G3PlX
import QuantumZipper.Proofs.Thm18.G3FidProxy
import QuantumZipper.Proofs.Thm18.G2LenSmoothGap
import QuantumZipper.Proofs.Thm18.G4CMeas4Good
import QuantumZipper.Proofs.Zipper.Cor15GoodWeld

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T, (G-b): law transfer of the Palm-window functional

The Palm-window functional `g3plPhi` of a field reads the field only through its regularized
circle averages (`avgReg`: boundary measure, translations, canonical proxies are all built from
`avgReg`, `Factorization.*_congr`). Its measurable version `g3plPhiM` (boundary measure read on
its certificate, `bdryM`) is a measurable functional of the field (a measurable family of
locally finite measures integrated against a jointly measurable integrand), and it agrees with
`g3plPhi` on good samples. Hence `E[Φ(Y)]` only depends on the law `fieldLawFull H Y P`, and the
comparison `G3PlPhiStmt` reduces to the explicit representative `wedgeRep` of `IsQuantumWedge`
(`g3PlPhiStmt_of_rep`). Own argument (law transfer, as `G1CoreRep.g1RegFixedStmt_of_rep`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm

/-! ## Integrating a jointly measurable function against a measurable family of measures -/

theorem measurable_lintegral_family {α : Type*} [MeasurableSpace α] {ν : α → Measure ℝ}
    (hν : Measurable ν) (hfin : ∀ a (N : ℕ), ν a (Icc (-(N : ℝ)) N) ≠ ⊤) {H : α × ℝ → ℝ≥0∞}
    (hH : Measurable H) : Measurable fun a => ∫⁻ x, H (a, x) ∂(ν a) := by
  have hN : ∀ N : ℕ, Measurable fun a => ∫⁻ x, H (a, x) ∂((ν a).restrict (Icc (-(N : ℝ)) N)) := by
    intro N
    set m : α → ℝ≥0∞ := fun a => ν a (Icc (-(N : ℝ)) N) with hmdef
    have hm : Measurable m := (Measure.measurable_coe measurableSet_Icc).comp hν
    have hκm : Measurable fun a => (m a + 1)⁻¹ • (ν a).restrict (Icc (-(N : ℝ)) N) := by
      refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
      simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hs]
      exact (hm.add_const 1).inv.mul ((Measure.measurable_coe (hs.inter measurableSet_Icc)).comp hν)
    let κ : Kernel α ℝ := ⟨fun a => (m a + 1)⁻¹ • (ν a).restrict (Icc (-(N : ℝ)) N), hκm⟩
    have hκ : ∀ a, κ a = (m a + 1)⁻¹ • (ν a).restrict (Icc (-(N : ℝ)) N) := fun a => rfl
    haveI : IsFiniteKernel κ := ⟨⟨1, ENNReal.one_lt_top, fun a => by
      rw [hκ, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply MeasurableSet.univ,
        univ_inter]
      have h1 : m a + 1 ≠ 0 := by simp
      have h2 : m a + 1 ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hfin a N, ENNReal.one_ne_top⟩
      calc (m a + 1)⁻¹ * ν a (Icc (-(N : ℝ)) N) ≤ (m a + 1)⁻¹ * (m a + 1) := by
            gcongr; exact le_self_add
        _ = 1 := ENNReal.inv_mul_cancel h1 h2⟩⟩
    have e : (fun a => ∫⁻ x, H (a, x) ∂((ν a).restrict (Icc (-(N : ℝ)) N))) =
        fun a => (m a + 1) * ∫⁻ x, H (a, x) ∂(κ a) := by
      funext a
      have h1 : m a + 1 ≠ 0 := by simp
      have h2 : m a + 1 ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hfin a N, ENNReal.one_ne_top⟩
      rw [hκ, lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel h1 h2,
        one_mul]
    rw [e]
    exact (hm.add_const 1).mul (hH.lintegral_kernel_prod_right' (κ := κ))
  have e : (fun a => ∫⁻ x, H (a, x) ∂(ν a)) =
      fun a => ⨆ N : ℕ, ∫⁻ x, H (a, x) ∂((ν a).restrict (Icc (-(N : ℝ)) N)) := by
    funext a
    have hHa : Measurable fun x => H (a, x) := hH.comp (measurable_const.prodMk measurable_id)
    have hsup : (fun x => H (a, x)) =
        fun x => ⨆ N : ℕ, (Icc (-(N : ℝ)) N).indicator (fun x => H (a, x)) x := by
      funext x
      refine le_antisymm ?_ (iSup_le fun N => indicator_le_self _ _ x)
      obtain ⟨N, hN⟩ := exists_nat_ge |x|
      refine le_iSup_of_le N (le_of_eq ?_)
      rw [indicator_of_mem]
      exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
    conv_lhs => rw [hsup]
    rw [lintegral_iSup (fun N => hHa.indicator measurableSet_Icc) (fun N M hNM x => ?_)]
    · exact iSup_congr fun N => lintegral_indicator measurableSet_Icc _
    · refine indicator_le_indicator_of_subset (Icc_subset_Icc ?_ ?_) (fun _ => bot_le) x
      · exact neg_le_neg (by exact_mod_cast hNM)
      · exact_mod_cast hNM
  rw [e]
  exact Measurable.iSup hN

/-! ## The measurable version of the Palm-window functional -/

theorem bdryM_Icc_ne_top (γ : ℝ) (y : FieldSample) (a b : ℝ) : bdryM γ y (Icc a b) ≠ ⊤ :=
  ((bdryM_le_qBoundaryMeasure γ y _).trans_lt (qBoundaryMeasure_Icc_lt_top γ _ _ _)).ne

theorem measurable_bdryM_Icc (γ : ℝ) :
    Measurable fun p : FieldSample × ℝ => bdryM γ p.1 (Icc p.2 0) :=
  measurable_measure_Icc_zero (measurable_bdryM γ) fun y b => bdryM_Icc_ne_top γ y b 0

theorem measurable_g3plPartner (γ : ℝ) :
    Measurable fun p : FieldSample × ℝ =>
      lenRight (bdryM γ p.1) (bdryM γ p.1 (Icc p.2 0)).toReal := by
  have ha : Measurable fun p : FieldSample × ℝ => bdryM γ p.1 :=
    (measurable_bdryM γ).comp (f := Prod.fst) measurable_fst
  have hb : Measurable fun p : FieldSample × ℝ => (bdryM γ p.1 (Icc p.2 0)).toReal :=
    ENNReal.measurable_toReal.comp (f := fun p : FieldSample × ℝ => bdryM γ p.1 (Icc p.2 0))
      (measurable_bdryM_Icc γ)
  have h1 : Measurable fun p : FieldSample × ℝ =>
      ((bdryM γ p.1, (bdryM γ p.1 (Icc p.2 0)).toReal) : Measure ℝ × ℝ) :=
    Measurable.prodMk ha hb
  exact measurable_lenRight.comp (f := fun p : FieldSample × ℝ =>
    ((bdryM γ p.1, (bdryM γ p.1 (Icc p.2 0)).toReal) : Measure ℝ × ℝ)) h1

theorem bdryM_congr {γ : ℝ} {y y' : FieldSample} (h : avgReg y = avgReg y') :
    bdryM γ y = bdryM γ y' := by
  unfold bdryM E1.M4.BCert
  rw [Factorization.bdryApprox_congr h, Factorization.qBoundaryMeasure_congr h]

end R18
end QuantumZipper
