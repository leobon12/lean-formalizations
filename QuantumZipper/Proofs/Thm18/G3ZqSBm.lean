import QuantumZipper.Proofs.Thm18.G3ZqResc3
import QuantumZipper.Proofs.Thm18.G1ProfileRed
import QuantumZipper.Proofs.Thm18.G4TraceNull2Scale
import QuantumZipper.Proofs.Zipper.ESMComplF1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3ZqS (1): a Brownian motion scaled by an independent random factor

For a Brownian motion `B` and a measurable positive random factor `c(ω')` on an independent
space, the process `B̃_t(ω', a) = S_{c(ω')}(a)_t` (Brownian scaling of the path `a`, read on the
canonical path space through the continuous regularization `pathReg`) is again a Brownian motion
under `P' ⊗ W` (`W` the path law), independent of every variable of `ω'` alone. This is Brownian
scaling (Revuz–Yor, Ch. I, Prop. 1.10) applied fibrewise: conditionally on `ω'` the process is a
Brownian motion, so its law does not depend on `ω'`.

It turns the COUPLED statement "a.s. in `ω'`, a.s. in the path, a property of
`(field(ω'), S_{b(ω')} path)`" into a statement about one Brownian motion independent of one
field on one space, where the setting-level a.s. results of Theorem 1.8 apply
(`Measure.ae_ae_of_ae_prod` needs no measurability of the property).

Own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqS

open G1Zm

variable {Ω' : Type} [MeasurableSpace Ω'] {Ω : Type} [MeasurableSpace Ω]

/-- The randomly scaled coordinate process on `Ω' × (ℝ≥0 → ℝ)`. -/
def rsBM (c : Ω' → ℝ) : ℝ≥0 → Ω' × (ℝ≥0 → ℝ) → ℝ :=
  fun t z => scalePath (c z.1) (G1Pkg.pathReg z.2) t

theorem measurable_pathReg_uncurry :
    Measurable (Function.uncurry fun (s : ℝ≥0) (a : ℝ≥0 → ℝ) => G1Pkg.pathReg a s) :=
  measurable_uncurry_of_continuous_of_measurable (fun a => G1Pkg.pathReg_spec.2.1 a)
    (fun s => (measurable_pi_apply s).comp G1Pkg.pathReg_spec.1)

theorem measurable_rsBM {c : Ω' → ℝ} (hc : Measurable c) (t : ℝ≥0) :
    Measurable (rsBM c t) := by
  have h1 : Measurable fun z : Ω' × (ℝ≥0 → ℝ) => ((c z.1 ^ 2).toNNReal * t, z.2) :=
    ((measurable_real_toNNReal.comp ((hc.comp measurable_fst).pow_const 2)).mul_const t).prodMk
      measurable_snd
  exact (measurable_pathReg_uncurry.comp h1).div (hc.comp measurable_fst)

theorem measurable_pathOf_rsBM {c : Ω' → ℝ} (hc : Measurable c) :
    Measurable (pathOf (rsBM c)) :=
  measurable_pi_iff.2 fun t => measurable_rsBM hc t

/-- At fixed `ω'`, the fibre process is the scaled regularized coordinate process. -/
theorem rsBM_fibre {c : Ω' → ℝ} (ω' : Ω') (hc : 0 < c ω') :
    (fun t (a : ℝ≥0 → ℝ) => rsBM c t (ω', a)) = G4TraceNull2.scaledBM (c ω') G1RC.regCoord := by
  funext t a
  simp only [rsBM, scalePath, G4TraceNull2.scaledBM, G1RC.regCoord]
  rw [Real.coe_toNNReal _ (sq_nonneg _), Real.sqrt_sq hc.le, div_eq_inv_mul]

variable {P' : Measure Ω'} [IsProbabilityMeasure P'] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

theorem fibre_isBrownian (hB : IsBrownianReal B P) {c : Ω' → ℝ} (ω' : Ω') (hc : 0 < c ω') :
    IsBrownianReal (fun t (a : ℝ≥0 → ℝ) => rsBM c t (ω', a)) (P.map (pathOf B)) := by
  rw [rsBM_fibre ω' hc]
  exact G4TraceNull2.isBrownianReal_scaledBM (G1RC.isBrownianReal_regCoord hB) hc

/-- **The randomly scaled process is a Brownian motion.** -/
theorem isBrownianReal_rsBM (hB : IsBrownianReal B P) {c : Ω' → ℝ} (hc : Measurable c)
    (hc0 : ∀ ω', 0 < c ω') :
    IsBrownianReal (rsBM c) (P'.prod (P.map (pathOf B))) := by
  have hW : IsProbabilityMeasure (P.map (pathOf B)) :=
    (Measure.isProbabilityMeasure_map_iff (IsBrownianReal.aemeasurable_pathOf hB)).2
      inferInstance
  refine { hasLaw := fun I => ?_, cont := ae_of_all _ fun z => ?_ }
  · have hF : Measurable fun z : Ω' × (ℝ≥0 → ℝ) => I.restrict (rsBM c · z) :=
      measurable_pi_iff.2 fun i => measurable_rsBM hc i
    refine ⟨hF.aemeasurable, ?_⟩
    ext S hS
    rw [Measure.map_apply hF hS, Measure.prod_apply (hF hS)]
    have hfib : ∀ ω', (P.map (pathOf B)) (Prod.mk ω' ⁻¹'
        ((fun z : Ω' × (ℝ≥0 → ℝ) => I.restrict (rsBM c · z)) ⁻¹' S)) = BrownianReal.projectiveFamily I S := by
      intro ω'
      have h := ((fibre_isBrownian hB ω' (hc0 ω')).hasLaw I).map_eq
      rw [← h, Measure.map_apply_of_aemeasurable
        ((fibre_isBrownian hB ω' (hc0 ω')).hasLaw I).aemeasurable hS]
      rfl
    simp_rw [hfib]
    simp
  · show Continuous fun t => scalePath (c z.1) (G1Pkg.pathReg z.2) t
    exact G3Zq.continuous_scalePath (G1Pkg.pathReg_spec.2.1 z.2)

/-- The fibre path law is the path law of `B`. -/
theorem fibre_pathLaw (hB : IsBrownianReal B P) {c : Ω' → ℝ} (hc : Measurable c) (ω' : Ω')
    (hc0 : 0 < c ω') :
    (P.map (pathOf B)).map (fun a => pathOf (rsBM c) (ω', a)) =
      (P.map (pathOf B)).map (pathOf G1RC.regCoord) :=
  F1.map_pathOf_eq_of_isBrownianReal (fibre_isBrownian hB ω' hc0)
    (G1RC.isBrownianReal_regCoord hB)

/-- **Independence of the randomly scaled path from every variable of the first factor.** -/
theorem indepFun_rsBM (hB : IsBrownianReal B P) {c : Ω' → ℝ} (hc : Measurable c)
    (hc0 : ∀ ω', 0 < c ω') {E : Type} [MeasurableSpace E] (Y : Ω' → E) :
    IndepFun (pathOf (rsBM c)) (fun z : Ω' × (ℝ≥0 → ℝ) => Y z.1)
      (P'.prod (P.map (pathOf B))) := by
  set W := P.map (pathOf B) with hWdef
  have hW : IsProbabilityMeasure W :=
    (Measure.isProbabilityMeasure_map_iff (IsBrownianReal.aemeasurable_pathOf hB)).2
      inferInstance
  have hpm := measurable_pathOf_rsBM hc
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  set κ : ℝ≥0∞ := (W.map (pathOf G1RC.regCoord)) s with hκ
  have hfib : ∀ ω', W (Prod.mk ω' ⁻¹' (pathOf (rsBM c) ⁻¹' s)) = κ := by
    intro ω'
    have h := congrArg (fun m : Measure (ℝ≥0 → ℝ) => m s) (fibre_pathLaw hB hc ω' (hc0 ω'))
    rw [Measure.map_apply (f := fun a => pathOf (rsBM c) (ω', a))
      (hpm.comp measurable_prodMk_left) hs] at h
    rw [hκ, ← h]
    rfl
  set E₁ : Set (Ω' × (ℝ≥0 → ℝ)) := pathOf (rsBM c) ⁻¹' s with hE₁
  have hE₁m : MeasurableSet E₁ := hpm hs
  set T : Set Ω' := Y ⁻¹' t with hT
  have hgt : (fun z : Ω' × (ℝ≥0 → ℝ) => Y z.1) ⁻¹' t = T ×ˢ univ := by
    ext z; simp [hT]
  have hμE : (P'.prod W) E₁ = κ := by
    rw [Measure.prod_apply hE₁m]; simp_rw [hfib]; simp
  have hμT : (P'.prod W) (T ×ˢ univ) = P' T := by
    rw [Measure.prod_prod, measure_univ, mul_one]
  rw [hgt, hμE, hμT]
  -- upper bound through a measurable hull of `T`
  apply le_antisymm
  · set T' := toMeasurable P' T with hT'
    have hT'm : MeasurableSet T' := measurableSet_toMeasurable _ _
    calc (P'.prod W) (E₁ ∩ T ×ˢ univ) ≤ (P'.prod W) (E₁ ∩ T' ×ˢ univ) :=
          measure_mono (inter_subset_inter_right _
            (prod_mono (subset_toMeasurable _ _) le_rfl))
      _ = ∫⁻ ω', T'.indicator (fun _ => κ) ω' ∂P' := by
          rw [Measure.prod_apply (hE₁m.inter (hT'm.prod MeasurableSet.univ))]
          refine lintegral_congr fun ω' => ?_
          by_cases h : ω' ∈ T'
          · rw [indicator_of_mem h, ← hfib ω']
            congr 1; ext a; simp [h]
          · rw [indicator_of_notMem h]
            have : Prod.mk ω' ⁻¹' (E₁ ∩ T' ×ˢ univ) = ∅ := by
              ext a; simp [h]
            rw [this, measure_empty]
      _ = κ * P' T := by
          rw [lintegral_indicator_const hT'm, measure_toMeasurable, mul_comm]
  · set M := toMeasurable (P'.prod W) (E₁ ∩ T ×ˢ univ) ∩ E₁ with hM
    have hMm : MeasurableSet M := (measurableSet_toMeasurable _ _).inter hE₁m
    have hMsup : E₁ ∩ T ×ˢ univ ⊆ M :=
      subset_inter (subset_toMeasurable _ _) inter_subset_left
    have hμM : (P'.prod W) M = (P'.prod W) (E₁ ∩ T ×ˢ univ) :=
      le_antisymm ((measure_mono inter_subset_left).trans_eq (measure_toMeasurable _))
        (measure_mono hMsup)
    have hfm : Measurable fun ω' => W (Prod.mk ω' ⁻¹' M) := measurable_measure_prodMk_left hMm
    set T₂ := {ω' | κ ≤ W (Prod.mk ω' ⁻¹' M)} with hT₂
    have hT₂m : MeasurableSet T₂ := measurableSet_le measurable_const hfm
    have hTT₂ : T ⊆ T₂ := by
      intro ω' hω'
      show κ ≤ W (Prod.mk ω' ⁻¹' M)
      rw [← hfib ω']
      refine measure_mono fun a ha => ?_
      exact hMsup ⟨ha, hω', mem_univ _⟩
    rw [← hμM, Measure.prod_apply hMm]
    calc κ * P' T ≤ κ * P' T₂ := by gcongr
      _ = ∫⁻ ω', T₂.indicator (fun _ => κ) ω' ∂P' := by
          rw [lintegral_indicator_const hT₂m]
      _ ≤ ∫⁻ ω', W (Prod.mk ω' ⁻¹' M) ∂P' := by
          refine lintegral_mono fun ω' => ?_
          by_cases h : ω' ∈ T₂
          · rw [indicator_of_mem h]; exact h
          · rw [indicator_of_notMem h]; exact bot_le

end G3ZqS
end Thm18Asm
end QuantumZipper
