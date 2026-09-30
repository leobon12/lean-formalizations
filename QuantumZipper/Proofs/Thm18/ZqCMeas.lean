import QuantumZipper.Proofs.Thm18.ZqCMass2
import QuantumZipper.Proofs.Thm18.G3ZqL10Cert

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-CORE (6): measurability of the Palm-side core functional in the Palm point

`aemeasurable_palmJ`: `x ↦ E[1_{W_x} Γ(zoom_L h^x)]` is a.e.-measurable on the core. The Palm
field `h^x = N_S(ofFun (palmProf γ x) + V)` is jointly measurable in `(x, ω)` on every folded
circle (the profile is jointly measurable, `measurable_palmProf_joint`), the zoom datum only reads
the dyadic coordinates (`G3ZqL.g3coordsM_reconstruct_coords`) and on the core the window event is
the circle functional `winS` (`ZqCMass`).

Own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace ZqC

open G3Z2b2 D3Plus G1Zm G3Zq G3ZqL G3ZqO Factorization G2PalmLoc G3Cv K3 GFFExist

theorem measurable_palmProf_joint (γ : ℝ) :
    Measurable fun p : ℝ × ℂ => G3Za.palmProf γ p.1 p.2 := by
  have e : (fun p : ℝ × ℂ => G3Za.palmProf γ p.1 p.2) = fun p => (γ - 2 / γ) * -Real.log ‖p.2‖ +
      γ / 2 * (neumannH (p.1 : ℂ) p.2 - -2 * Real.posLog ‖p.2‖) := by
    funext p
    simp only [G3Za.palmProf, PalmNorm.shiftFun, LogSingGood.Lf, R18.g3zS,
      Thm18Asm.kPot_refS_eq]
  rw [e]
  have h1 : Measurable fun p : ℝ × ℂ => neumannH (p.1 : ℂ) p.2 :=
    measurable_neumannH.comp ((Complex.measurable_ofReal.comp measurable_fst).prodMk
      measurable_snd)
  have h2 : Measurable fun p : ℝ × ℂ => Real.log ‖p.2‖ :=
    Real.measurable_log.comp (measurable_norm.comp measurable_snd)
  have h3 : Measurable fun p : ℝ × ℂ => Real.posLog ‖p.2‖ :=
    Real.continuous_posLog.measurable.comp (measurable_norm.comp measurable_snd)
  exact (h2.neg.const_mul _).add ((h1.sub (h3.const_mul _)).const_mul _)

theorem measurable_ofFun_palmProf (γ : ℝ) (μ : Measure ℂ) [SFinite μ] :
    Measurable fun x : ℝ => ofFun (G3Za.palmProf γ x) μ := by
  have h := (measurable_palmProf_joint γ).stronglyMeasurable
  exact (StronglyMeasurable.integral_prod_right' (ν := μ) h).measurable

/-- The Palm field is jointly measurable in `(x, ω)` on every s-finite measure. -/
theorem measurable_palmField_apply {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {V : Ω' → FieldSample} (hV : IsFreeGFFModConstH V P') (γ : ℝ) (μ : Measure ℂ)
    [SFinite μ] :
    Measurable fun p : ℝ × Ω' => G1Zm.palmFieldAt γ p.1 (V p.2) μ := by
  have e : (fun p : ℝ × Ω' => G1Zm.palmFieldAt γ p.1 (V p.2) μ) = fun p =>
      (ofFun (G3Za.palmProf γ p.1) μ + V p.2 μ) +
        (-(ofFun (G3Za.palmProf γ p.1) R18.g3zS + V p.2 R18.g3zS)) * (μ Set.univ).toReal := by
    funext p
    simp only [G1Zm.palmFieldAt, PalmNorm.normAt, addConst, Pi.add_apply]
  rw [e]
  have hf : ∀ ν : Measure ℂ, SFinite ν → Measurable fun p : ℝ × Ω' =>
      ofFun (G3Za.palmProf γ p.1) ν := fun ν _ =>
    (measurable_ofFun_palmProf γ ν).comp measurable_fst
  have hv : ∀ ν : Measure ℂ, Measurable fun p : ℝ × Ω' => V p.2 ν := fun ν =>
    (hV.measurable_coord ν).comp measurable_snd
  exact ((hf μ inferInstance).add (hv μ)).add
    ((((hf _ inferInstance).add (hv _)).neg).mul_const _)

theorem measurable_vOf_palmField {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {V : Ω' → FieldSample} (hV : IsFreeGFFModConstH V P') (γ : ℝ) :
    Measurable fun p : ℝ × Ω' => vOf (G1Zm.palmFieldAt γ p.1 (V p.2)) :=
  measurable_pi_iff.2 fun j => measurable_palmField_apply hV γ _

theorem measurable_coords_palmField {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {V : Ω' → FieldSample} (hV : IsFreeGFFModConstH V P') (γ : ℝ) :
    Measurable fun p : ℝ × Ω' => coords (G1Zm.palmFieldAt γ p.1 (V p.2)) :=
  measurable_pi_iff.2 fun j => measurable_palmField_apply hV γ _

theorem g1zM_reconstruct_coords (γ L : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool)
    (y : FieldSample) (a : ℝ≥0 → ℝ) (x : ℝ) :
    g1zM γ L Ψ left ((reconstruct (coords y), a), x) = g1zM γ L Ψ left ((y, a), x) := by
  unfold g1zM g3zoomLawM
  rw [g3coordsM_reconstruct_coords]

/-- **The Palm-side core functional is a.e.-measurable on the core.** -/
theorem aemeasurable_palmJ {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hsel : G1PsiSel γ Ψ)
    (L : ℝ) (R : ℕ) {Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞} (hΓ : Measurable Γ)
    (left : Bool) (U : ℝ) {η δ : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) (hδ : 0 < δ)
    (hδη : δ < η / 2) (a : ℝ≥0 → ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] {V : Ω' → FieldSample} (hV : IsFreeGFFModConstH V P') :
    AEMeasurable (palmJ γ L R Γ Ψ left U δ a P' V) (volume.restrict (coreSet left η)) := by
  set G : ℝ × Ω' → ℝ≥0∞ := fun p =>
    (winS γ left U δ).indicator 1 (vOf (G1Zm.palmFieldAt γ p.1 (V p.2)), p.1) *
      Γ (g1zLocData R (g1zM γ L Ψ left
        ((reconstruct (coords (G1Zm.palmFieldAt γ p.1 (V p.2))), a), p.1))) with hG
  have h1 : Measurable fun p : ℝ × Ω' =>
      (winS γ left U δ).indicator (1 : (ℕ → ℝ) × ℝ → ℝ≥0∞)
        (vOf (G1Zm.palmFieldAt γ p.1 (V p.2)), p.1) := by
    have h0 : Measurable ((winS γ left U δ).indicator (1 : (ℕ → ℝ) × ℝ → ℝ≥0∞)) :=
      measurable_one.indicator (measurableSet_winS γ left U δ)
    have h := h0.comp ((measurable_vOf_palmField hV γ).prodMk measurable_fst)
    simp only [Function.comp_def] at h
    exact h
  have hq : Measurable fun p : ℝ × Ω' =>
      (((reconstruct (coords (G1Zm.palmFieldAt γ p.1 (V p.2))), a), p.1) :
        (FieldSample × (ℝ≥0 → ℝ)) × ℝ) :=
    ((measurable_reconstruct.comp (measurable_coords_palmField hV γ)).prodMk
      measurable_const).prodMk measurable_fst
  have h2 : Measurable fun p : ℝ × Ω' => Γ (g1zLocData R (g1zM γ L Ψ left
      ((reconstruct (coords (G1Zm.palmFieldAt γ p.1 (V p.2))), a), p.1))) := by
    have h := (hΓ.comp ((measurable_g1zLocData R).comp (measurable_g1zM hsel L left))).comp hq
    simp only [Function.comp_def] at h
    exact h
  have hGm : Measurable G := h1.mul h2
  have hI : Measurable fun x => ∫⁻ ω, G (x, ω) ∂P' := hGm.lintegral_prod_right'
  refine hI.aemeasurable.congr ?_
  refine (ae_restrict_iff' (measurableSet_coreSet left η)).2 (Eventually.of_forall fun x hx => ?_)
  refine lintegral_congr fun ω => ?_
  obtain ⟨b1, b2⟩ := seg_bounds hη4 hδ hδη hx
  have hiff : (vOf (G1Zm.palmFieldAt γ x (V ω)), x) ∈ winS γ left U δ ↔
      ω ∈ palmWin γ left U δ x V := by
    have e1 : (vOf (G1Zm.palmFieldAt γ x (V ω)), x) ∈ winS γ left U δ ↔
        locLen γ (recF (vOf (G1Zm.palmFieldAt γ x (V ω)))) (segLo left δ x) (segHi left δ x)
          (δ / 4) ≤ ENNReal.ofReal U := Iff.rfl
    have e2 : ω ∈ palmWin γ left U δ x V ↔
        winLen γ left δ x (G1Zm.palmFieldAt γ x (V ω)) ≤ ENNReal.ofReal U := Iff.rfl
    rw [e1, e2, locLen_recF γ _ (by positivity) b1 b2, winLen_eq_locLen γ left hδ]
  simp only [hG]
  rw [g1zM_reconstruct_coords]
  by_cases hω : ω ∈ palmWin γ left U δ x V
  · rw [indicator_of_mem (hiff.2 hω), indicator_of_mem hω]
    simp only [Pi.one_apply]
  · rw [indicator_of_notMem (fun h => hω (hiff.1 h)), indicator_of_notMem hω]

end ZqC
end Thm18Asm
end QuantumZipper
