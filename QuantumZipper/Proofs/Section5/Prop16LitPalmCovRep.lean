import QuantumZipper.Proofs.Section5.Prop16LitPalmCovLoc
import QuantumZipper.Proofs.Section5.Prop16LitMeasEx

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: measurable raw coordinates of the rebuilt zooms

Towards `Prop16Lit.Prop16LitRepMeasStmt` (`Prop16LitPalmCov.lean`): the raw coordinates of the
literal zoom `zoomFieldLit γ C (Y q) (t q) (ψ (t q))` of a measurable family of fields at a
measurable point are a measurable function of the parameter wherever the chart is differentiable
on `ℍ` (`exists_measurable_coords_zoomFieldLit`), and so are those of the straight zoom; in
particular for the field `repFam D a b 0 y` rebuilt from the local readings `y`
(`exists_measurable_coords_litRep`, `measurable_coords_zoomField_rep`). Own elementary argument
(the proof of `prop16LitMeasStmt_of_exists`, `Prop16LitMeasEx.lean`).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Lit

variable {α : Type*} [MeasurableSpace α]

/-- **Measurable raw coordinates of the literal zoom of a measurable family.** -/
theorem exists_measurable_coords_zoomFieldLit {Y : α → FieldSample} (hY : Measurable Y)
    {t : α → ℝ} (ht : Measurable t) {ψ : ℝ → ℂ → ℂ}
    (hψm : Measurable fun q : ℝ × ℂ => ψ q.1 q.2) (γ C : ℝ) :
    ∃ Φ : α → ℕ → ℝ, Measurable Φ ∧ ∀ q, DifferentiableOn ℂ (ψ (t q)) H →
      Factorization.coords (zoomFieldLit γ C (Y q) (t q) (ψ (t q))) = Φ q := by
  obtain ⟨T, hTdef⟩ : ∃ T : α → FieldSample, T = fun q =>
      Factorization.reconstruct (Factorization.coords (translate (Y q) (t q : ℂ))) := ⟨_, rfl⟩
  have hT : Measurable T := by
    rw [hTdef]
    refine Factorization.measurable_reconstruct.comp ?_
    exact Measurable.comp (g := fun q : FieldSample × ℝ =>
        Factorization.coords (translate q.1 (q.2 : ℂ)))
      (f := fun q : α => (Y q, t q)) IndepParams.measurable_coords_translate (hY.prodMk ht)
  refine ⟨fun q i => (evalReg (T q) ((fcI i).map (ψ (t q))) +
      Qc γ * ∫ u, Real.log ‖chartDeriv ψ (t q, u)‖ ∂(fcI i)) + C / γ * ((fcI i) univ).toReal,
    ?_, fun q hq => ?_⟩
  · refine measurable_pi_iff.2 fun i => ?_
    have hlog : Measurable fun q : α × ℂ => Real.log ‖chartDeriv ψ (t q.1, q.2)‖ :=
      Real.measurable_log.comp ((measurable_chartDeriv hψm).comp
        ((ht.comp measurable_fst).prodMk measurable_snd)).norm
    refine ((MeasEx.measurable_evalReg_map hT (g := fun q z => ψ (t q) z)
      (hψm.comp ((ht.comp measurable_fst).prodMk measurable_snd)) _).add
      (measurable_const.mul ?_)).add measurable_const
    exact (StronglyMeasurable.integral_prod_right' hlog.stronglyMeasurable).measurable
  · funext i
    have hd : ∀ᵐ u ∂(fcI i), DifferentiableAt ℂ (ψ (t q)) u :=
      (TwoPoint.foldedCircle_ae_mem_H _ (radius_pos _)).mono fun u hu =>
        (hq u hu).differentiableAt (isOpen_H.mem_nhds hu)
    have hi : ∫ u, Real.log ‖deriv (ψ (t q)) u‖ ∂(fcI i) =
        ∫ u, Real.log ‖chartDeriv ψ (t q, u)‖ ∂(fcI i) :=
      integral_congr_ae (hd.mono fun u hu => by simp only [chartDeriv_eq hu])
    show zoomFieldLit γ C (Y q) (t q) (ψ (t q)) (fcI i) = _
    rw [hTdef]
    simp only [zoomFieldLit, addConst, coordChange, hi]
    rw [Factorization.evalReg_congr (Factorization.avgReg_reconstruct_coords _)]

/-- The rebuilt field is measurable in the readings. -/
theorem measurable_repFam (D : Set ℂ) (a b : ℝ) :
    Measurable fun y : ℕ → ℝ => Prop16Asm.repFam D a b 0 y :=
  Factorization.measurable_reconstruct.comp (Prop16Asm.measurable_repAdj (D := D) (a := a) (b := b)
    (h0 := 0))

/-- **Measurable raw coordinates of the literal zoom of the rebuilt field** (on `(a,b)`). -/
theorem exists_measurable_coords_litRep {D : Set ℂ} {a b : ℝ} {ψ : ℝ → ℂ → ℂ} {r₀ : ℝ → ℝ}
    (hfam : LitFamily D a b ψ r₀) (γ C : ℝ) :
    ∃ Φ : (ℕ → ℝ) × ℝ → ℕ → ℝ, Measurable Φ ∧ ∀ q : (ℕ → ℝ) × ℝ, q.2 ∈ Ioo a b →
      Factorization.coords (zoomFieldLit γ C (Prop16Asm.repFam D a b 0 q.1) q.2 (ψ q.2)) =
        Φ q := by
  obtain ⟨Φ, hΦ, hΦe⟩ := exists_measurable_coords_zoomFieldLit
    ((measurable_repFam D a b).comp measurable_fst) measurable_snd hfam.1 γ C
  exact ⟨Φ, hΦ, fun q hq => hΦe q (hfam.2.2 q.2 hq).1⟩

/-- **Measurable raw coordinates of the straight zoom of the rebuilt field.** -/
theorem measurable_coords_zoomField_rep (D : Set ℂ) (a b γ C : ℝ) :
    Measurable fun q : (ℕ → ℝ) × ℝ =>
      Factorization.coords (zoomField γ C (Prop16Asm.repFam D a b 0 q.1) q.2) := by
  have hR : ∀ μ : Measure ℂ, Measurable fun y : ℕ → ℝ => Prop16Asm.repFam D a b 0 y μ :=
    fun μ => (measurable_pi_apply μ).comp (measurable_repFam D a b)
  have e0 : ∀ y, ofFun (fun _ => (0 : ℝ)) + Prop16Asm.repFam D a b 0 y =
      Prop16Asm.repFam D a b 0 y := fun y => by funext μ; simp [ofFun]
  have := Prop16Area.measurable_coords_zoomField γ C (fun _ => (0 : ℝ)) hR
  simpa only [e0] using this

end Prop16Lit

end QuantumZipper
