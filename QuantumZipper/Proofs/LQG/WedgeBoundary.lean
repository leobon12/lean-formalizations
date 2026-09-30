import QuantumZipper.Proofs.LQG.WedgeBoundaryReg
import QuantumZipper.Proofs.LQG.LogSingGood
import QuantumZipper.Proofs.LQG.AtomlessUncond
import QuantumZipper.Proofs.LQG.Positivity

/-!
# WEDGE-BDRY (3): the wedge boundary measure is atomless and charges every interval

* `ae_bReg_logSing`: for a free field `X` and `α < Q`, a.s. `X + α(−log‖·‖)` is good and its
  boundary measure `|t|^{−αγ/2} ν_X` (restricted to `ℝ \ {0}`, M4-P4 `ae_logSingularity`) has no
  atoms and charges every open interval (from M4-P5 `ae_noAtoms_zField'`, M4-P2
  `ae_forall_pos_qBoundaryMeasure_Ioo`).
* `ae_bReg_wedgeField`: the same for the reference wedge field `wedgeField (lateralPart X) A Q`
  (transfer `wedge_ae_of_logSing`, rule (5.1)).
* `ae_bReg_canonical_wedgeField`: the same for its canonical description, on the event
  `0 < scaleParam` (R23 (b)).
* `ae_atomless_pos_of_isQuantumWedge`: the same for every quantum wedge, given R23 (b) for the
  reference field and a.e.-measurability of the two full-coordinate maps.

Sources: Sheffield (arXiv:1012.4797) §1.6 pp. 20–22 (the wedge field is a free boundary field with
an `α`-log singularity at `0` plus an independent radial part); Duplantier–Sheffield (2011) §6
(boundary measure, `e^{γ f/2}`-rule for continuous `f`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace QuantumZipper

namespace WedgeBdry

/-- **Free field with a log singularity at `0`.** -/
theorem ae_bReg_logSing {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample) (hX : IsFreeGFFModConstH X P) :
    ∀ᵐ ω ∂P, BReg γ (X ω + ofFun fun z => α * -Real.log ‖z‖) := by
  filter_upwards [LogSingGood.logSingGoodAS_holds hγ hγ2 hα Ω _ P X inferInstance hX,
    LogSing.ae_logSingularity hX hγ hγ2 1 hα 0 (LogSing.p3bBound hX hγ hγ2 one_pos (by simp)),
    AtomlessUncond.ae_noAtoms_zField' hX hγ hγ2 1,
    Positivity.ae_forall_pos_qBoundaryMeasure_Ioo hX hγ hγ2,
    Positivity.ae_qBoundaryMeasure_eq_smul_zField hX hγ hγ2 1] with ω hg hls hat hpos hsm
  set c := X ω (foldedCircle 0 1) with hc
  set Z := BdryExist.zField X 1 ω with hZ
  have hlog : LogSing.logPot α 0 = fun z : ℂ => α * -Real.log ‖z‖ := by
    funext z; simp [LogSing.logPot]
  set W := Z + ofFun (LogSing.logPot α 0) with hW
  have e2 : W = addConst (X ω + ofFun fun z => α * -Real.log ‖z‖) (-c) := by
    funext μ
    simp only [hW, hZ, BdryExist.zField, addConst, Pi.add_apply, hlog, hc]
    ring
  have e1 : (X ω + ofFun fun z => α * -Real.log ‖z‖) = addConst W c := by
    rw [e2]; funext μ; simp only [addConst, Pi.add_apply]; ring
  have hWg : IsLQGGood γ W := e2 ▸ hg.addConst _
  obtain ⟨-, hνW, -, -⟩ := hls
  have hZat : ∀ t, qBoundaryMeasure γ Z {t} = 0 := fun t => hat.measure_singleton t
  have hZpos : ∀ u v : ℝ, u < v → 0 < qBoundaryMeasure γ Z (Ioo u v) := by
    intro u v huv
    refine pos_iff_ne_zero.2 fun h0 => (hpos u v huv).ne' ?_
    rw [hsm, Measure.smul_apply, h0, smul_zero]
  have hWat : ∀ t, qBoundaryMeasure γ W {t} = 0 := by
    intro t
    rw [hνW]
    exact withDensity_absolutelyContinuous _ _
      (le_antisymm ((Measure.restrict_apply_le _ _).trans (hZat t).le) zero_le)
  have hWpos : ∀ u v : ℝ, u < v → 0 < qBoundaryMeasure γ W (Ioo u v) := by
    intro u v huv
    rw [hνW]
    refine pos_iff_ne_zero.2 fun h0 => (hZpos u v huv).ne' ?_
    have hfm : Measurable fun t : ℝ => ENNReal.ofReal (|t - 0| ^ (-(α * γ / 2))) :=
      ENNReal.measurable_ofReal.comp
        ((continuous_abs.comp (continuous_id.sub continuous_const)).measurable.pow_const _)
    rw [withDensity_apply_eq_zero' hfm.aemeasurable,
      Measure.restrict_apply' (measurableSet_singleton 0).compl] at h0
    have hsub : Ioo u v \ {0} ⊆
        {t : ℝ | ENNReal.ofReal (|t - 0| ^ (-(α * γ / 2))) ≠ 0} ∩ Ioo u v ∩ {0}ᶜ := by
      rintro t ⟨ht, ht0⟩
      refine ⟨⟨?_, ht⟩, ht0⟩
      simp only [mem_setOf_eq, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact Real.rpow_pos_of_pos (abs_pos.2 (by simpa using ht0)) _
    have := measure_mono_null hsub h0
    rwa [measure_diff_null (hZat 0)] at this
  rw [e1]
  refine bReg_of (hWg.addConst c) (fun t => ?_) (fun u v huv => ?_)
  · rw [GoodSample.qBoundaryMeasure_addConst hWg, Measure.smul_apply, hWat, smul_zero]
  · rw [GoodSample.qBoundaryMeasure_addConst hWg, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' (hWpos u v huv).ne'

/-- **The reference wedge field.** -/
theorem ae_bReg_wedgeField {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [hP : IsProbabilityMeasure P']
    {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ} (hX : IsFreeGFFModConstH X P')
    (hA : IsWedgeProcess α (Qc γ) A P') (hI : IndepFun X (fun ω t => A t ω) P') :
    ∀ᵐ ω ∂P', BReg γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)) :=
  wedge_ae_of_logSing (BReg γ) (measurableSet_bReg γ) (bReg_reconstruct γ)
    (fun _ _ hφ hx => hx.add_ofFun hφ)
    (fun Ω _ P X hP hX => by have := hP; exact ae_bReg_logSing hγ hγ2 hα P X hX)
    Ω' P' X A hP hX hA hI

/-- **The canonical description of the reference wedge field**, on the event `0 < scaleParam`. -/
theorem ae_bReg_canonical_wedgeField {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ} (hX : IsFreeGFFModConstH X P')
    (hA : IsWedgeProcess α (Qc γ) A P') (hI : IndepFun X (fun ω t => A t ω) P')
    (hscale : ∀ᵐ ω ∂P',
      0 < scaleParam γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) :
    ∀ᵐ ω ∂P', BReg γ (canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) := by
  filter_upwards [ae_bReg_wedgeField hγ hγ2 hα hX hA hI, hscale] with ω h1 h2
  exact h1.rescale hγ h2

/-- **Every quantum wedge**, given R23 (b) (`0 < scaleParam` for the reference field) and the
a.e.-measurability of the full-coordinate maps of `Y` and of the reference field. -/
theorem ae_atomless_pos_of_isQuantumWedge {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → FieldSample)
    (hY : IsQuantumWedge γ α Y P)
    (hYm : AEMeasurable (fun ω => (CoordsFull.coordsFull (Y ω),
      fun ρ : TestFun H => pairRaw (Y ω) ρ.1)) P)
    (href : ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (X : Ω' → FieldSample)
      (A : ℝ → Ω' → ℝ), IsProbabilityMeasure P' → IsFreeGFFModConstH X P' →
      IsWedgeProcess α (Qc γ) A P' → IndepFun X (fun ω t => A t ω) P' →
      (∀ᵐ ω ∂P', 0 < scaleParam γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) ∧
      AEMeasurable (fun ω => (CoordsFull.coordsFull
        (canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))),
        fun ρ : TestFun H => pairRaw
          (canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) ρ.1)) P') :
    ∀ᵐ ω ∂P, (∀ t : ℝ, qBoundaryMeasure γ (Y ω) {t} = 0) ∧
      (∀ u v : ℝ, u < v → 0 < qBoundaryMeasure γ (Y ω) (Ioo u v)) := by
  obtain ⟨hα, Ω', _, P', X, A, hP', hX, hA, hI, hlaw⟩ := hY
  obtain ⟨hsc, hm⟩ := href Ω' P' X A hP' hX hA hI
  have h := ae_of_fieldLawFull_eq hlaw hYm hm (BReg γ) (measurableSet_bReg γ)
    (bReg_reconstruct γ) (ae_bReg_canonical_wedgeField hγ hγ2 hα hX hA hI hsc)
  filter_upwards [h] with ω hω
  exact ⟨hω.noAtom, fun u v huv => hω.pos huv⟩

end WedgeBdry

end QuantumZipper
