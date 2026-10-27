import MatedCRTHarmonic.GMSCase.ConeLaw
import MatedCRTHarmonic.GMSCase.IGData

/-!
# The Case 3 and Case 4 laws on the frozen mating-of-trees coupling

Source: (`[18]:N`), Proposition 4.10, Cases 2–4 and the final
paragraph, `[18]`; (inverse coordinate `2(w − z₀)`); the
IG observation is `(hIG₀, U)`, field plus phase).

On the frozen coupling `D`, the **full IG observation** is `igObs ω = ((hIG₀ ω, U ω), ηL ω)`, the
Case 0–4 whole-plane field is the normalized `X₀` (`normalizedWP (X₀ ω)`, definitionally CANON's
`Canon.normalizeWholePlane (X₀ ω)`), and the γ-cone field is
`coneField (X ω) (coneRadial γ γ B B')` (the field of `MoTInput.cellModelOfCoupling`).

* `map_igTransform_igObs`: the Case 4 transformation `igTransform r z₀` (IG field `hIG₀(·/2 + z₀)`
  renormalized, phase shifted by `(hIG₀)_{1/2}(z₀)` modulo `r = 2πχ`, curve `case4Curve z₀ ηL`)
  preserves the law of `igObs` (from IGData's `map_igTransform_of_ccPos` and the v4 `igMap`).
* `indepFun_coneTuple_igObs`, `indepFun_normalizedWP_igObs`, `indepFun_coneField_igObs`: the IG
  observation is independent of the cone data, of the normalized `X₀` and of the γ-cone field.
* **`map_case4Local_eq_cone`** (Case 4 ↔ cone, fixed root): the law of
  `(case4Field γ (normalizedWP X₀) z₀ |_𝔻, igTransform r z₀ igObs)` equals the law of
  `(γ-cone field |_𝔻, igObs)`.
* **`map_case3_marked_cone`** (Cases 2–4 with an independent root `z₀ ∼ λ`, `B̄_{1/2}(z₀) ⊆ B̄_1(0)`
  λ-a.s.): under `P ⊗ λ`, the law of `((z₀, (normalizedWP X₀)_{1/2}(z₀)),
  (case4Field|_𝔻, igTransform r z₀ igObs))` is `law(z₀, h_{1/2}(z₀)) ⊗ law(cone|_𝔻, igObs)`.
  The Case 2 index of [18] is `(normalizedWP X₀)_{1/2}(z₀) + γ log 2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace Filter
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSCase

open LQGMetric LQGMetric.Blueprint MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.IGLaw

/-- The full imaginary-geometry observation `((hIG₀, U), ηL)`. -/
def igObs {Ω : Type*} (hIG₀ : Ω → Field) (U : Ω → ℝ) (ηL : Ω → C(ℝ, ℂ)) (ω : Ω) :
    (DistC × ℝ) × C(ℝ, ℂ) :=
  ((hIG₀ ω, U ω), ηL ω)

/-- The cone tuple `(X, B, B', X₀, B₀, B₀')` of the frozen bundle. -/
def coneTuple {Ω : Type*} (X X₀ : Ω → Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) × Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) :=
  (X ω, (fun t => B t ω), (fun t => B' t ω), X₀ ω, (fun t => B₀ t ω), (fun t => B₀' t ω))

/-- Restricting `g + γ(−log|·|)` to `𝔻` adds the restricted singularity. -/
def addRestrictedLogSing (γ : ℝ) (T : DistOn (ballO (0 : ℂ) 1)) : DistOn (ballO (0 : ℂ) 1) :=
  T + restrictTo (ballO (0 : ℂ) 1) (MoTPort.ofFunC (logSing γ))

theorem measurable_addRestrictedLogSing (γ : ℝ) : Measurable (addRestrictedLogSing γ) := by
  refine measurable_distOn_iff.2 fun φ => ?_
  show Measurable fun T : DistOn (ballO (0 : ℂ) 1) =>
    T φ + restrictTo (ballO (0 : ℂ) 1) (MoTPort.ofFunC (logSing γ)) φ
  exact (measurable_distOn_apply φ).add measurable_const

theorem restrictTo_addLogSing (γ : ℝ) (g : DistC) :
    restrictTo (ballO (0 : ℂ) 1) (addLogSing γ g) =
      addRestrictedLogSing γ (restrictTo (ballO (0 : ℂ) 1) g) := by
  refine DFunLike.ext _ _ fun φ => ?_
  rfl

section Bundle

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The IG period `2πχ` is positive. -/
theorem igPeriod_pos (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    0 < 2 * Real.pi * igChi γ := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  exact period_pos_of_uniform D.igField.2.1

/-- The phase `U` is almost everywhere measurable. -/
theorem aemeasurable_phase (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    AEMeasurable U P := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  exact MoTPort.WPGFFMod.aemeasurable_of_map_eq_unif (igPeriod_pos D) D.igField.2.1

theorem aemeasurable_igObs (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    AEMeasurable (igObs hIG₀ U ηL) P :=
  (D.igField.1.1.measurable.aemeasurable.prodMk (aemeasurable_phase D)).prodMk
    D.measurable_curves.1.aemeasurable

/-- `X₀ − (X₀)_1(0)` is a normalized whole-plane GFF (as CANON's `normalizedWPGFF_of_coupling`). -/
theorem isNormalizedWPGFF_normalizedWP
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    IsNormalizedWPGFF (fun ω => normalizedWP (X₀ ω)) P := by
  have hc : Measurable fun ω => -circleAvg (X₀ ω) 1 0 :=
    ((measurable_circleAvg_left 1 0).comp D.gff₀.measurable).neg
  refine ⟨D.gff₀.addConst hc, ?_⟩
  filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero D.gff₀] with ω hω
  change circleAvg (addConst (X₀ ω) (-circleAvg (X₀ ω) 1 0)) 1 0 = 0
  rw [hω, add_neg_cancel]

/-- The IG observation is a.s. a measurable function of the IG field and phase. -/
theorem exists_igObs_factor (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∃ G : DistC × ℝ → (DistC × ℝ) × C(ℝ, ℂ), Measurable G ∧
      igObs hIG₀ U ηL =ᵐ[P] fun ω => G (hIG₀ ω, U ω) := by
  obtain ⟨Φ, hΦ, hroot, -⟩ := igMapPos_of_igMapPositiveRadii (IGLaw.IsMatingOfTreesCoupling.igMapPositiveRadii D)
  refine ⟨fun p => (p, Φ (posIn (igCircleAvgInput p))),
    measurable_id.prodMk (hΦ.comp (measurable_posIn.comp measurable_igCircleAvgInput)), ?_⟩
  filter_upwards [hroot] with ω hω
  show ((hIG₀ ω, U ω), ηL ω) = ((hIG₀ ω, U ω), Φ (posIn (igCircleAvgInput (hIG₀ ω, U ω))))
  rw [hω]
  rfl

/-- **Case 4 law of the full IG observation** (frozen bundle v4, fixed root). -/
theorem map_igTransform_igObs
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    [Fact (0 < 2 * Real.pi * igChi γ)] (z₀ : ℂ) :
    P.map (fun ω => igTransform (2 * Real.pi * igChi γ) z₀ (igObs hIG₀ U ηL ω)) =
      P.map (igObs hIG₀ U ηL) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨Φ, hΦ, hroot, hcc⟩ := igMapPos_of_igMapPositiveRadii (IGLaw.IsMatingOfTreesCoupling.igMapPositiveRadii D)
  have htr : ∀ᵐ ω ∂P, Tendsto (ηL ω) (cocompact ℝ) (cocompact ℂ) := by
    filter_upwards [D.spaceFilling] with ω hω
    exact hω.2.1
  exact map_igTransform_of_ccPos D.igField.1 rfl D.igField.2.1 D.igField.2.2 hΦ hroot hcc htr z₀

/-- The IG observation is independent of the cone tuple `(X, B, B', X₀, B₀, B₀')`. -/
theorem indepFun_coneTuple_igObs
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    IndepFun (coneTuple X X₀ B B' B₀ B₀') (igObs hIG₀ U ηL) P := by
  obtain ⟨G, hG, hfac⟩ := exists_igObs_factor D
  have h1 : IndepFun (coneTuple X X₀ B B' B₀ B₀') (fun ω => (hIG₀ ω, U ω)) P :=
    D.indep_curve.symm
  exact (h1.comp measurable_id hG).congr (ae_eq_refl _) hfac.symm

/-- The normalized whole-plane GFF `X₀ − (X₀)_1(0)` is independent of the IG observation. -/
theorem indepFun_normalizedWP_igObs
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    IndepFun (fun ω => normalizedWP (X₀ ω)) (igObs hIG₀ U ηL) P := by
  have hN : Measurable normalizedWP :=
    DFGPS.L219.measurable_addConst_of measurable_id (measurable_circleAvg_left 1 0).neg
  let pr : Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) × Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → DistC :=
    fun q => normalizedWP q.2.2.2.1
  have hpr : Measurable pr :=
    hN.comp (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  exact (indepFun_coneTuple_igObs D).comp hpr measurable_id

/-- **The γ-cone field is independent of the IG observation** (IGCO's
`indepFun_coneField_ηL`, with the IG field and phase retained). -/
theorem indepFun_coneField_igObs
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    IndepFun (fun ω => coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)))
      (igObs hIG₀ U ηL) P := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨Bc, hBcm, hBc⟩ := ConeScaling.exists_continuousMap_version D.bm_B
  obtain ⟨Bc', hBc'm, hBc'⟩ := ConeScaling.exists_continuousMap_version D.bm_B'
  let coneXBB : Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) × Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) →
      Field × ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) := fun q => (q.1, (q.2.1, q.2.2.1))
  have hconeXBB : Measurable coneXBB :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  have hηXBB : IndepFun (igObs hIG₀ U ηL)
      (fun ω => (X ω, ((fun t => B t ω), (fun t => B' t ω)))) P :=
    ((indepFun_coneTuple_igObs D).comp hconeXBB measurable_id).symm
  have hpath : (fun ω => (X ω, ((fun t => B t ω), (fun t => B' t ω)))) =ᵐ[P]
      fun ω => (X ω, ((⇑(Bc ω) : ℝ≥0 → ℝ), (⇑(Bc' ω) : ℝ≥0 → ℝ))) := by
    filter_upwards [hBc, hBc'] with ω h1 h2
    congr 1
    ext t
    · exact (h1 t).symm
    · exact (h2 t).symm
  have hηXBc : IndepFun (igObs hIG₀ U ηL) (fun ω => (X ω, (Bc ω, Bc' ω))) P :=
    indepFun_triple_continuousMap_of_coe (hηXBB.congr (ae_eq_refl _) hpath)
  let W : Ω → C(ℝ, ℝ) := fun ω => ConeScaling.radMap γ γ (Bc ω, Bc' ω)
  have hηXW : IndepFun (igObs hIG₀ U ηL) (fun ω => (X ω, W ω)) P :=
    hηXBc.comp measurable_id (measurable_fst.prodMk
      ((ConeScaling.measurable_radMap γ γ).comp measurable_snd))
  have hW : ∀ᵐ ω ∂P, ∀ t,
      W ω t = CellScaling.coneRadial γ γ (fun s => B s ω) (fun s => B' s ω) t := by
    filter_upwards [hBc, hBc', D.bm_B.eval_zero_ae_eq_zero, D.bm_B'.eval_zero_ae_eq_zero,
      CellScaling.ae_goodDrift D.bm_B' (CellScaling.lqgQ_sub_pos hγ.1 hγ.2)] with ω h1 h2 h3 h4 hdrift t
    have e1 : (⇑(Bc ω) : ℝ≥0 → ℝ) = fun s => B s ω := funext h1
    have e2 : (⇑(Bc' ω) : ℝ≥0 → ℝ) = fun s => B' s ω := funext h2
    have hmem : (Bc ω, Bc' ω) ∈ ConeScaling.radGood γ γ := by
      refine ⟨?_, ?_, ?_⟩
      · rw [h1]; exact h3
      · rw [h2]; exact h4
      · show BddAbove {s : ℝ | 0 ≤ s ∧ CellScaling.coneDrift γ γ (⇑(Bc' ω)) s = 0}
        rw [e2]; exact hdrift.bddAbove_zeroSet
    show ConeScaling.radMap γ γ (Bc ω, Bc' ω) t = _
    rw [ConeScaling.radMap_apply, ite_eq_left hmem]
    simp only [e1, e2]
  have hF : Measurable fun p : Field × C(ℝ, ℝ) =>
      ConeScaling.fieldOf (CellScaling.lateralPart p.1) p.2 :=
    ConeScaling.measurable_fieldOf.comp
      ((ConeScaling.measurable_lateralPart.comp measurable_fst).prodMk measurable_snd)
  have hind : IndepFun (fun ω => ConeScaling.fieldOf (CellScaling.lateralPart (X ω)) (W ω))
      (igObs hIG₀ U ηL) P :=
    (hηXW.comp measurable_id hF).symm
  refine hind.congr ?_ (ae_eq_refl _)
  filter_upwards [hW] with ω hω
  rw [MesoModel.FrozenIdentities.coneField_eq_cellScaling, MesoModel.FrozenIdentities.coneRadial_eq_cellScaling]
  exact (ConeScaling.coneFieldOf_eq_fieldOf γ (X ω) hω).symm

/-- The γ-cone field is almost everywhere measurable (through IGCO's measurable radial path). -/
theorem aemeasurable_coneField
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    AEMeasurable (fun ω => coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))) P := by
  obtain ⟨Bc, hBcm, hBc⟩ := ConeScaling.exists_continuousMap_version D.bm_B
  obtain ⟨Bc', hBc'm, hBc'⟩ := ConeScaling.exists_continuousMap_version D.bm_B'
  let W : Ω → C(ℝ, ℝ) := fun ω => ConeScaling.radMap γ γ (Bc ω, Bc' ω)
  have hWm : Measurable W := (ConeScaling.measurable_radMap γ γ).comp (hBcm.prodMk hBc'm)
  have hW : ∀ᵐ ω ∂P, ∀ t,
      W ω t = CellScaling.coneRadial γ γ (fun s => B s ω) (fun s => B' s ω) t := by
    filter_upwards [hBc, hBc', D.bm_B.eval_zero_ae_eq_zero, D.bm_B'.eval_zero_ae_eq_zero,
      CellScaling.ae_goodDrift D.bm_B' (CellScaling.lqgQ_sub_pos hγ.1 hγ.2)] with ω h1 h2 h3 h4 hdrift t
    have e1 : (⇑(Bc ω) : ℝ≥0 → ℝ) = fun s => B s ω := funext h1
    have e2 : (⇑(Bc' ω) : ℝ≥0 → ℝ) = fun s => B' s ω := funext h2
    have hmem : (Bc ω, Bc' ω) ∈ ConeScaling.radGood γ γ := by
      refine ⟨?_, ?_, ?_⟩
      · rw [h1]; exact h3
      · rw [h2]; exact h4
      · show BddAbove {s : ℝ | 0 ≤ s ∧ CellScaling.coneDrift γ γ (⇑(Bc' ω)) s = 0}
        rw [e2]; exact hdrift.bddAbove_zeroSet
    show ConeScaling.radMap γ γ (Bc ω, Bc' ω) t = _
    rw [ConeScaling.radMap_apply, ite_eq_left hmem]
    simp only [e1, e2]
  have hF : Measurable fun ω => ConeScaling.fieldOf (CellScaling.lateralPart (X ω)) (W ω) :=
    ConeScaling.measurable_fieldOf.comp
      ((ConeScaling.measurable_lateralPart.comp D.gff.measurable).prodMk hWm)
  refine hF.aemeasurable.congr ?_
  filter_upwards [hW] with ω hω
  rw [MesoModel.FrozenIdentities.coneField_eq_cellScaling, MesoModel.FrozenIdentities.coneRadial_eq_cellScaling]
  exact (ConeScaling.coneFieldOf_eq_fieldOf γ (X ω) hω).symm

/-- **Case 4 ↔ γ-cone at a fixed root** (full IG data): the law of
`(case4Field|_𝔻, igTransform r z₀ igObs)` is the law of `(cone field|_𝔻, igObs)`. -/
theorem map_case4Local_eq_cone
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) [Fact (0 < 2 * Real.pi * igChi γ)] (z₀ : ℂ) :
    P.map (fun ω => (restrictTo (ballO (0 : ℂ) 1) (case4Field γ (normalizedWP (X₀ ω)) z₀),
        igTransform (2 * Real.pi * igChi γ) z₀ (igObs hIG₀ U ηL ω))) =
      P.map (fun ω => (restrictTo (ballO (0 : ℂ) 1)
        (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))), igObs hIG₀ U ηL ω)) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  set r := 2 * Real.pi * igChi γ
  set h : Ω → DistC := fun ω => normalizedWP (X₀ ω) with hdef
  have hh : IsNormalizedWPGFF h P := isNormalizedWPGFF_normalizedWP D
  set Y := igObs hIG₀ U ηL with hYdef
  have hYa : AEMeasurable Y P := aemeasurable_igObs D
  set Y' := hYa.mk Y with hY'def
  have hY'm : Measurable Y' := hYa.measurable_mk
  have hYY' : Y =ᵐ[P] Y' := hYa.ae_eq_mk
  have hτ : Measurable fun q : ℂ × ((DistC × ℝ) × C(ℝ, ℂ)) => igTransform r q.1 q.2 :=
    measurable_igTransform r
  have hind' : IndepFun h Y' P := (indepFun_normalizedWP_igObs D).congr (ae_eq_refl _) hYY'
  have hlaw' : P.map (fun ω => igTransform r z₀ (Y' ω)) = P.map Y' := by
    have e1 : P.map (fun ω => igTransform r z₀ (Y' ω)) = P.map (fun ω => igTransform r z₀ (Y ω)) :=
      Measure.map_congr (by filter_upwards [hYY'] with ω hω; rw [hω])
    rw [e1, map_igTransform_igObs D z₀, Measure.map_congr hYY']
  have hpair := map_case4_pair hh hY'm hτ hind' z₀ hlaw'
  set F : DistC → DistOn (ballO (0 : ℂ) 1) := fun g => restrictTo (ballO (0 : ℂ) 1) (addLogSing γ g)
    with hFdef
  have hFm : Measurable F := (measurable_restrictTo _).comp (measurable_addLogSing γ)
  have hpm : Measurable fun ω => (case4Normalized (h ω) z₀, igTransform r z₀ (Y' ω)) :=
    ((measurable_case4Normalized_left z₀).comp hh.1.measurable).prodMk
      ((measurable_transform_right hτ z₀).comp hY'm)
  -- left side
  have hL : P.map (fun ω => (restrictTo (ballO (0 : ℂ) 1) (case4Field γ (normalizedWP (X₀ ω)) z₀),
      igTransform r z₀ (Y ω))) = ((P.map h).map F).prod (P.map Y') := by
    have e1 : P.map (fun ω => (restrictTo (ballO (0 : ℂ) 1) (case4Field γ (normalizedWP (X₀ ω)) z₀),
        igTransform r z₀ (Y ω))) =
        P.map (Prod.map F id ∘ fun ω => (case4Normalized (h ω) z₀, igTransform r z₀ (Y' ω))) :=
      Measure.map_congr (by filter_upwards [hYY'] with ω hω; rw [hω]; rfl)
    rw [e1, ← Measure.map_map (hFm.prodMap measurable_id) hpm, hpair,
      ← Measure.map_prod_map _ _ hFm measurable_id, Measure.map_id]
  -- right side
  have hcm := aemeasurable_coneField D hγ
  have hcmR : AEMeasurable (fun ω => restrictTo (ballO (0 : ℂ) 1)
      (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)))) P :=
    (measurable_restrictTo _).comp_aemeasurable hcm
  have hcone := indepFun_coneField_igObs D hγ
  have hconeR : IndepFun (fun ω => restrictTo (ballO (0 : ℂ) 1)
      (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)))) Y P :=
    hcone.comp (measurable_restrictTo _) measurable_id
  have hR : P.map (fun ω => (restrictTo (ballO (0 : ℂ) 1)
      (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))), Y ω)) =
      ((P.map h).map F).prod (P.map Y') := by
    rw [hconeR.map_prod_eq_prod_map_map hcmR hYa,
      map_restrict_coneField hγ D.gff D.bm_B D.bm_B' D.indep_cone hh, Measure.map_congr hYY']
    congr 1
    rw [Measure.map_map hFm hh.1.measurable]
    rfl
  rw [hL, hR]

/-- **Cases 2–4 with an independent root** (full IG data): under `P ⊗ λ`, the root and the Case 3
index are independent of the Case 4 local data, whose law is the γ-cone's. -/
theorem map_case3_marked_cone
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) [Fact (0 < 2 * Real.pi * igChi γ)]
    (lam : Measure ℂ) [IsProbabilityMeasure lam]
    (hsupp : ∀ᵐ z₀ ∂lam, closedBall z₀ (1 / 2) ⊆ closedBall (0 : ℂ) 1) :
    (P.prod lam).map (fun p : Ω × ℂ =>
        ((p.2, halfAvg (normalizedWP (X₀ p.1)) p.2),
          (restrictTo (ballO (0 : ℂ) 1) (case4Field γ (normalizedWP (X₀ p.1)) p.2),
            igTransform (2 * Real.pi * igChi γ) p.2 (igObs hIG₀ U ηL p.1)))) =
      ((P.prod lam).map fun p : Ω × ℂ => (p.2, halfAvg (normalizedWP (X₀ p.1)) p.2)).prod
        (P.map fun ω => (restrictTo (ballO (0 : ℂ) 1)
          (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))), igObs hIG₀ U ηL ω)) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  set r := 2 * Real.pi * igChi γ
  set h : Ω → DistC := fun ω => normalizedWP (X₀ ω) with hdef
  have hh : IsNormalizedWPGFF h P := isNormalizedWPGFF_normalizedWP D
  set Y := igObs hIG₀ U ηL with hYdef
  have hYa : AEMeasurable Y P := aemeasurable_igObs D
  set Y' := hYa.mk Y with hY'def
  have hY'm : Measurable Y' := hYa.measurable_mk
  have hYY' : Y =ᵐ[P] Y' := hYa.ae_eq_mk
  have hτ : Measurable fun q : ℂ × ((DistC × ℝ) × C(ℝ, ℂ)) => igTransform r q.1 q.2 :=
    measurable_igTransform r
  have hind' : IndepFun h Y' P := (indepFun_normalizedWP_igObs D).congr (ae_eq_refl _) hYY'
  have hlaw' : ∀ z₀ : ℂ, P.map (fun ω => igTransform r z₀ (Y' ω)) = P.map Y' := by
    intro z₀
    have e1 : P.map (fun ω => igTransform r z₀ (Y' ω)) = P.map (fun ω => igTransform r z₀ (Y ω)) :=
      Measure.map_congr (by filter_upwards [hYY'] with ω hω; rw [hω])
    rw [e1, map_igTransform_igObs D z₀, Measure.map_congr hYY']
  have H := map_case3_marked hh hY'm hτ hind' hlaw' lam hsupp
  -- add the restricted singularity on the second factor
  set G : DistOn (ballO (0 : ℂ) 1) × ((DistC × ℝ) × C(ℝ, ℂ)) →
      DistOn (ballO (0 : ℂ) 1) × ((DistC × ℝ) × C(ℝ, ℂ)) :=
    Prod.map (addRestrictedLogSing γ) id with hGdef
  have hGm : Measurable G := (measurable_addRestrictedLogSing γ).prodMap measurable_id
  have hYfst : (fun p : Ω × ℂ => Y p.1) =ᵐ[P.prod lam] fun p => Y' p.1 :=
    Measure.quasiMeasurePreserving_fst.ae_eq_comp hYY'
  have hAm : Measurable fun p : Ω × ℂ => (p.2, halfAvg (h p.1) p.2) :=
    measurable_snd.prodMk (measurable_halfAvg_marked hh.1.measurable)
  have hLm : Measurable fun p : Ω × ℂ =>
      (restrictTo (ballO (0 : ℂ) 1) (case4Normalized (h p.1) p.2), igTransform r p.2 (Y' p.1)) :=
    ((measurable_restrictTo _).comp (measurable_case4Normalized_marked hh.1.measurable)).prodMk
      (measurable_transform_marked hτ hY'm)
  have e1 : (P.prod lam).map (fun p : Ω × ℂ =>
      ((p.2, halfAvg (normalizedWP (X₀ p.1)) p.2),
        (restrictTo (ballO (0 : ℂ) 1) (case4Field γ (normalizedWP (X₀ p.1)) p.2),
          igTransform r p.2 (Y p.1)))) =
      ((P.prod lam).map (fun p : Ω × ℂ => ((p.2, halfAvg (h p.1) p.2),
        (restrictTo (ballO (0 : ℂ) 1) (case4Normalized (h p.1) p.2),
          igTransform r p.2 (Y' p.1))))).map (Prod.map id G) := by
    rw [Measure.map_map (measurable_id.prodMap hGm) (hAm.prodMk hLm)]
    refine Measure.map_congr ?_
    filter_upwards [hYfst] with p hp
    simp only [Function.comp_apply, Prod.map_apply, id_eq, hGdef]
    rw [hp]
    rfl
  rw [e1, H, ← Measure.map_prod_map _ _ measurable_id hGm, Measure.map_id]
  congr 1
  -- the second factor is the cone's local law
  have hpm : Measurable fun ω => (restrictTo (ballO (0 : ℂ) 1) (h ω), Y' ω) :=
    ((measurable_restrictTo _).comp hh.1.measurable).prodMk hY'm
  set F : DistC → DistOn (ballO (0 : ℂ) 1) := fun g => restrictTo (ballO (0 : ℂ) 1) (addLogSing γ g)
    with hFdef
  have hFm : Measurable F := (measurable_restrictTo _).comp (measurable_addLogSing γ)
  have e2 : (P.map fun ω => (restrictTo (ballO (0 : ℂ) 1) (h ω), Y' ω)).map G =
      ((P.map h).map F).prod (P.map Y') := by
    rw [Measure.map_map hGm hpm]
    have e3 : (G ∘ fun ω => (restrictTo (ballO (0 : ℂ) 1) (h ω), Y' ω)) =
        fun ω => (F (h ω), Y' ω) := by
      funext ω
      simp only [Function.comp_apply, hGdef, Prod.map_apply, id_eq, hFdef]
      rw [restrictTo_addLogSing]
    have hFhm : Measurable fun ω => F (h ω) := hFm.comp hh.1.measurable
    have hindF : IndepFun (fun ω => F (h ω)) Y' P := hind'.comp hFm measurable_id
    rw [e3, hindF.map_prod_eq_prod_map_map hFhm.aemeasurable hY'm.aemeasurable,
      Measure.map_map hFm hh.1.measurable]
    rfl
  rw [e2]
  have hcm := aemeasurable_coneField D hγ
  have hcmR : AEMeasurable (fun ω => restrictTo (ballO (0 : ℂ) 1)
      (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)))) P :=
    (measurable_restrictTo _).comp_aemeasurable hcm
  have hconeR : IndepFun (fun ω => restrictTo (ballO (0 : ℂ) 1)
      (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)))) Y P :=
    (indepFun_coneField_igObs D hγ).comp (measurable_restrictTo _) measurable_id
  rw [hconeR.map_prod_eq_prod_map_map hcmR hYa,
    map_restrict_coneField hγ D.gff D.bm_B D.bm_B' D.indep_cone hh, Measure.map_congr hYY']
  congr 1
  rw [Measure.map_map hFm hh.1.measurable]
  rfl

end Bundle

end MatedCRTHarmonic.GMSCase
