import MatedCRTHarmonic.GMSCase.Translate
import MatedCRTHarmonic.LQGCoord.Transform
import MatedCRTHarmonic.CellScaling.JointScalingOClock
import MatedCRTHarmonic.GMSCase.Defs
import MatedCRTHarmonic.GMS4b.Window
import MatedCRTHarmonic.Frozen.MatedCRTAffineReroot
import MatedCRTHarmonic.GMSCase.ConeLaw
import MatedCRTHarmonic.ConeScaling.FieldDecomp
import MatedCRTHarmonic.GMSCase.Bundle
import MatedCRTHarmonic.GMSCase1.Case2Local
import MatedCRTHarmonic.GMSCase1.Representations

/-!
# [18] Proposition 4.10, Cases 3–4 on the whole-plane data `WPData` (route (c))

Source: (`[18]:N`), Proposition 4.10, Cases 3–4 and the final
paragraph, `[18]`; the Cases 1–2 on `WPData` (`GMSCase1/*`); the IG
data `((hIG₀, U), ηL)` are kept in full).

**Route (c) (repair of the Case 3 random-mesh gap).** [18] passes from the Case 2 field
`h² = h₀ − γ log|· − z|` to the γ-cone by renormalizing (`h³ = h² − h²_{1/2}(z)`) and dilating
(`h⁴ = h³(·/2 + z)`); the dilation changes the mesh by the random factor `e^{γ h²_{1/2}(z)}`, and
Case 2's fixed-mesh bounds do not control the resulting random-mesh events. Here no renormalization
and no dilation are used: for every root `z` with `‖z‖ + r ≤ 1` the translated Case 2 field
`h²(· + z) = h₀(· + z) − γ log|·|` restricted to `B_r(0)`, jointly with the IG data re-rooted at `z`
(`igTransformS (2πχ) 1 z`, curve `affineReroot z 1 0 ηL = ηL(τ_z + ·) − z`), has the law of the
γ-cone field restricted to `B_r(0)` jointly with the IG data. Thus the cone's events at mesh `ε`
are the Case 2 field's events at the **same** mesh `ε` for the translated test pair `(D + z, f(· − z))`.

Main results (namespace `MatedCRTHarmonic.GMSCase`; all on the frozen coupling `D`):

* `map_shiftedCase2_eq_cone` — fixed root `z`, `‖z‖ + r ≤ 1`;
* `map_shiftedCase2_marked_eq_cone` — independent random root `z ∼ lam`, `‖z‖ + r ≤ 1` a.s.;
* **`smallRoot_shiftedCase2_eq_cone`** — the conditional rooted law given `{z ∈ B_{ρ₀}(0)}`,
  `ρ₀ + r ≤ 1`, events of the `case2WPData` re-rooted at the marked root (`rerootData`);
* **`cone_event_le_of_case2`** — the chain to the Case 2 bound: a cone event of
  `(cone|_{B_r(0)}, wpAux)` whose re-rooted Case 2 version is contained (on the small-root event) in a
  fixed local Case 2 event has probability `≤ case1Moment^{1/p} δ^{1/q} / ρ₀²`.

Helpers: `shiftedCase2Field`, `rerootData`, `affineComp_one_ofFunC` (translation of a function
distribution), `affineComp_one_case2_eq`, `ae_rerootData_case2_eq`, `map_igTransformS_igObs`,
`map_restrict_ball_coneField`. The deterministic translation covariance of the area parametrization
and of `u_*^ε` at the same mesh is `GMSCase/AreaTranslate.lean` (imported here, so this module is the
single entry point of the Case 3–4 results).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace Filter
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSCase

open LQGMetric LQGMetric.Blueprint MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.IGLaw
open MatedCRTHarmonic.GMSCase1 (WPData AuxData wpField wpAux wpData case2WPData restrictData)

/-! ## Translation of function distributions -/

theorem locallyIntegrable_comp_add_right {f : ℂ → ℝ} (hf : LocallyIntegrable f volume) (z : ℂ) :
    LocallyIntegrable (fun w => f (w + z)) volume := by
  rw [locallyIntegrable_iff] at hf ⊢
  intro K hK
  set K' : Set ℂ := (fun w : ℂ => w + z) '' K
  have hK' : IsCompact K' := hK.image (continuous_id.add continuous_const)
  have h1 : Integrable (K'.indicator f) volume :=
    (integrable_indicator_iff hK'.measurableSet).2 (hf K' hK')
  have h2 : Integrable (fun w => K'.indicator f (w + z)) volume := h1.comp_add_right z
  have hpre : MeasurableSet ((fun w : ℂ => w + z) ⁻¹' K') :=
    hK'.isClosed.measurableSet.preimage (continuous_id.add continuous_const).measurable
  have h3 : IntegrableOn (fun w => f (w + z)) ((fun w : ℂ => w + z) ⁻¹' K') volume := by
    rw [← integrable_indicator_iff hpre]
    have e : ((fun w : ℂ => w + z) ⁻¹' K').indicator (fun w => f (w + z)) =
        fun w => K'.indicator f (w + z) := by
      funext w
      by_cases hw : w + z ∈ K'
      · rw [indicator_of_mem (show w ∈ (fun w : ℂ => w + z) ⁻¹' K' from hw),
          indicator_of_mem hw]
      · rw [indicator_of_notMem (show w ∉ (fun w : ℂ => w + z) ⁻¹' K' from hw),
          indicator_of_notMem hw]
    rw [e]
    exact h2
  exact h3.mono_set (subset_preimage_image _ _)

theorem ofFunC_apply_of_locallyIntegrable {f : ℂ → ℝ} (hf : LocallyIntegrable f volume)
    (φ : TestC) : MoTPort.ofFunC f φ = ∫ x, φ x * f x := by
  rw [MoTPort.ofFunC, Distribution.ofFun_apply (hf.locallyIntegrableOn _)]
  rfl

/-- **Translation of a function distribution**: `(ofFunC f)(· + z) = ofFunC (f(· + z))`. -/
theorem affineComp_one_ofFunC {f : ℂ → ℝ} (hf : LocallyIntegrable f volume) (z : ℂ) :
    affineComp 1 z (MoTPort.ofFunC f) = MoTPort.ofFunC (fun w => f (w + z)) := by
  refine DFunLike.ext _ _ fun φ => ?_
  rw [GFFInv.affineComp_apply, ofFunC_apply_of_locallyIntegrable hf,
    ofFunC_apply_of_locallyIntegrable (locallyIntegrable_comp_add_right hf z), one_pow, inv_one,
    one_mul, ← integral_add_right_eq_self (fun x => testAffinePull 1 z φ x * f x) z]
  congr 1
  funext v
  rw [testAffinePull_apply _ _ one_ne_zero, add_sub_cancel_right, Complex.ofReal_one, div_one]

/-! ## The re-rooted Case 2 data -/

/-- The Case 2 field `h − γ log|· − z|` translated to its root: `h(· + z) − γ log|·|`. -/
def shiftedCase2Field (γ : ℝ) (h : DistC) (z : ℂ) : DistC := addLogSing γ (affineComp 1 z h)

/-- **Re-rooting whole-plane data at `z`**: field `x(· + z)`; IG data `igTransformS (2πχ) 1 z`
(field `hIG₀(· + z) − (hIG₀)_1(z)`, phase `U + (hIG₀)_1(z)` mod `2πχ`, curve
`affineReroot z 1 0 ηL = ηL(τ_z + ·) − z`). -/
def rerootData (γ : ℝ) [Fact (0 < 2 * Real.pi * igChi γ)] (z : ℂ) (x : WPData) : WPData :=
  (affineComp 1 z x.1, igTransformS (2 * Real.pi * igChi γ) 1 z x.2)

theorem measurable_shiftedCase2Field (γ : ℝ) :
    Measurable fun p : DistC × ℂ => shiftedCase2Field γ p.1 p.2 :=
  (measurable_addLogSing γ).comp (measurable_affineComp_center 1)

theorem measurable_rerootData (γ : ℝ) [Fact (0 < 2 * Real.pi * igChi γ)] :
    Measurable fun p : ℂ × WPData => rerootData γ p.1 p.2 := by
  have h1 : Measurable fun p : ℂ × WPData => ((p.2.1, p.1) : DistC × ℂ) :=
    (measurable_fst.comp measurable_snd).prodMk measurable_fst
  have e1 : Measurable ((fun q : DistC × ℂ => affineComp 1 q.2 q.1) ∘
      fun p : ℂ × WPData => ((p.2.1, p.1) : DistC × ℂ)) := (measurable_affineComp_center 1).comp h1
  have h2 : Measurable fun p : ℂ × WPData => ((p.1, p.2.2) : ℂ × AuxData) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  have e2 : Measurable ((fun q : ℂ × AuxData => igTransformS (2 * Real.pi * igChi γ) 1 q.1 q.2) ∘
      fun p : ℂ × WPData => ((p.1, p.2.2) : ℂ × AuxData)) :=
    (measurable_igTransformS (2 * Real.pi * igChi γ) 1).comp h2
  exact e1.prodMk e2

theorem restrictTo_addLogSing_on (V : Opens ℂ) (γ : ℝ) (g : DistC) :
    restrictTo V (addLogSing γ g) = restrictTo V g + restrictTo V (MoTPort.ofFunC (logSing γ)) := by
  refine DFunLike.ext _ _ fun φ => ?_
  rfl

/-- `(h − γ log|· − z|)(· + z) = h(· + z) − γ log|·|`. -/
theorem affineComp_one_case2_eq (γ : ℝ) (h : DistC) (z : ℂ) :
    affineComp 1 z (h + CellScaling.ofFunC (fun w => -γ * Real.log ‖w - z‖)) =
      shiftedCase2Field γ h z := by
  have hli : LocallyIntegrable (fun w : ℂ => -γ * Real.log ‖w - z‖) volume := by
    refine (locallyIntegrable_comp_add_right (locallyIntegrable_logSing γ) (-z)).congr
      (Eventually.of_forall fun w => ?_)
    simp only [logSing, ← sub_eq_add_neg]
    ring
  have e : CellScaling.ofFunC (fun w => -γ * Real.log ‖w - z‖) =
      MoTPort.ofFunC (fun w => -γ * Real.log ‖w - z‖) := rfl
  rw [GM.affineComp_add, shiftedCase2Field, addLogSing, e, affineComp_one_ofFunC hli z]
  congr 2
  funext w
  simp only [logSing, add_sub_cancel_right]
  ring

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The re-rooted Case 2 data have field `shiftedCase2Field` almost surely (the
`ae_case2Field_eq`). -/
theorem ae_rerootData_case2_eq
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    [Fact (0 < 2 * Real.pi * igChi γ)] :
    ∀ᵐ v ∂Canon.rootedLaw P, rerootData γ v.2 (case2WPData γ X₀ hIG₀ U ηL v) =
      (shiftedCase2Field γ (wpField X₀ v.1) v.2,
        igTransformS (2 * Real.pi * igChi γ) 1 v.2 (wpAux hIG₀ U ηL v.1)) := by
  filter_upwards [GMSCase1.ae_case2Field_eq D] with v hv
  show (affineComp 1 v.2 (Canon.case2Field γ (wpField X₀ v.1) v.2),
      igTransformS (2 * Real.pi * igChi γ) 1 v.2 (wpAux hIG₀ U ηL v.1)) = _
  rw [hv, affineComp_one_case2_eq]

/-- The general-scale IG transformation preserves the law of the full IG observation. -/
theorem map_igTransformS_igObs
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    [Fact (0 < 2 * Real.pi * igChi γ)] {s : ℝ} (hs : 0 < s) (z₀ : ℂ) :
    P.map (fun ω => igTransformS (2 * Real.pi * igChi γ) s z₀ (igObs hIG₀ U ηL ω)) =
      P.map (igObs hIG₀ U ηL) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨Φ, hΦ, hroot, hcc⟩ :=
    igMapPos_of_igMapPositiveRadii (IGLaw.IsMatingOfTreesCoupling.igMapPositiveRadii D)
  have htr : ∀ᵐ ω ∂P, Tendsto (ηL ω) (cocompact ℝ) (cocompact ℂ) := by
    filter_upwards [D.spaceFilling] with ω hω
    exact hω.2.1
  exact map_igTransformS_of_ccPos D.igField.1 rfl D.igField.2.1 D.igField.2.2 hΦ hroot hcc htr hs z₀

/-- **The γ-cone on `B_r(0)` with the IG data** has the law of `(h₀ − γ log|·|)|_{B_r(0)}` with
The IG data, `h₀ = wpField X₀` (`0 < r ≤ 1`). -/
theorem map_restrict_ball_coneField
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {r : ℝ} (hr1 : r ≤ 1) :
    P.map (fun ω => (restrictTo (ballO (0 : ℂ) r)
        (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))), wpAux hIG₀ U ηL ω)) =
      P.map (fun ω => (restrictTo (ballO (0 : ℂ) r) (addLogSing γ (wpField X₀ ω)),
        wpAux hIG₀ U ηL ω)) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hh : IsNormalizedWPGFF (wpField X₀) P := GMSCase1.isNormalizedWPGFF_wpField D
  have hYa : AEMeasurable (wpAux hIG₀ U ηL) P := aemeasurable_igObs D
  have hle : ballO (0 : ℂ) r ≤ ballO (0 : ℂ) 1 := ballO_le_ballO hr1 0
  have hcm := aemeasurable_coneField D hγ
  have hcmD : AEMeasurable (fun ω => restrictTo (ballO (0 : ℂ) 1)
      (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)))) P :=
    (measurable_restrictTo _).comp_aemeasurable hcm
  have hcmR : AEMeasurable (fun ω => restrictTo (ballO (0 : ℂ) r)
      (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)))) P :=
    (measurable_restrictTo _).comp_aemeasurable hcm
  have hconeR : IndepFun (fun ω => restrictTo (ballO (0 : ℂ) r)
      (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))))
      (wpAux hIG₀ U ηL) P :=
    (indepFun_coneField_igObs D hγ).comp (measurable_restrictTo _) measurable_id
  have hFm : Measurable fun g : DistC => restrictTo (ballO (0 : ℂ) r) (addLogSing γ g) :=
    (measurable_restrictTo _).comp (measurable_addLogSing γ)
  have hFhm : Measurable fun ω => restrictTo (ballO (0 : ℂ) r) (addLogSing γ (wpField X₀ ω)) :=
    hFm.comp hh.1.measurable
  have hfieldR : IndepFun (fun ω => restrictTo (ballO (0 : ℂ) r) (addLogSing γ (wpField X₀ ω)))
      (wpAux hIG₀ U ηL) P :=
    (GMSCase1.indepFun_wpField_wpAux D).comp hFm measurable_id
  rw [hconeR.map_prod_eq_prod_map_map hcmR hYa, hfieldR.map_prod_eq_prod_map_map hFhm.aemeasurable hYa]
  congr 1
  -- the cone's law on `B_r(0)` from its law on `𝔻`
  have eC : (fun ω => restrictTo (ballO (0 : ℂ) r)
      (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)))) =
      resSub (ballO (0 : ℂ) r) (ballO (0 : ℂ) 1) ∘ fun ω => restrictTo (ballO (0 : ℂ) 1)
        (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))) :=
    funext fun ω => restrictTo_eq_resSub hle _
  have eF : (fun ω => restrictTo (ballO (0 : ℂ) r) (addLogSing γ (wpField X₀ ω))) =
      resSub (ballO (0 : ℂ) r) (ballO (0 : ℂ) 1) ∘
        fun ω => restrictTo (ballO (0 : ℂ) 1) (addLogSing γ (wpField X₀ ω)) :=
    funext fun ω => restrictTo_eq_resSub hle _
  have hFDm : Measurable fun ω => restrictTo (ballO (0 : ℂ) 1) (addLogSing γ (wpField X₀ ω)) :=
    ((measurable_restrictTo _).comp (measurable_addLogSing γ)).comp hh.1.measurable
  rw [eC, eF, ← AEMeasurable.map_map_of_aemeasurable
      (measurable_resSub _ _).aemeasurable hcmD,
    ← Measure.map_map (measurable_resSub _ _) hFDm,
    map_restrict_coneField hγ D.gff D.bm_B D.bm_B' D.indep_cone hh]

/-- **Cases 3–4, fixed root** (route (c)): for `0 < r` and `‖z‖ + r ≤ 1`, the translated Case 2
field `h₀(· + z) − γ log|·|` on `B_r(0)`, jointly with the IG data re-rooted at `z`, has the law of
The γ-cone field on `B_r(0)` jointly with the IG data. -/
theorem map_shiftedCase2_eq_cone
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) [Fact (0 < 2 * Real.pi * igChi γ)] {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : ‖z‖ + r ≤ 1) :
    P.map (fun ω => (restrictTo (ballO (0 : ℂ) r) (shiftedCase2Field γ (wpField X₀ ω) z),
        igTransformS (2 * Real.pi * igChi γ) 1 z (wpAux hIG₀ U ηL ω))) =
      P.map (fun ω => (restrictTo (ballO (0 : ℂ) r)
        (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))), wpAux hIG₀ U ηL ω)) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hr1 : r ≤ 1 := by linarith [norm_nonneg z]
  rw [map_restrict_ball_coneField D hγ hr1]
  set ρ := 2 * Real.pi * igChi γ with hρ
  set h : Ω → DistC := wpField X₀ with hdef
  have hh : IsNormalizedWPGFF h P := GMSCase1.isNormalizedWPGFF_wpField D
  set Y := wpAux hIG₀ U ηL with hYdef
  have hYa : AEMeasurable Y P := aemeasurable_igObs D
  set Y' := hYa.mk Y with hY'def
  have hY'm : Measurable Y' := hYa.measurable_mk
  have hYY' : Y =ᵐ[P] Y' := hYa.ae_eq_mk
  have hτ : Measurable fun q : ℂ × AuxData => igTransformS ρ 1 q.1 q.2 :=
    measurable_igTransformS ρ 1
  have hind' : IndepFun h Y' P := (GMSCase1.indepFun_wpField_wpAux D).congr (ae_eq_refl _) hYY'
  have hlaw' : P.map (fun ω => igTransformS ρ 1 z (Y' ω)) = P.map Y' := by
    have e1 : P.map (fun ω => igTransformS ρ 1 z (Y' ω)) =
        P.map (fun ω => igTransformS ρ 1 z (Y ω)) :=
      Measure.map_congr (by filter_upwards [hYY'] with ω hω; rw [hω])
    rw [e1]
    exact (map_igTransformS_igObs D one_pos z).trans (Measure.map_congr hYY')
  have hpair := map_restrict_affineComp_one_pair hh hr hY'm hτ hind' hz hlaw'
  set G : DistOn (ballO (0 : ℂ) r) × AuxData → DistOn (ballO (0 : ℂ) r) × AuxData :=
    Prod.map (fun T => T + restrictTo (ballO (0 : ℂ) r) (MoTPort.ofFunC (logSing γ))) id
    with hGdef
  have hGm : Measurable G := by
    refine Measurable.prodMap ?_ measurable_id
    refine measurable_distOn_iff.2 fun φ => ?_
    exact (measurable_distOn_apply φ).add measurable_const
  have hm1 : Measurable fun ω =>
      (restrictTo (ballO (0 : ℂ) r) (affineComp 1 z (h ω)), igTransformS ρ 1 z (Y' ω)) :=
    ((measurable_restrict_affineComp_one r z).comp hh.1.measurable).prodMk
      ((measurable_transform_right hτ z).comp hY'm)
  have hm2 : Measurable fun ω => (restrictTo (ballO (0 : ℂ) r) (h ω), Y' ω) :=
    ((measurable_restrictTo _).comp hh.1.measurable).prodMk hY'm
  calc P.map (fun ω => (restrictTo (ballO (0 : ℂ) r) (shiftedCase2Field γ (h ω) z),
          igTransformS ρ 1 z (Y ω)))
      = P.map (G ∘ fun ω =>
          (restrictTo (ballO (0 : ℂ) r) (affineComp 1 z (h ω)), igTransformS ρ 1 z (Y' ω))) := by
        refine Measure.map_congr ?_
        filter_upwards [hYY'] with ω hω
        simp only [Function.comp_apply, hGdef, Prod.map_apply, id_eq, shiftedCase2Field,
          restrictTo_addLogSing_on, hω]
    _ = P.map (G ∘ fun ω => (restrictTo (ballO (0 : ℂ) r) (h ω), Y' ω)) := by
        rw [← Measure.map_map hGm hm1, hpair, Measure.map_map hGm hm2]
    _ = P.map (fun ω => (restrictTo (ballO (0 : ℂ) r) (addLogSing γ (h ω)), Y ω)) := by
        refine Measure.map_congr ?_
        filter_upwards [hYY'] with ω hω
        simp only [Function.comp_apply, hGdef, Prod.map_apply, id_eq, restrictTo_addLogSing_on, hω]

/-- **Cases 3–4 with an independent random root** `z ∼ lam`, `‖z‖ + r ≤ 1` `lam`-a.s. -/
theorem map_shiftedCase2_marked_eq_cone
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) [Fact (0 < 2 * Real.pi * igChi γ)] {r : ℝ} (hr : 0 < r)
    (lam : Measure ℂ) [IsProbabilityMeasure lam] (hsupp : ∀ᵐ z ∂lam, ‖z‖ + r ≤ 1) :
    (P.prod lam).map (fun v : Ω × ℂ =>
        (restrictTo (ballO (0 : ℂ) r) (shiftedCase2Field γ (wpField X₀ v.1) v.2),
          igTransformS (2 * Real.pi * igChi γ) 1 v.2 (wpAux hIG₀ U ηL v.1))) =
      P.map (fun ω => (restrictTo (ballO (0 : ℂ) r)
        (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))), wpAux hIG₀ U ηL ω)) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hr1 : r ≤ 1 := by
    obtain ⟨z, hz⟩ := hsupp.exists
    linarith [norm_nonneg z]
  rw [map_restrict_ball_coneField D hγ hr1]
  set ρ := 2 * Real.pi * igChi γ with hρ
  set h : Ω → DistC := wpField X₀ with hdef
  have hh : IsNormalizedWPGFF h P := GMSCase1.isNormalizedWPGFF_wpField D
  set Y := wpAux hIG₀ U ηL with hYdef
  have hYa : AEMeasurable Y P := aemeasurable_igObs D
  set Y' := hYa.mk Y with hY'def
  have hY'm : Measurable Y' := hYa.measurable_mk
  have hYY' : Y =ᵐ[P] Y' := hYa.ae_eq_mk
  have hτ : Measurable fun q : ℂ × AuxData => igTransformS ρ 1 q.1 q.2 :=
    measurable_igTransformS ρ 1
  have hind' : IndepFun h Y' P := (GMSCase1.indepFun_wpField_wpAux D).congr (ae_eq_refl _) hYY'
  have hlaw' : ∀ z : ℂ, P.map (fun ω => igTransformS ρ 1 z (Y' ω)) = P.map Y' := by
    intro z
    have e1 : P.map (fun ω => igTransformS ρ 1 z (Y' ω)) =
        P.map (fun ω => igTransformS ρ 1 z (Y ω)) :=
      Measure.map_congr (by filter_upwards [hYY'] with ω hω; rw [hω])
    rw [e1]
    exact (map_igTransformS_igObs D one_pos z).trans (Measure.map_congr hYY')
  have hmarked := map_restrict_affineComp_one_marked hh hr hY'm hτ hind' hlaw' lam hsupp
  set G : DistOn (ballO (0 : ℂ) r) × AuxData → DistOn (ballO (0 : ℂ) r) × AuxData :=
    Prod.map (fun T => T + restrictTo (ballO (0 : ℂ) r) (MoTPort.ofFunC (logSing γ))) id
    with hGdef
  have hGm : Measurable G := by
    refine Measurable.prodMap ?_ measurable_id
    refine measurable_distOn_iff.2 fun φ => ?_
    exact (measurable_distOn_apply φ).add measurable_const
  have hm1 : Measurable fun v : Ω × ℂ =>
      (restrictTo (ballO (0 : ℂ) r) (affineComp 1 v.2 (h v.1)), igTransformS ρ 1 v.2 (Y' v.1)) := by
    have h1 : Measurable fun v : Ω × ℂ => ((h v.1, v.2) : DistC × ℂ) :=
      (hh.1.measurable.comp measurable_fst).prodMk measurable_snd
    have h2 : Measurable ((fun q : DistC × ℂ => affineComp 1 q.2 q.1) ∘
        fun v : Ω × ℂ => ((h v.1, v.2) : DistC × ℂ)) := (measurable_affineComp_center 1).comp h1
    exact ((measurable_restrictTo _).comp h2).prodMk (measurable_transform_marked hτ hY'm)
  have hm2 : Measurable fun ω => (restrictTo (ballO (0 : ℂ) r) (h ω), Y' ω) :=
    ((measurable_restrictTo _).comp hh.1.measurable).prodMk hY'm
  have hYfst : (fun v : Ω × ℂ => Y v.1) =ᵐ[P.prod lam] fun v => Y' v.1 :=
    Measure.quasiMeasurePreserving_fst.ae_eq_comp hYY'
  calc (P.prod lam).map (fun v : Ω × ℂ =>
        (restrictTo (ballO (0 : ℂ) r) (shiftedCase2Field γ (h v.1) v.2), igTransformS ρ 1 v.2 (Y v.1)))
      = (P.prod lam).map (G ∘ fun v : Ω × ℂ =>
          (restrictTo (ballO (0 : ℂ) r) (affineComp 1 v.2 (h v.1)),
            igTransformS ρ 1 v.2 (Y' v.1))) := by
        refine Measure.map_congr ?_
        filter_upwards [hYfst] with v hv
        simp only [Function.comp_apply, hGdef, Prod.map_apply, id_eq, shiftedCase2Field,
          restrictTo_addLogSing_on, hv]
    _ = P.map (G ∘ fun ω => (restrictTo (ballO (0 : ℂ) r) (h ω), Y' ω)) := by
        rw [← Measure.map_map hGm hm1, hmarked, Measure.map_map hGm hm2]
    _ = P.map (fun ω => (restrictTo (ballO (0 : ℂ) r) (addLogSing γ (h ω)), Y ω)) := by
        refine Measure.map_congr ?_
        filter_upwards [hYY'] with ω hω
        simp only [Function.comp_apply, hGdef, Prod.map_apply, id_eq, restrictTo_addLogSing_on, hω]

/-- **Cases 3–4 on `WPData` under the small-root conditional law** (route (c)). For `0 < r`,
`0 < ρ₀`, `ρ₀ + r ≤ 1` and every Borel event `G` of `DistOn (B_r(0)) × AuxData`: the probability,
under `(Canon.rootedLaw P)[· | z ∈ B_{ρ₀}(0)]`, that the Case 2 data `case2WPData` re-rooted at the
marked root and restricted to `B_r(0)` lie in `G`, equals the probability that the γ-cone field on
`B_r(0)` with the IG data `wpAux` lies in `G`. -/
theorem smallRoot_shiftedCase2_eq_cone
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) [Fact (0 < 2 * Real.pi * igChi γ)] {r ρ₀ : ℝ} (hr : 0 < r)
    (hρ₀ : 0 < ρ₀) (hρr : ρ₀ + r ≤ 1) {G : Set (DistOn (ballO (0 : ℂ) r) × AuxData)}
    (hG : MeasurableSet G) :
    (Canon.rootedLaw P)[|GMSCase1.smallRootEvent Ω ρ₀]
        ((fun v : Ω × ℂ => restrictData (ballO (0 : ℂ) r)
          (rerootData γ v.2 (case2WPData γ X₀ hIG₀ U ηL v))) ⁻¹' G) =
      P ((fun ω => (restrictTo (ballO (0 : ℂ) r)
        (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))),
          wpAux hIG₀ U ηL ω)) ⁻¹' G) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  set lam : Measure ℂ := Canon.rootMeasure[|ball (0 : ℂ) ρ₀] with hlam
  have hmass : Canon.rootMeasure (ball (0 : ℂ) ρ₀) = ENNReal.ofReal (ρ₀ ^ 2) :=
    GMS4.GMSA.normalizedLebesgueOnRootingDisk_ball ρ₀ hρ₀.le (by linarith)
  have hne : Canon.rootMeasure (ball (0 : ℂ) ρ₀) ≠ 0 := by
    rw [hmass]
    exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have : IsProbabilityMeasure lam := cond_isProbabilityMeasure hne
  have hsupp : ∀ᵐ z ∂lam, ‖z‖ + r ≤ 1 := by
    filter_upwards [ae_cond_mem (μ := Canon.rootMeasure) (measurableSet_ball (x := (0 : ℂ))
      (ε := ρ₀))] with z hz
    rw [mem_ball, dist_zero_right] at hz
    linarith
  have hcond : (Canon.rootedLaw P)[|GMSCase1.smallRootEvent Ω ρ₀] = P.prod lam :=
    prod_cond_univ_prod P Canon.rootMeasure (ball (0 : ℂ) ρ₀)
  have hFF' : (fun v : Ω × ℂ => restrictData (ballO (0 : ℂ) r)
        (rerootData γ v.2 (case2WPData γ X₀ hIG₀ U ηL v))) =ᵐ[P.prod lam]
      fun v : Ω × ℂ => (restrictTo (ballO (0 : ℂ) r) (shiftedCase2Field γ (wpField X₀ v.1) v.2),
        igTransformS (2 * Real.pi * igChi γ) 1 v.2 (wpAux hIG₀ U ηL v.1)) := by
    rw [← hcond]
    refine cond_absolutelyContinuous.ae_le ?_
    filter_upwards [ae_rerootData_case2_eq D] with v hv
    show (restrictTo (ballO (0 : ℂ) r) (rerootData γ v.2 (case2WPData γ X₀ hIG₀ U ηL v)).1,
      (rerootData γ v.2 (case2WPData γ X₀ hIG₀ U ηL v)).2) = _
    rw [hv]
  have hYa : AEMeasurable (wpAux hIG₀ U ηL) P := aemeasurable_igObs D
  have h1 : Measurable fun v : Ω × ℂ =>
      restrictTo (ballO (0 : ℂ) r) (shiftedCase2Field γ (wpField X₀ v.1) v.2) := by
    have hp : Measurable fun v : Ω × ℂ => ((wpField X₀ v.1, v.2) : DistC × ℂ) :=
      ((GMSCase1.measurable_wpField D).comp measurable_fst).prodMk measurable_snd
    have e : Measurable ((fun q : DistC × ℂ => shiftedCase2Field γ q.1 q.2) ∘
        fun v : Ω × ℂ => ((wpField X₀ v.1, v.2) : DistC × ℂ)) :=
      (measurable_shiftedCase2Field γ).comp hp
    exact (measurable_restrictTo _).comp e
  have hYfst : AEMeasurable (fun v : Ω × ℂ => wpAux hIG₀ U ηL v.1) (P.prod lam) :=
    hYa.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hq : AEMeasurable (fun v : Ω × ℂ => ((v.2, wpAux hIG₀ U ηL v.1) : ℂ × AuxData))
      (P.prod lam) := measurable_snd.aemeasurable.prodMk hYfst
  have h2' : AEMeasurable ((fun q : ℂ × AuxData => igTransformS (2 * Real.pi * igChi γ) 1 q.1 q.2) ∘
      fun v : Ω × ℂ => ((v.2, wpAux hIG₀ U ηL v.1) : ℂ × AuxData)) (P.prod lam) :=
    (measurable_igTransformS (2 * Real.pi * igChi γ) 1).comp_aemeasurable hq
  have h2 : AEMeasurable (fun v : Ω × ℂ =>
      igTransformS (2 * Real.pi * igChi γ) 1 v.2 (wpAux hIG₀ U ηL v.1)) (P.prod lam) := h2'
  have hF'a : AEMeasurable (fun v : Ω × ℂ =>
      (restrictTo (ballO (0 : ℂ) r) (shiftedCase2Field γ (wpField X₀ v.1) v.2),
        igTransformS (2 * Real.pi * igChi γ) 1 v.2 (wpAux hIG₀ U ηL v.1))) (P.prod lam) :=
    h1.aemeasurable.prodMk h2
  have hconea : AEMeasurable (fun ω => (restrictTo (ballO (0 : ℂ) r)
      (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))),
        wpAux hIG₀ U ηL ω)) P :=
    ((measurable_restrictTo _).comp_aemeasurable (aemeasurable_coneField D hγ)).prodMk hYa
  have hmarked := map_shiftedCase2_marked_eq_cone D hγ hr lam hsupp
  calc (Canon.rootedLaw P)[|GMSCase1.smallRootEvent Ω ρ₀]
        ((fun v : Ω × ℂ => restrictData (ballO (0 : ℂ) r)
          (rerootData γ v.2 (case2WPData γ X₀ hIG₀ U ηL v))) ⁻¹' G)
      = (P.prod lam) ((fun v : Ω × ℂ => restrictData (ballO (0 : ℂ) r)
          (rerootData γ v.2 (case2WPData γ X₀ hIG₀ U ηL v))) ⁻¹' G) := by rw [hcond]
    _ = (P.prod lam) ((fun v : Ω × ℂ =>
          (restrictTo (ballO (0 : ℂ) r) (shiftedCase2Field γ (wpField X₀ v.1) v.2),
            igTransformS (2 * Real.pi * igChi γ) 1 v.2 (wpAux hIG₀ U ηL v.1))) ⁻¹' G) :=
        measure_congr (hFF'.preimage G)
    _ = ((P.prod lam).map (fun v : Ω × ℂ =>
          (restrictTo (ballO (0 : ℂ) r) (shiftedCase2Field γ (wpField X₀ v.1) v.2),
            igTransformS (2 * Real.pi * igChi γ) 1 v.2 (wpAux hIG₀ U ηL v.1)))) G :=
        (Measure.map_apply_of_aemeasurable hF'a hG).symm
    _ = (P.map (fun ω => (restrictTo (ballO (0 : ℂ) r)
          (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))),
            wpAux hIG₀ U ηL ω))) G := by rw [hmarked]
    _ = P ((fun ω => (restrictTo (ballO (0 : ℂ) r)
          (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))),
            wpAux hIG₀ U ηL ω)) ⁻¹' G) := Measure.map_apply_of_aemeasurable hconea hG

/-- **The chain Case 2 → γ-cone** (route (c) with the Case 2 bound). Let `0 < r`, `0 < ρ₀`,
`ρ₀ + r ≤ 1`, `G'` a Borel event of `(cone|_{B_r(0)}, wpAux)`, `V ⊆ 𝔻` open and `G` a Borel event of
The restricted data `(h|_V, wpAux)`. If, whenever the marked root lies in `B_{ρ₀}(0)`, the re-rooted
Case 2 data in `G'` force the Case 2 data restricted to `V` into `G` (`hincl`: the translated test
pair is dominated by fixed ones, the `shiftedPair_lintegral_le`, plus locality), and the Case 0
event has probability `≤ δ`, then the cone event has probability
`≤ case1Moment^{1/p} δ^{1/q} / ρ₀²`. -/
theorem cone_event_le_of_case2
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) [Fact (0 < 2 * Real.pi * igChi γ)] {r ρ₀ : ℝ} (hr : 0 < r)
    (hρ₀ : 0 < ρ₀) (hρr : ρ₀ + r ≤ 1) {G' : Set (DistOn (ballO (0 : ℂ) r) × AuxData)}
    (hG' : MeasurableSet G') (V : Opens ℂ) (hV : (V : Set ℂ) ⊆ ball (0 : ℂ) 1)
    {G : Set (DistOn V × AuxData)} (hG : MeasurableSet G)
    (hincl : ∀ v : Ω × ℂ, v.2 ∈ ball (0 : ℂ) ρ₀ →
      restrictData (ballO (0 : ℂ) r) (rerootData γ v.2 (case2WPData γ X₀ hIG₀ U ηL v)) ∈ G' →
        restrictData V (case2WPData γ X₀ hIG₀ U ηL v) ∈ G)
    {p q : ℝ} (hpq : p.HolderConjugate q) {δ : ℝ≥0∞}
    (hbad : P ((fun ω => restrictData V (wpData X₀ hIG₀ U ηL ω)) ⁻¹' G) ≤ δ) :
    P ((fun ω => (restrictTo (ballO (0 : ℂ) r)
        (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))),
          wpAux hIG₀ U ηL ω)) ⁻¹' G') ≤
      GMSCase1.case1Moment D hγ p ^ (1 / p) * δ ^ (1 / q) / ENNReal.ofReal (ρ₀ ^ 2) := by
  rw [← smallRoot_shiftedCase2_eq_cone D hγ hr hρ₀ hρr hG']
  refine le_trans ?_ (GMSCase1.case2_smallRoot_local_event_le D hγ V hV hG hpq hbad hρ₀.le
    (by linarith))
  rw [cond_apply (GMSCase1.measurableSet_smallRootEvent ρ₀),
    cond_apply (GMSCase1.measurableSet_smallRootEvent ρ₀)]
  exact mul_le_mul_of_nonneg_left (measure_mono fun v hv => ⟨hv.1, hincl v hv.1.2 hv.2⟩) zero_le

end Coupling

end MatedCRTHarmonic.GMSCase
