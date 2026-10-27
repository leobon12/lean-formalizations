import MatedCRTHarmonic.GMS4FO.Final
import MatedCRTHarmonic.BundleSec4.MesoModelInputs

/-!
# The restricted Lemma 4.3 measurability input `Lemma43MeasurableM`

`GMS4FO.Lemma43Measurable D` asks null-measurability of `GMS4FO.failSet γ V ε Dm g A tol R r` for ARBITRARY
`Dm : Set ℂ`, `g : ℂ → ℝ`, `R : Set ℂ` (for non-measurable data, sample measurability of the integrals in
`LocalGood` is unavailable). the Proposition 4.10 argument uses it at exactly two places (`GMS4FO.cone_le_case2`, γ-cone law, at the
translated test `((· − z₀) '' Dm, g (· + z₀), (· − z₀) '' R)`; `GMS4FO.case2_smallRoot_failSet_le`, 0-cone law), always
at admissible test data: `ε > 0` a dyadic mesh, `Dm` open with `Dm ⊆ R`, `g` continuous on `Dm` with
`0 ≤ g ≤ M` there, `A, tol ≥ 0`, `R` open, `r ≥ 0`, and the degree balls `B̄(z, 4r)`, `z ∈ R`, inside `V`.

* **`Lemma43MeasurableM D`** — the restricted statement, exactly these hypotheses (the required measurability statement);
  `lemma43MeasurableM_of_lemma43Measurable` (the unrestricted one implies it);
* `cone_le_case2M`, `case2_smallRoot_failSet_leM`, `prop410Bad_le_at_meshM`, **`prop410At_of_inputsM`** — the
  four `hL`-consuming theorems re-proved verbatim from `Lemma43MeasurableM` (the remaining steps are imported),
  the instance facts threaded through;
* `InputsMForAllBundles`, `prop410AtForAllBundles_of_inputsM`;
* **`TwoInputsMForAllBundles`** (H4 + `Lemma43MeasurableM`) ⇒ **the companion map conclusion**,
  `exists_cellModel_of_matingOfTrees_of_twoInputsM`; `twoInputsMForAllBundles_of_twoInputs`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.BundleSec4

open MatedCRTHarmonic LQGMetric LQGMetric.Blueprint MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4FO

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **[18] Lemma 4.3, measurable form, at admissible test data** (restriction of `GMS4FO.Lemma43Measurable`;
The measurability statement): for every open `V ⊆ 𝔻` and every admissible test (`ε > 0`; `Dm` open, `Dm ⊆ R`; `g`
continuous on `Dm`, `0 ≤ g ≤ M` on `Dm`; `A, tol ≥ 0`; `R` open; `r ≥ 0`; `B̄(z, 4r) ⊆ V` for `z ∈ R`), the local
failure set is null-measurable for the laws of the γ-cone and of the 0-cone local data `(h|_V, ηL)`. -/
def Lemma43MeasurableM (_D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) : Prop :=
  ∀ (V : Opens ℂ), (V : Set ℂ) ⊆ ball (0 : ℂ) 1 →
    ∀ (ε : ℝ) (Dm : Set ℂ) (g : ℂ → ℝ) (A tol : ℝ) (R : Set ℂ) (r : ℝ),
      0 < ε → IsOpen Dm → ContinuousOn g Dm → (∃ M : ℝ, ∀ z ∈ Dm, 0 ≤ g z ∧ g z ≤ M) →
      0 ≤ A → 0 ≤ tol → IsOpen R → Dm ⊆ R → 0 ≤ r → (∀ z ∈ R, closedBall z (4 * r) ⊆ V) →
        NullMeasurableSet (failSet γ V ε Dm g A tol R r)
            (P.map fun ω => (restrictTo V (coneField (X ω) (coneRadial γ γ (fun t => B t ω)
              (fun t => B' t ω))), ηL ω)) ∧
          NullMeasurableSet (failSet γ V ε Dm g A tol R r)
            (P.map fun ω => (restrictTo V (coneField (X₀ ω) (coneRadial γ 0 (fun t => B₀ t ω)
              (fun t => B₀' t ω))), ηL ω))

/-- `0 ≤ pairBd M j` for `M ≥ 0`. -/
theorem bundle_pairBd_nonneg {M : ℝ} (hM : 0 ≤ M) (j : Fin 3) : 0 ≤ pairBd M j := by
  fin_cases j <;> simp [pairBd, hM]

/-- **the per-root chain from `Lemma43MeasurableM`** (`GMS4FO.cone_le_case2` with the admissibility of the
test threaded through; the restricted input is applied at the translated test). -/
theorem cone_le_case2M (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) [Fact (0 < 2 * Real.pi * igChi γ)] (hL : Lemma43MeasurableM D)
    {r₀ r₁ : ℝ} (hr₁ : 0 < r₁) {z₀ : ℂ} (hz₀ : ‖z₀‖ + r₁ ≤ 1)
    (hr₀₁ : r₀ + ‖z₀‖ ≤ r₁) {ε : ℝ} (hε : 0 < ε) {Dm R : Set ℂ} {g : ℂ → ℝ} {A tol r : ℝ}
    (hr : 0 ≤ r) (hDR : Dm ⊆ R) (hRV : ∀ z ∈ R, closedBall z (4 * r) ⊆ ball (0 : ℂ) r₀)
    (hDo : IsOpen Dm) (hgc : ContinuousOn g Dm) (hgb : ∃ M : ℝ, ∀ z ∈ Dm, 0 ≤ g z ∧ g z ≤ M)
    (hA : 0 ≤ A) (htol : 0 ≤ tol) (hRo : IsOpen R) :
    P {ω | ¬ GlobalGood (η ω) ε ((fun z => z - z₀) '' Dm) (fun u => g (u + z₀)) A tol
        ((fun z => z - z₀) '' R) r} ≤
      P {ω | (restrictTo (ballO (0 : ℂ) r₀) (GMSCase1.wpField X₀ ω +
          CellScaling.ofFunC (fun w => -γ * Real.log ‖w - z₀‖)), ηL ω) ∈
        failSet γ (ballO (0 : ℂ) r₀) ε Dm g A tol R r} := by
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hD : MeasurableSet Dm := hDo.measurableSet
  have hVcball : (ballO (-z₀) r₀ : Set ℂ) ⊆ ball (0 : ℂ) r₁ := ball_neg_subset hr₀₁
  have hVc1 : (ballO (-z₀) r₀ : Set ℂ) ⊆ ball (0 : ℂ) 1 :=
    hVcball.trans (ball_subset_ball (by linarith [norm_nonneg z₀]))
  have hUV := mem_ball_neg_iff z₀ r₀
  -- the translated test is admissible
  have hRV' : ∀ z ∈ (fun z => z - z₀) '' R, closedBall z (4 * r) ⊆ (ballO (-z₀) r₀ : Set ℂ) := by
    rintro _ ⟨w, hw, rfl⟩ x hx
    have hx' : x + z₀ ∈ closedBall w (4 * r) := by
      rw [mem_closedBall, dist_eq_norm] at hx ⊢
      rwa [show x + z₀ - w = x - (w - z₀) by ring]
    exact (hUV x).2 (hRV w hw hx')
  have hgc' : ContinuousOn (fun u => g (u + z₀)) ((fun z => z - z₀) '' Dm) := by
    have hadd : Continuous fun u : ℂ => u + z₀ := continuous_id.add continuous_const
    refine hgc.comp hadd.continuousOn ?_
    rintro _ ⟨w, hw, rfl⟩
    simpa using hw
  have hgb' : ∃ M : ℝ, ∀ u ∈ (fun z => z - z₀) '' Dm, 0 ≤ g (u + z₀) ∧ g (u + z₀) ≤ M := by
    obtain ⟨M, hM⟩ := hgb
    refine ⟨M, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    simpa using hM w hw
  -- step 1: the γ-cone side, through the bridge
  have hstep1 : P {ω | ¬ GlobalGood (η ω) ε ((fun z => z - z₀) '' Dm) (fun u => g (u + z₀)) A tol
      ((fun z => z - z₀) '' R) r} ≤
      P {ω | (restrictTo (ballO (-z₀) r₀)
        (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))), ηL ω) ∈
          failSet γ (ballO (-z₀) r₀) ε ((fun z => z - z₀) '' Dm) (fun u => g (u + z₀)) A tol
            ((fun z => z - z₀) '' R) r} := by
    refine measure_mono_ae ?_
    filter_upwards [ae_bridge_cone D hγ] with ω hω hfail
    obtain ⟨μ, hμ, φ, hηφ, hbr⟩ := hω
    have hfail' : ¬ GlobalGood ((ηL ω) ∘ φ) ε ((fun z => z - z₀) '' Dm) (fun u => g (u + z₀)) A tol
        ((fun z => z - z₀) '' R) r := by
      rw [← hηφ]; exact hfail
    exact mem_failSet_of_globalFail hμ (hbr (ballO (-z₀) r₀) isBounded_ball) hε hr (image_mono hDR) hRV'
      (measurableSet_image_sub hD z₀) hfail'
  -- step 2: the restricted law
  have hπc : AEMeasurable (fun ω => (restrictTo (ballO (-z₀) r₀)
      (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))), ηL ω)) P :=
    ((measurable_restrictTo _).comp_aemeasurable (GMSCase.aemeasurable_coneField D hγ)).prodMk
      D.measurable_curves.1.aemeasurable
  have hπs : AEMeasurable (fun ω => (restrictTo (ballO (-z₀) r₀)
      (GMSCase.shiftedCase2Field γ (GMSCase1.wpField X₀ ω) z₀),
        MatedCRT.affineReroot z₀ 1 0 (ηL ω))) P := by
    have hc : Measurable fun ω => MatedCRT.affineReroot z₀ 1 0 (ηL ω) := by
      have hp : Measurable fun ω => ((z₀, ηL ω) : ℂ × C(ℝ, ℂ)) :=
        measurable_const.prodMk D.measurable_curves.1
      have e : Measurable ((fun p : ℂ × C(ℝ, ℂ) => GMSCase.caseCurve 1 p.1 p.2) ∘
          fun ω => ((z₀, ηL ω) : ℂ × C(ℝ, ℂ))) :=
        (GMSCase.measurable_caseCurve 1).comp hp
      exact e
    exact (measurable_shiftedField D _ z₀).aemeasurable.prodMk hc.aemeasurable
  have hmaps := map_cone_eq_shifted D hγ hr₁ hz₀ (V := ballO (-z₀) r₀) hVcball
  have hnull := (hL (ballO (-z₀) r₀) hVc1 ε ((fun z => z - z₀) '' Dm) (fun u => g (u + z₀)) A tol
    ((fun z => z - z₀) '' R) r hε (isOpen_image_sub hDo z₀) hgc' hgb' hA htol (isOpen_image_sub hRo z₀)
    (image_mono hDR) hr hRV').1
  have hstep2 := (Measure.map_apply₀ hπc hnull).symm.trans
    ((congrArg (fun m : Measure (DistOn (ballO (-z₀) r₀) × C(ℝ, ℂ)) => m _) hmaps).trans
      (Measure.map_apply₀ hπs (hmaps ▸ hnull)))
  -- step 3: recentring
  refine hstep1.trans (hstep2.le.trans (measure_mono_ae ?_))
  filter_upwards [D.spaceFilling] with ω hsf hmem
  have hfv : HasFirstVisits (ηL ω) := hasFirstVisits_of_surjective hsf.1 hsf.2.1
  have hmem' : (restrictTo (ballO (-z₀) r₀) (affineComp 1 z₀ (GMSCase1.wpField X₀ ω +
      CellScaling.ofFunC (fun w => -γ * Real.log ‖w - z₀‖))), MatedCRT.affineReroot z₀ 1 0 (ηL ω)) ∈
      failSet γ (ballO (-z₀) r₀) ε ((fun z => z - z₀) '' Dm) (fun u => g (u + z₀)) A tol
        ((fun z => z - z₀) '' R) r := by
    rw [GMSCase.affineComp_one_case2_eq]
    exact hmem
  have := mem_failSet_translate hUV hfv hmem'
  rw [image_add_image_sub, image_add_image_sub] at this
  simpa only [sub_add_cancel] using this

/-- **the Cases 0 → 1 → 2 on `failSet` from `Lemma43MeasurableM`** (`GMS4FO.case2_smallRoot_failSet_le` with
The admissibility of the test as hypotheses). -/
theorem case2_smallRoot_failSet_leM (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (hL : Lemma43MeasurableM D) {V₀ : Opens ℂ}
    (hV₀ : (V₀ : Set ℂ) ⊆ ball (0 : ℂ) 1) {ε : ℝ} {Dm R : Set ℂ} {g : ℂ → ℝ} {A tol r : ℝ}
    (hε : 0 < ε) (hDo : IsOpen Dm) (hgc : ContinuousOn g Dm) (hgb : ∃ M : ℝ, ∀ z ∈ Dm, 0 ≤ g z ∧ g z ≤ M)
    (hA : 0 ≤ A) (htol : 0 ≤ tol) (hRo : IsOpen R) (hDR : Dm ⊆ R) (hr : 0 ≤ r)
    (hRV : ∀ z ∈ R, closedBall z (4 * r) ⊆ V₀)
    {p q : ℝ} (hpq : p.HolderConjugate q) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) {δ : ℝ≥0∞}
    (hbad : P {ω | (restrictTo V₀ (coneField (X₀ ω) (coneRadial γ 0 (fun t => B₀ t ω)
        (fun t => B₀' t ω))), ηL ω) ∈ failSet γ V₀ ε Dm g A tol R r} ≤ δ) :
    (Canon.rootedLaw P)[|GMSCase1.smallRootEvent Ω κ]
        {v : Ω × ℂ | (restrictTo V₀ (GMSCase1.wpField X₀ v.1 +
          CellScaling.ofFunC (fun w => -γ * Real.log ‖w - v.2‖)), ηL v.1) ∈
            failSet γ V₀ ε Dm g A tol R r} ≤
      GMSCase1.case1Moment D hγ p ^ (1 / p) * δ ^ (1 / q) / ENNReal.ofReal (κ ^ 2) := by
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  set F := failSet γ V₀ ε Dm g A tol R r with hF
  set G₀ : Set (DistOn V₀ × GMSCase1.AuxData) := {x | (x.1, x.2.2) ∈ F} with hG₀
  set π₀ : Ω → DistOn V₀ × GMSCase1.AuxData := fun ω =>
    GMSCase1.restrictData V₀ (GMSCase1.zeroConeData γ X₀ hIG₀ B₀ B₀' U ηL ω) with hπ₀
  have hπ₀m : AEMeasurable π₀ P :=
    (GMSCase1.measurable_restrictData V₀).comp_aemeasurable
      ((GMS4.aemeasurable_prop48ZeroConeField D).prodMk (GMSCase1.aemeasurable_wpAux D hγ))
  set G := toMeasurable (P.map π₀) G₀ with hG
  have hGm : MeasurableSet G := measurableSet_toMeasurable _ _
  have proj_m : Measurable fun x : DistOn V₀ × GMSCase1.AuxData => (x.1, x.2.2) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  have hlaw : (P.map π₀).map (fun x : DistOn V₀ × GMSCase1.AuxData => (x.1, x.2.2)) =
      P.map fun ω => (restrictTo V₀ (coneField (X₀ ω) (coneRadial γ 0 (fun t => B₀ t ω)
        (fun t => B₀' t ω))), ηL ω) := by
    rw [AEMeasurable.map_map_of_aemeasurable proj_m.aemeasurable hπ₀m]
    rfl
  have hG₀null : NullMeasurableSet G₀ (P.map π₀) := by
    have h := (hL V₀ hV₀ ε Dm g A tol R r hε hDo hgc hgb hA htol hRo hDR hr hRV).2
    rw [← hlaw] at h
    exact h.preimage (proj_m.quasiMeasurePreserving _)
  have hV₀le : V₀ ≤ Blueprint.ballO (0 : ℂ) 1 := hV₀
  have hbad' : P ((fun ω => GMSCase1.restrictData V₀ (GMSCase1.wpData X₀ hIG₀ U ηL ω)) ⁻¹' G) ≤ δ := by
    rw [← GMSCase1.measure_restrictData_zeroConeData_preimage D hγ V₀ hV₀le hGm,
      ← Measure.map_apply_of_aemeasurable hπ₀m hGm, hG, measure_toMeasurable,
      Measure.map_apply₀ hπ₀m hG₀null]
    exact hbad
  refine le_trans (measure_mono_ae ?_) (GMSCase1.case2_smallRoot_local_event_le D hγ V₀ hV₀ hGm hpq hbad'
    hκ0 hκ1)
  have hac : (Canon.rootedLaw P)[|GMSCase1.smallRootEvent Ω κ] ≪ Canon.rootedLaw P :=
    cond_absolutelyContinuous
  filter_upwards [hac.ae_le (GMSCase1.ae_case2Field_eq D)] with v hv hmem
  change GMSCase1.restrictData V₀ (GMSCase1.case2WPData γ X₀ hIG₀ U ηL v) ∈ G
  apply subset_toMeasurable
  change (restrictTo V₀ (Canon.case2Field γ (GMSCase1.wpField X₀ v.1) v.2),
    (GMSCase1.wpAux hIG₀ U ηL v.1).2) ∈ F
  rw [hv]
  exact hmem

/-- **[18] Proposition 4.10 at one dyadic mesh from `Lemma43MeasurableM`** (`GMS4FO.prop410Bad_le_at_mesh`; the
two `hL` instances are at the admissible pairs `(pairDom Dm κ j, pairFun f j)`, `R = B_{13/16}(0)`). -/
theorem prop410Bad_le_at_meshM (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) [Fact (0 < 2 * Real.pi * igChi γ)] (hL : Lemma43MeasurableM D)
    {q α₀ A₀ C₀ : ℝ} (hA₀ : 0 ≤ A₀) (hC₀ : 0 ≤ C₀)
    (h0 : ∀ k : ℕ, 1 ≤ k → ∀ (Dm : Set ℂ) (g : ℂ → ℝ) (M : ℝ), IsOpen Dm →
      Dm ⊆ ball (0 : ℂ) (13 / 16) → ContinuousOn g Dm → (∀ z ∈ Dm, 0 ≤ g z ∧ g z ≤ M) →
        P {ω | ¬ GlobalGood (η₀ ω) (CellFamily.mesh k) Dm g A₀ (CellFamily.mesh k ^ α₀ * M)
          (ball (0 : ℂ) (13 / 16)) (CellFamily.mesh k ^ q)} ≤ ENNReal.ofReal (C₀ * CellFamily.mesh k ^ α₀))
    {p q' : ℝ} (hpq : p.HolderConjugate q') {k : ℕ} (hk : 1 ≤ k) {β α : ℝ} {Dm : Set ℂ}
    {f : ℂ → ℝ} (hadm : GMS4.Prop210Admissible (CellFamily.mesh k) (3 / 4) 100 β Dm f)
    (hκs : CellFamily.mesh k ^ (α₀ / (4 * q')) ≤ 1 / 32) (hrs : 4 * CellFamily.mesh k ^ q ≤ 1 / 32)
    (htol : tolTotal (CellFamily.mesh k) α₀ β (α₀ / (4 * q')) A₀ ≤ CellFamily.mesh k ^ α) :
    P (BundleSec4.Prop410Bad η (CellFamily.mesh k) Dm f A₀ (CellFamily.mesh k ^ α)) ≤
      3 * (GMSCase1.case1Moment D hγ p ^ (1 / p) *
        ENNReal.ofReal (C₀ ^ (1 / q') * CellFamily.mesh k ^ (α₀ / (2 * q')))) := by
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨hε0, hε1, -, -, -, -, hDo, -, hDsub, hthick, hfb, hlip⟩ := hadm
  have hq'0 : 0 < q' := hpq.symm.pos
  have hκ0 : 0 < CellFamily.mesh k ^ (α₀ / (4 * q')) := Real.rpow_pos_of_pos hε0 _
  have hκ1 : CellFamily.mesh k ^ (α₀ / (4 * q')) ≤ 1 := hκs.trans (by norm_num)
  have hr0 : 0 ≤ CellFamily.mesh k ^ q := (Real.rpow_pos_of_pos hε0 _).le
  have hM0 : 0 ≤ 100 * CellFamily.mesh k ^ (-β) := by positivity
  have hα₀ε : 0 ≤ CellFamily.mesh k ^ α₀ := (Real.rpow_pos_of_pos hε0 _).le
  have hRV : ∀ z ∈ ball (0 : ℂ) (13 / 16), closedBall z (4 * CellFamily.mesh k ^ q) ⊆ ball (0 : ℂ) (7 / 8) :=
    fun z hz => closedBall_subset_of_mem hz hrs
  have hfM : ∀ z ∈ Dm, f z ≤ 100 * CellFamily.mesh k ^ (-β) := fun z hz => (hfb z hz).2
  have hfc : ContinuousOn f Dm := continuousOn_of_lipschitz hM0 hlip
  have hVT : volume (thickening (CellFamily.mesh k ^ (α₀ / (4 * q'))) (frontier Dm)) ≤
      ENNReal.ofReal (100 * CellFamily.mesh k ^ (α₀ / (4 * q'))) :=
    hthick _ ⟨hκ0, lt_of_le_of_lt hκs (by norm_num)⟩
  -- admissibility of the three pairs
  have htolj : ∀ j : Fin 3, 0 ≤ CellFamily.mesh k ^ α₀ * pairBd (100 * CellFamily.mesh k ^ (-β)) j :=
    fun j => mul_nonneg hα₀ε (bundle_pairBd_nonneg hM0 j)
  have hgbj : ∀ j : Fin 3, ∃ M : ℝ, ∀ z ∈ pairDom Dm (CellFamily.mesh k ^ (α₀ / (4 * q'))) j,
      0 ≤ pairFun f j z ∧ pairFun f j z ≤ M :=
    fun j => ⟨_, pairFun_bounds hfb _ j⟩
  -- the three local failure events on `Ω × ℂ`
  let S : Fin 3 → Set (Ω × ℂ) := fun j => {v | (restrictTo (ballO (0 : ℂ) (7 / 8))
    (GMSCase1.wpField X₀ v.1 + CellScaling.ofFunC (fun w => -γ * Real.log ‖w - v.2‖)), ηL v.1) ∈
      failSet γ (ballO (0 : ℂ) (7 / 8)) (CellFamily.mesh k) (pairDom Dm (CellFamily.mesh k ^ (α₀ / (4 * q'))) j)
        (pairFun f j) A₀ (CellFamily.mesh k ^ α₀ * pairBd (100 * CellFamily.mesh k ^ (-β)) j)
        (ball (0 : ℂ) (13 / 16)) (CellFamily.mesh k ^ q)}
  -- step A: one root
  have hA : ∀ z₀ ∈ ball (0 : ℂ) (CellFamily.mesh k ^ (α₀ / (4 * q'))),
      P (BundleSec4.Prop410Bad η (CellFamily.mesh k) Dm f A₀ (CellFamily.mesh k ^ α)) ≤
        ∑ j, P ((fun ω => (ω, z₀)) ⁻¹' S j) := by
    intro z₀ hz₀
    have hz₀' : ‖z₀‖ < CellFamily.mesh k ^ (α₀ / (4 * q')) := by rwa [mem_ball, dist_zero_right] at hz₀
    have hsub : BundleSec4.Prop410Bad η (CellFamily.mesh k) Dm f A₀ (CellFamily.mesh k ^ α) ⊆
        ⋃ j : Fin 3, {ω | ¬ GlobalGood (η ω) (CellFamily.mesh k)
          ((fun z => z - z₀) '' pairDom Dm (CellFamily.mesh k ^ (α₀ / (4 * q'))) j)
          (fun u => pairFun f j (u + z₀)) A₀ (CellFamily.mesh k ^ α₀ * pairBd (100 * CellFamily.mesh k ^ (-β)) j)
          ((fun z => z - z₀) '' ball (0 : ℂ) (13 / 16)) (CellFamily.mesh k ^ q)} := by
      intro ω hω
      obtain ⟨j, hj⟩ := exists_fail_of_target (c := η ω) (R := ball (0 : ℂ) (13 / 16))
        (r := CellFamily.mesh k ^ q) hε0.le hDo hM0 hκ0.le hA₀ hfM hlip hz₀' (volume_le_two hDsub) hVT hα₀ε
        (htol.trans' (le_of_eq (by unfold tolTotal; ring))) hω
      exact mem_iUnion.2 ⟨j, hj⟩
    refine (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans
      (Finset.sum_le_sum fun j _ => ?_))
    have hnz : ‖z₀‖ + 15 / 16 ≤ 1 := by linarith
    have hr01 : 7 / 8 + ‖z₀‖ ≤ 15 / 16 := by linarith
    exact cone_le_case2M D hγ hL (r₀ := 7 / 8) (by norm_num) hnz hr01 hε0
      hr0 (pairDom_subset hDsub hκs j) hRV (isOpen_pairDom hDo _ j) (continuousOn_pairFun hfc _ j)
      (hgbj j) hA₀ (htolj j) isOpen_ball
  -- step B: average over the root
  have hB := le_cond_sum_of_forall_slice P hκ0 hκ1 S hA
  refine hB.trans ?_
  -- step C: Cases 0–2 for each pair
  have hC : ∀ j : Fin 3, (Canon.rootedLaw P)[|GMSCase1.smallRootEvent Ω (CellFamily.mesh k ^ (α₀ / (4 * q')))]
      (S j) ≤ GMSCase1.case1Moment D hγ p ^ (1 / p) *
        ENNReal.ofReal (C₀ ^ (1 / q') * CellFamily.mesh k ^ (α₀ / (2 * q'))) := by
    intro j
    have hbad0 := (zeroCone_failSet_le D hγ (V := ballO (0 : ℂ) (7 / 8)) isBounded_ball hε0 hr0
      (pairDom_subset hDsub hκs j) hRV ((isOpen_pairDom hDo _ j).measurableSet)
      (g := pairFun f j) (A := A₀) (tol := CellFamily.mesh k ^ α₀ * pairBd (100 * CellFamily.mesh k ^ (-β)) j)).trans
      (h0 k hk _ _ _ (isOpen_pairDom hDo _ j) (pairDom_subset hDsub hκs j) (continuousOn_pairFun hfc _ j)
        (pairFun_bounds hfb _ j))
    have h := case2_smallRoot_failSet_leM D hγ hL (V₀ := ballO (0 : ℂ) (7 / 8))
      (ball_subset_ball (by norm_num)) hε0 (isOpen_pairDom hDo _ j) (continuousOn_pairFun hfc _ j)
      (hgbj j) hA₀ (htolj j) isOpen_ball (pairDom_subset hDsub hκs j) hr0 hRV hpq hκ0.le hκ1 hbad0
    rw [mul_div_assoc, GMSCase1.case1_rate_div_eq hC₀ hε0 hq'0] at h
    exact h
  calc ∑ j, (Canon.rootedLaw P)[|GMSCase1.smallRootEvent Ω (CellFamily.mesh k ^ (α₀ / (4 * q')))] (S j)
      ≤ ∑ _j : Fin 3, GMSCase1.case1Moment D hγ p ^ (1 / p) *
          ENNReal.ofReal (C₀ ^ (1 / q') * CellFamily.mesh k ^ (α₀ / (2 * q'))) :=
        Finset.sum_le_sum fun j _ => hC j
    _ = _ := by simp

/-- **[18] Proposition 4.10 at `(ρ, C) = (3/4, 100)` for the γ-cone curve, from `ZeroConeCase0At D (13/16)` and
The restricted `Lemma43MeasurableM D`** (`GMS4FO.prop410At_of_inputs`, verbatim, with `prop410Bad_le_at_meshM`). -/
theorem prop410At_of_inputsM (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (h0 : ZeroConeCase0At D (13 / 16)) (hL : Lemma43MeasurableM D) :
    BundleSec4.Prop410At P η (3 / 4) 100 := by
  have : Fact (0 < 2 * Real.pi * igChi γ) := ⟨GMSCase.igPeriod_pos D⟩
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨q, α₀, A₀, C₀, hq, hα₀, hA₀, hC₀, h0⟩ := h0
  obtain ⟨p, hp1, hp4⟩ := GMSCase1.exists_case1_exponent hγ
  have hpq : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp1
  set q' := p.conjExponent with hq'def
  have hq'0 : 0 < q' := hpq.symm.pos
  have hq'1 : 1 < q' := hpq.symm.lt
  have hMfin : GMSCase1.case1Moment D hγ p ^ (1 / p) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity)
      (GMSCase1.case1Moment_lt_top D hγ (by linarith) hp4).ne
  set ξ := α₀ / (4 * q') with hξdef
  have hξ : 0 < ξ := by positivity
  have hξα : ξ ≤ α₀ := by
    rw [hξdef, div_le_iff₀ (by positivity)]
    nlinarith
  have h2ξ : α₀ / (2 * q') = 2 * ξ := by rw [hξdef]; field_simp; ring
  set K := 300 + 10200 * A₀ with hK
  have hK0 : 0 < K := by positivity
  -- small meshes
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 ((eventually_mesh_rpow_le hξ (by norm_num : (0 : ℝ) < 1 / 32)).and
    ((eventually_mesh_rpow_le hq (by norm_num : (0 : ℝ) < 1 / 128)).and
      (eventually_mesh_rpow_le (by positivity : 0 < ξ / 2) (inv_pos.2 hK0))))
  set Mreal := (GMSCase1.case1Moment D hγ p ^ (1 / p)).toReal with hMreal
  set Cfail := max (3 * Mreal * C₀ ^ (1 / q')) ((CellFamily.mesh k₀ ^ (ξ / 4))⁻¹) with hCfail
  have hCinv : 0 ≤ (CellFamily.mesh k₀ ^ (ξ / 4))⁻¹ :=
    (inv_pos.2 (Real.rpow_pos_of_pos (BundleSec4.bundle_mesh_pos k₀) _)).le
  refine ⟨ξ / 4, A₀, ξ / 4, Cfail, by positivity, by positivity, hA₀,
    le_max_of_le_right hCinv, fun k Dm f hadm => ?_⟩
  have hε0 : 0 < CellFamily.mesh k := hadm.1
  have hε1 : CellFamily.mesh k < 1 := hadm.2.1
  have hk1 : 1 ≤ k := by
    by_contra hk
    have : k = 0 := by omega
    subst this
    simp [CellFamily.mesh] at hε1
  rcases le_or_gt k₀ k with hk | hk
  · obtain ⟨hκs, hrs, hKs⟩ := hk₀ k hk
    have htol : tolTotal (CellFamily.mesh k) α₀ (ξ / 4) ξ A₀ ≤ CellFamily.mesh k ^ (ξ / 4) := by
      refine (tolTotal_le hε0 hε1.le hξ.le hξα).trans ?_
      have hsplit : CellFamily.mesh k ^ (3 * ξ / 4) = CellFamily.mesh k ^ (ξ / 2) * CellFamily.mesh k ^ (ξ / 4) := by
        rw [← Real.rpow_add hε0]; congr 1; ring
      rw [hsplit, ← mul_assoc]
      have h1 : K * CellFamily.mesh k ^ (ξ / 2) ≤ 1 := by
        have := mul_le_mul_of_nonneg_left hKs hK0.le
        rwa [mul_inv_cancel₀ hK0.ne'] at this
      calc K * CellFamily.mesh k ^ (ξ / 2) * CellFamily.mesh k ^ (ξ / 4)
          ≤ 1 * CellFamily.mesh k ^ (ξ / 4) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_pos_of_pos hε0 _).le
        _ = CellFamily.mesh k ^ (ξ / 4) := one_mul _
    have hbound := prop410Bad_le_at_meshM D hγ hL hA₀ hC₀ h0 hpq hk1 hadm hκs (by linarith) htol
    refine hbound.trans ?_
    rw [h2ξ, ← ENNReal.ofReal_toReal hMfin, ← hMreal, ← ENNReal.ofReal_mul (by positivity),
      show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hpow : CellFamily.mesh k ^ (2 * ξ) ≤ CellFamily.mesh k ^ (ξ / 4) :=
      Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (by linarith)
    have hM0 : 0 ≤ Mreal := ENNReal.toReal_nonneg
    have hC0' : 0 ≤ C₀ ^ (1 / q') := Real.rpow_nonneg hC₀ _
    calc 3 * (Mreal * (C₀ ^ (1 / q') * CellFamily.mesh k ^ (2 * ξ)))
        = 3 * Mreal * C₀ ^ (1 / q') * CellFamily.mesh k ^ (2 * ξ) := by ring
      _ ≤ Cfail * CellFamily.mesh k ^ (ξ / 4) :=
        mul_le_mul (le_max_left _ _) hpow (Real.rpow_pos_of_pos hε0 _).le
          (le_max_of_le_right hCinv)
  · -- the finitely many large meshes: the bound exceeds one
    have hmesh : CellFamily.mesh k₀ ≤ CellFamily.mesh k := mesh_anti hk.le
    have hpos : 0 < CellFamily.mesh k₀ ^ (ξ / 4) := Real.rpow_pos_of_pos (BundleSec4.bundle_mesh_pos k₀) _
    have hge : CellFamily.mesh k₀ ^ (ξ / 4) ≤ CellFamily.mesh k ^ (ξ / 4) :=
      Real.rpow_le_rpow (BundleSec4.bundle_mesh_pos k₀).le hmesh (by positivity)
    calc P (BundleSec4.Prop410Bad η (CellFamily.mesh k) Dm f A₀ (CellFamily.mesh k ^ (ξ / 4))) ≤ 1 := prob_le_one
      _ = ENNReal.ofReal ((CellFamily.mesh k₀ ^ (ξ / 4))⁻¹ * CellFamily.mesh k₀ ^ (ξ / 4)) := by
        rw [inv_mul_cancel₀ hpos.ne', ENNReal.ofReal_one]
      _ ≤ ENNReal.ofReal (Cfail * CellFamily.mesh k ^ (ξ / 4)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul (le_max_right _ _) hge hpos.le
          (le_max_of_le_right hCinv))

end Coupling

/-! ### The mated-CRT map conclusion from the restricted input -/

/-- the two inputs with the restricted Lemma 4.3 measurability, for every frozen coupling. -/
def InputsMForAllBundles : Prop :=
  ∀ (γ : ℝ) (_ : γ ∈ Ioo (0 : ℝ) 2) (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω)
    (P : Measure Ω) (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
    (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2)
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm),
      ZeroConeCase0At D (13 / 16) ∧ Lemma43MeasurableM D

/-- `BundleSec4.Prop410AtForAllBundles` from the restricted inputs. -/
theorem prop410AtForAllBundles_of_inputsM (h : InputsMForAllBundles) : Prop410AtForAllBundles :=
  fun γ hγ Ω mΩ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D =>
    prop410At_of_inputsM D hγ (h γ hγ Ω mΩ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D).1
      (h γ hγ Ω mΩ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D).2

end MatedCRTHarmonic.BundleSec4
