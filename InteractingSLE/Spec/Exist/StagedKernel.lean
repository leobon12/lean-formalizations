/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedCongr
import InteractingSLE.Spec.Sec5.Lemma56Stages

/-!
# Staged histories, step (c): the field-determined realization under a conditional-expectation kernel

Packet PROVE-STAGED (Goal 2 of PROVE-FLOWEXIST3, obstruction (c)). Let `r : Ω → R` be a measurable map into a standard
Borel space (the retained past of a staged history: `pastSigma` is exactly `comap r`), and suppose that, conditionally on
`r` (`condExpKernel P (comap r) ω₀`, for `P`-a.e. `ω₀`), a measurable field `Y` is a GFF whose data is the force-boundary
data of a word read measurably off `r ω₀`. Then **one** measurable driver `E` on `Ω` realizes, for `P`-a.e. `ω₀`, an
optional hull coupling with that field under the kernel at `ω₀` (`exists_drv_condKernel`).

* **`ae_ae_eq_of_comap`**: the kernel at `ω₀` is carried by the atom `{r = r ω₀}` (countable separation of `R` and
  `κ_{ω₀}(A) = 1_A(ω₀)` for past events `A`, `Sec5.Lemma56Stages.condExpKernel_apply_eq_indicator`);
* **`isOptionalHullCoupling_drv`** (one probability space): for an ordered word, a measurable GFF `h₀` with its data and
  a measurable `E` that is almost surely the field-determined driver `drvPath (detCode Φ (w, h₀))` of
  `Theorem12ParamStatement` (`StagedDet.lean`), there are `𝓕, V, B` making `(E, h₀)` an optional hull coupling. The
  coupling is the field-determined realization of PROVE-FLOWEXIST3 (`exists_fieldDetermination_realization` with the
  sealed Theorem 1.1 coupling as reference and `hullClauseTransferStatement`), moved to the usual augmentation and then
  to `E` (`IsOptionalHullCoupling.congr_ae`); the reference law identifies `detCode Φ (w, ·)` with the killed driver
  code of the realization almost everywhere (both are the killed driver code of the reference coupling).
* **`exists_drv_condKernel`**: `E ω = (drvPath z, z.1)` with `z = detCode Φ_{m,n} (w(r ω), Y ω)`, `(m, n)` the numbers
  of marks read off `r ω`; measurable by a countable decomposition over `(m, n)`. On the atom of `ω₀` it is the
  driver of the previous item.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Exist

namespace Staged

open Sec2.Assembly LQGMetric

/-! ### The kernel is carried by the atom of `ω₀` -/

/-- **The conditional kernel given `r` is carried by `{r = r ω₀}`** for almost every `ω₀`. -/
theorem ae_ae_eq_of_comap {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {R : Type*} [MeasurableSpace R] [MeasurableSpace.CountablySeparated R] {r : Ω → R}
    (hr : Measurable r) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (MeasurableSpace.comap r inferInstance) ω₀), r ω = r ω₀ := by
  obtain ⟨S, hSc, hSm, hsep⟩ := exists_countable_separating R MeasurableSet univ
  have hm : MeasurableSpace.comap r inferInstance ≤ mΩ := hr.comap_le
  have hind : ∀ᵐ ω₀ ∂P, ∀ s ∈ S, condExpKernel P (MeasurableSpace.comap r inferInstance) ω₀ (r ⁻¹' s) =
      (r ⁻¹' s).indicator 1 ω₀ :=
    (ae_ball_iff hSc).2 fun s hs =>
      Sec5.Lemma56Stages.condExpKernel_apply_eq_indicator hm ⟨s, hSm s hs, rfl⟩
  filter_upwards [hind] with ω₀ hω₀
  set κ₀ := condExpKernel P (MeasurableSpace.comap r inferInstance) ω₀
  have hs : ∀ s ∈ S, ∀ᵐ ω ∂κ₀, (r ω ∈ s ↔ r ω₀ ∈ s) := by
    intro s hsS
    have hpre : MeasurableSet (r ⁻¹' s) := hr (hSm s hsS)
    by_cases h₀ : r ω₀ ∈ s
    · have h1 : κ₀ (r ⁻¹' s) = 1 := by
        rw [hω₀ s hsS, indicator_of_mem (show ω₀ ∈ r ⁻¹' s from h₀)]; rfl
      have hc : κ₀ (r ⁻¹' s)ᶜ = 0 := by rw [prob_compl_eq_zero_iff hpre]; exact h1
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hc] with ω hω
      simp only [mem_compl_iff, not_not, mem_preimage] at hω
      exact ⟨fun _ => h₀, fun _ => hω⟩
    · have h1 : κ₀ (r ⁻¹' s) = 0 := by
        rw [hω₀ s hsS, indicator_of_notMem (show ω₀ ∉ r ⁻¹' s from h₀)]
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h1] with ω hω
      exact ⟨fun h => absurd h hω, fun h => absurd h h₀⟩
  filter_upwards [(ae_ball_iff hSc).2 hs] with ω hω
  exact hsep _ (mem_univ _) _ (mem_univ _) fun s hsS => hω s hsS

/-! ### The driver on one probability space -/

/-- The chosen jointly measurable determination map of `Theorem12ParamStatement`. -/
def paramΦ (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (nL nR : ℕ) :
    WordData nL nR × DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ) :=
  (h12p κ hκ nL nR).choose

theorem measurable_paramΦ (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (nL nR : ℕ) :
    Measurable (paramΦ h12p hκ nL nR) :=
  (h12p κ hκ nL nR).choose_spec.1

open Classical in
/-- The staged driver read off a driver code: on the good driver codes `DSet` the path frozen at its left limit and
the lifetime; the constant `0` path with lifetime `0` off it. -/
def drvOf (z : DCode) : (ℝ≥0 → ℝ) × ℝ≥0∞ := if z ∈ DSet then (drvPath z, z.1) else (fun _ => 0, 0)

open Classical in
theorem measurable_drvOf : Measurable drvOf :=
  Measurable.ite measurableSet_DSet (measurable_drvPath.prodMk measurable_fst) measurable_const

theorem drvOf_of_mem {z : DCode} (hz : z ∈ DSet) : drvOf z = (drvPath z, z.1) := by
  simp only [drvOf, hz, ↓reduceIte]

/-- **The staged driver is regular at every sample**: continuous before its lifetime, `0` at time `0`, constant from
its lifetime on, and at a finite positive lifetime its value is the continuous left limit whenever it has one. -/
theorem drvOf_regular (z : DCode) :
    ContinuousOn (drvOf z).1 {t | (t : ℝ≥0∞) < (drvOf z).2} ∧ (drvOf z).1 0 = 0 ∧
      (∀ t : ℝ≥0, (drvOf z).2 ≤ t → (drvOf z).1 t = (drvOf z).1 (drvOf z).2.toNNReal) ∧
      ((drvOf z).2 ≠ ⊤ → 0 < (drvOf z).2 → ∀ c : ℝ,
        Tendsto (drvOf z).1 (𝓝[<] (drvOf z).2.toNNReal) (𝓝 c) → (drvOf z).1 (drvOf z).2.toNNReal = c) := by
  by_cases hz : z ∈ DSet
  · rw [drvOf_of_mem hz]
    refine ⟨(continuousOn_of_mem_DSet hz).congr fun t ht => drvPath_of_lt ht, ?_, fun t ht => ?_,
      fun hne hpos c hc => drvPath_eq_of_tendsto hne hpos hc⟩
    · have hd : dec z.2 0 = 0 := by
        have e : ∀ n : ℕ, flr n 0 = 0 := fun n => by simp [flr]
        rw [show dec z.2 0 = limsup (fun n => z.2 n (flr n 0)) atTop by rw [dec]]
        simp only [e, hz.2.1 _ 0 (by simp [dyad]), limsup_const]
      by_cases h0 : ((0 : ℝ≥0) : ℝ≥0∞) < z.1
      · exact (drvPath_of_lt h0).trans hd
      · have hζ : z.1 = 0 := by
          rw [ENNReal.coe_zero] at h0; exact le_antisymm (not_lt.1 h0) zero_le
        have e : ∀ m : ℕ, z.1.toNNReal - 1 / ((m : ℝ≥0) + 1) = 0 := fun m => by simp [hζ]
        simp only [drvPath, h0, ↓reduceIte, e, limsup_const, hd]
    · have hne : z.1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top ht
      have h1 : ¬ (t : ℝ≥0∞) < z.1 := not_lt.2 ht
      have h2 : ¬ ((z.1.toNNReal : ℝ≥0) : ℝ≥0∞) < z.1 := by
        rw [ENNReal.coe_toNNReal hne]; exact lt_irrefl _
      simp only [drvPath, h1, h2, ↓reduceIte]
  · simp only [drvOf, hz, ↓reduceIte]
    simp

/-- Equality of driver codes is a measurable condition. -/
theorem measurableSet_eq_dCode {α : Type*} [MeasurableSpace α] {A B : α → DCode} (hA : Measurable A)
    (hB : Measurable B) : MeasurableSet {f | A f = B f} := by
  have e : {f | A f = B f} = ({f | (A f).1 ≤ (B f).1} ∩ {f | (B f).1 ≤ (A f).1}) ∩
      ⋂ n : ℕ, ⋂ k : ℕ, {f | (A f).2 n k = (B f).2 n k} := by
    ext f
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
    constructor
    · intro h; rw [h]; exact ⟨⟨le_rfl, le_rfl⟩, fun _ _ => rfl⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact Prod.ext (le_antisymm h1 h2) (funext fun n => funext fun k => h3 n k)
  rw [e]
  refine ((measurableSet_le (measurable_fst.comp hA) (measurable_fst.comp hB)).inter
    (measurableSet_le (measurable_fst.comp hB) (measurable_fst.comp hA))).inter
    (MeasurableSet.iInter fun n => MeasurableSet.iInter fun k => ?_)
  exact measurableSet_eq_fun ((measurable_code n k).comp (measurable_snd.comp hA))
    ((measurable_code n k).comp (measurable_snd.comp hB))

theorem measurable_dOf {nL nR : ℕ} : Measurable (dOf (nL := nL) (nR := nR)) :=
  measurable_cζ.prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd))

/-- Two good history codes with the same lifetime and the same driver before it have the same driver code. -/
theorem dOf_eq_of_agree {a a' : ℝ} {nL nR : ℕ} {xL xL' : Fin nL → ℝ} {xR xR' : Fin nR → ℝ}
    {ρL ρL' : Fin nL → ℝ} {ρR ρR' : Fin nR → ℝ} {x x' : XCode nL nR} (hx : x ∈ DetSet a xL xR ρL ρR)
    (hx' : x' ∈ DetSet a' xL' xR' ρL' ρR') (hζ : cζ x = cζ x')
    (hw : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → cw x t = cw x' t) : dOf x = dOf x' := by
  have hz := dOf_mem_DSet hx
  have hz' := dOf_mem_DSet hx'
  refine Prod.ext hζ (funext fun n => funext fun k => ?_)
  by_cases hlt : (dyad n k : ℝ≥0∞) < cζ x
  · have hlt' : (dyad n k : ℝ≥0∞) < cζ x' := hζ ▸ hlt
    rw [← (hz.1 n k hlt).dec_dyad le_rfl, ← (hz'.1 n k hlt').dec_dyad le_rfl]
    exact hw _ hlt
  · have hlt' : ¬ (dyad n k : ℝ≥0∞) < cζ x' := hζ ▸ hlt
    exact (hz.2.2.1 n k hlt).trans (hz'.2.2.1 n k hlt').symm

/-- The frozen driver path agrees with the decoded code before the lifetime and at time `0`. -/
theorem drvPath_dOf_agree {nL nR : ℕ} (x : XCode nL nR) :
    drvPath (dOf x) 0 = cw x 0 ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → drvPath (dOf x) t = cw x t := by
  refine ⟨?_, fun t ht => drvPath_of_lt ht⟩
  by_cases h0 : ((0 : ℝ≥0) : ℝ≥0∞) < cζ x
  · exact drvPath_of_lt h0
  · have hζ : cζ x = 0 := by
      rw [ENNReal.coe_zero] at h0; exact le_antisymm (not_lt.1 h0) zero_le
    have e : ∀ m : ℕ, (dOf x).1.toNNReal - 1 / ((m : ℝ≥0) + 1) = 0 := fun m => by
      simp [dOf, hζ]
    simp only [drvPath, e, limsup_const]
    split_ifs <;> rfl

/-! ### The field-determined realization, with the good set exported -/

section Realization

open WholeField
open scoped unitInterval

/-- **The field-determined realization with the good-set property exported** (a copy of
`Exist.exists_fieldDetermination_realization`, PROVE-FLOWEXIST3, which also records `Ψ f ∈ DetSet` on `S`). For the
reference coupling there are a Borel history code `Ψ` (with a generating trace on a Borel full-measure set `S`, as in
`exists_fieldDetermination`) such that on every probability space carrying a field `h` with the reference law, the
processes `Ψ(h)` together with some filtration and noise form an integrated `SLE_κ(ρ)` evolution. -/
theorem exists_fieldDetermination_realization_det (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) {Ω₀ : Type u}
    {mΩ₀ : MeasurableSpace Ω₀} {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] {𝓕₀ : Filtration ℝ≥0 mΩ₀}
    {W₀ : ℝ≥0 → Ω₀ → ℝ} {VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ}
    {B₀ : ℝ≥0 → Ω₀ → ℝ} {ζ₀ : Ω₀ → ℝ≥0∞} {h₀ : Ω₀ → DistOn upperHalfPlaneOpens}
    (hcoup : IsOptionalHullCoupling κ xL xR ρL ρR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀) :
    ∃ (Ψ : DistOn upperHalfPlaneOpens → XCode nL nR) (S : Set (DistOn upperHalfPlaneOpens))
      (ηf : DistOn upperHalfPlaneOpens → ℝ≥0 → ℂ),
      Measurable Ψ ∧ MeasurableSet S ∧
      (∀ᵐ ω ∂P₀, h₀ ω ∈ S ∧ cζ (Ψ (h₀ ω)) = ζ₀ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ ω →
        cw (Ψ (h₀ ω)) t = W₀ t ω ∧ (∀ i, cvL (Ψ (h₀ ω)) i t = VL₀ i t ω) ∧
          ∀ j, cvR (Ψ (h₀ ω)) j t = VR₀ j t ω) ∧
      (∀ f ∈ S, Ψ f ∈ DetSet κ xL xR ρL ρR) ∧
      (∀ f ∈ S, IsGeneratingTrace (cw (Ψ f)) (cζ (Ψ f)) (ηf f)) ∧
      ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistOn upperHalfPlaneOpens), Measurable h → P.map h = P₀.map h₀ →
        ∃ (𝓕 : Filtration ℝ≥0 mΩ) (B : ℝ≥0 → Ω → ℝ),
          IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 (fun t ω => cw (Ψ (h ω)) t)
            (fun i t ω => cvL (Ψ (h ω)) i t) (fun j t ω => cvR (Ψ (h ω)) j t) B
            (fun ω => cζ (Ψ (h ω))) := by
  obtain ⟨Ψ, S, ηf, B', hΨm, hSm, hB'm, hB'c, hB'0, hB'B, hB'ae, hae, hS⟩ :=
    exists_fieldDetermination_frz h12 h13 hκ hF hcoup
  refine ⟨Ψ, S, ηf, hΨm, hSm, hae.mono fun ω hω => ⟨hω.1, hω.2.2.1, hω.2.2.2⟩,
    fun f hf => (hS f hf).1, fun f hf => (hS f hf).2, ?_⟩
  intro Ω mΩ P hP h hh hlaw
  have hh₀ : Measurable h₀ := hcoup.2.1
  set X₀ : Ω₀ → XCode nL nR := fun ω => Ψ (h₀ ω) with hX₀def
  have hX₀m : Measurable X₀ := hΨm.comp hh₀
  have hX₀ : ∀ᵐ ω ∂P₀, X₀ ω ∈ DetSet κ xL xR ρL ρR ∧ X₀ ω = frz (codeOf xL xR B' W₀ VL₀ VR₀ ζ₀ ω) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ ω → cw (X₀ ω) t = W₀ t ω ∧ (∀ i, cvL (X₀ ω) i t = VL₀ i t ω) ∧
        ∀ j, cvR (X₀ ω) j t = VR₀ j t ω := by
    filter_upwards [hae] with ω hω
    exact ⟨(hS _ hω.1).1, hω.2.1, hω.2.2.2⟩
  obtain ⟨𝓖, hE₀⟩ := model_isIntegratedSLEEvolution hcoup hκ hB'm hB'c hB'0 hB'B hB'ae hX₀m hX₀
  obtain ⟨U, hUm, hU01, hUlaw⟩ :=
    exists_uniform_field hcoup hκ hΨm (hX₀.mono fun ω hω => ⟨hω.1, hω.2.1⟩)
  have hencm := measurable_enc_proc hB'm
  have : IsProbabilityMeasure (P₀.map fun ω => enc fun t => B' t ω) :=
    (Measure.isProbabilityMeasure_map_iff hencm.aemeasurable).2 inferInstance
  obtain ⟨Fw, hFwm, hFw⟩ := (P₀.map fun ω => enc fun t => B' t ω).exists_measurable_map_eq
  set V : DistOn upperHalfPlaneOpens → XCode nL nR × PCode :=
    fun f => (Ψ f, killB (Ψ f) (Fw (projIcc 0 1 zero_le_one (U f)))) with hV
  have hVm : Measurable V := hΨm.prodMk (measurable_killB.comp (hΨm.prodMk
    (hFwm.comp (continuous_projIcc.measurable.comp hUm))))
  have hlawV := map_field_eq_model hh₀ hΨm hUm hU01 hUlaw hB'm hFwm hFw
  -- the good set of code pairs
  set GY : Set (XCode nL nR × PCode) := Prod.fst ⁻¹' DetSet κ xL xR ρL ρR ∩
    ⋂ N : ℕ, Prod.snd ⁻¹' {c : PCode | UC c N} with hGYdef
  have hGYm : MeasurableSet GY :=
    (measurable_fst (measurableSet_detSet κ xL xR ρL ρR)).inter
      (MeasurableSet.iInter fun N => measurable_snd (measurableSet_UC N))
  have hGY : ∀ y ∈ GY, Continuous (noiseY y) ∧ IsIntegratedSLEPath κ xL xR ρL ρR (cw y.1) (cvL y.1)
      (cvR y.1) (noiseY y) (cζ y.1) := by
    rintro y ⟨⟨⟨⟨⟨hg, -, hp⟩, -⟩, -⟩, -⟩, hUC⟩
    have hUC' : ∀ N : ℕ, UC y.2 N := fun N => mem_iInter.1 hUC N
    refine ⟨continuous_noiseY hg.continuous_b (continuous_dec_of_UC hUC'), ?_⟩
    exact isIntegratedSLEPath_congr hp rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) fun t ht => noiseY_of_lt ht
  have hg₀m := measurable_modelMap hX₀m hB'm
  have hmodelGY : ∀ᵐ p ∂(P₀.prod P₀), modelMap X₀ B' p ∈ GY := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hX₀] with p hp
    refine ⟨hp.1, mem_iInter.2 fun N => ?_⟩
    change UC (killB (X₀ p.1) (enc fun t => B' t p.2)) N
    unfold killB
    split_ifs
    · exact uc_enc (hB'c p.2).continuousOn
    · exact uc_enc (f := fun _ => (0 : ℝ)) continuousOn_const
  set g : Ω → XCode nL nR × PCode := fun ω => V (h ω) with hg
  have hgm : Measurable g := hVm.comp hh
  have hlawg : P.map g = (P₀.prod P₀).map (modelMap X₀ B') := by
    rw [show g = V ∘ h from rfl, ← Measure.map_map hVm hh, hlaw]
    exact hlawV
  have hgGY : ∀ᵐ ω ∂P, g ω ∈ GY := by
    have h1 : ∀ᵐ y ∂(P.map g), y ∈ GY := by
      rw [hlawg]; exact (ae_map_iff hg₀m.aemeasurable hGYm).2 hmodelGY
    exact (ae_map_iff hgm.aemeasurable hGYm).1 h1
  exact ⟨_, _, isIntegratedSLEEvolution_of_map_eq (Wy := fun t y => cw y.1 t)
    (VLy := fun i t y => cvL y.1 i t) (VRy := fun j t y => cvR y.1 j t) (ζy := fun y => cζ y.1)
    (By := fun t y => noiseY y t) isMeasurableKilledDriving_codeY measurable_noiseY hg₀m hE₀ hgm hlawg
    (hgGY.mono fun ω hω => (hGY _ hω).1) (hgGY.mono fun ω hω => (hGY _ hω).2)⟩

end Realization

/-- **The field-determined driver realizes an optional hull coupling** on one probability space. -/
theorem isOptionalHullCoupling_drv (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u}) {κ : ℝ}
    (hκ : 0 < κ) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) {Ω : Type u} [mΩ : MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsGFFWithBoundaryData Q h₀ (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR))
    {E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : Measurable E)
    (hE : ∀ᵐ ω ∂Q, E ω = drvOf (detCode (paramΦ h12p hκ nL nR) (((xL, xR), (ρL, ρR)), h₀ ω))) :
    ∃ (𝓕 : Filtration ℝ≥0 mΩ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ),
      IsOptionalHullCoupling κ xL xR ρL ρR Q 𝓕 (fun t ω => (E ω).1 t) VL VR B (fun ω => (E ω).2) h₀ := by
  set Φ := paramΦ h12p hκ nL nR with hΦdef
  have hΦm : Measurable Φ := measurable_paramΦ h12p hκ nL nR
  have h12 : Theorem12Statement.{u} := theorem12Statement_of_param h12p
  -- the reference coupling (sealed Theorem 1.1) and its field-determined realization
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hr, hcoup⟩ :=
    Spec.Provider.exists_isOptionalHullCoupling.{u} (κ := κ) (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR) hκ hF
  obtain ⟨Ψ, S, ηf, hΨm, hSm, hae, hSdet, -, hreal⟩ :=
    exists_fieldDetermination_realization_det h12 h13 hκ hF hcoup
  obtain ⟨u, hu, -⟩ := Spec.Provider.existsUnique_isBoundedHarmonicExtension_forceBoundaryData (κ := κ)
    (ρL := ρL) (ρR := ρR) (vL := xL) (vR := xR)
  have hr' : IsGFFWithBoundaryData P₀ hr (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) :=
    ⟨hcoup.2.1, hcoup.2.2.1⟩
  have hlaw : Q.map h₀ = P₀.map hr := map_eq_of_isGFFWithBoundaryData hh₀ hr' hu
  -- the realization on `(Ω, Q)`, on the usual augmentation
  obtain ⟨𝓕, B, hEv⟩ := hreal Q h₀ hh₀.1 hlaw
  have hEa := Ito.isIntegratedSLEEvolution_usualAugmentation hEv
  have hdet : ∀ᵐ ω ∂P₀, (pathsOfCode (Ψ (hr ω))).1 = ζ₀ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ ω →
      (pathsOfCode (Ψ (hr ω))).2.1 t = W₀ t ω ∧ (∀ i, (pathsOfCode (Ψ (hr ω))).2.2.1 i t = VL₀ i t ω) ∧
        ∀ j, (pathsOfCode (Ψ (hr ω))).2.2.2 j t = VR₀ j t ω := by
    filter_upwards [hae] with ω hω
    exact ⟨hω.2.1, hω.2.2⟩
  have hdatum : IsFieldRealizationDatum κ xL xR ρL ρR (pathsOfCode ∘ Ψ) Q h₀ :=
    ⟨hκ, hF, measurable_pathsOfCode.comp hΨm, hh₀.1, Ω₀, mΩ₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hr, hcoup,
      hdet, hlaw⟩
  have hC := hullClauseTransferStatement κ _ _ _ _ (pathsOfCode ∘ Ψ) Q h₀ hdatum _ B hEa
  -- the determined driver code is the realized one almost everywhere for the reference law
  have hdetm : Measurable fun f : DistOn upperHalfPlaneOpens => detCode Φ (((xL, xR), (ρL, ρR)), f) :=
    (measurable_detCode hΦm).comp (measurable_const.prodMk measurable_id)
  have hAm : MeasurableSet {f : DistOn upperHalfPlaneOpens |
      detCode Φ (((xL, xR), (ρL, ρR)), f) = dOf (Ψ f)} :=
    measurableSet_eq_dCode hdetm (measurable_dOf.comp hΨm)
  have href : ∀ᵐ f ∂(P₀.map hr), detCode Φ (((xL, xR), (ρL, ρR)), f) = dOf (Ψ f) := by
    refine (ae_map_iff hcoup.2.1.aemeasurable hAm).2 ?_
    filter_upwards [ae_detCode_eq hκ hF h13 hcoup ((h12p κ hκ nL nR).choose_spec.2 xL xR ρL ρR hF hcoup), hae] with ω ⟨x₀, hx₀, hζx, hwx, hcode⟩ hω
    have hcode' : detCode Φ (((xL, xR), (ρL, ρR)), hr ω) = dOf x₀ := hcode
    rw [hcode']
    refine dOf_eq_of_agree hx₀ (hSdet _ hω.1) (hζx.trans hω.2.1.symm) fun t ht => ?_
    rw [hζx] at ht
    exact ((hwx t ht).1).trans ((hω.2.2 t ht).1).symm
  rw [← hlaw] at href
  have hQ : ∀ᵐ ω ∂Q, detCode Φ (((xL, xR), (ρL, ρR)), h₀ ω) = dOf (Ψ (h₀ ω)) :=
    (ae_map_iff hh₀.1.aemeasurable hAm).1 href
  -- move the coupling to `E`
  have hX' : IsMeasurableKilledDriving (fun t ω => (E ω).1 t) (fun i t ω => cvL (Ψ (h₀ ω)) i t)
      (fun j t ω => cvR (Ψ (h₀ ω)) j t) (fun ω => (E ω).2) := by
    intro t A hA
    refine (measurableSet_lt measurable_const (measurable_snd.comp hEm)).inter (hA.preimage ?_)
    refine ((measurable_pi_apply t).comp (measurable_fst.comp hEm)).prodMk
      ((measurable_pi_iff.2 fun i => (measurable_cvL_at i t).comp (hΨm.comp hh₀.1)).prodMk
        (measurable_pi_iff.2 fun j => (measurable_cvR_at j t).comp (hΨm.comp hh₀.1)))
  refine ⟨_, _, _, B, IsOptionalHullCoupling.congr_ae hC
    (fun t N hN h0 => Ito.measurableSet_usualAugmentation_of_null hN h0 t) hX' ?_⟩
  have hSQ : ∀ᵐ ω ∂Q, h₀ ω ∈ S := by
    have h1 : ∀ᵐ f ∂(P₀.map hr), f ∈ S :=
      (ae_map_iff hcoup.2.1.aemeasurable hSm).2 (hae.mono fun ω hω => hω.1)
    rw [← hlaw] at h1
    exact (ae_map_iff hh₀.1.aemeasurable hSm).1 h1
  filter_upwards [hE, hQ, hSQ] with ω hEω hQω hSω
  rw [hEω, hQω, drvOf_of_mem (dOf_mem_DSet (hSdet _ hSω))]
  exact ⟨rfl, (drvPath_dOf_agree _).1, (drvPath_dOf_agree _).2⟩

/-! ### The staged driver on the whole space -/

/-- Padded force-word data: positions and weights indexed by `ℕ` (only the first `nL`, `nR` entries are used). -/
abbrev PadWord : Type := ((ℕ → ℝ) × (ℕ → ℝ)) × ((ℕ → ℝ) × (ℕ → ℝ))

/-- The word with `m` left and `n` right marks read off padded data. -/
def truncWord (m n : ℕ) (p : PadWord) : WordData m n :=
  (((fun i : Fin m => p.1.1 i), fun j : Fin n => p.1.2 j), ((fun i : Fin m => p.2.1 i), fun j : Fin n => p.2.2 j))

theorem measurable_truncWord (m n : ℕ) : Measurable (truncWord m n) := by
  unfold truncWord
  refine ((measurable_pi_iff.2 fun i => (measurable_pi_apply _).comp (measurable_fst.comp measurable_fst)).prodMk
    (measurable_pi_iff.2 fun j => (measurable_pi_apply _).comp (measurable_snd.comp measurable_fst))).prodMk
    ((measurable_pi_iff.2 fun i => (measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)).prodMk
    (measurable_pi_iff.2 fun j => (measurable_pi_apply _).comp (measurable_snd.comp measurable_snd)))

/-- **The staged driver**: at a sample with past `x` and field `f`, the field-determined driver of the word read off
`x`. -/
def stagedDrv (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) {R : Type*} (nLf nRf : R → ℕ)
    (pw : R → PadWord) (x : R) (f : DistOn upperHalfPlaneOpens) : (ℝ≥0 → ℝ) × ℝ≥0∞ :=
  drvOf (detCode (paramΦ h12p hκ (nLf x) (nRf x)) (truncWord (nLf x) (nRf x) (pw x), f))

/-- **The staged driver is regular at every sample** (`drvOf_regular`). -/
theorem stagedDrv_regular (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) {R : Type*} (nLf nRf : R → ℕ)
    (pw : R → PadWord) (x : R) (f : DistOn upperHalfPlaneOpens) :
    ContinuousOn (stagedDrv h12p hκ nLf nRf pw x f).1 {t | (t : ℝ≥0∞) < (stagedDrv h12p hκ nLf nRf pw x f).2} ∧
      (stagedDrv h12p hκ nLf nRf pw x f).1 0 = 0 ∧
      (∀ t : ℝ≥0, (stagedDrv h12p hκ nLf nRf pw x f).2 ≤ t → (stagedDrv h12p hκ nLf nRf pw x f).1 t =
        (stagedDrv h12p hκ nLf nRf pw x f).1 (stagedDrv h12p hκ nLf nRf pw x f).2.toNNReal) ∧
      ((stagedDrv h12p hκ nLf nRf pw x f).2 ≠ ⊤ → 0 < (stagedDrv h12p hκ nLf nRf pw x f).2 → ∀ c : ℝ,
        Tendsto (stagedDrv h12p hκ nLf nRf pw x f).1
          (𝓝[<] (stagedDrv h12p hκ nLf nRf pw x f).2.toNNReal) (𝓝 c) →
        (stagedDrv h12p hκ nLf nRf pw x f).1 (stagedDrv h12p hκ nLf nRf pw x f).2.toNNReal = c) :=
  drvOf_regular _

theorem measurable_stagedDrv (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) {R : Type*}
    [MeasurableSpace R] {nLf nRf : R → ℕ} (hnL : Measurable nLf) (hnR : Measurable nRf) {pw : R → PadWord}
    (hpw : Measurable pw) :
    Measurable fun p : R × DistOn upperHalfPlaneOpens => stagedDrv h12p hκ nLf nRf pw p.1 p.2 := by
  set F : (R × DistOn upperHalfPlaneOpens) × (ℕ × ℕ) → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun q =>
    drvOf (detCode (paramΦ h12p hκ q.2.1 q.2.2) (truncWord q.2.1 q.2.2 (pw q.1.1), q.1.2)) with hF
  have hFm : Measurable F := by
    refine measurable_from_prod_countable_left fun mn => ?_
    exact measurable_drvOf.comp ((measurable_detCode (measurable_paramΦ h12p hκ mn.1 mn.2)).comp
      (((measurable_truncWord mn.1 mn.2).comp (hpw.comp measurable_fst)).prodMk measurable_snd))
  have e : (fun p : R × DistOn upperHalfPlaneOpens => stagedDrv h12p hκ nLf nRf pw p.1 p.2) =
      fun p => F (p, (nLf p.1, nRf p.1)) := rfl
  rw [e]
  exact hFm.comp (measurable_id.prodMk ((hnL.comp measurable_fst).prodMk (hnR.comp measurable_fst)))

/-- **Step (c): one measurable driver realizes the field-determined coupling under the kernel at almost every
`ω₀`.** For a measurable past `r` with values in a standard Borel space, measurable numbers of marks and padded word
data read off the past, and a measurable field `Y`: for `P`-a.e. `ω₀`, whenever the word read off `r ω₀` is ordered and
a measurable field `h₀`, equal to `Y` almost surely under the kernel, is a GFF with the word's force-boundary data
under the kernel, the driver `E` and `h₀` form an optional hull coupling under the kernel. -/
theorem exists_drv_condKernel (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u}) {κ : ℝ}
    (hκ : 0 < κ) {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {R : Type*} [MeasurableSpace R] [StandardBorelSpace R] {r : Ω → R}
    (hr : Measurable r) {nLf nRf : R → ℕ} (hnL : Measurable nLf) (hnR : Measurable nRf) {pw : R → PadWord}
    (hpw : Measurable pw) {Y : Ω → DistOn upperHalfPlaneOpens} (hY : Measurable Y) :
    ∃ E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, Measurable E ∧
      (∀ ω, E ω = stagedDrv h12p hκ nLf nRf pw (r ω) (Y ω)) ∧
      ∀ᵐ ω₀ ∂P, ∀ h₀ : Ω → DistOn upperHalfPlaneOpens,
        IsOrderedForceWord (truncWord (nLf (r ω₀)) (nRf (r ω₀)) (pw (r ω₀))).1.1
          (truncWord (nLf (r ω₀)) (nRf (r ω₀)) (pw (r ω₀))).1.2 →
        (∀ᵐ ω ∂(condExpKernel P (MeasurableSpace.comap r inferInstance) ω₀), Y ω = h₀ ω) →
        IsGFFWithBoundaryData (condExpKernel P (MeasurableSpace.comap r inferInstance) ω₀) h₀
          (forceBoundaryData κ (truncWord (nLf (r ω₀)) (nRf (r ω₀)) (pw (r ω₀))).2.1
            (truncWord (nLf (r ω₀)) (nRf (r ω₀)) (pw (r ω₀))).2.2
            (truncWord (nLf (r ω₀)) (nRf (r ω₀)) (pw (r ω₀))).1.1
            (truncWord (nLf (r ω₀)) (nRf (r ω₀)) (pw (r ω₀))).1.2)
          (forceJumpSet (truncWord (nLf (r ω₀)) (nRf (r ω₀)) (pw (r ω₀))).1.1
            (truncWord (nLf (r ω₀)) (nRf (r ω₀)) (pw (r ω₀))).1.2) →
        ∃ (𝓕 : Filtration ℝ≥0 mΩ) (VL : Fin (nLf (r ω₀)) → ℝ≥0 → Ω → ℝ)
          (VR : Fin (nRf (r ω₀)) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ),
          IsOptionalHullCoupling κ (truncWord (nLf (r ω₀)) (nRf (r ω₀)) (pw (r ω₀))).1.1
            (truncWord (nLf (r ω₀)) (nRf (r ω₀)) (pw (r ω₀))).1.2
            (truncWord (nLf (r ω₀)) (nRf (r ω₀)) (pw (r ω₀))).2.1
            (truncWord (nLf (r ω₀)) (nRf (r ω₀)) (pw (r ω₀))).2.2
            (condExpKernel P (MeasurableSpace.comap r inferInstance) ω₀) 𝓕 (fun t ω => (E ω).1 t) VL VR B
            (fun ω => (E ω).2) h₀ := by
  set E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun ω => stagedDrv h12p hκ nLf nRf pw (r ω) (Y ω) with hEdef
  have hEm : Measurable E := (measurable_stagedDrv h12p hκ hnL hnR hpw).comp (hr.prodMk hY)
  refine ⟨E, hEm, fun _ => rfl, ?_⟩
  filter_upwards [ae_ae_eq_of_comap (P := P) hr] with ω₀ hatom h₀ hF hYh hh₀
  refine isOptionalHullCoupling_drv h12p h13 hκ hF hh₀ hEm ?_
  filter_upwards [hatom, hYh] with ω hrω hYω
  change stagedDrv h12p hκ nLf nRf pw (r ω) (Y ω) = _
  rw [hYω, hrω]
  rfl

end Staged

end Exist

end InteractingSLE
