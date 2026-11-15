/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.CanonicalMain
import InteractingSLE.WangWu.Prop418RangeMain
import InteractingSLE.WangWu.ReverseContactGlue
import InteractingSLE.WangWu.ImgChartConstMarks

/-!
# Seed lines of a given field at `κ = 4` (Wang–Wu §4.4: "Let `β` be its zero-height seed and let `α` be its height-`u`
seed. Both are simple proper arcs from `0` to `∞`, determined by the field, by Proposition 4.18")

Packet PROVE-WW-B20. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), Proposition 4.19
(L1655–L1708) and Proposition 4.24 (L1816–L1867): both start from **one** field `h` and several seed lines of it, each
of which is the level line of a shifted field and is determined by the field (Proposition 4.18).

This file realises, on **every** probability space carrying a field with the right law, the coupling of a nonnegative
two-seed word at `κ = 4` with that very field (**`exists_isOptionalHullCoupling_twoSeed_of_field`**): the `κ =
4` seed-line
counterpart of the specification's flow-line construction `Exist.exists_isFlowLine_of_thm12_thm13_only`. That
construction takes its determination map and traces from the frozen Theorems 1.2–1.3; here they come from the
nonnegative-word results of Proposition 4.18 (`hasFieldDeterminedHistories_twoSeed_of_contact` with the proved contact
step `reverseTipContactStatement`, and `isCompleteForceWord_twoSeed`). So nothing here uses Theorem 1.2, Theorem 1.3 or
any `*_of_param` result (rulings R43, R48).

* `exists_fieldDetermination_frz_of`, `exists_fieldDetermination_realization_of`: `Exist.exists_fieldDetermination_frz`
  and `Exist.exists_fieldDetermination_realization` with the two uses of the frozen Theorems 1.2–1.3 replaced by their
  conclusions **for the one reference coupling** (a Borel lifetime-and-trace map of its field and an almost sure
  generating trace);
* `exists_isOptionalHullCoupling_of_field_of`: from such a reference, every probability space (same universe) carrying
  a field with the reference law carries an optional hull coupling of the word with that field
  (`Exist.hullClauseTransferStatement`, proved);
* **`exists_isOptionalHullCoupling_twoSeed_of_field`**: the nonnegative two-seed words at `κ = 4`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal unitInterval

universe u

namespace InteractingSLE.WangWu.SeedField

open LQGMetric Sec2.Assembly WholeField Exist

variable {nL nR : ℕ}

/-! ### The canonical code of a reference coupling, from its own determination and trace -/

/-- **`Exist.exists_fieldDetermination_frz` from one reference coupling**: the two inputs taken from the frozen
Theorems 1.2–1.3 there are only used for the given coupling, so their conclusions for that coupling suffice. -/
theorem exists_fieldDetermination_frz_of {κ : ℝ} (hκ : 0 < κ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω₀ : Type*} {mΩ₀ : MeasurableSpace Ω₀}
    {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] {𝓕₀ : Filtration ℝ≥0 mΩ₀} {W₀ : ℝ≥0 → Ω₀ → ℝ}
    {VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ} {B₀ : ℝ≥0 → Ω₀ → ℝ}
    {ζ₀ : Ω₀ → ℝ≥0∞} {h₀ : Ω₀ → LQGMetric.DistOn upperHalfPlaneOpens}
    (hcoup : IsOptionalHullCoupling κ xL xR ρL ρR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀)
    (hdet : ∃ Φ : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ), Measurable Φ ∧
      ∀ᵐ ω ∂P₀, (Φ (h₀ ω)).1 = ζ₀ ω ∧
        ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₀ t ω) (ζ₀ ω) η →
          ∀ t : ℝ≥0, (Φ (h₀ ω)).2 t = η (min (t : ℝ≥0∞) (ζ₀ ω)).toNNReal)
    (htr : ∀ᵐ ω ∂P₀, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₀ t ω) (ζ₀ ω) η) :
    ∃ (Ψ : LQGMetric.DistOn upperHalfPlaneOpens → XCode nL nR)
      (S : Set (LQGMetric.DistOn upperHalfPlaneOpens))
      (ηf : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0 → ℂ) (B' : ℝ≥0 → Ω₀ → ℝ),
      Measurable Ψ ∧ MeasurableSet S ∧ (∀ t, Measurable (B' t)) ∧ (∀ ω, Continuous (B' · ω)) ∧
      (∀ ω, B' 0 ω = 0) ∧ ProbabilityTheory.IsBrownianReal B' P₀ ∧ (∀ᵐ ω ∂P₀, ∀ t, B' t ω = B₀ t ω) ∧
      (∀ᵐ ω ∂P₀, h₀ ω ∈ S ∧ Ψ (h₀ ω) = frz (codeOf xL xR B' W₀ VL₀ VR₀ ζ₀ ω) ∧
        cζ (Ψ (h₀ ω)) = ζ₀ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ ω →
        cw (Ψ (h₀ ω)) t = W₀ t ω ∧ (∀ i, cvL (Ψ (h₀ ω)) i t = VL₀ i t ω) ∧
          ∀ j, cvR (Ψ (h₀ ω)) j t = VR₀ j t ω) ∧
      ∀ f ∈ S, Ψ f ∈ DetSet κ xL xR ρL ρR ∧ IsGeneratingTrace (cw (Ψ f)) (cζ (Ψ f)) (ηf f) := by
  have hE := hcoup.1
  obtain ⟨Φ, hΦm, hΦ⟩ := hdet
  obtain ⟨B', hB'm, hB'c, hB'0, hB'B, hB'ae⟩ := QuantumZipper.RS.exists_good_version0 hE.1.1
  obtain ⟨G, hGm, hG⟩ := exists_measurable_leftInverse_of_injOn
    (measurable_traceOfCode (nL := nL) (nR := nR)) (measurableSet_detSet κ xL xR ρL ρR)
    (injOn_traceOfCode hκ)
  refine ⟨G ∘ codeΦ Φ, GoodField Φ G κ xL xR ρL ρR, traceOfΦ Φ, B', hGm.comp (measurable_codeΦ hΦm),
    measurableSet_goodField hΦm hGm κ xL xR ρL ρR, hB'm, hB'c, hB'0, hB'B, hB'ae, ?_,
    fun f hf => ⟨hf.1, isGeneratingTrace_of_mem_goodField hf⟩⟩
  filter_upwards [hΦ, htr, ae_codeOf_mem hκ hE hB'c hB'ae] with ω hΦω h13ω hcode
  obtain ⟨η, hη⟩ := h13ω
  obtain ⟨hx₁, hdec⟩ := hcode
  set x₀ := frz (codeOf xL xR B' W₀ VL₀ VR₀ ζ₀ ω) with hx₀def
  have hζx : cζ x₀ = ζ₀ ω := rfl
  have hcwx : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ ω → cw x₀ t = W₀ t ω := fun t ht => (hdec t ht).1
  have hηx : IsGeneratingTrace (cw x₀) (ζ₀ ω) η := Sec7.IsGeneratingTrace.congr_lt hη hcwx
  have hcrel : x₀ ∈ CRel κ xL xR ρL ρR := frz_mem_cRel hx₁
  have hmem : x₀ ∈ DetSet κ xL xR ρL ρR :=
    ⟨⟨hcrel, frozenB_frz hx₁.1.1⟩, fun n k hT => mem_traceSet_of_isGeneratingTrace hcrel hT hηx hT.le⟩
  have hcode : traceOfCode x₀ = codeΦ Φ (h₀ ω) := by
    refine Prod.ext hΦω.1.symm (funext fun n => funext fun k => ?_)
    simp only [traceOfCode, codeΦ, hζx, hΦω.1]
    by_cases hlt : ((dyad n k : ℝ≥0) : ℝ≥0∞) < ζ₀ ω
    · simp only [hlt, ↓reduceIte]
      rw [hΦω.2 η hη, min_eq_left hlt.le, ENNReal.toNNReal_coe]
      exact LP.traceAt_eq_of_isGeneratingTrace hηx hcrel.1.1.continuousOn_w hcrel.1.2.2.1 hlt
    · simp only [hlt, ↓reduceIte]
  have hΨ : G (codeΦ Φ (h₀ ω)) = x₀ := by rw [← hcode]; exact hG x₀ hmem
  have hγ := continuous_trace_min hη.2.1
  have hre : reCode Φ (h₀ ω) = enc fun t => (η (min (t : ℝ≥0∞) (ζ₀ ω)).toNNReal).re := by
    funext n k; simp only [reCode, enc, hΦω.2 η hη]
  have him : imCode Φ (h₀ ω) = enc fun t => (η (min (t : ℝ≥0∞) (ζ₀ ω)).toNNReal).im := by
    funext n k; simp only [imCode, enc, hΦω.2 η hη]
  refine ⟨⟨by simp only [hΨ]; exact hmem, by simp only [hΨ]; exact hcode,
    fun N => ⟨hre ▸ uc_enc (Complex.continuous_re.comp hγ).continuousOn,
      him ▸ uc_enc (Complex.continuous_im.comp hγ).continuousOn⟩, ?_⟩, by simp only [Function.comp_apply, hΨ], ?_,
      fun t ht => ?_⟩
  · rw [hΦω.2 η hη]
    simpa using hη.1
  · simp only [Function.comp_apply, hΨ]; rfl
  · simp only [Function.comp_apply, hΨ]
    exact ⟨(hdec t ht).1, (hdec t ht).2.1, (hdec t ht).2.2.1⟩

/-- **`Exist.exists_fieldDetermination_realization` from one reference coupling** (its determination map and its traces
as hypotheses instead of the frozen Theorems 1.2–1.3). -/
theorem exists_fieldDetermination_realization_of {κ : ℝ} (hκ : 0 < κ) {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω₀ : Type u}
    {mΩ₀ : MeasurableSpace Ω₀} {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] {𝓕₀ : Filtration ℝ≥0 mΩ₀}
    {W₀ : ℝ≥0 → Ω₀ → ℝ} {VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ}
    {B₀ : ℝ≥0 → Ω₀ → ℝ} {ζ₀ : Ω₀ → ℝ≥0∞} {h₀ : Ω₀ → DistOn upperHalfPlaneOpens}
    (hcoup : IsOptionalHullCoupling κ xL xR ρL ρR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀)
    (hdet : ∃ Φ : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ), Measurable Φ ∧
      ∀ᵐ ω ∂P₀, (Φ (h₀ ω)).1 = ζ₀ ω ∧
        ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₀ t ω) (ζ₀ ω) η →
          ∀ t : ℝ≥0, (Φ (h₀ ω)).2 t = η (min (t : ℝ≥0∞) (ζ₀ ω)).toNNReal)
    (htr : ∀ᵐ ω ∂P₀, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₀ t ω) (ζ₀ ω) η) :
    ∃ (Ψ : DistOn upperHalfPlaneOpens → XCode nL nR) (S : Set (DistOn upperHalfPlaneOpens))
      (ηf : DistOn upperHalfPlaneOpens → ℝ≥0 → ℂ),
      Measurable Ψ ∧ MeasurableSet S ∧
      (∀ᵐ ω ∂P₀, h₀ ω ∈ S ∧ cζ (Ψ (h₀ ω)) = ζ₀ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ ω →
        cw (Ψ (h₀ ω)) t = W₀ t ω ∧ (∀ i, cvL (Ψ (h₀ ω)) i t = VL₀ i t ω) ∧
          ∀ j, cvR (Ψ (h₀ ω)) j t = VR₀ j t ω) ∧
      (∀ f ∈ S, IsGeneratingTrace (cw (Ψ f)) (cζ (Ψ f)) (ηf f)) ∧
      ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistOn upperHalfPlaneOpens), Measurable h → P.map h = P₀.map h₀ →
        ∃ (𝓕 : Filtration ℝ≥0 mΩ) (B : ℝ≥0 → Ω → ℝ),
          IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 (fun t ω => cw (Ψ (h ω)) t)
            (fun i t ω => cvL (Ψ (h ω)) i t) (fun j t ω => cvR (Ψ (h ω)) j t) B
            (fun ω => cζ (Ψ (h ω))) := by
  obtain ⟨Ψ, S, ηf, B', hΨm, hSm, hB'm, hB'c, hB'0, hB'B, hB'ae, hae, hS⟩ :=
    exists_fieldDetermination_frz_of hκ hcoup hdet htr
  refine ⟨Ψ, S, ηf, hΨm, hSm, hae.mono fun ω hω => ⟨hω.1, hω.2.2.1, hω.2.2.2⟩,
    fun f hf => (hS f hf).2, ?_⟩
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

/-! ### Couplings of a given field -/

/-- **A coupling of a given field, from one determined reference** (the construction of
`Exist.exists_isFlowLine_of_thm12_thm13_only`, with the reference's own determination and traces): if one coupling of
an ordered word has a field-determined killed history and almost surely a generating trace, then every probability
space (same universe) carrying a field with its law carries an optional hull coupling of the word with that field. -/
theorem exists_isOptionalHullCoupling_of_field_of {κ : ℝ} (hκ : 0 < κ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) {Ω₀ : Type u}
    {mΩ₀ : MeasurableSpace Ω₀} {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] {𝓕₀ : Filtration ℝ≥0 mΩ₀}
    {W₀ : ℝ≥0 → Ω₀ → ℝ} {VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ}
    {B₀ : ℝ≥0 → Ω₀ → ℝ} {ζ₀ : Ω₀ → ℝ≥0∞} {h₀ : Ω₀ → DistOn upperHalfPlaneOpens}
    (hcoup : IsOptionalHullCoupling κ xL xR ρL ρR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀)
    (hdet : LP.IsFieldDeterminedHistory P₀ h₀ W₀ VL₀ VR₀ ζ₀)
    (htr : ∀ᵐ ω ∂P₀, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₀ t ω) (ζ₀ ω) η)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) (hlaw : P.map h = P₀.map h₀) :
    ∃ (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞), IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h := by
  obtain ⟨Ψ, S, ηf, hΨm, hSm, hae, -, hreal⟩ := exists_fieldDetermination_realization_of hκ hcoup
    (LP.exists_measurable_lifetime_trace_eq_comp_field_of_isFieldDeterminedHistory hcoup hdet) htr
  obtain ⟨𝓕, B, hE⟩ := hreal P h hh hlaw
  have hdet' : ∀ᵐ ω ∂P₀, (pathsOfCode (Ψ (h₀ ω))).1 = ζ₀ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ ω →
      (pathsOfCode (Ψ (h₀ ω))).2.1 t = W₀ t ω ∧ (∀ i, (pathsOfCode (Ψ (h₀ ω))).2.2.1 i t = VL₀ i t ω) ∧
        ∀ j, (pathsOfCode (Ψ (h₀ ω))).2.2.2 j t = VR₀ j t ω := by
    filter_upwards [hae] with ω hω
    exact ⟨hω.2.1, hω.2.2⟩
  have hdatum : IsFieldRealizationDatum κ xL xR ρL ρR (pathsOfCode ∘ Ψ) P h :=
    ⟨hκ, hF, measurable_pathsOfCode.comp hΨm, hh, Ω₀, mΩ₀, P₀, inferInstance, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, h₀, hcoup,
      hdet', hlaw⟩
  exact ⟨𝓕, _, _, _, B, _, hullClauseTransferStatement κ _ _ _ _ (pathsOfCode ∘ Ψ) P h hdatum 𝓕 B hE⟩

/-- **The seed line of a given field at `κ = 4`** (Proposition 4.18 for the nonnegative two-seed words, realised on the
field's own space): for `ρL, ρR ≥ 0` and every probability space carrying a GFF `h` with the two-seed boundary data
`−λ(1 + ρL)` on `ℝ₋`, `λ(1 + ρR)` on `ℝ₊`, there is an optional hull coupling of `SLE₄(ρL; ρR)` (force points `0−, 0+`)
with the field `h` on that space. -/
theorem exists_isOptionalHullCoupling_twoSeed_of_field {rL rR : ℝ} (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) LP.twoSeedXL
      LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR)) :
    ∃ (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (ζ : Ω → ℝ≥0∞),
      IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h := by
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, h₀, hcoup⟩ :=
    Spec.Provider.exists_isOptionalHullCoupling.{u} (κ := 4) (xL := LP.twoSeedXL) (xR := LP.twoSeedXR)
      (ρL := fun _ : Fin 1 => rL) (ρR := fun _ : Fin 1 => rR) (by norm_num) LP.isOrderedForceWord_twoSeed
  have hdet := hasFieldDeterminedHistories_twoSeed_of_contact.{u, 0} reverseTipContactStatement hL hR P₀ 𝓕₀ W₀ VL₀
    VR₀ B₀ ζ₀ h₀ hcoup
  have htr : ∀ᵐ ω ∂P₀, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₀ t ω) (ζ₀ ω) η := by
    filter_upwards [isCompleteForceWord_twoSeed.{u} hL hR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ hcoup.1] with ω hω
    obtain ⟨η, hη, -⟩ := hω
    exact ⟨η, hη⟩
  obtain ⟨u₀, hu, -⟩ := Spec.Provider.existsUnique_isBoundedHarmonicExtension_forceBoundaryData (κ := 4)
    (ρL := fun _ : Fin 1 => rL) (ρR := fun _ : Fin 1 => rR) (vL := LP.twoSeedXL) (vR := LP.twoSeedXR)
  have hh₀ : IsGFFWithBoundaryData P₀ h₀ (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) := ⟨hcoup.2.1, hcoup.2.2.1⟩
  exact exists_isOptionalHullCoupling_of_field_of (by norm_num) LP.isOrderedForceWord_twoSeed hcoup hdet htr hh.1
    (map_eq_of_isGFFWithBoundaryData hh hh₀ hu)

end InteractingSLE.WangWu.SeedField
