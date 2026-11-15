/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.CanonicalModel

/-!
# Named input (ii) proved: a Brownian continuation from the field; flow lines exist from Theorems 1.2–1.3

Packet PROVE-FLOWEXIST3 (AUD-3c N1, `Exist.CanonicalBrownianStatement` in its code form). Let `Ψ` be the Borel history
code of the reference coupling (`Exist.exists_fieldDetermination_frz`) and `U` the uniform variable built from the field
(`Exist.exists_uniform_field`). Represent the law `ν_W` of the code of a Brownian motion as the image of the uniform
law on `[0, 1]` (`Measure.exists_measurable_map_eq`, `F_W : [0, 1] → PCode`) and put
`V(f) = F_W(U(f))` on `{cζ(Ψ f) < ∞}`, `0` otherwise.

* **`map_field_eq_model`**: the law of `(Ψ, V)` under the field law is the law of the model map `(X₀(ω), B'(ω'))` under
  `P ⊗ P` (rectangles: `(Ψ, U)` is a product on `{cζ < ∞}`, and `V` is killed on `{cζ = ∞}` on both sides);
* **`exists_fieldDetermination_realization`**: for every space carrying a field `h` with the reference law, the
  processes `Ψ(h)` with the noise `noiseY(Ψ(h), V(h))` form an integrated evolution
  (`Exist.isIntegratedSLEEvolution_of_map_eq` from the model, `Exist.model_isIntegratedSLEEvolution`);
* **`exists_isFlowLine_of_thm12_thm13_only`**: the frozen `exists_isFlowLine` (provider shape) from the frozen
  Theorems 1.2 and 1.3 alone (named inputs (i) and (ii) are both proved).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal unitInterval

namespace InteractingSLE

namespace Exist

open LQGMetric Sec2.Assembly WholeField

variable {nL nR : ℕ}

/-! ### The uniform law on `[0, 1]` -/

theorem map_projIcc_volume :
    (volume.restrict (Icc (0 : ℝ) 1)).map (projIcc (0 : ℝ) 1 zero_le_one) = (volume : Measure I) := by
  rw [← unitInterval.measurePreserving_coe.map_eq, Measure.map_map continuous_projIcc.measurable
    measurable_subtype_coe]
  have : projIcc (0 : ℝ) 1 zero_le_one ∘ Subtype.val = (id : I → I) := funext fun x => projIcc_val zero_le_one x
  rw [this, Measure.map_id]

/-- A uniform variable on a set: the law of `U` restricted to `S` is `μ(S)` times the uniform law, from the
distribution function on `[0, 1]`. -/
theorem map_restrict_eq_of_cdf {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {S : Set α} {U : α → ℝ} (hUm : Measurable U) (hU01 : ∀ a, 0 ≤ U a ∧ U a ≤ 1)
    (hcdf : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → μ (S ∩ {a | U a ≤ u}) = μ S * ENNReal.ofReal u) :
    (μ.restrict S).map U = μ S • volume.restrict (Icc (0 : ℝ) 1) := by
  refine Measure.ext_of_Iic _ _ fun u => ?_
  rw [Measure.map_apply hUm measurableSet_Iic, Measure.restrict_apply (hUm measurableSet_Iic),
    Measure.smul_apply, Measure.restrict_apply measurableSet_Iic, smul_eq_mul]
  have hpre : U ⁻¹' Iic u ∩ S = S ∩ {a | U a ≤ u} := by
    ext a; simp [and_comm]
  rw [hpre]
  rcases lt_or_ge u 0 with hu | hu
  · have h1 : S ∩ {a | U a ≤ u} = ∅ := by
      ext a; simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
      exact fun _ => lt_of_lt_of_le hu (hU01 a).1
    have h2 : Iic u ∩ Icc (0 : ℝ) 1 = ∅ := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false, not_and]
      intro hx h0; linarith
    rw [h1, h2, measure_empty, measure_empty, mul_zero]
  rcases le_or_gt u 1 with hu1 | hu1
  · rw [hcdf u hu hu1]
    congr 1
    have : Iic u ∩ Icc (0 : ℝ) 1 = Icc 0 u := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hu1⟩
    rw [this, Real.volume_Icc, sub_zero]
  · have h1 : S ∩ {a | U a ≤ u} = S := by
      ext a; simp only [mem_inter_iff, mem_ofPred_eq, and_iff_left_iff_imp]
      exact fun _ => ((hU01 a).2).trans hu1.le
    have h2 : Iic u ∩ Icc (0 : ℝ) 1 = Icc 0 1 := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc, and_iff_right_iff_imp]
      exact fun hx => hx.2.trans hu1.le
    rw [h1, h2, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]

/-! ### The law of the field-side construction is the model law -/

section Law

/-- **The law identity.** Under the field law `μ = P₀ ∘ h₀⁻¹`, the pair (history code, Brownian code built from the
field) has the law of the model map under `P₀ ⊗ P₀`. -/
theorem map_field_eq_model {Ω₀ : Type*} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
    {h₀ : Ω₀ → DistOn upperHalfPlaneOpens} (hh₀ : Measurable h₀)
    {Ψ : DistOn upperHalfPlaneOpens → XCode nL nR} (hΨm : Measurable Ψ) {U : DistOn upperHalfPlaneOpens → ℝ}
    (hUm : Measurable U) (hU01 : ∀ f, 0 ≤ U f ∧ U f ≤ 1)
    (hUlaw : ∀ A : Set (XCode nL nR), MeasurableSet A → ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      (P₀.map h₀) {f | Ψ f ∈ A ∧ cζ (Ψ f) < ⊤ ∧ U f ≤ u} =
        (P₀.map h₀) {f | Ψ f ∈ A ∧ cζ (Ψ f) < ⊤} * ENNReal.ofReal u)
    {B' : ℝ≥0 → Ω₀ → ℝ} (hB'm : ∀ t, Measurable (B' t)) {Fw : I → PCode} (hFwm : Measurable Fw)
    (hFw : (volume : Measure I).map Fw = P₀.map (fun ω => enc fun t => B' t ω)) :
    (P₀.map h₀).map (fun f => (Ψ f, killB (Ψ f) (Fw (projIcc 0 1 zero_le_one (U f))))) =
      (P₀.prod P₀).map (modelMap (fun ω => Ψ (h₀ ω)) B') := by
  set μ := P₀.map h₀ with hμ
  have : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff hh₀.aemeasurable).2 inferInstance
  set X₀ : Ω₀ → XCode nL nR := fun ω => Ψ (h₀ ω) with hX₀
  have hX₀m : Measurable X₀ := hΨm.comp hh₀
  have hpm : Measurable (projIcc (0 : ℝ) 1 zero_le_one) := continuous_projIcc.measurable
  set G : DistOn upperHalfPlaneOpens → PCode := fun f => Fw (projIcc 0 1 zero_le_one (U f)) with hG
  have hGm : Measurable G := hFwm.comp (hpm.comp hUm)
  set νW := P₀.map (fun ω => enc fun t => B' t ω) with hνW
  have hencm := measurable_enc_proc hB'm
  have hFin : MeasurableSet {x : XCode nL nR | cζ x < ⊤} := measurableSet_lt measurable_cζ measurable_const
  have hFm : Measurable fun f => (Ψ f, killB (Ψ f) (G f)) :=
    hΨm.prodMk (measurable_killB.comp (hΨm.prodMk hGm))
  have hgm := measurable_modelMap hX₀m hB'm
  -- the Brownian code built from the field on `{cζ < ∞}`
  have hGlaw : ∀ A : Set (XCode nL nR), MeasurableSet A → ∀ C : Set PCode, MeasurableSet C →
      μ {f | Ψ f ∈ A ∧ cζ (Ψ f) < ⊤ ∧ G f ∈ C} = μ {f | Ψ f ∈ A ∧ cζ (Ψ f) < ⊤} * νW C := by
    intro A hA C hC
    set S : Set (DistOn upperHalfPlaneOpens) := {f | Ψ f ∈ A ∧ cζ (Ψ f) < ⊤} with hS
    have hSm : MeasurableSet S := hΨm (hA.inter hFin)
    have hmap := map_restrict_eq_of_cdf (μ := μ) (S := S) hUm hU01 fun u hu0 hu1 => by
      rw [← hUlaw A hA u hu0 hu1]
      congr 1
      ext f; simp only [hS, mem_inter_iff, mem_ofPred_eq, and_assoc]
    have hD : MeasurableSet ((Fw ∘ projIcc (0 : ℝ) 1 zero_le_one) ⁻¹' C) := (hFwm.comp hpm) hC
    have e1 : μ {f | Ψ f ∈ A ∧ cζ (Ψ f) < ⊤ ∧ G f ∈ C} =
        (μ.restrict S) (U ⁻¹' ((Fw ∘ projIcc (0 : ℝ) 1 zero_le_one) ⁻¹' C)) := by
      rw [Measure.restrict_apply (hUm hD)]
      congr 1
      ext f; simp only [hS, hG, mem_inter_iff, mem_ofPred_eq, mem_preimage, Function.comp_apply]
      tauto
    have e2 : (volume.restrict (Icc (0 : ℝ) 1)).map (Fw ∘ projIcc (0 : ℝ) 1 zero_le_one) = νW := by
      rw [← Measure.map_map hFwm hpm, map_projIcc_volume, hFw]
    rw [e1, ← Measure.map_apply hUm hD, hmap, Measure.smul_apply, smul_eq_mul,
      ← Measure.map_apply (hFwm.comp hpm) hC, e2]
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨A, hA, C, hC, rfl⟩
    replace hA : MeasurableSet A := hA
    replace hC : MeasurableSet C := hC
    rw [Measure.map_apply hFm (hA.prod hC), Measure.map_apply hgm (hA.prod hC)]
    set E₁ : Set (XCode nL nR) := A ∩ {x | cζ x < ⊤} with hE₁
    set E₂ : Set (XCode nL nR) := A ∩ {x | ¬ cζ x < ⊤ ∧ (0 : PCode) ∈ C} with hE₂
    have hE₁m : MeasurableSet E₁ := hA.inter hFin
    have hE₂m : MeasurableSet E₂ := hA.inter (hFin.compl.inter (MeasurableSet.const _))
    have hL : (fun f => (Ψ f, killB (Ψ f) (G f))) ⁻¹' (A ×ˢ C) =
        {f | Ψ f ∈ A ∧ cζ (Ψ f) < ⊤ ∧ G f ∈ C} ∪ Ψ ⁻¹' E₂ := by
      ext f
      simp only [mem_preimage, mem_prod, mem_union, mem_ofPred_eq, hE₂, mem_inter_iff, killB]
      by_cases hf : cζ (Ψ f) < ⊤
      · simp only [hf, ↓reduceIte]; tauto
      · simp only [hf, ↓reduceIte]; tauto
    have hR : modelMap X₀ B' ⁻¹' (A ×ˢ C) =
        (X₀ ⁻¹' E₁) ×ˢ ((fun ω => enc fun t => B' t ω) ⁻¹' C) ∪ (X₀ ⁻¹' E₂) ×ˢ univ := by
      ext p
      simp only [mem_preimage, mem_prod, mem_union, mem_ofPred_eq, hE₁, hE₂, mem_inter_iff, modelMap,
        killB, mem_univ, and_true]
      by_cases hp : cζ (X₀ p.1) < ⊤
      · simp only [hp, ↓reduceIte]; tauto
      · simp only [hp, ↓reduceIte]; tauto
    have hdL : Disjoint {f | Ψ f ∈ A ∧ cζ (Ψ f) < ⊤ ∧ G f ∈ C} (Ψ ⁻¹' E₂) :=
      Set.disjoint_left.2 fun f h1 h2 => h2.2.1 h1.2.1
    have hdR : Disjoint ((X₀ ⁻¹' E₁) ×ˢ ((fun ω => enc fun t => B' t ω) ⁻¹' C)) ((X₀ ⁻¹' E₂) ×ˢ univ) :=
      Set.disjoint_left.2 fun p h1 h2 => h2.1.2.1 h1.1.2
    rw [hL, hR, measure_union hdL (hΨm hE₂m), measure_union hdR ((hX₀m hE₂m).prod MeasurableSet.univ),
      Measure.prod_prod, Measure.prod_prod, measure_univ, mul_one, hGlaw A hA C hC]
    have e₁ : μ {f | Ψ f ∈ A ∧ cζ (Ψ f) < ⊤} = P₀ (X₀ ⁻¹' E₁) := by
      change μ (Ψ ⁻¹' E₁) = P₀ (X₀ ⁻¹' E₁)
      rw [hμ, Measure.map_apply hh₀ (hΨm hE₁m)]; rfl
    have e₂ : μ (Ψ ⁻¹' E₂) = P₀ (X₀ ⁻¹' E₂) := by
      rw [hμ, Measure.map_apply hh₀ (hΨm hE₂m)]; rfl
    rw [e₁, e₂, hνW, Measure.map_apply hencm hC]
  · rw [Measure.map_apply hFm MeasurableSet.univ, Measure.map_apply hgm MeasurableSet.univ,
      preimage_univ, preimage_univ, measure_univ, measure_univ]

end Law

/-! ### Realization on every space carrying the field -/

section Realization

universe u

/-- **Named input (ii), code form: the driving evolution is realized on every space carrying the field.** For the
reference coupling there are a Borel history code `Ψ` (with a generating trace on a Borel full-measure set `S`, as in
`exists_fieldDetermination`) such that on every probability space carrying a field `h` with the reference law, the
processes `Ψ(h)` together with some filtration and noise form an integrated `SLE_κ(ρ)` evolution. -/
theorem exists_fieldDetermination_realization (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
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

end Realization

/-! ### Existence of flow lines from Theorems 1.2–1.3 -/

section FlowLine

universe u

/-- **Existence of flow lines from Theorems 1.2 and 1.3 alone** (the frozen `exists_isFlowLine`, Theorem 1.5's
non-vacuity companion, in provider shape: all of the anchor's arguments implicit, its hypotheses auto-parameters).
Named inputs (i) (`hullClauseTransferStatement`) and (ii) (`exists_fieldDetermination_realization`) are both proved;
Theorem 1.1 enters through its sealed provider. Conditional helper on the frozen Theorems 1.2 and 1.3 (exactly their
types); it is not the provider. -/
theorem exists_isFlowLine_of_thm12_thm13_only (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {x θ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps := by assumption) :
    ∃ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps x θ P h η ζ := by
  have _ := hκ4
  have hF := Theorem15.isOrderedForceWord_flowLine b jumps x
  -- the reference coupling of the flow-line word (Theorem 1.1)
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, h₀, hcoup⟩ :=
    Spec.Provider.exists_isOptionalHullCoupling.{u} (κ := κ) (xL := flowLineXL b jumps x)
      (xR := flowLineXR b jumps x) (ρL := flowLineRhoL κ b jumps x θ) (ρR := flowLineRhoR κ b jumps x θ) hκ hF
  -- the history is a Borel function of the field, and the driving evolution is realized on every space
  obtain ⟨Ψ, S, ηf, hΨm, hSm, hae, htr, hreal⟩ := exists_fieldDetermination_realization h12 h13 hκ hF hcoup
  -- the flow-line field and its law
  set h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens :=
    fun ω => flowField x (θ * QuantumZipper.chiC κ) (h ω) with hh'def
  have hh' := isGFFWithBoundaryData_flowField hκ hb x θ hh
  obtain ⟨u, hu, -⟩ := Spec.Provider.existsUnique_isBoundedHarmonicExtension_forceBoundaryData (κ := κ)
    (ρL := flowLineRhoL κ b jumps x θ) (ρR := flowLineRhoR κ b jumps x θ) (vL := flowLineXL b jumps x)
    (vR := flowLineXR b jumps x)
  have hh₀ : IsGFFWithBoundaryData P₀ h₀
      (forceBoundaryData κ (flowLineRhoL κ b jumps x θ) (flowLineRhoR κ b jumps x θ) (flowLineXL b jumps x)
        (flowLineXR b jumps x)) (forceJumpSet (flowLineXL b jumps x) (flowLineXR b jumps x)) :=
    ⟨hcoup.2.1, hcoup.2.2.1⟩
  have hlaw : P.map h' = P₀.map h₀ := map_eq_of_isGFFWithBoundaryData hh' hh₀ hu
  -- realization on the given space, then the hull clauses (named input (i), proved)
  obtain ⟨𝓕, B, hE⟩ := hreal P h' hh'.1 hlaw
  have hdet : ∀ᵐ ω ∂P₀, (pathsOfCode (Ψ (h₀ ω))).1 = ζ₀ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ ω →
      (pathsOfCode (Ψ (h₀ ω))).2.1 t = W₀ t ω ∧ (∀ i, (pathsOfCode (Ψ (h₀ ω))).2.2.1 i t = VL₀ i t ω) ∧
        ∀ j, (pathsOfCode (Ψ (h₀ ω))).2.2.2 j t = VR₀ j t ω := by
    filter_upwards [hae] with ω hω
    exact ⟨hω.2.1, hω.2.2⟩
  have hdatum : IsFieldRealizationDatum κ (flowLineXL b jumps x) (flowLineXR b jumps x)
      (flowLineRhoL κ b jumps x θ) (flowLineRhoR κ b jumps x θ) (pathsOfCode ∘ Ψ) P h' :=
    ⟨hκ, hF, measurable_pathsOfCode.comp hΨm, hh'.1, Ω₀, mΩ₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, h₀, hcoup,
      hdet, hlaw⟩
  have hcoupΩ := hullClauseTransferStatement κ _ _ _ _ (pathsOfCode ∘ Ψ) P h' hdatum 𝓕 B hE
  -- the field lies in the good set almost surely
  have hS₀ : ∀ᵐ f ∂(P₀.map h₀), f ∈ S :=
    (ae_map_iff hcoup.2.1.aemeasurable hSm).2 (hae.mono fun ω hω => hω.1)
  rw [← hlaw] at hS₀
  have hSΩ : ∀ᵐ ω ∂P, h' ω ∈ S := (ae_map_iff hh'.1.aemeasurable hSm).1 hS₀
  refine ⟨fun ω t => ηf (h' ω) t + x, fun ω => cζ (Ψ (h' ω)), h', 𝓕, _, _, _, B,
    fun ω => isTranslateAddConst_flowField x _ (h ω), hcoupΩ, ?_⟩
  filter_upwards [hSΩ] with ω hω
  have e : (fun t => ηf (h' ω) t + (x : ℂ) - x) = ηf (h' ω) := by
    funext t; ring
  rw [e]
  exact htr _ hω

end FlowLine

end Exist

end InteractingSLE
