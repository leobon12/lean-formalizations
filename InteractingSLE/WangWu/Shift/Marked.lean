/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Shift.Union
import InteractingSLE.WangWu.ReverseContactMartFilt2Glue

/-!
# The height-shifted two-slit law, part 5: both stopped histories retained, and the explicit conditional law

Packet PROVE-WW-B26 (PROVE-WW-B18's `isHistoryAvoidanceLocal_twoSlit_glue`, `exists_condExp_twoSlit_glue_history`,
`ae_condExp_cexp_twoSlit_glue` with the height shift). Setting of `ImageWordFiltShiftStatement`, glued space
`P ⊗ k(X)`, `h = X + δλ`:

* **`isHistoryAvoidanceLocal_twoSlit_glue_shift`**: `A_t ∪ G_s` satisfies Aux. lemma 18's history-marked avoidance
  criterion for the shared centred field `h − u₀ = X − (u₀ − δλ)` and the marks `twoSlitMarks t s`;
* `exists_condExp_twoSlit_glue_history_shift`: hence its germ law with both stopped histories;
* **`ae_condExp_cexp_twoSlit_glue_shift`**: almost surely before contact, for `supp φ ⊆ ℍ \ (A ∪ G)`,
  `E[e^{i(h,φ)} | 𝒜_{A∪G} ∨ marks] = exp(i ∫ chartMeanW ![r_L, −r_L − δ] ![r_R, −r_R + δ] ∘ f'_T ∘ Ψ · φ) ·
  exp(−½ G_{ℍ∖(A∪G)}(φ, φ))`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull fwdMap)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu

open WholeField LocalSets LawUnique Coupling

section Glue

variable {rL rR δ : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {𝓕₂ : Filtration ℝ≥0 mΩ₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
  {ζ₂ : Ω₂ → ℝ≥0∞} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}

/-- **The two stopped slits with both stopped histories retained, with the height shift.** On `P ⊗ k(X)`, for
rational `t, s > 0`, the union of the forward slit at `t` and the reflected reverse slit at `s` satisfies the
history-marked avoidance criterion for the centred field `h − u₀` and the marks `twoSlitMarks t s`. -/
theorem isHistoryAvoidanceLocal_twoSlit_glue_shift (hL : 0 ≤ rL) (hR : 0 ≤ rR) (hL₁ : 0 ≤ rL + δ)
    (hR₁ : 0 ≤ rR - δ)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    {X : Ω → DistOn upperHalfPlaneOpens} (hXm : Measurable X)
    (hX : ∀ ω, h ω = Exist.flowField 0 (δ * wwLambda) (X ω))
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR - δ) (fun _ => rL + δ) P₂ 𝓕₂ W₂ VL₂ VR₂
      B₂ ζ₂ h₂)
    (hlaw : P.map X = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀)
    {t s : ℚ} (ht : 0 < t) (hs : 0 < s) :
    IsHistoryAvoidanceLocal (twoSlitMarks W VL VR ζ t s)
      (fun p : Ω × HistorySpace 1 1 => histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)
      (fun p => centredField h u₀ p.1) (glueMeasure P k X hXm) := by
  set μ := glueMeasure P k X hXm with hμ
  set u₁ : ℂ → ℝ := fun z => u₀ z + -(δ * wwLambda) with hu₁def
  have hu₁ := Shift.isBoundedHarmonicExtension_shift (δ := δ) hu₀
  have hcf := Shift.centredField_shift hX hu₀.1
  have e0 : (fun p : Ω × HistorySpace 1 1 => centredField h u₀ p.1) = fun p => centredField X u₁ p.1 :=
    funext fun p => congrFun hcf p.1
  rw [e0]
  obtain ⟨hXk, -⟩ := hC.2.2.2
  obtain ⟨hX₂, -⟩ := hC₂.2.2.2
  have hh₂m := hC₂.2.1
  set D₁ := SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₁ with hD₁
  have hDh₁ : IsHarmonicDistOn D₁ H := isHarmonicDistOn_smoothDist hu₁.1
  have hYm : Measurable (killedHistory W VL VR ζ) := measurable_killedHistory hXk
  have hY₂m : Measurable (killedHistory W₂ VL₂ VR₂ ζ₂) := measurable_killedHistory hX₂
  have hcm : Measurable (centredField X u₁) := measurable_centredField hXm u₁
  -- the forward slit on `Ω`
  have hτ := isStoppingTime_const (drivingFiltration P hXk) (t : ℝ).toNNReal
  have hτζ : ∀ᵐ ω ∂P, ((((t : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := by
    filter_upwards [IsMarkedChain.ae_seedLine isOrderedForceWord_twoSeed (hasNonnegCumWeights_twoSeed hL hR) hC.1]
      with ω hω
    rw [hω.1]
    exact ENNReal.coe_lt_top
  have hfwd := isHistoryAvoidanceLocal_hull hC (by norm_num) hu₀ hXk hτ hτζ
    (A := fun ω => histHull t (killedHistory W VL VR ζ ω)) ((measurable_histHull t).comp hYm)
    (by
      filter_upwards [ae_histHull_eq_fwdHull hL hR hC.1 ht] with ω hω
      rw [hω, WithTop.untopD_coe])
  rw [hcf] at hfwd
  have hfwd' := IsHistoryAvoidanceLocal.mono_marks hfwd ((comap_stopSigma_le (P := P) hXk (t : ℝ).toNNReal).trans
    (IsStoppingTime.measurableSpace_const _ _).symm.le)
  have hlaw₁ : μ.map (fun p : Ω × HistorySpace 1 1 => (centredField X u₁ p.1, killedHistory W VL VR ζ p.1)) =
      P.map (fun ω => (centredField X u₁ ω, killedHistory W VL VR ζ ω)) := by
    rw [show (fun p : Ω × HistorySpace 1 1 => (centredField X u₁ p.1, killedHistory W VL VR ζ p.1)) =
        (fun ω => (centredField X u₁ ω, killedHistory W VL VR ζ ω)) ∘ Prod.fst from rfl,
      ← Measure.map_map (hcm.prodMk hYm) measurable_fst, hμ, glueMeasure_fst k hXm]
  have hA₁ := isHistoryAvoidanceLocal_of_map_eq (𝔐 := stopSigma (t : ℝ).toNNReal) hcm hYm
    (hcm.comp measurable_fst) (hYm.comp measurable_fst) hlaw₁ (measurable_histHull t) (stopSigma_le _) hfwd'
  -- the reflected reverse slit on `Ω₂`
  have hτ₂ := isStoppingTime_const (drivingFiltration P₂ hX₂) (s : ℝ).toNNReal
  have hτζ₂ : ∀ᵐ ω ∂P₂, ((((s : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0) : ℝ≥0∞) < ζ₂ ω := by
    filter_upwards [IsMarkedChain.ae_seedLine isOrderedForceWord_twoSeed (hasNonnegCumWeights_twoSeed hR₁ hL₁)
      hC₂.1] with ω hω
    rw [hω.1]
    exact ENNReal.coe_lt_top
  have hrev := isHistoryAvoidanceLocal_reflect_hull hC₂ (by norm_num) hDh₁ hX₂ hτ₂ hτζ₂
    (A := fun ω => negInv '' histHull s (killedHistory W₂ VL₂ VR₂ ζ₂ ω))
    ((measurable_image_negInv.comp (measurable_histHull s)).comp hY₂m)
    (by
      filter_upwards [ae_histHull_eq_fwdHull hR₁ hL₁ hC₂.1 hs] with ω hω
      rw [hω, WithTop.untopD_coe])
  have hrev' := IsHistoryAvoidanceLocal.mono_marks hrev ((comap_stopSigma_le (P := P₂) hX₂ (s : ℝ).toNNReal).trans
    (IsStoppingTime.measurableSpace_const _ _).symm.le)
  have hX₂m : Measurable fun ω => reflectField (h₂ ω) - D₁ :=
    (measurable_sub_dist D₁).comp (measurable_reflectField.comp hh₂m)
  have hlaw₂ : μ.map (fun p : Ω × HistorySpace 1 1 => (centredField X u₁ p.1, p.2)) =
      P₂.map (fun ω => (reflectField (h₂ ω) - D₁, killedHistory W₂ VL₂ VR₂ ζ₂ ω)) := by
    have hT : Measurable fun q : DistOn upperHalfPlaneOpens × HistorySpace 1 1 => (q.1 - D₁, q.2) :=
      ((measurable_sub_dist D₁).comp measurable_fst).prodMk measurable_snd
    have hpair : Measurable fun p : Ω × HistorySpace 1 1 => (X p.1, p.2) :=
      (hXm.comp measurable_fst).prodMk measurable_snd
    have hpair₂ : Measurable fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω) :=
      (measurable_reflectField.comp hh₂m).prodMk hY₂m
    rw [show (fun p : Ω × HistorySpace 1 1 => (centredField X u₁ p.1, p.2)) =
        (fun q : DistOn upperHalfPlaneOpens × HistorySpace 1 1 => (q.1 - D₁, q.2)) ∘ fun p => (X p.1, p.2) from rfl,
      show (fun ω => (reflectField (h₂ ω) - D₁, killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
        (fun q : DistOn upperHalfPlaneOpens × HistorySpace 1 1 => (q.1 - D₁, q.2)) ∘
          fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω) from rfl,
      ← Measure.map_map hT hpair, ← Measure.map_map hT hpair₂, hμ, glueMeasure_map_pair hXm k, hlaw, hk]
  have hA₂ := isHistoryAvoidanceLocal_of_map_eq (𝔐 := stopSigma (s : ℝ).toNNReal) hX₂m hY₂m
    (hcm.comp measurable_fst) measurable_snd hlaw₂ (measurable_image_negInv.comp (measurable_histHull s))
    (stopSigma_le _) hrev'
  -- the union
  have hσ : MeasurableSpace.comap (fun p : Ω × HistorySpace 1 1 => centredField X u₁ p.1) inferInstance =
      MeasurableSpace.comap (fun p : Ω × HistorySpace 1 1 => X p.1) inferInstance := by
    refine le_antisymm ?_ ?_
    · change MeasurableSpace.comap ((fun f => f - D₁) ∘ fun p : Ω × HistorySpace 1 1 => X p.1) _ ≤ _
      rw [← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono (measurable_sub_dist D₁).comap_le
    · calc MeasurableSpace.comap (fun p : Ω × HistorySpace 1 1 => X p.1) inferInstance
          = MeasurableSpace.comap ((fun f => f + D₁) ∘ fun p : Ω × HistorySpace 1 1 => centredField X u₁ p.1)
              inferInstance := by
            congr 1; funext p; exact (sub_add_cancel (X p.1) D₁).symm
        _ ≤ _ := by
            rw [← MeasurableSpace.comap_comp]
            exact MeasurableSpace.comap_mono (Coupling.measurable_add_distOnConst D₁).comap_le
  have hci := condIndepEv_glue_fst (μ := P) k hXm
  rw [← hσ] at hci
  have hℋ₁ : MeasurableSpace.comap (fun p : Ω × HistorySpace 1 1 => killedHistory W VL VR ζ p.1)
      (stopSigma (t : ℝ).toNNReal) ≤ MeasurableSpace.comap Prod.fst mΩ := by
    rw [show (fun p : Ω × HistorySpace 1 1 => killedHistory W VL VR ζ p.1) =
      killedHistory W VL VR ζ ∘ Prod.fst from rfl, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono ((MeasurableSpace.comap_mono (stopSigma_le _)).trans hYm.comap_le)
  have hℋ₂ : MeasurableSpace.comap (fun p : Ω × HistorySpace 1 1 => p.2) (stopSigma (s : ℝ).toNNReal) ≤
      MeasurableSpace.comap Prod.snd inferInstance :=
    MeasurableSpace.comap_mono (stopSigma_le _)
  exact isHistoryAvoidanceLocal_union measurable_fst.comap_le measurable_snd.comap_le hℋ₁ hℋ₂
    (((measurable_histHull t).comp hYm).comp (comap_measurable Prod.fst))
    (((measurable_image_negInv.comp (measurable_histHull s))).comp (comap_measurable Prod.snd)) hci hA₁ hA₂

/-- **The conditional law of the centred field given the germ of the two stopped slits and both stopped histories**
(Aux. lemma 18's germ law on the glued space): for every test function `φ` there is a germ-measurable `M` with
`M = E[(h − u₀, φ) | 𝒜 ∨ ℋ]` and `E[e^{i (h − u₀, φ)} | 𝒜 ∨ ℋ] = e^{iM} e^{−σ²_{ℍ∖(A∪G)}(φ)/2}`, where `𝒜` is the germ
σ-algebra of `A ∪ G` and `ℋ` the marks `twoSlitMarks`. -/
theorem exists_condExp_twoSlit_glue_history_shift (hL : 0 ≤ rL) (hR : 0 ≤ rR) (hL₁ : 0 ≤ rL + δ) (hR₁ : 0 ≤ rR - δ)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    {X : Ω → DistOn upperHalfPlaneOpens} (hXm : Measurable X)
    (hX : ∀ ω, h ω = Exist.flowField 0 (δ * wwLambda) (X ω))
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR - δ) (fun _ => rL + δ) P₂ 𝓕₂ W₂ VL₂ VR₂
      B₂ ζ₂ h₂)
    (hlaw : P.map X = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀)
    {t s : ℚ} (ht : 0 < t) (hs : 0 < s) (φ : TestOn upperHalfPlaneOpens) :
    ∃ M : Ω × HistorySpace 1 1 → ℝ,
      Measurable[germSigma (fun p : Ω × HistorySpace 1 1 =>
        histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2) (fun p => centredField h u₀ p.1)] M ∧
      M =ᵐ[glueMeasure P k X hXm] (glueMeasure P k X hXm)[fun p => centredField h u₀ p.1 φ |
        germSigma (fun p : Ω × HistorySpace 1 1 =>
          histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2) (fun p => centredField h u₀ p.1) ⊔
          twoSlitMarks W VL VR ζ t s] ∧
      (fun p => Complex.exp (Complex.I * (M p : ℂ)) *
          ((Real.exp (-(1 / 2) * QuantumZipper.zeroGFFTestCov (H \ relClosureH
            (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)) φ φ) : ℝ) : ℂ))
        =ᵐ[glueMeasure P k X hXm]
        (glueMeasure P k X hXm)[fun p => Complex.exp (Complex.I * (centredField h u₀ p.1 φ : ℂ)) |
          germSigma (fun p : Ω × HistorySpace 1 1 =>
            histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2) (fun p => centredField h u₀ p.1) ⊔
            twoSlitMarks W VL VR ζ t s] := by
  obtain ⟨hXk, -⟩ := hC.2.2.2
  have hF : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun p : Ω × HistorySpace 1 1 =>
      centredField h u₀ p.1) (glueMeasure P k X hXm) :=
    isZeroBoundaryGFF_comp_of_map_eq (g := fun ω => centredField h u₀ ω) (f := Prod.fst) measurable_fst
      (glueMeasure_fst (μ := P) k hXm) (isZeroBoundaryGFF_centredField hC hu₀)
  have hAm : Measurable[_, hittingSigma] fun p : Ω × HistorySpace 1 1 =>
      histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2 :=
    measurable_union_hitting (((measurable_histHull t).comp (measurable_killedHistory hXk)).comp measurable_fst)
      ((measurable_image_negInv.comp (measurable_histHull s)).comp measurable_snd)
  have hAc : ∀ p : Ω × HistorySpace 1 1, histHull t (killedHistory W VL VR ζ p.1) ∪
      negInv '' histHull s p.2 ⊆ H ∧ IsOpen (H \ (histHull t (killedHistory W VL VR ζ p.1) ∪
        negInv '' histHull s p.2)) := by
    intro p
    obtain ⟨h1, h2⟩ := histHull_relClosed t (killedHistory W VL VR ζ p.1)
    obtain ⟨h3, h4⟩ := image_negInv_relClosed (histHull_relClosed s p.2)
    refine ⟨union_subset h1 h3, ?_⟩
    have e : H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2) =
        (H \ histHull t (killedHistory W VL VR ζ p.1)) ∩ (H \ negInv '' histHull s p.2) := by
      ext z; simp only [Set.mem_sdiff, mem_inter_iff, mem_union]; tauto
    rw [e]
    exact h2.inter h4
  exact exists_condExp_germSigma_history hF hAm (twoSlitMarks_le t s hXk)
    (isHistoryAvoidanceLocal_twoSlit_glue_shift hL hR hL₁ hR₁ hC hXm hX hC₂ hlaw k hk hu₀ ht hs)
    (Eventually.of_forall hAc) φ

/-- **The conditional characteristic function of the field given the germ of the two stopped slits and both stopped
histories, explicitly** (Proposition 3.7 with retained histories, Proposition 3.8 and PROVE-WW-B14's identification
of the union mean, `ae_union_mean_eq_chartMean_glue`). Almost surely on `{A ∩ G = ∅}`, for `φ` supported in
`ℍ \ (A ∪ G)`, there is an image chain `(W', T)` of `Ψ(A)` (`Ψ = revChart` of the reverse frozen driver) with
`E[e^{i (h, φ)} | 𝒜 ∨ ℋ] = exp(i ∫ chartMean ∘ f'_T ∘ Ψ · φ) · exp(−½ G_{ℍ∖(A∪G)}(φ, φ))`: given the germ of the union
and both stopped histories, the field off the union is the explicit `SLE₄(r_L, −r_L; r_R, −r_R)` mean of the image
slit, pulled back by `Ψ`, plus a zero-boundary GFF on `ℍ \ (A ∪ G)`. -/
theorem ae_condExp_cexp_twoSlit_glue_shift (hL : 0 ≤ rL) (hR : 0 ≤ rR) (hL₁ : 0 ≤ rL + δ) (hR₁ : 0 ≤ rR - δ)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    {X : Ω → DistOn upperHalfPlaneOpens} (hXm : Measurable X)
    (hX : ∀ ω, h ω = Exist.flowField 0 (δ * wwLambda) (X ω))
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR - δ) (fun _ => rL + δ) P₂ 𝓕₂ W₂ VL₂ VR₂
      B₂ ζ₂ h₂)
    (hlaw : P.map X = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀)
    {t s : ℚ} (ht : 0 < t) (hs : 0 < s) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ p ∂(glueMeasure P k X hXm),
      Disjoint (histHull t (killedHistory W VL VR ζ p.1)) (negInv '' histHull s p.2) →
      tsupport φ ⊆ H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2) →
      ∃ W' : ℝ → ℝ, Continuous W' ∧ W' 0 = 0 ∧ ∃ T : ℝ, 0 < T ∧ ∃ η' : ℝ → ℂ, IsLoewnerTrace W' η' ∧
        IsProperArc η' ∧
        fwdHull W' T = revChart (Ito.rpath (frzDrive s p.2)) s '' histHull t (killedHistory W VL VR ζ p.1) ∧
        (glueMeasure P k X hXm)[fun p' => Complex.exp (Complex.I * (h p'.1 φ : ℂ)) |
            germSigma (fun p : Ω × HistorySpace 1 1 =>
              histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2) (fun p => centredField h u₀ p.1) ⊔
              twoSlitMarks W VL VR ζ t s] p =
          Complex.exp (Complex.I * ((∫ z, chartMeanW ![rL, -rL - δ] ![rR, -rR + δ] W' T (frzVL s p.2) (frzVR s p.2)
              (fwdMap W' T (revChart (Ito.rpath (frzDrive s p.2)) s z)) * φ z : ℝ) : ℂ)) *
            ((Real.exp (-(1 / 2) * QuantumZipper.zeroGFFTestCov
              (H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)) φ φ) : ℝ) : ℂ) := by
  obtain ⟨hXk, -⟩ := hC.2.2.2
  set μ := glueMeasure P k X hXm with hμ
  obtain ⟨M, -, hM1, hM2⟩ := exists_condExp_twoSlit_glue_history_shift hL hR hL₁ hR₁ hC hXm hX hC₂ hlaw k hk hu₀ ht hs φ
  have hF : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun p : Ω × HistorySpace 1 1 =>
      centredField h u₀ p.1) μ :=
    isZeroBoundaryGFF_comp_of_map_eq (g := fun ω => centredField h u₀ ω) (f := Prod.fst) measurable_fst
      (glueMeasure_fst (μ := P) k hXm) (isZeroBoundaryGFF_centredField hC hu₀)
  have hAm : Measurable[_, hittingSigma] fun p : Ω × HistorySpace 1 1 =>
      histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2 :=
    measurable_union_hitting (((measurable_histHull t).comp (measurable_killedHistory hXk)).comp measurable_fst)
      ((measurable_image_negInv.comp (measurable_histHull s)).comp measurable_snd)
  have hloc := isLocalSet_twoSlit_glue_shift hL hR hL₁ hR₁ hC hXm hX hC₂ hlaw k hk hu₀ ht hs
  obtain ⟨g, hg⟩ := LocalSets.IsLocalSet.exists_isLocalSetMean hF hAm hloc
  have hgM := IsLocalSetMean.ae_eq_condExp_germSigma_sup hF hAm hloc (twoSlitMarks_le t s hXk)
    (isHistoryAvoidanceLocal_twoSlit_glue_shift hL hR hL₁ hR₁ hC hXm hX hC₂ hlaw k hk hu₀ ht hs) hg φ
  have hB14 := ae_union_mean_eq_chartMean_glue_shift hL hR hL₁ hR₁ hC hXm hX hC₂ hlaw k hk hu₀ ht hs hg
  -- pulling out the harmonic shift
  set c : ℂ := Complex.exp (Complex.I * ((∫ z, u₀ z * φ z : ℝ) : ℂ)) with hc
  have e : (fun p : Ω × HistorySpace 1 1 => Complex.exp (Complex.I * (h p.1 φ : ℂ))) =
      c • fun p => Complex.exp (Complex.I * (centredField h u₀ p.1 φ : ℂ)) := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, hc, centredField_apply h hu₀.1 p.1 φ, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hpull := condExp_smul (μ := μ) c (fun p : Ω × HistorySpace 1 1 =>
    Complex.exp (Complex.I * (centredField h u₀ p.1 φ : ℂ))) (germSigma (fun p : Ω × HistorySpace 1 1 =>
      histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2) (fun p => centredField h u₀ p.1) ⊔
        twoSlitMarks W VL VR ζ t s)
  rw [← e] at hpull
  filter_upwards [hM1, hM2, hgM, hB14, hpull] with p h1 h2 h3 h4 h5 hdisj hsupp
  obtain ⟨w, hw, hgw, W', hW'c, hW'0, T, hT, η', hη', hprop, hhull, hmean⟩ := h4 hdisj
  refine ⟨W', hW'c, hW'0, T, hT, η', hη', hprop, hhull, ?_⟩
  rw [h5, Pi.smul_apply, ← h2, smul_eq_mul]
  have hMp : M p = ∫ z, w z * φ z := by rw [h1, ← h3, hgw φ hsupp]
  obtain ⟨hsub1, hop1⟩ := histHull_relClosed t (killedHistory W VL VR ζ p.1)
  obtain ⟨hsub2, hop2⟩ := image_negInv_relClosed (histHull_relClosed s p.2)
  have hopen : IsOpen (H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)) := by
    have e2 : H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2) =
        (H \ histHull t (killedHistory W VL VR ζ p.1)) ∩ (H \ negInv '' histHull s p.2) := by
      ext z; simp only [Set.mem_sdiff, mem_inter_iff, mem_union]; tauto
    rw [e2]
    exact hop1.inter hop2
  rw [hMp, relClosureH_eq (union_subset hsub1 hsub2) hopen]
  -- the explicit mean
  have hwi : Integrable fun z => w z * φ z :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn
      (fun z hz => (hw z hz).1.continuousAt.continuousWithinAt) φ hsupp
  have hui : Integrable fun z => u₀ z * φ z :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn
      (fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt) φ φ.tsupport_subset
  have hint : (∫ z, chartMeanW ![rL, -rL - δ] ![rR, -rR + δ] W' T (frzVL s p.2) (frzVR s p.2)
      (fwdMap W' T (revChart (Ito.rpath (frzDrive s p.2)) s z)) * φ z) =
      (∫ z, w z * φ z) + ∫ z, u₀ z * φ z := by
    rw [← integral_add hwi hui]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ tsupport φ
    · simp only
      rw [← hmean z (hsupp hz)]
      ring
    · simp only [image_eq_zero_of_notMem_tsupport hz, mul_zero, add_zero]
  rw [hint, hc, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

end Glue

end InteractingSLE.WangWu
