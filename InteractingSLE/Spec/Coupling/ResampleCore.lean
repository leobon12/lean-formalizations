import InteractingSLE.Spec.Coupling.ProtectedKernel
import Mathlib.Probability.Kernel.CondDistrib

/-!
# Gaussian resampling, measure-theoretic core (Theorem 1.1, obligation 3)

Packet PROVE-T11-KER (Astra §1, "Finite families: Gaussian resampling supplies compatibility", pp. 5–6). The finite
family construction is carried out with the driving history kept fixed: at every stage the field is sampled from a
Markov kernel `η : Ω → 𝒟'(ℍ)` given the whole history, and the stage constraints are statements about the joint law
`P ⊗ η` on events of the stage σ-algebra. This file contains the generic tools.

* `lintegral_compProd_eq_of_rect` : two joint laws `P ⊗ κ₁`, `P ⊗ κ₂` that agree on the rectangles `A × B` with `A`
  in a sub-σ-algebra `𝒜` agree on every `𝒜 ⊗ 𝔅`-measurable integrand;
* `exists_kernel_condVersion` : every Markov kernel has an `𝒜`-measurable version with the same joint law on
  `𝒜`-rectangles (Mathlib's `condDistrib` on `Ω × X`);
* `exists_condKernel_restrictDist` : the conditional law of a field given its restriction to `V`
  (Mathlib's `Kernel.condKernel`), concentrated on the fields with that restriction.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Coupling

open LQGMetric GFF

section General

variable {Ω X : Type*} [mX : MeasurableSpace X]

theorem prod_le_prod_of_le {𝒜 mΩ : MeasurableSpace Ω} (h𝒜 : 𝒜 ≤ mΩ) :
    𝒜.prod mX ≤ mΩ.prod mX :=
  sup_le_sup (MeasurableSpace.comap_mono h𝒜) le_rfl

/-- **Agreement on `𝒜`-rectangles extends to `𝒜 ⊗ 𝔅`-measurable integrands.** -/
theorem lintegral_compProd_eq_of_rect {𝒜 mΩ : MeasurableSpace Ω} (h𝒜 : 𝒜 ≤ mΩ) {P : Measure Ω}
    [IsFiniteMeasure P] {κ₁ κ₂ : Kernel Ω X} [IsMarkovKernel κ₁] [IsMarkovKernel κ₂]
    (h : ∀ A, MeasurableSet[𝒜] A → ∀ B, MeasurableSet B → (P ⊗ₘ κ₁) (A ×ˢ B) = (P ⊗ₘ κ₂) (A ×ˢ B))
    {F : Ω × X → ℝ≥0∞} (hF : Measurable[𝒜.prod mX] F) :
    ∫⁻ p, F p ∂(P ⊗ₘ κ₁) = ∫⁻ p, F p ∂(P ⊗ₘ κ₂) := by
  have hle := prod_le_prod_of_le (mX := mX) h𝒜
  suffices htrim : (P ⊗ₘ κ₁).trim hle = (P ⊗ₘ κ₂).trim hle by
    calc ∫⁻ p, F p ∂(P ⊗ₘ κ₁) = ∫⁻ p, F p ∂((P ⊗ₘ κ₁).trim hle) :=
          (lintegral_trim (μ := P ⊗ₘ κ₁) hle hF).symm
      _ = ∫⁻ p, F p ∂((P ⊗ₘ κ₂).trim hle) := by rw [htrim]
      _ = ∫⁻ p, F p ∂(P ⊗ₘ κ₂) := lintegral_trim (μ := P ⊗ₘ κ₂) hle hF
  have hgen : 𝒜.prod mX = MeasurableSpace.generateFrom
      (image2 (· ×ˢ ·) {A : Set Ω | MeasurableSet[𝒜] A} {B : Set X | MeasurableSet B}) :=
    (@generateFrom_prod Ω X 𝒜 mX).symm
  have hpi : IsPiSystem
      (image2 (· ×ˢ ·) {A : Set Ω | MeasurableSet[𝒜] A} {B : Set X | MeasurableSet B}) :=
    @isPiSystem_prod Ω X 𝒜 mX
  have hrect : ∀ A, MeasurableSet[𝒜] A → ∀ B, MeasurableSet B →
      (P ⊗ₘ κ₁).trim hle (A ×ˢ B) = (P ⊗ₘ κ₂).trim hle (A ×ˢ B) := by
    intro A hA B hB
    have hAB : MeasurableSet[𝒜.prod mX] (A ×ˢ B) := @MeasurableSet.prod Ω X 𝒜 mX _ _ hA hB
    rw [trim_measurableSet_eq hle hAB, trim_measurableSet_eq hle hAB]
    exact h A hA B hB
  have : @IsFiniteMeasure (Ω × X) (𝒜.prod mX) ((P ⊗ₘ κ₁).trim hle) := isFiniteMeasure_trim hle
  refine ext_of_generate_finite _ hgen hpi ?_ ?_
  · rintro _ ⟨A, hA, B, hB, rfl⟩
    exact hrect A hA B hB
  · have := hrect univ (@MeasurableSet.univ Ω 𝒜) univ MeasurableSet.univ
    rwa [univ_prod_univ] at this

/-- A kernel measurable for a sub-σ-algebra `𝒜 ≤ mΩ`, as a kernel for `mΩ`. -/
def kernelOfLE {𝒜 mΩ : MeasurableSpace Ω} (h𝒜 : 𝒜 ≤ mΩ) (κ : Kernel[𝒜] Ω X) : Kernel Ω X :=
  ⟨fun ω => κ ω, κ.measurable.mono h𝒜 le_rfl⟩

@[simp] theorem kernelOfLE_apply {𝒜 mΩ : MeasurableSpace Ω} (h𝒜 : 𝒜 ≤ mΩ) (κ : Kernel[𝒜] Ω X) (ω : Ω) :
    kernelOfLE h𝒜 κ ω = κ ω := rfl

theorem measurable_kernelOfLE {𝒜 mΩ : MeasurableSpace Ω} (h𝒜 : 𝒜 ≤ mΩ) (κ : Kernel[𝒜] Ω X) :
    Measurable[𝒜] fun ω => kernelOfLE h𝒜 κ ω :=
  κ.measurable

instance isMarkovKernel_kernelOfLE {𝒜 mΩ : MeasurableSpace Ω} (h𝒜 : 𝒜 ≤ mΩ) (κ : Kernel[𝒜] Ω X)
    [IsMarkovKernel κ] : IsMarkovKernel (kernelOfLE h𝒜 κ) :=
  ⟨fun ω => by rw [kernelOfLE_apply]; infer_instance⟩

/-- **An `𝒜`-measurable version of a kernel** (the conditional distribution of the second coordinate of
`P ⊗ κ` given the first one, read in `𝒜`): it has the same joint law on `𝒜`-rectangles. -/
theorem exists_kernel_condVersion [StandardBorelSpace X] [Nonempty X] {𝒜 mΩ : MeasurableSpace Ω}
    (h𝒜 : 𝒜 ≤ mΩ) (P : Measure Ω) [IsFiniteMeasure P] (κ : Kernel Ω X) [IsMarkovKernel κ] :
    ∃ κ' : Kernel Ω X, IsMarkovKernel κ' ∧ Measurable[𝒜] (fun ω => κ' ω) ∧
      ∀ A, MeasurableSet[𝒜] A → ∀ B, MeasurableSet B → (P ⊗ₘ κ') (A ×ˢ B) = (P ⊗ₘ κ) (A ×ˢ B) := by
  set ρ : Measure (Ω × X) := P ⊗ₘ κ with hρ
  have hfst : Measurable[mΩ.prod mX, 𝒜] (Prod.fst : Ω × X → Ω) := measurable_fst.mono le_rfl h𝒜
  set cd : Kernel[𝒜] Ω X := @condDistrib (Ω × X) Ω X _ _ _ (mΩ.prod mX) 𝒜 Prod.snd Prod.fst ρ _
    with hcd
  have hdis := @compProd_map_condDistrib (Ω × X) Ω X _ _ _ (mΩ.prod mX) ρ _ Prod.fst Prod.snd 𝒜
    ⟨Prod.fst, hfst, EventuallyEq.rfl⟩ (@measurable_snd Ω X mΩ mX).aemeasurable
  refine ⟨kernelOfLE h𝒜 cd, inferInstance, measurable_kernelOfLE h𝒜 cd, fun A hA B hB => ?_⟩
  have hA' : MeasurableSet[mΩ] A := h𝒜 A hA
  have hAB : MeasurableSet[𝒜.prod mX] (A ×ˢ B) := @MeasurableSet.prod Ω X 𝒜 mX _ _ hA hB
  -- evaluate the disintegration on the rectangle
  have hL := congrArg (fun μ => μ (A ×ˢ B)) hdis
  rw [@Measure.map_apply _ _ (mΩ.prod mX) (𝒜.prod mX) _ _
    ((hfst.prodMk measurable_snd)) _ hAB] at hL
  rw [@Measure.compProd_apply_prod Ω X 𝒜 mX _ _ _ _ _ _ hA hB] at hL
  -- the first marginal of `ρ` on `𝒜` is the trimmed `P`
  have hmarg : @Measure.map _ _ (mΩ.prod mX) 𝒜 Prod.fst ρ = P.trim h𝒜 := by
    refine @Measure.ext _ 𝒜 _ _ fun S hS => ?_
    rw [@Measure.map_apply _ _ (mΩ.prod mX) 𝒜 _ _ hfst _ hS, trim_measurableSet_eq h𝒜 hS,
      ← Set.prod_univ, hρ, Measure.compProd_apply_prod (h𝒜 S hS) MeasurableSet.univ]
    simp
  rw [hmarg, restrict_trim h𝒜 P hA,
    lintegral_trim (μ := P.restrict A) h𝒜 (f := fun ω => cd ω B)
      ((Measure.measurable_coe hB).comp cd.measurable)] at hL
  rw [Measure.compProd_apply_prod hA' hB, Measure.compProd_apply_prod hA' hB]
  simp only [kernelOfLE_apply]
  rw [hL, hρ, show (fun a : Ω × X => (a.1, a.2)) ⁻¹' (A ×ˢ B) = A ×ˢ B from rfl,
    Measure.compProd_apply_prod hA' hB]

/-- Gluing a finite family of kernels along a measurable index: `ω ↦ κ (S ω) ω`. -/
theorem measurable_glue {ι : Type*} [Fintype ι] {m : MeasurableSpace Ω} {S : Ω → ι}
    (hS : ∀ i, MeasurableSet[m] {ω | S ω = i}) {κ : ι → Ω → Measure X}
    (hκ : ∀ i, Measurable[m] (κ i)) : Measurable[m] fun ω => κ (S ω) ω := by
  classical
  refine @Measure.measurable_of_measurable_coe _ _ _ m _ fun B hB => ?_
  have : (fun ω => κ (S ω) ω B) = fun ω => ∑ i, {ω | S ω = i}.indicator (fun ω => κ i ω B) ω := by
    funext ω
    rw [Finset.sum_eq_single (S ω)]
    · simp
    · intro i _ hi
      simp [Set.indicator, Ne.symm hi]
    · simp
  rw [this]
  exact Finset.measurable_sum _ fun i _ =>
    (((Measure.measurable_coe hB).comp (hκ i)).indicator (hS i))

/-- The glued kernel `ω ↦ κ (S ω) ω`. -/
def kernelGlue {ι : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω} (S : Ω → ι)
    (hS : ∀ i, MeasurableSet {ω | S ω = i}) (κ : ι → Kernel Ω X) : Kernel Ω X :=
  ⟨fun ω => κ (S ω) ω, measurable_glue hS fun i => (κ i).measurable⟩

@[simp] theorem kernelGlue_apply {ι : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω} (S : Ω → ι)
    (hS : ∀ i, MeasurableSet {ω | S ω = i}) (κ : ι → Kernel Ω X) (ω : Ω) :
    kernelGlue S hS κ ω = κ (S ω) ω := rfl

instance isMarkovKernel_kernelGlue {ι : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω} (S : Ω → ι)
    (hS : ∀ i, MeasurableSet {ω | S ω = i}) (κ : ι → Kernel Ω X) [∀ i, IsMarkovKernel (κ i)] :
    IsMarkovKernel (kernelGlue S hS κ) :=
  ⟨fun ω => by rw [kernelGlue_apply]; infer_instance⟩

end General

/-! ### `Ω` read in a sub-σ-algebra -/

/-- `Ω` with the σ-algebra `𝒜` (a type synonym, so that kernels measurable for `𝒜` use the standard instances). -/
def WithSigma (Ω : Type*) (_𝒜 : MeasurableSpace Ω) : Type _ := Ω

instance WithSigma.instMeasurableSpace {Ω : Type*} (𝒜 : MeasurableSpace Ω) :
    MeasurableSpace (WithSigma Ω 𝒜) := 𝒜

section Restrict

variable {Ω : Type*}

/-- **The conditional law of the field given its restriction to `V`.** For an `𝒜`-measurable Markov kernel
`η : Ω → 𝒟'(ℍ)` there is a Markov kernel `C : Ω × 𝒟'(V) → 𝒟'(ℍ)`, measurable for `𝒜 ⊗ 𝔅`, disintegrating
`η ω` over `h ↦ h|_V`, and `C (ω, g)` is concentrated on `{h | h|_V = g}` for `η ω`-almost every restriction `g`. -/
theorem exists_condKernel_restrictDist {𝒜 mΩ : MeasurableSpace Ω} (h𝒜 : 𝒜 ≤ mΩ)
    (η : Kernel Ω (DistOn upperHalfPlaneOpens)) [IsMarkovKernel η] (hη : Measurable[𝒜] fun ω => η ω)
    (V : TopologicalSpace.Opens ℂ) :
    ∃ C : Kernel (Ω × DistOn V) (DistOn upperHalfPlaneOpens), IsMarkovKernel C ∧
      Measurable[𝒜.prod inferInstance] (fun p => C p) ∧
      (∀ ω B, MeasurableSet B → η ω B = ∫⁻ g, C (ω, g) B ∂((η ω).map (restrictDist V))) ∧
      ∀ ω, ∀ᵐ g ∂((η ω).map (restrictDist V)), C (ω, g) {h | restrictDist V h ≠ g} = 0 := by
  set η' : Kernel (WithSigma Ω 𝒜) (DistOn upperHalfPlaneOpens) := ⟨fun ω => η ω, hη⟩ with hη'
  have : IsMarkovKernel η' := ⟨fun ω => (inferInstance : IsMarkovKernel η).isProbabilityMeasure ω⟩
  have hr : Measurable (restrictDist V (D := upperHalfPlaneOpens)) := measurable_restrictDist V
  have hpair : Measurable fun h : DistOn upperHalfPlaneOpens => (restrictDist V h, h) :=
    hr.prodMk measurable_id
  set κ : Kernel (WithSigma Ω 𝒜) (DistOn V × DistOn upperHalfPlaneOpens) :=
    η'.map fun h => (restrictDist V h, h) with hκ
  have hfst : κ.fst = η'.map (restrictDist V) := Kernel.fst_map_prod η' measurable_id
  set C' := κ.condKernel with hC'
  have hdis : κ.fst ⊗ₖ C' = κ := Kernel.disintegrate κ C'
  have hle : (𝒜.prod (inferInstance : MeasurableSpace (DistOn V))) ≤
      (mΩ.prod (inferInstance : MeasurableSpace (DistOn V))) := prod_le_prod_of_le h𝒜
  have key1 : ∀ (ω : WithSigma Ω 𝒜) (B : Set (DistOn upperHalfPlaneOpens)), MeasurableSet B →
      η' ω B = ∫⁻ g, C' (ω, g) B ∂((η' ω).map (restrictDist V)) := by
    intro ω B hB
    have h1 : κ ω (univ ×ˢ B) = η' ω B := by
      rw [hκ, Kernel.map_apply' _ hpair _ (MeasurableSet.univ.prod hB)]
      congr 1
      ext h; simp
    rw [← h1, ← hdis, Kernel.compProd_apply_prod MeasurableSet.univ hB, Measure.restrict_univ, hfst,
      Kernel.map_apply _ hr]
  have key2 : ∀ ω : WithSigma Ω 𝒜,
      ∀ᵐ g ∂((η' ω).map (restrictDist V)), C' (ω, g) {h | restrictDist V h ≠ g} = 0 := by
    intro ω
    set G : Set (DistOn V × DistOn upperHalfPlaneOpens) := {p | restrictDist V p.2 ≠ p.1} with hG
    have hGm : MeasurableSet G :=
      (measurableSet_eq_fun (hr.comp measurable_snd) measurable_fst).compl
    have h0 : κ ω G = 0 := by
      rw [hκ, Kernel.map_apply' _ hpair _ hGm]
      have : (fun h : DistOn upperHalfPlaneOpens => (restrictDist V h, h)) ⁻¹' G = ∅ := by
        ext h; simp [hG]
      rw [this, measure_empty]
    rw [← hdis, Kernel.compProd_apply hGm] at h0
    have hmeas : Measurable fun g : DistOn V => C' (ω, g) (Prod.mk g ⁻¹' G) :=
      Kernel.measurable_kernel_prodMk_left' hGm ω
    have := (lintegral_eq_zero_iff hmeas).1 h0
    rw [hfst, Kernel.map_apply _ hr] at this
    filter_upwards [this] with g hg
    exact hg
  refine ⟨⟨fun p => C' p, C'.measurable.mono hle le_rfl⟩,
    ⟨fun p => (inferInstance : IsMarkovKernel C').isProbabilityMeasure p⟩, C'.measurable,
    fun ω B hB => key1 ω B hB, fun ω => key2 ω⟩

end Restrict


/-! ### One stage of the finite-family construction -/

section Stage

variable {Ω X : Type*} [mX : MeasurableSpace X]

theorem lintegral_compProd_indicator {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {κ : Kernel Ω X} [IsMarkovKernel κ] {A : Set Ω} (hA : MeasurableSet A) {f : Ω × X → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ p, (A ×ˢ univ).indicator f p ∂(P ⊗ₘ κ) = ∫⁻ ω in A, ∫⁻ x, f (ω, x) ∂κ ω ∂P := by
  rw [Measure.lintegral_compProd (hf.indicator (hA.prod MeasurableSet.univ)),
    ← lintegral_indicator hA]
  congr 1
  funext ω
  by_cases hω : ω ∈ A
  · simp [Set.indicator, hω]
  · simp [Set.indicator, hω]

/-- **One stage of the forward construction** (Astra pp. 5–6, without the resampling of `P_V h`). Let `η` be an
`𝒜`-measurable field kernel whose restriction to `V` has, on `𝒜`-rectangles, the joint law of a kernel `Q`, and let
`Q'` have the same joint law as `Q` on `𝒜`-rectangles ((1.8)). Then there is an `𝒜'`-measurable field kernel `η'`
with the same joint law as `η` on `𝒜`-rectangles (the old history–field law is unchanged) whose restriction to `V`
has the joint law of `Q'` on `𝒜'`-rectangles. Construction: `η' ω = ∫ C(ω, g) dQ̄'(ω)(g)`, with `C` the conditional
law of `η` given the restriction (`exists_condKernel_restrictDist`) and `Q̄'` an `𝒜'`-measurable version of `Q'`. -/
theorem exists_stage {𝒜 𝒜' mΩ : MeasurableSpace Ω} (h𝒜 : 𝒜 ≤ 𝒜') (h𝒜' : 𝒜' ≤ mΩ) (P : Measure Ω)
    [IsFiniteMeasure P] (η : Kernel Ω (DistOn upperHalfPlaneOpens)) [IsMarkovKernel η]
    (hη : Measurable[𝒜] fun ω => η ω) (V : TopologicalSpace.Opens ℂ) (Q Q' : Kernel Ω (DistOn V))
    [IsMarkovKernel Q] [IsMarkovKernel Q']
    (hηQ : ∀ A, MeasurableSet[𝒜] A → ∀ B, MeasurableSet B →
      (P ⊗ₘ η.map (restrictDist V)) (A ×ˢ B) = (P ⊗ₘ Q) (A ×ˢ B))
    (hQQ' : ∀ A, MeasurableSet[𝒜] A → ∀ B, MeasurableSet B →
      (P ⊗ₘ Q') (A ×ˢ B) = (P ⊗ₘ Q) (A ×ˢ B)) :
    ∃ η' : Kernel Ω (DistOn upperHalfPlaneOpens), IsMarkovKernel η' ∧
      Measurable[𝒜'] (fun ω => η' ω) ∧
      (∀ A, MeasurableSet[𝒜] A → ∀ B, MeasurableSet B → (P ⊗ₘ η') (A ×ˢ B) = (P ⊗ₘ η) (A ×ˢ B)) ∧
      ∀ A, MeasurableSet[𝒜'] A → ∀ B, MeasurableSet B →
        (P ⊗ₘ η'.map (restrictDist V)) (A ×ˢ B) = (P ⊗ₘ Q') (A ×ˢ B) := by
  have h𝒜m : 𝒜 ≤ mΩ := h𝒜.trans h𝒜'
  have hr : Measurable (restrictDist V (D := upperHalfPlaneOpens)) := measurable_restrictDist V
  obtain ⟨Qb, hQb, hQbm, hQbr⟩ := exists_kernel_condVersion h𝒜' P Q'
  obtain ⟨C, hC, hCm, hCη, hCc⟩ := exists_condKernel_restrictDist h𝒜m η hη V
  -- the new kernel
  set η' : Kernel Ω (DistOn upperHalfPlaneOpens) := Kernel.snd (Qb ⊗ₖ C) with hη'
  have hη'B : ∀ ω B, MeasurableSet B → η' ω B = ∫⁻ g, C (ω, g) B ∂(Qb ω) := by
    intro ω B hB
    rw [hη', Kernel.snd_apply' _ _ hB, show (Prod.snd ⁻¹' B : Set (DistOn V × _)) = univ ×ˢ B by
      ext; simp, Kernel.compProd_apply_prod MeasurableSet.univ hB, Measure.restrict_univ]
  -- rectangle agreements on `𝒜`
  have hQbQ : ∀ A, MeasurableSet[𝒜] A → ∀ B, MeasurableSet B →
      (P ⊗ₘ Qb) (A ×ˢ B) = (P ⊗ₘ Q) (A ×ˢ B) := fun A hA B hB =>
    (hQbr A (h𝒜 A hA) B hB).trans (hQQ' A hA B hB)
  have hQbη : ∀ A, MeasurableSet[𝒜] A → ∀ B, MeasurableSet B →
      (P ⊗ₘ Qb) (A ×ˢ B) = (P ⊗ₘ η.map (restrictDist V)) (A ×ˢ B) := fun A hA B hB =>
    (hQbQ A hA B hB).trans (hηQ A hA B hB).symm
  have hCB : ∀ B : Set (DistOn upperHalfPlaneOpens), MeasurableSet B →
      Measurable[𝒜.prod inferInstance] fun p : Ω × DistOn V => C p B := fun B hB =>
    (Measure.measurable_coe hB).comp hCm
  -- measurability of `η'` for `𝒜'`
  have hη'm : Measurable[𝒜'] fun ω => η' ω := by
    refine @Measure.measurable_of_measurable_coe _ _ _ 𝒜' _ fun B hB => ?_
    have hf : Measurable[(𝒜'.prod inferInstance)] fun p : Ω × DistOn V => C p B :=
      (hCB B hB).mono (prod_le_prod_of_le h𝒜) le_rfl
    set Qb' : Kernel (WithSigma Ω 𝒜') (DistOn V) := ⟨fun ω => Qb ω, hQbm⟩
    have hQb'm : IsMarkovKernel Qb' := ⟨fun ω => hQb.isProbabilityMeasure ω⟩
    have := @Measurable.lintegral_kernel_prod_right' (WithSigma Ω 𝒜') (DistOn V) _ _ Qb' _
      (fun p : WithSigma Ω 𝒜' × DistOn V => C p B) hf
    rw [show (fun ω => η' ω B) = fun ω => ∫⁻ g, C (ω, g) B ∂(Qb ω) from
      funext fun ω => hη'B ω B hB]
    exact this
  have : IsMarkovKernel (η.map (restrictDist V)) := Kernel.IsMarkovKernel.map η hr
  refine ⟨η', inferInstance, hη'm, fun A hA B hB => ?_, fun A hA B hB => ?_⟩
  · -- the old joint law is unchanged
    have hA' : MeasurableSet[mΩ] A := h𝒜m A hA
    have hF : Measurable[𝒜.prod inferInstance]
        ((A ×ˢ univ).indicator fun p : Ω × DistOn V => C p B) :=
      (hCB B hB).indicator (@MeasurableSet.prod Ω _ 𝒜 _ _ _ hA MeasurableSet.univ)
    have hFm : Measurable fun p : Ω × DistOn V => C p B :=
      (hCB B hB).mono (prod_le_prod_of_le h𝒜m) le_rfl
    calc (P ⊗ₘ η') (A ×ˢ B) = ∫⁻ ω in A, η' ω B ∂P := Measure.compProd_apply_prod hA' hB
      _ = ∫⁻ ω in A, ∫⁻ g, C (ω, g) B ∂(Qb ω) ∂P := by
          refine setLIntegral_congr_fun hA' fun ω _ => hη'B ω B hB
      _ = ∫⁻ p, (A ×ˢ univ).indicator (fun p : Ω × DistOn V => C p B) p ∂(P ⊗ₘ Qb) :=
          (lintegral_compProd_indicator hA' hFm).symm
      _ = ∫⁻ p, (A ×ˢ univ).indicator (fun p : Ω × DistOn V => C p B) p
            ∂(P ⊗ₘ η.map (restrictDist V)) := lintegral_compProd_eq_of_rect h𝒜m hQbη hF
      _ = ∫⁻ ω in A, ∫⁻ g, C (ω, g) B ∂((η.map (restrictDist V)) ω) ∂P :=
          lintegral_compProd_indicator hA' hFm
      _ = ∫⁻ ω in A, η ω B ∂P := by
          refine setLIntegral_congr_fun hA' fun ω _ => ?_
          rw [Kernel.map_apply _ hr, ← hCη ω B hB]
      _ = (P ⊗ₘ η) (A ×ˢ B) := (Measure.compProd_apply_prod hA' hB).symm
  · -- the new restriction law
    have hA' : MeasurableSet[mΩ] A := h𝒜' A hA
    set N : Set (Ω × DistOn V) := {p | C p {h | restrictDist V h ≠ p.2} ≠ 0} with hN
    have hNm : MeasurableSet[𝒜.prod inferInstance] N := by
      set C𝒜 : Kernel (WithSigma Ω 𝒜 × DistOn V) (DistOn upperHalfPlaneOpens) := ⟨fun p => C p, hCm⟩
      have : IsMarkovKernel C𝒜 := ⟨fun p => hC.isProbabilityMeasure p⟩
      have hG : MeasurableSet {q : (WithSigma Ω 𝒜 × DistOn V) × DistOn upperHalfPlaneOpens |
          restrictDist V q.2 ≠ q.1.2} :=
        (measurableSet_eq_fun (hr.comp measurable_snd) (measurable_snd.comp measurable_fst)).compl
      have := Kernel.measurable_kernel_prodMk_left (κ := C𝒜) hG
      exact (this (measurableSet_singleton 0)).compl
    have hNm' : MeasurableSet N := prod_le_prod_of_le h𝒜m N hNm
    have hN0 : (P ⊗ₘ η.map (restrictDist V)) N = 0 := by
      rw [Measure.compProd_apply hNm']
      have hz : ∀ a, (η.map (restrictDist V)) a (Prod.mk a ⁻¹' N) = 0 := fun a => by
        rw [Kernel.map_apply _ hr]
        exact ae_iff.1 (hCc a)
      simp [hz]
    have hNb : (P ⊗ₘ Qb) N = 0 := by
      have h1 := lintegral_compProd_eq_of_rect h𝒜m hQbη
        (F := N.indicator 1) ((measurable_const.indicator hNm))
      rw [lintegral_indicator_one hNm', lintegral_indicator_one hNm'] at h1
      rw [h1, hN0]
    have hpt : ∀ p : Ω × DistOn V, p ∉ N → C p (restrictDist V ⁻¹' B) = B.indicator 1 p.2 := by
      intro p hp
      have hp0 : C p {h | restrictDist V h ≠ p.2} = 0 := by
        simpa [hN] using hp
      have hCp : IsProbabilityMeasure (C p) := hC.isProbabilityMeasure p
      by_cases hpB : p.2 ∈ B
      · rw [Set.indicator_of_mem hpB, Pi.one_apply]
        refine (prob_compl_eq_zero_iff (hr hB)).1 (measure_mono_null ?_ hp0)
        intro h hh
        simp only [mem_compl_iff, mem_preimage] at hh
        intro heq
        exact hh (heq ▸ hpB)
      · rw [Set.indicator_of_notMem hpB]
        refine measure_mono_null ?_ hp0
        intro h hh heq
        exact hpB (heq ▸ hh)
    have hFm : Measurable fun p : Ω × DistOn V => C p (restrictDist V ⁻¹' B) :=
      ((Measure.measurable_coe (hr hB)).comp hCm).mono (prod_le_prod_of_le h𝒜m) le_rfl
    have hBm : Measurable fun p : Ω × DistOn V => B.indicator (1 : DistOn V → ℝ≥0∞) p.2 :=
      (measurable_const.indicator hB).comp measurable_snd
    calc (P ⊗ₘ η'.map (restrictDist V)) (A ×ˢ B)
        = ∫⁻ ω in A, (η'.map (restrictDist V)) ω B ∂P := Measure.compProd_apply_prod hA' hB
      _ = ∫⁻ ω in A, ∫⁻ g, C (ω, g) (restrictDist V ⁻¹' B) ∂(Qb ω) ∂P := by
          refine setLIntegral_congr_fun hA' fun ω _ => ?_
          rw [Kernel.map_apply' _ hr _ hB, hη'B ω _ (hr hB)]
      _ = ∫⁻ p, (A ×ˢ univ).indicator (fun p : Ω × DistOn V => C p (restrictDist V ⁻¹' B)) p
            ∂(P ⊗ₘ Qb) := (lintegral_compProd_indicator hA' hFm).symm
      _ = ∫⁻ p, (A ×ˢ univ).indicator (fun p : Ω × DistOn V => B.indicator 1 p.2) p
            ∂(P ⊗ₘ Qb) := by
          refine lintegral_congr_ae ?_
          have hae : ∀ᵐ p ∂(P ⊗ₘ Qb), p ∉ N := measure_eq_zero_iff_ae_notMem.1 hNb
          filter_upwards [hae] with p hp
          by_cases hpA : p ∈ A ×ˢ univ
          · rw [Set.indicator_of_mem hpA, Set.indicator_of_mem hpA, hpt p hp]
          · rw [Set.indicator_of_notMem hpA, Set.indicator_of_notMem hpA]
      _ = ∫⁻ ω in A, ∫⁻ g, B.indicator 1 g ∂(Qb ω) ∂P := lintegral_compProd_indicator hA' hBm
      _ = ∫⁻ ω in A, Qb ω B ∂P := by
          refine setLIntegral_congr_fun hA' fun ω _ => ?_
          rw [lintegral_indicator_one hB]
      _ = (P ⊗ₘ Qb) (A ×ˢ B) := (Measure.compProd_apply_prod hA' hB).symm
      _ = (P ⊗ₘ Q') (A ×ˢ B) := hQbr A hA B hB

end Stage

end Coupling

end InteractingSLE
