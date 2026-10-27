import MatedCRTHarmonic.GMS4.Prop48PrimedIntegral
import MatedCRTHarmonic.GMS4.Prop48CanonicalMoments
import MatedCRTHarmonic.GMS4O.Prop48OAssembly

/-!
# A jointly measurable version of the (4.28) conditional mean

`GMS4.Canonical.conditionalMean D hγ ε q ζ ω z` is defined separately at each centre `z` as Mathlib's
conditional expectation `P[maskedUStar z | σ(circleObservation z)]`. Mathlib picks one
representative per centre, by choice, so nothing can be proved about `z ↦ conditionalMean ω z` for a
fixed sample. The spatial integrals of [18] (4.28)–(4.38)
 need a version that is jointly measurable in `(ω, z)`.

This file builds such a version from the disintegration of the kernel
`z ↦ law(Y_z, X_z)`, where `Y` is the pair of conditioning circle averages and `X` the masked
density. Both are built from measurable versions of the *fields*, so they agree with the literal
objects for all centres at once on one probability-one event. Mathlib's `Kernel.condKernel` gives a
jointly measurable conditional kernel, and `m(ω, z) := ∫ x⁺ d condKernel(z, Y_z(ω))`.

* `p48o_condMean_ae_eq_condExp` (generic): for **every** centre `z`, `m(·, z)` is a version of
  `E[X_z | σ(Y'_z)]` for any measurable `Y'_z` a.s. equal to `Y_z`.
* `p48oCondMeanJoint` (canonical) and `p48o_condMeanJoint_ae_eq_conditionalMean`: for every centre with
  integrable masked density, `m(·, z) =ᵐ Canonical.conditionalMean(·, z)`.
* The Tonelli consequences in the shapes of the H4 fields: spatial integrability, the a.s. mean
  bound and a.e.-measurability of the centred integral, from the Proposition 4.8 premise supplied to H4.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4O

/-! ### Generic construction -/

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- The kernel `z ↦ law(Y(·, z), X(·, z))`. -/
def p48oPairKernel (Y : Ω → ℂ → ℝ × ℝ) (X : Ω → ℂ → ℝ) : Kernel ℂ ((ℝ × ℝ) × ℝ) :=
  (Kernel.const ℂ P ×ₖ Kernel.id).map (fun p : Ω × ℂ => (Y p.1 p.2, X p.1 p.2))

instance p48oPairKernel.instIsFiniteKernel (Y : Ω → ℂ → ℝ × ℝ) (X : Ω → ℂ → ℝ) :
    IsFiniteKernel (p48oPairKernel P Y X) := by
  unfold p48oPairKernel
  infer_instance

lemma p48oPairKernel_apply {Y : Ω → ℂ → ℝ × ℝ} {X : Ω → ℂ → ℝ}
    (hY : Measurable fun p : Ω × ℂ => Y p.1 p.2) (hX : Measurable fun p : Ω × ℂ => X p.1 p.2)
    (z : ℂ) : p48oPairKernel P Y X z = P.map (fun ω => (Y ω z, X ω z)) := by
  have hF : Measurable fun p : Ω × ℂ => (Y p.1 p.2, X p.1 p.2) := hY.prodMk hX
  rw [p48oPairKernel, Kernel.map_apply _ hF, Kernel.prod_apply, Kernel.const_apply,
    Kernel.id_apply, Measure.prod_dirac,
    Measure.map_map hF (measurable_prodMk_right (y := z) : Measurable fun x : Ω => (x, z))]
  rfl

/-- The conditional value `g(z, y) = ∫ x⁺ d(condKernel)(z, y)`. -/
def p48oCondValue (Y : Ω → ℂ → ℝ × ℝ) (X : Ω → ℂ → ℝ) (p : ℂ × (ℝ × ℝ)) : ℝ :=
  ∫ x, max x 0 ∂(Kernel.condKernel (p48oPairKernel P Y X) p)

/-- **The jointly measurable conditional mean** `m(ω, z) = g(z, Y(ω, z))`. -/
def p48oCondMean (Y : Ω → ℂ → ℝ × ℝ) (X : Ω → ℂ → ℝ) (ω : Ω) (z : ℂ) : ℝ :=
  p48oCondValue P Y X (z, Y ω z)

lemma measurable_p48oCondValue (Y : Ω → ℂ → ℝ × ℝ) (X : Ω → ℂ → ℝ) :
    Measurable (p48oCondValue P Y X) := by
  have h : StronglyMeasurable fun q : (ℂ × (ℝ × ℝ)) × ℝ => max q.2 0 :=
    (measurable_snd.max measurable_const).stronglyMeasurable
  exact (h.integral_kernel_prod_right' (κ := Kernel.condKernel (p48oPairKernel P Y X))).measurable

lemma p48oCondValue_nonneg (Y : Ω → ℂ → ℝ × ℝ) (X : Ω → ℂ → ℝ) (p : ℂ × (ℝ × ℝ)) :
    0 ≤ p48oCondValue P Y X p :=
  integral_nonneg fun x => le_max_right x 0

lemma p48oCondMean_nonneg (Y : Ω → ℂ → ℝ × ℝ) (X : Ω → ℂ → ℝ) (ω : Ω) (z : ℂ) :
    0 ≤ p48oCondMean P Y X ω z :=
  p48oCondValue_nonneg P Y X _

/-- Joint measurability of the conditional mean. -/
lemma measurable_p48oCondMean {Y : Ω → ℂ → ℝ × ℝ} (X : Ω → ℂ → ℝ)
    (hY : Measurable fun p : Ω × ℂ => Y p.1 p.2) :
    Measurable fun p : Ω × ℂ => p48oCondMean P Y X p.1 p.2 :=
  (measurable_p48oCondValue P Y X).comp (measurable_snd.prodMk hY)

/-- **Defining identity at one centre.** For every Borel `B`, the conditional mean has the same
integral as `X_z` over `{Y_z ∈ B}`; it is integrable. -/
theorem p48o_condMean_setIntegral {Y : Ω → ℂ → ℝ × ℝ} {X : Ω → ℂ → ℝ}
    (hY : Measurable fun p : Ω × ℂ => Y p.1 p.2) (hX : Measurable fun p : Ω × ℂ => X p.1 p.2)
    (z : ℂ) (hXint : Integrable (fun ω => X ω z) P) (hX0 : ∀ ω, 0 ≤ X ω z) :
    Integrable (fun ω => p48oCondMean P Y X ω z) P ∧
      ∀ B : Set (ℝ × ℝ), MeasurableSet B →
        ∫ ω in (fun ω => Y ω z) ⁻¹' B, p48oCondMean P Y X ω z ∂P =
          ∫ ω in (fun ω => Y ω z) ⁻¹' B, X ω z ∂P := by
  set κ := p48oPairKernel P Y X with hκ
  have hYz : Measurable fun ω => Y ω z := hY.comp (measurable_id.prodMk measurable_const)
  have hXz : Measurable fun ω => X ω z := hX.comp (measurable_id.prodMk measurable_const)
  have hF : Measurable fun ω => (Y ω z, X ω z) := hYz.prodMk hXz
  have hκz : κ z = P.map (fun ω => (Y ω z, X ω z)) := p48oPairKernel_apply P hY hX z
  have hfst : κ.fst z = P.map (fun ω => Y ω z) := by
    rw [Kernel.fst_apply, hκz, Measure.map_map measurable_fst hF]
    rfl
  have hdis : (κ.fst ⊗ₖ Kernel.condKernel κ) z = κ z := by rw [Kernel.disintegrate]
  have hgm : Measurable fun y : ℝ × ℝ => p48oCondValue P Y X (z, y) :=
    (measurable_p48oCondValue P Y X).comp (measurable_const.prodMk measurable_id)
  -- the positive part is integrable under the joint law
  have hpos : Integrable (fun q : (ℝ × ℝ) × ℝ => max q.2 0) (κ z) := by
    rw [hκz, integrable_map_measure
      (measurable_snd.max measurable_const).aestronglyMeasurable hF.aemeasurable]
    refine hXint.congr (Eventually.of_forall fun ω => ?_)
    simp only [Function.comp_apply, max_eq_left (hX0 ω)]
  have hpos' : Integrable (fun q : (ℝ × ℝ) × ℝ => max q.2 0)
      ((κ.fst ⊗ₖ Kernel.condKernel κ) z) := by rw [hdis]; exact hpos
  -- the conditional value is integrable under the law of `Y_z`
  have hgint : Integrable (fun y : ℝ × ℝ => p48oCondValue P Y X (z, y)) (κ.fst z) :=
    hpos'.integral_compProd
  have hgintP : Integrable (fun ω => p48oCondMean P Y X ω z) P := by
    rw [hfst] at hgint
    exact (integrable_map_measure hgm.aestronglyMeasurable hYz.aemeasurable).1 hgint
  refine ⟨hgintP, fun B hB => ?_⟩
  have hBset : MeasurableSet (B ×ˢ (univ : Set ℝ)) := hB.prod MeasurableSet.univ
  set G : (ℝ × ℝ) × ℝ → ℝ := (B ×ˢ (univ : Set ℝ)).indicator fun q => max q.2 0 with hG
  have hGint : Integrable G ((κ.fst ⊗ₖ Kernel.condKernel κ) z) := hpos'.indicator hBset
  have hGm : Measurable G := (measurable_snd.max measurable_const).indicator hBset
  calc ∫ ω in (fun ω => Y ω z) ⁻¹' B, p48oCondMean P Y X ω z ∂P
      = ∫ y in B, p48oCondValue P Y X (z, y) ∂(P.map fun ω => Y ω z) := by
        rw [setIntegral_map hB hgm.aestronglyMeasurable hYz.aemeasurable]
        rfl
    _ = ∫ y, B.indicator (fun y => p48oCondValue P Y X (z, y)) y ∂(κ.fst z) := by
        rw [integral_indicator hB, hfst]
    _ = ∫ y, ∫ x, G (y, x) ∂(Kernel.condKernel κ (z, y)) ∂(κ.fst z) := by
        congr 1
        funext y
        by_cases hy : y ∈ B
        · rw [Set.indicator_of_mem hy]
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only [hG, Set.indicator_of_mem (show (y, x) ∈ B ×ˢ (univ : Set ℝ) from
            ⟨hy, mem_univ x⟩)]
        · rw [Set.indicator_of_notMem hy]
          symm
          refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
          simp only [hG, Set.indicator_of_notMem (show (y, x) ∉ B ×ˢ (univ : Set ℝ) from
            fun h => hy h.1), Pi.zero_apply]
    _ = ∫ q, G q ∂((κ.fst ⊗ₖ Kernel.condKernel κ) z) := (integral_compProd hGint).symm
    _ = ∫ q, G q ∂(P.map fun ω => (Y ω z, X ω z)) := by rw [hdis, hκz]
    _ = ∫ ω, G (Y ω z, X ω z) ∂P := integral_map hF.aemeasurable hGm.aestronglyMeasurable
    _ = ∫ ω in (fun ω => Y ω z) ⁻¹' B, X ω z ∂P := by
        rw [← integral_indicator (hYz hB)]
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        by_cases hω : ω ∈ (fun ω => Y ω z) ⁻¹' B
        · rw [Set.indicator_of_mem hω]
          simp only [hG, Set.indicator_of_mem (show (Y ω z, X ω z) ∈ B ×ˢ (univ : Set ℝ) from
            ⟨hω, mem_univ _⟩), max_eq_left (hX0 ω)]
        · rw [Set.indicator_of_notMem hω]
          simp only [hG, Set.indicator_of_notMem (show (Y ω z, X ω z) ∉ B ×ˢ (univ : Set ℝ) from
            fun h => hω h.1)]

/-- **The jointly measurable conditional mean is a version of the conditional expectation at every
centre**, given any measurable conditioning variable and density a.s. equal to the ones used to
build it. -/
theorem p48o_condMean_ae_eq_condExp {Y : Ω → ℂ → ℝ × ℝ} {X : Ω → ℂ → ℝ}
    (hY : Measurable fun p : Ω × ℂ => Y p.1 p.2) (hX : Measurable fun p : Ω × ℂ => X p.1 p.2)
    (z : ℂ) (hX0 : ∀ ω, 0 ≤ X ω z)
    {Y' : Ω → ℝ × ℝ} (hY' : Measurable Y') (hYY' : (fun ω => Y ω z) =ᵐ[P] Y')
    {X' : Ω → ℝ} (hX' : Integrable X' P) (hXX' : (fun ω => X ω z) =ᵐ[P] X') :
    (fun ω => p48oCondMean P Y X ω z) =ᵐ[P] P[X' | MeasurableSpace.comap Y' inferInstance] := by
  have hXint : Integrable (fun ω => X ω z) P := hX'.congr hXX'.symm
  obtain ⟨hgint, hset⟩ := p48o_condMean_setIntegral P hY hX z hXint hX0
  have hm : MeasurableSpace.comap Y' inferInstance ≤ ‹MeasurableSpace Ω› := hY'.comap_le
  have hgm : Measurable fun y : ℝ × ℝ => p48oCondValue P Y X (z, y) :=
    (measurable_p48oCondValue P Y X).comp (measurable_const.prodMk measurable_id)
  -- the version read through `Y'`
  set g' : Ω → ℝ := fun ω => p48oCondValue P Y X (z, Y' ω) with hg'
  have hgg' : (fun ω => p48oCondMean P Y X ω z) =ᵐ[P] g' := by
    filter_upwards [hYY'] with ω hω
    simp only [p48oCondMean, hg', hω]
  have hg'int : Integrable g' P := hgint.congr hgg'
  have hg'm : StronglyMeasurable[MeasurableSpace.comap Y' inferInstance] g' :=
    (hgm.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable
  have hpre : ∀ B : Set (ℝ × ℝ), (fun ω => Y ω z) ⁻¹' B =ᵐ[P] Y' ⁻¹' B := by
    intro B
    filter_upwards [hYY'] with ω hω
    simp only [Set.mem_preimage, hω]
  refine hgg'.trans (ae_eq_condExp_of_forall_setIntegral_eq hm hX'
    (fun s _ _ => hg'int.integrableOn) (fun s hs _ => ?_) hg'm.aestronglyMeasurable)
  obtain ⟨B, hB, rfl⟩ := hs
  calc ∫ ω in Y' ⁻¹' B, g' ω ∂P
      = ∫ ω in (fun ω => Y ω z) ⁻¹' B, g' ω ∂P := setIntegral_congr_set (hpre B).symm
    _ = ∫ ω in (fun ω => Y ω z) ⁻¹' B, p48oCondMean P Y X ω z ∂P :=
        integral_congr_ae (ae_restrict_of_ae hgg'.symm)
    _ = ∫ ω in (fun ω => Y ω z) ⁻¹' B, X ω z ∂P := hset B hB
    _ = ∫ ω in (fun ω => Y ω z) ⁻¹' B, X' ω ∂P := integral_congr_ae (ae_restrict_of_ae hXX')
    _ = ∫ ω in Y' ⁻¹' B, X' ω ∂P := setIntegral_congr_set (hpre B)

end Generic

/-! ### The canonical zero-cone instance -/

section Canonical

open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4.Canonical

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- A measurable version of the zero-cone field of the reference sample. -/
def p48oZeroConeFieldVersion
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) : Ω → MatedCRT.Field :=
  (MatedCRTHarmonic.Canon.aemeasurable_reference_field D hγ).mk _

lemma measurable_p48oZeroConeFieldVersion
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) : Measurable (p48oZeroConeFieldVersion D hγ) :=
  (MatedCRTHarmonic.Canon.aemeasurable_reference_field D hγ).measurable_mk

/-- The jointly measurable pair of conditioning circle averages, with the IG phase. -/
def p48oObsVersion
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (ω : Ω) (z : ℂ) : ℝ × ℝ :=
  (LQGMetric.circleAvg (p48oZeroConeFieldVersion D hγ ω)
      (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ) z,
    LQGMetric.circleAvg (hIG₀ ω) (MatedCRTHarmonic.Canon.conditioningRadius ε q ζ) z +
      phaseVersion D hγ ω)

/-- The jointly measurable masked density `1_{F(z)} u_*(z)` of [18] (4.22). -/
def p48oMaskedVersion
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (ω : Ω) (z : ℂ) : ℝ :=
  (GMS4c.lemma49Event ε q ζ z).indicator (fun _ => GMS4F.realUStar ε (η₀ ω) z)
    ((η₀ ω, p48oObsVersion D hγ ε q ζ ω z) : GMS4c.Lemma49Input)

/-- **The jointly measurable (4.28) conditional mean** on the canonical zero-cone coupling. -/
def p48oCondMeanJoint
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) : Ω → ℂ → ℝ :=
  letI := D.isProbabilityMeasure
  p48oCondMean P (p48oObsVersion D hγ ε q ζ) (p48oMaskedVersion D hγ ε q ζ)

lemma measurable_p48oObsVersion
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) :
    Measurable fun p : Ω × ℂ => p48oObsVersion D hγ ε q ζ p.1 p.2 := by
  set r : ℝ := MatedCRTHarmonic.Canon.conditioningRadius ε q ζ
  have hp1 : Measurable fun p : Ω × ℂ =>
      ((p48oZeroConeFieldVersion D hγ p.1, (r, p.2)) : LQGMetric.DistC × ℝ × ℂ) :=
    ((measurable_p48oZeroConeFieldVersion D hγ).comp measurable_fst).prodMk
      (measurable_const.prodMk measurable_snd)
  have hp2 : Measurable fun p : Ω × ℂ => ((hIG₀ p.1, (r, p.2)) : LQGMetric.DistC × ℝ × ℂ) :=
    (D.igField.1.1.measurable.comp measurable_fst).prodMk (measurable_const.prodMk measurable_snd)
  have h1 : Measurable fun p : Ω × ℂ =>
      LQGMetric.circleAvg (p48oZeroConeFieldVersion D hγ p.1) r p.2 := by
    have h := LQGMetric.measurable_circleAvg.comp hp1
    exact h
  have h2 : Measurable fun p : Ω × ℂ => LQGMetric.circleAvg (hIG₀ p.1) r p.2 := by
    have h := LQGMetric.measurable_circleAvg.comp hp2
    exact h
  have h3 : Measurable fun p : Ω × ℂ => phaseVersion D hγ p.1 :=
    (measurable_phaseVersion D hγ).comp measurable_fst
  have h := h1.prodMk (h2.add h3)
  exact h

/-- The event (4.22) is jointly Borel in the observation and the centre. -/
lemma p48o_measurableSet_lemma49Event_joint {ε : ℝ} (hε : 0 ≤ ε) (q ζ : ℝ) :
    MeasurableSet {p : GMS4c.Lemma49Input × ℂ | p.1 ∈ GMS4c.lemma49Event ε q ζ p.2} := by
  have hcp : Measurable fun p : GMS4c.Lemma49Input × ℂ => ((p.1.1, p.2) : C(ℝ, ℂ) × ℂ) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hW : Measurable fun p : GMS4c.Lemma49Input × ℂ => GMS4b.windowDiam ε p.1.1 p.2 := by
    have h := (GMS4b.measurable_windowDiam ε).comp hcp
    exact h
  have hIn : Measurable fun p : GMS4c.Lemma49Input × ℂ => GMS4b.degreeIn ε p.1.1 p.2 := by
    have h := (GMS4b.measurable_degreeIn ε).comp hcp
    exact h
  have hOut : Measurable fun p : GMS4c.Lemma49Input × ℂ => GMS4b.degreeOut ε p.1.1 p.2 := by
    have h := (GMS4b.measurable_degreeOut hε).comp hcp
    exact h
  have hcoe : Measurable fun n : ℕ∞ => (n : ℝ≥0∞) := measurable_of_countable _
  have hadd : Measurable fun y : ℕ∞ × ℕ∞ => y.1 + y.2 := measurable_of_countable _
  have hsum : Measurable fun p : GMS4c.Lemma49Input × ℂ =>
      (((GMS4b.degreeIn ε p.1.1 p.2 + GMS4b.degreeOut ε p.1.1 p.2 : ℕ∞) : ℝ≥0∞)) := by
    have h := hcoe.comp (hadd.comp (hIn.prodMk hOut))
    exact h
  have hA : Measurable fun p : GMS4c.Lemma49Input × ℂ => max |p.1.2.1| |p.1.2.2| := by
    have ha : Measurable fun p : GMS4c.Lemma49Input × ℂ => p.1.2.1 :=
      measurable_fst.comp (measurable_snd.comp measurable_fst)
    have hb : Measurable fun p : GMS4c.Lemma49Input × ℂ => p.1.2.2 :=
      measurable_snd.comp (measurable_snd.comp measurable_fst)
    exact ha.abs.max hb.abs
  have h1 : MeasurableSet {p : GMS4c.Lemma49Input × ℂ | GMS4b.windowDiam ε p.1.1 p.2 ≤ ε ^ q} :=
    measurableSet_le hW measurable_const
  have h2 : MeasurableSet {p : GMS4c.Lemma49Input × ℂ |
      (((GMS4b.degreeIn ε p.1.1 p.2 + GMS4b.degreeOut ε p.1.1 p.2 : ℕ∞) : ℝ≥0∞)) ≤
        ENNReal.ofReal (ε ^ (-ζ))} :=
    measurableSet_le hsum measurable_const
  have h3 : MeasurableSet {p : GMS4c.Lemma49Input × ℂ |
      max |p.1.2.1| |p.1.2.2| ≤ 2 * q * Real.log ε⁻¹} :=
    measurableSet_le hA measurable_const
  have hset : {p : GMS4c.Lemma49Input × ℂ | p.1 ∈ GMS4c.lemma49Event ε q ζ p.2} =
      {p : GMS4c.Lemma49Input × ℂ | GMS4b.windowDiam ε p.1.1 p.2 ≤ ε ^ q} ∩
        ({p : GMS4c.Lemma49Input × ℂ |
          (((GMS4b.degreeIn ε p.1.1 p.2 + GMS4b.degreeOut ε p.1.1 p.2 : ℕ∞) : ℝ≥0∞)) ≤
          ENNReal.ofReal (ε ^ (-ζ))} ∩
        {p : GMS4c.Lemma49Input × ℂ | max |p.1.2.1| |p.1.2.2| ≤ 2 * q * Real.log ε⁻¹}) := by
    ext p
    unfold GMS4c.lemma49Event
    exact Iff.rfl
  rw [hset]
  exact h1.inter (h2.inter h3)

lemma measurable_p48oMaskedVersion
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 ≤ ε) (q ζ : ℝ) :
    Measurable fun p : Ω × ℂ => p48oMaskedVersion D hγ ε q ζ p.1 p.2 := by
  have hη : Measurable η₀ := D.measurable_curves.2.2.1
  have hin : Measurable fun p : Ω × ℂ =>
      ((((η₀ p.1, p48oObsVersion D hγ ε q ζ p.1 p.2) : GMS4c.Lemma49Input)), p.2) := by
    have hc : Measurable fun p : Ω × ℂ => η₀ p.1 := hη.comp measurable_fst
    have h := (hc.prodMk (measurable_p48oObsVersion D hγ ε q ζ)).prodMk
      (measurable_snd : Measurable fun p : Ω × ℂ => p.2)
    exact h
  have hS : MeasurableSet {p : Ω × ℂ |
      ((η₀ p.1, p48oObsVersion D hγ ε q ζ p.1 p.2) : GMS4c.Lemma49Input) ∈
        GMS4c.lemma49Event ε q ζ p.2} :=
    hin (p48o_measurableSet_lemma49Event_joint hε q ζ)
  have hu : Measurable fun p : Ω × ℂ => GMS4F.realUStar ε (η₀ p.1) p.2 := by
    have hc : Measurable fun p : Ω × ℂ => ((η₀ p.1, p.2) : C(ℝ, ℂ) × ℂ) :=
      (hη.comp measurable_fst).prodMk measurable_snd
    have h := (GMS4F.measurable_realUStar hε).comp hc
    exact h
  have e : (fun p : Ω × ℂ => p48oMaskedVersion D hγ ε q ζ p.1 p.2) =
      {p : Ω × ℂ | ((η₀ p.1, p48oObsVersion D hγ ε q ζ p.1 p.2) : GMS4c.Lemma49Input) ∈
        GMS4c.lemma49Event ε q ζ p.2}.indicator
        (fun p => GMS4F.realUStar ε (η₀ p.1) p.2) := by
    funext p
    by_cases hp : ((η₀ p.1, p48oObsVersion D hγ ε q ζ p.1 p.2) : GMS4c.Lemma49Input) ∈
        GMS4c.lemma49Event ε q ζ p.2
    · simp only [p48oMaskedVersion, Set.indicator_of_mem hp]
      rw [Set.indicator_of_mem (show p ∈ {p : Ω × ℂ |
        ((η₀ p.1, p48oObsVersion D hγ ε q ζ p.1 p.2) : GMS4c.Lemma49Input) ∈
          GMS4c.lemma49Event ε q ζ p.2} from hp)]
    · simp only [p48oMaskedVersion, Set.indicator_of_notMem hp]
      rw [Set.indicator_of_notMem (show p ∉ {p : Ω × ℂ |
        ((η₀ p.1, p48oObsVersion D hγ ε q ζ p.1 p.2) : GMS4c.Lemma49Input) ∈
          GMS4c.lemma49Event ε q ζ p.2} from hp)]
  rw [e]
  exact hu.indicator hS

lemma p48oMaskedVersion_nonneg
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (ω : Ω) (z : ℂ) :
    0 ≤ p48oMaskedVersion D hγ ε q ζ ω z :=
  Set.indicator_nonneg (fun _ _ => GMS4F.realUStar_nonneg _ _ _) _

/-- Joint measurability of the canonical conditional mean. -/
theorem measurable_p48oCondMeanJoint
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) :
    Measurable fun p : Ω × ℂ => p48oCondMeanJoint D hγ ε q ζ p.1 p.2 := by
  let _ := D.isProbabilityMeasure
  exact measurable_p48oCondMean P _ (measurable_p48oObsVersion D hγ ε q ζ)

theorem p48oCondMeanJoint_nonneg
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (ω : Ω) (z : ℂ) :
    0 ≤ p48oCondMeanJoint D hγ ε q ζ ω z := by
  let _ := D.isProbabilityMeasure
  exact p48oCondMean_nonneg P _ _ ω z

/-- On one probability-one event the field version and the phase version are the literal ones. -/
lemma p48o_ae_versions_eq
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∀ᵐ ω ∂P, p48oZeroConeFieldVersion D hγ ω =
        (MatedCRTHarmonic.Canon.referenceSample D hγ ω).zeroConeField ∧
      phaseVersion D hγ ω = U ω := by
  filter_upwards [(MatedCRTHarmonic.Canon.aemeasurable_reference_field D hγ).ae_eq_mk,
    ae_phaseVersion_eq D hγ] with ω h1 h2
  exact ⟨h1.symm, h2⟩

/-- **The masked version is the literal masked density, simultaneously at every centre**, a.s. -/
theorem p48o_ae_maskedVersion_eq
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) :
    ∀ᵐ ω ∂P, ∀ z : ℂ, p48oMaskedVersion D hγ ε q ζ ω z = maskedUStar D hγ ε q ζ z ω := by
  filter_upwards [p48o_ae_versions_eq D hγ] with ω hω z
  have hin : ((η₀ ω, p48oObsVersion D hγ ε q ζ ω z) : GMS4c.Lemma49Input) =
      MatedCRTHarmonic.Canon.referenceConditioningInput D hγ ε q ζ z ω := by
    simp only [p48oObsVersion, MatedCRTHarmonic.Canon.referenceConditioningInput,
      MatedCRTHarmonic.Canon.actualIGAverage, hω.1, hω.2]
  by_cases hmem : ω ∈ localEvent D hγ ε q ζ z
  · have hmem' : ((η₀ ω, p48oObsVersion D hγ ε q ζ ω z) : GMS4c.Lemma49Input) ∈
        GMS4c.lemma49Event ε q ζ z := by
      rw [hin]; exact hmem
    simp only [p48oMaskedVersion, maskedUStar, Set.indicator_of_mem hmem',
      Set.indicator_of_mem hmem]
    rfl
  · have hmem' : ((η₀ ω, p48oObsVersion D hγ ε q ζ ω z) : GMS4c.Lemma49Input) ∉
        GMS4c.lemma49Event ε q ζ z := by
      rw [hin]; exact hmem
    simp only [p48oMaskedVersion, maskedUStar, Set.indicator_of_notMem hmem',
      Set.indicator_of_notMem hmem]

/-- The observation version agrees a.s. with the selected `circleObservation` at each centre. -/
theorem p48o_ae_obsVersion_eq_circleObservation
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (z : ℂ) :
    (fun ω => p48oObsVersion D hγ ε q ζ ω z) =ᵐ[P] circleObservation D hγ ε q ζ z := by
  filter_upwards [p48o_ae_versions_eq D hγ, ae_circleObservation_eq_actual D hγ ε q ζ z]
    with ω hω hobs
  rw [hobs]
  simp only [p48oObsVersion, MatedCRTHarmonic.Canon.actualIGAverage, hω.1, hω.2]

/-- **The jointly measurable conditional mean is a version of the canonical conditional mean at
every centre** with integrable masked density. -/
theorem p48o_condMeanJoint_ae_eq_conditionalMean
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 ≤ ε) (q ζ : ℝ) (z : ℂ)
    (hint : Integrable (maskedUStar D hγ ε q ζ z) P) :
    (fun ω => p48oCondMeanJoint D hγ ε q ζ ω z) =ᵐ[P]
      fun ω => conditionalMean D hγ ε q ζ ω z := by
  let _ := D.isProbabilityMeasure
  have hXX : (fun ω => p48oMaskedVersion D hγ ε q ζ ω z) =ᵐ[P] maskedUStar D hγ ε q ζ z := by
    filter_upwards [p48o_ae_maskedVersion_eq D hγ ε q ζ] with ω hω
    exact hω z
  exact p48o_condMean_ae_eq_condExp P (measurable_p48oObsVersion D hγ ε q ζ)
    (measurable_p48oMaskedVersion D hγ hε q ζ) z
    (fun ω => p48oMaskedVersion_nonneg D hγ ε q ζ ω z)
    (measurable_circleObservation D hγ ε q ζ z)
    (p48o_ae_obsVersion_eq_circleObservation D hγ ε q ζ z) hint hXX

/-! ### Spatial (Tonelli) consequences in the shapes of the H4 fields

The premise `hmean` is exactly what `prop48_canonical_of_lemma49_gmcReconstruction` supplies to its H4
at a scale `ε` and radius `ρ`: integrability of the masked density and an a.s. bound `A` for the
canonical conditional mean at every centre of `B_ρ(0)`. -/

/-- The all-visit and first-hit masked densities agree at Lebesgue-a.e. centre, on one
probability-one event (the pointwise form behind the `ae_integral_maskedPrime_eq_masked`). -/
theorem p48o_ae_ae_maskedPrime_eq_masked
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(volume : Measure ℂ),
      maskedUStarPrime D hγ ε q ζ z ω = maskedUStar D hγ ε q ζ z ω := by
  filter_upwards [D.spaceFilling, D.areaParam₀,
    ae_zeroCone_volume_multiVisitPoints_eq_zero D] with ω hspace hparam hnull
  obtain ⟨φ, -, hφ⟩ := hparam.1
  have hsurj : Function.Surjective (η₀ ω) := by
    intro z
    obtain ⟨t, ht⟩ := hspace.1 z
    exact ⟨φ.symm t, by simpa [hφ] using ht⟩
  have htrans : Tendsto (η₀ ω) (cocompact ℝ) (cocompact ℂ) := by
    have hφt : Tendsto φ (cocompact ℝ) (cocompact ℝ) :=
      φ.toHomeomorph.isClosedEmbedding.tendsto_cocompact
    have hηfun : (η₀ ω : ℝ → ℂ) = (ηL ω) ∘ φ := funext hφ
    rw [hηfun]
    exact hspace.2.1.comp hφt
  filter_upwards [compl_mem_ae_iff.mpr hnull] with z hz
  have hhit : (η₀ ω) (GMS4b.hitTime (η₀ ω) z) = z :=
    GMS4b.hitTime_spec (η₀ ω).continuous htrans (hsurj z)
  have hevent := localEventPrime_iff_localEvent_of_not_multi D hγ ε q ζ ω z hhit hz
  by_cases hω : ω ∈ localEventPrime D hγ ε q ζ z
  · have hω' := hevent.mp hω
    simp only [maskedUStarPrime, maskedUStar, Set.indicator_of_mem hω,
      Set.indicator_of_mem hω']
    exact uStarPrime_eq_uStar_of_not_multi ε η₀ ω z hhit hz
  · have hω' : ω ∉ localEvent D hγ ε q ζ z := fun h => hω (hevent.mpr h)
    simp only [maskedUStarPrime, maskedUStar, Set.indicator_of_notMem hω,
      Set.indicator_of_notMem hω']

/-- The a.s. bound transfers to the jointly measurable version at every centre of `B_ρ(0)`. -/
theorem p48o_condMeanJoint_le_of_mean
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 ≤ ε) {q ζ ρ A : ℝ}
    (hmean : ∀ z ∈ Metric.ball (0 : ℂ) ρ,
      Integrable (maskedUStar D hγ ε q ζ z) P ∧ ∀ᵐ ω ∂P, conditionalMean D hγ ε q ζ ω z ≤ A) :
    ∀ z ∈ Metric.ball (0 : ℂ) ρ, ∀ᵐ ω ∂P, p48oCondMeanJoint D hγ ε q ζ ω z ≤ A := by
  intro z hz
  obtain ⟨hi, hb⟩ := hmean z hz
  filter_upwards [p48o_condMeanJoint_ae_eq_conditionalMean D hγ hε q ζ z hi, hb] with ω h1 h2
  rw [h1]
  exact h2

/-- **Tonelli:** a.s., the bound holds at Lebesgue-a.e. centre of `B_ρ(0)`. -/
theorem p48o_ae_ae_condMeanJoint_le
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 ≤ ε) {q ζ ρ A : ℝ}
    (hmean : ∀ z ∈ Metric.ball (0 : ℂ) ρ,
      Integrable (maskedUStar D hγ ε q ζ z) P ∧ ∀ᵐ ω ∂P, conditionalMean D hγ ε q ζ ω z ≤ A) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(volume.restrict (Metric.ball (0 : ℂ) ρ)),
      p48oCondMeanJoint D hγ ε q ζ ω z ≤ A := by
  let _ := D.isProbabilityMeasure
  have hS : MeasurableSet {p : Ω × ℂ | p48oCondMeanJoint D hγ ε q ζ p.1 p.2 ≤ A} :=
    measurableSet_le (measurable_p48oCondMeanJoint D hγ ε q ζ) measurable_const
  have h1 : ∀ᵐ z ∂(volume.restrict (Metric.ball (0 : ℂ) ρ)), ∀ᵐ ω ∂P,
      p48oCondMeanJoint D hγ ε q ζ ω z ≤ A := by
    rw [ae_restrict_iff' measurableSet_ball]
    exact Eventually.of_forall fun z hz => p48o_condMeanJoint_le_of_mean D hγ hε hmean z hz
  exact (Measure.ae_ae_comm hS).2 h1

lemma p48o_integrableOn_test {ρ : ℝ} {domain : Set ℂ} {f : ℂ → ℝ}
    (hadm : GMS4.Prop48TestPairAdmissible ρ domain f) : IntegrableOn f domain := by
  have h := p48o_integrableOn_test_mul hadm hadm.test_measurable measurable_const
    (M := 1) (g := fun _ => (1 : ℝ)) (fun _ => by norm_num)
  simpa only [mul_one] using h

/-- **H4 `spatial_integrable`, conditional-mean part**, for the jointly measurable version. -/
theorem p48o_ae_integrable_test_mul_condMeanJoint
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 ≤ ε) {q ζ ρ A : ℝ}
    (hmean : ∀ z ∈ Metric.ball (0 : ℂ) ρ,
      Integrable (maskedUStar D hγ ε q ζ z) P ∧ ∀ᵐ ω ∂P, conditionalMean D hγ ε q ζ ω z ≤ A)
    {domain : Set ℂ} {f : ℂ → ℝ} (hadm : GMS4.Prop48TestPairAdmissible ρ domain f) :
    ∀ᵐ ω ∂P, Integrable (fun z => f z * p48oCondMeanJoint D hγ ε q ζ ω z)
      (volume.restrict domain) := by
  filter_upwards [p48o_ae_ae_condMeanJoint_le D hγ hε hmean] with ω hω
  have hm : Measurable fun z => p48oCondMeanJoint D hγ ε q ζ ω z :=
    (measurable_p48oCondMeanJoint D hγ ε q ζ).comp (measurable_const.prodMk measurable_id)
  have hωD : ∀ᵐ z ∂(volume.restrict domain), p48oCondMeanJoint D hγ ε q ζ ω z ≤ A :=
    ae_restrict_of_ae_restrict_of_subset hadm.domain_subset_ball hω
  refine IntegrableOn.of_bound (p48o_volume_lt_top_of_admissible hadm) ?_
    (GMS4.prop48TestSupNorm ρ f * |A|) ?_
  · have hext : Measurable fun z => p48oTestExt ρ f z * p48oCondMeanJoint D hγ ε q ζ ω z :=
      (measurable_p48oTestExt hadm.test_measurable).mul hm
    refine hext.aestronglyMeasurable.congr ?_
    refine (ae_restrict_iff' hadm.domain_borel).2 (Eventually.of_forall fun z hz => ?_)
    simp only
    rw [p48oTestExt_eq_of_mem (hadm.domain_subset_ball hz)]
  · filter_upwards [hωD, ae_restrict_mem hadm.domain_borel] with z hzA hzD
    have h0 := p48oCondMeanJoint_nonneg D hγ ε q ζ ω z
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
    exact mul_le_mul (p48o_abs_test_le hadm (hadm.domain_subset_ball hzD))
      (hzA.trans (le_abs_self A)) h0
      ((abs_nonneg _).trans (p48o_abs_test_le hadm (hadm.domain_subset_ball hzD)))

/-- **H4 `mean_integral_le`** for the jointly measurable version. -/
theorem p48o_ae_setIntegral_test_mul_condMeanJoint_le
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 ≤ ε) {q ζ ρ A : ℝ}
    (hmean : ∀ z ∈ Metric.ball (0 : ℂ) ρ,
      Integrable (maskedUStar D hγ ε q ζ z) P ∧ ∀ᵐ ω ∂P, conditionalMean D hγ ε q ζ ω z ≤ A)
    {domain : Set ℂ} {f : ℂ → ℝ} (hadm : GMS4.Prop48TestPairAdmissible ρ domain f) :
    ∀ᵐ ω ∂P, (∫ z in domain, f z * p48oCondMeanJoint D hγ ε q ζ ω z) ≤
      A * ∫ z in domain, f z := by
  filter_upwards [p48o_ae_ae_condMeanJoint_le D hγ hε hmean,
    p48o_ae_integrable_test_mul_condMeanJoint D hγ hε hmean hadm] with ω hω hint
  have hωD : ∀ᵐ z ∂(volume.restrict domain), p48oCondMeanJoint D hγ ε q ζ ω z ≤ A :=
    ae_restrict_of_ae_restrict_of_subset hadm.domain_subset_ball hω
  have hfA : IntegrableOn (fun z => f z * A) domain := (p48o_integrableOn_test hadm).mul_const A
  calc (∫ z in domain, f z * p48oCondMeanJoint D hγ ε q ζ ω z) ≤ ∫ z in domain, f z * A := by
        refine setIntegral_mono_ae_restrict hint hfA ?_
        filter_upwards [hωD, ae_restrict_mem hadm.domain_borel] with z hzA hzD
        exact mul_le_mul_of_nonneg_left hzA (p48o_test_nonneg hadm hzD)
    _ = A * ∫ z in domain, f z := by rw [integral_mul_const, mul_comm]

/-- **H4 `spatial_integrable`, density part**: the all-visit masked density is a.s. integrable
against the test. Uses only the premise `hmean` (via `E[X_z] = E[E[X_z | Y_z]] ≤ A`). -/
theorem p48o_ae_integrable_test_mul_maskedPrime
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 ≤ ε) {q ζ ρ A : ℝ}
    (hmean : ∀ z ∈ Metric.ball (0 : ℂ) ρ,
      Integrable (maskedUStar D hγ ε q ζ z) P ∧ ∀ᵐ ω ∂P, conditionalMean D hγ ε q ζ ω z ≤ A)
    {domain : Set ℂ} {f : ℂ → ℝ} (hadm : GMS4.Prop48TestPairAdmissible ρ domain f) :
    ∀ᵐ ω ∂P, Integrable (fun z => f z * maskedUStarPrime D hγ ε q ζ z ω)
      (volume.restrict domain) := by
  let _ := D.isProbabilityMeasure
  have hXm := measurable_p48oMaskedVersion D hγ hε q ζ
  -- the pointwise first moment is at most `A`
  have hE : ∀ z ∈ Metric.ball (0 : ℂ) ρ,
      ∫⁻ ω, ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) ∂P ≤ ENNReal.ofReal A := by
    intro z hz
    obtain ⟨hi, hb⟩ := hmean z hz
    have heq : (fun ω => p48oMaskedVersion D hγ ε q ζ ω z) =ᵐ[P] maskedUStar D hγ ε q ζ z := by
      filter_upwards [p48o_ae_maskedVersion_eq D hγ ε q ζ] with ω hω
      exact hω z
    have hm : MeasurableSpace.comap (circleObservation D hγ ε q ζ z) inferInstance ≤
        ‹MeasurableSpace Ω› := (measurable_circleObservation D hγ ε q ζ z).comap_le
    have heq' : (fun ω => ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z)) =ᵐ[P]
        fun ω => ENNReal.ofReal (maskedUStar D hγ ε q ζ z ω) := by
      filter_upwards [heq] with ω h
      rw [h]
    rw [lintegral_congr_ae heq',
      ← ofReal_integral_eq_lintegral_ofReal hi
        (Eventually.of_forall fun ω => maskedUStar_nonneg D hγ ε q ζ z ω)]
    apply ENNReal.ofReal_le_ofReal
    calc ∫ ω, maskedUStar D hγ ε q ζ z ω ∂P = ∫ ω, conditionalMean D hγ ε q ζ ω z ∂P :=
          (integral_condExp hm).symm
      _ ≤ ∫ _ω, A ∂P := integral_mono_ae integrable_condExp (integrable_const A) hb
      _ = A := by simp
  -- Tonelli over the ball
  have hG : Measurable fun p : Ω × ℂ => ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ p.1 p.2) := by
    have h := ENNReal.measurable_ofReal.comp hXm
    exact h
  have hfin : ∫⁻ ω, (∫⁻ z in Metric.ball (0 : ℂ) ρ,
      ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z)) ∂P ≠ ⊤ := by
    rw [lintegral_lintegral_swap hG.aemeasurable]
    refine ne_top_of_le_ne_top (b := ∫⁻ _z in Metric.ball (0 : ℂ) ρ, ENNReal.ofReal A) ?_ ?_
    · rw [setLIntegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
    · exact setLIntegral_mono measurable_const fun z hz => hE z hz
  have hLm : Measurable fun ω => ∫⁻ z in Metric.ball (0 : ℂ) ρ,
      ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) := by
    have h := hG.lintegral_prod_right' (ν := volume.restrict (Metric.ball (0 : ℂ) ρ))
    exact h
  have hae : ∀ᵐ ω ∂P, (∫⁻ z in Metric.ball (0 : ℂ) ρ,
      ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z)) < ⊤ :=
    ae_lt_top' hLm.aemeasurable hfin
  filter_upwards [hae, p48o_ae_maskedVersion_eq D hγ ε q ζ,
    p48o_ae_ae_maskedPrime_eq_masked D hγ ε q ζ] with ω hω h1 h2
  have hu : Measurable fun z => p48oMaskedVersion D hγ ε q ζ ω z := by
    have h := hXm.comp (measurable_const.prodMk (measurable_id (α := ℂ)) :
      Measurable fun z : ℂ => (ω, z))
    exact h
  have huint : IntegrableOn (fun z => p48oMaskedVersion D hγ ε q ζ ω z) domain := by
    refine IntegrableOn.mono_set ?_ hadm.domain_subset_ball
    refine ⟨hu.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have e : (fun z => ‖p48oMaskedVersion D hγ ε q ζ ω z‖ₑ) =
        fun z => ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) := by
      funext z
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (p48oMaskedVersion_nonneg D hγ ε q ζ ω z)]
    rw [e]
    exact hω
  have hfm : AEStronglyMeasurable f (volume.restrict domain) := by
    have hext : Measurable (p48oTestExt ρ f) := measurable_p48oTestExt hadm.test_measurable
    refine hext.aestronglyMeasurable.congr ?_
    refine (ae_restrict_iff' hadm.domain_borel).2 (Eventually.of_forall fun z hz => ?_)
    rw [p48oTestExt_eq_of_mem (hadm.domain_subset_ball hz)]
  have hprod : Integrable (fun z => f z * p48oMaskedVersion D hγ ε q ζ ω z)
      (volume.restrict domain) := by
    refine huint.bdd_mul hfm (c := GMS4.prop48TestSupNorm ρ f) ?_
    filter_upwards [ae_restrict_mem hadm.domain_borel] with z hz
    rw [Real.norm_eq_abs]
    exact p48o_abs_test_le hadm (hadm.domain_subset_ball hz)
  refine hprod.congr ?_
  filter_upwards [ae_restrict_of_ae h2] with z hz
  rw [h1 z, hz]

/-- The centred all-visit integral of [18] (4.28)–(4.29) with the jointly measurable conditional
mean. -/
def p48oPrimedFluctuationJoint
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (domain : Set ℂ) (f : ℂ → ℝ) (ω : Ω) : ℝ :=
  ∫ z in domain, f z *
    (maskedUStarPrime D hγ ε q ζ z ω - p48oCondMeanJoint D hγ ε q ζ ω z)

/-- **H4 `fluctuation_aemeasurable`** for the jointly measurable version (no moment premise). -/
theorem p48o_aemeasurable_primedFluctuationJoint
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 ≤ ε) (q ζ : ℝ) {ρ : ℝ}
    {domain : Set ℂ} {f : ℂ → ℝ} (hadm : GMS4.Prop48TestPairAdmissible ρ domain f) :
    AEMeasurable (p48oPrimedFluctuationJoint D hγ ε q ζ domain f) P := by
  have hG : Measurable fun p : Ω × ℂ => p48oTestExt ρ f p.2 *
      (p48oMaskedVersion D hγ ε q ζ p.1 p.2 - p48oCondMeanJoint D hγ ε q ζ p.1 p.2) :=
    ((measurable_p48oTestExt hadm.test_measurable).comp measurable_snd).mul
      ((measurable_p48oMaskedVersion D hγ hε q ζ).sub (measurable_p48oCondMeanJoint D hγ ε q ζ))
  have hsm := hG.stronglyMeasurable.integral_prod_right' (ν := volume.restrict domain)
  refine hsm.measurable.aemeasurable.congr ?_
  filter_upwards [p48o_ae_maskedVersion_eq D hγ ε q ζ,
    p48o_ae_ae_maskedPrime_eq_masked D hγ ε q ζ] with ω h1 h2
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae h2, ae_restrict_mem hadm.domain_borel] with z hz hzD
  rw [p48oTestExt_eq_of_mem (hadm.domain_subset_ball hzD), h1 z, hz]

/-- **H4 `spatial_integrable`**, both parts, for the jointly measurable version. -/
theorem p48o_ae_spatial_integrable_joint
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 ≤ ε) {q ζ ρ A : ℝ}
    (hmean : ∀ z ∈ Metric.ball (0 : ℂ) ρ,
      Integrable (maskedUStar D hγ ε q ζ z) P ∧ ∀ᵐ ω ∂P, conditionalMean D hγ ε q ζ ω z ≤ A)
    {domain : Set ℂ} {f : ℂ → ℝ} (hadm : GMS4.Prop48TestPairAdmissible ρ domain f) :
    ∀ᵐ ω ∂P,
      Integrable (fun z => f z * maskedUStarPrime D hγ ε q ζ z ω) (volume.restrict domain) ∧
      Integrable (fun z => f z * p48oCondMeanJoint D hγ ε q ζ ω z) (volume.restrict domain) := by
  filter_upwards [p48o_ae_integrable_test_mul_maskedPrime D hγ hε hmean hadm,
    p48o_ae_integrable_test_mul_condMeanJoint D hγ hε hmean hadm] with ω h1 h2
  exact ⟨h1, h2⟩

/-- **The a.s. form of [18] (4.29)** with the jointly measurable conditional mean: on the global
event `E^ε`, the first-hit integral is at most `A ∫ f` plus the centred all-visit integral. -/
theorem p48o_ae_good_integral_comparison_joint
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 ≤ ε) {q ζ ρ A : ℝ}
    (hmean : ∀ z ∈ Metric.ball (0 : ℂ) ρ,
      Integrable (maskedUStar D hγ ε q ζ z) P ∧ ∀ᵐ ω ∂P, conditionalMean D hγ ε q ζ ω z ≤ A)
    {domain : Set ℂ} {f : ℂ → ℝ} (hadm : GMS4.Prop48TestPairAdmissible ρ domain f) :
    ∀ᵐ ω ∂P, ω ∈ goodEvent D hγ ε q ζ ρ →
      (∫ z in domain, f z * uStar ε η₀ ω z) ≤
        A * (∫ z in domain, f z) + p48oPrimedFluctuationJoint D hγ ε q ζ domain f ω := by
  filter_upwards [ae_integral_maskedPrime_eq_masked D hγ ε q ζ domain f,
    p48o_ae_spatial_integrable_joint D hγ hε hmean hadm,
    p48o_ae_setIntegral_test_mul_condMeanJoint_le D hγ hε hmean hadm]
    with ω hmask hInt hmeanω hgood
  have hmasked : (∫ z in domain, f z * maskedUStarPrime D hγ ε q ζ z ω) =
      ∫ z in domain, f z * uStar ε η₀ ω z := by
    calc _ = ∫ z in domain, f z * maskedUStar D hγ ε q ζ z ω := hmask
      _ = ∫ z in domain, f z * uStar ε η₀ ω z := by
        apply setIntegral_congr_fun hadm.domain_borel
        intro z hz
        change f z * (localEvent D hγ ε q ζ z).indicator
          (fun ω' => uStar ε η₀ ω' z) ω = f z * uStar ε η₀ ω z
        rw [Set.indicator_of_mem
          (localEvent_of_goodEvent D hγ ε q ζ ρ hgood (hadm.domain_subset_ball hz))]
  have hsubtract : p48oPrimedFluctuationJoint D hγ ε q ζ domain f ω =
      (∫ z in domain, f z * maskedUStarPrime D hγ ε q ζ z ω) -
        ∫ z in domain, f z * p48oCondMeanJoint D hγ ε q ζ ω z := by
    change (∫ z, f z * (maskedUStarPrime D hγ ε q ζ z ω -
      p48oCondMeanJoint D hγ ε q ζ ω z) ∂volume.restrict domain) = _
    simp_rw [mul_sub]
    exact integral_sub hInt.1 hInt.2
  rw [hsubtract, hmasked]
  linarith

end Canonical

end MatedCRTHarmonic.GMS4O
