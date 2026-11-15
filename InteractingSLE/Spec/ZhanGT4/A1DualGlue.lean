/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1DualRecord

/-!
# Gluing a reference coupling over a given large curve

Packet PROVE-ZHAN-A1DUAL, steps (a)–(b) of PROVE-ZHAN-GT4-A2X's "What remains" 1. Source: Astra, *Follow-up proofs*,
§A.1 L183–L187 ("There is a coupling of these two marginal laws …"; R38): a coupling built on its own space is
realized over a GIVEN copy of the large curve by disintegrating it over the large curve's record.

Let `(Ω, P)` carry an integrated evolution `L = (W, VL, VR, B, ζ)` and let a standard Borel `(Ω₀, μ)` carry another
evolution `L₀` of the same ordered word. With `R`, `R₀` the killed records at rational times (`A1DualRecord`), their
laws agree (`map_killedRec_eq`). The kernel `K ω = condDistrib id R₀ μ (R ω)` (Mathlib's regular conditional
distribution of the whole reference sample given its large record, lifted to `ULift Ω₀`) gives, on `Ω × ULift Ω₀`
under `P ⊗ₘ K`:

* `(R ∘ fst, down ∘ snd)` has the law of `(R₀, id)` under `μ` (`map_glue_eq`), so the second coordinate has law `μ`;
* almost surely the reference large curve read on the second coordinate agrees with the given one before the lifetime
  (same lifetime; same driver, marks and Brownian motion at every time before it) — at rational times from the
  record, at all times by continuity before the lifetime (`exists_glue_version`).

## Main results

* `map_compProd_comap`, `exists_kernel_glue`, `ae_eq_of_glue`: the measure-theoretic glue;
* **`exists_glue_version`**: the glue for two evolutions of one ordered word.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A1Dual

/-! ### The measure-theoretic glue -/

section Kernel

variable {Ω E F : Type*} {mΩ : MeasurableSpace Ω} {mE : MeasurableSpace E} {mF : MeasurableSpace F}

/-- Pushing `P ⊗ₘ (κ ∘ R)` forward by `R × id` gives `(P.map R) ⊗ₘ κ`. -/
theorem map_compProd_comap {P : Measure Ω} [IsFiniteMeasure P] {R : Ω → E} (hR : Measurable R) (κ : Kernel E F)
    [IsMarkovKernel κ] : (P ⊗ₘ κ.comap R hR).map (Prod.map R id) = (P.map R) ⊗ₘ κ := by
  refine Measure.ext_prod fun {s t} hs ht => ?_
  rw [Measure.map_apply (hR.prodMap measurable_id) (hs.prod ht), Measure.compProd_apply_prod hs ht]
  have e : Prod.map R id ⁻¹' (s ×ˢ t) = (R ⁻¹' s) ×ˢ t := by ext; simp
  rw [e, Measure.compProd_apply_prod (hR hs) ht, setLIntegral_map hs (κ.measurable_coe ht) hR]
  simp only [Kernel.comap_apply]

theorem nonempty_of_isProbabilityMeasure {μ : Measure F} [IsProbabilityMeasure μ] : Nonempty F := by
  rcases isEmpty_or_nonempty F with h | h
  · exact absurd (Measure.eq_zero_of_isEmpty μ) (IsProbabilityMeasure.ne_zero μ)
  · exact h

/-- **The glue kernel**: over a given record `R` with the same law as the reference record `R₀`, the regular
conditional distribution of the reference sample given `R₀`, evaluated at `R`, lifted to `ULift Ω₀`. -/
theorem exists_kernel_glue {P : Measure Ω} [IsProbabilityMeasure P] {R : Ω → E} (hR : Measurable R)
    {Ω₀ : Type} [MeasurableSpace Ω₀] [StandardBorelSpace Ω₀] {μ : Measure Ω₀} [IsProbabilityMeasure μ]
    {R₀ : Ω₀ → E} (hR₀ : Measurable R₀) (hlaw : P.map R = μ.map R₀) :
    ∃ K : Kernel Ω (ULift.{u} Ω₀), IsMarkovKernel K ∧
      (P ⊗ₘ K).map (fun z => (R z.1, z.2.down)) = μ.map (fun ω₀ => (R₀ ω₀, ω₀)) := by
  have : Nonempty Ω₀ := nonempty_of_isProbabilityMeasure (μ := μ)
  set κ : Kernel E Ω₀ := condDistrib id R₀ μ
  refine ⟨(κ.comap R hR).map ULift.up, Kernel.IsMarkovKernel.map _ measurable_up, ?_⟩
  have hΦ : Measurable fun z : Ω × ULift.{u} Ω₀ => (R z.1, z.2.down) :=
    (hR.comp measurable_fst).prodMk (measurable_down.comp measurable_snd)
  rw [Measure.compProd_map measurable_up, Measure.map_map hΦ (measurable_id.prodMap measurable_up)]
  have e : ((fun z : Ω × ULift.{u} Ω₀ => (R z.1, z.2.down)) ∘ Prod.map id ULift.up) = Prod.map R id := by
    funext z; rfl
  rw [e, map_compProd_comap hR κ, hlaw]
  exact compProd_map_condDistrib hR₀.aemeasurable aemeasurable_id

variable {P : Measure Ω} [IsProbabilityMeasure P] {R : Ω → E} {Ω₀ : Type} [MeasurableSpace Ω₀]
  {μ : Measure Ω₀} {R₀ : Ω₀ → E} {K : Kernel Ω (ULift.{u} Ω₀)} [IsMarkovKernel K]

omit [IsProbabilityMeasure P] [IsMarkovKernel K] in
/-- The second coordinate of the glued space has the reference law. -/
theorem map_snd_of_glue (hR : Measurable R) (hR₀ : Measurable R₀)
    (hglue : (P ⊗ₘ K).map (fun z => (R z.1, z.2.down)) = μ.map (fun ω₀ => (R₀ ω₀, ω₀))) :
    (P ⊗ₘ K).map (fun z => z.2.down) = μ := by
  have hΦ : Measurable fun z : Ω × ULift.{u} Ω₀ => (R z.1, z.2.down) :=
    (hR.comp measurable_fst).prodMk (measurable_down.comp measurable_snd)
  have e : (fun z : Ω × ULift.{u} Ω₀ => z.2.down) = Prod.snd ∘ fun z => (R z.1, z.2.down) := rfl
  rw [e, ← Measure.map_map measurable_snd hΦ, hglue,
    Measure.map_map measurable_snd (show Measurable fun ω₀ : Ω₀ => (R₀ ω₀, ω₀) from hR₀.prodMk measurable_id)]
  exact Measure.map_id

omit [IsProbabilityMeasure P] [IsMarkovKernel K] in
/-- **A real function of the record agrees almost surely on the two coordinates of the glued space.** -/
theorem ae_eq_of_glue (hR : Measurable R) (hR₀ : Measurable R₀)
    (hglue : (P ⊗ₘ K).map (fun z => (R z.1, z.2.down)) = μ.map (fun ω₀ => (R₀ ω₀, ω₀))) {g : E → ℝ}
    (hg : Measurable g) : ∀ᵐ z ∂(P ⊗ₘ K), g (R z.1) = g (R₀ z.2.down) := by
  have hΦ : Measurable fun z : Ω × ULift.{u} Ω₀ => (R z.1, z.2.down) :=
    (hR.comp measurable_fst).prodMk (measurable_down.comp measurable_snd)
  have hD : MeasurableSet {p : E × Ω₀ | g p.1 = g (R₀ p.2)} :=
    measurableSet_eq_fun (hg.comp measurable_fst) (hg.comp (hR₀.comp measurable_snd))
  have h1 : ∀ᵐ p ∂((P ⊗ₘ K).map fun z => (R z.1, z.2.down)), p ∈ {p : E × Ω₀ | g p.1 = g (R₀ p.2)} := by
    rw [hglue]
    exact (ae_map_iff (hR₀.prodMk measurable_id).aemeasurable hD).2 (Eventually.of_forall fun _ => rfl)
  exact ae_of_ae_map hΦ.aemeasurable h1

end Kernel

/-! ### The glue for two evolutions -/

section Evolution

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The glue over a given evolution** (A2X "What remains" 1(a)): for an integrated evolution `L` on `(Ω, P)` and a
reference evolution `L₀` of the same ordered word on a standard Borel `(Ω₀, μ)`, there is a Markov kernel
`K : Ω → ULift Ω₀` such that the second coordinate of `(Ω × ULift Ω₀, P ⊗ₘ K)` has law `μ` and, almost surely, `L₀`
read on the second coordinate has the lifetime of `L` read on the first and agrees with it at every time before the
lifetime. -/
theorem exists_glue_version (ha : 0 < a) (hF : IsOrderedForceWord xL xR)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {Ω₀ : Type} [MeasurableSpace Ω₀] [StandardBorelSpace Ω₀] {μ : Measure Ω₀} [IsProbabilityMeasure μ]
    {𝓕₀ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₀)} {W₀ : ℝ≥0 → Ω₀ → ℝ}
    {VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ} {B₀ : ℝ≥0 → Ω₀ → ℝ} {ζ₀ : Ω₀ → ℝ≥0∞}
    (hE₀ : IsIntegratedSLEEvolution a xL xR ρL ρR μ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀) :
    ∃ K : Kernel Ω (ULift.{u} Ω₀), IsMarkovKernel K ∧ (P ⊗ₘ K).map (fun z => z.2.down) = μ ∧
      ∀ᵐ z ∂(P ⊗ₘ K), ζ₀ z.2.down = ζ z.1 ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ z.1 →
        W₀ t z.2.down = W t z.1 ∧ (∀ i, VL₀ i t z.2.down = VL i t z.1) ∧
          (∀ j, VR₀ j t z.2.down = VR j t z.1) ∧ B₀ t z.2.down = B t z.1 := by
  have hR : Measurable (killedRec W VL VR B ζ) := measurable_killedRec hE.2.1 hE.2.2.1 hE.2.2.2.1
    fun t => (hE.1.2.1 t).mono (𝓕.le t) le_rfl
  have hR₀ : Measurable (killedRec W₀ VL₀ VR₀ B₀ ζ₀) := measurable_killedRec hE₀.2.1 hE₀.2.2.1 hE₀.2.2.2.1
    fun t => (hE₀.1.2.1 t).mono (𝓕₀.le t) le_rfl
  obtain ⟨K, hK, hglue⟩ := exists_kernel_glue.{u} hR hR₀ (map_killedRec_eq ha hF hE hE₀)
  have hsnd := map_snd_of_glue hR hR₀ hglue
  refine ⟨K, hK, hsnd, ?_⟩
  have hA : ∀ᵐ z ∂(P ⊗ₘ K), ∀ q, recAlive q (killedRec W VL VR B ζ z.1) =
      recAlive q (killedRec W₀ VL₀ VR₀ B₀ ζ₀ z.2.down) :=
    ae_all_iff.2 fun q => ae_eq_of_glue hR hR₀ hglue (measurable_recAlive q)
  have hW : ∀ᵐ z ∂(P ⊗ₘ K), ∀ q, recW q (killedRec W VL VR B ζ z.1) = recW q (killedRec W₀ VL₀ VR₀ B₀ ζ₀ z.2.down) :=
    ae_all_iff.2 fun q => ae_eq_of_glue hR hR₀ hglue (measurable_recW q)
  have hVL : ∀ᵐ z ∂(P ⊗ₘ K), ∀ i q, recVL i q (killedRec W VL VR B ζ z.1) =
      recVL i q (killedRec W₀ VL₀ VR₀ B₀ ζ₀ z.2.down) :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun q => ae_eq_of_glue hR hR₀ hglue (measurable_recVL i q)
  have hVR : ∀ᵐ z ∂(P ⊗ₘ K), ∀ j q, recVR j q (killedRec W VL VR B ζ z.1) =
      recVR j q (killedRec W₀ VL₀ VR₀ B₀ ζ₀ z.2.down) :=
    ae_all_iff.2 fun j => ae_all_iff.2 fun q => ae_eq_of_glue hR hR₀ hglue (measurable_recVR j q)
  have hB : ∀ᵐ z ∂(P ⊗ₘ K), ∀ q, recB q (killedRec W VL VR B ζ z.1) = recB q (killedRec W₀ VL₀ VR₀ B₀ ζ₀ z.2.down) :=
    ae_all_iff.2 fun q => ae_eq_of_glue hR hR₀ hglue (measurable_recB q)
  have hfst : (P ⊗ₘ K).map Prod.fst = P := Measure.fst_compProd P K
  have hp := ae_comp_of_map_eq measurable_fst hfst (hE.2.2.2.2.and hE.1.1.cont)
  have hp₀ := ae_comp_of_map_eq (measurable_down.comp measurable_snd) hsnd (hE₀.2.2.2.2.and hE₀.1.1.cont)
  filter_upwards [hA, hW, hVL, hVR, hB, hp, hp₀] with z hzA hzW hzVL hzVR hzB hzp hzp₀
  obtain ⟨⟨-, -, -, hcw, hcvL, hcvR, -⟩, hcB⟩ := hzp
  obtain ⟨⟨-, -, -, hcw₀, hcvL₀, hcvR₀, -⟩, hcB₀⟩ := hzp₀
  have hlt : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < ζ z.1 ↔ ((q : ℝ≥0) : ℝ≥0∞) < ζ₀ z.2.down := fun q => by
    have h := hzA q
    rw [recAlive_killedRec, recAlive_killedRec] at h
    constructor
    · intro h1; by_contra h2; simp [h1, h2] at h
    · intro h2; by_contra h1; simp [h1, h2] at h
  have hζ : ζ z.1 = ζ₀ z.2.down := eq_of_forall_nnrat_lt_iff hlt
  refine ⟨hζ.symm, ?_⟩
  have hcw₀' : ContinuousOn (fun t => W₀ t z.2.down) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ z.1} := by
    rw [hζ]; exact hcw₀
  have hcvL₀' : ∀ i, ContinuousOn (fun t => VL₀ i t z.2.down) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ z.1} := fun i => by
    rw [hζ]; exact hcvL₀ i
  have hcvR₀' : ∀ j, ContinuousOn (fun t => VR₀ j t z.2.down) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ z.1} := fun j => by
    rw [hζ]; exact hcvR₀ j
  have hcB₀' : ContinuousOn (fun t => B₀ t z.2.down) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ z.1} := hcB₀.continuousOn
  have hrat : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < ζ z.1 → W₀ q z.2.down = W q z.1 ∧
      (∀ i, VL₀ i q z.2.down = VL i q z.1) ∧ (∀ j, VR₀ j q z.2.down = VR j q z.1) ∧
        B₀ q z.2.down = B q z.1 := fun q hq => by
    obtain ⟨e1, e2, e3, e4⟩ := killedRec_of_lt (W := W) (VL := VL) (VR := VR) (B := B) z.1 hq
    obtain ⟨f1, f2, f3, f4⟩ := killedRec_of_lt (W := W₀) (VL := VL₀) (VR := VR₀) (B := B₀) z.2.down
      ((hlt q).1 hq)
    refine ⟨?_, fun i => ?_, fun j => ?_, ?_⟩
    · rw [← f1, ← e1]; exact (hzW q).symm
    · rw [← f2 i, ← e2 i]; exact (hzVL i q).symm
    · rw [← f3 j, ← e3 j]; exact (hzVR j q).symm
    · rw [← f4, ← e4]; exact (hzB q).symm
  intro t ht
  refine ⟨eqOn_of_nnrat hcw₀' hcw (fun q hq => (hrat q hq).1) t ht,
    fun i => eqOn_of_nnrat (hcvL₀' i) (hcvL i) (fun q hq => (hrat q hq).2.1 i) t ht,
    fun j => eqOn_of_nnrat (hcvR₀' j) (hcvR j) (fun q hq => (hrat q hq).2.2.1 j) t ht,
    eqOn_of_nnrat hcB₀' hcB.continuousOn (fun q hq => (hrat q hq).2.2.2) t ht⟩

end Evolution

end InteractingSLE.ZhanGT4.A1Dual
