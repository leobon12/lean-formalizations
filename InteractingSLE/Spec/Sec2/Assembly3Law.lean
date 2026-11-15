/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.Assembly3Cont
import InteractingSLE.Spec.Sec2.TwoSeedLaw

/-!
# Theorem 2.2, uniqueness for the admissible entrances: the law of the two-seed code

Packet PROVE-SEC2-PATCH4. The state of an evolution at the dyadic times, killed at its lifetime
(`Assembly3.stCode`), is a random element of the countable product `ℕ × ℕ → S`. For two-seed
evolutions with weights `> −2` the lifetime is `∞` almost surely, so the probabilities of the square
cylinders are killed finite-dimensional probabilities, which PROVE-SEC2-JAC2's
`TwoSeed.measure_killedState_eq_twoSeed` determines; square cylinders form a generating π-system
(`generateFrom_squareCylinders`), so the law of the code is unique
(`Assembly3.map_stCode_eq_twoSeed`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace Assembly3

open Assembly Assembly2

/-- The state space of a word with `nL` left and `nR` right marks (driver, marks, Brownian
motion). -/
abbrev StateSp (nL nR : ℕ) : Type := ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ

section Code

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL nR : ℕ}

/-- The state at the dyadic times `dyad n k`, killed at `ζ` (the Brownian coordinate is not
killed). -/
def stCode (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℕ × ℕ → StateSp nL nR :=
  fun p => (Girsanov.killed ζ W (dyad p.1 p.2) ω,
    fun i => Girsanov.killed ζ (VL i) (dyad p.1 p.2) ω,
    fun j => Girsanov.killed ζ (VR j) (dyad p.1 p.2) ω, B (dyad p.1 p.2) ω)

theorem measurable_stCode {𝓕 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hW : AdaptedBefore 𝓕 ζ W) (hVL : ∀ i, AdaptedBefore 𝓕 ζ (VL i))
    (hVR : ∀ j, AdaptedBefore 𝓕 ζ (VR j)) (hB : ∀ t, Measurable (B t)) :
    Measurable (stCode ζ W VL VR B) := by
  have hk : ∀ {X : ℝ≥0 → Ω → ℝ}, AdaptedBefore 𝓕 ζ X → ∀ t,
      Measurable (Girsanov.killed ζ X t) := fun hX t =>
    (Girsanov.measurable_killed hX t).mono (𝓕.le t) le_rfl
  refine measurable_pi_iff.2 fun p => ?_
  exact (hk hW _).prodMk ((measurable_pi_iff.2 fun i => hk (hVL i) _).prodMk
    ((measurable_pi_iff.2 fun j => hk (hVR j) _).prodMk (hB _)))

/-- A square cylinder event of the code is, when the lifetime is infinite almost surely, a killed
finite-dimensional event. -/
theorem measure_stCode_preimage_pi {P : Measure Ω} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (s : Finset (ℕ × ℕ)) (t : ℕ × ℕ → Set (StateSp nL nR)) :
    P (stCode ζ W VL VR B ⁻¹' (s : Set (ℕ × ℕ)).pi t) =
      P {ω | ∀ j : Fin s.card,
        ((dyad (s.equivFin.symm j : ℕ × ℕ).1 (s.equivFin.symm j : ℕ × ℕ).2 : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
        (W (dyad (s.equivFin.symm j : ℕ × ℕ).1 (s.equivFin.symm j : ℕ × ℕ).2) ω,
          (fun i => VL i (dyad (s.equivFin.symm j : ℕ × ℕ).1 (s.equivFin.symm j : ℕ × ℕ).2) ω),
          (fun i => VR i (dyad (s.equivFin.symm j : ℕ × ℕ).1 (s.equivFin.symm j : ℕ × ℕ).2) ω),
          B (dyad (s.equivFin.symm j : ℕ × ℕ).1 (s.equivFin.symm j : ℕ × ℕ).2) ω) ∈
          t (s.equivFin.symm j)} := by
  refine measure_congr ?_
  filter_upwards [hζ] with ω hω
  have hk : ∀ (X : ℝ≥0 → Ω → ℝ) (u : ℝ≥0), Girsanov.killed ζ X u ω = X u ω := fun X u =>
    Girsanov.killed_of_lt (by rw [hω]; exact ENNReal.coe_lt_top)
  have hcode : ∀ p : ℕ × ℕ, stCode ζ W VL VR B ω p = (W (dyad p.1 p.2) ω,
      fun i => VL i (dyad p.1 p.2) ω, fun j => VR j (dyad p.1 p.2) ω, B (dyad p.1 p.2) ω) :=
    fun p => by simp only [stCode, hk]
  refine propext ?_
  simp only [mem_preimage, Set.mem_pi, Finset.mem_coe, hcode, hω, ENNReal.coe_lt_top, true_and]
  constructor
  · intro h j
    exact h _ (s.equivFin.symm j).2
  · intro h p hp
    have := h (s.equivFin ⟨p, hp⟩)
    simpa only [Equiv.symm_apply_apply] using this

end Code

/-- **The law of the dyadic code of a two-seed evolution is unique** (weights `> −2`). -/
theorem map_stCode_eq_twoSeed {a : ℝ} (ha : 0 < a) {ρa ρb : ℝ} (hρa : -2 < ρa) (hρb : -2 < ρb)
    {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ VR₁ : Fin 1 → ℝ≥0 → Ω₁ → ℝ}
    {B₁ : ℝ≥0 → Ω₁ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞}
    (h₁ : IsIntegratedSLEEvolution a (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0) (fun _ => ρa)
      (fun _ => ρb) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ}
    {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (h₂ : IsIntegratedSLEEvolution a (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0) (fun _ => ρa)
      (fun _ => ρb) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂) :
    P₁.map (stCode ζ₁ W₁ VL₁ VR₁ B₁) = P₂.map (stCode ζ₂ W₂ VL₂ VR₂ B₂) := by
  have hm₁ := measurable_stCode h₁.2.1 h₁.2.2.1 h₁.2.2.2.1 fun t =>
    (h₁.1.2.1 t).mono (𝓕₁.le t) le_rfl
  have hm₂ := measurable_stCode h₂.2.1 h₂.2.2.1 h₂.2.2.2.1 fun t =>
    (h₂.1.2.1 t).mono (𝓕₂.le t) le_rfl
  have hζ₁ := ae_lifetime_eq_top_twoSeed ha h₁ hρa hρb
  have hζ₂ := ae_lifetime_eq_top_twoSeed ha h₂ hρa hρb
  refine ext_of_generate_finite _ generateFrom_squareCylinders.symm
    (isPiSystem_squareCylinders (fun _ => MeasurableSpace.isPiSystem_measurableSet)
      fun _ => (MeasurableSet.univ : MeasurableSet (univ : Set (StateSp 1 1))))
    ?_ (by rw [measure_univ, measure_univ])
  rintro S ⟨s, t, ht, rfl⟩
  simp only [mem_univ_pi, mem_ofPred_eq] at ht
  have hS : MeasurableSet ((s : Set (ℕ × ℕ)).pi t) :=
    MeasurableSet.pi (Finset.countable_toSet _) fun p _ => ht p
  rw [Measure.map_apply hm₁ hS, Measure.map_apply hm₂ hS, measure_stCode_preimage_pi hζ₁,
    measure_stCode_preimage_pi hζ₂]
  exact TwoSeed.measure_killedState_eq_twoSeed ha (fun _ => rfl) (fun _ => rfl) h₁ h₂ _ _ _
    fun j => ht _

end Assembly3

end Sec2

end InteractingSLE
