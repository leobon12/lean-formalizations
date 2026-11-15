/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFin3Girsanov
import InteractingSLE.Spec.ZhanGT4.DualSeedFin3Axis

/-!
# Adapted actual inputs of the mapped-driver formula

Packet PROVE-ZHAN-GT4-A22. The D10 rate is a measurable rational function
of the already constructed alive conformal factors. Supply the actual
map and generator measurability from those factors, including at seeds.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (IsForwardSol)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The actual D10 drift is measurable on an alive event. No own seed-gap
inverse appears in its formula. -/
theorem measurable_seed_d10Rate {n : ℕ} {d : Ω → SeedData n} {κ : ℝ} {rr : Fin n → ℝ}
    (hdκ : ∀ ω, (d ω).κ = κ) (hdr : ∀ ω, (d ω).r = rr) {t : ℝ} {G : Set Ω}
    (hG : MeasurableSet G)
    (hA : ∀ k, Measurable (G.indicator fun ω => (d ω).A k t))
    (h20 : Measurable (G.indicator fun ω => (d ω).A20 t))
    (hB : ∀ m, Measurable (G.indicator fun ω => (d ω).B0 t m)) :
    Measurable (G.indicator fun ω => (d ω).d10Rate t) := by
  have hm := ((hA 1).pow_const 2).mul
    (((measurable_const (a := κ)).div (((hA 0).sub h20).const_mul 2)).neg.add
      (Finset.measurable_sum Finset.univ (fun m _ =>
        (measurable_const (a := κ * rr m)).div ((hA 0).sub (hB m)))))
  convert hm.indicator hG using 1
  funext ω
  by_cases hω : ω ∈ G
  · simp only [Pi.mul_apply, Pi.add_apply, Pi.neg_apply, Pi.div_apply, Pi.sub_apply,
      indicator_of_mem hω, SeedData.d10Rate, hdκ ω, hdr ω]
  · simp only [indicator_of_notMem hω]

/-- Actual adapted drivers and force coordinates give every alive map
coefficient and the D10 generator used in the positive-band Itô theorem. -/
theorem measurable_seed_map_inputs {𝓕 : Filtration ℝ≥0 mΩ} {n : ℕ}
    {X : ℝ≥0 → Ω → ℝ} {d : Ω → SeedData n} {κ : ℝ} {rr : Fin n → ℝ}
    {A : Set ℂ} {φ : ℂ → ℂ} {ζ₀ : ℝ} {G : Set Ω} {T : Ω → ℝ}
    (hXm : ∀ u, Measurable[𝓕 u] (X u)) (hXc : ∀ ω, Continuous (X · ω))
    (hdW : ∀ ω, (d ω).W = Ito.rpath (X · ω)) (hdφ : ∀ ω, (d ω).φ = φ)
    (hdζ : ∀ ω, (d ω).ζ₀ = ζ₀) (hdκ : ∀ ω, (d ω).κ = κ) (hdr : ∀ ω, (d ω).r = rr)
    (q : ℝ≥0) (hG : MeasurableSet[𝓕 q] G) (hqT : ∀ ω ∈ G, (q : ℝ) ≤ T ω)
    (h : ∀ ω ∈ G, OwnData (d ω).W A (d ω).φ (T ω) (d ω).a (d ω).W')
    (hv₀ : ∀ ω ∈ G, ∃ v₀ : ℝ → ℂ, IsForwardSol (d ω).W' (d ω).ζ₀ ((d ω).a (T ω)) v₀)
    (hcl : ∀ ω ∈ G, ∀ m, ∃ ρ > 0, Disjoint (ball ((d ω).V m q : ℂ) ρ) (imgHull (d ω).W A q))
    (hVm : ∀ m, Measurable[𝓕 q] (G.indicator fun ω => (d ω).V m q)) :
    (∀ k, Measurable[𝓕 q] (G.indicator fun ω => (d ω).A k q)) ∧
      Measurable[𝓕 q] (G.indicator fun ω => (d ω).d10Rate q) := by
  obtain ⟨hA, h20, -, -, hB, -, -⟩ :=
    measurable_seed_parts hXm hXc hdW hdφ hdζ q hG hqT h hv₀ hcl hVm
  exact ⟨hA, @measurable_seed_d10Rate Ω (𝓕 q) n d κ rr hdκ hdr q G hG hA h20 hB⟩

end InteractingSLE.ZhanGT4
