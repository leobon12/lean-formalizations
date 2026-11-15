/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux50HitMain

/-!
# Lemma 7.1, ingredient (iii): independence from uniqueness of the joint law

Packet PROVE-LEMMA72C. Specification §7.1, proof of Lemma 7.1 (`source/spec/p193-240.md` L608–L620, pp. 225–226:
"Apply Aux. lemma 46. Conditionally on `A`, the pairs `(X_j, H_j)` are independent; each has the same fixed joint law,
and they are independent of the exterior field") and of Lemma 7.2 (L638: "The component-pair factorization in the
preceding proof says that `(η_ψ, h_ψ)` is independent of `Q`").

The source obtains the independence of the pocket pair from the exterior record through the component-pair
factorization (Aux. lemma 46: the conditional SLE laws of all pockets by successive conditioning at their entry times,
and the full-curve kernels of all component fields). This file gives a shorter route through the **uniqueness of the
joint law of a two-seed coupling** (Aux. lemmas 50–51, proved for every `0 < κ < 8`:
`Aux50Hit.hasTraceStopKernel_of_lt_eight` and `Aux50.map_prod_killedHistory_eq`): every two two-seed couplings with
the frozen optional hull specification and continuous generating traces have the same joint law of the field and the
killed driving history. Hence, if the pair `(h_ψ, history)` is such a coupling also after conditioning on any event
`G` of positive probability of a σ-algebra `𝒬`, its law under `P[· | G]` is its law under `P`, i.e. it is independent
of `𝒬`.

* `indepFun_of_forall_cond_map_eq`: a variable whose law is unchanged by conditioning on every event of positive
  probability of `σ(Y)` is independent of `Y`;
* `IsTwoSeedCouplingOf`: the pair `(h_ψ, H)` is, under a measure `μ`, the field and (almost surely) the killed driving
  history of a two-seed optional hull coupling with a continuous generating trace;
* `map_eq_of_isTwoSeedCouplingOf`: two such measures give the same joint law (Aux. lemma 51 for `κ < 8`);
* **`indepFun_of_forall_cond_isTwoSeedCouplingOf`**: if the pair is a two-seed coupling under `P` and under every
  `P[· | G]`, `G ∈ σ(Y)`, `P G ≠ 0`, then `(H, h_ψ)` is independent of `Y`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec7.Lemma72C

open LawUnique

/-! ### Independence from invariance of the law under conditioning -/

section Generic

variable {Ω β γ : Type*} [mΩ : MeasurableSpace Ω] [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- **A law unchanged by conditioning gives independence.** If the law of `X` under `P[· | G]` is its law under `P`
for every event `G ∈ σ(Y)` of positive probability, then `X` and `Y` are independent. -/
theorem indepFun_of_forall_cond_map_eq {X : Ω → β} {Y : Ω → γ} (hX : Measurable X) (hY : Measurable Y)
    (hcond : ∀ G : Set Ω, MeasurableSet[MeasurableSpace.comap Y mγ] G → P G ≠ 0 → (P[|G]).map X = P.map X) :
    IndepFun X Y P := by
  rw [IndepFun_iff]
  rintro _ G ⟨S, hS, rfl⟩ hG
  have hGm : MeasurableSet G := hY.comap_le _ hG
  by_cases hP : P G = 0
  · have h1 : P (X ⁻¹' S ∩ G) = 0 := measure_mono_null inter_subset_right hP
    rw [h1, hP, mul_zero]
  · have h := congrArg (fun μ : Measure β => μ S) (hcond G hG hP)
    simp only [Measure.map_apply hX hS] at h
    rw [cond_apply hGm] at h
    have hfin : P G ≠ ⊤ := measure_ne_top P G
    have key : P (G ∩ X ⁻¹' S) = P G * P (X ⁻¹' S) := by
      rw [← h, ← mul_assoc, ENNReal.mul_inv_cancel hP hfin, one_mul]
    rw [inter_comm, key, mul_comm]

end Generic

/-! ### Two-seed couplings: one joint law -/

section Coupling

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- **The pair `(h_ψ, H)` is a two-seed coupling under `μ`**: there are a filtration, a driver with its two geometric
force points, a Brownian motion and a lifetime forming an optional hull coupling of the two-seed word
`SLE_κ(rL; rR)` (frozen `IsOptionalHullCoupling`) with field `h_ψ`, whose driver has almost surely a continuous
generating trace and whose killed driving history is almost surely `H`. -/
def IsTwoSeedCouplingOf (κ rL rR : ℝ) (μ : Measure Ω) (hψ : Ω → DistOn upperHalfPlaneOpens)
    (H : Ω → HistorySpace 1 1) : Prop :=
  ∃ (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
    IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) μ 𝓕 W VL VR B ζ hψ ∧
      (∀ᵐ ω ∂μ, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η) ∧
      (fun ω => killedHistory W VL VR ζ ω) =ᵐ[μ] H

variable {κ rL rR : ℝ} {hψ : Ω → DistOn upperHalfPlaneOpens} {H : Ω → HistorySpace 1 1}

/-- **One joint law for two-seed couplings** (Aux. lemma 51 at every `0 < κ < 8`, seed weights `> −2`): two
probability measures under which `(h_ψ, H)` is a two-seed coupling give it the same law. -/
theorem map_eq_of_isTwoSeedCouplingOf (hκ : 0 < κ) (hκ8 : κ < 8) (hL : -2 < rL) (hR : -2 < rR)
    {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsTwoSeedCouplingOf κ rL rR μ hψ H) (hν : IsTwoSeedCouplingOf κ rL rR ν hψ H) :
    μ.map (fun ω => (H ω, hψ ω)) = ν.map (fun ω => (H ω, hψ ω)) := by
  obtain ⟨𝓕₁, W₁, VL₁, VR₁, B₁, ζ₁, hC₁, htr₁, hH₁⟩ := hμ
  obtain ⟨𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, hC₂, htr₂, hH₂⟩ := hν
  obtain ⟨K, hKm, hK₁, hK₂⟩ := Aux50Hit.hasTraceStopKernel_of_lt_eight.{u, u} hκ hκ8 hL hR
  have hlaw := Aux50.map_prod_killedHistory_eq hκ hL hR hKm hK₁ hK₂ hC₁ htr₁ hC₂ htr₂
  obtain ⟨hX₁, -⟩ := hC₁.2.2.2
  obtain ⟨hX₂, -⟩ := hC₂.2.2.2
  have hm₁ : Measurable fun ω => (hψ ω, killedHistory W₁ VL₁ VR₁ ζ₁ ω) :=
    hC₁.2.1.prodMk (measurable_killedHistory hX₁)
  have hm₂ : Measurable fun ω => (hψ ω, killedHistory W₂ VL₂ VR₂ ζ₂ ω) :=
    hC₂.2.1.prodMk (measurable_killedHistory hX₂)
  have e₁ : μ.map (fun ω => (H ω, hψ ω)) =
      (μ.map fun ω => (hψ ω, killedHistory W₁ VL₁ VR₁ ζ₁ ω)).map Prod.swap := by
    rw [Measure.map_map measurable_swap hm₁]
    refine Measure.map_congr ?_
    filter_upwards [hH₁] with ω hω
    simp only [Function.comp_apply, Prod.swap_prod_mk, hω]
  have e₂ : ν.map (fun ω => (H ω, hψ ω)) =
      (ν.map fun ω => (hψ ω, killedHistory W₂ VL₂ VR₂ ζ₂ ω)).map Prod.swap := by
    rw [Measure.map_map measurable_swap hm₂]
    refine Measure.map_congr ?_
    filter_upwards [hH₂] with ω hω
    simp only [Function.comp_apply, Prod.swap_prod_mk, hω]
  rw [e₁, e₂, hlaw]

/-- **Lemma 7.1's independence from the uniqueness of the joint law.** Let `(h_ψ, H)` be a two-seed coupling
(`0 < κ < 8`, seed weights `> −2`) under `P`, and also under `P[· | G]` for every event `G ∈ σ(Y)` of positive
probability. Then `(H, h_ψ)` is independent of `Y`. -/
theorem indepFun_of_forall_cond_isTwoSeedCouplingOf {P : Measure Ω} [IsProbabilityMeasure P] {γ : Type*}
    [mγ : MeasurableSpace γ] {Y : Ω → γ} (hY : Measurable Y) (hκ : 0 < κ) (hκ8 : κ < 8) (hL : -2 < rL)
    (hR : -2 < rR) (hH : Measurable H) (hP : IsTwoSeedCouplingOf κ rL rR P hψ H)
    (hcond : ∀ G : Set Ω, MeasurableSet[MeasurableSpace.comap Y mγ] G → P G ≠ 0 →
      IsTwoSeedCouplingOf κ rL rR (P[|G]) hψ H) :
    IndepFun (fun ω => (H ω, hψ ω)) Y P := by
  have hψm : Measurable hψ := by
    obtain ⟨_, _, _, _, _, _, hC, -, -⟩ := hP
    exact hC.2.1
  refine indepFun_of_forall_cond_map_eq (hH.prodMk hψm) hY fun G hG hPG => ?_
  have := cond_isProbabilityMeasure (μ := P) hPG
  exact map_eq_of_isTwoSeedCouplingOf hκ hκ8 hL hR (hcond G hG hPG) hP

end Coupling

end InteractingSLE.Sec7.Lemma72C
