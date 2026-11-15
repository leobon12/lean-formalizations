/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.AvoidMart

/-!
# Aux. lemma 25: a localized Itô martingale with a random initial state

Packet PROVE-AUX25. A generic form of the localized Itô formula (`Ito.martingale_itoLocalized`) for a state
`Λ` driven pathwise by a Brownian motion, `Λ_t = Λ_0 + ∫₀ᵗ Ψ(Λ_s, B_s) ds`, with an `𝓖_0`-measurable
(random) initial state, stopped at the first hitting time `σ` of a closed exit set `C` before a time `N`.
If `Φ` is `C³` on an open `U` containing a compact `K ⊇ closure Cᶜ` and the Itô drift `itoGen Φ p (Ψ p)`
vanishes on `K`, then `∫_S Φ(Λ_σ, B_σ) = ∫_S Φ(Λ_0, 0)` for every `S ∈ 𝓖_0` (optional stopping for the
bounded martingale `Φ(Λ_{·∧σ}, B_{·∧σ})`).

(`Zhan.martingale_loc`, PROVE-ZHAN-B, needs a deterministic initial state; here the initial state is
random, as it is after a restart.)

## Main results

* `Aux25.isStoppingTime_hitStop`, `Aux25.mem_K_of_le_hitStop`;
* `Aux25.setIntegral_hitStop_eq`: optional stopping for a drift-free observable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Aux25

section Loc

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {B : ℝ≥0 → Ω → ℝ} {Λ : ℝ≥0 → Ω → E} {Ψ : E × ℝ → E} {Φ : E × ℝ → ℝ}
  {U C K : Set (E × ℝ)} {N : ℝ≥0}

/-- The path `(Λ_t, B_t)`. -/
def statePath (Λ : ℝ≥0 → Ω → E) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : E × ℝ := (Λ t ω, B t ω)

/-- The hitting time of the exit set `C` before `N`. -/
def hitStop (Λ : ℝ≥0 → Ω → E) (B : ℝ≥0 → Ω → ℝ) (C : Set (E × ℝ)) (N : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  hittingBtwn (statePath Λ B) C 0 N ω

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_statePath (hΛc : ∀ ω, Continuous (Λ · ω)) (hBc : ∀ ω, Continuous (B · ω))
    (ω : Ω) : Continuous fun t => statePath Λ B t ω :=
  (hΛc ω).prodMk (hBc ω)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
theorem hitStop_le (ω : Ω) : hitStop Λ B C N ω ≤ N := hittingBtwn_le ω

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem isStoppingTime_hitStop (hB : IsFilteredBrownianReal 𝓖 B Q) (hBc : ∀ ω, Continuous (B · ω))
    (hΛm : ∀ t, Measurable[𝓖 t] (Λ t)) (hΛc : ∀ ω, Continuous (Λ · ω)) (hC : IsClosed C) :
    IsStoppingTime 𝓖 fun ω => (hitStop Λ B C N ω : WithTop ℝ≥0) :=
  QuantumZipper.ItoLite.isStoppingTime_hittingBtwn_of_isClosed (𝓕 := 𝓖)
    (U := statePath Λ B) (fun t => (hΛm t).prodMk (hB.2.1 t)) (continuous_statePath hΛc hBc) hC N

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Up to the hitting time the path stays in `K`, if it starts off `C`. -/
theorem mem_K_of_le_hitStop (hΛc : ∀ ω, Continuous (Λ · ω)) (hBc : ∀ ω, Continuous (B · ω))
    (hCK : closure Cᶜ ⊆ K) {ω : Ω} (h0 : statePath Λ B 0 ω ∉ C) {t : ℝ≥0}
    (ht : t ≤ hitStop Λ B C N ω) : statePath Λ B t ω ∈ K :=
  hCK (Zhan.mem_closure_compl_of_le_hittingBtwn (X := statePath Λ B) (continuous_statePath hΛc hBc ω)
    h0 ht)

variable (hB : IsFilteredBrownianReal 𝓖 B Q) (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0)
  (hΛm : ∀ t, Measurable[𝓖 t] (Λ t)) (hΛc : ∀ ω, Continuous (Λ · ω))
  (hΛeq : ∀ ω (t : ℝ≥0), Λ t ω = Λ 0 ω + ∫ s in (0 : ℝ)..t, Ψ (statePath Λ B s.toNNReal ω))
  (hU : IsOpen U) (hΦ : ContDiffOn ℝ 3 Φ U) (hΨ : ContinuousOn Ψ K) (hK : IsCompact K)
  (hKU : K ⊆ U) (hC : IsClosed C) (hCK : closure Cᶜ ⊆ K) (h0 : ∀ ω, statePath Λ B 0 ω ∉ C)
  (hgen : ∀ p ∈ K, Ito.itoGen Φ p (Ψ p) = 0)

include hB hBc hB0 hΛm hΛc hΛeq hU hΦ hΨ hK hKU hC hCK h0 hgen in
/-- **Optional stopping for a drift-free observable** with a random initial state. -/
theorem setIntegral_hitStop_eq {S : Set Ω} (hS : MeasurableSet[𝓖 0] S) :
    ∫ ω in S, Φ (statePath Λ B (hitStop Λ B C N ω) ω) ∂Q =
      ∫ ω in S, Φ (Λ 0 ω, 0) ∂Q := by
  have hQ := hB.isProbabilityMeasure'
  set σ := hitStop Λ B C N with hσdef
  have hσ := isStoppingTime_hitStop (N := N) hB hBc hΛm hΛc hC
  have hmemK : ∀ ω (t : ℝ≥0), t ≤ σ ω → statePath Λ B t ω ∈ K := fun ω t ht =>
    mem_K_of_le_hitStop hΛc hBc hCK (h0 ω) ht
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hΨ
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  set lam : ℝ → Ω → E := fun s ω => Ψ (statePath Λ B s.toNNReal ω) with hlam
  have hpc : ∀ ω, Continuous fun s : ℝ => statePath Λ B s.toNNReal ω := fun ω =>
    (continuous_statePath hΛc hBc ω).comp continuous_real_toNNReal
  have hlamc : ∀ ω, ContinuousOn (fun s => lam s ω) (Icc 0 (σ ω)) := fun ω =>
    hΨ.comp (hpc ω).continuousOn fun s hs =>
      hmemK ω _ (Real.toNNReal_le_iff_le_coe.2 hs.2)
  have hΛσm : ∀ t, Measurable[𝓖 t] fun ω => Λ (min t (σ ω)) ω := fun t => by
    have h := Ito.measurable_stopped_of_agree (X := Λ) hσ hΛm (G := univ)
      (@MeasurableSet.univ _ (𝓖 0)) (0 : E) (fun _ _ _ _ => rfl)
      (fun ω _ => (hΛc ω).continuousOn) t
    simpa using h
  have hmart := Ito.martingale_itoLocalized (B := B) (Λ := Λ) (lam := lam) hB hBc hU hΦ hK hKU hσ
    hΛσm (fun ω => (hlamc ω).intervalIntegrable_of_Icc (σ ω).coe_nonneg)
    (fun ω t _ => hΛeq ω t) (Kb := N * max M 0) (fun ω => ?_) (fun ω t ht => hmemK ω t ht)
  · -- the drift integral vanishes
    have hzero : ∀ ω (t : ℝ≥0), ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0),
        Ito.itoGen Φ (Λ s.toNNReal ω, B s.toNNReal ω) (lam s ω) = 0 := by
      intro ω t
      refine intervalIntegral.integral_zero_ae (Eventually.of_forall fun s hs => ?_)
      rw [uIoc_of_le (NNReal.coe_nonneg _)] at hs
      have hsσ : s.toNNReal ≤ σ ω := by
        refine Real.toNNReal_le_iff_le_coe.2 (hs.2.trans ?_)
        exact_mod_cast min_le_right t (σ ω)
      exact hgen _ (hmemK ω _ hsσ)
    have hsi := hmart.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ N) hS
    have hL : ∀ ω, Φ (Λ (min N (σ ω)) ω, B (min N (σ ω)) ω) -
        ∫ s in (0 : ℝ)..(min N (σ ω) : ℝ≥0), Ito.itoGen Φ (Λ s.toNNReal ω, B s.toNNReal ω)
          (lam s ω) = Φ (statePath Λ B (σ ω) ω) := fun ω => by
      rw [hzero, sub_zero, min_eq_right (hitStop_le ω)]; rfl
    have hR : ∀ ω, Φ (Λ (min 0 (σ ω)) ω, B (min 0 (σ ω)) ω) -
        ∫ s in (0 : ℝ)..(min 0 (σ ω) : ℝ≥0), Ito.itoGen Φ (Λ s.toNNReal ω, B s.toNNReal ω)
          (lam s ω) = Φ (Λ 0 ω, 0) := fun ω => by
      rw [hzero, sub_zero, min_eq_left (zero_le (a := σ ω)), hB0]
    rw [← hσdef] at hsi
    simp only [hL, hR] at hsi
    exact hsi.symm
  · -- the bound on `∫₀^σ ‖λ‖`
    have hle : ∀ s ∈ uIoc (0 : ℝ) (σ ω), ‖lam s ω‖ ≤ max M 0 := by
      intro s hs
      rw [uIoc_of_le (σ ω).coe_nonneg] at hs
      have : s.toNNReal ≤ σ ω := Real.toNNReal_le_iff_le_coe.2 hs.2
      exact (hM _ (hmemK ω _ this)).trans (le_max_left _ _)
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := σ ω)
      (f := fun s => ‖lam s ω‖) (fun s hs => by rw [norm_norm]; exact hle s hs)
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg (σ ω).coe_nonneg] at hint
    have h1 : ∫ s in (0 : ℝ)..(σ ω), ‖lam s ω‖ ≤ max M 0 * (σ ω) := (le_abs_self _).trans hint
    have h2 : ((σ ω : ℝ≥0) : ℝ) ≤ N := by exact_mod_cast hitStop_le ω
    nlinarith

end Loc

end Aux25

end InteractingSLE
