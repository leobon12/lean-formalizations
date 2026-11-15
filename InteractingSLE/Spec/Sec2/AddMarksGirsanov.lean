/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.GirsanovSLE
import InteractingSLE.Spec.Sec2.AddMarksPath

/-!
# Changing the weights of separated marks by Girsanov's theorem, and consistency of the localizations

Packet PROVE-SEC2-GIR2. Specification, proof of Theorem 2.2 (`source/spec/p001-048.md`):

* L486: "one can obtain existence of a process with the properties above, defined up until the first
  time that one of the *other* force points collides with `W_t`, using a Girsanov transformation …
  (as long as one stops at a bounded stopping time that occurs before `W_t` gets within some fixed
  constant distance of one of the other force points)";
* L488: "One can also reverse this procedure (starting with a process defined for multiple force
  points and applying Girsanov's theorem to produce the process corresponding to one force point)".

Both steps change the weights of marks that stay at distance `≥ δ` from the driver before a bounded
stopping time `τ`: adding marks changes their weight from `0` to `ρ`, removing them from `ρ` to `0`
(a mark of weight `0` only follows the Loewner flow of the driver).

* `Sec2.IsSLEEvolutionUpTo`: a filtered Brownian motion and processes adapted before `τ` whose paths
  are almost surely local integrated paths (`Sec2.IsSLEPathUpTo`) before `τ`;
  `IsIntegratedSLEEvolution.isSLEEvolutionUpTo` (Definition 2.1 gives one) and
  `IsSLEEvolutionUpTo.mono` (restriction to an earlier stopping time);
* `IsSLEEvolutionUpTo.girsanov_changeWeights`: **the Girsanov step**. Under `Q = Z_{T+1} · P`, with `Z`
  the Doléans density of `θ = weightDrift …` (minus `κ^{-1/2}` times the change of drift, cut at `τ`),
  `Q` is a probability measure equivalent to `P` and the same processes, with the Brownian motion
  `B̃ = B + ∫ θ`, are a local evolution of the force word with the new weights before `τ`;
* `girsanovMeasure_apply_eq_of_eqOn`: two Girsanov measures agree on every event of `𝓕_d` on which
  the two drifts agree before `d`;
* `girsanovMeasure_weightDrift_apply_eq`: **consistency of the localizations** (the input of the
  patching "up to the first collision"): the changed measures for two stopping times `τ₁ ≤ τ₂` (and
  any two cut levels) agree on every event of `𝓕_d` contained in `{d ≤ τ₁}`; in particular on the
  finite-dimensional events of the state killed at `τ₁`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

/-- **A local integrated `SLE_a(ρ)` evolution before the random time `τ`** on `(Ω, 𝓕, P)`: `B` is a
Brownian motion of `𝓕`, `W` and the marks are adapted before `τ` (`AdaptedBefore`), and almost
surely the paths are a local integrated path (`IsSLEPathUpTo`) before `τ`. With `τ = ζ` the
lifetime, an evolution of Definition 2.1 is one (`IsIntegratedSLEEvolution.isSLEEvolutionUpTo`). -/
structure IsSLEEvolutionUpTo (a : ℝ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0∞) : Prop where
  brownian : IsFilteredBrownianReal 𝓕 B P
  adapted_W : AdaptedBefore 𝓕 τ W
  adapted_VL : ∀ i, AdaptedBefore 𝓕 τ (VL i)
  adapted_VR : ∀ i, AdaptedBefore 𝓕 τ (VR i)
  ae_path : ∀ᵐ ω ∂P, IsSLEPathUpTo a xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
    (fun i t => VR i t ω) (fun t => B t ω) (τ ω)

end Sec2

open Sec2 Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ τ : Ω → ℝ≥0∞}

/-- Adaptedness before a later time gives adaptedness before an earlier stopping time. -/
theorem AdaptedBefore.of_le {X : ℝ≥0 → Ω → ℝ} (hX : AdaptedBefore 𝓕 ζ X)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s}) (hle : ∀ ω, τ ω ≤ ζ ω) :
    AdaptedBefore 𝓕 τ X := by
  intro t A hA
  have h : {ω | (t : ℝ≥0∞) < τ ω ∧ X t ω ∈ A}
      = {ω | τ ω ≤ t}ᶜ ∩ {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω ∈ A} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_compl_iff, not_le]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h1.trans_le (hle ω), h2⟩, fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩⟩
  rw [h]
  exact (hτ t).compl.inter (hX t A hA)

/-- An evolution of Definition 2.1 is a local evolution before its lifetime. -/
theorem IsIntegratedSLEEvolution.isSLEEvolutionUpTo
    (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    IsSLEEvolutionUpTo a xL xR ρL ρR P 𝓕 W VL VR B ζ := by
  obtain ⟨hB, hW, hVL, hVR, hpath⟩ := h
  exact ⟨hB, hW, hVL, hVR, hpath.mono fun ω hp => hp.isSLEPathUpTo le_rfl⟩

namespace Sec2.IsSLEEvolutionUpTo

/-- Restriction of a local evolution to an earlier stopping time. -/
theorem mono (h : IsSLEEvolutionUpTo a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s}) (hle : ∀ ω, τ ω ≤ ζ ω) :
    IsSLEEvolutionUpTo a xL xR ρL ρR P 𝓕 W VL VR B τ :=
  ⟨h.brownian, h.adapted_W.of_le hτ hle, fun i => (h.adapted_VL i).of_le hτ hle,
    fun i => (h.adapted_VR i).of_le hτ hle, h.ae_path.mono fun ω hp => hp.mono (hle ω)⟩

end Sec2.IsSLEEvolutionUpTo

/-! ### The drift of a change of weights -/

namespace Sec2

/-- The change of the weights, indexed like `Girsanov.allMarks` (left marks first). -/
def weightDiff {nL nR : ℕ} (ρL ρL' : Fin nL → ℝ) (ρR ρR' : Fin nR → ℝ) : Fin (nL + nR) → ℝ :=
  Fin.addCases (motive := fun _ => ℝ) (fun i => ρL' i - ρL i) (fun i => ρR' i - ρR i)

/-- The Girsanov drift of the change of weights `(ρL; ρR) → (ρL'; ρR')`, cut at `τ` and at level `δ`:
`θ = −κ^{-1/2} ∑ (ρ' − ρ) r_δ(W − V)` before `τ`, `0` after. -/
def weightDrift (κ δ : ℝ) {nL nR : ℕ} (ρL ρL' : Fin nL → ℝ) (ρR ρR' : Fin nR → ℝ)
    (τ ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  shiftDrift κ 1 δ (weightDiff ρL ρL' ρR ρR') τ ζ W (allMarks VL VR)

end Sec2

theorem Sec2.allMarks_adaptedBefore (hVL : ∀ i, AdaptedBefore 𝓕 ζ (VL i))
    (hVR : ∀ i, AdaptedBefore 𝓕 ζ (VR i)) (k : Fin (nL + nR)) :
    AdaptedBefore 𝓕 ζ (allMarks VL VR k) := by
  cases k using Fin.addCases with
  | left i => simpa [allMarks] using hVL i
  | right i => simpa [allMarks] using hVR i

/-- The weighted drift integrals of all marks split into the left and the right sums. -/
theorem Sec2.sum_weightDiff_integral (ρL ρL' : Fin nL → ℝ) (ρR ρR' : Fin nR → ℝ) (ω : Ω)
    (t : ℝ) :
    ∑ k, ∫ s in (0 : ℝ)..t, weightDiff ρL ρL' ρR ρR' k
        / (W s.toNNReal ω - allMarks VL VR k s.toNNReal ω)
      = (∑ i, ∫ s in (0 : ℝ)..t, (ρL' i - ρL i) / (W s.toNNReal ω - VL i s.toNNReal ω))
        + (∑ i, ∫ s in (0 : ℝ)..t, (ρR' i - ρR i) / (W s.toNNReal ω - VR i s.toNNReal ω)) := by
  rw [Fin.sum_univ_add]
  simp only [weightDiff, allMarks, Fin.addCases_left, Fin.addCases_right]

/-- **The Girsanov step: changing the weights of separated marks** (Specification, proof of
Theorem 2.2, L486 "adding" and L488 "removing" force points, and the many-point extension of the
two-seed case, L548). Let `(W, V, B)` be a local evolution of the force word `(xL; xR)`, `(ρL; ρR)`
before `ζ`, let `(ρL'; ρR')` be new weights, and let `τ ≤ ζ ∧ T` be a stopping time before which
every mark whose weight changes stays at distance `≥ δ > 0` from `W` ("a bounded stopping time that
occurs before `W_t` gets within some fixed constant distance of one of the other force points").
With `θ = weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR` and `Q = Z_{T+1} · P`:

* `Q` is a probability measure equivalent to `P`;
* under `Q`, `(W, V, B̃)` with `B̃ = B + ∫₀^· θ` is a local evolution of the force word with the new
  weights `(ρL'; ρR')` before `τ`. -/
theorem Sec2.IsSLEEvolutionUpTo.girsanov_changeWeights [IsProbabilityMeasure P] {κ : ℝ}
    (hκ : 0 < κ) (hE : IsSLEEvolutionUpTo κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (ρL' : Fin nL → ℝ)
    (ρR' : Fin nR → ℝ) (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s})
    (hτζ : ∀ ω, τ ω ≤ ζ ω) {T : ℝ≥0} (hτT : ∀ ω, τ ω ≤ T) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω →
      (∀ i, ρL' i ≠ ρL i → δ ≤ |W t ω - VL i t ω|) ∧
        ∀ i, ρR' i ≠ ρR i → δ ≤ |W t ω - VR i t ω|) :
    MathFin.IsEquivProbMeasure P
      (girsanovMeasure P 𝓕 B (weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR) (T + 1)) ∧
    IsSLEEvolutionUpTo κ xL xR ρL' ρR'
      (girsanovMeasure P 𝓕 B (weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR) (T + 1)) 𝓕 W VL VR
      (girsanovProcess B (weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR)) τ := by
  have hU := allMarks_adaptedBefore hE.adapted_VL hE.adapted_VR
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} ∧
      ∀ k, ContinuousOn (fun s => allMarks VL VR k s ω) {s | (s : ℝ≥0∞) < ζ ω} := by
    filter_upwards [hE.ae_path] with ω hp
    refine ⟨hp.continuousOn_w, fun k => ?_⟩
    cases k using Fin.addCases with
    | left i => simpa [allMarks] using hp.continuousOn_vL i
    | right i => simpa [allMarks] using hp.continuousOn_vR i
  have hgap' : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω → ∀ k,
      weightDiff ρL ρL' ρR ρR' k ≠ 0 → δ ≤ |W t ω - allMarks VL VR k t ω| := by
    filter_upwards [hgap] with ω hg t ht k hk
    cases k using Fin.addCases with
    | left i =>
      simp only [weightDiff, allMarks, Fin.addCases_left] at hk ⊢
      exact (hg t ht).1 i (sub_ne_zero.1 hk)
    | right i =>
      simp only [weightDiff, allMarks, Fin.addCases_right] at hk ⊢
      exact (hg t ht).2 i (sub_ne_zero.1 hk)
  obtain ⟨h1, h2, h3⟩ := girsanov_shift_drift (P := P) hκ 1 hδ (weightDiff ρL ρL' ρR ρR')
    hE.brownian hE.adapted_W hU hτ hτζ hτT hcont hgap'
  refine ⟨h1, ⟨h2, hE.adapted_W.of_le hτ hτζ, fun i => (hE.adapted_VL i).of_le hτ hτζ,
    fun i => (hE.adapted_VR i).of_le hτ hτζ, h1.ac.ae_le ?_⟩⟩
  filter_upwards [h3, hE.ae_path, hgap] with ω h3ω hp hg
  refine (hp.mono (hτζ ω)).changeWeights ρL' ρR' ?_ ?_ ?_
  · intro t ht i hi he
    have := (hg t ht).1 i hi
    rw [he, sub_self, abs_zero] at this
    exact absurd this (not_le.2 hδ)
  · intro t ht i hi he
    have := (hg t ht).2 i hi
    rw [he, sub_self, abs_zero] at this
    exact absurd this (not_le.2 hδ)
  · intro t ht
    obtain ⟨-, hB⟩ := h3ω t ht.le
    rw [sum_weightDiff_integral] at hB
    simp only [sum_integral_div_eq] at hB ⊢
    have eL : ∑ i, (ρL i - ρL' i) * ∫ s in (0 : ℝ)..(t : ℝ), (W s.toNNReal ω - VL i s.toNNReal ω)⁻¹
        = -∑ i, (ρL' i - ρL i) * ∫ s in (0 : ℝ)..(t : ℝ), (W s.toNNReal ω - VL i s.toNNReal ω)⁻¹ := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have eR : ∑ i, (ρR i - ρR' i) * ∫ s in (0 : ℝ)..(t : ℝ), (W s.toNNReal ω - VR i s.toNNReal ω)⁻¹
        = -∑ i, (ρR' i - ρR i) * ∫ s in (0 : ℝ)..(t : ℝ), (W s.toNNReal ω - VR i s.toNNReal ω)⁻¹ := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [eL, eR]
    unfold weightDrift
    linarith

/-! ### Two Girsanov measures agree on events where their drifts agree -/

namespace Girsanov

variable {θ θ' : ℝ≥0 → Ω → ℝ}

/-- The dyadic Riemann sums up to time `d` only see the integrand before `d`. -/
theorem riemannSum_eq_of_eqOn {d : ℝ≥0} {ω : Ω} (h : ∀ t < d, θ t ω = θ' t ω) (n : ℕ) :
    riemannSum B θ n d ω = riemannSum B θ' n d ω := by
  unfold riemannSum
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : grid n i < d
  · rw [h _ hi]
  · have hdi : d ≤ grid n i := not_lt.1 hi
    have h1 : min (grid n (i + 1)) d = d := min_eq_right (hdi.trans (grid_mono n (Nat.le_succ i)))
    have h2 : min (grid n i) d = d := min_eq_right hdi
    rw [h1, h2, sub_self, mul_zero, mul_zero]

/-- The quadratic integral up to time `d` only sees the integrand before `d`. -/
theorem quadInt_eq_of_eqOn {d : ℝ≥0} {ω : Ω} (h : ∀ t < d, θ t ω = θ' t ω) :
    quadInt θ d ω = quadInt θ' d ω := by
  unfold quadInt
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_ne_real (d : ℝ)] with u hud hu
  rw [uIoc_of_le d.coe_nonneg] at hu
  have hlt : u.toNNReal < d := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hu.1.le]
    exact lt_of_le_of_ne hu.2 hud
  rw [h _ hlt]

/-- **Locality of the Itô integral**: on an event where two integrands agree before `d`, their
stochastic integrals at time `d` agree almost surely (both are limits in probability of the same
Riemann sums there). -/
theorem stochIntegral_ae_eq_of_eqOn [IsProbabilityMeasure P] (hB : IsFilteredPreBrownian B 𝓕 P)
    (hθm : StronglyAdapted 𝓕 θ) (hθm' : StronglyAdapted 𝓕 θ') {C C' : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) (hθb' : ∀ t ω, |θ' t ω| ≤ C') (hθreg : IsRiemannRegular P θ)
    (hθreg' : IsRiemannRegular P θ') {d : ℝ≥0} {A : Set Ω}
    (heq : ∀ᵐ ω ∂P, ω ∈ A → ∀ t < d, θ t ω = θ' t ω) :
    ∀ᵐ ω ∂P, ω ∈ A → stochIntegral P 𝓕 B θ d ω = stochIntegral P 𝓕 B θ' d ω := by
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_riemannSum hB hθm hθb hθreg d).exists_seq_tendsto_ae
  obtain ⟨ms, hms, hae'⟩ := ((tendstoInMeasure_riemannSum hB hθm' hθb' hθreg' d).comp
    hns.tendsto_atTop).exists_seq_tendsto_ae
  filter_upwards [hae, hae', heq] with ω h1 h2 he hA
  have h1' : Tendsto (fun i => riemannSum B θ (ns (ms i)) d ω) atTop
      (𝓝 (stochIntegral P 𝓕 B θ d ω)) := h1.comp hms.tendsto_atTop
  have h2' : Tendsto (fun i => riemannSum B θ (ns (ms i)) d ω) atTop
      (𝓝 (stochIntegral P 𝓕 B θ' d ω)) := by
    have e : (fun i => riemannSum B θ (ns (ms i)) d ω)
        = fun i => ((fun n => riemannSum B θ' n d) ∘ ns) (ms i) ω :=
      funext fun i => riemannSum_eq_of_eqOn (he hA) _
    rw [e]
    exact h2
  exact tendsto_nhds_unique h1' h2'

/-- The Girsanov measure of an `𝓕_d`-event is the integral of the density at time `d` over it. -/
theorem girsanovMeasure_apply_eq_ofReal_setIntegral [IsProbabilityMeasure P]
    [IsFilteredPreBrownian B 𝓕 P] (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) {d T : ℝ≥0} (hdT : d ≤ T)
    {A : Set Ω} (hA : MeasurableSet[𝓕 d] A) :
    girsanovMeasure P 𝓕 B θ T A
      = ENNReal.ofReal (∫ ω in A, doleansDensity P 𝓕 B θ d ω ∂P) := by
  have hA' : MeasurableSet A := 𝓕.le d A hA
  rw [girsanovMeasure, withDensity_apply _ hA', ← ofReal_integral_eq_lintegral_ofReal,
    (martingale_doleansDensity (B := B) hθ hθb hθreg).setIntegral_eq hdT hA]
  · exact ((memLp_doleansDensity (B := B) hθ.stronglyAdapted hθb hθreg T).integrable
      one_le_two).integrableOn
  · exact ae_of_all _ fun ω => (doleansDensity_pos T ω).le

/-- **Two Girsanov measures agree on every `𝓕_d`-event on which the drifts agree before `d`**
(for horizons `T, T' ≥ d`). The densities at time `d` agree almost surely there
(`stochIntegral_ae_eq_of_eqOn`, `quadInt_eq_of_eqOn`), and each measure of the event is the integral
of its density at time `d` (martingale property). -/
theorem girsanovMeasure_apply_eq_of_eqOn [IsProbabilityMeasure P]
    (hBF : IsFilteredBrownianReal 𝓕 B P) (hθ : IsStronglyProgressive 𝓕 θ)
    (hθ' : IsStronglyProgressive 𝓕 θ') {C C' : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    (hθb' : ∀ t ω, |θ' t ω| ≤ C') (hθreg : IsRiemannRegular P θ)
    (hθreg' : IsRiemannRegular P θ') {d T T' : ℝ≥0} (hdT : d ≤ T) (hdT' : d ≤ T')
    {A : Set Ω} (hA : MeasurableSet[𝓕 d] A)
    (heq : ∀ᵐ ω ∂P, ω ∈ A → ∀ t < d, θ t ω = θ' t ω) :
    girsanovMeasure P 𝓕 B θ T A = girsanovMeasure P 𝓕 B θ' T' A := by
  have := isFilteredPreBrownian_of_isFilteredBrownianReal hBF
  rw [girsanovMeasure_apply_eq_ofReal_setIntegral hθ hθb hθreg hdT hA,
    girsanovMeasure_apply_eq_ofReal_setIntegral hθ' hθb' hθreg' hdT' hA]
  congr 1
  refine setIntegral_congr_ae (𝓕.le d A hA) ?_
  filter_upwards [stochIntegral_ae_eq_of_eqOn (B := B) this hθ.stronglyAdapted hθ'.stronglyAdapted
    hθb hθb' hθreg hθreg' heq, heq] with ω h1 h2 hωA
  simp only [doleansDensity, h1 hωA, quadInt_eq_of_eqOn (h2 hωA)]

end Girsanov

/-! ### Consistency of the localizations of a change of weights -/

namespace Sec2

theorem continuous_shiftIntegrand (κ ε : ℝ) {δ : ℝ} (hδ : 0 < δ) {m : ℕ} (σ : Fin m → ℝ) :
    Continuous fun p : ℝ × (Fin m → ℝ) => shiftIntegrand κ ε δ σ p.1 p.2 :=
  continuous_const.mul (continuous_addedDriftCut σ hδ)

theorem abs_shiftIntegrand_le (κ ε : ℝ) {δ : ℝ} (hδ : 0 < δ) {m : ℕ} (σ : Fin m → ℝ) (w : ℝ)
    (u : Fin m → ℝ) :
    |shiftIntegrand κ ε δ σ w u| ≤ |ε / Real.sqrt κ| * ((∑ j, |σ j|) * δ⁻¹) := by
  rw [shiftIntegrand, abs_mul, abs_neg]
  exact mul_le_mul_of_nonneg_left (abs_addedDriftCut_le σ hδ w u) (abs_nonneg _)

/-- The drift of a change of weights is progressive, bounded and Riemann-regular (the hypotheses
of the Girsanov layer `GirsanovDensity`). -/
theorem IsSLEEvolutionUpTo.weightDrift_props {κ : ℝ}
    (hE : IsSLEEvolutionUpTo κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (ρL' : Fin nL → ℝ)
    (ρR' : Fin nR → ℝ) (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s})
    (hτζ : ∀ ω, τ ω ≤ ζ ω) {δ : ℝ} (hδ : 0 < δ) :
    IsStronglyProgressive 𝓕 (weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR) ∧
    (∀ t ω, |weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR t ω|
      ≤ |1 / Real.sqrt κ| * ((∑ j, |weightDiff ρL ρL' ρR ρR' j|) * δ⁻¹)) ∧
    IsRiemannRegular P (weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR) := by
  have hU := allMarks_adaptedBefore hE.adapted_VL hE.adapted_VR
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} ∧
      ∀ k, ContinuousOn (fun s => allMarks VL VR k s ω) {s | (s : ℝ≥0∞) < ζ ω} := by
    filter_upwards [hE.ae_path] with ω hp
    refine ⟨hp.continuousOn_w, fun k => ?_⟩
    cases k using Fin.addCases with
    | left i => simpa [allMarks] using hp.continuousOn_vL i
    | right i => simpa [allMarks] using hp.continuousOn_vR i
  exact ⟨isStronglyProgressive_cutDrift (continuous_shiftIntegrand κ 1 hδ _) hE.adapted_W hU hτ,
    fun t ω => abs_cutDrift_le (abs_shiftIntegrand_le κ 1 hδ _) t ω,
    isRiemannRegular_cutDrift (continuous_shiftIntegrand κ 1 hδ _) hτζ hcont⟩

/-- Before `τ`, the drift of a change of weights is the uncut drift
`−κ^{-1/2} (∑ (ρL' − ρL)/(W − VL) + ∑ (ρR' − ρR)/(W − VR))`. -/
theorem weightDrift_eq_of_lt {κ δ : ℝ} (hδ : 0 < δ) {ρL' : Fin nL → ℝ} {ρR' : Fin nR → ℝ}
    {ω : Ω} (hτζ : τ ω ≤ ζ ω) (hWc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hVLc : ∀ i, ContinuousOn (fun s => VL i s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hVRc : ∀ i, ContinuousOn (fun s => VR i s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hg : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω →
      (∀ i, ρL' i ≠ ρL i → δ ≤ |W t ω - VL i t ω|) ∧
        ∀ i, ρR' i ≠ ρR i → δ ≤ |W t ω - VR i t ω|) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < τ ω) :
    weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR t ω
      = -(1 / Real.sqrt κ) * ((∑ i, (ρL' i - ρL i) / (W t ω - VL i t ω))
          + ∑ i, (ρR' i - ρR i) / (W t ω - VR i t ω)) := by
  have hUc : ∀ k, ContinuousOn (fun s => allMarks VL VR k s ω) {s | (s : ℝ≥0∞) < ζ ω} := by
    intro k
    cases k using Fin.addCases with
    | left i => simpa [allMarks] using hVLc i
    | right i => simpa [allMarks] using hVRc i
  unfold weightDrift shiftDrift
  rw [cutDrift_eq_of_lt (continuous_shiftIntegrand κ 1 hδ _) hτζ hWc hUc ht, shiftIntegrand,
    addedDriftCut, Fin.sum_univ_add]
  simp only [weightDiff, allMarks, Fin.addCases_left, Fin.addCases_right]
  congr 2
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : ρL' i = ρL i
    · simp [hi]
    · rw [recipCut_of_le hδ ((hg t ht).1 i hi), div_eq_mul_inv]
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : ρR' i = ρR i
    · simp [hi]
    · rw [recipCut_of_le hδ ((hg t ht).2 i hi), div_eq_mul_inv]

/-- The drift of a change of weights cut at `τ` does not depend on the lifetime used to kill the
coordinates, as long as it is at least `τ`. -/
theorem weightDrift_congr_lifetime {κ δ : ℝ} {ρL' : Fin nL → ℝ} {ρR' : Fin nR → ℝ}
    {ζ' : Ω → ℝ≥0∞} (h : ∀ ω, τ ω ≤ ζ ω) (h' : ∀ ω, τ ω ≤ ζ' ω) :
    weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR = weightDrift κ δ ρL ρL' ρR ρR' τ ζ' W VL VR := by
  funext t ω
  unfold weightDrift shiftDrift cutDrift
  congr 1
  funext n
  unfold cutIntegrand
  split_ifs with hs
  · have h1 := hs.trans_le (h ω)
    have h2 := hs.trans_le (h' ω)
    congr 1
    · simp [killed, h1, h2]
    · funext k
      simp [killed, h1, h2]
  · rfl

/-- **Consistency of the localizations** (the patching input of the existence step up to the first
collision, Specification L486 and the NOTE of the graph node "Adding separated force points by
Girsanov"). For two bounded stopping times `τ₁, τ₂ ≤ ζ` with separation levels `δ₁, δ₂` as in
`girsanov_changeWeights`, the two changed measures agree on every event `A ∈ 𝓕_d` contained in
`{d ≤ τ₁} ∩ {d ≤ τ₂}` (for `d ≤ T₁ + 1, T₂ + 1`): before both stopping times the two cut drifts are
the same uncut drift. -/
theorem IsSLEEvolutionUpTo.girsanovMeasure_weightDrift_apply_eq [IsProbabilityMeasure P] {κ : ℝ}
    (hE : IsSLEEvolutionUpTo κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (ρL' : Fin nL → ℝ)
    (ρR' : Fin nR → ℝ) {τ₁ τ₂ : Ω → ℝ≥0∞}
    (hτ₁ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ₁ ω ≤ s})
    (hτ₂ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ₂ ω ≤ s}) (hτ₁ζ : ∀ ω, τ₁ ω ≤ ζ ω)
    (hτ₂ζ : ∀ ω, τ₂ ω ≤ ζ ω) {δ₁ δ₂ : ℝ} (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂)
    (hgap₁ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ₁ ω →
      (∀ i, ρL' i ≠ ρL i → δ₁ ≤ |W t ω - VL i t ω|) ∧
        ∀ i, ρR' i ≠ ρR i → δ₁ ≤ |W t ω - VR i t ω|)
    (hgap₂ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ₂ ω →
      (∀ i, ρL' i ≠ ρL i → δ₂ ≤ |W t ω - VL i t ω|) ∧
        ∀ i, ρR' i ≠ ρR i → δ₂ ≤ |W t ω - VR i t ω|)
    {d T₁ T₂ : ℝ≥0} (hd₁ : d ≤ T₁) (hd₂ : d ≤ T₂) {A : Set Ω} (hA : MeasurableSet[𝓕 d] A)
    (hAτ : ∀ ω ∈ A, (d : ℝ≥0∞) ≤ τ₁ ω ∧ (d : ℝ≥0∞) ≤ τ₂ ω) :
    girsanovMeasure P 𝓕 B (weightDrift κ δ₁ ρL ρL' ρR ρR' τ₁ ζ W VL VR) T₁ A
      = girsanovMeasure P 𝓕 B (weightDrift κ δ₂ ρL ρL' ρR ρR' τ₂ ζ W VL VR) T₂ A := by
  obtain ⟨h1p, h1b, h1r⟩ := hE.weightDrift_props ρL' ρR' hτ₁ hτ₁ζ hδ₁
  obtain ⟨h2p, h2b, h2r⟩ := hE.weightDrift_props ρL' ρR' hτ₂ hτ₂ζ hδ₂
  refine Girsanov.girsanovMeasure_apply_eq_of_eqOn hE.brownian h1p h2p h1b h2b h1r h2r hd₁ hd₂ hA ?_
  filter_upwards [hE.ae_path, hgap₁, hgap₂] with ω hp hg₁ hg₂ hωA t ht
  have ht₁ : (t : ℝ≥0∞) < τ₁ ω := lt_of_lt_of_le (by exact_mod_cast ht) (hAτ ω hωA).1
  have ht₂ : (t : ℝ≥0∞) < τ₂ ω := lt_of_lt_of_le (by exact_mod_cast ht) (hAτ ω hωA).2
  rw [weightDrift_eq_of_lt hδ₁ (hτ₁ζ ω) hp.continuousOn_w hp.continuousOn_vL hp.continuousOn_vR hg₁
      ht₁, weightDrift_eq_of_lt hδ₂ (hτ₂ζ ω) hp.continuousOn_w hp.continuousOn_vL
      hp.continuousOn_vR hg₂ ht₂]

end Sec2

end InteractingSLE
