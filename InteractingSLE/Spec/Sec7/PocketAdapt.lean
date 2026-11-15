/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketPhaseMeans

/-!
# Prefix adaptedness in the relative history filtration

Packet PROVE-STRIPSYS18 (specification §7.4, proof of Aux. lemma 125, p. 396, "The relative stopping filtration";
p. 397: "These are genuine stopping times in the relative history and supply pre-lifetime localizations for the
martingale and SDE arguments"; Aux. lemma 122, p. 390: "Conditional on initial information fixing the word and its
marked positions, the coordinates satisfy this SDE with Brownian noise independent of that initial information").

The hypothesis `IsPrefixAdapted 𝓕 γ` of `PocketPhaseMeans.pocketWordEvolution_of_charFun` asks that the events "the
relative prefix up to capacity time `r` meets a dyadic square" be `𝓕_r`-measurable. In the **relative history
filtration** — the time-zero information `𝓔` (the walls, the word and its marks) together with these prefix events —
this holds by construction, for any random curve whose prefix events are measurable. Its usual augmentation
(`usualAugmentation`) is right-continuous and contains the null sets, as `pocketWordEvolution_of_charFun` needs.
So hPW reduces to the coupling clause in that filtration:

* `prefixEvent`, `prefixFilt`: the prefix events and the relative history filtration `𝓔 ∨ σ(prefix events up to s)`;
* `isPrefixAdapted_prefixFilt`, `isPrefixAdapted_usualAugmentation_prefixFilt`;
* **`pocketWordEvolution_of_charFun_prefixFilt`**: hPW from a driven random curve with large points and measurable
  prefix events, `𝓔`-measurable marks, and the coupling clause of the pocket word in the usual augmentation of the
  relative history filtration.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketAdapt

open Coupling PocketTraversal PocketPhaseMeans Lemma71C

variable {Ω : Type*} {𝓔 : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}

/-- **The prefix event** at capacity time `r`: before the terminal capacity time, the relative prefix up to capacity
time `r` meets the closed dyadic square `(n, k)`. -/
def prefixEvent (γ : Ω → ℝ → ℂ) (r : ℝ≥0) (n : ℕ) (k : ℤ × ℤ) : Set Ω :=
  {ω | (r : ℝ≥0∞) < capLife (γ ω) ∧ (Restart.dyadicSquare n k ∩ γ ω '' Icc 0 (capInv (γ ω) r)).Nonempty}

/-- The σ-algebra of the time-zero information and the prefix events up to capacity time `s`. -/
@[instance_reducible] def prefixSigma (𝓔 : MeasurableSpace Ω) (γ : Ω → ℝ → ℂ) (s : ℝ≥0) : MeasurableSpace Ω :=
  𝓔 ⊔ MeasurableSpace.generateFrom {A | ∃ r ≤ s, ∃ n k, A = prefixEvent γ r n k}

theorem prefixSigma_mono (𝓔 : MeasurableSpace Ω) (γ : Ω → ℝ → ℂ) : Monotone (prefixSigma 𝓔 γ) := by
  intro s t hst
  refine sup_le_sup_left (MeasurableSpace.generateFrom_mono ?_) _
  rintro A ⟨r, hr, n, k, rfl⟩
  exact ⟨r, hr.trans hst, n, k, rfl⟩

theorem prefixSigma_le (h𝓔 : 𝓔 ≤ mΩ) {γ : Ω → ℝ → ℂ}
    (hm : ∀ r n k, MeasurableSet[mΩ] (prefixEvent γ r n k)) (s : ℝ≥0) : prefixSigma 𝓔 γ s ≤ mΩ := by
  refine sup_le h𝓔 (MeasurableSpace.generateFrom_le ?_)
  rintro A ⟨r, -, n, k, rfl⟩
  exact hm r n k

/-- **The relative history filtration** `s ↦ 𝓔 ∨ σ(prefix events up to capacity time s)`. -/
def prefixFilt (𝓔 : MeasurableSpace Ω) (h𝓔 : 𝓔 ≤ mΩ) (γ : Ω → ℝ → ℂ)
    (hm : ∀ r n k, MeasurableSet[mΩ] (prefixEvent γ r n k)) : Filtration ℝ≥0 mΩ where
  seq := prefixSigma 𝓔 γ
  mono' := prefixSigma_mono 𝓔 γ
  le' := prefixSigma_le h𝓔 hm

variable (h𝓔 : 𝓔 ≤ mΩ) {γ : Ω → ℝ → ℂ} (hm : ∀ r n k, MeasurableSet[mΩ] (prefixEvent γ r n k))

theorem le_prefixFilt_zero : 𝓔 ≤ prefixFilt 𝓔 h𝓔 γ hm 0 := le_sup_left

/-- **The prefixes are adapted to the relative history filtration.** -/
theorem isPrefixAdapted_prefixFilt : IsPrefixAdapted (prefixFilt 𝓔 h𝓔 γ hm) γ := fun r n k =>
  (le_sup_right : _ ≤ prefixSigma 𝓔 γ r) _ (MeasurableSpace.measurableSet_generateFrom ⟨r, le_rfl, n, k, rfl⟩)

/-- **The prefixes are adapted to the usual augmentation of the relative history filtration.** -/
theorem isPrefixAdapted_usualAugmentation_prefixFilt (P : Measure Ω) :
    IsPrefixAdapted (usualAugmentation (prefixFilt 𝓔 h𝓔 γ hm) P) γ := fun r n k =>
  Ito.le_usualAugmentation _ P r _ (isPrefixAdapted_prefixFilt h𝓔 hm r n k)

universe v

/-- **Lemma 7.25's pocket-word evolution (hPW) from the coupling clause in the relative history filtration**
(specification pp. 389–397 and p. 414): `PocketPhaseMeans.pocketWordEvolution_of_charFun` in the usual augmentation
`𝓖` of the relative history filtration `𝓔 ∨ σ(prefix events)`, in which the prefixes are adapted by construction and
the null sets are at time zero. Inputs: a standard Borel probability space; a time-zero σ-algebra `𝓔`; a random driven
curve `γ` with points of `ℍ` of arbitrarily large modulus and measurable prefix events; `𝓔`-measurable marks (seeds at
`0`, the other left marks negative and the other right marks positive, ordered); weights with seed weights
`r_L, r_R < κ/2 − 4` and all side partial sums `> −2`; and a random distribution `h` with integrable pairings satisfying
the conditional-law clause of the pocket word at the geometric force coordinates along the canonical driver, with
lifetime `capLife γ`, in `𝓖`. -/
theorem pocketWordEvolution_of_charFun_prefixFilt {κ rL rR : ℝ} (hκ : 4 < κ) (hLd : rL < κ / 2 - 4)
    (hRd : rR < κ / 2 - 4) {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} (hρL : ρL 0 = rL)
    (hρR : ρR 0 = rR) (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin (nR + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i)
    {Ω : Type v} {𝓔 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓔 : 𝓔 ≤ mΩ) {γ : Ω → ℝ → ℂ} (hm : ∀ r n k, MeasurableSet[mΩ] (prefixEvent γ r n k))
    (hγ : ∀ ω, IsDrivenCurve (γ ω)) (hunb : ∀ ω (M : ℝ), ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} (hxLm : Measurable[𝓔] xL) (hxRm : Measurable[𝓔] xR)
    (hseedL : ∀ ω, xL ω 0 = 0) (hseedR : ∀ ω, xR ω 0 = 0)
    (hxLd : ∀ ω (i : Fin nL), xL ω i.succ < 0) (hxRd : ∀ ω (j : Fin nR), 0 < xR ω j.succ)
    (hxLi : ∀ ω, Antitone (xL ω)) (hxRi : ∀ ω, Monotone (xR ω)) {h : Ω → DistOn upperHalfPlaneOpens}
    (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => h ω φ) P)
    (hcf : MartMeans.IsCouplingCharFun κ ρL ρR P (usualAugmentation (prefixFilt 𝓔 h𝓔 γ hm) P)
      (fun t ω => segDriver (γ ω) t) (geomLW (fun t ω => segDriver (γ ω) t) xL)
      (geomRW (fun t ω => segDriver (γ ω) t) xR) (fun ω => capLife (γ ω)) h) :
    Sec7.Lemma725Ref.PocketWordEvolution.{v} κ rL rR := by
  have h0 : 𝓔 ≤ usualAugmentation (prefixFilt 𝓔 h𝓔 γ hm) P 0 :=
    (le_prefixFilt_zero h𝓔 hm).trans (Ito.le_usualAugmentation _ P 0)
  exact pocketWordEvolution_of_charFun hκ hLd hRd hρL hρR hsL hsR
    (fun s hs h0' => Ito.measurableSet_usualAugmentation_of_null hs h0' 0) hγ hunb
    (isPrefixAdapted_usualAugmentation_prefixFilt h𝓔 hm P) (hxLm.mono h0 le_rfl) (hxRm.mono h0 le_rfl) hseedL
    hseedR hxLd hxRd hxLi hxRi hint hcf

end InteractingSLE.Sec7.PocketAdapt
