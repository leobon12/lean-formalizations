/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3RowGirsanov
import InteractingSLE.Spec.ZhanGT4.A1LargeDensEncl

/-!
# Zhan's A.1 (G3): the large curve's one-sample law, through the Girsanov change to ordinary `SLE_κ`

Packet PROVE-A1-G3ROW. Source: Astra, *Follow-up proofs* §A.1.3 (`ig1_followup_proofs.txt` L300–L355, R38): on a
protected rectangle the large curve is compared with ordinary `SLE_κ` (its own force gaps are bounded below), and the
frozen-curve calculation (D8)/(D10) is run "with the other curve stopped".

A1-LARGEDENS's `isSeedSampleLaw_largeG3_of_encl` gives A1-FAMILY's one-sample law `IsSeedSampleLaw` of the (G3) large
image word under `(M̃_S/M̃_0)·P` for a Brownian motion `B` of `P` whose driver `√κ B` is the large curve at every
sample. The (G3) large curve is `SLE_κ(κ − 4, −4)`, so its own Brownian motion does not qualify. Here:

* **`drive_girsanov_removeAll_eq`**: after removing every mark by Girsanov (`girsanov_removeAll_pathwise`), the
  driver `√κ B⁰` of the new Brownian motion is the large driver on `[0, τ]` before the lifetime, at every sample;
* **`isSeedSampleLaw_largeG3_of_removeAll`**: A1-LARGEDENS's one-sample law of the (G3) large image word under
  `Q⁰.withDensity (M̃_S/M̃_0)`, `Q⁰ = Z_{T+1}·P` the Girsanov measure of `B⁰` (the law of ordinary `SLE_κ` up to the
  rectangle stop), for any integrated `SLE_κ(ρ)` evolution with every-sample path relation, continuous Brownian path
  and force gaps (A1-COMMON's patched marginals);
* **`girsMeasure_girsanovMeasure_eq`**, **`isSeedSampleLaw_withDensity_of_ae_eq_mul`**: the tilted law is
  `P.withDensity (Z_{T+1} · M̃_S/M̃_0)`, so the one-sample law transfers to every density equal to `Z_{T+1}·M̃_S/M̃_0`
  `P`-a.e. (the form of the G3 row identity the patch density must satisfy).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Row

open Girsanov A1Family A1MultiMark A1Forces A2X A1LargeDens
open QuantumZipper (fwdMap fwdHull drive)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {nL nR : ℕ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W B : ℝ≥0 → Ω → ℝ}
  {UL : Fin nL → ℝ≥0 → Ω → ℝ} {UR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ τ : Ω → ℝ≥0∞} {δ : ℝ}

/-- **The new driver is the large driver up to the stop**: at a sample where the path relation holds and the force
gaps are at least `δ` before `τ ≤ ζ`, `drive κ B⁰ ω u = W(u) ω` for every `u ∈ [0, τ]` before the lifetime. -/
theorem drive_girsanov_removeAll_eq (hκ : 0 < κ) (hδ : 0 < δ) {ω : Ω}
    (hp : IsIntegratedSLEPath κ xL xR ρL ρR (W · ω) (fun i t => UL i t ω) (fun i t => UR i t ω) (B · ω) (ζ ω))
    (hτζ : τ ω ≤ ζ ω) (hgL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω → ∀ i, δ ≤ |W t ω - UL i t ω|)
    (hgR : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω → ∀ j, δ ≤ |W t ω - UR j t ω|) {u : ℝ}
    (huτ : (u.toNNReal : ℝ≥0∞) ≤ τ ω) (huζ : (u.toNNReal : ℝ≥0∞) < ζ ω) :
    drive κ (girsanovProcess B (removeAllDrift κ δ ρL ρR τ ζ W UL UR)) ω u = W u.toNNReal ω :=
  (sqrt_mul_girsanovProcess_removeAll hκ hδ hp hτζ hgL hgR huτ huζ).symm

/-- **(G3) The large-curve direction's one-sample law through the Girsanov change to ordinary `SLE_κ`.** Let
`(W, U, B)` be an integrated `SLE_κ(ρ)` evolution (for (G3): the large curve `SLE_κ(κ − 4, −4)`, marks `x, y`) with the
path relation and a continuous Brownian path at every sample, `τ ≤ ζ ∧ T₀` a stopping time before which every force
gap is at least `δ > 0` at every sample, and `B⁰`, `Q⁰` the Brownian motion and measure of
`girsanov_removeAll_pathwise`. Then, with A1-LARGEDENS's enclosure data and family premises for `B⁰` (its driver is
the large curve up to `τ`, `drive_girsanov_removeAll_eq`), A1-FAMILY's one-sample law of the (G3) large image word holds
under `Q⁰.withDensity (M̃_S/M̃_0)`. -/
theorem isSeedSampleLaw_largeG3_of_removeAll [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W UL UR B ζ)
    (hpath : ∀ ω, IsIntegratedSLEPath κ xL xR ρL ρR (W · ω) (fun i t => UL i t ω) (fun i t => UR i t ω) (B · ω)
      (ζ ω))
    (hBc : ∀ ω, Continuous fun t => B t ω) (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s})
    (hτζ : ∀ ω, τ ω ≤ ζ ω) {T₀ : ℝ≥0} (hτT : ∀ ω, τ ω ≤ T₀) (hδ : 0 < δ)
    (hgL : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < τ ω → ∀ i, δ ≤ |W t ω - UL i t ω|)
    (hgR : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < τ ω → ∀ j, δ ≤ |W t ω - UR j t ω|)
    {W' a : Ω → ℝ → ℝ} {S : Ω → ℝ≥0} {T : Ω → ℝ} {n' : ℕ} {d : Ω → SeedData n'} {A' : Ω → Set ℂ}
    {Wi : ℝ≥0 → Ω → ℝ} {ζi : Ω → ℝ≥0∞} {N : ℝ≥0 → Ω → ℝ} {Scap : ℕ → Ω → ℝ≥0} {m : ℕ}
    {H₁ H₂ : Set ℂ} {δ' q d₀ ν M Tm : ℝ} {W₂ : ℝ → ℝ} {t₂ : ℝ}
    (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂) (hδ' : 0 < δ')
    (hsepδ : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ' ≤ ‖a - z‖) (hd : 0 < d₀) (hq : q < 0)
    (hqH : Disjoint (ball (q : ℂ) (2 * d₀)) (H₁ ∪ H₂)) (hν : 0 < ν)
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    (hown₁ : ∀ ω, OwnData (drive κ (girsanovProcess B (removeAllDrift κ δ ρL ρR τ ζ W UL UR)) ω) (fwdHull W₂ t₂)
      (fun z => fwdMap W₂ t₂ z + W₂ t₂) (T ω) (a ω) (W' ω))
    (hST : ∀ ω, (S ω : ℝ) ≤ T ω) (hTm : ∀ ω, T ω ≤ Tm)
    (hK₁ : ∀ ω, fwdHull (drive κ (girsanovProcess B (removeAllDrift κ δ ρL ρR τ ζ W UL UR)) ω) (T ω) ⊆ H₁)
    (hW₂ : Continuous W₂) (hW₂H : ((W₂ 0 : ℝ) : ℂ) ∈ closure H₂) (hqW : W₂ 0 < q) (ht₂ : 0 < t₂)
    (ht₂m : t₂ ≤ Tm) (hK₂ : fwdHull W₂ t₂ ⊆ H₂) {px pp pm : ℝ}
    (hζq : ∀ k, ![px, pp, pm] k < (fwdMap W₂ t₂ q).re + W₂ t₂) (hζM : ∀ k, |![px, pp, pm] k| ≤ M)
    (hζν : ∀ k, ν ≤ |![px, pp, pm] k - W₂ t₂|)
    (hζνmk : ∀ k l, k ≠ l → ν ≤ |![px, pp, pm] k - ![px, pp, pm] l|)
    (hown : ∀ ω, OwnData (d ω).W (A' ω) (d ω).φ (S ω) (d ω).a (d ω).W') (hda : ∀ ω, (d ω).a = a ω)
    (hdW' : ∀ ω, (d ω).W' = W' ω) {VL : Fin 4 → ℝ≥0 → Ω → ℝ} {VR : Fin 0 → ℝ≥0 → Ω → ℝ}
    (hSm : ∀ ω, Scap m ω = seedCapacityHorizon d S ω)
    (hW : ∀ ω t, t ≤ Scap m ω → Wi t ω = seedCapacityDriver d S t ω)
    (hVL : ∀ ω i t, t ≤ Scap m ω →
      VL i t ω = capForce d S (fun ω => frzImg (d ω).W' (d ω).a (![px, pp, W₂ t₂, pm] i)) t ω)
    (hN : ∀ ω t, t ≤ Scap m ω → N t ω = seedCapacityNoise κ (largeG3ImgRhoL κ) ![] (Wi · ω)
      (fun i t => VL i t ω) (fun j t => VR j t ω) t)
    (hζ : ∀ ω, (Scap m ω : ℝ≥0∞) ≤ ζi ω)
    (Tk : ℕ → Ω → ℝ≥0) (hT : ∀ k, IsStoppingTime 𝓕 fun ω => (Tk k ω : WithTop ℝ≥0))
    (hcap₁ : ∀ k ω, Tk k ω ≤ S ω → (Scap k ω : ℝ) = (d ω).a (Tk k ω))
    (hcap₂ : ∀ k ω, S ω ≤ Tk k ω → Scap m ω ≤ Scap k ω) :
    IsSeedSampleLaw (girsMeasure (girsanovMeasure P 𝓕 B (removeAllDrift κ δ ρL ρR τ ζ W UL UR) (T₀ + 1))
        (Real.sqrt κ) (girsanovProcess B (removeAllDrift κ δ ρL ρR τ ζ W UL UR)) S fun ω =>
        (frzDataOf κ (girsanovProcess B (removeAllDrift κ δ ρL ρR τ ζ W UL UR)) W' a
          (fun z => fwdMap W₂ t₂ z + W₂ t₂) (largeG3RR κ) (W₂ t₂) ![px, pp, pm] ω).ell)
      Wi ζi VL VR N Scap m := by
  obtain ⟨hQ, hB0, hB0c, -⟩ := girsanov_removeAll_pathwise hκ hE hpath hBc hτ hτζ hτT hδ hgL hgR
  exact isSeedSampleLaw_largeG3_of_encl hH₁ hH₂ hδ' hsepδ hd hq hqH hν hκ hB0 hB0c hS hown₁ hST hTm hK₁ hW₂ hW₂H
    hqW ht₂ ht₂m hK₂ hζq hζM hζν hζνmk hown hda hdW' hSm hW hVL hN hζ Tk hT hcap₁ hcap₂

/-! ### The tilted law as one density against `P` -/

/-- **The two-step tilt is one density**: `(Z_T · P).withDensity g = (Z_T · g) · P` for a.e.-measurable densities. -/
theorem girsMeasure_girsanovMeasure_eq {θ B0 : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {σ : ℝ} {S : Ω → ℝ≥0}
    {ℓ : Ω → ℝ → ℝ → ℝ}
    (hZ : AEMeasurable (fun ω => ENNReal.ofReal (doleansDensity P 𝓕 B θ T ω)) P)
    (hg : AEMeasurable (fun ω => ENNReal.ofReal (girsDensity σ B0 S ℓ ω)) P) :
    girsMeasure (girsanovMeasure P 𝓕 B θ T) σ B0 S ℓ =
      P.withDensity fun ω => ENNReal.ofReal (doleansDensity P 𝓕 B θ T ω) * ENNReal.ofReal (girsDensity σ B0 S ℓ ω) := by
  rw [girsMeasure, girsanovMeasure, ← withDensity_mul₀ hZ hg]
  rfl

/-- **The one-sample law under a density equal to `Z_T · M̃_S/M̃_0` almost everywhere** (the form of the (G3) row
identity: the patch density `D σ m (x, ·)` must equal the Girsanov density of the change to ordinary `SLE_κ` times the
frozen-curve density, `P`-a.e.). -/
theorem isSeedSampleLaw_withDensity_of_ae_eq_mul {nL' nR' : ℕ} {θ B0 : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {σ : ℝ}
    {S : Ω → ℝ≥0} {ℓ : Ω → ℝ → ℝ → ℝ} {Wj : ℝ≥0 → Ω → ℝ} {ζj : Ω → ℝ≥0∞} {VL : Fin nL' → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR' → ℝ≥0 → Ω → ℝ} {N : ℝ≥0 → Ω → ℝ} {Scap : ℕ → Ω → ℝ≥0} {m : ℕ}
    (h : IsSeedSampleLaw (girsMeasure (girsanovMeasure P 𝓕 B θ T) σ B0 S ℓ) Wj ζj VL VR N Scap m)
    (hZ : AEMeasurable (fun ω => ENNReal.ofReal (doleansDensity P 𝓕 B θ T ω)) P)
    (hg : AEMeasurable (fun ω => ENNReal.ofReal (girsDensity σ B0 S ℓ ω)) P) {D : Ω → ℝ≥0∞}
    (hD : D =ᵐ[P] fun ω => ENNReal.ofReal (doleansDensity P 𝓕 B θ T ω) * ENNReal.ofReal (girsDensity σ B0 S ℓ ω)) :
    IsSeedSampleLaw (P.withDensity D) Wj ζj VL VR N Scap m := by
  rwa [withDensity_congr_ae hD, ← girsMeasure_girsanovMeasure_eq hZ hg]

end InteractingSLE.ZhanGT4.A1G3Row
