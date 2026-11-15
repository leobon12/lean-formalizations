/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1LargeDensWord
import InteractingSLE.Spec.ZhanGT4.A1LargeDensD9

/-!
# Zhan's A.1 (R80): the large-curve direction's one-sample law from enclosure data

Packet PROVE-A1-LARGEDENS. Source: Astra, *Follow-up proofs* §A.1.3 (`ig1_followup_proofs.txt` L300–L355, R38): the
(D9) constants of a protected rectangle, (D8)/Girsanov, (D10), the capacity time change and Lévy's characterization,
"with the other curve stopped".

This file combines the large-curve direction's (D9) assembly with the small curve's accesses as frozen-chart marks
(`exists_frzD10Hyp_left_marks`) with the one-sample laws of the large image words
(`isSeedSampleLaw_largeEight_of_frzD10Hyp`, `isSeedSampleLaw_largeG3_of_frzD10Hyp`). The frozen-curve hypotheses
`FrzD10Hyp` are no longer premises; what remains is deterministic enclosure geometry:

* the growing (large) curve is `√κB` for a Brownian motion `B` of `𝓕` under `P`, with image data (`OwnData`) up to
  `T ≤ Tm` and hull in the enclosure `H₁`; `S ≤ T` is a stopping time;
* the frozen (small) curve has the continuous physical driver `W₂`, starts in `closure H₂` left of the protected point
  `q < 0`, and is frozen at `0 < t₂ ≤ Tm` with hull in `H₂`; the enclosures are `2δ`-separated and `B(q, 2d)` misses
  both;
* the frozen-chart marks (the images of the small curve's seeds and ordinary marks) lie left of the frozen image of
  `q`, are bounded by `M`, and are `ν`-separated from the frozen tip `W₂(t₂)` and from each other.

Results: **`isSeedSampleLaw_largeEight_of_encl`** and **`isSeedSampleLaw_largeG3_of_encl`**: A1-FAMILY's one-sample law
`IsSeedSampleLaw` of the large image word under `Q = (M̃_S/M̃_0)·P`, for seeded data carrying the large curve's image
chain; **`isSeedSampleLaw_withDensity_of_ae_eq`**: the same law under `P.withDensity D` for every density `D` equal
`P`-a.e. to `M̃_S/M̃_0` (the interface for the patch coupling's rectangle density).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1LargeDens

open A1Family A1MultiMark A1Forces A2X
open QuantumZipper (fwdMap fwdHull drive)

section Encl

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {W' a : Ω → ℝ → ℝ}
  {S : Ω → ℝ≥0} {T : Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} {n' : ℕ} {d : Ω → SeedData n'}
  {A' : Ω → Set ℂ} {Wi : ℝ≥0 → Ω → ℝ} {ζi : Ω → ℝ≥0∞} {N : ℝ≥0 → Ω → ℝ} {Scap : ℕ → Ω → ℝ≥0} {m : ℕ}
  {H₁ H₂ : Set ℂ} {δ q d₀ ν M Tm : ℝ} {W₂ : ℝ → ℝ} {t₂ : ℝ}

/-- A Brownian motion under a probability measure lives on a nonempty space. -/
theorem nonempty_of_isFilteredBrownianReal (hB : IsFilteredBrownianReal 𝓕 B P) : Nonempty Ω := by
  have hP := hB.isProbabilityMeasure'
  by_contra h
  rw [not_nonempty_iff] at h
  have := hP.measure_univ
  rw [Set.univ_eq_empty_iff.2 h, measure_empty] at this
  exact zero_ne_one this

/-- The driver bound used by the capacity time change: the hulls stay in the bounded enclosure `H₁`. -/
theorem exists_abs_B_le {n : ℕ} {A : Set ℂ} {φ : ℂ → ℂ} {rr : Fin n → ℝ} {ζ₀ : ℝ} {ζ : Fin n → ℝ}
    {r a₀ γ Γ lam L : ℝ} (hH : FrzD10Hyp κ B W' a A φ rr ζ₀ ζ S T r a₀ γ Γ lam L Tm) (hκ : 0 < κ)
    (hBc : ∀ ω, Continuous (B · ω)) (hH₁ : IsHPHull H₁) (hK₁ : ∀ ω, fwdHull (drive κ B ω) (T ω) ⊆ H₁) :
    ∃ NB : ℝ, ∀ ω (t : ℝ≥0), t ≤ S ω → |B t ω| ≤ NB := by
  obtain ⟨C, hC⟩ := hH₁.2.1.exists_norm_le
  exact ⟨_, hH.abs_B_le hκ hBc (R := max C 1) (lt_of_lt_of_le one_pos (le_max_right _ _))
    fun ω z hz => mem_closedBall_zero_iff.2 ((hC z (hK₁ ω hz)).trans (le_max_left _ _))⟩

/-- **(Eight) The large-curve direction's one-sample law from enclosure data**: image word `x⁺`, the small tip, `x⁻`
(frozen-chart marks `pp`, `W₂(t₂)`, `pm`) with A.1's weights `largeEightImgRhoL κ`, under `Q = (M̃_S/M̃_0)·P`. -/
theorem isSeedSampleLaw_largeEight_of_encl (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂) (hδ : 0 < δ)
    (hsepδ : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖) (hd : 0 < d₀) (hq : q < 0)
    (hqH : Disjoint (ball (q : ℂ) (2 * d₀)) (H₁ ∪ H₂)) (hν : 0 < ν) (hκ : 0 < κ)
    (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    (hown₁ : ∀ ω, OwnData (drive κ B ω) (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) (T ω) (a ω) (W' ω))
    (hST : ∀ ω, (S ω : ℝ) ≤ T ω) (hTm : ∀ ω, T ω ≤ Tm) (hK₁ : ∀ ω, fwdHull (drive κ B ω) (T ω) ⊆ H₁)
    (hW₂ : Continuous W₂) (hW₂H : ((W₂ 0 : ℝ) : ℂ) ∈ closure H₂) (hqW : W₂ 0 < q) (ht₂ : 0 < t₂)
    (ht₂m : t₂ ≤ Tm) (hK₂ : fwdHull W₂ t₂ ⊆ H₂) {pp pm : ℝ}
    (hζq : ∀ k, ![pp, pm] k < (fwdMap W₂ t₂ q).re + W₂ t₂) (hζM : ∀ k, |![pp, pm] k| ≤ M)
    (hζν : ∀ k, ν ≤ |![pp, pm] k - W₂ t₂|) (hζνmk : ∀ k l, k ≠ l → ν ≤ |![pp, pm] k - ![pp, pm] l|)
    (hown : ∀ ω, OwnData (d ω).W (A' ω) (d ω).φ (S ω) (d ω).a (d ω).W') (hda : ∀ ω, (d ω).a = a ω)
    (hdW' : ∀ ω, (d ω).W' = W' ω) {VL : Fin 3 → ℝ≥0 → Ω → ℝ} {VR : Fin 0 → ℝ≥0 → Ω → ℝ}
    (hSm : ∀ ω, Scap m ω = seedCapacityHorizon d S ω)
    (hW : ∀ ω t, t ≤ Scap m ω → Wi t ω = seedCapacityDriver d S t ω)
    (hVL : ∀ ω i t, t ≤ Scap m ω →
      VL i t ω = capForce d S (fun ω => frzImg (d ω).W' (d ω).a (![pp, W₂ t₂, pm] i)) t ω)
    (hN : ∀ ω t, t ≤ Scap m ω → N t ω = seedCapacityNoise κ (largeEightImgRhoL κ) ![] (Wi · ω)
      (fun i t => VL i t ω) (fun j t => VR j t ω) t)
    (hζ : ∀ ω, (Scap m ω : ℝ≥0∞) ≤ ζi ω)
    (Tk : ℕ → Ω → ℝ≥0) (hT : ∀ k, IsStoppingTime 𝓕 fun ω => (Tk k ω : WithTop ℝ≥0))
    (hcap₁ : ∀ k ω, Tk k ω ≤ S ω → (Scap k ω : ℝ) = (d ω).a (Tk k ω))
    (hcap₂ : ∀ k ω, S ω ≤ Tk k ω → Scap m ω ≤ Scap k ω) :
    IsSeedSampleLaw (girsMeasure P (Real.sqrt κ) B S fun ω =>
        (frzDataOf κ B W' a (fun z => fwdMap W₂ t₂ z + W₂ t₂) (largeEightRR κ) (W₂ t₂) ![pp, pm] ω).ell)
      Wi ζi VL VR N Scap m := by
  have := nonempty_of_isFilteredBrownianReal hB
  obtain ⟨r, a₀, γ, Γ, lam, L, hmain⟩ :=
    exists_frzD10Hyp_left_marks (Ω := Ω) hH₁ hH₂ hδ hsepδ hd hq hqH (M := M) hν 2 Tm
  have hH := hmain κ B W' a (largeEightRR κ) ![pp, pm] W₂ t₂ S T hown₁ hST hTm hK₁ hW₂ hW₂H hqW ht₂ ht₂m hK₂ hζq
    hζM hζν hζνmk
  obtain ⟨NB, hBb⟩ := exists_abs_B_le hH hκ hBc hH₁ hK₁
  exact isSeedSampleLaw_largeEight_of_frzD10Hyp hH hκ hB hBc hS hBb hown hda hdW' hSm hW hVL hN hζ Tk hT hcap₁
    hcap₂

/-- **(G3) The large-curve direction's one-sample law from enclosure data**: image word `x`, `y⁺`, the small tip,
`y⁻` (frozen-chart marks `px`, `pp`, `W₂(t₂)`, `pm`) with A.1's weights `largeG3ImgRhoL κ`, under `Q = (M̃_S/M̃_0)·P`
(`B` a Brownian motion with `√κB` the large curve's driver up to `T`). -/
theorem isSeedSampleLaw_largeG3_of_encl (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂) (hδ : 0 < δ)
    (hsepδ : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖) (hd : 0 < d₀) (hq : q < 0)
    (hqH : Disjoint (ball (q : ℂ) (2 * d₀)) (H₁ ∪ H₂)) (hν : 0 < ν) (hκ : 0 < κ)
    (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    (hown₁ : ∀ ω, OwnData (drive κ B ω) (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) (T ω) (a ω) (W' ω))
    (hST : ∀ ω, (S ω : ℝ) ≤ T ω) (hTm : ∀ ω, T ω ≤ Tm) (hK₁ : ∀ ω, fwdHull (drive κ B ω) (T ω) ⊆ H₁)
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
    IsSeedSampleLaw (girsMeasure P (Real.sqrt κ) B S fun ω =>
        (frzDataOf κ B W' a (fun z => fwdMap W₂ t₂ z + W₂ t₂) (largeG3RR κ) (W₂ t₂) ![px, pp, pm] ω).ell)
      Wi ζi VL VR N Scap m := by
  have := nonempty_of_isFilteredBrownianReal hB
  obtain ⟨r, a₀, γ, Γ, lam, L, hmain⟩ :=
    exists_frzD10Hyp_left_marks (Ω := Ω) hH₁ hH₂ hδ hsepδ hd hq hqH (M := M) hν 3 Tm
  have hH := hmain κ B W' a (largeG3RR κ) ![px, pp, pm] W₂ t₂ S T hown₁ hST hTm hK₁ hW₂ hW₂H hqW ht₂ ht₂m hK₂ hζq
    hζM hζν hζνmk
  obtain ⟨NB, hBb⟩ := exists_abs_B_le hH hκ hBc hH₁ hK₁
  exact isSeedSampleLaw_largeG3_of_frzD10Hyp hH hκ hB hBc hS hBb hown hda hdW' hSm hW hVL hN hζ Tk hT hcap₁ hcap₂

/-- **The one-sample law transfers to any density equal to the Girsanov density almost everywhere** (the interface
for the rectangle density `D σ m (x, ·)` of the patch coupling: once it agrees `P`-a.e. with `M̃_S/M̃_0`, the
large-curve direction's one-sample law holds under `P.withDensity D`, the form of `FrozenFamilyFst.ofSampleLaw`). -/
theorem isSeedSampleLaw_withDensity_of_ae_eq {nL nR : ℕ} {σ : ℝ} {ℓ : Ω → ℝ → ℝ → ℝ} {Wj : ℝ≥0 → Ω → ℝ}
    {ζj : Ω → ℝ≥0∞} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (h : IsSeedSampleLaw (girsMeasure P σ B S ℓ) Wj ζj VL VR N Scap m) {D : Ω → ℝ≥0∞}
    (hD : D =ᵐ[P] fun ω => ENNReal.ofReal (girsDensity σ B S ℓ ω)) :
    IsSeedSampleLaw (P.withDensity D) Wj ζj VL VR N Scap m := by
  rwa [withDensity_congr_ae hD]

end Encl

end InteractingSLE.ZhanGT4.A1LargeDens
