/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2YePkg
import InteractingSLE.Spec.Supplement.SB2YfCurve
import InteractingSLE.Spec.Supplement.SB2OmCfg

/-!
# `Om.IsStageS2` at one sample (decisions D38/D39)

Packet PROVE-T14-SB2LIFT (round 32). **`isStageS2_of`**: GEOM2's S2 record `Om.IsStageS2 c Φ B wB sB W u` (the exact
hypothesis `hS2` of `Om.hmean_of_stageS2` at one sample), for the canonical chart `Φ = Mo.hullChart B x₀`, from

* B's stage chart `c` (a domain chart of `ℍ ∖ Y` with mapping-out forward map up to a shift and canonical lift; boundary
  limits of the inverse within bounded distance of the identity), the canonical chart's boundary limits with finite
  fibres, the untouched line `(0, ∞)` in stage coordinates and the offset normalization (the chart package,
  `stageChartPkg`);
* the version's driver `W` with the global Loewner trace `ηr` of `−W`, its clock `τ` on `[0, sB]` (continuous, strictly
  increasing, `τ 0 = 0`, `τ sB = u > 0`), `ηr ∘ τ` in `ℍ̄`;
* B's stopped driver `wB` with the global trace `η` of `−wB`, injective on `[0, sB]` with no real arc and tip in `ℍ`;
* the link: the relative chart's inverse tends to `η r` at `ηr (τ r)` (the relative curve read in B's coordinates).
Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Bornology
open scoped NNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Theorem14.SB.Sx

open Restart Supp9B

variable {c : Chart} {Y B : Set ℂ} {s₀ x₀ : ℝ} {gc gΦ : ℂ → ℂ} {Cc : ℝ}

/-- **GEOM2's S2 record at one sample.** -/
theorem isStageS2_of (hcD : IsDomainChart (H \ Y) c) (hY : IsHPHull Y) (hB : IsHPHull B) (hYB : Y ⊆ B)
    (hg₀ : IsMapOut Y (fun z => c.1 z + (s₀ : ℂ))) {LY : ℂ → ℂ}
    (hLY : IsCanonicalDerivLog Y (fun z => c.1 z + (s₀ : ℂ)) LY) (hlift : EqOn c.2.2 (fun z => (LY z).im) (H \ Y))
    (hgc : ∀ q ∈ Hbar, Tendsto c.2.1 (𝓝[H] q) (𝓝 (gc q))) (hCc : ∀ q ∈ Hbar, ‖gc q - q‖ ≤ Cc)
    (hgΦ : ∀ p ∈ Hbar, Tendsto (Mo.hullChart B x₀).2.1 (𝓝[H] p) (𝓝 (gΦ p)))
    (hgΦf : ∀ z, (gΦ ⁻¹' {z} ∩ {w : ℂ | 0 ≤ w.im}).Finite)
    (hfree : ∀ x : ℝ, 0 < x → ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) (pullHull c B))
    (hnorm : ∃ e : ℝ → ℝ, (∀ x : ℝ, 0 < x → Tendsto (Mn.pullChart c (Mo.hullChart B x₀)).1 (𝓝[H] (x : ℂ))
      (𝓝 (e x : ℂ))) ∧ Tendsto e (𝓝[>] 0) (𝓝 0))
    {W : ℝ → ℝ} {ηr : ℝ → ℂ} {τ : ℝ → ℝ} {sB u : ℝ} {wB : ℝ → ℝ} {η : ℝ → ℂ}
    (hWc : Continuous W) (hW0 : W 0 = 0) (hηr : IsLoewnerTrace (fun r => -W r) ηr) (hsB : 0 < sB) (hu : 0 < u)
    (hτc : ContinuousOn τ (Icc 0 sB)) (hτm : StrictMonoOn τ (Icc 0 sB)) (hτ0 : τ 0 = 0) (hτs : τ sB = u)
    (hηrH : ∀ r ∈ Icc (0 : ℝ) sB, 0 ≤ (ηr (τ r)).im)
    (hwBc : Continuous wB) (hwB0 : wB 0 = 0) (hη : IsLoewnerTrace (fun r => -wB r) η)
    (hηinj : InjOn η (Icc 0 sB)) (hnoarc : interior {r ∈ Ioo (0 : ℝ) sB | (η r).im = 0} = ∅) (hηH : η sB ∈ H)
    (hlink : ∀ r ∈ Icc (0 : ℝ) sB,
      Tendsto (Lf.reflChart (Mn.pullChart c (Mo.hullChart B x₀))).2.1 (𝓝[H] (ηr (τ r))) (𝓝 (η r))) :
    Om.IsStageS2 c (Mo.hullChart B x₀) B wB sB W u := by
  obtain ⟨q, R, g, hqc, hq0, hqH, hqR, hRq, hcr, hgcont, hgi, hgf, hL, hid1, hid2, hid3, hgt, hgm, ⟨K, hK, hqg⟩,
    hreal, ⟨C, hgb⟩⟩ := stageChartPkg hcD hY hB hYB hg₀ hLY hlift hgc hCc hgΦ hgΦf hfree hnorm
  have hlink' : ∀ r ∈ Icc (0 : ℝ) sB, g (ηr (τ r)) = η r := fun r hr => by
    have hp : ηr (τ r) ∈ Hbar := hηrH r hr
    have : (𝓝[H] (ηr (τ r))).NeBot := GW1P.neBot_nhdsWithin_H hp
    exact tendsto_nhds_unique (hgt _ hp) (hlink r hr)
  have hWc' : Continuous fun r => -W r := hWc.neg
  have hW0' : (fun r => -W r) 0 = 0 := by simp only [hW0, neg_zero]
  obtain ⟨β', γ, S₀, Sm, hβ', hβ'0, hS1, hγ, hγ0, hglift, hchain, hS₀Sm, hnoarc', hsBS₀, hwhull, hηβ, hcap⟩ :=
    stageCurvePkg hqc hq0 hqR hRq hcr hgcont hgi hgm hgb hK hqg hreal hWc' hW0' hηr hsB hu hτc hτm hτ0 hτs
      hηrH hη hηinj hnoarc hlink'
  exact ⟨q, 0, R, _, g, β', γ, S₀, Sm, ηr, η, hqc, hq0, le_rfl, hqH, hqR, hRq, hcr, hgcont, hgi, hgf, hL, hβ',
    hβ'0, hS1, hγ, hγ0, hglift, hchain, hS₀Sm, hnoarc', hsBS₀, hwBc, hwB0, hη, hwhull, hηβ, hηH, hcap, hid1, hid2,
    hid3⟩

/-- **GEOM2's S2 record at one sample, with the link on a dense set of good times** (`isStageS2_of` with the link asked
only on a set `G ⊆ [0, sB]` dense in `[0, sB]`; at the other times it follows by continuity of the relative chart's
boundary map, of `ηr ∘ τ` and of `η`). -/
theorem isStageS2_of_dense (hcD : IsDomainChart (H \ Y) c) (hY : IsHPHull Y) (hB : IsHPHull B) (hYB : Y ⊆ B)
    (hg₀ : IsMapOut Y (fun z => c.1 z + (s₀ : ℂ))) {LY : ℂ → ℂ}
    (hLY : IsCanonicalDerivLog Y (fun z => c.1 z + (s₀ : ℂ)) LY) (hlift : EqOn c.2.2 (fun z => (LY z).im) (H \ Y))
    (hgc : ∀ q ∈ Hbar, Tendsto c.2.1 (𝓝[H] q) (𝓝 (gc q))) (hCc : ∀ q ∈ Hbar, ‖gc q - q‖ ≤ Cc)
    (hgΦ : ∀ p ∈ Hbar, Tendsto (Mo.hullChart B x₀).2.1 (𝓝[H] p) (𝓝 (gΦ p)))
    (hgΦf : ∀ z, (gΦ ⁻¹' {z} ∩ {w : ℂ | 0 ≤ w.im}).Finite)
    (hfree : ∀ x : ℝ, 0 < x → ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) (pullHull c B))
    (hnorm : ∃ e : ℝ → ℝ, (∀ x : ℝ, 0 < x → Tendsto (Mn.pullChart c (Mo.hullChart B x₀)).1 (𝓝[H] (x : ℂ))
      (𝓝 (e x : ℂ))) ∧ Tendsto e (𝓝[>] 0) (𝓝 0))
    {W : ℝ → ℝ} {ηr : ℝ → ℂ} {τ : ℝ → ℝ} {sB u : ℝ} {wB : ℝ → ℝ} {η : ℝ → ℂ}
    (hWc : Continuous W) (hW0 : W 0 = 0) (hηr : IsLoewnerTrace (fun r => -W r) ηr) (hsB : 0 < sB) (hu : 0 < u)
    (hτc : ContinuousOn τ (Icc 0 sB)) (hτm : StrictMonoOn τ (Icc 0 sB)) (hτ0 : τ 0 = 0) (hτs : τ sB = u)
    (hηrH : ∀ r ∈ Icc (0 : ℝ) sB, 0 ≤ (ηr (τ r)).im)
    (hwBc : Continuous wB) (hwB0 : wB 0 = 0) (hη : IsLoewnerTrace (fun r => -wB r) η)
    (hηinj : InjOn η (Icc 0 sB)) (hnoarc : interior {r ∈ Ioo (0 : ℝ) sB | (η r).im = 0} = ∅) (hηH : η sB ∈ H)
    {G : Set ℝ} (hGs : G ⊆ Icc 0 sB) (hGd : Icc (0 : ℝ) sB ⊆ closure G)
    (hlink : ∀ r ∈ G,
      Tendsto (Lf.reflChart (Mn.pullChart c (Mo.hullChart B x₀))).2.1 (𝓝[H] (ηr (τ r))) (𝓝 (η r))) :
    Om.IsStageS2 c (Mo.hullChart B x₀) B wB sB W u := by
  obtain ⟨-, -, g, -, -, -, -, -, -, hgcont, -, -, -, -, -, -, hgt, -, -, -, -⟩ :=
    stageChartPkg hcD hY hB hYB hg₀ hLY hlift hgc hCc hgΦ hgΦf hfree hnorm
  have hτ0' : ∀ r ∈ Icc (0 : ℝ) sB, 0 ≤ τ r := fun r hr => by
    rw [← hτ0]; exact hτm.monotoneOn ⟨le_rfl, hsB.le⟩ hr hr.1
  have hF : ContinuousOn (fun r => g (ηr (τ r))) (Icc 0 sB) := by
    refine hgcont.comp ((hηr.2.1.comp hτc fun r hr => hτ0' r hr)) fun r hr => hηrH r hr
  have hη' : ContinuousOn η (Icc 0 sB) := hη.2.1.mono fun r hr => hr.1
  have hG : EqOn (fun r => g (ηr (τ r))) η G := fun r hr => by
    have hp : ηr (τ r) ∈ Hbar := hηrH r (hGs hr)
    have : (𝓝[H] (ηr (τ r))).NeBot := GW1P.neBot_nhdsWithin_H hp
    exact tendsto_nhds_unique (hgt _ hp) (hlink r hr)
  have heq := hG.of_subset_closure hF hη' hGs hGd
  refine isStageS2_of hcD hY hB hYB hg₀ hLY hlift hgc hCc hgΦ hgΦf hfree hnorm hWc hW0 hηr hsB hu hτc hτm hτ0
    hτs hηrH hwBc hwB0 hη hηinj hnoarc hηH fun r hr => ?_
  have h := hgt _ (hηrH r hr)
  rwa [show g (ηr (τ r)) = η r from heq hr] at h

end InteractingSLE.Theorem14.SB.Sx
