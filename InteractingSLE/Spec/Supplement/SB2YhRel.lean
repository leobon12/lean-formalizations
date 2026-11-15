/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2YeHull
import InteractingSLE.Spec.Supplement.SB2JRight

/-!
# The relative chart's free line and offset normalization at a tail seed

Packet PROVE-T14-SB2LIFT (round 32; `IsStageS2` at a tail stage). Let `c` be a chart whose inverse has boundary limits
`gc` on `ℍ̄`, sending `(0, ∞)` into the free line `(R, ∞)` with `Re gc y → R⁺` as `y → 0⁺` (B's stage chart at its
seed `R`, `stage_seed_facts`), and let `X` be compact with every real point `≤ R`. Then for the canonical chart
`Φ = Mo.hullChart (fillH X) x₀`:

* **`free_pullHull`**: `(0, ∞)` is untouched by `pullHull c (fillH X)` (the hypothesis `hfree` of `Sx.isStageS2_of`);
* **`norm_pullChart`**: if `x₀` is the right entry value of `Φ` at `R` (NOJUMP's `IsRightEntryChart X (realMax X)
  ((Mo.hullChart (fillH X) 0).recenter x₀)` with `realMax X = R`), the relative chart `pullChart c Φ` has real
  boundary values on `(0, ∞)` tending to `0` at `0⁺` (the hypothesis `hnorm`).

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Sx

variable {c : Chart} {gc : ℂ → ℂ} {R : ℝ} {X : Set ℂ}

/-- **The free line `(0, ∞)` of the pulled-back retained hull.** -/
theorem free_pullHull (hgc : ∀ q ∈ Hbar, Tendsto c.2.1 (𝓝[H] q) (𝓝 (gc q)))
    (hpos : ∀ y : ℝ, 0 < y → ∃ x : ℝ, R < x ∧ gc (y : ℂ) = x) (hXc : IsCompact X)
    (hXR : ∀ y : ℝ, (y : ℂ) ∈ X → y ≤ R) :
    ∀ y : ℝ, 0 < y → ∃ ρ > 0, Disjoint (ball (y : ℂ) ρ) (pullHull c (fillH X)) := by
  intro y hy
  obtain ⟨x, hx, hgx⟩ := hpos y hy
  obtain ⟨ρ', hρ', hd⟩ := Lx.exists_ball_disjoint_fillH_right hXc fun y' hy' => lt_of_le_of_lt (hXR y' hy') hx
  have hlim := hgc (y : ℂ) (show (0 : ℝ) ≤ (y : ℂ).im by simp)
  rw [hgx] at hlim
  have hev : ∀ᶠ z in 𝓝[H] (y : ℂ), c.2.1 z ∈ ball (x : ℂ) ρ' := hlim (ball_mem_nhds _ hρ')
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhdsWithin_iff.1 hev
  refine ⟨ρ, hρ, disjoint_left.2 fun z hz hzD => ?_⟩
  have h1 : c.2.1 z ∈ ball (x : ℂ) ρ' := hsub ⟨hz, hzD.1⟩
  exact disjoint_left.1 hd h1 hzD.2

/-- **The offset normalization of the relative chart** from the right entry value of the canonical chart at `R`. -/
theorem norm_pullChart (hc : c.IsConformal) (hgc : ∀ q ∈ Hbar, Tendsto c.2.1 (𝓝[H] q) (𝓝 (gc q)))
    (hpos : ∀ y : ℝ, 0 < y → ∃ x : ℝ, R < x ∧ gc (y : ℂ) = x)
    (hre : Tendsto (fun y : ℝ => (gc (y : ℂ)).re) (𝓝[>] 0) (𝓝[>] R)) {Φ : Chart}
    (hent : ∃ eΦ : ℝ → ℝ, (∀ x : ℝ, R < x → Tendsto Φ.1 (𝓝[H] (x : ℂ)) (𝓝 (eΦ x : ℂ))) ∧
      Tendsto eΦ (𝓝[>] R) (𝓝 0)) :
    ∃ e : ℝ → ℝ, (∀ y : ℝ, 0 < y → Tendsto (Mn.pullChart c Φ).1 (𝓝[H] (y : ℂ)) (𝓝 (e y : ℂ))) ∧
      Tendsto e (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨eΦ, heΦ, heΦ0⟩ := hent
  refine ⟨fun y => eΦ (gc (y : ℂ)).re, fun y hy => ?_, heΦ0.comp hre⟩
  obtain ⟨x, hx, hgx⟩ := hpos y hy
  have hlim := hgc (y : ℂ) (show (0 : ℝ) ≤ (y : ℂ).im by simp)
  rw [hgx] at hlim
  have h1 : Tendsto c.2.1 (𝓝[H] (y : ℂ)) (𝓝[H] (x : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, eventually_nhdsWithin_of_forall fun z hz => hc.2.1 hz⟩
  have h2 := (heΦ x hx).comp h1
  show Tendsto (fun w => Φ.1 (c.2.1 w)) (𝓝[H] (y : ℂ)) (𝓝 (eΦ (gc (y : ℂ)).re : ℂ))
  rw [hgx, Complex.ofReal_re]
  exact h2

end InteractingSLE.Theorem14.SB.Sx
