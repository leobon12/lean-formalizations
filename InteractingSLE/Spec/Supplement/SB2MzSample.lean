/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MzGlue

/-!
# The identification of `EL`'s stage with the canonical stage at one sample

Packet PROVE-SB2-LCMEAN, round 15 (item 4: identification with `EL`). At one sample, let `Y` be the retained union,
`cℓ` B's stage chart, `c` the upper launch chart, `c₁` the relative run chart, `m` the relative shift, and let the
canonical chart be the hull chart of `fill Y` with an offset `x₀`. Suppose:

* the physical relative chart `Mo.physRelChart c c₁ m` is a domain chart of `ℍ ∖ fill Y` (`Mq.StageChainAtP`), and its
  stage-coordinate version `Mn.stageRelChart cℓ c c₁ m` one of `ℍ ∖ stageRetained cℓ Y` (`Mn.StageChainAtR2`);
* `c`, `c₁` are normalized and `cℓ` is conformal;
* `stageRetained cℓ Y` is filled;
* `EL`'s stage driver and the canonical driver both have the chain clause (`Mx.ChainFor`) for B's piece, in the
  respective stage charts, with positive lifetimes.

Then the two drivers agree before their common lifetime, and the canonical chart agrees with the physical relative
chart on `ℍ ∖ fill Y` (forward map and lift):

* **`ident_at_sample`**.

All statements are deterministic (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Mz

open Mx

/-- **The identification of `EL`'s stage with the canonical stage at one sample.** -/
theorem ident_at_sample {cℓ c c₁ : Chart} {m : ℝ} {Y : Set ℂ} (hY : IsHPHull (fillH Y))
    (hcN : WalkIntCanon.IsNormalized c) (hc₁N : WalkIntCanon.IsNormalized c₁) (hcℓ : cℓ.IsConformal)
    (hP : IsDomainChart (H \ fillH Y) (Mo.physRelChart c c₁ m))
    (hdR : IsDomainChart (H \ Mn.stageRetained cℓ Y) (Mn.stageRelChart cℓ c c₁ m))
    (hfill : ∀ z ∈ H \ Mn.stageRetained cℓ Y, z ∉ fillH (Mn.stageRetained cℓ Y)) {β' : ℝ≥0 → ℂ} {BL : ℝ≥0∞}
    {x₀ : ℝ} {e D : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hR : ChainFor (Mn.stageRetained cℓ Y) (Mn.stageRelChart cℓ c c₁ m) β' BL e)
    (hC : ChainFor (Mn.stageRetained cℓ Y) (stageChartOf cℓ (Mo.hullChart (fillH Y) x₀)) β' BL D)
    (he : e.2 ≠ 0) (hD : D.2 ≠ 0) :
    e.2 = D.2 ∧ (∀ t : ℝ≥0, (t : ℝ≥0∞) < e.2 → e.1 t = D.1 t) ∧
      EqOn (Mo.hullChart (fillH Y) x₀).1 (Mo.physRelChart c c₁ m).1 (H \ fillH Y) ∧
      EqOn (Mo.hullChart (fillH Y) x₀).2.2 (Mo.physRelChart c c₁ m).2.2 (H \ fillH Y) := by
  obtain ⟨d, hfwd, hlift⟩ := hullChart_eq_add_of_physRelChart hY hcN hc₁N m hP x₀
  have hcℓ' : ∀ w ∈ H \ Mn.stageRetained cℓ Y, cℓ.2.1 w ∈ H \ fillH Y :=
    fun w hw => mem_diff_of_notMem_stageRetained hcℓ hw
  have hdR' : IsDomainChart (H \ Mn.stageRetained cℓ Y) (stageChartOf cℓ (Mo.physRelChart c c₁ m)) := by
    rw [← stageRelChart_eq_stageChartOf]
    exact hdR
  obtain ⟨hdC, hfwd'⟩ := stageChartOf_translate (Mo.isDomainChart_hullChart hY x₀) hP hfwd hlift hcℓ' hdR'
  obtain ⟨hd0, hlife, hagree⟩ := ident_of_chainFor hdR hdC hfill (fun z hz => by
    rw [hfwd' z hz, stageRelChart_eq_stageChartOf]) hR hC he hD
  subst hd0
  refine ⟨hlife, hagree, fun z hz => ?_, hlift⟩
  rw [hfwd z hz]
  push_cast
  ring

end InteractingSLE.Theorem14.SB.Mz
