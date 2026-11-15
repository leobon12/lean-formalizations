/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NeEnd

/-!
# The stage law in version form: the separable piece for PROVE-GW2-NEARIMG2 (D69)

Packet PROVE-GW2-RELDET (round 36, decision D64; the split of D69). `GW2Bh.StageLawXStatement` asks, at a good sample
of a successful history, for one canonical relative driver `Wc` (continuous from `0`, equal to the versions below their
caps, with a generating trace living to the root-`x` relative life, and with the clock bounded before the root-`x`
contact). At one sample the explored curve is transient: the capped candidate is frozen after its cap or its death.
* **No contact.** NEARIMG2's `GW2Ni.exists_canon_of_noContact` gives the driver.
* **A finite first contact away from the retained tip `α s`.** This is **`CanonContactStatement`** below, the
  deterministic analogue of `exists_canon_of_noContact` at the contact. The relative trace converges as `t → τ`
  (the contact point is a boundary point of the retained complement other than the tip, so the cluster-set argument
  of `tendsto_relBdry_of_transient` applies there), the clock is bounded before `τ`, and the glued driver frozen at
  the relative life is the canonical driver. NEARIMG2 proves it (D69); RELDET consumes it as stated.
* **A first contact at the retained tip.** This must be excluded almost surely (RELDET's).

* **`CanonContactStatement`** (named input; PROVE-GW2-NEARIMG2 proves it, D69).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw Restart Supp8.GB6 GW2TipSystem GW2Rz

/-- **The canonical relative driver with a first contact away from the retained tip** (one sample; for
PROVE-GW2-NEARIMG2, D69). The setting is that of `GW2Ni.exists_canon_of_noContact`, with a finite first root-`x`
contact `τ` at a point other than the retained tip. The conclusion is that of `exists_canon_of_noContact`, read
before `τ`: a continuous driver from `0` generating the re-centred relative hulls at every clock value before `τ`,
with a generating trace living to the root-`x` relative life, and the clock bounded before `τ`. -/
def CanonContactStatement : Prop :=
  ∀ {Ω : Type u} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) {α : ℝ≥0 → ℂ},
    IsGeneratingTrace (W · ω) ⊤ α → Continuous (W · ω) → W 0 ω = 0 → ζ ω = ⊤ →
    ∀ {s : ℝ≥0}, 0 < s → ∀ {x : ℝ}, 0 ≤ x → (∀ u ∈ Icc 0 s, x * ‖α u‖ < 1) →
    ∀ {w : ℝ≥0 → ℝ}, Continuous w → w 0 = 0 → ∀ {γ : ℝ≥0 → ℂ}, IsGeneratingTrace w ⊤ γ → α s ≠ 0 →
    ∀ τ : ℝ≥0, firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
        ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) = (τ : ℝ≥0∞) →
    sphereInv (((x : ℂ) + γ τ : ℂ) : OnePoint ℂ) ≠ ((α s : ℂ) : OnePoint ℂ) →
    ∃ Wc : ℝ≥0 → ℝ, Continuous Wc ∧ Wc 0 = 0 ∧
      (∀ t : ℝ≥0, t < τ → fwdHull (fun q : ℝ => Wc q.toNNReal) (GW2Ni.gClk x s (cfRec s W ζ ω) w t) =
        (fun z : ℂ => z + ((-GW2Bf.relBase x s (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤)) : ℝ) : ℂ)) ''
          RootH29.forwardHull x s t (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤))) ∧
      (∃ (ζc : ℝ≥0∞) (ηc : ℝ≥0 → ℂ), IsGeneratingTrace Wc ζc ηc ∧
        ENNReal.ofReal (GW2Bh.contactLifeX x s (cfRec s W ζ ω) w γ α) ≤ ζc) ∧
      ∃ M : ℝ, ∀ t : ℝ≥0, t < τ → GW2Ni.gClk x s (cfRec s W ζ ω) w t ≤ M

end InteractingSLE.Theorem14.GW2Rd
