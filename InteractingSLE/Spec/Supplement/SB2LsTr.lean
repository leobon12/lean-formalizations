/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LsHit

/-!
# Transfer of the new record between two launches

Packet PROVE-T14-SB2LIFT (round 9; (L3) of handoff §R5.2 reduced to a correspondence of physical sets). Two launches,
the actual one and the relative one of SB2(2)'s lifted walk, decide their new right records from their aliveness
beyond the old records. By `lRecR_run_eq` both are "off a set" (the closure of the new filled prefix). This file
transfers the record:

* `map_sSup_insert`: an increasing map continuous on `[R, ∞)` commutes with `sSup (insert a S)`, for `S` bounded above
  and beyond `a ≥ R`;
* **`lRecR_corr`**: assume
  - the actual and the relative launch characterize aliveness beyond their records by sets `F₁`, `F₂`;
  - `ι` is strictly increasing and continuous on `[R, ∞)` with `recR₂ = ι recR₁` and `R ≤ recR₁`;
  - every relative point beyond `recR₂` is an `ι`-image of an actual point beyond `recR₁`;
  - `x ∈ F₁ ↔ ι x ∈ F₂` beyond `recR₁`;
  - the actual hit set is bounded above.

  Then `lRecR s₂ ⊤ d₂ = ι (lRecR s₁ ⊤ d₁)`. This is `SB2LkCorr.launch_corr`'s record hypothesis `hrec'` (with `p` at
  most the actual record).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw

/-- **An increasing continuous map commutes with `sSup (insert a S)`.** -/
theorem map_sSup_insert {ι : ℝ → ℝ} {R a : ℝ} {S : Set ℝ} (hmono : MonotoneOn ι (Ici R))
    (hcont : ContinuousOn ι (Ici R)) (ha : R ≤ a) (hS : ∀ x ∈ S, a < x) (hSb : BddAbove S) :
    ι (sSup (insert a S)) = sSup (insert (ι a) (ι '' S)) := by
  have hA : insert a S ⊆ Ici R := by
    rintro x (rfl | hx)
    · exact ha
    · exact ha.trans (hS x hx).le
  have hAb : BddAbove (insert a S) := hSb.insert a
  have hsup : R ≤ sSup (insert a S) := ha.trans (le_csSup hAb (mem_insert a S))
  have hc : ContinuousWithinAt ι (insert a S) (sSup (insert a S)) :=
    (hcont _ hsup).mono hA
  rw [(hmono.mono hA).map_csSup_of_continuousWithinAt hc (insert_nonempty a S) hAb, image_insert_eq]

/-- **The new record transfers through `ι`.** -/
theorem lRecR_corr {s₁ s₂ : ExplState} {d₁ d₂ : (ℝ≥0 → ℝ) × ℝ≥0∞} {F₁ F₂ : Set ℂ} {ι : ℝ → ℝ} {R : ℝ}
    (hmono : StrictMonoOn ι (Ici R)) (hcont : ContinuousOn ι (Ici R)) (hR : R ≤ stRecR s₁)
    (hrec : stRecR s₂ = ι (stRecR s₁))
    (h₁ : ∀ x : ℝ, stRecR s₁ < x → (lAlive (stChart s₁) ⊤ d₁ x ↔ (x : ℂ) ∉ F₁))
    (h₂ : ∀ y : ℝ, stRecR s₂ < y → (lAlive (stChart s₂) ⊤ d₂ y ↔ (y : ℂ) ∉ F₂))
    (hsurj : ∀ y : ℝ, stRecR s₂ < y → ∃ x, stRecR s₁ < x ∧ ι x = y)
    (hF : ∀ x : ℝ, stRecR s₁ < x → ((x : ℂ) ∈ F₁ ↔ ((ι x : ℝ) : ℂ) ∈ F₂))
    (hbdd : BddAbove {x : ℝ | stRecR s₁ < x ∧ (x : ℂ) ∈ F₁}) :
    lRecR s₂ ⊤ d₂ = ι (lRecR s₁ ⊤ d₁) := by
  rw [lRecR_eq_of_alive_iff h₁, lRecR_eq_of_alive_iff h₂]
  have hset : {y : ℝ | stRecR s₂ < y ∧ (y : ℂ) ∈ F₂} = ι '' {x : ℝ | stRecR s₁ < x ∧ (x : ℂ) ∈ F₁} := by
    ext y
    constructor
    · rintro ⟨hy, hyF⟩
      obtain ⟨x, hx, rfl⟩ := hsurj y hy
      exact ⟨x, ⟨hx, (hF x hx).2 hyF⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hxF⟩, rfl⟩
      refine ⟨?_, (hF x hx).1 hxF⟩
      rw [hrec]
      exact hmono (mem_Ici.2 hR) (mem_Ici.2 (hR.trans hx.le)) hx
  rw [hset, hrec]
  exact (map_sSup_insert hmono.monotoneOn hcont hR (fun x hx => hx.1) hbdd).symm

end InteractingSLE.Theorem14.SB.Lk
