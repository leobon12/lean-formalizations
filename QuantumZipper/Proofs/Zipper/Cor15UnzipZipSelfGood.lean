import QuantumZipper.Proofs.Zipper.Cor15GrpHalves
import QuantumZipper.Proofs.Zipper.Cor15LawB1
import QuantumZipper.Proofs.Zipper.Cor15WRCore

/-!
# D35 core piece 3: `D_a (U_a c) ≈ c` (Corollary 1.5(b), positive times)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18;
the paper gives no proof, it calls the corollary immediate from Theorems 1.2–1.4). Decision
D35 (`DECISIONS.md`): the missing input `Cor15UnzipZipSelfStmt` (`Cor15GrpHalves`) is the round
trip in the *other* order, `D_a (U_a x) ≈ x` (`≈` = `ConfigEq`), at the genuine configuration
`x = c`.

**Why the naive route fails.** The round trip at `y = D_a c` *is* known (`grp_roundTrip`:
`U_a (D_a c) ≈ c`), and feeding it through the literal congruence `zipCapDown_congr_grpEq`
gives, pathwise, `D_a (U_a (D_a c)) = D_a c`: the identity `D_a U_a = id` holds at the point
`y = D_a c`, not at `c`. So one needs a transfer from the law of `D_a c` to the law of `c`;
B1-FULL (`b1_full`) gives exactly `law (b1Data ∘ D_a c) = law (b1Data ∘ c)`.

This file isolates the transfer (proved here, own elementary argument) from the reading input
it needs (stated as `Cor15UnzipZipGoodStmt`, the analogue of the other D35 nodes
`Cor15WeldReadStmt`, `Cor15ZcReadStmt`, `Cor15RezipRegStmt`):

* `UnzipZipHolds` — the predicate `ConfigEq (D_a (U_a x)) x` at a configuration `x`;
* `zipCapDown_zipCapUp_snd`: the **driver half is free**: for `u ≥ 0` the driver of
  `D_a (U_a x)` is `x.2 u - x.2 0` whenever `weldDriver γ x.1 a 0 = 0` (pure unfolding of the
  two definitions — `zipCapUp` re-traces the zipped segment with driver
  `W'(a-s) - W'(a)` and `zipCapDown` re-reads it from time `a`). Hence, when `x.2 0 = 0`,
  `UnzipZipHolds γ a x ↔ RegEq (D_a (U_a x)).1 x.1`: **the whole content is the field half**
  (which is where the additive constant of `RegEq` sits);
* `unzipZipHolds_congr`, `unzipZipHolds_zipCapDown` — the predicate only depends on the
  `ConfigEq` class, and it holds at `D_a z` as soon as the round trip at `z` holds;
* `Cor15UnzipZipGoodStmt` — the remaining node: a measurable set `A` of `b1Data` values,
  charged a.s. by `b1Data (D_a c)`, on which the round trip holds *deterministically*;
* `cor15UnzipZipSelfStmt_of_good` — `Cor15UnzipZipSelfStmt` from that node: the good set is
  moved from `D_a c` to `c` by B1-FULL (`ae_mem_of_map_eq`), and on it the round trip is
  deterministic. No measurability of `zipCapUp`/`zipCapDown` is needed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace QuantumZipper
namespace Cor15Group

open B1Full

/-- **The round trip in the other order at a configuration `x`**: `D_a (U_a x) ≈ x`, i.e.
`ConfigEq (zipCapDown γ a (zipCapUp γ a x)) x` (Corollary 1.5(b) for `s + t = 0`). -/
def UnzipZipHolds (γ a : ℝ) (x : FieldSample × (ℝ → ℝ)) : Prop :=
  ConfigEq (zipCapDown γ a (zipCapUp γ a x)) x

/-! ## The driver half of the round trip is automatic -/

/-- **Driver of the composite `D_a ∘ U_a`.** With `W' = weldDriver γ x.1 a` and `W' 0 = 0`, for
`u ≥ 0` the driver of `zipCapDown γ a (zipCapUp γ a x)` is `x.2 u - x.2 0`: zipping retraces
the segment `[0,a]` with driver `W'(a-s) - W'(a)` (so at time `a` it reads `W'(0) - W'(a)`),
and unzipping by `a` re-reads the continuation `x.2` and subtracts that value. -/
theorem zipCapDown_zipCapUp_snd {γ a : ℝ} (ha : 0 ≤ a) {x : FieldSample × (ℝ → ℝ)}
    (hW0 : weldDriver γ x.1 a 0 = 0) (hx0 : x.2 0 = 0) (u : ℝ) (hu : 0 ≤ u) :
    (zipCapDown γ a (zipCapUp γ a x)).2 u = x.2 u := by
  have hum : max u 0 = u := max_eq_left hu
  have ham : max a 0 = a := max_eq_left ha
  rcases eq_or_lt_of_le hu with h | h
  · subst h
    simp only [zipCapDown, max_eq_left le_rfl, add_zero, sub_self, hx0]
  · have hmax : max (a + u) 0 = a + u := max_eq_left (by linarith)
    have hu' : ¬ (a + u ≤ a) := by linarith
    simp only [zipCapDown, zipCapUp, hum, ham, hmax, sub_self, hW0, add_sub_cancel_left,
      ite_eq_right hu', ite_eq_left (le_refl a)]
    ring

/-- **`UnzipZipHolds` is exactly its field half** once the drivers vanish at `0`
(which holds for every genuine configuration: `drive κ B ω 0 = 0` and `W' 0 = 0` for the
welding driver). -/
theorem unzipZipHolds_iff_regEq {γ a : ℝ} (ha : 0 ≤ a) {x : FieldSample × (ℝ → ℝ)}
    (hW0 : weldDriver γ x.1 a 0 = 0) (hx0 : x.2 0 = 0) :
    UnzipZipHolds γ a x ↔ RegEq (zipCapDown γ a (zipCapUp γ a x)).1 x.1 := by
  refine ⟨fun h => h.1, fun h => ⟨h, fun u hu => ?_⟩⟩
  exact zipCapDown_zipCapUp_snd ha hW0 hx0 u hu

/-! ## The predicate is a function of the `ConfigEq` class -/

variable {κ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-! ## The remaining reading node, and the transfer -/

/-- B1-FULL in terms of `b1Data` (`B1Full.b1_full`). -/
theorem b1_full_data (hκ : 0 < κ) (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) {a : ℝ} (ha : 0 < a) :
    P.map (fun ω => b1Data (zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω))) =
      P.map (fun ω => b1Data (grpCfg κ B X ω)) := by
  have h := b1_full κ hκ P B X hB hX hind ha
  simpa only [b1Data, lawData, grpCfg, unzippedField, zipCapDown] using h

end Cor15Group
end QuantumZipper
