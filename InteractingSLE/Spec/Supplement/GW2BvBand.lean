/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BvClause
import InteractingSLE.Spec.Supplement.GW2BuReachX
import InteractingSLE.Spec.Supplement.GW2RwStart

/-!
# The start band and the dilation's scale condition on alive histories

Packet PROVE-GW2-BUF (round 19; clause (iii)). On J32's alive histories the history start is in `(−9/4, −7/4)`
off the root and `0` at the root (`GW2Rw.ae_histStart_mem_of_alive`, `GW2Bf.histStart_nil`). So it is below
`2 + 1/8`, and the near dilation satisfies ruling R112's scale condition (`GW2Sdh.nearLam_scale`). These are the
premises of `ae_reach_of_visit_instX`.

* **`ae_startBand`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open GW2TipSystem GW2TipSystem.RootC24

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The start band on alive histories.** -/
theorem ae_startBand (h13 : Exist.Theorem13Statement.{u}) (gap : RootCv.GapFamily.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    ∀ᵐ ξ ∂c.P, ξ ∈ ((GW2Sdz.J32S gap Ω c).experiment r).data.alive ((GW2Sdz.J32S gap Ω c).G r) l →
      GW2Bf.histStart c r l ξ < 2 + 1 / 8 ∧
        (lamL l : ℝ) * (2 + 1 / 8 - GW2Bf.histStart c r l ξ) ≤ 2 + 1 / 8 := by
  filter_upwards [GW2Rw.ae_histStart_mem_of_alive h13 c r] with ξ hband halive
  have halive32 := GW2Sdz.alive_scaled_subset gap Ω c r l halive
  have hS : (l.length ≠ 0 → -(9 / 4) ≤ GW2Bf.histStart c r l ξ) ∧ (l.length = 0 → 0 ≤ GW2Bf.histStart c r l ξ) ∧
      GW2Bf.histStart c r l ξ < 2 + 1 / 8 := by
    cases l with
    | nil =>
      rw [GW2Bf.histStart_nil]
      refine ⟨fun h => absurd rfl h, fun _ => le_rfl, by norm_num⟩
    | cons x l' =>
      have hb := hband x l' halive32
      refine ⟨fun _ => hb.1.le, fun h => absurd h (List.cons_ne_nil x l' ∘ List.length_eq_zero_iff.1), ?_⟩
      linarith [hb.2]
  refine ⟨hS.2.2, ?_⟩
  have h := GW2Sdh.nearLam_scale Ω c r l ξ hS.1 hS.2.1
  rwa [nearLam_eq_lamL] at h

end InteractingSLE.Theorem14.GW2Bh
