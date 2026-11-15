/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BoStop
import InteractingSLE.Spec.Supplement.GW2RvPkg

/-!
# BUF's near stops at every root: `NearStopsX` PROVED (given the owners' instance inputs)

Packet PROVE-GW2-BUF (round 12). ROOTX's package `pkgX K` reads the near stop `(K Ω c r).nearStop l n m a` on
candidate `a`'s root-`x` instance of version `m`. `NearStopsX h13 ver ch K` asks that, at good roots on time-ordered
histories, these stops be `GoodX` eventually in `m`.

* **`nearStopPkgX E K₀`**: the base package `K₀` with the near stop replaced, at good roots, by `GW2BoStop.nearStopX`
  on the instance of version `m`. The lower cap is the previous version's cap `V (m − 1)`, read by that version's
  rule. The exit rule is `E Ω c r l n a` (any measurable path rule; D16's `shapeStop` for the near facts).
* **`nearStopsX_nearStopPkgX`**: `NearStopsX` for it, from the owners' `InstInputsX` (the instances are `GoodX`) and
  the version family's strict caps. ROOTX's `lowCapStopX_good_family` applies on the instance of version `k + 1`
  with the cap `V k`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId GW2TipSystem GW2TipSystem.RootC24 GW2Rd GW2Rz GW2Rv GW2Sde GW2Sdh

section Pkg

variable (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u}) (ch : SchedChoiceFamily.{u})

open Classical in
/-- **The base package with BUF's near stops at every root.** -/
def nearStopPkgX (E : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (_r : ScaledRootIdx c.Θ c.Q), List (EntryIdx c.Θ c.Q) → ℕ → ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞)
    (K₀ : PkgFamily.{u}) : PkgFamily.{u} := fun Ω _ _ c r =>
  { K₀ Ω c r with
    nearStop := fun l n m a =>
      if h : GoodRoot c r then
        nearStopX c r l (instX h13 ver ch Ω c r l a m h.1) (rootPt r.1) ((ver Ω c r l a).V (m - 1))
          ((ver Ω c r l a).isA h.1 (m - 1)).1.2.choose (E Ω c r l n a)
      else (K₀ Ω c r).nearStop l n m a }

variable {h13 ver ch}

/-- **`NearStopsX` for BUF's near stops** (given the owners' instance inputs and measurable exit path rules). -/
theorem nearStopsX_nearStopPkgX (hI : InstInputsX h13 ver ch)
    {E : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (_r : ScaledRootIdx c.Θ c.Q), List (EntryIdx c.Θ c.Q) → ℕ → ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)) (n a : ℕ), IsPathRule (E Ω c r l n a) ∧ Measurable (E Ω c r l n a))
    (K₀ : PkgFamily.{u}) : NearStopsX h13 ver ch (nearStopPkgX h13 ver ch E K₀) := by
  intro Ω _ _ c r l hTO h n
  refine eventually_atTop.2 ⟨1, fun m hm a => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  have hx := h.1
  set hA := (ver Ω c r l a).isA hx with hAdef
  have hIall : ∀ j, (slowInstX h13 c r l a hA (fun _ => ch Ω c r l a) j).GoodX c r l (rootPt r.1) := fun j =>
    hI.goodX hTO h a (j + 1)
  have hL := lowCapStopX_good_family h13 c r l a hA (fun _ => ch Ω c r l a) hx (ver Ω c r l a).mono
    (ver Ω c r l a).fin ((ver Ω c r l a).strict hx) hIall k
  have hgood : (instX h13 ver ch Ω c r l a (k + 1) h.1).GoodX c r l (rootPt r.1) := hI.goodX hTO h a (k + 1)
  have hstop : (nearStopPkgX h13 ver ch E K₀ Ω c r).nearStop l n (k + 1) a =
      nearStopX c r l (instX h13 ver ch Ω c r l a (k + 1) h.1) (rootPt r.1) ((ver Ω c r l a).V k)
        ((ver Ω c r l a).isA h.1 k).1.2.choose (E Ω c r l n a) := by
    simp only [nearStopPkgX, h, ↓reduceDIte, Nat.add_sub_cancel]
  rw [hstop]
  exact nearStopX_goodX hgood hL ((ver Ω c r l a).fin (k + 1)) (ae_of_all _ ((ver Ω c r l a).mono k))
    (hE Ω c r l n a).1 (hE Ω c r l n a).2

end Pkg

end InteractingSLE.Theorem14.GW2Bh
