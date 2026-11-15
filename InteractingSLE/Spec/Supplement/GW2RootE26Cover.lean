/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootE26Initial

/-!
# Small protected initial cutoffs belong to the original countable family

Packet PROVE-T14-GW2ROOT2. The canonical first driver is independent of
its prescribed cutoff. A live initial generating trace has a positive
pre-contact horizon, so density supplies arbitrarily small protected
cutoffs from the original set `Q`. No positive contact horizon is assumed.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootE26

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric RootC24 Supp8.GB6

/-- Prescribing a different first cutoff leaves the actual first canonical
driver and its lifetime unchanged, at every sample. -/
theorem canonical_first_independent_time {κ : ℝ} (hκ : 0 < κ)
    (h12p : Theorem12ParamStatement.{u}) (βA : BoundaryWord × ℝ × RecData → BoundaryWord)
    (c₀ : BoundaryWord) {Ω : Type u} (h : Ω → DistOn upperHalfPlaneOpens)
    (x θ : ℝ) (v V : ℝ≥0) (ω : Ω) :
    canonSpecFam hκ h12p βA c₀ h (schedSpec x [(θ, v)]) 0 ω =
      canonSpecFam hκ h12p βA c₀ h (schedSpec x [(θ, V)]) 0 ω := by
  rfl

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- Every live source initial zero-root piece admits arbitrarily small
protected prescribed cutoffs from the original `Q`, with the very same
canonical driver. This is the pre-contact part of the countable root cover. -/
theorem ae_initial_exists_protected_cutoff (h13 : Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (hroot : rootPt r.1 = 0) :
    let E := canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec 0 [rootEntry r.1]) 0
    let γ := GW2aSingle.chosenTrace (fun t ω => (E ω).1 t) (fun ω => (E ω).2)
    ∀ᵐ ω ∂c.P, 0 < (E ω).2 → ∀ δ : ℝ≥0, 0 < δ → ∃ q : c.Q,
      0 < (q : ℝ≥0) ∧ (q : ℝ≥0) < δ ∧
        canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h
          (schedSpec 0 [((rootEntry r.1).1, (q : ℝ≥0))]) 0 ω = E ω ∧
        ((q : ℝ≥0) : ℝ≥0∞) < min
          (firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
            ((fun t => (c.α ω t : OnePoint ℂ)) '' Icc 0 c.s)) (E ω).2 := by
  have hfirst := RootZ21.ae_capR_nil_eq_forwardCapacity
    c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s c.P h13 c.hβA
    c.hb c.hc₀J c.hc₀ c.hh c.hcf c.hζ c.α c.hα r hroot
  dsimp only at hfirst ⊢
  filter_upwards [hfirst, c.hα] with ω hf hαω
  intro hT δ hδ
  have hpos := RootJ16.precontact_horizon_pos hαω
    (show (c.s : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top) hf.1 hT
  obtain ⟨b, hb0, hb⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp
    (lt_min hpos (ENNReal.coe_pos.mpr hδ))
  obtain ⟨q, hq, hqQ⟩ := c.hQd.inter_open_nonempty (Ioo (0 : ℝ≥0) b) isOpen_Ioo
    (nonempty_Ioo.mpr (ENNReal.coe_pos.mp hb0))
  have hqb := (ENNReal.coe_lt_coe.mpr hq.2).trans hb
  refine ⟨⟨q, hqQ⟩, hq.1, ENNReal.coe_lt_coe.mp (hqb.trans_le (min_le_right _ _)), ?_,
    hqb.trans_le (min_le_left _ _)⟩
  exact canonical_first_independent_time c.hκ c.h12p c.βA c.c₀ c.h 0
    (rootEntry r.1).1 q (rootEntry r.1).2 ω

end InteractingSLE.Theorem14.GW2TipSystem.RootE26
