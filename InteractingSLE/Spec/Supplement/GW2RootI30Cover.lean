/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootI30Initial

/-!
# The actual low-arc cover supplies the relative clock

Packet PROVE-T14-GW2ROOT2. Theorem 1.3 and the original source setup
prove strict continuous capacity growth, positivity and the literal
initial normalized-capacity identity on every cover event. A continuous
relative driver realizes the actual image hulls throughout that prefix.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootI30

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart RootC24 Supp8.GB6

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- Every low-arc cover event has its actual strict continuous relative
capacity clock, literal initial capacity, and a continuous image driver. -/
theorem ae_cover_clock (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) :
    let v := (rootEntry r.1).2
    ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c r →
      let p := RootCv.rootRecs c r.1 ω
      let a := fun t => RootH29.forwardCapacity (rootPt r.1) c.s t p
      a 0 = 0 ∧ StrictMonoOn a (Icc 0 v) ∧ ContinuousOn a (Icc 0 v) ∧
      0 < a v ∧
      capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r [] ω = 4 ^ r.2 * a v ∧
      ∃ V : ℝ → ℝ, Continuous V ∧ ∀ t ∈ Icc 0 v,
        fwdHull V (a t) = RootH29.forwardHull (rootPt r.1) c.s t p := by
  intro v
  filter_upwards [RootCv.ae_coverEvent_spec h13 c r, c.hα,
    GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ, c.hζ]
    with ω hcover hα hreg hζ hω
  obtain ⟨hseed, hsH, hγ, _, hv, harc⟩ := hcover hω
  obtain ⟨_, _, hW, hW0, _⟩ := hreg
  have hs : 0 < c.s := by
    by_contra hn
    have hs0 : c.s = 0 := le_antisymm (not_lt.mp hn) zero_le
    exact ne_zero_of_mem_H hsH (by rw [hs0]; exact hα.1)
  let E := canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 []) 0 ω
  have he : IsRegularDriver E := isRegularDriver_canonFam c.hκ c.h12p c.βA c.c₀
    (specAngle (schedSpecOf r.1 [])) (specDelta (schedSpecOf r.1 []))
    (rootPt r.1) c.h 0 ω
  obtain ⟨V, hV, h0, hm, hc, hK⟩ := exists_reader_chain c.W c.ζ ω hα hW hW0 hζ hs
    (RootH29.rootPt_nonneg_of_seedOK c hseed) harc he hγ hv
  have hcap := capR_nil_eq_reader c r ω hseed hα hW hW0 hζ hs hγ harc hv
  have hp : RootCv.rootRecs c r.1 ω = (cfRec c.s c.W c.ζ ω, recOf (v : ℝ≥0∞) E) :=
    Prod.ext rfl (RootCv.stopRec_root_eq c r.1 ω)
  dsimp only
  rw [hp] at hcap ⊢
  refine ⟨h0, hm, hc, ?_, hcap, V, hV, fun t ht => (hK t ht).2.1⟩
  have hv0 : 0 < v := c.hQpos r.1.2.2 r.1.2.2.property
  have hh := hm (show (0 : ℝ≥0) ∈ Icc 0 v from ⟨zero_le, zero_le⟩)
    (show v ∈ Icc 0 v from ⟨zero_le, le_rfl⟩) hv0
  simpa only [h0] using hh

/-- Literal initial normalized capacity is positive on each actual cover event. -/
theorem ae_cover_capR_pos (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c r →
      0 < capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r [] ω := by
  filter_upwards [ae_cover_clock h13 c r] with ω hω hcover
  obtain ⟨_, _, _, hpos, hcap, _⟩ := hω hcover
  rw [hcap]
  exact mul_pos (pow_pos (by norm_num) _) hpos

end InteractingSLE.Theorem14.GW2TipSystem.RootI30
