/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootH29Actual
import InteractingSLE.Spec.Supplement.GW2RootH29Record

/-!
# Low-arc physical experiment readers from the actual source setup

Packet PROVE-T14-GW2ROOT2. COVER and Theorem 1.3 supply every premise
of the translated physical reader's regularity. Its whole closed prefix
is continuous, starts at zero, ends in the open half-plane and has null
boundary occupation. Both the tip and translated hull capacity are
measurable in the literal stage-start sigma algebra at random own times.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootH29

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart RootC24 Supp8.GB6

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The low-arc physical tip reader is known at the actual root stage,
including at every stage-measurable random own time. -/
theorem measurable_initial_rootTipRead_random (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) {t : Ω → ℝ≥0} (ht : Measurable[c.sigma r []] t) :
    Measurable[c.sigma r []] fun ω =>
      rootTipRead (rootPt r.1) c.s (t ω) (RootCv.rootRecs c r.1 ω) :=
  @measurable_rootTipRead_random Ω (c.sigma r []) (rootPt r.1) c.s _
    (RootCv.measurable_rootRecs c r) t ht

/-- The translated physical hull capacity is observable at every
random own time using the same actual root records. -/
theorem measurable_initial_forwardCapacity_random (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) {t : Ω → ℝ≥0} (ht : Measurable[c.sigma r []] t) :
    Measurable[c.sigma r []] fun ω =>
      forwardCapacity (rootPt r.1) c.s (t ω) (RootCv.rootRecs c r.1 ω) :=
  @measurable_forwardCapacity_random Ω (c.sigma r []) (rootPt r.1) c.s _
    (RootCv.measurable_rootRecs c r) t ht

variable [StandardBorelSpace Ω]

/-- The actual low-arc cover supplies the physical experiment's full
tip regularity. In particular, positivity and closed-hull safety of the
root arc are proved from the source data, rather than supplied as inputs. -/
theorem ae_cover_rootTip_regular (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) :
    let v := (rootEntry r.1).2
    let E := canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 []) 0
    let γ := GW2aSingle.chosenTrace (fun t ω => (E ω).1 t) (fun ω => (E ω).2)
    ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c r →
      let p := RootCv.rootRecs c r.1 ω
      ContinuousOn (fun t => rootTipRead (rootPt r.1) c.s t p) (Icc 0 v) ∧
      rootTipRead (rootPt r.1) c.s 0 p = 0 ∧
      rootTipRead (rootPt r.1) c.s v p ∈ H ∧
      volume {t : ℝ | t ∈ Ioo 0 (v : ℝ) ∧
        rootTipRead (rootPt r.1) c.s t.toNNReal p ∉ H} = 0 ∧
      ∀ t ≤ v, rootTipRead (rootPt r.1) c.s t p ∈ H ↔ γ ω t ∈ H := by
  intro v E γ
  filter_upwards [RootCv.ae_coverEvent_spec h13 c r, c.hα,
    GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ, c.hζ]
    with ω hcover hα hreg hζ hω
  obtain ⟨hseed, _, hγ, htip, hv, harc⟩ := hcover hω
  obtain ⟨_, _, hW, hW0, _⟩ := hreg
  have hx := rootPt_nonneg_of_seedOK c hseed
  have he : IsRegularDriver (E ω) := isRegularDriver_canonFam c.hκ c.h12p c.βA c.c₀
    (specAngle (schedSpecOf r.1 [])) (specDelta (schedSpecOf r.1 []))
    (rootPt r.1) c.h 0 ω
  have hp : RootCv.rootRecs c r.1 ω = (cfRec c.s c.W c.ζ ω, recOf (v : ℝ≥0∞) (E ω)) :=
    Prod.ext rfl (RootCv.stopRec_root_eq c r.1 ω)
  dsimp only
  rw [hp]
  have hmem := fun t (ht : t ≤ v) =>
    rootTipRead_mem_H_iff c.W c.ζ ω hα hW hW0 hζ hx harc he hγ hv ht
  refine ⟨continuousOn_rootTipRead c.W c.ζ ω hα hW hW0 hζ hx harc he hγ hv, ?_,
    (hmem v le_rfl).mpr ?_,
    volume_rootTipRead_notMem_H c.W c.ζ ω hα hW hW0 hζ hx harc he hγ hv, hmem⟩
  · rw [rootTipRead_eq c.W c.ζ ω hα hW hW0 hζ hx harc he hγ hv zero_le,
      hγ.1, add_zero, sub_self]
  · change 0 < (γ ω v).im
    change 0 < ((rootPt r.1 : ℂ) + γ ω v).im at htip
    simpa only [Complex.add_im, Complex.ofReal_im, zero_add] using htip

end InteractingSLE.Theorem14.GW2TipSystem.RootH29
