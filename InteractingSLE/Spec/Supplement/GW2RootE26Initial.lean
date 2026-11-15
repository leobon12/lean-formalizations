/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootE26Actual
import InteractingSLE.Spec.Supplement.GW2RootE26Prefix
import InteractingSLE.Spec.Supplement.GW2RootD25Initial

/-!
# Actual initial gates from the original source hypotheses

Packet PROVE-T14-GW2ROOT2. The raw reader is measurable in the exact
retained root records on every sample. On the protected initial source
event it equals the physical `S < q < F` observation, simultaneously
at all queries through the recording endpoint.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootE26

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric RootC24 RootD25 Supp8.GB6

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Both actual observation gates are measurable in the literal initial
retained sigma algebra, including exceptional samples and endpoint queries. -/
theorem measurable_initial_cutoffObservationRead (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (F q : ℝ≥0) :
    Measurable[c.sigma r []] (fun ω =>
      cutoffObservationRead (2 ^ r.2) c.s (rootEntry r.1).2 F q
        (cfRec c.s c.W c.ζ ω,
          stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 []) 0 ω)) :=
  measurable_rootSigma_cutoffObservationRead c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ r []
    ⟨0, by simp only [entryList, List.map_nil, List.length_nil]; omega⟩
    (2 ^ r.2) (rootEntry r.1).2 F q

variable [StandardBorelSpace Ω]

/-- The Borel reader is the actual initial experiment observation under
the original source hypotheses; its first-entry gate is a conclusion. -/
theorem ae_initial_cutoffObservationRead_eq_actual (h13 : Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (hroot : rootPt r.1 = 0) :
    let a : ℝ≥0 := 2 ^ r.2
    let v := (rootEntry r.1).2
    let E := canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec 0 [rootEntry r.1]) 0
    let γ := GW2aSingle.chosenTrace (fun t ω => (E ω).1 t) (fun ω => (E ω).2)
    ∀ᵐ ω ∂c.P, c.α ω c.s ∈ H → (v : ℝ≥0∞) < min
      (firstContactTime (fun q => sphereInv (γ ω q : OnePoint ℂ))
        ((fun q => (c.α ω q : OnePoint ℂ)) '' Icc 0 c.s)) (E ω).2 →
      let p := (cfRec c.s c.W c.ζ ω,
        stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 []) 0 ω)
      ∀ F q : ℝ≥0, q ≤ v → cutoffObservationRead a c.s v F q p =
        if entryPhysical a c.s v p < q ∧ q < F then
          physicalObservationRead a c.s v q p else (0, 0) := by
  have hfirst := RootZ21.ae_capR_nil_eq_forwardCapacity
    c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s c.P h13 c.hβA
    c.hb c.hc₀J c.hc₀ c.hh c.hcf c.hζ c.α c.hα r hroot
  dsimp only at hfirst ⊢
  filter_upwards [hfirst, GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ,
    c.hζ, c.hα] with ω hf hr hζω hαω
  intro hsH hv F q hq
  obtain ⟨_, _, hW, hW0, _⟩ := hr
  have hαζ : IsGeneratingTrace (c.W · ω) (c.ζ ω) (c.α ω) := by rwa [hζω]
  have ha : 0 < (2 : ℝ≥0) ^ r.2 := by positivity
  have he := isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ 0
    (specAngle (schedSpec 0 [rootEntry r.1])) (specDelta (schedSpec 0 [rootEntry r.1]))
    (c.h ω) 0
  rw [RootA22.initial_stopRec_eq c.hκ c.h12p c.βA c.c₀ c.h r hroot ω]
  exact cutoffObservationRead_eq_actual c.W c.ζ ω hαζ hW hW0 hζω hsH he hf.1 hv ha hq F

/-- Initial gated observations through any smaller protected recording
cutoff agree with the literal source record, including the smaller endpoint. -/
theorem ae_initial_cutoffObservationRead_prefix_eq (h13 : Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (hroot : rootPt r.1 = 0) :
    let a : ℝ≥0 := 2 ^ r.2
    let v := (rootEntry r.1).2
    let E := canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec 0 [rootEntry r.1]) 0
    let γ := GW2aSingle.chosenTrace (fun t ω => (E ω).1 t) (fun ω => (E ω).2)
    ∀ᵐ ω ∂c.P, c.α ω c.s ∈ H → (v : ℝ≥0∞) < min
      (firstContactTime (fun q => sphereInv (γ ω q : OnePoint ℂ))
        ((fun q => (c.α ω q : OnePoint ℂ)) '' Icc 0 c.s)) (E ω).2 →
      ∀ V q F : ℝ≥0, q ≤ V → V ≤ v →
        cutoffObservationRead a c.s V F q
            (cfRec c.s c.W c.ζ ω, recOf (V : ℝ≥0∞) (E ω)) =
          cutoffObservationRead a c.s v F q (cfRec c.s c.W c.ζ ω,
            stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 []) 0 ω) := by
  have hfirst := RootZ21.ae_capR_nil_eq_forwardCapacity
    c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s c.P h13 c.hβA
    c.hb c.hc₀J c.hc₀ c.hh c.hcf c.hζ c.α c.hα r hroot
  dsimp only at hfirst ⊢
  filter_upwards [hfirst, GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ,
    c.hζ, c.hα] with ω hf hr hζω hαω
  intro hsH hv V q F hq hV
  obtain ⟨_, _, hW, hW0, _⟩ := hr
  have hαζ : IsGeneratingTrace (c.W · ω) (c.ζ ω) (c.α ω) := by rwa [hζω]
  have hs : (c.s : ℝ≥0∞) < c.ζ ω := by rw [hζω]; exact ENNReal.coe_lt_top
  have ha : 0 < (2 : ℝ≥0) ^ r.2 := by positivity
  have he := isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ 0
    (specAngle (schedSpec 0 [rootEntry r.1])) (specDelta (schedSpec 0 [rootEntry r.1]))
    (c.h ω) 0
  rw [RootA22.initial_stopRec_eq c.hκ c.h12p c.βA c.c₀ c.h r hroot ω]
  exact cutoffObservationRead_prefix_eq c.W c.ζ ω hαζ hW.continuousOn hW0 hs hsH
    he hf.1 hv ha hq hV F

end InteractingSLE.Theorem14.GW2TipSystem.RootE26
