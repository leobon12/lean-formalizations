/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootD25Regular
import InteractingSLE.Spec.Supplement.GW2RootC24Data

/-!
# Source construction of the initial normalized physical experiment

Packet PROVE-T14-GW2ROOT2. From exactly the source setup, construct the
actual stopped sample measurably, identify its lifetime with the literal
initial root capacity, and prove driver continuity, physical trace
continuity and zero physical boundary occupation before contact.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootD25

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric RootC24 Supp8.GB6

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The concrete initial sample is measurable in the original sample space,
at every sample, for every root. No geometric premise is required. -/
theorem measurable_initialSample (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    Measurable (fun ω => relativeSample (2 ^ r.2) c.s (rootEntry r.1).2
      (cfRec c.s c.W c.ζ ω,
        stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 []) 0 ω)) := by
  have hm := measurable_rootSigma_relativeSample c.hκ c.h12p c.βA c.c₀ c.h
    c.s c.W c.ζ r [] ⟨0, by simp only [entryList, List.map_nil, List.length_nil]; omega⟩
    (2 ^ r.2) (rootEntry r.1).2
  exact hm.mono (stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _) le_rfl

variable [StandardBorelSpace Ω]

/-- The original flow trace supplies all the regularity assertions for
the constructed physical observations on each protected zero-root prefix.
No relative clock, driver, sample reading or occupation input is assumed. -/
theorem ae_initial_physical_regular (h13 : Theorem13Statement.{u})
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
      (relativeSample a c.s v p).1 = ENNReal.ofReal
          (capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r [] ω) ∧
        (∀ t : ℝ, t.toNNReal < v → ContinuousAt
          (fun q : ℝ => (physicalObservationRead a c.s v q.toNNReal p).1) t) ∧
        ContinuousOn (fun t : ℝ => (physicalObservationRead a c.s v t.toNNReal p).2)
          (Icc 0 (v : ℝ)) ∧
        volume {t : ℝ | t ∈ Ioo 0 (v : ℝ) ∧
          (physicalObservationRead a c.s v t.toNNReal p).2 ∉ H} = 0 := by
  have hfirst := RootZ21.ae_capR_nil_eq_forwardCapacity
    c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s c.P h13 c.hβA
    c.hb c.hc₀J c.hc₀ c.hh c.hcf c.hζ c.α c.hα r hroot
  have hnorm := RootB23.ae_initial_normalized_readers_regular
    c.hκ c.h12p c.βA c.c₀ c.h c.W c.ζ c.s c.b c.jumps c.P h13 c.hβA
    c.hb c.hc₀J c.hc₀ c.hh c.hcf c.hζ c.α c.hα r hroot
  dsimp only at hfirst hnorm ⊢
  filter_upwards [hfirst, hnorm, GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ,
    c.hζ, c.hα] with ω hf hn hr hζω hαω
  intro hsH hv
  have hnormω := hn hsH hv
  obtain ⟨_, _, hW, hW0, _⟩ := hr
  have hαζ : IsGeneratingTrace (c.W · ω) (c.ζ ω) (c.α ω) := by rwa [hζω]
  have hs : (c.s : ℝ≥0∞) < c.ζ ω := by rw [hζω]; exact ENNReal.coe_lt_top
  have ha : 0 < (2 : ℝ≥0) ^ r.2 := by positivity
  let e := canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec 0 [rootEntry r.1]) 0 ω
  have he : IsRegularDriver e :=
    isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ 0 _ _ (c.h ω) 0
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (physicalClock _ _ _ _ : ℝ≥0∞) = _
    rw [hnormω.1, ENNReal.ofReal_coe_nnreal]
    rfl
  all_goals rw [RootA22.initial_stopRec_eq c.hκ c.h12p c.βA c.c₀ c.h r hroot ω]
  · intro t ht
    exact continuousAt_physicalObservationRead_fst c.W c.ζ ω hαζ hW0 hsH he hf.1 hv
      ha hW hζω ht
  · exact continuousOn_physicalObservationRead_snd c.W c.ζ ω hαζ hW.continuousOn hW0 hs
      hsH he hf.1 hv ha
  · exact volume_physicalObservationRead_snd_notMem_H c.W c.ζ ω hαζ hW.continuousOn hW0
      hs hsH he hf.1 hv ha

end InteractingSLE.Theorem14.GW2TipSystem.RootD25
