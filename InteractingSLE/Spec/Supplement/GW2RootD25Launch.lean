/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootD25Initial
import InteractingSLE.Spec.Supplement.GW2RootD25Entry
import InteractingSLE.Spec.Supplement.CS3ProofSelect

/-!
# The actual initial entry satisfies the source experiment's regularity clause

Packet PROVE-T14-GW2ROOT2. The source flow trace and counterflow supply
every regularity assertion on protected zero-root prefixes. The entry,
failure cutoff, driver, tip, sample and measurable reach event are all
the concrete readers constructed in this continuation.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootD25

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric RootC24 Supp8.GB6

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The initial concrete experiment has the actual reach identification
and all five regularity conclusions required at successful entry. -/
theorem ae_initial_entry_regular (h13 : Theorem13Statement.{u})
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
      let S := entryPhysical a c.s v p
      let X : ℝ → ℝ := fun t => (physicalObservationRead a c.s v t.toNNReal p).1
      let Γ : ℝ → ℂ := fun t => (physicalObservationRead a c.s v t.toNNReal p).2
      (relativeSample a c.s v p ∈ reachSet ↔ S < v) ∧
        (S < v → 0 ≤ (S : ℝ) ∧ ContinuousAt X S ∧ X S ∈ CS3Select.band 1 ∧
          ContinuousOn Γ (Ioo (S : ℝ) (v : ℝ)) ∧
          volume {t : ℝ | t ∈ Ioo (S : ℝ) (v : ℝ) ∧ Γ t ∉ H} = 0) := by
  have hreg := ae_initial_physical_regular h13 c r hroot
  have hfirst := RootZ21.ae_capR_nil_eq_forwardCapacity
    c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s c.P h13 c.hβA
    c.hb c.hc₀J c.hc₀ c.hh c.hcf c.hζ c.α c.hα r hroot
  dsimp only at hreg hfirst ⊢
  filter_upwards [hreg, hfirst, GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ,
    c.hζ, c.hα] with ω hr hf hcf hζω hαω
  intro hsH hv
  have hregω := hr hsH hv
  obtain ⟨_, _, hW, hW0, _⟩ := hcf
  have hαζ : IsGeneratingTrace (c.W · ω) (c.ζ ω) (c.α ω) := by rwa [hζω]
  have ha : 0 < (2 : ℝ≥0) ^ r.2 := by positivity
  let e := canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec 0 [rootEntry r.1]) 0 ω
  have he : IsRegularDriver e :=
    isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ 0 _ _ (c.h ω) 0
  let p := (cfRec c.s c.W c.ζ ω,
    stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 []) 0 ω)
  have hent : relativeSample (2 ^ r.2) c.s (rootEntry r.1).2 p ∈ reachSet →
      entryPhysical (2 ^ r.2) c.s (rootEntry r.1).2 p < (rootEntry r.1).2 ∧
        (physicalObservationRead (2 ^ r.2) c.s (rootEntry r.1).2
          (entryPhysical (2 ^ r.2) c.s (rootEntry r.1).2 p) p).1 = 2 := by
    dsimp only [p]
    rw [RootA22.initial_stopRec_eq c.hκ c.h12p c.βA c.c₀ c.h r hroot ω]
    exact entryPhysical_spec_before_contact c.W c.ζ ω hαζ hW hW0 hζω hsH he hf.1 hv ha
  have hiff : relativeSample (2 ^ r.2) c.s (rootEntry r.1).2 p ∈ reachSet ↔
      entryPhysical (2 ^ r.2) c.s (rootEntry r.1).2 p < (rootEntry r.1).2 := by
    refine ⟨fun h => (hent h).1, fun h => ?_⟩
    by_contra hfail
    rw [entryPhysical_eq_cutoff hfail] at h
    exact (lt_irrefl _) h
  refine ⟨hiff, fun hS => ⟨NNReal.coe_nonneg _, ?_, ?_, ?_, ?_⟩⟩
  · exact hregω.2.1 _ (by simpa only [Real.toNNReal_coe] using hS)
  · have htwo := (hent (hiff.mpr hS)).2
    simp only [Real.toNNReal_coe]
    change (physicalObservationRead (2 ^ r.2) c.s (rootEntry r.1).2
      (entryPhysical (2 ^ r.2) c.s (rootEntry r.1).2 p) p).1 ∈ CS3Select.band 1
    rw [htwo]
    norm_num [CS3Select.band]
  · exact hregω.2.2.1.mono fun t ht =>
      ⟨(NNReal.coe_nonneg _).trans ht.1.le, ht.2.le⟩
  · apply measure_mono_null ?_ hregω.2.2.2
    intro t ht
    exact ⟨⟨lt_of_le_of_lt (NNReal.coe_nonneg _) ht.1.1, ht.1.2⟩, ht.2⟩

end InteractingSLE.Theorem14.GW2TipSystem.RootD25
