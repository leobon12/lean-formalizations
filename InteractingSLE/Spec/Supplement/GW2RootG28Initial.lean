/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootG28Observe
import InteractingSLE.Spec.Supplement.GW2RootD25Launch

/-!
# The original source supplies the initial buffered experiment geometry

Packet PROVE-T14-GW2ROOT2. From the source GFF setup and Theorem 1.3,
the actual recorded initial piece supplies safe random buffers and
their dense physical cover. On protected initial prefixes, the killed
sample has the exact reach event and all five experiment regularity clauses.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootG28

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric RootC24 Supp8.GB6 RootD25

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- Every live initial zero-root record supplies safe positive geometric
buffers, and those with caps from the original `Q` cover each pre-contact query. -/
theorem ae_initial_contactBuffer_spec (h13 : Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (hroot : rootPt r.1 = 0) :
    let v := (rootEntry r.1).2
    let E := canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec 0 [rootEntry r.1]) 0
    let γ := GW2aSingle.chosenTrace (fun t ω => (E ω).1 t) (fun ω => (E ω).2)
    ∀ᵐ ω ∂c.P, c.α ω c.s ∈ H → (v : ℝ≥0∞) < (E ω).2 →
      let p := (cfRec c.s c.W c.ζ ω,
        stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 []) 0 ω)
      (∀ b : c.Q, (b : ℝ≥0) < v → ∀ m : ℕ,
        0 < contactBuffer c.s v b m p ∧ (contactBuffer c.s v b m p : ℝ≥0∞) < min
          (firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
            ((fun t => (c.α ω t : OnePoint ℂ)) '' Icc 0 c.s)) (E ω).2) ∧
      ∀ t : ℝ≥0, t < v → (t : ℝ≥0∞) < firstContactTime
        (fun u => sphereInv (γ ω u : OnePoint ℂ))
        ((fun u => (c.α ω u : OnePoint ℂ)) '' Icc 0 c.s) →
        ∃ b : c.Q, 0 < (b : ℝ≥0) ∧ (b : ℝ≥0) < v ∧ ∃ m : ℕ,
          t < contactBuffer c.s v b m p := by
  have hfirst := RootZ21.ae_capR_nil_eq_forwardCapacity
    c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s c.P h13 c.hβA
    c.hb c.hc₀J c.hc₀ c.hh c.hcf c.hζ c.α c.hα r hroot
  dsimp only at hfirst ⊢
  filter_upwards [hfirst, GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ,
    c.hζ, c.hα] with ω hf hcf hζω hαω
  intro hsH hv
  obtain ⟨_, _, hW, hW0, _⟩ := hcf
  have hs : 0 < c.s := by
    by_contra hn
    have hz : c.s = 0 := le_antisymm (not_lt.mp hn) zero_le
    rw [hz, hαω.1] at hsH
    exact (lt_irrefl (0 : ℝ)) hsH
  let e := canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec 0 [rootEntry r.1]) 0 ω
  have he : IsRegularDriver e :=
    isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ 0 _ _ (c.h ω) 0
  rw [RootA22.initial_stopRec_eq c.hκ c.h12p c.βA c.c₀ c.h r hroot ω]
  constructor
  · intro b hb m
    exact contactBuffer_before_contact c.W c.ζ c.s ω hW hW0 hζω hαω he hf.1 hv
      hs (c.hQpos b.val b.property) hb m
  · intro t htv ht
    exact exists_source_contactBuffer c.W c.ζ c.s ω hW hW0 hζω hαω he hf.1 hv
      c.hQd htv ht

/-- The initial random-buffer experiment has the actual reach
identification and every regularity clause, from the original source alone. -/
theorem ae_initial_buffered_entry_regular (h13 : Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (hroot : rootPt r.1 = 0) :
    let a : ℝ≥0 := 2 ^ r.2
    let v := (rootEntry r.1).2
    let E := canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec 0 [rootEntry r.1]) 0
    let γ := GW2aSingle.chosenTrace (fun t ω => (E ω).1 t) (fun ω => (E ω).2)
    ∀ᵐ ω ∂c.P, c.α ω c.s ∈ H → (v : ℝ≥0∞) < min
      (firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
        ((fun t => (c.α ω t : OnePoint ℂ)) '' Icc 0 c.s)) (E ω).2 →
      ∀ b : ℝ≥0, b ≤ v → ∀ m : ℕ,
      let p := (cfRec c.s c.W c.ζ ω,
        stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 []) 0 ω)
      let S := entryPhysical a c.s v p
      let F := contactBuffer c.s v b m p
      let X : ℝ → ℝ := fun t => (physicalObservationRead a c.s v t.toNNReal p).1
      let Γ : ℝ → ℂ := fun t => (physicalObservationRead a c.s v t.toNNReal p).2
      (bufferedSample a c.s v b m p ∈ reachSet ↔ S < F) ∧
        (S < F → 0 ≤ (S : ℝ) ∧ ContinuousAt X S ∧ X S ∈ CS3Select.band 1 ∧
          ContinuousOn Γ (Ioo (S : ℝ) (F : ℝ)) ∧
          volume {t : ℝ | t ∈ Ioo (S : ℝ) (F : ℝ) ∧ Γ t ∉ H} = 0) := by
  have hreg := ae_initial_entry_regular h13 c r hroot
  have hfirst := RootZ21.ae_capR_nil_eq_forwardCapacity
    c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s c.P h13 c.hβA
    c.hb c.hc₀J c.hc₀ c.hh c.hcf c.hζ c.α c.hα r hroot
  dsimp only at hreg hfirst ⊢
  filter_upwards [hreg, hfirst, GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ,
    c.hζ, c.hα] with ω hr hf hcf hζω hαω
  intro hsH hv b hb m
  have hrω := hr hsH hv
  obtain ⟨_, _, hW, hW0, _⟩ := hcf
  have hαζ : IsGeneratingTrace (c.W · ω) (c.ζ ω) (c.α ω) := by rwa [hζω]
  have ha : 0 < (2 : ℝ≥0) ^ r.2 := by positivity
  let e := canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec 0 [rootEntry r.1]) 0 ω
  have he : IsRegularDriver e :=
    isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ 0 _ _ (c.h ω) 0
  rw [RootA22.initial_stopRec_eq c.hκ c.h12p c.βA c.c₀ c.h r hroot ω] at hrω ⊢
  have hFv := (contactBuffer_le c.s (rootEntry r.1).2 b m
    (cfRec c.s c.W c.ζ ω, recOf ((rootEntry r.1).2 : ℝ≥0∞) e)).trans hb
  refine ⟨bufferedSample_mem_reach_iff c.W c.ζ ω hαζ hW hW0 hζω
    hsH he hf.1 hv ha hb m, fun hSF => ?_⟩
  obtain ⟨hS0, hC, hband, hΓ, hnull⟩ := hrω.2 (hSF.trans_le hFv)
  refine ⟨hS0, hC, hband, hΓ.mono ?_, measure_mono_null ?_ hnull⟩
  · intro t ht
    exact ⟨ht.1, ht.2.trans_le (NNReal.coe_le_coe.mpr hFv)⟩
  · intro t ht
    exact ⟨⟨ht.1.1, ht.1.2.trans_le (NNReal.coe_le_coe.mpr hFv)⟩, ht.2⟩

end InteractingSLE.Theorem14.GW2TipSystem.RootG28
