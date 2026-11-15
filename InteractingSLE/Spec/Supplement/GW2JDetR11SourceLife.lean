/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootG28Initial
import InteractingSLE.Spec.Supplement.GW2CvProps

/-!
# Positive lifetimes of the actual initial buffered samples

The stopped comparison needs a positive recording stop. The source's
geometric buffer and the landed strict capacity clock supply this fact;
no probabilistic comparison or additional clock premise is used.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2JDetR11

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootG28
  GW2TipSystem.RootD25 GW2Schedule GW2Tip Exist Staged StagedLaw Restart Supp8.GB6

/-- Killing at a geometric buffer inside a strictly increasing clock
retains its exact capacity lifetime. A positive buffer has positive lifetime. -/
theorem bufferedSample_life_of_clock (a s v b : ℝ≥0) (m : ℕ)
    (p : RecData × RecData) (hb : b ≤ v)
    (h0 : physicalClock a s 0 p = 0)
    (hm : StrictMonoOn (fun t => physicalClock a s t p) (Icc 0 v))
    (hF : 0 < contactBuffer s v b m p) :
    (bufferedSample a s v b m p).1 =
        (physicalClock a s (contactBuffer s v b m p) p : ℝ≥0∞) ∧
      0 < (bufferedSample a s v b m p).1 := by
  have hFv := (contactBuffer_le s v b m p).trans hb
  have hle := hm.monotoneOn ⟨zero_le, hFv⟩ ⟨zero_le, le_rfl⟩ hFv
  have hpos := hm ⟨zero_le, zero_le⟩ ⟨zero_le, hFv⟩ hF
  dsimp only at hpos
  rw [h0] at hpos
  have heq : (bufferedSample a s v b m p).1 =
      (physicalClock a s (contactBuffer s v b m p) p : ℝ≥0∞) :=
    min_eq_left (ENNReal.coe_le_coe.mpr hle)
  exact ⟨heq, heq ▸ ENNReal.coe_pos.mpr hpos⟩

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- At the original zero root, every source buffer below the protected
root time gives a positive actual capacity-killed sample. -/
theorem ae_initial_bufferedSample_pos (h13 : Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (hroot : rootPt r.1 = 0) :
    let v := (rootEntry r.1).2
    let E := canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec 0 [rootEntry r.1]) 0
    let γ := GW2aSingle.chosenTrace (fun t ω => (E ω).1 t) (fun ω => (E ω).2)
    ∀ᵐ ω ∂c.P, c.α ω c.s ∈ H → (v : ℝ≥0∞) < min
      (firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
        ((fun t => (c.α ω t : OnePoint ℂ)) '' Icc 0 c.s)) (E ω).2 →
      ∀ b : c.Q, (b : ℝ≥0) < v → ∀ m : ℕ,
        0 < (bufferedSample (2 ^ r.2) c.s v b m (RootCv.rootRecs c r.1 ω)).1 := by
  have hbuf := ae_initial_contactBuffer_spec h13 c r hroot
  have hfirst := RootZ21.ae_capR_nil_eq_forwardCapacity
    c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s c.P h13 c.hβA
    c.hb c.hc₀J c.hc₀ c.hh c.hcf c.hζ c.α c.hα r hroot
  dsimp only at hbuf hfirst ⊢
  filter_upwards [hbuf, hfirst, GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ,
    c.hζ, c.hα] with ω hb hf hcf hζω hαω
  intro hsH hv b hbv m
  have hF := (hb hsH (hv.trans_le (min_le_right _ _))).1 b hbv m
  obtain ⟨_, _, hW, hW0, _⟩ := hcf
  have hαζ : IsGeneratingTrace (c.W · ω) (c.ζ ω) (c.α ω) := by rwa [hζω]
  have hs : (c.s : ℝ≥0∞) < c.ζ ω := by rw [hζω]; exact ENNReal.coe_lt_top
  let e := canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec 0 [rootEntry r.1]) 0 ω
  have he : IsRegularDriver e :=
    isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ 0 _ _ (c.h ω) 0
  have ha : 0 < (2 : ℝ≥0) ^ r.2 := by positivity
  obtain ⟨h0, hm, _⟩ := RootE26.physicalClock_regular
    c.W c.ζ ω hαζ hW.continuousOn hW0 hs hsH he hf.1 hv ha
  change 0 < (bufferedSample _ _ _ _ _ (_, _)).1
  rw [RootA22.initial_stopRec_eq c.hκ c.h12p c.βA c.c₀ c.h r hroot ω] at hF ⊢
  exact (bufferedSample_life_of_clock _ _ _ _ _ _ hbv.le h0 hm hF.1).2

/-- COVER supplies every geometric premise in the positivity theorem. -/
theorem ae_initial_bufferedSample_pos_on_cover (h13 : Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (hroot : rootPt r.1 = 0) :
    ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c r →
      ∀ b : c.Q, (b : ℝ≥0) < (rootEntry r.1).2 → ∀ m : ℕ,
        0 < (bufferedSample (2 ^ r.2) c.s (rootEntry r.1).2 b m
          (RootCv.rootRecs c r.1 ω)).1 := by
  have hpos := ae_initial_bufferedSample_pos h13 c r hroot
  have hcov := RootCv.ae_coverEvent_spec_zero h13 c r hroot
  dsimp only at hpos hcov
  filter_upwards [hpos, hcov] with ω hp hc hω
  exact hp (hc hω).1 (hc hω).2.2

end InteractingSLE.Theorem14.GW2JDetR11
