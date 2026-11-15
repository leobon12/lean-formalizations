/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TcSup
import InteractingSLE.Spec.Supplement.LPTrace

/-!
# The explored trace read through countably many measurable samples

Packet PROVE-GW2-RELDET, ruling R113 (`GW2TbHull.SchedCurveLocalStatement`). The chosen trace `GW2SyJoin.schedTr` is
not known to be measurable. The explored curve on `[0, q]` is read instead as the closure of its rational samples taken
with the measurable trace readout `LP.traceAt` (`schedSamples`). Its avoidance events are then EXACTLY countable
intersections of events of the explored path on `[0, q]` (`measurableSet_disjoint_schedSamples`), and almost surely
it is the trace image (`ae_schedSamples_eq`).

* `disjoint_closure_range_iff`: an open set misses the closure of a range iff it misses every value;
* **`measurableSet_disjoint_schedSamples`**: for any σ-algebra reading `schedW` on `[0, q]`;
* **`ae_schedSamples_eq`**: `schedSamples q = schedTr '' [0, q]` almost surely (Theorem 1.3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology TopologicalSpace Metric
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open GW2TipSystem GW2TipSystem.RootC24

theorem disjoint_closure_range_iff {ι : Type*} {f : ι → ℂ} {U : Set ℂ} (hU : IsOpen U) :
    Disjoint (closure (range f)) U ↔ ∀ i, f i ∉ U := by
  constructor
  · exact fun h i hi => disjoint_left.1 h (subset_closure ⟨i, rfl⟩) hi
  · intro h
    refine Disjoint.closure_left ?_ hU
    rw [disjoint_left]
    rintro _ ⟨i, rfl⟩ hi
    exact h i hi

section Samples

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- **The explored curve on `[0, q]`, read through measurable rational samples.** -/
def schedSamples (q : ℝ≥0) (ω : Ω) : Set ℂ :=
  closure (range fun t : ℚ≥0 => LP.traceAt (min (t : ℝ≥0) q) fun s => schedW c r l a s ω)

/-- **Its avoidance events are events of the explored path on `[0, q]`.** -/
theorem measurableSet_disjoint_schedSamples {q : ℝ≥0} (M : {m : MeasurableSpace Ω // m ≤ mΩ})
    (hm : ∀ t ≤ q, @Measurable Ω ℝ M.1 _ (schedW c r l a t)) {U : Set ℂ} (hU : IsOpen U) :
    @MeasurableSet Ω M.1 {ω | Disjoint (schedSamples c r l a q ω) U} := by
  have hp : @Measurable Ω (ℝ≥0 → ℝ) M.1 _ fun ω => fun s => schedW c r l a (min s q) ω :=
    (@measurable_pi_iff _ _ _ M.1 _ _).2 fun s => hm _ (min_le_right _ _)
  have hsamp : ∀ t : ℚ≥0, @Measurable Ω ℂ M.1 _
      fun ω => LP.traceAt (min (t : ℝ≥0) q) fun s => schedW c r l a s ω := by
    intro t
    have e : (fun ω => LP.traceAt (min (t : ℝ≥0) q) fun s => schedW c r l a s ω) =
        fun ω => LP.traceAt (min (t : ℝ≥0) q) fun s => schedW c r l a (min s q) ω := by
      funext ω
      refine LP.traceAt_congr fun s hs => ?_
      rw [min_eq_left (hs.trans (min_le_right _ _))]
    rw [e]
    exact (LP.measurable_traceAt _).comp hp
  have e : {ω | Disjoint (schedSamples c r l a q ω) U} =
      ⋂ t : ℚ≥0, (fun ω => LP.traceAt (min (t : ℝ≥0) q) fun s => schedW c r l a s ω) ⁻¹' Uᶜ := by
    ext ω
    simp only [mem_ofPred_eq, schedSamples, disjoint_closure_range_iff hU, mem_iInter, mem_preimage, mem_compl_iff]
  rw [e]
  exact @MeasurableSet.iInter Ω _ M.1 _ _ fun t => hsamp t hU.measurableSet.compl

/-- **Almost surely the samples' closure is the trace image** (Theorem 1.3). -/
theorem ae_schedSamples_eq [StandardBorelSpace Ω] (h13 : Exist.Theorem13Statement.{u}) (q : ℝ≥0) :
    ∀ᵐ ω ∂c.P, schedSamples c r l a q ω = schedTr c r l a ω '' Icc 0 q := by
  filter_upwards [ae_schedW_trace c r l a h13] with ω hω
  set γ := schedTr c r l a ω with hγ
  have hγc : Continuous γ := continuousOn_univ.1 (hω.1.2.1.mono fun t _ =>
    show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hsamp : ∀ t : ℝ≥0, LP.traceAt t (fun s => schedW c r l a s ω) = γ t := fun t =>
    LP.traceAt_eq_of_isGeneratingTrace hω.1 (continuous_schedW c r l a ω).continuousOn (schedW_zero c r l a ω)
      ENNReal.coe_lt_top
  have hrange : (range fun t : ℚ≥0 => LP.traceAt (min (t : ℝ≥0) q) fun s => schedW c r l a s ω) =
      range fun t : ℚ≥0 => γ (min (t : ℝ≥0) q) := by
    simp only [hsamp]
  rw [schedSamples, hrange]
  have hcl : IsClosed (γ '' Icc 0 q) := (isCompact_Icc.image hγc).isClosed
  apply Subset.antisymm
  · refine closure_minimal ?_ hcl
    rintro _ ⟨t, rfl⟩
    exact ⟨min (t : ℝ≥0) q, ⟨zero_le, min_le_right _ _⟩, rfl⟩
  · rintro _ ⟨s, hs, rfl⟩
    have hg : Continuous fun t : ℝ≥0 => γ (min t q) := hγc.comp (continuous_id.min continuous_const)
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := Metric.continuous_iff.1 hg s ε hε
    -- a rational time within `δ` of `s`
    obtain ⟨t, hst, htδ⟩ := Supp8.GB6.HullId.exists_nnrat_btwn
      (show s < s + ⟨δ / 2, by positivity⟩ from lt_add_of_pos_right _ (by exact_mod_cast half_pos hδ))
    refine ⟨γ (min (t : ℝ≥0) q), ⟨t, rfl⟩, ?_⟩
    have hd : dist (t : ℝ≥0) s < δ := by
      rw [NNReal.dist_eq]
      have h1 : (s : ℝ) < (t : ℝ≥0) := by exact_mod_cast hst
      have h2 : ((t : ℝ≥0) : ℝ) < s + δ / 2 := by exact_mod_cast htδ
      rw [abs_lt]
      constructor <;> linarith
    have h3 := hδε (t : ℝ≥0) hd
    rw [min_eq_left hs.2, dist_comm] at h3
    exact h3

end Samples

end InteractingSLE.Theorem14.GW2Rd
