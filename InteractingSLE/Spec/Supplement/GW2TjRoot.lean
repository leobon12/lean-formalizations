/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TjLoc
import InteractingSLE.Spec.Supplement.GW2ThSets

/-!
# (T1)–(T2) at every root (decision D8)

Packet PROVE-GW2-RELDET. Decision D8 (R120): the stage instance takes the root point `x`, with explored physical set
`x + fwdHull schedW t`, and every owner restates its statements once with the root parameter (and D1's guard). The
proof of (T1)–(T2) does not read the root except through the union and the explored set of the earlier pieces:

* **`ae_stageSet_subset_schedUnionX`**: at every root, for a time-ordered history, almost surely the explored set of
  the earlier pieces lies in round 21's root-`x` union `schedUnionX` (counterflow hull together with the explored hull
  translated to the root; `ℍ` off `oldSuccess`);
* `KernelUnionLocalX`: STAGEMEAN's `GW2Olm.KernelUnionLocal` for the root-`x` union;
* **`SchedKernelLinesStatementX`**, **`schedKernelLinesStatementX`**: the successor of `SchedKernelLinesStatementT` at
  every root (no `rootPt r.1 = 0`), from Theorems 1.2–1.3 (`exists_schedLinesLocal_setsX` and
  `GW2TjLoc.kernelLocal_of_union`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open LocalSets WholeField Exist Staged StagedLaw GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31 GW2Sdi Sec5.Prop513Schedule

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The explored set of the earlier pieces lies in the root-`x` union, almost surely** (time-ordered history). -/
theorem ae_stageSet_subset_schedUnionX (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hord : TimeOrdered 0 (historyProgram c r l)) (t : ℝ≥0) :
    ∀ᵐ ω ∂c.P, WalkLaw.stageSet c.κ c.b c.jumps (GW2Olm.futSpec c r l a) (GW2Olm.futFam c r l a)
      (GW2Olm.curIdx c r l) ω ⊆ schedUnionX c r l a (historyTime c r l) t ω := by
  filter_upwards [Gm.ae_futureJoined_trace h13 c r, ae_schedW_trace c r l a h13] with ω hfut htr
  intro z hz
  by_cases hωE : oldSuccess c r l ω
  swap
  · have e : schedHullX c r l a (historyTime c r l + t) ω = H := by simp only [schedHullX, hωE, ↓reduceIte]
    exact Or.inr (e ▸ hz.2)
  set x := rootPt r.1 with hx
  set Lh := historyProgram c r l with hLh
  set y : ℝ × ℝ≥0 := ((candidateAngle c r a : ℝ), historyTime c r l + candidateCap c r a) with hy
  have hrun := RootC11.run_schedSpec_append c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h x y ω
    (l := Lh) (n := Lh.length) le_rfl
  have hz' : z ∈ (⋃ p ∈ (ExplState.run c.κ c.b c.jumps (schedSpec x Lh)
      (fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x Lh) j ω) Lh.length).1,
      p.1.tipSet p.2.1 p.2.2) := by
    rw [← hrun]
    exact hz.1
  have hlen : (schedSpec x Lh).2.2.length = Lh.length := GW2Schedule.length_scheduleProgram 0 Lh
  have hzP : z ∈ prefixSet c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h x Lh ω := by
    change z ∈ ExplState.physSet c.κ c.b c.jumps (schedSpec x Lh)
      (fun k => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x Lh) k ω)
    unfold ExplState.physSet
    simp only []
    rw [hlen]
    exact Or.inl (Or.inr hz')
  have hγ : IsGeneratingTrace (Gm.futureJoined c r l a ω) ⊤ (schedTr c r l a ω) := by
    rw [← schedW_of_oldSuccess c r l a hωE]
    exact htr.1
  rw [Gm.prefixSet_history_eq c r l a ω hord hωE (hfut l a hωE).1 hγ] at hzP
  obtain ⟨w, ⟨s, hs, rfl⟩, rfl⟩ := hzP
  have hwH : schedTr c r l a ω s ∈ H := (mem_H_add_iff x).1 hz.2
  have hfill : IsFilling (schedHull c r l a (historyTime c r l + t) ω)
      (schedTr c r l a ω '' Icc 0 (historyTime c r l + t)) :=
    htr.1.2.2 (historyTime c r l + t) ENNReal.coe_lt_top
  have hmem : schedTr c r l a ω s ∈ schedHull c r l a (historyTime c r l + t) ω := by
    by_contra hn
    obtain ⟨⟨z₀, -, hcc⟩, -⟩ := hfill
    have hin : schedTr c r l a ω s ∈ H \ schedHull c r l a (historyTime c r l + t) ω := ⟨hwH, hn⟩
    rw [← hcc] at hin
    exact (connectedComponentIn_subset _ _ hin).2 ⟨s, ⟨hs.1, hs.2.trans le_self_add⟩, rfl⟩
  have e : schedHullX c r l a (historyTime c r l + t) ω =
      (fun z => (x : ℂ) + z) '' schedHull c r l a (historyTime c r l + t) ω := by
    simp only [schedHullX, hωE, ↓reduceIte]
    rfl
  refine Or.inr ?_
  rw [e]
  exact ⟨_, hmem, rfl⟩

/-- **(T1) for the root-`x` union** (`GW2Olm.KernelUnionLocal` with `schedUnionX` in place of `schedUnionS`). -/
def KernelUnionLocalX (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (𝓚 : ℝ≥0 → MeasurableSpace Ω) : Prop :=
  ∀ t : ℝ≥0, ∀ᵐ ω₀ ∂c.P, ∀ (cL : Chart) (θ : ℝ), GW2Olm.curLaunch c r l a ω₀ = some (cL, θ) →
    ∀ X : Ω → DistOn upperHalfPlaneOpens, (∀ ω, IsChartTransport cL 1 0 (chiC c.κ) (c.h ω) (X ω)) →
    ∀ uL : ℂ → ℝ, LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField X uL)
        (condExpKernel c.P (GW2Olm.pastG c r l a) ω₀) →
      IsHistoryAvoidanceLocal (𝓚 t) (fun ω => cL.1 '' (schedUnionX c r l a (historyTime c r l) t ω ∩ cL.dom))
        (centredField X uL) (condExpKernel c.P (GW2Olm.pastG c r l a) ω₀)

/-- **(T1)–(T2) at every root** (D8 with D1's guard): the successor of `SchedKernelLinesStatementT` for the
root-`x` union. -/
def SchedKernelLinesStatementX : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), TimeOrdered 0 (historyProgram c r l) →
    ∃ (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω),
      InnerProductSpace.HarmonicOnNhd u₀ H ∧
      LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h u₀) c.P ∧
      (∀ t, stgFilt (Supp8.RelSafe.physFilt (GW2Sde.measurable_gb6Rec_src c) (measurable_schedW c r l a) c.P)
        (historyTime c r l) (GW2Sde.measurable_stageEncRec c r l) t ≤ ℋ t) ∧
      (∀ t, ℋ t ≤ mΩ) ∧
      (∀ t, IsHistoryAvoidanceLocal (ℋ t) (schedUnionX c r l a (historyTime c r l) t) (centredField c.h u₀) c.P) ∧
      ∃ 𝓚 : ℝ≥0 → MeasurableSpace Ω, GW2Olm.KernelMarksAgree c r l a 𝓚 ℋ ∧ KernelUnionLocalX c r l a 𝓚

/-- **(T1)–(T2) hold at every root, with the stage filtration as the instance's marks** (Theorems 1.2–1.3). -/
theorem schedKernelLinesStatementX (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u}) :
    SchedKernelLinesStatementX.{u} := by
  intro Ω mΩ _ c r l a hord
  obtain ⟨u₀, ℋ', hharm, hzb, hstg, -, hBm, hBc, hloc'⟩ :=
    exists_schedLinesLocal_setsX c r l a h12 h13 hord (le_refl (historyTime c r l))
  have hloc : ∀ t, IsHistoryAvoidanceLocal (stgF c r l a t) (schedUnionX c r l a (historyTime c r l) t)
      (centredField c.h u₀) c.P := fun t U G hUH hG hd F hF => hloc' t U G hUH hG hd F (hstg t F hF)
  exact ⟨u₀, stgF c r l a, hharm, hzb, fun t => le_rfl, fun t => (stgFilt _ _ _).le t, hloc,
    kerMarks c r l a, kernelMarksAgree_stgFilt c r l a,
    fun t => kernelLocal_of_union h13 c r l a hharm hzb hBm (fun t ω => hBc t ω) hloc
      (fun t => ae_stageSet_subset_schedUnionX h13 c r l a hord t) t⟩

end InteractingSLE.Theorem14.GW2Rd
