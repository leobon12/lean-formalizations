/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmJ32Obs
import InteractingSLE.Spec.Supplement.GW2RootK32Active

/-!
# Causality of J32's separation buffer (tools for the observation gate)

Packet PROVE-GW2-GEOM2 (round 5). J32's failure time `F = T + sourceBuffer` reads the separation gauge
`t ↦ RootJ31.separationRead x s (T + cap) (T + t) p` of the candidate's future pair through a gauge stop
(`Version.localStop`). This file shows that this gauge, and hence the stop's comparison with a time `τ`, only
depends on the joined driver up to `T + τ`:

* (with `Gm.frozenTraceRead_recOfDriver`: a driver record read at its horizon gives the trace frozen there)
* `separationRead_congr`: the separation at `t` reads the flow prefix only up to `t`;
* **`lt_localStop_congr`**: whether `τ` precedes a gauge stop depends on the (continuous) gauge on `[0, τ]` only;
* **`ae_nextJoined_trace`**: almost surely, the next history's joined driver has a `⊤`-trace whenever the history
  succeeded (all its pieces are launched).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip RootC24 RootJ32 Sec5.Prop513TreeExtract
  Sec5.Prop513Schedule

/-- The separation gauge at `t` reads the flow record's frozen trace only up to `t`. -/
theorem separationRead_congr {x : ℝ} {s v v' t : ℝ≥0} {p p' : RecData × RecData} (h1 : p.1 = p'.1)
    (h2 : ∀ τ ≤ t, RootG28.frozenTraceRead v p.2 τ = RootG28.frozenTraceRead v' p'.2 τ) :
    RootJ31.separationRead x s v t p = RootJ31.separationRead x s v' t p' := by
  unfold RootJ31.separationRead
  rw [h1]
  congr 2
  funext q
  have hq : (((q.1.val : ℚ≥0) : ℝ≥0)) ≤ 1 := by exact_mod_cast q.1.2
  rw [h2 _ (mul_le_of_le_one_right zero_le hq)]

/-- **Whether a time precedes a gauge stop depends on the gauge up to that time.** -/
theorem lt_localStop_congr {g g' : ℝ≥0 → ℝ} (hg : Continuous g) (hg' : Continuous g') {τ : ℝ≥0}
    (h : ∀ u ≤ τ, g u = g' u) (m : ℕ) :
    τ < Supp8.GB6.RelDrv.Version.localStop g m ↔ τ < Supp8.GB6.RelDrv.Version.localStop g' m := by
  unfold Supp8.GB6.RelDrv.Version.localStop
  rw [h 0 zero_le]
  set ε := Supp8.GB6.RelDrv.Version.gaugeLevel (g' 0) m
  by_cases hτ : τ < (m : ℝ≥0) + 1
  · rw [← not_le, ← not_le, Supp8.GB6.RelDrv.Version.gaugeStop_le_iff hg hτ,
      Supp8.GB6.RelDrv.Version.gaugeStop_le_iff hg' hτ]
    constructor
    · rintro hn ⟨u, hu, hgu⟩
      exact hn ⟨u, hu, by rwa [h u hu]⟩
    · rintro hn ⟨u, hu, hgu⟩
      exact hn ⟨u, hu, by rwa [← h u hu]⟩
  · have h1 := Supp8.GB6.RelDrv.Version.gaugeStop_le g ε ((m : ℝ≥0) + 1)
    have h2 := Supp8.GB6.RelDrv.Version.gaugeStop_le g' ε ((m : ℝ≥0) + 1)
    exact ⟨fun hlt => absurd (hlt.trans_le h1) hτ, fun hlt => absurd (hlt.trans_le h2) hτ⟩

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The next history's joined driver has a `⊤`-trace**, almost surely, whenever the history succeeded. -/
theorem ae_nextJoined_trace (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : c.Q), RootJ31.oldSuccess c r l ω →
      ∃ γ, IsGeneratingTrace
        (RootJ31.joinedRead (RootJ31.historyProgram c r ((RootJ31.candidateAngle c r a, q) :: l))
          (RootJ31.programRecords c (rootPt r.1)
            (RootJ31.historyProgram c r ((RootJ31.candidateAngle c r a, q) :: l)) ω)) ⊤ γ := by
  have : Countable c.Θ := c.hΘc.to_subtype
  have : Countable c.Q := c.hQc.to_subtype
  have hnext : ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : c.Q),
      ∀ k < (RootJ31.historyProgram c r l ++ [((RootJ31.candidateAngle c r a : ℝ), (q : ℝ≥0))]).length,
        AllSucc (specDelta (schedSpec (rootPt r.1) (RootJ31.historyProgram c r l ++
            [((RootJ31.candidateAngle c r a : ℝ), (q : ℝ≥0))])))
          (fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec (rootPt r.1)
            (RootJ31.historyProgram c r l ++ [((RootJ31.candidateAngle c r a : ℝ), (q : ℝ≥0))])) j ω) k →
        LocalExt.IsDrvGood (recHist (stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpec (rootPt r.1)
          (RootJ31.historyProgram c r l ++ [((RootJ31.candidateAngle c r a : ℝ), (q : ℝ≥0))])) k ω)) ∧
        ∃ η, IsGeneratingTrace (fun t : ℝ≥0 => rdrv (stopRec c.hκ c.h12p c.βA c.c₀ c.h
          (schedSpec (rootPt r.1) (RootJ31.historyProgram c r l ++
            [((RootJ31.candidateAngle c r a : ℝ), (q : ℝ≥0))])) k ω) t) ⊤ η := by
    rw [ae_all_iff]; intro l
    rw [ae_all_iff]; intro a
    rw [ae_all_iff]; intro q
    exact ae_launched_rdrv_trace h13 c (rootPt r.1)
      (RootJ31.historyProgram c r l ++ [((RootJ31.candidateAngle c r a : ℝ), (q : ℝ≥0))])
  filter_upwards [hnext] with ω hnext l a q hold
  set x := rootPt r.1
  set Lh := RootJ31.historyProgram c r l with hLh
  set L' := Lh ++ [((RootJ31.candidateAngle c r a : ℝ), (q : ℝ≥0))] with hL'
  set Δ' := specDelta (schedSpec x L')
  set D' := fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x L') j ω
  have hsh := (RootJ31.oldSuccess_iff_allSucc c r l ω).mp hold
  have hΔ'h : ∀ j < Lh.length, Δ' j = specDelta (schedSpec x Lh) j := fun j hj =>
    specDelta_schedSpec_append x _ hj
  have hD'h : ∀ j < Lh.length, D' j =
      canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x Lh) j ω := fun j hj =>
    RootC11.canonSpecFam_append c.hκ c.h12p c.βA c.c₀ c.h x _ hj ω
  have hs' : AllSucc Δ' D' Lh.length := by
    intro j hj
    rw [hΔ'h j hj, hD'h j hj]
    exact hsh j hj
  rw [RootJ31.historyProgram_cons]
  refine exists_isGeneratingTrace_joinedRead L' _ fun i hi => ?_
  have him : i ≤ Lh.length := by
    rw [hL', List.length_append, List.length_singleton] at hi
    omega
  exact (hnext l a q i hi (hs'.mono him)).2

end InteractingSLE.Theorem14.GW2TipSystem.Gm
