/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61R1CBuild
import InteractingSLE.Spec.Sec5.Aux61SlitWYAccess

/-! # The concrete restart-choice model reads its selected records

R1C's good-record retraction supplies the continuous model, driver reader,
and complete configuration membership required by the landed slit lemmas.
No additional model or incidence premise is introduced.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWZ
open Aux61SlitW Aux61SlitWX Aux61R1C Aux61Restart Aux61ULoc LawUnique

/-- Good records satisfy the full geometric configuration for R1C's
actual total model, including its original-target current incidence. -/
theorem configuration_of_good {nL nR : ℕ} {s : ℝ≥0} {q : ℚ} (hs : 0 < s)
    {y : Rec nL nR} (hy : y ∈ goodSet s q) :
    y ∈ restartConfigurationEvent s (rationalTime q) q (finY s q) (finη s q) (finU s q) := by
  obtain ⟨hq, hUc, hU0, hη, hi, hH, hc, h0, hprotected⟩ := hy.1.facts
  have hY : historyHull s (finY s q) y = recHull s y := by
    simp only [historyHull, finY_of_mem hy, recHull]
  have htrace := finη_of_mem hy
  have hdrive : (fun t => finU s q t y) = fun t => recU q t y := by
    funext t
    exact congrArg (recU q t) (retr_of_mem hy)
  change (InjOn (finη s q y) (Icc (0 : ℝ) q) ∧
    MapsTo (finη s q y) (Ioc (0 : ℝ) q) H ∧
    0 < infDist (finη s q y q) (historyHull s (finY s q) y)) ∧
    ((1 : ℂ) ∉ closure (historyHull s (finY s q) y)) ∧
    ∃ b : ℂ, (1 : ℂ) ∈ closure (restartComponent (historyHull s (finY s q) y) (finη s q y) q b) ∧
      ∃ᶠ w in 𝓝[H] 0, (ownHistoryChart (finU s q) (rationalTime q) y).2.1 w ∈
        restartComponent (historyHull s (finY s q) y) (finη s q y) q b
  rw [htrace, hY]
  refine ⟨⟨hi, hH, ?_⟩, hprotected, ?_⟩
  · rw [recη_of_le (by exact_mod_cast hq.le) y le_rfl]
    exact infDist_recHull_pos hs hy.2.1
  · obtain ⟨-, -, hmark⟩ := selN_spec (show (regSet (nL := nL) (nR := nR) s q).Nonempty from ⟨y, hy.1⟩)
    have hm := hmark y
    rw [tgtComp_of_mem hy.1] at hm
    refine ⟨baseSeq (selN s q y), hm, ?_⟩
    obtain ⟨n₀, hn₀⟩ := hy.2.2
    have hev : ∀ᶠ n in atTop, (ownHistoryChart (finU s q) (rationalTime q) y).2.1 (accPt n) ∈
        restartComponent (recHull s y) (recη q y) q (baseSeq (selN s q y)) := by
      refine eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩
      have h := hn₀ n hn
      rw [tgtComp_of_mem hy.1] at h
      simp only [stU] at h
      rw [retr_of_mem (show y ∈ regSet s q from hy.1)] at h
      change fwdMapInv (Ito.rpath fun t => finU s q t y) (rationalTime q) (accPt n) ∈ _
      rwa [hdrive]
    exact tendsto_accPt.frequently hev.frequently

universe u
variable {S : SourceSetting.{u}} (C : RestartChoices S)

/-- The landed reader interface for the exact concrete choice model.
Only the choices' selected-set measurability is an input, already a field
of `ChoiceInputs`; all model and configuration facts are proved. -/
theorem readers (hsel : ∀ i, MeasurableSet (C.selected i)) : ReaderFacts C.toR1Restart where
  selected_measurable := C.selected_measurable hsel
  q_pos := fun i => by
    obtain ⟨y, hy⟩ := i.2
    exact hy.1.facts.1
  time_eq := fun _ => rfl
  counterflow := C.record_Y
  path := C.record_η
  driver_continuous := fun i y hy => by
    change Continuous fun t => finU (rationalTime S.s) (C.q i.1) t y
    have heq : (fun t => finU (rationalTime S.s) (C.q i.1) t y) = fun t => recU (C.q i.1) t y := by
      funext t
      exact congrArg (recU _ t) (retr_of_mem hy.2)
    rw [heq]
    exact hy.2.1.facts.2.1
  driver := fun _ y hy t ht => by
    change recU _ t (retr _ y) = _
    rw [retr_of_mem hy.2]
    exact frozenDrv_of_le ht y.2
  configuration := fun _ y hy => configuration_of_good (rationalTime_s_pos S) hy.2

end InteractingSLE.Sec5.Aux61SlitWZ
