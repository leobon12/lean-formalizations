/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61FibDataCode

/-!
# Restart paths completed along their selected access

The successor landing condition reads the left-time limit of the interior
chart path. It imposes no limit along other accesses to the physical endpoint.
The completed path uses that same left-time limit at its exit.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec5.Aux61GInst

open Aux61FibData

/-- Landing along the actual approaching path, at a finite first contact. -/
def HasAccessLanding {X : Type*} (E : Set X) (c : X → Chart)
    (ρ : X → ℝ≥0 → ℂ) (T : X → ℝ≥0∞) (V : Set ℂ) : Prop :=
  ∀ x ∈ E, 0 < T x → Aux61FibData.exitTime E c ρ T V x = T x → T x < ⊤ →
    ∃ L : ℂ, L ∉ V ∧ Tendsto (inPath E c ρ T x) (𝓝[<] (T x).toNNReal) (𝓝 L)

/-- Times strictly below a positive end time, converging to it. -/
def beforeEnd (e : ℝ≥0) (n : ℕ) : ℝ≥0 := e * (1 - (1 / 2 : ℝ≥0) ^ n)

theorem beforeEnd_lt {e : ℝ≥0} (he : 0 < e) (n : ℕ) : beforeEnd e n < e := by
  exact mul_lt_of_lt_one_right he (tsub_lt_self zero_lt_one (pow_pos (by norm_num) n))

theorem tendsto_beforeEnd (e : ℝ≥0) : Tendsto (beforeEnd e) atTop (𝓝 e) := by
  have h := ((tendsto_const_nhds (x := (1 : ℝ≥0))).sub
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ≥0) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ≥0) < 1))).const_mul e
  change Tendsto (fun n => e * (1 - (1 / 2 : ℝ≥0) ^ n)) atTop (𝓝 e)
  simpa only [tsub_zero, mul_one] using h

theorem tendsto_beforeEnd_left {e : ℝ≥0} (he : 0 < e) :
    Tendsto (beforeEnd e) atTop (𝓝[<] e) :=
  tendsto_nhdsWithin_iff.2 ⟨tendsto_beforeEnd e, Eventually.of_forall (beforeEnd_lt he)⟩

open scoped Classical in
/-- The left-time endpoint of the chart path. -/
def accessExitPoint {X : Type*} (E : Set X) (c : X → Chart)
    (ρ : X → ℝ≥0 → ℂ) (T : X → ℝ≥0∞) (V : Set ℂ) (x : X) : ℂ :=
  limUnder (𝓝[<] (exitNN E c ρ T V x)) (inPath E c ρ T x)

open scoped Classical in
/-- The interior chart path completed by its selected access, frozen after exit. -/
def accessExitPath {X : Type*} (E : Set X) (c : X → Chart)
    (ρ : X → ℝ≥0 → ℂ) (T : X → ℝ≥0∞) (V : Set ℂ) (x : X) (u : ℝ≥0) : ℂ :=
  if x ∈ exitEv E c ρ T V then
    if u < exitNN E c ρ T V x then inPath E c ρ T x u else accessExitPoint E c ρ T V x
  else 0

section Restart

variable {X : Type*} [MeasurableSpace X] {E : Set X} {c : X → Chart}
  {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ}
  (hs : IsRestartSpec E c ρ T) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
  (hland : HasAccessLanding E c ρ T V)

include hs hV hV0 hland

omit hV0 in
/-- The selected access supplies the exit limit, including an exit before contact. -/
theorem exists_accessExitPoint {x : X} (hx : x ∈ exitEv E c ρ T V) :
    ∃ L : ℂ, L ∉ V ∧ Tendsto (inPath E c ρ T x)
      (𝓝[<] (exitNN E c ρ T V x)) (𝓝 L) := by
  have he := IsRestartSpec.coe_exitNN hx
  have heT : ((exitNN E c ρ T V x : ℝ≥0) : ℝ≥0∞) ≤ T x := he ▸ IsRestartSpec.exitTime_le x
  rcases lt_or_eq_of_le heT with hlt | heq
  · refine ⟨inPath E c ρ T x (exitNN E c ρ T V x),
      hs.inPath_exitTime_notMem hx.1.1 hV (he ▸ hlt), ?_⟩
    exact ((hs.continuousOn_inPath hx.1.1).continuousAt
      ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds hlt)).tendsto.mono_left
        nhdsWithin_le_nhds
  · have hfin : T x < ⊤ := heq ▸ ENNReal.coe_lt_top
    have htime : exitNN E c ρ T V x = (T x).toNNReal := by rw [← heq]; rfl
    rw [htime]
    exact hland x hx.1.1 hx.1.2 (he.symm.trans heq) hfin

omit hland in
theorem exitNN_pos {x : X} (hx : x ∈ exitEv E c ρ T V) : 0 < exitNN E c ρ T V x := by
  have he := hs.exitTime_pos hx.1.1 hV hV0 hx.1.2
  rw [← IsRestartSpec.coe_exitNN hx] at he
  exact_mod_cast he

/-- The selected exit point is the actual left-time limit, and lies outside the window. -/
theorem accessExitPoint_spec {x : X} (hx : x ∈ exitEv E c ρ T V) :
    accessExitPoint E c ρ T V x ∉ V ∧ Tendsto (inPath E c ρ T x)
      (𝓝[<] (exitNN E c ρ T V x)) (𝓝 (accessExitPoint E c ρ T V x)) := by
  have : (𝓝[<] (exitNN E c ρ T V x)).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨0, exitNN_pos hs hV hV0 hx⟩
  obtain ⟨L, hLV, hL⟩ := exists_accessExitPoint hs hV hland hx
  have he : accessExitPoint E c ρ T V x = L := hL.limUnder_eq
  rw [he]
  exact ⟨hLV, hL⟩

end Restart

end InteractingSLE.Sec5.Aux61GInst
