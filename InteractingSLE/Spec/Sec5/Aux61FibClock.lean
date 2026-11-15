/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61ActDisint
import InteractingSLE.Spec.Restart.RetEndClock

/-!
# A reference clock killed at the clock, with explicit announcing stops

Packet PROVE-AUX61-FIB, piece (F1) of `planning/handoffs/PROVE-AUX61-ACT.md` (the fibre's clock). A
`Aux61Act.DyActFibre` needs a clock source killed at its clock (`CS.U = RC.e`, so that `driving_eq_of_U_eq` gives the
fibre's completed filtration) and the kernel at the stops `min(T_N, k/2ⁿ)` of the clock's announcing sequence `T`.
For those stops to come from stops of the glued space (piece (F3)), `T` must be an **explicit** function of the
fibre's code, not one chosen by `Classical.choice` inside `Aux61R45.ClockSource.exists_referenceClock`. This file
builds the clock by hand:

* `annStop ℓ Γ U N`: the first time before `U` at which a continuous clearance reader `ℓ` of the path drops below
  `1/(N+1)`, capped at `N` (`ℓ` is a deterministic function on the fibre: in the application the distance of the
  physical point read through the inverse chart to the retained boundary, together with the distance to the window's
  complement, positive at the seed and zero at the clock);
* **`ClockSource.isAnnouncingSeq_annStop`**: these stops announce the source lifetime in the source's completed
  filtration, when `ℓ ∘ Γ` is positive before the lifetime and nonpositive at a finite lifetime;
* **`ClockSource.stronglyAdapted_of_frz`**: a driver frozen at the lifetime (almost surely) is adapted to the completed
  filtration of its own killed history (the landed `StoppedK2.measurable_frz` and completeness);
* **`ClockSource.refClockSelf`**: a `ReferenceClock` whose clock **is** (definitionally) the source lifetime, whose
  driver **is** the source driver, and whose announcing sequence **is** `annStop`; hence (`driving_eq_self`) the
  fibre's completed filtration is the reference one.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result; R77: no post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Fib

open Coupling (hitBelow IsAnnouncingSeq)
open Aux61R45 (ClockSource ReferenceClock)
open Sec7.PocketTraversal

universe u

/-! ### Explicit announcing stops -/

theorem coe_untopD_of_ne_top {a : WithTop ℝ≥0} (h : a ≠ ⊤) (d : ℝ≥0) : ((a.untopD d : ℝ≥0) : WithTop ℝ≥0) = a := by
  obtain ⟨u, rfl⟩ := WithTop.ne_top_iff_exists.1 h
  rfl

section Ann

variable {S : Type u} [MeasurableSpace S]

/-- **The explicit announcing stops**: the first time before `U ω` at which the clearance `ℓ (Γ ω t)` drops below
`1/(N+1)`, capped at `N`. -/
def annStop (ℓ : ℂ → ℝ) (Γ : S → ℝ≥0 → ℂ) (U : S → ℝ≥0∞) (N : ℕ) (ω : S) : ℝ≥0 :=
  (min (hitBelow (fun t => ℓ (Γ ω t)) (U ω) (1 / ((N : ℝ) + 1))) ((N : ℝ≥0) : WithTop ℝ≥0)).untopD 0

omit [MeasurableSpace S] in
theorem coe_annStop (ℓ : ℂ → ℝ) (Γ : S → ℝ≥0 → ℂ) (U : S → ℝ≥0∞) (N : ℕ) (ω : S) :
    ((annStop ℓ Γ U N ω : ℝ≥0) : WithTop ℝ≥0) =
      min (hitBelow (fun t => ℓ (Γ ω t)) (U ω) (1 / ((N : ℝ) + 1))) ((N : ℝ≥0) : WithTop ℝ≥0) :=
  coe_untopD_of_ne_top (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _)) 0

omit [MeasurableSpace S] in
theorem annStop_le (ℓ : ℂ → ℝ) (Γ : S → ℝ≥0 → ℂ) (U : S → ℝ≥0∞) (N : ℕ) (ω : S) :
    annStop ℓ Γ U N ω ≤ N := by
  have h := coe_annStop ℓ Γ U N ω
  have h' : ((annStop ℓ Γ U N ω : ℝ≥0) : WithTop ℝ≥0) ≤ ((N : ℝ≥0) : WithTop ℝ≥0) := h ▸ min_le_right _ _
  exact WithTop.coe_le_coe.1 h'

omit [MeasurableSpace S] in
theorem monotone_annStop (ℓ : ℂ → ℝ) (Γ : S → ℝ≥0 → ℂ) (U : S → ℝ≥0∞) (ω : S) :
    Monotone fun N => annStop ℓ Γ U N ω := by
  intro n m hnm
  refine WithTop.coe_le_coe.1 ?_
  rw [coe_annStop, coe_annStop]
  refine min_le_min (Coupling.hitBelow_anti (one_div_le_one_div_of_le (by positivity) ?_)) ?_
  · have : (n : ℝ) ≤ m := by exact_mod_cast hnm
    linarith
  · exact WithTop.coe_le_coe.2 (by exact_mod_cast hnm)

end Ann

/-! ### Announcing the source lifetime -/

namespace ClockSource

variable {S : Type u} [MeasurableSpace S] (D : ClockSource S)

/-- The trace of a clock source starts at the seed `y` (almost surely). -/
theorem ae_Γ_zero : ∀ᵐ ω ∂D.P, D.Γ ω 0 = D.y := by
  filter_upwards [D.trace] with ω hg
  exact sub_eq_zero.1 hg.1

/-- **The explicit stops announce the source lifetime** in the source's completed filtration, when the clearance
`ℓ ∘ Γ` is positive at the seed and before the lifetime and nonpositive at a finite lifetime. -/
theorem isAnnouncingSeq_annStop {ℓ : ℂ → ℝ} (hℓ : Continuous ℓ) (hℓy : 0 < ℓ D.y)
    (hΓm : ∀ t, Measurable fun ω => D.Γ ω t) (hΓc : ∀ ω, Continuous (D.Γ ω))
    (hpos : ∀ᵐ ω ∂D.P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < D.U ω → 0 < ℓ (D.Γ ω t))
    (hend : ∀ᵐ ω ∂D.P, ∀ T : ℝ≥0, (T : ℝ≥0∞) = D.U ω → ℓ (D.Γ ω T) ≤ 0) :
    IsAnnouncingSeq D.driving D.P D.U (annStop ℓ D.Γ D.U) := by
  let X : ℝ≥0 → S → ℝ := fun t ω => ℓ (D.Γ ω t)
  have ha : AdaptedBefore D.driving D.U X := by
    intro t A hA
    exact D.measurableSet_trace_before hΓm (ae_of_all _ fun _ _ _ => rfl) t (hℓ.measurable hA)
  have hc : ∀ ω, ContinuousOn (X · ω) {t : ℝ≥0 | (t : ℝ≥0∞) < D.U ω} :=
    fun ω => (hℓ.comp (hΓc ω)).continuousOn
  refine ⟨fun N => ?_, fun ω => monotone_annStop ℓ D.Γ D.U ω, fun N => ?_, ?_⟩
  · have h := (Restart.FlowStopIdentCMI.isStoppingTime_scalar_hitBelow ha hc
      (1 / ((N : ℝ) + 1))).min_const ((N : ℝ≥0))
    have e : (fun ω => ((annStop ℓ D.Γ D.U N ω : ℝ≥0) : WithTop ℝ≥0)) =
        fun ω => min (hitBelow (X · ω) (D.U ω) (1 / ((N : ℝ) + 1))) ((N : ℝ≥0) : WithTop ℝ≥0) :=
      funext fun ω => coe_annStop ℓ D.Γ D.U N ω
    rw [e]
    exact h
  · filter_upwards [hend, ae_Γ_zero D] with ω hω h0
    rcases eq_top_or_lt_top (D.U ω) with htop | hfin
    · rw [htop]
      exact ENNReal.coe_lt_top
    · set T : ℝ≥0 := (D.U ω).toNNReal with hTdef
      have hT : (T : ℝ≥0∞) = D.U ω := ENNReal.coe_toNNReal hfin.ne
      have hTℓ := hω T hT
      have hT0 : 0 < T := by
        rcases eq_zero_or_pos T with h | h
        · rw [h, h0] at hTℓ
          exact absurd hTℓ (not_le.2 hℓy)
        · exact h
      have hε : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
      have : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT0⟩
      have hlim : Tendsto (X · ω) (𝓝[<] T) (𝓝 (X T ω)) :=
        ((hℓ.comp (hΓc ω)).tendsto T).mono_left nhdsWithin_le_nhds
      have hev : ∀ᶠ s in 𝓝[<] T, s < T ∧ X s ω < 1 / ((N : ℝ) + 1) := by
        filter_upwards [self_mem_nhdsWithin,
          hlim.eventually (gt_mem_nhds (lt_of_le_of_lt hTℓ hε))] with s hs hd
        exact ⟨hs, hd⟩
      obtain ⟨s, hs, hXs⟩ := hev.exists
      have hsU : (s : ℝ≥0∞) < D.U ω := hT ▸ ENNReal.coe_lt_coe.2 hs
      have hle : ((annStop ℓ D.Γ D.U N ω : ℝ≥0) : WithTop ℝ≥0) ≤ s := by
        rw [coe_annStop]
        exact (min_le_left _ _).trans (Coupling.hitBelow_le hsU hXs)
      rw [← hT]
      exact ENNReal.coe_lt_coe.2 ((WithTop.coe_le_coe.1 hle).trans_lt hs)
  · filter_upwards [hpos] with ω hω t ht
    have h1 := Coupling.eventually_le_hitBelow (hc ω) hω ht
    have h2 : ∀ᶠ k : ℕ in atTop, (t : ℝ≥0) ≤ (k : ℝ≥0) := by
      filter_upwards [eventually_ge_atTop ⌈(t : ℝ)⌉₊] with k hk
      have : (t : ℝ) ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
      exact_mod_cast this
    obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
    refine ⟨k, WithTop.coe_le_coe.1 ?_⟩
    rw [coe_annStop]
    exact le_min hk1 (WithTop.coe_le_coe.2 hk2)

/-- **A driver frozen at the lifetime is adapted** to the completed filtration of its own killed history: the frozen
process `StoppedK2.frz U W₀` is adapted (`StoppedK2.measurable_frz`), and an almost surely equal measurable process is
adapted to a completed filtration. -/
theorem stronglyAdapted_of_frz (hW₀m : ∀ t, Measurable (D.W₀ t))
    (hfrz : ∀ᵐ ω ∂D.P, ∀ t, D.W₀ t ω = Restart.StoppedK2.frz D.U D.W₀ t ω) :
    StronglyAdapted D.driving D.W₀ := by
  intro t
  have hf : Measurable[D.driving t] (Restart.StoppedK2.frz D.U D.W₀ t) :=
    Restart.StoppedK2.measurable_frz D.adaptedBefore t
  have hm : Measurable[D.driving t] (D.W₀ t) := by
    intro A hA
    refine Coupling.measurableSet_usualAugmentation_of_ae_eq (hW₀m t hA) (hf hA) ?_
    filter_upwards [hfrz] with ω hω
    change (D.W₀ t ω ∈ A) = (Restart.StoppedK2.frz D.U D.W₀ t ω ∈ A)
    rw [hω t]
  exact hm.stronglyMeasurable

end ClockSource

/-! ### The reference clock killed at the clock -/

namespace ClockSource

variable {S : Type u} [MeasurableSpace S] (D : ClockSource S)

/-- **A reference clock killed at the clock, with explicit data** (a definition, so that its clock, driver and
announcing stops are definitionally the source lifetime, the source driver and `annStop ℓ D.Γ D.U`). Inputs: the
source driver is continuous from `0`, measurable and frozen at its lifetime; the trace is measurable and continuous;
the clearance `ℓ` is continuous, positive at the seed and before the lifetime and nonpositive at a finite lifetime; the
lifetime is the window exit (`RLC.exitTime`); positive-time trace points before the lifetime are interior; the
reference seed is not a threshold state. -/
def refClockSelf (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (θ : ℝ) (V : Set ℂ)
    (hseed : ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b J D.y θ)
      (flowLineRhoR κ b J D.y θ) 0 (flowLineXL b J D.y) (flowLineXR b J D.y))
    (hW₀c : ∀ ω, Continuous (D.W₀ · ω)) (hW₀0 : ∀ ω, D.W₀ 0 ω = 0) (hW₀m : ∀ t, Measurable (D.W₀ t))
    (hfrz : ∀ᵐ ω ∂D.P, ∀ t, D.W₀ t ω = Restart.StoppedK2.frz D.U D.W₀ t ω)
    (hΓm : ∀ t, Measurable fun ω => D.Γ ω t) (hΓc : ∀ ω, Continuous (D.Γ ω))
    (ℓ : ℂ → ℝ) (hℓ : Continuous ℓ) (hℓy : 0 < ℓ D.y)
    (hpos : ∀ᵐ ω ∂D.P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < D.U ω → 0 < ℓ (D.Γ ω t))
    (hend : ∀ᵐ ω ∂D.P, ∀ T : ℝ≥0, (T : ℝ≥0∞) = D.U ω → ℓ (D.Γ ω T) ≤ 0)
    (hexit : ∀ᵐ ω ∂D.P, D.U ω = RLC.exitTime V (D.Γ ω) (D.U ω))
    (hinterior : ∀ᵐ ω ∂D.P, ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < D.U ω → D.Γ ω t ∈ QuantumZipper.H) :
    ReferenceClock D κ b J θ V :=
  have hes : IsStoppingTime D.driving fun ω => (D.U ω : WithTop ℝ≥0) :=
    Ito.isStoppingTime_lifetime D.adaptedBefore
  have hWa : StronglyAdapted D.driving D.W₀ := stronglyAdapted_of_frz D hW₀m hfrz
  have hT := isAnnouncingSeq_annStop D hℓ hℓy hΓm hΓc hpos hend
  have hX : IsMeasurableKilledDriving D.W₀ (geomLW D.W₀ fun _ => flowLineXL b J D.y)
      (geomRW D.W₀ fun _ => flowLineXR b J D.y) D.U :=
    Coupling.isMeasurableKilledDriving_of_adaptedBefore
      (MartChar.adaptedBefore_of_stronglyAdapted hes hWa)
      (fun i => MartChar.adaptedBefore_of_stronglyAdapted hes
        (stronglyAdapted_geomLW hWa hW₀c measurable_const i))
      (fun j => MartChar.adaptedBefore_of_stronglyAdapted hes
        (stronglyAdapted_geomRW hWa hW₀c measurable_const j))
  have hag : ∀ᵐ ω ∂D.P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < D.U ω → D.W₀ t ω = D.W₀ t ω :=
    ae_of_all _ fun _ _ _ => rfl
  have hth : ∀ᵐ ω ∂D.P, D.U ω ≤ MartChar.thresholdTime
      (flowLineRhoL κ b J D.y θ) (flowLineRhoR κ b J D.y θ) (D.W₀ · ω)
      (fun i t => geomLW D.W₀ (fun _ => flowLineXL b J D.y) i t ω)
      (fun j t => geomRW D.W₀ (fun _ => flowLineXR b J D.y) j t ω) := by
    apply Aux61R45.threshold_of_interior_trace hW₀0 hW₀c (Restart.FlowStopIdentLL.flowLineXL_nonpos_seed b J D.y)
      (Restart.FlowStopIdentLL.flowLineXR_nonneg_seed b J D.y) hseed D.trace
    filter_upwards [hinterior] with ω hH t ht hte
    change 0 < (D.Γ ω t - (D.y : ℂ)).im
    have hHt : 0 < (D.Γ ω t).im := hH t ht hte
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using hHt
  ReferenceClock.mk D.U (Restart.FlowStopIdentLift.measurable_lifetime D.killed) (fun _ => le_rfl) hexit D.W₀
    hW₀0 hW₀c hWa hes (annStop ℓ D.Γ D.U) hT hag hX
    (D.announcing_reference (fun _ => le_rfl) hW₀0 hW₀c hag hX hT) hth D.trace

end ClockSource

/-- **The fibre's completed filtration is the reference one** for a reference clock whose clock is the source
lifetime (`Aux61Act.driving_eq_of_U_eq`). -/
theorem driving_eq_self {S : Type u} [MeasurableSpace S] {D : ClockSource S} {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    {θ : ℝ} {V : Set ℂ} (C : ReferenceClock D κ b J θ V) (hC : ∀ ω, C.e ω = D.U ω) :
    D.driving = drivingFiltration D.P C.killed :=
  Aux61Act.driving_eq_of_U_eq C fun ω => (hC ω).symm

end InteractingSLE.Sec5.Aux61Fib
