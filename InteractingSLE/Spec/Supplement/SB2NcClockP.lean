/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NcLoc

/-!
# F2b′'s relative curve and clock as processes

Packet PROVE-AUX61-NOJUMP (round 21, D34, component B). For F2b′'s stage objects `S` (`StageObj`):

* `S.ρM`: the relative stage curve on the good event `S.Eg`, the vertical ray off it — driven at every sample and
  measurable at every time (**`measurable_ρM`**, `measurable_bRel`);
* `S.a`: the relative clock in B's time, `Vc.clockOf (bLift) 0 L` on `S.Eg`, `0` off it — continuous, monotone, `0`
  at `0` at every sample (**`continuous_a`**, `monotone_a`, `a_zero`), equal on `S.Eg` to
  `capClock ρ (uOf L t)` before `L` and to `capLife ρ` after (**`a_eq`**), and measurable (**`measurable_a`**,
  through `measurable_ofReal_capClock_rand`: the capacity at a random parameter is a supremum over rationals).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.SB.Nc

open Sec7.PocketTraversal Sec7.Lemma71C Dv Lk Exist Exist.Staged Exist.StagedLaw LuM

/-- **The capacity of a driven family at a random parameter is measurable.** -/
theorem measurable_ofReal_capClock_rand {Ω : Type*} [MeasurableSpace Ω] {ρ : Ω → ℝ → ℂ}
    (hd : ∀ ω, IsDrivenCurve (ρ ω)) (hm : ∀ t, 0 ≤ t → Measurable fun ω => ρ ω t) {v : Ω → ℝ}
    (hv : Measurable v) (hv0 : ∀ ω, 0 ≤ v ω) :
    Measurable fun ω => ENNReal.ofReal (capClock (ρ ω) (v ω)) := by
  classical
  set T : ℚ → Ω → ℝ≥0∞ := fun q ω =>
    if h : (0 : ℝ) ≤ q then ({ω | (q : ℝ) ≤ v ω}.indicator fun ω => ENNReal.ofReal (capClock (ρ ω) q)) ω
    else 0 with hT
  have hTm : ∀ q, Measurable (T q) := fun q => by
    by_cases hq : (0 : ℝ) ≤ q
    · have e : T q = {ω | (q : ℝ) ≤ v ω}.indicator fun ω => ENNReal.ofReal (capClock (ρ ω) q) := by
        funext ω; simp only [hT, hq, dite_true]
      rw [e]
      exact (ENNReal.measurable_ofReal.comp (Supp8.GB6.CoordB.measurable_capClock hd hm hq)).indicator
        (measurableSet_le measurable_const hv)
    · have e : T q = fun _ => 0 := by funext ω; simp only [hT, hq, dite_false]
      rw [e]; exact measurable_const
  have e : (fun ω => ENNReal.ofReal (capClock (ρ ω) (v ω))) = fun ω => ⨆ q : ℚ, T q ω := by
    funext ω
    have hmono := (hd ω).strictMonoOn_capClock.monotoneOn
    have hcont := (hd ω).continuousOn_capClock
    refine le_antisymm ?_ (iSup_le fun q => ?_)
    · -- rational approximations from below
      set qn : ℕ → ℚ := fun n => (⌊v ω * ((n : ℝ) + 1)⌋ : ℚ) / ((n : ℚ) + 1) with hqn
      have hq0 : ∀ n, (0 : ℝ) ≤ qn n := fun n => by
        simp only [hqn]; push_cast
        exact div_nonneg (by exact_mod_cast Int.floor_nonneg.2 (by have := hv0 ω; positivity)) (by positivity)
      have hqv : ∀ n, (qn n : ℝ) ≤ v ω := fun n => by
        simp only [hqn]; push_cast
        rw [div_le_iff₀ (by positivity)]; exact Int.floor_le _
      have hqlim : Tendsto (fun n => (qn n : ℝ)) atTop (𝓝 (v ω)) := by
        have hlow : ∀ n : ℕ, v ω - 1 / ((n : ℝ) + 1) ≤ qn n := fun n => by
          simp only [hqn]; push_cast
          rw [le_div_iff₀ (by positivity), sub_mul, one_div_mul_cancel (by positivity)]
          linarith [Int.lt_floor_add_one (v ω * ((n : ℝ) + 1))]
        have h1 : Tendsto (fun n : ℕ => v ω - 1 / ((n : ℝ) + 1)) atTop (𝓝 (v ω)) := by
          have := (tendsto_const_nhds (x := v ω)).sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
          simpa using this
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds hlow hqv
      have hcl : Tendsto (fun n => ENNReal.ofReal (capClock (ρ ω) (qn n))) atTop
          (𝓝 (ENNReal.ofReal (capClock (ρ ω) (v ω)))) := by
        have := (hcont (v ω) (mem_Ici.2 (hv0 ω))).tendsto.comp (tendsto_nhdsWithin_iff.2
          ⟨hqlim, Eventually.of_forall fun n => mem_Ici.2 (hq0 n)⟩)
        exact (ENNReal.continuous_ofReal.tendsto _).comp this
      refine le_of_tendsto' hcl fun n => le_iSup_of_le (qn n) ?_
      simp only [hT, hq0 n, dite_true]
      rw [indicator_of_mem (show ω ∈ {ω | ((qn n : ℚ) : ℝ) ≤ v ω} from hqv n)]
    · by_cases hq : (0 : ℝ) ≤ q
      · simp only [hT, hq, dite_true]
        by_cases hqv : (q : ℝ) ≤ v ω
        · rw [indicator_of_mem (show ω ∈ {ω | (q : ℝ) ≤ v ω} from hqv)]
          exact ENNReal.ofReal_le_ofReal (hmono hq (hv0 ω) hqv)
        · rw [indicator_of_notMem (show ω ∉ {ω | (q : ℝ) ≤ v ω} from hqv)]; exact zero_le
      · simp only [hT, hq, dite_false]; exact zero_le
  rw [e]
  exact Measurable.iSup hTm

theorem measurable_uOf {Ω : Type*} [MeasurableSpace Ω] {L : Ω → ℝ≥0∞} (hL : Measurable L) (t : ℝ) :
    Measurable fun ω => uOf (L ω) t := by
  classical
  unfold uOf
  exact Measurable.ite (hL (measurableSet_singleton ⊤)) measurable_const
    (measurable_const.div ((ENNReal.measurable_toReal.comp hL).sub measurable_const))

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ}
  {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ}

namespace StageObj

variable (S : StageObj P κ b jumps E u l k ℓ)

open Classical in
/-- The relative stage curve on the good event, the vertical ray off it. -/
def ρM (ω : Ω) : ℝ → ℂ :=
  if ω ∈ S.Eg then bRel κ b jumps E ℓ S.K S.x₀ ω else fun t : ℝ => (t : ℂ) * Complex.I

theorem ρM_eq {ω : Ω} (hω : ω ∈ S.Eg) : S.ρM ω = bRel κ b jumps E ℓ S.K S.x₀ ω := by
  simp only [ρM, hω, ↓reduceIte]

theorem driven_ρM (ω : Ω) : IsDrivenCurve (S.ρM ω) := by
  by_cases hω : ω ∈ S.Eg
  · rw [S.ρM_eq hω]; exact (S.good ω hω).driven
  · simp only [ρM, hω, ↓reduceIte]; exact isDrivenCurve_vert

theorem bLife_eq {ω : Ω} (hω : ω ∈ S.Eg) : bLife b jumps E ℓ ω = (S.Ê ℓ ω).2 := (S.good ω hω).agree.2.1 ℓ

theorem bPc_eq {ω : Ω} (hω : ω ∈ S.Eg) :
    bPc κ b jumps E ℓ ω = pcPt (wRun κ (-(Real.pi / 2)) b jumps (fun j => S.Ê j ω) ℓ) (S.Ê ℓ ω) := by
  have hag := (S.good ω hω).agree
  have hl := (S.good ω hω).stage.2
  unfold bPc
  rw [Nv.pcPt_congr _ (hag.2.2 ℓ hl), hag.1 ℓ]

theorem launch_Ê {ω : Ω} (hω : ω ∈ S.Eg) :
    (wRun κ (-(Real.pi / 2)) b jumps (fun j => S.Ê j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
  have hl := (S.good ω hω).stage.2
  rw [show wRun κ (-(Real.pi / 2)) b jumps (fun j => S.Ê j ω) (ℓ + 1) = _ from ((S.good ω hω).agree.1 (ℓ + 1)).symm]
  exact hl

theorem measurable_ρM (hb : IsPiecewiseConstantBoundaryData b jumps) (r : ℝ) (hr : 0 ≤ r) :
    Measurable fun ω => S.ρM ω r := by
  classical
  have hKm : Restart.IsDyadicHitMeasurable S.K := fun n q => (S.hK n q).1
  have h := measurable_bRel (E := E) (ℓ := ℓ) hb S.hÊm S.hÊreg S.hÊP hKm S.hKc S.hKp (S.hx₀.mono inf_le_left le_rfl)
    S.hEg.1 (fun ω hω => S.launch_Ê hω) (fun ω hω => S.bPc_eq hω) (fun ω hω => S.bLife_eq hω)
    (fun ω hω => (S.good ω hω).pos) (fun ω hω => (S.good ω hω).driven) r hr
  have e : (fun ω => S.ρM ω r) = (fun ω => if ω ∈ S.Eg then bRel κ b jumps E ℓ S.K S.x₀ ω r else 0) +
      S.Egᶜ.indicator fun _ => (r : ℂ) * Complex.I := by
    funext ω
    by_cases hω : ω ∈ S.Eg
    · simp [ρM, hω]
    · simp [ρM, hω]
  rw [e]
  exact h.add (measurable_const.indicator S.hEg.1.compl)

open Classical in
/-- **The relative clock** in B's time (`0` off the good event). -/
def a (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  if ω ∈ S.Eg then Vc.clockOf (bLift κ b jumps E ℓ S.K S.x₀ ω) 0 (bLife b jumps E ℓ ω) t else 0

theorem a_of_mem {ω : Ω} (hω : ω ∈ S.Eg) (t : ℝ≥0) :
    S.a t ω = Vc.clockOf (bLift κ b jumps E ℓ S.K S.x₀ ω) 0 (bLife b jumps E ℓ ω) t := by
  simp only [a, hω, ↓reduceIte]

theorem a_of_notMem {ω : Ω} (hω : ω ∉ S.Eg) (t : ℝ≥0) : S.a t ω = 0 := by simp only [a, hω, ↓reduceIte]

theorem a_eq {ω : Ω} (hω : ω ∈ S.Eg) (t : ℝ≥0) :
    S.a t ω = if (t : ℝ≥0∞) < bLife b jumps E ℓ ω then
      ENNReal.ofReal (capClock (S.ρM ω) (uOf (bLife b jumps E ℓ ω) t)) else capLife (S.ρM ω) := by
  rw [S.a_of_mem hω, S.ρM_eq hω]
  exact clockOf_canonVal (S.good ω hω).driven (S.good ω hω).pos t

theorem continuous_a (ω : Ω) : Continuous fun t => S.a t ω := by
  by_cases hω : ω ∈ S.Eg
  · simp only [S.a_of_mem hω]
    exact continuous_clockOf_canonVal (S.good ω hω).driven (S.good ω hω).pos
  · simp only [S.a_of_notMem hω]; exact continuous_const

theorem monotone_a (ω : Ω) : Monotone fun t => S.a t ω := by
  by_cases hω : ω ∈ S.Eg
  · simp only [S.a_of_mem hω]; exact Vc.monotone_clockOf _ _ _
  · simp only [S.a_of_notMem hω]; exact monotone_const

theorem a_zero (ω : Ω) : S.a 0 ω = 0 := by
  by_cases hω : ω ∈ S.Eg
  · have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < bLife b jumps E ℓ ω := by
      rw [ENNReal.coe_zero]; exact pos_iff_ne_zero.2 (S.good ω hω).pos
    rw [S.a_eq hω]
    simp only [h0, ↓reduceIte, NNReal.coe_zero, uOf_zero, (S.driven_ρM ω).capClock_zero, ENNReal.ofReal_zero]
  · exact S.a_of_notMem hω 0

theorem measurable_a (hb : IsPiecewiseConstantBoundaryData b jumps) (t : ℝ≥0) : Measurable (S.a t) := by
  classical
  have hLm : Measurable fun ω => (S.Ê ℓ ω).2 := measurable_snd.comp (S.hÊm ℓ)
  have hρ := fun r hr => S.measurable_ρM hb r hr
  have e : S.a t = fun ω => if ω ∈ S.Eg then (if (t : ℝ≥0∞) < (S.Ê ℓ ω).2 then
      ENNReal.ofReal (capClock (S.ρM ω) (max (uOf (S.Ê ℓ ω).2 t) 0)) else capLife (S.ρM ω)) else 0 := by
    funext ω
    by_cases hω : ω ∈ S.Eg
    · rw [S.a_eq hω, S.bLife_eq hω]
      simp only [hω, ↓reduceIte]
      split_ifs with ht
      · rw [max_eq_left (uOf_nonneg (beforeL_of_lt ht))]
      · rfl
    · rw [S.a_of_notMem hω]; simp only [hω, ↓reduceIte]
  rw [e]
  refine Measurable.ite S.hEg.1 (Measurable.ite (measurableSet_lt measurable_const hLm) ?_
    (Supp8.GB6.CoordB.measurable_capLife S.driven_ρM hρ)) measurable_const
  exact measurable_ofReal_capClock_rand S.driven_ρM hρ ((measurable_uOf hLm t).max measurable_const)
    fun ω => le_max_right _ _

end StageObj

end

end InteractingSLE.Theorem14.SB.Nc
