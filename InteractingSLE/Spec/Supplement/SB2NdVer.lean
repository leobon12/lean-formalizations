/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NdAdapt
import InteractingSLE.Spec.Supplement.SB2VsVer

/-!
# F2b′'s versions at a good sample

Packet PROVE-AUX61-NOJUMP (round 21, D34, component D). At a good sample of the stop inputs (`StopIn.Gs`), the
sample-level facts behind the version fields (SB2(1)'s `SB2VsVer` for the relative stage curve):

* the clock is the relative lifetime from B's lifetime on and strictly below it before (`a_eq_capLife_of_le`,
  `a_lt_capLife_of_lt`); live times are before B's lifetime (**`lt_life_of_lt`**); the clock reaches every level below
  a stop (**`reach_of_mem`**);
* **`V_le_thr_of_mem`**: the stop is at most the threshold of its frozen driver on the sample's type cell (the
  relative collision core `Vs.le_thr_of_avoid`, since the gauge is positive before the stop);
* **`ann_of_mem`**: the stops are announced;
* **`trace_of_mem`**: the frozen driver has a Loewner trace whose value at the clock is the chart at B's point,
  wherever that point is in the chart's domain;
* `thr_congr`: the threshold only sees the force points at the sample.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Nd

open Vs Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId Supp8.GB6.RelDrv.Version Supp8.Q3Stop Sec7.PocketTraversal
  Sec7.Lemma71C Restart Exist Exist.Staged Lv Ms Mf WalkSide LocalSets Lk LuM Nc Dv Vr

/-- **The threshold only sees the force points at the sample.** -/
theorem thr_congr {Ω : Type*} {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ)
    {xL xL' : Ω → Fin nL → ℝ} {xR xR' : Ω → Fin nR → ℝ} {ω : Ω} (hL : xL ω = xL' ω) (hR : xR ω = xR' ω) :
    FCDet.thr ρL ρR W xL xR ω = FCDet.thr ρL ρR W xL' xR' ω := by
  unfold FCDet.thr geomLW geomRW
  simp only [hL, hR]

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ}
  {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ} {ψ : ℝ}

namespace StopIn

variable (T : StopIn P κ b jumps E u l k ℓ ψ)

theorem a_eq_capLife_of_le {ω : Ω} (hω : ω ∈ T.S.Eg) {t : ℝ≥0} (ht : bLife b jumps E ℓ ω ≤ t) :
    T.S.a t ω = capLife (T.S.ρM ω) := by
  rw [T.S.a_eq hω, if_neg (not_lt.2 ht)]

theorem a_lt_capLife_of_lt {ω : Ω} (hω : ω ∈ T.S.Eg) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < bLife b jumps E ℓ ω) :
    T.S.a t ω < capLife (T.S.ρM ω) := by
  rw [T.S.a_eq hω, if_pos ht]
  exact (T.S.driven_ρM ω).ofReal_capClock_lt (uOf_nonneg (beforeL_of_lt ht))

/-- **Live times are before B's lifetime.** -/
theorem lt_life_of_lt {m : ℕ} {ω : Ω} (hω : ω ∈ T.Gs) {t : ℝ≥0} (ht : T.S.a t ω < T.V m ω) :
    (t : ℝ≥0∞) < bLife b jumps E ℓ ω := by
  by_contra hle
  rw [not_lt] at hle
  rw [T.a_eq_capLife_of_le (T.Gs_subset_Eg hω) hle, T.V_eq hω] at ht
  exact absurd (T.Vstop_lt hω) (not_lt.2 ht.le)

/-- **The clock reaches every level below a stop.** -/
theorem reach_of_mem {m : ℕ} {ω : Ω} (hω : ω ∈ T.Gs) {q : ℝ≥0} (hq : (q : ℝ≥0∞) < T.V m ω) :
    ∃ t, (q : ℝ≥0∞) ≤ T.S.a t ω := by
  have hEg := T.Gs_subset_Eg hω
  have hq' : (q : ℝ≥0∞) < capLife (T.S.ρM ω) := by rw [T.V_eq hω] at hq; exact hq.trans (T.Vstop_lt hω)
  by_cases hL : bLife b jumps E ℓ ω = ⊤
  · obtain ⟨n, hn⟩ := exists_lt_capClock_of_lt_capLife (γ := T.S.ρM ω) (s := q)
      (by rw [ENNReal.ofReal_coe_nnreal]; exact hq')
    refine ⟨n, ?_⟩
    rw [T.S.a_eq hω.1, if_pos (by rw [hL]; exact ENNReal.coe_lt_top)]
    have hu : uOf (bLife b jumps E ℓ ω) ((n : ℝ≥0) : ℝ) = n := by unfold uOf; rw [if_pos hL]; simp
    rw [hu, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hn.le
  · refine ⟨(bLife b jumps E ℓ ω).toNNReal, ?_⟩
    rw [T.a_eq_capLife_of_le hEg (by rw [ENNReal.coe_toNNReal hL])]
    exact hq'.le

/-- **The gauge positive before the stop keeps the trace off the type's bad set.** -/
theorem notMem_badSet {m : ℕ} {ω : Ω} (hω : ω ∈ T.Gs) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T.Vstop m ω) :
    capTrace (T.S.ρM ω) t ∉ badSet (cellXL κ ψ T.cw (angleWordType κ ψ (T.cw ω)) ω)
      (cellXR κ ψ T.cw (angleWordType κ ψ (T.cw ω)) ω) (typedRhoL (angleWordType κ ψ (T.cw ω)))
      (typedRhoR (angleWordType κ ψ (T.cw ω))) := by
  obtain ⟨hV, -, -, -, hpos⟩ := T.sample hω m
  rw [hV] at ht
  have h1 := hpos t (by exact_mod_cast ht)
  have h2 : 0 < relGauge κ ψ T.cw T.types ω (capTrace (T.S.ρM ω) t) := lt_of_lt_of_le h1 (min_le_left _ _)
  rw [relGauge_eq κ ψ T.cw T.types ((T.rel ω hω).cover) rfl] at h2
  intro hmem
  have h3 : infEDist (capTrace (T.S.ρM ω) t) (closure (badSet (cellXL κ ψ T.cw (angleWordType κ ψ (T.cw ω)) ω)
      (cellXR κ ψ T.cw (angleWordType κ ψ (T.cw ω)) ω) (typedRhoL (angleWordType κ ψ (T.cw ω)))
      (typedRhoR (angleWordType κ ψ (T.cw ω))))) = 0 := infEDist_zero_of_mem (subset_closure hmem)
  unfold cellGauge at h2
  rw [h3, zero_min] at h2
  exact lt_irrefl _ h2

/-- **The stop is at most the threshold of the frozen driver on the sample's type cell.** -/
theorem V_le_thr_of_mem {m : ℕ} {ω : Ω} (hω : ω ∈ T.Gs) {w : WordType}
    (hw : angleWordType κ ψ (T.cw ω) = w) :
    T.V m ω ≤ FCDet.thr (typedRhoL w) (typedRhoR w) (T.W m) (cellXL κ ψ T.cw w) (cellXR κ ψ T.cw w) ω := by
  subst hw
  have htop := T.Vstop_ne_top (m := m) hω
  have hg := T.isGeneratingTrace_Wr ω (V := T.Vstop m ω) (T.Vstop_lt hω)
  rw [T.V_eq hω, ← ENNReal.coe_toNNReal htop]
  refine le_thr_of_avoid (T.continuous_W m) (T.W_zero m)
    (FCDet.isOrderedForceWord_typeXL (T.cw ω)).2.1
    (FCDet.isOrderedForceWord_typeXL (T.cw ω)).2.2.2 (Γ := capTrace (T.S.ρM ω)) ?_ fun t ht =>
      T.notMem_badSet (m := m) hω ?_
  · rw [ENNReal.coe_toNNReal htop]
    exact Sec5.CrossRestart.isGeneratingTrace_congr_drive (w := fun t => T.W m t ω) hg
      fun s hs => T.W_eq_Wr hω hs.le
  · exact (ENNReal.coe_lt_coe.2 ht).trans_eq (ENNReal.coe_toNNReal htop)

/-- **The stops are announced** by the record-path rules along the frozen driver. -/
theorem ann_of_mem {m : ℕ} {ω : Ω} (hω : ω ∈ T.Gs) :
    (∀ n, annRules gaugeRead m n (T.record ω, fun s => T.W m s ω) < T.V m ω) ∧
      ⨆ n, annRules gaugeRead m n (T.record ω, fun s => T.W m s ω) = T.V m ω := by
  obtain ⟨-, -, hann, hsup, -⟩ := T.sample hω m
  have he : ∀ n, annRules gaugeRead m n (T.record ω, fun s => T.W m s ω) =
      annRules gaugeRead m n (T.record ω, fun s => T.Wr s ω) := fun n =>
    isPathRule_annRules isCausal_gaugeRead m n _ _ _ fun q hq => (T.W_eq_Wr hω (hq.trans (hann n).le)).symm
  simp only [he, T.V_eq hω]
  exact ⟨hann, hsup⟩

/-- **The frozen driver's Loewner trace reads B's point through the chart at the clock.** -/
theorem trace_of_mem {m : ℕ} {ω : Ω} (hω : ω ∈ T.Gs) {t : ℝ≥0} (ht : T.S.a t ω < T.V m ω) :
    ∃ ηr : ℝ → ℂ, IsLoewnerTrace (fun s : ℝ => T.W m s.toNNReal ω) ηr ∧
      ∀ s : ℝ≥0, s ≤ t → (0 : ℝ≥0) ≤ s →
        bPc κ b jumps E ℓ ω s ∈ ((Mo.hullChart (fillH (T.S.K ω)) (T.S.x₀ ω)).dom : Set ℂ) →
        ηr (T.S.a s ω).toReal = (Mo.hullChart (fillH (T.S.K ω)) (T.S.x₀ ω)).1 (bPc κ b jumps E ℓ ω s) := by
  have hEg := T.Gs_subset_Eg hω
  have hd := T.S.driven_ρM ω
  have hpos := T.Vstop_pos (m := m) hω
  have htop := T.Vstop_ne_top (m := m) hω
  set v : ℝ≥0 := (T.Vstop m ω).toNNReal with hv
  have hvc : (v : ℝ≥0∞) = T.Vstop m ω := ENNReal.coe_toNNReal htop
  have hv0 : 0 < v := by rw [← ENNReal.coe_lt_coe, hvc]; exact hpos
  obtain ⟨ηr, hLT, heq⟩ := exists_loewnerTrace_min hv0 (by rw [hvc]; exact T.Vstop_lt hω) (T.Wr_zero ω)
    (T.continuousOn_Wr ω) fun V hV => T.isGeneratingTrace_Wr ω hV
  refine ⟨ηr, ?_, fun s hst _ hdom => ?_⟩
  · have e : (fun s : ℝ => T.W m s.toNNReal ω) = fun r : ℝ => T.Wr (min r.toNNReal v) ω :=
      funext fun r => T.W_of_mem hω _
    rw [e]; exact hLT
  · have has : T.S.a s ω < T.Vstop m ω := by
      rw [← T.V_eq hω]; exact lt_of_le_of_lt (T.S.monotone_a ω hst) ht
    have hsL : (s : ℝ≥0∞) < bLife b jumps E ℓ ω := by
      by_contra hle
      rw [not_lt] at hle
      rw [T.a_eq_capLife_of_le hEg hle] at has
      exact absurd (T.Vstop_lt hω) (not_lt.2 has.le)
    have hb := beforeL_of_lt hsL
    have has' : T.S.a s ω = ENNReal.ofReal (capClock (T.S.ρM ω) (uOf (bLife b jumps E ℓ ω) s)) := by
      rw [T.S.a_eq hEg, if_pos hsL]
    have hc0 := hd.capClock_nonneg (uOf_nonneg hb)
    have htoR : (T.S.a s ω).toReal = capClock (T.S.ρM ω) (uOf (bLife b jumps E ℓ ω) s) := by
      rw [has', ENNReal.toReal_ofReal hc0]
    have hlt : ((T.S.a s ω).toNNReal : ℝ≥0∞) < v := by
      rw [ENNReal.coe_toNNReal (ne_top_of_lt has), hvc]; exact has
    have h1 : ηr (T.S.a s ω).toReal = capTrace (T.S.ρM ω) (T.S.a s ω).toNNReal := by
      rw [← heq _ hlt]; rfl
    rw [h1]
    unfold capTrace
    have h2 : ((T.S.a s ω).toNNReal : ℝ) = capClock (T.S.ρM ω) (uOf (bLife b jumps E ℓ ω) s) := by
      rw [← htoR]; rfl
    rw [h2, hd.capInv_eq (uOf_nonneg hb), T.S.ρM_eq hEg]
    show canonVal (T.S.K ω) (T.S.x₀ ω) (bPc κ b jumps E ℓ ω) (bLife b jumps E ℓ ω)
      (cTime (bLife b jumps E ℓ ω) (uOf (bLife b jumps E ℓ ω) s)) = _
    rw [cTime_uOf hb, Real.toNNReal_coe]
    have hdom' : bPc κ b jumps E ℓ ω s ∈ H \ fillH (T.S.K ω) := by
      rwa [Mo.coe_dom_hullChart (Mo.isHPHull_fillH T.S.hKc T.S.hKp ω)] at hdom
    unfold canonVal
    rw [if_pos ⟨hsL.le, hdom'⟩]

end StopIn

end InteractingSLE.Theorem14.SB.Nd
