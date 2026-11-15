/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NcDense
import InteractingSLE.Spec.Supplement.SB2NvPt

/-!
# F2b′'s relative stage curve is measurable at every time

Packet PROVE-AUX61-NOJUMP (round 21, D34, component B). **`measurable_bRel`**: on a measurable event `M` where the
relative stage curve `bRel` is driven, B's piece is that of a measurable family `Ê` with regular launches at every
sample (PROVE-GW2-GEOM2's `Nv.exists_regular_version`), and B launches, the curve at every time `r ≥ 0` is measurable.
It is read at the rational parameters whose B-time is good (`Lk.measurable_of_dense_good`): there it is the hull
chart at B's point (`measurable_indicator_hullChart_rand`, `Nv.measurable_pcPt_at`), and these parameters are dense
(`exists_rat_good`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Nc

open Sec7.PocketTraversal Sec7.Lemma71C Dv Lk Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep Restart

theorem cTime_le_any {L : ℝ≥0∞} {u : ℝ} (hu : 0 ≤ u) : ((cTime L u : ℝ≥0) : ℝ≥0∞) ≤ L := by
  by_cases hL : L = 0
  · subst hL
    have : cTime 0 u = 0 := by
      unfold cTime rTime
      rw [if_neg ENNReal.zero_ne_top]
      simp [clockOf]
    rw [this]; simp
  · exact cTime_le hL hu

theorem measurable_cTime {Ω : Type*} [MeasurableSpace Ω] {L : Ω → ℝ≥0∞} (hL : Measurable L) (u : ℝ) :
    Measurable fun ω => cTime (L ω) u := by
  classical
  unfold cTime rTime
  refine measurable_real_toNNReal.comp (Measurable.ite (hL (measurableSet_singleton ⊤)) measurable_const ?_)
  unfold clockOf
  exact (ENNReal.measurable_toReal.comp hL).mul measurable_const

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*} [MeasurableSpace Ω]

open Classical in
/-- **The relative stage curve is measurable at every time** on an event where it is driven. -/
theorem measurable_bRel (hb : IsPiecewiseConstantBoundaryData b jumps) {E : ExplSpec → ℕ → Ω → Drv} {ℓ : ℕ}
    {Ê : ℕ → Ω → Drv} (hÊm : ∀ j, Measurable (Ê j)) (hÊreg : ∀ j ω, IsRegularDriver (Ê j ω))
    (hÊP : ∀ ω, RegLaunches κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) fun j => Ê j ω)
    {K : Ω → Set ℂ} (hK : IsDyadicHitMeasurable K) (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ lowerHalf)) {x₀ : Ω → ℝ} (hx₀ : Measurable x₀) {M : Set Ω}
    (hM : MeasurableSet M)
    (hMl : ∀ ω ∈ M, (wRun κ (-(Real.pi / 2)) b jumps (fun j => Ê j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hMp : ∀ ω ∈ M, bPc κ b jumps E ℓ ω = pcPt (wRun κ (-(Real.pi / 2)) b jumps (fun j => Ê j ω) ℓ) (Ê ℓ ω))
    (hML : ∀ ω ∈ M, bLife b jumps E ℓ ω = (Ê ℓ ω).2) (hML0 : ∀ ω ∈ M, bLife b jumps E ℓ ω ≠ 0)
    (hMd : ∀ ω ∈ M, IsDrivenCurve (bRel κ b jumps E ℓ K x₀ ω)) (r : ℝ) (hr : 0 ≤ r) :
    Measurable fun ω => if ω ∈ M then bRel κ b jumps E ℓ K x₀ ω r else 0 := by
  classical
  set θ : ℝ := -(Real.pi / 2) with hθ
  set Lh : Ω → ℝ≥0∞ := fun ω => (Ê ℓ ω).2 with hLh
  have hLhm : Measurable Lh := measurable_snd.comp (hÊm ℓ)
  set LS : Set Ω := {ω | (wRun κ θ b jumps (fun j => Ê j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none} with hLS
  have hLSm : MeasurableSet LS := Nv.measurableSet_launch hb hÊm hÊreg ℓ
  -- the readings at the rational parameters
  set zq : ℕ → Ω → ℂ := fun i ω => if ω ∈ LS then
    pcPt (wRun κ θ b jumps (fun j => Ê j ω) ℓ) (Ê ℓ ω) (cTime (Lh ω) (ratPt i : ℝ)) else 0 with hzq
  have hzqm : ∀ i, Measurable (zq i) := fun i =>
    Nv.measurable_pcPt_at (κ := κ) (θ := θ) hb hÊm hÊreg hÊP ℓ (measurable_cTime hLhm _)
      fun ω _ => cTime_le_any (NNReal.coe_nonneg _)
  set good : ℕ → Ω → Prop := fun i ω => ω ∈ LS ∧ zq i ω ∈ H \ fillH (K ω) with hgood
  have hgoodm : ∀ i, MeasurableSet {ω | good i ω} := fun i =>
    hLSm.inter (measurableSet_mem_H_diff_fillH_rand hK hKc (hzqm i))
  set V : ℕ → Ω → ℂ := fun i => {ω | zq i ω ∈ H \ fillH (K ω)}.indicator
    fun ω => (Mo.hullChart (fillH (K ω)) (x₀ ω)).1 (zq i ω) with hV
  have hVm : ∀ i, Measurable (V i) := fun i => measurable_indicator_hullChart_rand hK hKc hKp hx₀ (hzqm i)
  have h := Lk.measurable_of_dense_good (ρ := fun ω (s : ℝ≥0) => bRel κ b jumps E ℓ K x₀ ω s) hgoodm hVm hM
    (fun ω hω => (hMd ω hω).continuousOn.comp_continuous NNReal.continuous_coe fun s => s.2) ?_ ?_ r.toNNReal
  · simp only [Real.coe_toNNReal _ hr] at h
    exact h
  · -- the values at good indices
    intro ω hω i hi
    have hzi : zq i ω = bPc κ b jumps E ℓ ω (cTime (bLife b jumps E ℓ ω) (ratPt i : ℝ)) := by
      simp only [hzq, hi.1, ↓reduceIte, hMp ω hω, hML ω hω, hLh]
    show canonCurve (K ω) (x₀ ω) (bPc κ b jumps E ℓ ω) (bLife b jumps E ℓ ω) (ratPt i) = V i ω
    rw [canonCurve_eq]
    have hg : cTime (bLife b jumps E ℓ ω) (ratPt i : ℝ) ∈
        canonGood (K ω) (bPc κ b jumps E ℓ ω) (bLife b jumps E ℓ ω) :=
      ⟨cTime_le_any (NNReal.coe_nonneg _), hzi ▸ hi.2⟩
    unfold canonVal
    simp only [hg, ↓reduceIte, hV]
    rw [indicator_of_mem (show ω ∈ {ω | zq i ω ∈ H \ fillH (K ω)} from hi.2), hzi]
  · -- good indices are dense
    intro ω hω t ε hε
    have hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => Ê j ω) (ℓ + 1)).2.2.2.1 ℓ ≠
        none := hMl ω hω
    have hpc : ContinuousOn (bPc κ b jumps E ℓ ω) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ bLife b jumps E ℓ ω} := by
      rw [hMp ω hω, hML ω hω]; exact continuousOn_pcPt_launch (hÊP ω) hl
    have hXo : IsOpen (H \ fillH (K ω)) := isOpen_H_diff_fillH (hKc ω).isBounded
    obtain ⟨q, hq0, hqd, hqg⟩ := exists_rat_good hXo (hML0 ω hω) hpc (hMd ω hω) t hε
    obtain ⟨i, hi⟩ := Nv.exists_ofNat_eq q
    have hri : ratPt i = (q : ℝ).toNNReal := by rw [Nv.ratPt_eq_ofNat, hi]
    refine ⟨i, ⟨hMl ω hω, ?_⟩, by rw [hri]; exact hqd⟩
    have hzi : zq i ω = bPc κ b jumps E ℓ ω (cTime (bLife b jumps E ℓ ω) (ratPt i : ℝ)) := by
      simp only [hzq, show ω ∈ LS from hMl ω hω, ↓reduceIte, hMp ω hω, hML ω hω, hLh]
    rw [hzi, hri]
    exact hqg.2

end InteractingSLE.Theorem14.SB.Nc
