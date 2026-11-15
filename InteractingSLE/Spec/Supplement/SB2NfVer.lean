/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NfAdapt
import InteractingSLE.Spec.Supplement.SB2NfHull
import InteractingSLE.Spec.Supplement.SB2NdVer

/-!
# F2b′'s root versions at a good sample

Packet PROVE-AUX61-NOJUMP (round 22, the root variant). The sample-level facts behind the root's version fields
(`Nd.StopIn`'s `SB2NdVer` and `SB2NeHullV` for the root clock `a t = clock of the relative piece at t − rSh`):

* (general stops) `StopG.notMem_badSet`, **`StopG.V_le_thr_of_mem`**, **`StopG.ann_of_mem`**;
* the clock is the relative lifetime from B's lifetime on and strictly below it before; live times are before B's
  lifetime (**`lt_life_of_lt`**); the clock reaches every level below a stop (**`reach_of_mem`**);
* **`trace_of_mem`**: the frozen driver's Loewner trace reads B's point through the chart at the clock, at every
  B-time after the entrance where the point is in the chart's domain;
* **`hull_of_mem`**: the `hull` field for the joint second set (`fwdHull_eq`, `hull_joint`, `fillH_retX_bPc_eq`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Nf

open Vs Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId Supp8.GB6.RelDrv.Version Supp8.Q3Stop Sec7.PocketTraversal
  Sec7.Lemma71C Restart Exist Exist.Staged Lv Ms Mf WalkSide LocalSets Lk LuM Nc Dv Vr Nd

namespace StopG

variable {κ ψ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} (T : StopG P κ ψ)

/-- **The gauge positive before the stop keeps the trace off the type's bad set.** -/
theorem notMem_badSet {m : ℕ} {ω : Ω} (hω : ω ∈ T.Gs) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T.Vstop m ω) :
    capTrace (T.ρ ω) t ∉ badSet (cellXL κ ψ T.cw (angleWordType κ ψ (T.cw ω)) ω)
      (cellXR κ ψ T.cw (angleWordType κ ψ (T.cw ω)) ω) (typedRhoL (angleWordType κ ψ (T.cw ω)))
      (typedRhoR (angleWordType κ ψ (T.cw ω))) := by
  obtain ⟨hV, -, -, -, hpos⟩ := T.sample hω m
  rw [hV] at ht
  have h1 := hpos t (by exact_mod_cast ht)
  have h2 : 0 < relGauge κ ψ T.cw T.types ω (capTrace (T.ρ ω) t) := lt_of_lt_of_le h1 (min_le_left _ _)
  rw [relGauge_eq κ ψ T.cw T.types ((T.rel ω hω).cover) rfl] at h2
  intro hmem
  have h3 : infEDist (capTrace (T.ρ ω) t) (closure (badSet (cellXL κ ψ T.cw (angleWordType κ ψ (T.cw ω)) ω)
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
    (FCDet.isOrderedForceWord_typeXL (T.cw ω)).2.2.2 (Γ := capTrace (T.ρ ω)) ?_ fun t ht =>
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

end StopG

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ}
  {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ}

namespace RootStop

variable (T : RootStop P κ b jumps E u l k ℓ)

theorem Gs_subset_Eg {ω : Ω} (hω : ω ∈ T.toG.Gs) : ω ∈ T.S.Eg := hω.1

/-- B-times before B's lifetime are, after the shift, before the relative lifetime. -/
theorem tsub_lt_rLife {ω : Ω} (hω : ω ∈ T.S.Eg) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < bLife b jumps E ℓ ω) :
    (((t - rSh κ b jumps E u l k ℓ ω : ℝ≥0)) : ℝ≥0∞) < rLife κ b jumps E u l k ℓ ω := by
  unfold rLife
  rcases le_total (rSh κ b jumps E u l k ℓ ω) t with h' | h'
  · rw [lt_tsub_iff_left, ← ENNReal.coe_add, add_tsub_cancel_of_le h']; exact ht
  · rw [tsub_eq_zero_of_le h', ENNReal.coe_zero]
    have := (T.S.geo hω).pos
    unfold rLife at this
    exact pos_iff_ne_zero.2 this

theorem a_eq_of_lt {ω : Ω} (hω : ω ∈ T.S.Eg) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < bLife b jumps E ℓ ω) :
    T.S.a t ω = ENNReal.ofReal (capClock (T.S.ρM ω) (uOf (rLife κ b jumps E u l k ℓ ω)
      ((t - rSh κ b jumps E u l k ℓ ω : ℝ≥0) : ℝ))) := by
  rw [T.S.a_eq hω, if_pos (T.tsub_lt_rLife hω ht)]

theorem a_eq_capLife_of_le {ω : Ω} (hω : ω ∈ T.S.Eg) {t : ℝ≥0} (ht : bLife b jumps E ℓ ω ≤ t) :
    T.S.a t ω = capLife (T.S.ρM ω) := by
  rw [T.S.a_eq hω, if_neg]
  rw [not_lt, ENNReal.coe_sub]
  exact tsub_le_tsub_right ht _

theorem a_lt_capLife_of_lt {ω : Ω} (hω : ω ∈ T.S.Eg) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < bLife b jumps E ℓ ω) :
    T.S.a t ω < capLife (T.S.ρM ω) := by
  rw [T.a_eq_of_lt hω ht]
  exact (T.S.driven_ρM ω).ofReal_capClock_lt (uOf_nonneg (beforeL_of_lt (T.tsub_lt_rLife hω ht)))

/-- **Live times are before B's lifetime.** -/
theorem lt_life_of_lt {m : ℕ} {ω : Ω} (hω : ω ∈ T.toG.Gs) {t : ℝ≥0} (ht : T.S.a t ω < T.toG.V m ω) :
    (t : ℝ≥0∞) < bLife b jumps E ℓ ω := by
  by_contra hle
  rw [not_lt] at hle
  rw [T.a_eq_capLife_of_le (T.Gs_subset_Eg hω) hle, T.toG.V_eq hω] at ht
  exact absurd (T.toG.Vstop_lt hω) (not_lt.2 ht.le)

/-- **The clock reaches every level below a stop.** -/
theorem reach_of_mem {m : ℕ} {ω : Ω} (hω : ω ∈ T.toG.Gs) {q : ℝ≥0} (hq : (q : ℝ≥0∞) < T.toG.V m ω) :
    ∃ t, (q : ℝ≥0∞) ≤ T.S.a t ω := by
  have hEg := T.Gs_subset_Eg hω
  have hq' : (q : ℝ≥0∞) < capLife (T.S.ρM ω) := by
    rw [T.toG.V_eq hω] at hq; exact hq.trans (T.toG.Vstop_lt hω)
  by_cases hL : bLife b jumps E ℓ ω = ⊤
  · obtain ⟨n, hn⟩ := exists_lt_capClock_of_lt_capLife (γ := T.S.ρM ω) (s := q)
      (by rw [ENNReal.ofReal_coe_nnreal]; exact hq')
    refine ⟨rSh κ b jumps E u l k ℓ ω + n, ?_⟩
    rw [T.a_eq_of_lt hEg (by rw [hL]; exact ENNReal.coe_lt_top)]
    have hrL : rLife κ b jumps E u l k ℓ ω = ⊤ := by unfold rLife; rw [hL, ENNReal.top_sub_coe]
    have hu : uOf (rLife κ b jumps E u l k ℓ ω)
        ((rSh κ b jumps E u l k ℓ ω + (n : ℝ≥0) - rSh κ b jumps E u l k ℓ ω : ℝ≥0) : ℝ) = n := by
      unfold uOf; rw [if_pos hrL, add_tsub_cancel_left]; simp
    rw [hu, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hn.le
  · refine ⟨(bLife b jumps E ℓ ω).toNNReal, ?_⟩
    rw [T.a_eq_capLife_of_le hEg (by rw [ENNReal.coe_toNNReal hL])]
    exact hq'.le

theorem continuousOn_rPc {ω : Ω} (hω : ω ∈ T.S.Eg) :
    ContinuousOn (rPc κ b jumps E u l k ℓ ω) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ rLife κ b jumps E u l k ℓ ω} := by
  have hc := continuousOn_bPc₀ (T.S.good₀ ω hω.1)
  have hle := (T.S.geo hω).shlt.le
  refine hc.comp (continuous_const.add continuous_id).continuousOn fun t ht => ?_
  show (((rSh κ b jumps E u l k ℓ ω + t : ℝ≥0)) : ℝ≥0∞) ≤ bLife b jumps E ℓ ω
  rw [ENNReal.coe_add]
  calc (rSh κ b jumps E u l k ℓ ω : ℝ≥0∞) + t ≤ rSh κ b jumps E u l k ℓ ω + rLife κ b jumps E u l k ℓ ω :=
        add_le_add le_rfl ht
    _ = bLife b jumps E ℓ ω := add_tsub_cancel_of_le hle

/-- **The frozen driver's Loewner trace reads B's point through the chart at the clock** after the entrance. -/
theorem trace_of_mem {m : ℕ} {ω : Ω} (hω : ω ∈ T.toG.Gs) {t : ℝ≥0} (ht : T.S.a t ω < T.toG.V m ω) :
    ∃ ηr : ℝ → ℂ, IsLoewnerTrace (fun s : ℝ => T.toG.W m s.toNNReal ω) ηr ∧
      ∀ s : ℝ≥0, s ≤ t → rSh κ b jumps E u l k ℓ ω ≤ s →
        bPc κ b jumps E ℓ ω s ∈ ((Mo.hullChart (fillH (T.S.K ω)) (T.S.x₀ ω)).dom : Set ℂ) →
        ηr (T.S.a s ω).toReal = (Mo.hullChart (fillH (T.S.K ω)) (T.S.x₀ ω)).1 (bPc κ b jumps E ℓ ω s) := by
  have hEg := T.Gs_subset_Eg hω
  have hd := T.S.driven_ρM ω
  have hpos := T.toG.Vstop_pos (m := m) hω
  have htop := T.toG.Vstop_ne_top (m := m) hω
  set v : ℝ≥0 := (T.toG.Vstop m ω).toNNReal with hv
  have hvc : (v : ℝ≥0∞) = T.toG.Vstop m ω := ENNReal.coe_toNNReal htop
  have hv0 : 0 < v := by rw [← ENNReal.coe_lt_coe, hvc]; exact hpos
  obtain ⟨ηr, hLT, heq⟩ := exists_loewnerTrace_min hv0 (by rw [hvc]; exact T.toG.Vstop_lt hω) (T.toG.Wr_zero ω)
    (T.toG.continuousOn_Wr ω) fun V hV => T.toG.isGeneratingTrace_Wr ω hV
  refine ⟨ηr, ?_, fun s hst hshs hdom => ?_⟩
  · have e : (fun s : ℝ => T.toG.W m s.toNNReal ω) = fun r : ℝ => T.toG.Wr (min r.toNNReal v) ω :=
      funext fun r => T.toG.W_of_mem hω _
    rw [e]; exact hLT
  · have has : T.S.a s ω < T.toG.Vstop m ω := by
      rw [← T.toG.V_eq hω]; exact lt_of_le_of_lt (T.S.monotone_a ω hst) ht
    have hsL : (s : ℝ≥0∞) < bLife b jumps E ℓ ω := by
      by_contra hle
      rw [not_lt] at hle
      rw [T.a_eq_capLife_of_le hEg hle] at has
      exact absurd (T.toG.Vstop_lt hω) (not_lt.2 has.le)
    set sh := rSh κ b jumps E u l k ℓ ω with hshdef
    have hrL := T.tsub_lt_rLife hEg hsL
    have hb := beforeL_of_lt hrL
    have has' := T.a_eq_of_lt hEg hsL
    have hc0 := hd.capClock_nonneg (uOf_nonneg hb)
    have htoR : (T.S.a s ω).toReal = capClock (T.S.ρM ω) (uOf (rLife κ b jumps E u l k ℓ ω) ((s - sh : ℝ≥0) : ℝ)) := by
      rw [has', ENNReal.toReal_ofReal hc0]
    have hlt : ((T.S.a s ω).toNNReal : ℝ≥0∞) < v := by
      rw [ENNReal.coe_toNNReal (ne_top_of_lt has), hvc]; exact has
    have h1 : ηr (T.S.a s ω).toReal = capTrace (T.S.ρM ω) (T.S.a s ω).toNNReal := heq _ hlt
    rw [h1]
    unfold capTrace
    have h2 : ((T.S.a s ω).toNNReal : ℝ) =
        capClock (T.S.ρM ω) (uOf (rLife κ b jumps E u l k ℓ ω) ((s - sh : ℝ≥0) : ℝ)) := by
      rw [← htoR]; rfl
    rw [h2, hd.capInv_eq (uOf_nonneg hb), T.S.ρM_eq hEg]
    show canonVal (T.S.K ω) (T.S.x₀ ω) (rPc κ b jumps E u l k ℓ ω) (rLife κ b jumps E u l k ℓ ω)
      (cTime (rLife κ b jumps E u l k ℓ ω) (uOf (rLife κ b jumps E u l k ℓ ω) ((s - sh : ℝ≥0) : ℝ))) = _
    rw [cTime_uOf hb, Real.toNNReal_coe]
    have hps : rPc κ b jumps E u l k ℓ ω (s - sh) = bPc κ b jumps E ℓ ω s := by
      simp only [rPc, ← hshdef, add_tsub_cancel_of_le hshs]
    have hdom' : rPc κ b jumps E u l k ℓ ω (s - sh) ∈ H \ fillH (T.S.K ω) := by
      rw [hps]; rwa [Mo.coe_dom_hullChart (Mo.isHPHull_fillH T.S.hKc T.S.hKp ω)] at hdom
    unfold canonVal
    rw [if_pos ⟨hrL.le, hdom'⟩, hps]

/-- **The frozen driver's hull at the clock** is the fill of the relative curve up to `uOf (t − rSh)`. -/
theorem fwdHull_eq {m : ℕ} {ω : Ω} (hω : ω ∈ T.toG.Gs) {t : ℝ≥0} (ht : T.S.a t ω < T.toG.V m ω) :
    fwdHull (fun s : ℝ => T.toG.W m s.toNNReal ω) ((T.S.a t ω).toNNReal : ℝ) =
      fillH (T.S.ρM ω '' Icc 0 (uOf (rLife κ b jumps E u l k ℓ ω)
        ((t - rSh κ b jumps E u l k ℓ ω : ℝ≥0) : ℝ))) := by
  have hEg := T.Gs_subset_Eg hω
  have hd := T.S.driven_ρM ω
  have hpos := T.toG.Vstop_pos (m := m) hω
  have htop := T.toG.Vstop_ne_top (m := m) hω
  set v : ℝ≥0 := (T.toG.Vstop m ω).toNNReal with hv
  have hvc : (v : ℝ≥0∞) = T.toG.Vstop m ω := ENNReal.coe_toNNReal htop
  have hv0 : 0 < v := by rw [← ENNReal.coe_lt_coe, hvc]; exact hpos
  obtain ⟨ηr, hLT, heq⟩ := exists_loewnerTrace_min hv0 (by rw [hvc]; exact T.toG.Vstop_lt hω) (T.toG.Wr_zero ω)
    (T.toG.continuousOn_Wr ω) fun V hV => T.toG.isGeneratingTrace_Wr ω hV
  have e : (fun s : ℝ => T.toG.W m s.toNNReal ω) = fun r : ℝ => T.toG.Wr (min r.toNNReal v) ω :=
    funext fun r => T.toG.W_of_mem hω _
  rw [e, hLT.2.2 _ (NNReal.coe_nonneg _)]
  congr 1
  have hsL : (t : ℝ≥0∞) < bLife b jumps E ℓ ω := T.lt_life_of_lt hω ht
  have hrL := T.tsub_lt_rLife hEg hsL
  have hb := beforeL_of_lt hrL
  have hc0 := hd.capClock_nonneg (uOf_nonneg hb)
  have has' := T.a_eq_of_lt hEg hsL
  have hcv : ((T.S.a t ω).toNNReal : ℝ≥0∞) < v := by
    rw [ENNReal.coe_toNNReal (ne_top_of_lt ht), hvc, ← T.toG.V_eq hω]; exact ht
  have hcR : ((T.S.a t ω).toNNReal : ℝ) = capClock (T.S.ρM ω) (uOf (rLife κ b jumps E u l k ℓ ω)
      ((t - rSh κ b jumps E u l k ℓ ω : ℝ≥0) : ℝ)) := by
    show (T.S.a t ω).toReal = _
    rw [has', ENNReal.toReal_ofReal hc0]
  have him : ηr '' Icc 0 ((T.S.a t ω).toNNReal : ℝ) = capTrace (T.S.ρM ω) '' Icc 0 (T.S.a t ω).toNNReal := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxle : x.toNNReal ≤ (T.S.a t ω).toNNReal := Real.toNNReal_le_iff_le_coe.2 hx.2
      refine ⟨x.toNNReal, ⟨zero_le, hxle⟩, ?_⟩
      have hxv : (x.toNNReal : ℝ≥0∞) < v := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hxle) hcv
      have := heq _ hxv
      rw [Real.coe_toNNReal _ hx.1] at this
      exact this.symm
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r, ⟨r.2, NNReal.coe_le_coe.2 hr.2⟩, heq r (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr.2) hcv)⟩
  rw [him, hd.image_capTrace (hcv.trans (by rw [hvc]; exact T.toG.Vstop_lt hω)), hcR, hd.capInv_eq (uOf_nonneg hb)]

/-- **The pulled-back relative hull is the joint fill** of the retained union and B's piece up to `t`. -/
theorem hull_joint {m : ℕ} {ω : Ω} (hω : ω ∈ T.toG.Gs) {t : ℝ≥0} (ht : T.S.a t ω < T.toG.V m ω) :
    H \ fillH (retX κ b jumps E u l k ℓ ω ∪ bPc κ b jumps E ℓ ω '' Icc 0 t) =
      (Mo.hullChart (fillH (T.S.K ω)) (T.S.x₀ ω)).2.1 ''
        (H \ fwdHull (fun s : ℝ => T.toG.W m s.toNNReal ω) ((T.S.a t ω).toNNReal : ℝ)) := by
  have hEg := T.Gs_subset_Eg hω
  have hg := T.S.good₀ ω hEg.1
  have G := T.S.geo hEg
  have hsL : (t : ℝ≥0∞) < bLife b jumps E ℓ ω := T.lt_life_of_lt hω ht
  have hrL := T.tsub_lt_rLife hEg hsL
  have hb := beforeL_of_lt hrL
  rw [T.fwdHull_eq hω ht, T.S.ρM_eq hEg, fillH_retX_bPc_eq hg G hsL]
  have hcc : canonCurve (T.S.K ω) (T.S.x₀ ω) (rPc κ b jumps E u l k ℓ ω) (rLife κ b jumps E u l k ℓ ω) =
      canonCurve (retX κ b jumps E u l k ℓ ω) (T.S.x₀ ω) (rPc κ b jumps E u l k ℓ ω)
        (rLife κ b jumps E u l k ℓ ω) := by
    unfold canonCurve canonVal canonGood; rw [hg.fill]
  have h := Ne.H_diff_fillH_union_canon hg.retc hg.hull G.pos (T.continuousOn_rPc hEg) G.driven (uOf_nonneg hb)
  rw [cTime_uOf hb, Real.toNNReal_coe] at h
  rw [hg.fill]
  show _ = _ '' (H \ fillH (canonCurve (T.S.K ω) (T.S.x₀ ω) (rPc κ b jumps E u l k ℓ ω)
    (rLife κ b jumps E u l k ℓ ω) '' _))
  rw [hcc]
  exact h

/-- **The root's `hull` field** for the joint second set. -/
theorem hull_of_mem {m : ℕ} {ω : Ω} (hω : ω ∈ T.toG.Gs) {t : ℝ≥0} (ht : T.S.a t ω < T.toG.V m ω)
    {A₁ A₂ : Set ℂ}
    (h₁ : A₁ = fillVer (fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
      WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
        (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) ω)
    (h₂ : A₂ = fillVer (fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
      WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
        (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
        (ℓ + 1) ω) ω) :
    H \ (A₁ ∪ A₂) = (Mo.hullChart (fillH (T.S.K ω)) (T.S.x₀ ω)).2.1 ''
      (H \ fwdHull (fun s : ℝ => T.toG.W m s.toNNReal ω) ((T.S.a t ω).toNNReal : ℝ)) := by
  have hEg := T.Gs_subset_Eg hω
  have hg := T.S.good₀ ω hEg.1
  have hsL : (t : ℝ≥0∞) < bLife b jumps E ℓ ω := T.lt_life_of_lt hω ht
  have hA₁ : A₁ = fillH (retX κ b jumps E u l k ℓ ω) := by
    have hb : Bornology.IsBounded (retX κ b jumps E u l k ℓ ω ∩ H) := hg.retc.isBounded.subset inter_subset_left
    rw [h₁, fillVer_of_bounded (B := fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
      WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
        (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω)
      (by show Bornology.IsBounded (_ ∪ _); rw [stageSet_first_eq₀ hg]; exact hb)]
    show fillH (closure (_ ∪ _)) = _
    rw [stageSet_first_eq₀ hg, Mo.fillH_closure_inter_H]
  have hA₂ : A₂ = fillH (retX κ b jumps E u l k ℓ ω ∪ bPc κ b jumps E ℓ ω '' Icc 0 t) := by
    have hPc : IsCompact (bPc κ b jumps E ℓ ω '' Icc 0 t) :=
      isCompact_Icc.image_of_continuousOn ((continuousOn_bPc₀ hg).mono fun s hs =>
        show (s : ℝ≥0∞) ≤ bLife b jumps E ℓ ω from (ENNReal.coe_le_coe.2 hs.2).trans hsL.le)
    have hb : Bornology.IsBounded ((retX κ b jumps E u l k ℓ ω ∪ bPc κ b jumps E ℓ ω '' Icc 0 t) ∩ H) :=
      (hg.retc.union hPc).isBounded.subset inter_subset_left
    rw [h₂, fillVer_of_bounded (B := fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
      WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
        (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
        (ℓ + 1) ω)
      (by show Bornology.IsBounded (_ ∪ _); rw [stageSet_joint_eq₀ hg hsL]; exact hb)]
    show fillH (closure (_ ∪ _)) = _
    rw [stageSet_joint_eq₀ hg hsL, Mo.fillH_closure_inter_H]
  rw [hA₁, hA₂, union_eq_right.2 (fillH_mono subset_union_left)]
  exact T.hull_joint hω ht

end RootStop

end InteractingSLE.Theorem14.SB.Nf
