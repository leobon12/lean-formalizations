/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactMartPrefix
import InteractingSLE.Spec.Sec7.PocketTraversalCoords
import InteractingSLE.Spec.Sec5.Prop59PiecesJoint
import InteractingSLE.Spec.Sec5.Prop59PiecesClock

/-!
# Measurable families of killed arcs: terminal capacity, killed driver, clock and mark images

Packet PROVE-PROP59-PIECES. The pieces of Proposition 5.9's alternating construction are read through a family of
killed arcs `γ ω` on pre-contact times `P ω` (one for every sample). PROVE-PROP59T4's regularity `IsRegPiece` asks
for jointly measurable drivers and marks, a measurable lifetime and a clock measurable at every time. This file
proves these facts for every family of killed arcs whose rational data are measurable (`IsKilledFamily`: the
rational pre-contact events, the clocks on them and the positions; WangWu's hypotheses of
`measurable_indicator_kW_of_base`):

* `measurable_kLife`: the terminal capacity (as an `ℝ≥0∞`-valued lifetime);
* `measurable_kW`, **`measurable_uncurry_kW`**: the killed driver at every time, and jointly (`Prop59PiecesJoint`);
* `measurable_kInvK`, `measurable_arcEnd`, `measurable_absClock`, **`measurable_uncurry_absClock`**: the compressed
  original clock (`Prop59PiecesClock`), through rational times;
* **`measurable_killedRightImg`**: the geometric image of a measurable mark under a driver that is continuous before
  a measurable lifetime, killed at the lifetime, is measurable at every time (PROVE-GLUECOND5's `frzImg` argument:
  freeze the driver after the time, then `PocketTraversal.measurable_rightImg_realPath_of_measurable`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Prop59Pieces

open WangWu WangWu.ImgWord CrossRestart MartChar.RealFlow
open Sec7.Lemma71C (capClock)

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Families of killed arcs -/

/-- **A measurable family of killed arcs**: every `γ ω` is a killed arc on `P ω`, and the rational pre-contact
events, the clocks on them and the rational positions are measurable. -/
structure IsKilledFamily (γ : Ω → ℝ → ℂ) (P : Ω → Set ℝ) : Prop where
  arc : ∀ ω, IsKilledArc (γ ω) (P ω)
  pre : ∀ q : ℚ, MeasurableSet {ω | (q : ℝ) ∈ P ω}
  cap : ∀ q : ℚ, Measurable ({ω | (q : ℝ) ∈ P ω}.indicator fun ω => capClock (γ ω) q)
  pos : ∀ q : ℚ, Measurable fun ω => γ ω q

variable {γ : Ω → ℝ → ℂ} {P : Ω → Set ℝ}

/-- The terminal capacity as an `ℝ≥0∞`-valued lifetime. -/
def lifeE (g : ℝ → ℂ) (Q : Set ℝ) : ℝ≥0∞ := kLife g Q

theorem lt_lifeE_iff {g : ℝ → ℂ} {Q : Set ℝ} {t : ℝ≥0} :
    (t : ℝ≥0∞) < lifeE g Q ↔ (t : WithTop ℝ≥0) < kLife g Q := Iff.rfl

namespace IsKilledFamily

theorem measurableSet_lt_kLife (hF : IsKilledFamily γ P) (r : ℝ≥0) :
    MeasurableSet {ω | (r : WithTop ℝ≥0) < kLife (γ ω) (P ω)} :=
  WangWu.measurableSet_lt_kLife hF.arc hF.pre hF.cap r

/-- The terminal capacity is measurable (as an `ℝ≥0∞`-valued lifetime). -/
theorem measurable_kLife (hF : IsKilledFamily γ P) :
    Measurable fun ω => lifeE (γ ω) (P ω) := by
  refine measurable_of_Ioi fun x => ?_
  induction x using ENNReal.recTopCoe with
  | top => simp
  | coe r => exact hF.measurableSet_lt_kLife r

/-- The killed driver is measurable at every time. -/
theorem measurable_kW (hF : IsKilledFamily γ P) (t : ℝ≥0) : Measurable fun ω => kW (γ ω) (P ω) t := by
  have h := measurable_indicator_kW_of_base hF.arc hF.pre hF.cap hF.pos t
  have e : (fun ω => kW (γ ω) (P ω) t) =
      {ω | (t : WithTop ℝ≥0) < kLife (γ ω) (P ω)}.indicator fun ω => kW (γ ω) (P ω) t := by
    funext ω
    by_cases ht : (t : WithTop ℝ≥0) < kLife (γ ω) (P ω)
    · rw [indicator_of_mem (show ω ∈ {ω | (t : WithTop ℝ≥0) < kLife (γ ω) (P ω)} from ht)]
    · rw [indicator_of_notMem (show ω ∉ {ω | (t : WithTop ℝ≥0) < kLife (γ ω) (P ω)} from ht)]
      simp only [kW, ht, ↓reduceIte]
  rw [e]
  exact h

/-- **The killed driver is jointly measurable.** -/
theorem measurable_uncurry_kW (hF : IsKilledFamily γ P) :
    Measurable (Function.uncurry fun t ω => kW (γ ω) (P ω) t) :=
  measurable_uncurry_of_killed (L := fun ω => lifeE (γ ω) (P ω)) hF.measurable_kW
    (fun ω => (hF.arc ω).continuousOn_kW) hF.measurable_kLife
    fun u ω hu => by
      have hu' : ¬ (u : WithTop ℝ≥0) < kLife (γ ω) (P ω) := hu
      simp only [kW, hu', ↓reduceIte]

/-! ### The clock -/

/-- The inverse capacity clock killed at the terminal capacity. -/
def kInvK (γ : ℝ → ℂ) (P : Set ℝ) (τ : ℝ≥0) : ℝ := if (τ : WithTop ℝ≥0) < kLife γ P then kInv γ P τ else 0

/-- Before the terminal capacity, `σ⁻¹(τ) < a` iff some rational pre-contact time below `a` has capacity above `τ`. -/
theorem kInv_lt_iff {g : ℝ → ℂ} {Q : Set ℝ} (hg : IsKilledArc g Q) {τ : ℝ≥0}
    (hτ : (τ : WithTop ℝ≥0) < kLife g Q) (a : ℝ) :
    kInv g Q τ < a ↔ ∃ q : ℚ, (q : ℝ) < a ∧ (q : ℝ) ∈ Q ∧ (τ : ℝ) < capClock g q := by
  obtain ⟨hm, he⟩ := hg.kInv_spec hτ
  constructor
  · intro hlt
    obtain ⟨u', hu', huu'⟩ := hg.exists_gt _ hm
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min hlt huu')
    have hqQ : (q : ℝ) ∈ Q := hg.icc u' hu' ⟨(hg.nonneg _ hm).trans hq1.le, hq2.le.trans (min_le_right _ _)⟩
    refine ⟨q, hq2.trans_le (min_le_left _ _), hqQ, ?_⟩
    rw [← he]
    exact hg.strictMonoOn_capClock hm hqQ hq1
  · rintro ⟨q, hqa, hqQ, hτq⟩
    refine lt_of_lt_of_le ?_ hqa.le
    by_contra h
    have := hg.strictMonoOn_capClock.monotoneOn hqQ hm (not_lt.1 h)
    rw [he] at this
    linarith

theorem measurable_kInvK (hF : IsKilledFamily γ P) (τ : ℝ≥0) :
    Measurable fun ω => kInvK (γ ω) (P ω) τ := by
  refine measurable_of_Iio fun a => ?_
  have e : (fun ω => kInvK (γ ω) (P ω) τ) ⁻¹' Iio a =
      ({ω | (τ : WithTop ℝ≥0) < kLife (γ ω) (P ω)} ∩ ⋃ q : ℚ, {ω | (q : ℝ) < a} ∩ ({ω | (q : ℝ) ∈ P ω} ∩
        {ω | (τ : ℝ) < ({ω | (q : ℝ) ∈ P ω}.indicator fun ω => capClock (γ ω) q) ω})) ∪
      ({ω | (τ : WithTop ℝ≥0) < kLife (γ ω) (P ω)}ᶜ ∩ {ω | (0 : ℝ) < a}) := by
    ext ω
    simp only [mem_preimage, mem_Iio, mem_union, mem_inter_iff, mem_iUnion, mem_compl_iff, mem_ofPred_eq]
    by_cases hτ : (τ : WithTop ℝ≥0) < kLife (γ ω) (P ω)
    · simp only [kInvK, hτ, ↓reduceIte, true_and, not_true_eq_false, false_and, or_false]
      rw [kInv_lt_iff (hF.arc ω) hτ a]
      refine exists_congr fun q => and_congr_right fun _ => ⟨fun h => ⟨h.1, ?_⟩, fun h => ⟨h.1, ?_⟩⟩
      · rw [indicator_of_mem (show ω ∈ {ω | (q : ℝ) ∈ P ω} from h.1)]; exact h.2
      · rw [indicator_of_mem (show ω ∈ {ω | (q : ℝ) ∈ P ω} from h.1)] at h; exact h.2
    · simp only [kInvK, hτ, ↓reduceIte, false_and, not_false_eq_true, true_and, false_or]
  rw [e]
  refine ((hF.measurableSet_lt_kLife τ).inter (MeasurableSet.iUnion fun q => ?_)).union
    ((hF.measurableSet_lt_kLife τ).compl.inter (MeasurableSet.const _))
  exact (MeasurableSet.const _).inter ((hF.pre q).inter (measurableSet_lt measurable_const (hF.cap q)))

/-- `c < E` iff some rational pre-contact time has compressed time above `c`. -/
theorem lt_arcEnd_iff {g : ℝ → ℂ} {Q : Set ℝ} (hg : IsKilledArc g Q) (c : ℝ) :
    c < arcEnd Q ↔ ∃ q : ℚ, (q : ℝ) ∈ Q ∧ c < physTime q := by
  constructor
  · intro h
    obtain ⟨_, ⟨u, hu, rfl⟩, hcu⟩ := exists_lt_of_lt_csSup (Set.Nonempty.image _ ⟨0, hg.zero_mem⟩) h
    obtain ⟨u', hu', huu'⟩ := hg.exists_gt u hu
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn huu'
    have hqQ : (q : ℝ) ∈ Q := hg.icc u' hu' ⟨(hg.nonneg u hu).trans hq1.le, hq2.le⟩
    exact ⟨q, hqQ, hcu.trans (physTime_strictMono (hg.nonneg u hu) hq1)⟩
  · rintro ⟨q, hqQ, hcq⟩
    exact hcq.trans (physTime_lt_arcEnd hg hqQ)

theorem measurable_arcEnd (hF : IsKilledFamily γ P) : Measurable fun ω => arcEnd (P ω) := by
  refine measurable_of_Ioi fun c => ?_
  have e : (fun ω => arcEnd (P ω)) ⁻¹' Ioi c = ⋃ q : ℚ, {ω | (q : ℝ) ∈ P ω} ∩ {_ω | c < physTime q} := by
    ext ω
    simp only [mem_preimage, mem_Ioi, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    exact lt_arcEnd_iff (hF.arc ω) c
  rw [e]
  exact MeasurableSet.iUnion fun q => (hF.pre q).inter (MeasurableSet.const _)

omit [MeasurableSpace Ω] in
/-- The clock in measurable form: the killed inverse clock and the lifetime in `ℝ≥0∞`. -/
theorem absClock_eq (ω : Ω) (τ : ℝ≥0) :
    absClock (γ ω) (P ω) τ = if (τ : WithTop ℝ≥0) < kLife (γ ω) (P ω) then
      (physTime (kInvK (γ ω) (P ω) τ)).toNNReal
    else (arcEnd (P ω)).toNNReal + ((τ : ℝ≥0∞) - lifeE (γ ω) (P ω)).toNNReal := by
  by_cases hτ : (τ : WithTop ℝ≥0) < kLife (γ ω) (P ω)
  · simp only [absClock, kInvK, hτ, ↓reduceIte]
  · simp only [absClock, hτ, ↓reduceIte]
    congr 1
    have htop : kLife (γ ω) (P ω) ≠ ⊤ := fun h => by rw [h] at hτ; exact hτ (WithTop.coe_lt_top τ)
    obtain ⟨K, hK⟩ := WithTop.ne_top_iff_exists.1 htop
    have e : lifeE (γ ω) (P ω) = (K : ℝ≥0∞) := hK.symm
    rw [← hK, WithTop.untopD_coe, e, ← ENNReal.coe_sub, ENNReal.toNNReal_coe]

theorem measurable_absClock (hF : IsKilledFamily γ P) (τ : ℝ≥0) :
    Measurable fun ω => absClock (γ ω) (P ω) τ := by
  simp only [absClock_eq]
  refine Measurable.ite (hF.measurableSet_lt_kLife τ) ?_ ?_
  · exact measurable_real_toNNReal.comp
      ((measurable_id.div (measurable_const.add measurable_id)).comp (hF.measurable_kInvK τ))
  · exact (measurable_real_toNNReal.comp hF.measurable_arcEnd).add
      (ENNReal.measurable_toNNReal.comp (measurable_const.sub hF.measurable_kLife))

/-- **The clock is jointly measurable** (continuous in time, measurable at every time). -/
theorem measurable_uncurry_absClock (hF : IsKilledFamily γ P) :
    Measurable (Function.uncurry fun τ ω => absClock (γ ω) (P ω) τ) :=
  measurable_uncurry_of_continuous_of_measurable (fun ω => continuous_absClock (hF.arc ω))
    hF.measurable_absClock

end IsKilledFamily

/-! ### Mark images under a killed driver -/

/-- **The geometric image of a right mark under a killed driver is measurable.** Let `X · ω` be continuous before a
measurable lifetime `L ω` and measurable at every time, and `x` measurable. Then
`ω ↦ rightImg (X · ω) (x ω) t` killed at `L` is measurable (freeze the driver after `t`). -/
theorem measurable_killedRightImg {X : ℝ≥0 → Ω → ℝ} {L : Ω → ℝ≥0∞} (hX : ∀ u, Measurable (X u))
    (hc : ∀ ω, ContinuousOn (X · ω) {u | (u : ℝ≥0∞) < L ω}) (hL : Measurable L) {x : Ω → ℝ}
    (hx : Measurable x) (t : ℝ≥0) :
    Measurable fun ω => if (t : ℝ≥0∞) < L ω then rightImg (Bessel.realPath X ω) (x ω) t else 0 := by
  classical
  set F : ℝ≥0 → Ω → ℝ := fun u ω => if (t : ℝ≥0∞) < L ω then X (min u t) ω else 0 with hFdef
  have hset : MeasurableSet {ω | (t : ℝ≥0∞) < L ω} := measurableSet_lt measurable_const hL
  have hFm : ∀ u, Measurable (F u) := fun u => Measurable.ite hset (hX _) measurable_const
  have hFc : ∀ ω, Continuous fun u => F u ω := by
    intro ω
    by_cases ht : (t : ℝ≥0∞) < L ω
    · simp only [hFdef, ht, ↓reduceIte]
      exact (hc ω).comp_continuous (continuous_id.min continuous_const)
        fun u => lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right u t)) ht
    · simp only [hFdef, ht, ↓reduceIte]
      exact continuous_const
  let 𝓕c : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω) :=
    ⟨fun _ => inferInstance, monotone_const, fun _ => le_rfl⟩
  have hR : Measurable fun ω => rightImg (Bessel.realPath F ω) (x ω) t :=
    Sec7.PocketTraversal.measurable_rightImg_realPath_of_measurable (𝓕 := 𝓕c) hFm hFc hx t
  have e : (fun ω => if (t : ℝ≥0∞) < L ω then rightImg (Bessel.realPath X ω) (x ω) t else 0) =
      fun ω => if (t : ℝ≥0∞) < L ω then rightImg (Bessel.realPath F ω) (x ω) t else 0 := by
    funext ω
    by_cases ht : (t : ℝ≥0∞) < L ω
    · simp only [ht, ↓reduceIte]
      refine Sec7.Lemma71B.rightImg_congr (Bessel.continuous_realPath hFc ω) t.coe_nonneg (fun r hr => ?_) _
      have hrt : r.toNNReal ≤ t := by rw [Real.toNNReal_le_iff_le_coe]; exact hr.2
      simp only [Bessel.realPath, hFdef, ht, ↓reduceIte, min_eq_left hrt]
    · simp only [ht, ↓reduceIte]
  rw [e]
  exact Measurable.ite hset hR measurable_const

end InteractingSLE.Sec5.Prop59Pieces
