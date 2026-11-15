/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2TipSepAtStop
import InteractingSLE.Spec.ZhanGT4.DualJointHit
import InteractingSLE.Spec.ZhanGT4.A1RefCDLive
import InteractingSLE.Spec.Sec2.CriticalExtension
import InteractingSLE.Foundations.Loewner.YuanCorollary13Slit
import QuantumZipper.Proofs.Thm11.ForwardTamed

/-!
# A.2, part 2, step 1: first hits inside the strip life are stopping times of the usual augmentation

Packet PROVE-ZHAN-A2TIPSEP. Source: Astra, *Follow-up proofs*, §A.2 L555–L561 ("Stop the large curve at its first hit
of `α ∪ γ`"; R38, R53, R70).

The first time the hulls of a driver, continuous before its lifetime, meet a compact `L ⊆ ℍ` inside the strip life of
a mark is a pathwise time. After regularizing the processes on a null set (continuous at every sample), it is a
stopping time of the usual augmentation:

* `measurable_tamedZ_family`: the tamed Loewner flow of a family of continuous drivers with measurable evaluations is
  measurable;
* `HitBy w v ζ L t`: some time `≤ t` of the strip life has hull meeting `L`; `hitBy_iff_rat` (a countable formula,
  using that the strip life is open), `hitBy_iff_of_isFirstHit`, `exists_isFirstHit_of_hitBy`;
* `ae_of_firstHit_of_stop`: **a property holding almost surely at every positive stopping time of the usual
  augmentation inside the strip life holds almost surely at every first hit of `L` inside the strip life.**
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A2TipSep

open QuantumZipper A2X A2Part2

/-! ### Measurability of the tamed flow for a family of drivers -/

/-- **The tamed flow of a measurable family of continuous drivers is measurable** (FD-4 of QuantumZipper for any
family: `measurable_tamed_drive`'s proof through the space `C([0, t], ℝ)`). -/
theorem measurable_tamedZ_family {Ω : Type*} [MeasurableSpace Ω] {D : Ω → ℝ → ℝ} (hDc : ∀ ω, Continuous (D ω))
    {t : ℝ} (ht : 0 ≤ t) (hDm : ∀ r ∈ Icc (0 : ℝ) t, Measurable fun ω => D ω r) {c : ℝ} (hc : 0 < c) (a : ℂ) :
    Measurable fun ω => tamedZ (D ω) c a t := by
  let _ : MeasurableSpace C(Icc (0 : ℝ) t, ℝ) := borel _
  have : BorelSpace C(Icc (0 : ℝ) t, ℝ) := ⟨rfl⟩
  let Φ : Ω → C(Icc (0 : ℝ) t, ℝ) := fun ω => ⟨fun x => D ω x, (hDc ω).comp continuous_subtype_val⟩
  have hΦ : Measurable Φ := measurable_to_continuousMap_Icc Φ fun x => hDm x x.2
  have hagree : ∀ ω, ∀ r ∈ Icc (0 : ℝ) t, D ω r = extIccPath ht (Φ ω) r := fun ω r hr => by
    rw [extIccPath_of_mem ht _ hr]; rfl
  have e : (fun ω => tamedZ (D ω) c a t) =
      (fun p : ℂ × C(Icc (0 : ℝ) t, ℝ) => tamedZ (extIccPath ht p.2) c p.1 t) ∘ (fun ω => (a, Φ ω)) := by
    funext ω
    exact tamedZ_congr_drive (hDc ω) (continuous_extIccPath ht _) hc ht a (hagree ω)
  rw [e]
  exact (continuous_tamed_path hc ht).1.measurable.comp (measurable_const.prodMk hΦ)

/-! ### Hits inside the strip life, pathwise -/

section Det

variable {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {L : Set ℂ}

/-- Some time `≤ t` of the strip life of `v` has hull meeting `L`. -/
def HitBy (w v : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (L : Set ℂ) (t : ℝ≥0) : Prop :=
  ∃ t' ≤ t, Strip.IsStripLife w v ζ t' ∧ (fwdHull (Strip.extPath w) t' ∩ L).Nonempty

theorem HitBy.mono {t t' : ℝ≥0} (h : HitBy w v ζ L t) (htt' : t ≤ t') : HitBy w v ζ L t' := by
  obtain ⟨s, hs, h⟩ := h
  exact ⟨s, hs.trans htt', h⟩

/-- **The strip life is open on the right** for paths continuous before the lifetime. -/
theorem isStripLife_exists_gt (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hv : ContinuousOn v {t | (t : ℝ≥0∞) < ζ})
    {t : ℝ≥0} (h : Strip.IsStripLife w v ζ t) : ∃ r, t < r ∧ Strip.IsStripLife w v ζ r := by
  have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hcw : ContinuousAt (fun s : ℝ≥0 => w s - v s) t :=
    ((hw.sub hv).continuousAt (hopen.mem_nhds h.1))
  have h1 : ∀ᶠ s : ℝ≥0 in 𝓝 t, (s : ℝ≥0∞) < ζ := hopen.mem_nhds h.1
  have hev : ∀ᶠ s : ℝ≥0 in 𝓝 t, (s : ℝ≥0∞) < ζ ∧ 0 < w s - v s :=
    h1.and (hcw.eventually (lt_mem_nhds (sub_pos.2 (h.2 t le_rfl))))
  obtain ⟨ε, hε, hP⟩ := Metric.eventually_nhds_iff.1 hev
  set r : ℝ≥0 := t + (ε / 2).toNNReal with hr
  have hrr : (r : ℝ) = t + ε / 2 := by
    rw [hr, NNReal.coe_add, Real.coe_toNNReal _ (by positivity)]
  have hdist : ∀ r' : ℝ≥0, t ≤ r' → r' ≤ r → dist r' t < ε := by
    intro r' h1 h2
    rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 h1))]
    have : (r' : ℝ) ≤ r := NNReal.coe_le_coe.2 h2
    linarith
  refine ⟨r, lt_add_of_pos_right t (Real.toNNReal_pos.2 (by positivity)),
    (hP (hdist r le_self_add le_rfl)).1, fun r' hr' => ?_⟩
  rcases le_total r' t with hle | hle
  · exact h.2 r' hle
  · exact sub_pos.1 (hP (hdist r' hle hr')).2

/-- **A countable formula for `HitBy`**: either the time `t` itself is in the strip life and hits, or some rational
time `≤ t` does (the strip life is open on the right). -/
theorem hitBy_iff_rat (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hv : ContinuousOn v {t | (t : ℝ≥0∞) < ζ})
    (t : ℝ≥0) : HitBy w v ζ L t ↔ (Strip.IsStripLife w v ζ t ∧ (fwdHull (Strip.extPath w) t ∩ L).Nonempty) ∨
      ∃ q : ℚ≥0, (q : ℝ≥0) ≤ t ∧ Strip.IsStripLife w v ζ q ∧ (fwdHull (Strip.extPath w) q ∩ L).Nonempty := by
  constructor
  · rintro ⟨t', ht', hl, hh⟩
    by_cases hlt : Strip.IsStripLife w v ζ t
    · left
      exact ⟨hlt, hh.mono (inter_subset_inter_left _ (fwdHull_subset_of_le (NNReal.coe_le_coe.2 ht')))⟩
    · right
      obtain ⟨r, htr, hlr⟩ := isStripLife_exists_gt hw hv hl
      have ht't : t' < t := lt_of_le_of_ne ht' fun h => hlt (h ▸ hl)
      have hrt : t' < min r t := lt_min htr ht't
      obtain ⟨_, ⟨q, rfl⟩, hq1, hq2⟩ := LocalExt.dense_range_coe_nnrat.exists_between hrt
      refine ⟨q, (hq2.trans_le (min_le_right _ _)).le, hlr.mono (hq2.trans_le (min_le_left _ _)).le,
        hh.mono (inter_subset_inter_left _ (fwdHull_subset_of_le (NNReal.coe_le_coe.2 hq1.le)))⟩
  · rintro (⟨hl, hh⟩ | ⟨q, hq, hl, hh⟩)
    · exact ⟨t, le_rfl, hl, hh⟩
    · exact ⟨q, hq, hl, hh⟩

/-- At a first hit inside the strip life, `HitBy` holds exactly from that time on. -/
theorem hitBy_iff_of_isFirstHit {s : ℝ≥0} (hs : IsFirstHit (Strip.extPath w) L s)
    (hl : Strip.IsStripLife w v ζ s) (t : ℝ≥0) : HitBy w v ζ L t ↔ s ≤ t := by
  constructor
  · rintro ⟨t', ht', -, hh⟩
    by_contra hst
    push Not at hst
    have hlt : (t' : ℝ) < s := NNReal.coe_lt_coe.2 (ht'.trans_lt hst)
    have := hs.2.2 t' t'.2 hlt
    rw [this] at hh
    exact hh.ne_empty rfl
  · exact fun h => ⟨s, h, hl, hs.2.1⟩

/-- **`HitBy` comes from a first hit inside the strip life.** -/
theorem exists_isFirstHit_of_hitBy (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hL : IsCompact L) (hLH : L ⊆ H)
    {t : ℝ≥0} (h : HitBy w v ζ L t) :
    ∃ s : ℝ≥0, IsFirstHit (Strip.extPath w) L s ∧ Strip.IsStripLife w v ζ s := by
  obtain ⟨t', -, hl, hh⟩ := h
  obtain ⟨t₂, ht'₂, ht₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hl.1
  have hlt : (t' : ℝ) < t₂ := NNReal.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 ht'₂)
  have hcont := Strip.continuousOn_extPath hw ht₂ζ
  have hA := Ito.continuous_clampDrv t₂.2 hcont
  have hAeq : EqOn (Ito.clampDrv (Strip.extPath w) t₂) (Strip.extPath w) (Icc 0 t₂) := Ito.clampDrv_eqOn
  have hK : ∀ r : ℝ, 0 ≤ r → r ≤ t' → fwdHull (Ito.clampDrv (Strip.extPath w) t₂) r = fwdHull (Strip.extPath w) r :=
    fun r h0 h1 => LocalExt.fwdHull_congr_of_eqOn_of_lt h0 (h1.trans_lt hlt) hAeq
  have hh' : (fwdHull (Ito.clampDrv (Strip.extPath w) t₂) t' ∩ L).Nonempty := by rw [hK t' t'.2 le_rfl]; exact hh
  obtain ⟨s, ⟨hs0, hsK, hsb⟩, hst'⟩ := exists_isFirstHit hA hL hLH t'.2 hh'
  refine ⟨⟨s, hs0⟩, ⟨hs0, ?_, fun r hr0 hrs => ?_⟩, hl.mono (show (⟨s, hs0⟩ : ℝ≥0) ≤ t' from hst')⟩
  · show (fwdHull (Strip.extPath w) s ∩ L).Nonempty
    rw [← hK s hs0 hst']; exact hsK
  · rw [← hK r hr0 (hrs.le.trans hst')]; exact hsb r hr0 hrs

end Det


/-! ### Measurability and the first-hit stopping time -/

section Stop

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓗 : Filtration ℝ≥0 mΩ} {W V : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {L : Set ℂ}

/-- **Strip life and hit at a fixed time are measurable** at that time, for processes adapted and continuous before
the lifetime at every sample. -/
theorem measurableSet_life_hit (hW : AdaptedBefore 𝓗 ζ W) (hV : AdaptedBefore 𝓗 ζ V)
    (hcW : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hcV : ∀ ω, ContinuousOn (V · ω) {t | (t : ℝ≥0∞) < ζ ω}) (hL : IsCompact L) (hLH : L ⊆ H) (r : ℝ≥0) :
    MeasurableSet[𝓗 r] {ω | Strip.IsStripLife (W · ω) (V · ω) (ζ ω) r ∧
      (fwdHull (Strip.extPath (W · ω)) r ∩ L).Nonempty} := by
  have hlife : MeasurableSet[𝓗 r] {ω | Strip.IsStripLife (W · ω) (V · ω) (ζ ω) r} := by
    have := A1RefCD.measurableSet_isStripLife (τ := fun _ => r) hW hV hcW hcV (isStoppingTime_const 𝓗 r)
    rwa [IsStoppingTime.measurableSpace_const] at this
  classical
  set D : Ω → ℝ → ℝ := fun ω => if Strip.IsStripLife (W · ω) (V · ω) (ζ ω) r then
    Ito.clampDrv (Strip.extPath (W · ω)) r else fun _ => 0 with hD
  have hDc : ∀ ω, Continuous (D ω) := by
    intro ω
    by_cases h : Strip.IsStripLife (W · ω) (V · ω) (ζ ω) r
    · simp only [hD, h, ↓reduceIte]
      exact Ito.continuous_clampDrv r.2 (Strip.continuousOn_extPath (hcW ω) h.1)
    · simp only [hD, h, ↓reduceIte]; exact continuous_const
  have hDK : ∀ ω, Strip.IsStripLife (W · ω) (V · ω) (ζ ω) r →
      fwdHull (D ω) r = fwdHull (Strip.extPath (W · ω)) r := by
    intro ω h
    obtain ⟨t₂, hrt₂, ht₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 h.1
    have hlt : (r : ℝ) < t₂ := NNReal.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 hrt₂)
    have hc₂ := Strip.continuousOn_extPath (hcW ω) ht₂ζ
    have hc₁ := Strip.continuousOn_extPath (hcW ω) h.1
    simp only [hD, h, ↓reduceIte]
    refine (YuanCorollary13.fwdHull_eq_of_eqOn_Icc (Ito.continuous_clampDrv r.2 hc₁)
      (Ito.continuous_clampDrv t₂.2 hc₂) r.2 fun x hx =>
        (Ito.clampDrv_eqOn hx).trans (Ito.clampDrv_eqOn ⟨hx.1, hx.2.trans hlt.le⟩).symm).trans ?_
    exact LocalExt.fwdHull_congr_of_eqOn_of_lt r.2 hlt Ito.clampDrv_eqOn
  have hDm : ∀ x ∈ Icc (0 : ℝ) r, Measurable[𝓗 r] fun ω => D ω x := by
    intro x hx
    have hxr : x.toNNReal ≤ r := Real.toNNReal_le_iff_le_coe.2 hx.2
    have e : (fun ω => D ω x) = fun ω => if Strip.IsStripLife (W · ω) (V · ω) (ζ ω) r then
        (if ((x.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω then W x.toNNReal ω else 0) else 0 := by
      funext ω
      by_cases h : Strip.IsStripLife (W · ω) (V · ω) (ζ ω) r
      · have hxζ : ((x.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω := (ENNReal.coe_le_coe.2 hxr).trans_lt h.1
        simp only [hD, h, hxζ, ↓reduceIte]
        rw [Ito.clampDrv_eqOn hx]; rfl
      · simp only [hD, h, ↓reduceIte]
    rw [e]
    exact Measurable.ite hlife ((Sec2.measurable_killed_of_adaptedBefore hW x.toNNReal 0).mono
      (𝓗.mono hxr) le_rfl) measurable_const
  have hhit : MeasurableSet[𝓗 r] {ω | (L ∩ fwdHull (D ω) r).Nonempty} :=
    @ZhanGT4.measurableSet_hit Ω (𝓗 r) D hDc r r.2 (fun k q hq0 hqr a =>
      @measurable_tamedZ_family Ω (𝓗 r) D hDc q hq0 (fun x hx => hDm x ⟨hx.1, hx.2.trans hqr⟩) _
        (by positivity) a) L hL hLH
  have e : {ω | Strip.IsStripLife (W · ω) (V · ω) (ζ ω) r ∧ (fwdHull (Strip.extPath (W · ω)) r ∩ L).Nonempty} =
      {ω | Strip.IsStripLife (W · ω) (V · ω) (ζ ω) r} ∩ {ω | (L ∩ fwdHull (D ω) r).Nonempty} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨h, hh⟩; exact ⟨h, by rw [hDK ω h, inter_comm]; exact hh⟩
    · rintro ⟨h, hh⟩; exact ⟨h, by rw [hDK ω h, inter_comm] at hh; exact hh⟩
  rw [e]
  exact hlife.inter hhit


/-- **`HitBy` at a fixed time is measurable** at that time (the countable formula `hitBy_iff_rat`). -/
theorem measurableSet_hitBy (hW : AdaptedBefore 𝓗 ζ W) (hV : AdaptedBefore 𝓗 ζ V)
    (hcW : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hcV : ∀ ω, ContinuousOn (V · ω) {t | (t : ℝ≥0∞) < ζ ω}) (hL : IsCompact L) (hLH : L ⊆ H) (t : ℝ≥0) :
    MeasurableSet[𝓗 t] {ω | HitBy (W · ω) (V · ω) (ζ ω) L t} := by
  have e : {ω | HitBy (W · ω) (V · ω) (ζ ω) L t} =
      {ω | Strip.IsStripLife (W · ω) (V · ω) (ζ ω) t ∧ (fwdHull (Strip.extPath (W · ω)) t ∩ L).Nonempty} ∪
        ⋃ q : ℚ≥0, {ω | (q : ℝ≥0) ≤ t ∧ (Strip.IsStripLife (W · ω) (V · ω) (ζ ω) q ∧
          (fwdHull (Strip.extPath (W · ω)) q ∩ L).Nonempty)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_iUnion]
    exact hitBy_iff_rat (hcW ω) (hcV ω) t
  rw [e]
  refine (measurableSet_life_hit hW hV hcW hcV hL hLH t).union (MeasurableSet.iUnion fun q => ?_)
  by_cases hq : (q : ℝ≥0) ≤ t
  · have e2 : {ω | (q : ℝ≥0) ≤ t ∧ (Strip.IsStripLife (W · ω) (V · ω) (ζ ω) q ∧
        (fwdHull (Strip.extPath (W · ω)) q ∩ L).Nonempty)} =
        {ω | Strip.IsStripLife (W · ω) (V · ω) (ζ ω) q ∧ (fwdHull (Strip.extPath (W · ω)) q ∩ L).Nonempty} := by
      ext ω; simp only [mem_ofPred_eq, hq, true_and]
    rw [e2]
    exact 𝓗.mono hq _ (measurableSet_life_hit hW hV hcW hcV hL hLH q)
  · have e2 : {ω | (q : ℝ≥0) ≤ t ∧ (Strip.IsStripLife (W · ω) (V · ω) (ζ ω) q ∧
        (fwdHull (Strip.extPath (W · ω)) q ∩ L).Nonempty)} = ∅ := by
      ext ω; simp only [mem_ofPred_eq, hq, false_and, mem_empty_iff_false]
    rw [e2]
    exact @MeasurableSet.empty _ (𝓗 t)

open scoped Classical in
/-- **The first hit of `L` inside the strip life, capped at `N`** (`N` when there is no such hit by `N`). -/
def hitTime (W V : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (L : Set ℂ) (N : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  if HitBy (W · ω) (V · ω) (ζ ω) L N then sInf {t | HitBy (W · ω) (V · ω) (ζ ω) L t} else N

theorem hitTime_le_iff (hcW : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω}) (hL : IsCompact L)
    (hLH : L ⊆ H) (N t : ℝ≥0) (ω : Ω) :
    hitTime W V ζ L N ω ≤ t ↔ N ≤ t ∨ HitBy (W · ω) (V · ω) (ζ ω) L t := by
  unfold hitTime
  split_ifs with h
  · obtain ⟨s, hs, hl⟩ := exists_isFirstHit_of_hitBy (hcW ω) hL hLH h
    have hset : {t | HitBy (W · ω) (V · ω) (ζ ω) L t} = Ici s := by
      ext t; exact hitBy_iff_of_isFirstHit hs hl t
    rw [hset, csInf_Ici]
    have hsN : s ≤ N := (hitBy_iff_of_isFirstHit hs hl N).1 h
    constructor
    · intro hst; right; exact (hitBy_iff_of_isFirstHit hs hl t).2 hst
    · rintro (hNt | hh)
      · exact hsN.trans hNt
      · exact (hitBy_iff_of_isFirstHit hs hl t).1 hh
  · constructor
    · intro hNt; left; exact hNt
    · rintro (hNt | hh)
      · exact hNt
      · by_contra hlt
        push Not at hlt
        exact h (hh.mono hlt.le)

/-- **The capped first hit is a stopping time.** -/
theorem isStoppingTime_hitTime (hW : AdaptedBefore 𝓗 ζ W) (hV : AdaptedBefore 𝓗 ζ V)
    (hcW : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hcV : ∀ ω, ContinuousOn (V · ω) {t | (t : ℝ≥0∞) < ζ ω}) (hL : IsCompact L) (hLH : L ⊆ H) (N : ℝ≥0) :
    IsStoppingTime 𝓗 fun ω => (hitTime W V ζ L N ω : WithTop ℝ≥0) := by
  intro t
  have e : {ω | (hitTime W V ζ L N ω : WithTop ℝ≥0) ≤ t} = {ω | N ≤ t ∨ HitBy (W · ω) (V · ω) (ζ ω) L t} := by
    ext ω
    simp only [mem_ofPred_eq, WithTop.coe_le_coe]
    exact hitTime_le_iff hcW hL hLH N t ω
  rw [e]
  by_cases hNt : N ≤ t
  · simp only [hNt, true_or, ofPred_true]; exact MeasurableSet.univ
  · simp only [hNt, false_or]
    exact measurableSet_hitBy hW hV hcW hcV hL hLH t

/-- At a first hit inside the strip life before `N`, the capped first hit is that time. -/
theorem hitTime_eq_of_isFirstHit {ω : Ω} {s N : ℝ≥0} (hs : IsFirstHit (Strip.extPath (W · ω)) L s)
    (hl : Strip.IsStripLife (W · ω) (V · ω) (ζ ω) s) (hsN : s ≤ N) : hitTime W V ζ L N ω = s := by
  unfold hitTime
  simp only [(hitBy_iff_of_isFirstHit hs hl _).2 hsN, ↓reduceIte]
  have hset : {t | HitBy (W · ω) (V · ω) (ζ ω) L t} = Ici s := by
    ext t; exact hitBy_iff_of_isFirstHit hs hl t
  rw [hset, csInf_Ici]

/-- A first hit inside the strip life is positive (the hull at time `0` is empty). -/
theorem pos_of_isFirstHit {w v : ℝ≥0 → ℝ} {ζ₀ : ℝ≥0∞} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ₀}) {s : ℝ≥0}
    (hs : IsFirstHit (Strip.extPath w) L s) (hl : Strip.IsStripLife w v ζ₀ s) : 0 < s := by
  rcases eq_or_lt_of_le (zero_le (a := s)) with h0 | h0
  · exfalso
    have hζ0 : (0 : ℝ≥0∞) < ζ₀ := by rw [← ENNReal.coe_zero, h0]; exact hl.1
    obtain ⟨t₂, ht₂0, ht₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hζ0
    have ht₂ : (0 : ℝ) < t₂ := NNReal.coe_pos.2 (ENNReal.coe_pos.1 ht₂0)
    have hcont₂ := Strip.continuousOn_extPath hw ht₂ζ
    have hK : fwdHull (Strip.extPath w) 0 = ∅ := by
      rw [← LocalExt.fwdHull_congr_of_eqOn_of_lt le_rfl ht₂ (Ito.clampDrv_eqOn (W := Strip.extPath w))]
      exact RS.fwdHull_zero_eq_empty (Ito.continuous_clampDrv t₂.2 hcont₂)
    have := hs.2.1
    rw [← h0, NNReal.coe_zero, hK, empty_inter] at this
    exact this.ne_empty rfl
  · exact h0

/-- **From stopping times to first hits, everywhere-regular processes** (the countable argument's stopping,
L555–L561): for processes adapted to `𝓗` and continuous before the lifetime at every sample, a property holding almost
surely at every positive `𝓗`-stopping time inside the strip life holds almost surely at every first hit of the compact
`L ⊆ ℍ` inside the strip life. -/
theorem ae_of_firstHit_of_stop_reg {P : Measure Ω} (hW : AdaptedBefore 𝓗 ζ W) (hV : AdaptedBefore 𝓗 ζ V)
    (hcW : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hcV : ∀ ω, ContinuousOn (V · ω) {t | (t : ℝ≥0∞) < ζ ω}) {Q : ℝ≥0 → Ω → Prop}
    (hQ : ∀ τ : Ω → ℝ≥0, IsStoppingTime 𝓗 (fun ω => (τ ω : WithTop ℝ≥0)) →
      ∀ᵐ ω ∂P, 0 < τ ω → Strip.IsStripLife (W · ω) (V · ω) (ζ ω) (τ ω) → Q (τ ω) ω)
    (hL : IsCompact L) (hLH : L ⊆ H) :
    ∀ᵐ ω ∂P, ∀ s : ℝ≥0, IsFirstHit (Strip.extPath (W · ω)) L s →
      Strip.IsStripLife (W · ω) (V · ω) (ζ ω) s → Q s ω := by
  have hall := ae_all_iff.2 fun N : ℕ => hQ _ (isStoppingTime_hitTime hW hV hcW hcV hL hLH (N : ℝ≥0))
  filter_upwards [hall] with ω hω s hs hl
  obtain ⟨N, hN⟩ := exists_nat_ge (s : ℝ)
  have hτ := hitTime_eq_of_isFirstHit (V := V) (ζ := ζ) hs hl (show s ≤ (N : ℝ≥0) by exact_mod_cast hN)
  have := hω N (by rw [hτ]; exact pos_of_isFirstHit (hcW ω) hs hl) (by rw [hτ]; exact hl)
  rwa [hτ] at this

/-- **From stopping times to first hits** (the countable argument's stopping, L555–L561): a property holding almost
surely at every positive stopping time of the usual augmentation inside the strip life holds almost surely at every
first hit of the compact `L ⊆ ℍ` inside the strip life. The processes are regularized on a measurable null set, which
the usual augmentation contains (`ae_of_firstHit_of_stop_reg` for the regularized processes). -/
theorem ae_of_firstHit_of_stop {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (hW : AdaptedBefore 𝓕 ζ W)
    (hV : AdaptedBefore 𝓕 ζ V)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ ContinuousOn (V · ω) {t | (t : ℝ≥0∞) < ζ ω})
    {Q : ℝ≥0 → Ω → Prop}
    (hQ : ∀ τ : Ω → ℝ≥0, IsStoppingTime (usualAugmentation 𝓕 P) (fun ω => (τ ω : WithTop ℝ≥0)) →
      ∀ᵐ ω ∂P, 0 < τ ω → Strip.IsStripLife (W · ω) (V · ω) (ζ ω) (τ ω) → Q (τ ω) ω)
    (hL : IsCompact L) (hLH : L ⊆ H) :
    ∀ᵐ ω ∂P, ∀ s : ℝ≥0, IsFirstHit (Strip.extPath (W · ω)) L s →
      Strip.IsStripLife (W · ω) (V · ω) (ζ ω) s → Q s ω := by
  classical
  obtain ⟨N₀, hN₀sub, hN₀m, hN₀0⟩ := exists_measurable_superset_of_null (ae_iff.1 hc)
  set reg : (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ := fun X t ω => if ω ∈ N₀ then 0 else X t ω with hreg
  set ζ' : Ω → ℝ≥0∞ := fun ω => if ω ∈ N₀ then 0 else ζ ω with hζ'
  have hG : ∀ t, MeasurableSet[usualAugmentation 𝓕 P t] N₀ := fun t =>
    Ito.measurableSet_usualAugmentation_of_null hN₀m hN₀0 t
  have hadapt : ∀ X : ℝ≥0 → Ω → ℝ, AdaptedBefore 𝓕 ζ X → AdaptedBefore (usualAugmentation 𝓕 P) ζ' (reg X) := by
    intro X hX t A hA
    have e : {ω | (t : ℝ≥0∞) < ζ' ω ∧ reg X t ω ∈ A} = N₀ᶜ ∩ {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω ∈ A} := by
      ext ω
      by_cases h : ω ∈ N₀ <;> simp [hζ', hreg, h]
    rw [e]
    exact (hG t).compl.inter (Ito.le_usualAugmentation 𝓕 P t _ (hX t A hA))
  have hgood : ∀ ω, ω ∉ N₀ →
      ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ ContinuousOn (V · ω) {t | (t : ℝ≥0∞) < ζ ω} :=
    fun ω hω => by by_contra hcon; exact hω (hN₀sub hcon)
  have eX : ∀ X : ℝ≥0 → Ω → ℝ, ∀ ω, ω ∉ N₀ → (reg X · ω) = (X · ω) := fun X ω h => by
    funext t; simp [hreg, h]
  have eζ : ∀ ω, ω ∉ N₀ → ζ' ω = ζ ω := fun ω h => by simp [hζ', h]
  have hcont : ∀ X : ℝ≥0 → Ω → ℝ, (∀ ω, ω ∉ N₀ → ContinuousOn (X · ω) {t | (t : ℝ≥0∞) < ζ ω}) →
      ∀ ω, ContinuousOn (reg X · ω) {t | (t : ℝ≥0∞) < ζ' ω} := by
    intro X hX ω
    by_cases h : ω ∈ N₀
    · have : {t : ℝ≥0 | (t : ℝ≥0∞) < ζ' ω} = ∅ := by ext t; simp [hζ', h]
      rw [this]; exact continuousOn_empty _
    · rw [eX X ω h, eζ ω h]; exact hX ω h
  have hN₀c : ∀ᵐ ω ∂P, ω ∉ N₀ := ae_iff.2 (by simpa using hN₀0)
  have hreg := ae_of_firstHit_of_stop_reg (P := P) (Q := Q) (hadapt W hW) (hadapt V hV)
    (hcont W fun ω h => (hgood ω h).1) (hcont V fun ω h => (hgood ω h).2) (fun τ hτ => by
      filter_upwards [hQ τ hτ, hN₀c] with ω hω hωN hτ0 hl
      rw [eX W ω hωN, eX V ω hωN, eζ ω hωN] at hl
      exact hω hτ0 hl) hL hLH
  filter_upwards [hreg, hN₀c] with ω hω hωN s hs hl
  rw [← eX W ω hωN] at hs
  exact hω s hs (by rw [eX W ω hωN, eX V ω hωN, eζ ω hωN]; exact hl)

end Stop

end InteractingSLE.ZhanGT4.A2TipSep
