/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.StoppedExtendWFDet

/-!
# Galmarino rules on killed histories: capped rules are trivial; first-hit rules

Packet PROVE-L1G. The Galmarino form of Aux. lemma 54 (`StoppedExtendWF.StoppedHullExtendGKStatement`) and of (L1)
(`StoppedExtendWF.FlowLineStopIdentGStatement`) ask for a measurable rule `R` on killed histories with
`StoppedExtendWF.IsHistGalmarino R`: if two continuous histories live until `R γ` and agree before `R γ`, then `R` takes
the same value on them.

* **Capped rules are trivial** (`eq_zero_of_isHistGalmarino_of_le_fst`). The history killed at time `0` (`zeroHist`) is
  continuous and agrees with every history before time `0`. So a Galmarino rule with `R γ ≤ γ.1` for every `γ` is `0` on
  every continuous history (`not_isHistGalmarino_of_le_fst`). In particular the rule
  `R γ = min (γ.1, exit time read from γ)` proposed in `planning/handoffs/PROVE-DOMAINMARKOV10.md` §4.3 (and the
  first-contact rules "capped at the history's lifetime" of its §3) are **not** Galmarino. A history killed before its
  exit time has `R γ = γ.1`, while a longer continuation has the later exit time. A Galmarino rule must read the stop
  from the samples, including the left limit at the end of the record.
* **Strong Galmarino rules** (`IsStrongGalmarino`): agreement before any `r ≥ R γ` fixes the value. They are Galmarino
  (`IsStrongGalmarino.isHistGalmarino`), and they are closed under `min` (`IsStrongGalmarino.min`). Constants are
  strong.
* **First-hit rules** (`hitRule ψ F`): for an observable `ψ γ t` of the history that is non-anticipating
  (`IsNonAnticipating`: its value at a dyadic time `q` depends only on the samples at dyadic times `≤ q`) and any set
  `F`, `hitGap ψ F γ t` is the infimum of `infEDist (ψ γ q) F` over dyadic `q < t` with `q < γ.1`. The rule is the first
  `t ≤ γ.1` with zero gap **when that first time is attained**, and `⊤` otherwise. It is strong Galmarino with no
  continuity assumption (`isStrongGalmarino_hitRule`) and measurable (`measurable_hitRule`). On a record of a path `g`
  that is continuous up to a first hit `T > 0` of a closed `F`, it equals `T` (`hitRule_eq_of_hit`). If `g` stays off
  `F` before `e`, it is at least `e` (`le_hitRule_of_off`). `hitRuleSeq` is the same for a countable union of closed
  sets (`isStrongGalmarino_hitRuleSeq`, `measurable_hitRuleSeq`, `hitRuleSeq_eq_of_hit`, `le_hitRuleSeq_of_off`).
* **Readers**: `histState` (the state at time `t`, as the limit of the samples at the dyadic times below `t`) and
  `histTrace y` (the trace point `y + LP.traceAt t (driver read from the history)`), both non-anticipating and
  measurable. On a killed history they give the state and the generating trace (`histState_killedHistory`,
  `histTrace_killedHistory`).
* **The threshold set** of a force word as a countable union of closed sets: `thrSet ρL ρR m` (closed,
  `isClosed_thrSet`), contained in `ForceWord.ThresholdCondition` (`thresholdCondition_of_mem_thrSet`) and covering it
  (`exists_mem_thrSet`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

namespace FlowStopIdentG

open LawUnique StoppedExtendWF

variable {nL nR : ℕ}

/-! ### Capped rules are trivial -/

/-- The history killed at time `0` (it records no sample). -/
def zeroHist : HistorySpace nL nR := (0, fun _ => 0)

theorem isKilledContHist_zeroHist : IsKilledContHist (zeroHist : HistorySpace nL nR) :=
  ⟨fun _ => 0, continuousOn_const, fun _ hp => (ENNReal.not_lt_zero hp).elim⟩

/-- **A Galmarino rule that vanishes on the empty history vanishes on every continuous history.** -/
theorem eq_zero_of_isHistGalmarino {R : HistorySpace nL nR → ℝ≥0∞} (hR : IsHistGalmarino R)
    (h0 : R zeroHist = 0) {γ : HistorySpace nL nR} (hγ : IsKilledContHist γ) : R γ = 0 := by
  have h := hR zeroHist γ isKilledContHist_zeroHist hγ (by rw [h0]; exact zero_le) (by rw [h0]; exact zero_le)
    (fun _ hp => by rw [h0] at hp; exact (ENNReal.not_lt_zero hp).elim)
  rw [h, h0]

/-- **Capped Galmarino rules are trivial**: a Galmarino rule with `R γ ≤ γ.1` for every history is `0` on every
continuous history. -/
theorem eq_zero_of_isHistGalmarino_of_le_fst {R : HistorySpace nL nR → ℝ≥0∞} (hR : IsHistGalmarino R)
    (hle : ∀ γ, R γ ≤ γ.1) {γ : HistorySpace nL nR} (hγ : IsKilledContHist γ) : R γ = 0 :=
  eq_zero_of_isHistGalmarino hR (le_antisymm (hle zeroHist) zero_le) hγ

/-- **A capped rule that is positive on one continuous history is not Galmarino.** This applies to
`γ ↦ min γ.1 (exit time read from γ)` on the killed history of any stopped path with a positive stop. -/
theorem not_isHistGalmarino_of_le_fst {R : HistorySpace nL nR → ℝ≥0∞} (hle : ∀ γ, R γ ≤ γ.1)
    {γ : HistorySpace nL nR} (hγ : IsKilledContHist γ) (hne : R γ ≠ 0) : ¬ IsHistGalmarino R :=
  fun hR => hne (eq_zero_of_isHistGalmarino_of_le_fst hR hle hγ)

/-! ### Strong Galmarino rules -/

/-- Two histories agree at every dyadic time before `r`. -/
def AgreeBefore (γ γ' : HistorySpace nL nR) (r : ℝ≥0∞) : Prop :=
  ∀ p : ℕ × ℕ, (dyadicTime p : ℝ≥0∞) < r → γ.2 p = γ'.2 p

theorem AgreeBefore.symm {γ γ' : HistorySpace nL nR} {r : ℝ≥0∞} (h : AgreeBefore γ γ' r) :
    AgreeBefore γ' γ r :=
  fun p hp => (h p hp).symm

/-- **Strong Galmarino rules**: if two continuous histories live until `r`, agree before `r`, and `R γ ≤ r`, then
`R γ' = R γ`. -/
def IsStrongGalmarino (R : HistorySpace nL nR → ℝ≥0∞) : Prop :=
  ∀ γ γ' : HistorySpace nL nR, IsKilledContHist γ → IsKilledContHist γ' → ∀ r : ℝ≥0∞, r ≤ γ.1 → r ≤ γ'.1 →
    AgreeBefore γ γ' r → R γ ≤ r → R γ' = R γ

theorem IsStrongGalmarino.isHistGalmarino {R : HistorySpace nL nR → ℝ≥0∞} (hR : IsStrongGalmarino R) :
    IsHistGalmarino R :=
  fun γ γ' hγ hγ' h1 h2 hag => hR γ γ' hγ hγ' (R γ) h1 h2 hag le_rfl

theorem isStrongGalmarino_const (c : ℝ≥0∞) : IsStrongGalmarino fun _ : HistorySpace nL nR => c :=
  fun _ _ _ _ _ _ _ _ _ => rfl

/-- A strong Galmarino rule beyond `r` on one history is beyond `r` on every history that agrees with it before `r`. -/
theorem IsStrongGalmarino.lt_of_lt {R : HistorySpace nL nR → ℝ≥0∞} (hR : IsStrongGalmarino R)
    {γ γ' : HistorySpace nL nR} (hγ : IsKilledContHist γ) (hγ' : IsKilledContHist γ') {r : ℝ≥0∞} (h1 : r ≤ γ.1)
    (h2 : r ≤ γ'.1) (hag : AgreeBefore γ γ' r) (hlt : r < R γ) : r < R γ' := by
  by_contra h
  push Not at h
  have e := hR γ' γ hγ' hγ r h2 h1 hag.symm h
  rw [e] at hlt
  exact absurd h (not_le.2 hlt)

/-- **The minimum of two strong Galmarino rules is strong Galmarino.** -/
theorem IsStrongGalmarino.min {R₁ R₂ : HistorySpace nL nR → ℝ≥0∞} (h₁ : IsStrongGalmarino R₁)
    (h₂ : IsStrongGalmarino R₂) : IsStrongGalmarino fun γ => min (R₁ γ) (R₂ γ) := by
  intro γ γ' hγ hγ' r h1 h2 hag hle
  change Min.min (R₁ γ) (R₂ γ) ≤ r at hle
  change Min.min (R₁ γ') (R₂ γ') = Min.min (R₁ γ) (R₂ γ)
  by_cases ha : R₁ γ ≤ r
  · have e₁ := h₁ γ γ' hγ hγ' r h1 h2 hag ha
    by_cases hb : R₂ γ ≤ r
    · rw [e₁, h₂ γ γ' hγ hγ' r h1 h2 hag hb]
    · have hb' := h₂.lt_of_lt hγ hγ' h1 h2 hag (not_le.1 hb)
      rw [e₁, min_eq_left (ha.trans hb'.le), min_eq_left (ha.trans (not_le.1 hb).le)]
  · have hb : R₂ γ ≤ r := by
      rcases min_le_iff.1 hle with h | h
      · exact absurd h ha
      · exact h
    have e₂ := h₂ γ γ' hγ hγ' r h1 h2 hag hb
    have ha' := h₁.lt_of_lt hγ hγ' h1 h2 hag (not_le.1 ha)
    rw [e₂, min_eq_right (hb.trans ha'.le), min_eq_right (hb.trans (not_le.1 ha).le)]

/-! ### Dyadic times are dense -/

/-- Between two extended nonnegative reals there is a dyadic time. -/
theorem exists_dyadicTime_btwn {a b : ℝ≥0∞} (h : a < b) :
    ∃ p : ℕ × ℕ, a < dyadicTime p ∧ (dyadicTime p : ℝ≥0∞) < b := by
  obtain ⟨r, har, hrb⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 h
  obtain ⟨r', har', hr'r⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 har
  have hr : r' < r := ENNReal.coe_lt_coe.1 hr'r
  obtain ⟨n, hn⟩ := ((tendsto_dyadicTime_lowerDyadic r).eventually (lt_mem_nhds hr)).exists
  exact ⟨lowerDyadic r n, har'.trans (ENNReal.coe_lt_coe.2 hn),
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (dyadicTime_lowerDyadic_le r n)) hrb⟩

/-! ### First-hit rules -/

section Hit

variable {E : Type*} [PseudoEMetricSpace E]

/-- **The left gap** of the observable `ψ` to the set `F` before `t`: the infimum of `infEDist (ψ γ q) F` over the
dyadic times `q < t` before the recorded stop (`⊤` if there is none). -/
def hitGap (ψ : HistorySpace nL nR → ℝ≥0 → E) (F : Set E) (γ : HistorySpace nL nR) (t : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ p : ℕ × ℕ, if (dyadicTime p : ℝ≥0∞) < t ∧ (dyadicTime p : ℝ≥0∞) < γ.1 then
    Metric.infEDist (ψ γ (dyadicTime p)) F else ⊤

/-- The first time `t ≤ γ.1` with zero left gap. -/
def hitStart (ψ : HistorySpace nL nR → ℝ≥0 → E) (F : Set E) (γ : HistorySpace nL nR) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0∞) (_ : t ≤ γ.1 ∧ hitGap ψ F γ t = 0), t

/-- **The first-hit rule**: `hitStart` when it is finite and attained (zero left gap at it), `⊤` otherwise. -/
def hitRule (ψ : HistorySpace nL nR → ℝ≥0 → E) (F : Set E) (γ : HistorySpace nL nR) : ℝ≥0∞ :=
  if hitStart ψ F γ < ⊤ ∧ hitGap ψ F γ (hitStart ψ F γ) = 0 then hitStart ψ F γ else ⊤

/-- **Non-anticipating observables**: the value at a dyadic time `q` depends only on the samples at dyadic times
`≤ q`. -/
def IsNonAnticipating (ψ : HistorySpace nL nR → ℝ≥0 → E) : Prop :=
  ∀ (γ γ' : HistorySpace nL nR) (p : ℕ × ℕ),
    (∀ p' : ℕ × ℕ, dyadicTime p' ≤ dyadicTime p → γ.2 p' = γ'.2 p') → ψ γ (dyadicTime p) = ψ γ' (dyadicTime p)

variable {ψ : HistorySpace nL nR → ℝ≥0 → E} {F : Set E}

theorem hitGap_anti (γ : HistorySpace nL nR) {s t : ℝ≥0∞} (hst : s ≤ t) : hitGap ψ F γ t ≤ hitGap ψ F γ s := by
  refine iInf_mono fun p => ?_
  by_cases hs : (dyadicTime p : ℝ≥0∞) < s ∧ (dyadicTime p : ℝ≥0∞) < γ.1
  · rw [ite_eq_left hs, ite_eq_left ⟨lt_of_lt_of_le hs.1 hst, hs.2⟩]
  · rw [ite_eq_right hs]
    exact le_top

theorem hitStart_le {γ : HistorySpace nL nR} {t : ℝ≥0∞} (ht : t ≤ γ.1) (h0 : hitGap ψ F γ t = 0) :
    hitStart ψ F γ ≤ t :=
  iInf₂_le t ⟨ht, h0⟩

theorem le_hitStart {γ : HistorySpace nL nR} {s : ℝ≥0∞} (h : ∀ t, t ≤ γ.1 → hitGap ψ F γ t = 0 → s ≤ t) :
    s ≤ hitStart ψ F γ :=
  le_iInf₂ fun t ht => h t ht.1 ht.2

theorem hitStart_le_hitRule (γ : HistorySpace nL nR) : hitStart ψ F γ ≤ hitRule ψ F γ := by
  unfold hitRule
  split_ifs
  · exact le_rfl
  · exact le_top

/-- Two histories with the same observable at the dyadic times before `t ≤` both stops have the same gap at `t`. -/
theorem hitGap_congr {γ γ' : HistorySpace nL nR} {t : ℝ≥0∞} (ht : t ≤ γ.1) (ht' : t ≤ γ'.1)
    (h : ∀ p : ℕ × ℕ, (dyadicTime p : ℝ≥0∞) < t → ψ γ (dyadicTime p) = ψ γ' (dyadicTime p)) :
    hitGap ψ F γ t = hitGap ψ F γ' t := by
  refine iInf_congr fun p => ?_
  by_cases hp : (dyadicTime p : ℝ≥0∞) < t
  · rw [ite_eq_left ⟨hp, lt_of_lt_of_le hp ht⟩, ite_eq_left ⟨hp, lt_of_lt_of_le hp ht'⟩, h p hp]
  · rw [ite_eq_right fun h' => hp h'.1, ite_eq_right fun h' => hp h'.1]

omit [PseudoEMetricSpace E] in
/-- A non-anticipating observable agrees on two histories at the dyadic times before `r` if they agree before `r`. -/
theorem IsNonAnticipating.eq_of_agreeBefore (hψ : IsNonAnticipating ψ) {γ γ' : HistorySpace nL nR} {r : ℝ≥0∞}
    (hag : AgreeBefore γ γ' r) {p : ℕ × ℕ} (hp : (dyadicTime p : ℝ≥0∞) < r) :
    ψ γ (dyadicTime p) = ψ γ' (dyadicTime p) :=
  hψ γ γ' p fun p' hp' => hag p' (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hp') hp)

/-- Two histories that live until `r` and agree before `r` are equal when `r = ⊤`. -/
theorem eq_of_agreeBefore_top {γ γ' : HistorySpace nL nR} (h1 : ⊤ ≤ γ.1) (h2 : ⊤ ≤ γ'.1)
    (hag : AgreeBefore γ γ' ⊤) : γ' = γ :=
  Prod.ext ((top_le_iff.1 h2).trans (top_le_iff.1 h1).symm)
    (funext fun p => (hag p ENNReal.coe_lt_top).symm)

/-- **First-hit rules are strong Galmarino** (no continuity assumption). -/
theorem isStrongGalmarino_hitRule (hψ : IsNonAnticipating ψ) (F : Set E) : IsStrongGalmarino (hitRule ψ F) := by
  intro γ γ' _ _ r h1 h2 hag hle
  by_cases hA : hitStart ψ F γ < ⊤ ∧ hitGap ψ F γ (hitStart ψ F γ) = 0
  · have hRs : hitRule ψ F γ = hitStart ψ F γ := ite_eq_left hA
    rw [hRs] at hle
    have hgap : ∀ t, t ≤ r → hitGap ψ F γ' t = hitGap ψ F γ t := fun t ht =>
      (hitGap_congr (ht.trans h1) (ht.trans h2) fun p hp => hψ.eq_of_agreeBefore hag (lt_of_lt_of_le hp ht)).symm
    have hs' : hitStart ψ F γ' = hitStart ψ F γ := by
      refine le_antisymm (hitStart_le (hle.trans h2) (by rw [hgap _ hle]; exact hA.2)) (le_hitStart fun t ht h0 => ?_)
      by_contra hts
      push Not at hts
      have htr : t ≤ r := hts.le.trans hle
      exact absurd (hitStart_le (htr.trans h1) (by rw [← hgap t htr]; exact h0)) (not_le.2 hts)
    rw [hRs]
    unfold hitRule
    rw [ite_eq_left ⟨hs' ▸ hA.1, by rw [hs', hgap _ hle]; exact hA.2⟩, hs']
  · have hR : hitRule ψ F γ = ⊤ := ite_eq_right hA
    rw [hR, top_le_iff] at hle
    subst hle
    rw [eq_of_agreeBefore_top h1 h2 hag]

/-! #### Measurability -/

section Meas

variable [MeasurableSpace E] [OpensMeasurableSpace E]

theorem measurable_hitGap_comp (hψ : ∀ p : ℕ × ℕ, Measurable fun γ : HistorySpace nL nR => ψ γ (dyadicTime p))
    (F : Set E) {τ : HistorySpace nL nR → ℝ≥0∞} (hτ : Measurable τ) :
    Measurable fun γ => hitGap ψ F γ (τ γ) := by
  refine Measurable.iInf fun p => Measurable.ite ?_
    ((Metric.continuous_infEDist (s := F)).measurable.comp (hψ p)) measurable_const
  exact (measurableSet_lt measurable_const hτ).inter (measurableSet_lt measurable_const measurable_fst)

theorem measurable_hitStart (hψ : ∀ p : ℕ × ℕ, Measurable fun γ : HistorySpace nL nR => ψ γ (dyadicTime p))
    (F : Set E) : Measurable (hitStart ψ F) := by
  refine measurable_of_Iio fun c => ?_
  have e : hitStart ψ F ⁻¹' Iio c =
      (⋃ p : ℕ × ℕ, {γ : HistorySpace nL nR | (dyadicTime p : ℝ≥0∞) < c ∧
        ((dyadicTime p : ℝ≥0∞) ≤ γ.1 ∧ hitGap ψ F γ (dyadicTime p) = 0)}) ∪
      {γ | γ.1 < c ∧ hitGap ψ F γ γ.1 = 0} := by
    ext γ
    simp only [mem_preimage, mem_Iio, mem_union, mem_iUnion, mem_ofPred_eq]
    constructor
    · intro h
      obtain ⟨t, ⟨ht1, ht0⟩, htc⟩ : ∃ t, (t ≤ γ.1 ∧ hitGap ψ F γ t = 0) ∧ t < c := by
        unfold hitStart at h
        simpa only [iInf_lt_iff, exists_prop] using h
      by_cases hc : γ.1 < c
      · exact Or.inr ⟨hc, le_antisymm ((hitGap_anti γ ht1).trans ht0.le) (zero_le)⟩
      · obtain ⟨p, hp1, hp2⟩ := exists_dyadicTime_btwn htc
        exact Or.inl ⟨p, hp2, (hp2.le.trans (not_lt.1 hc)),
          le_antisymm ((hitGap_anti γ hp1.le).trans ht0.le) (zero_le)⟩
    · rintro (⟨p, hpc, hp1, hp0⟩ | ⟨hc, h0⟩)
      · exact lt_of_le_of_lt (hitStart_le hp1 hp0) hpc
      · exact lt_of_le_of_lt (hitStart_le le_rfl h0) hc
  rw [e]
  refine (MeasurableSet.iUnion fun p => ?_).union ?_
  · refine (MeasurableSet.const _).inter ((measurableSet_le measurable_const measurable_fst).inter ?_)
    exact measurableSet_eq_fun (measurable_hitGap_comp hψ F measurable_const) measurable_const
  · exact (measurableSet_lt measurable_fst measurable_const).inter
      (measurableSet_eq_fun (measurable_hitGap_comp hψ F measurable_fst) measurable_const)

/-- **First-hit rules are measurable.** -/
theorem measurable_hitRule (hψ : ∀ p : ℕ × ℕ, Measurable fun γ : HistorySpace nL nR => ψ γ (dyadicTime p))
    (F : Set E) : Measurable (hitRule ψ F) := by
  have hs := measurable_hitStart hψ F
  exact Measurable.ite ((measurableSet_lt hs measurable_const).inter
    (measurableSet_eq_fun (measurable_hitGap_comp hψ F hs) measurable_const)) hs measurable_const

end Meas

/-! #### Values on regular records -/

/-- **Positive gap** before a time up to which the recorded path stays off the closed set `F`. -/
theorem pos_hitGap (hF : IsClosed F) {γ : HistorySpace nL nR} {g : ℝ≥0 → E} {T : ℝ≥0}
    (hg : ContinuousOn g (Iic T)) (hoff : ∀ s ≤ T, g s ∉ F)
    (hψg : ∀ p : ℕ × ℕ, dyadicTime p ≤ T → (dyadicTime p : ℝ≥0∞) < γ.1 → ψ γ (dyadicTime p) = g (dyadicTime p))
    {t : ℝ≥0∞} (ht : t ≤ T) : 0 < hitGap ψ F γ t := by
  have hfc : ContinuousOn (fun s => Metric.infEDist (g s) F) (Iic T) :=
    (Metric.continuous_infEDist (s := F)).comp_continuousOn hg
  have hK : IsCompact (Iic T) := by
    have e : Iic T = Icc 0 T := by
      ext s
      simp
    rw [e]
    exact isCompact_Icc
  obtain ⟨s₀, hs₀, hmin⟩ := hK.exists_isMinOn ⟨0, Set.mem_Iic.2 zero_le⟩ hfc
  have hpos : 0 < Metric.infEDist (g s₀) F :=
    Metric.infEDist_pos_iff_notMem_closure.2 (by rw [hF.closure_eq]; exact hoff s₀ hs₀)
  refine lt_of_lt_of_le hpos (le_iInf fun p => ?_)
  by_cases hp : (dyadicTime p : ℝ≥0∞) < t ∧ (dyadicTime p : ℝ≥0∞) < γ.1
  · rw [ite_eq_left hp]
    have hpT : dyadicTime p ≤ T := ENNReal.coe_le_coe.1 (hp.1.le.trans ht)
    rw [hψg p hpT hp.2]
    exact hmin hpT
  · rw [ite_eq_right hp]
    exact le_top

/-- **Zero gap at a hit** approached from below. -/
theorem hitGap_eq_zero {γ : HistorySpace nL nR} {g : ℝ≥0 → E} {T : ℝ≥0} (hT : 0 < T) (hTγ : (T : ℝ≥0∞) ≤ γ.1)
    (hg : ContinuousWithinAt g (Iio T) T) (hgT : g T ∈ F)
    (hψg : ∀ p : ℕ × ℕ, (dyadicTime p : ℝ≥0∞) < T → ψ γ (dyadicTime p) = g (dyadicTime p)) :
    hitGap ψ F γ T = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) (zero_le)
  have hev : ∀ᶠ s in 𝓝[<] T, edist (g s) (g T) < ε :=
    (EMetric.tendsto_nhds.1 hg) ε (by exact_mod_cast hε)
  obtain ⟨l, hl, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hT).1 hev
  obtain ⟨p, hp1, hp2⟩ := exists_dyadicTime_btwn (ENNReal.coe_lt_coe.2 (show l < T from hl))
  have hpl : l < dyadicTime p := ENNReal.coe_lt_coe.1 hp1
  have hpT : dyadicTime p < T := ENNReal.coe_lt_coe.1 hp2
  have h1 : hitGap ψ F γ T ≤ Metric.infEDist (ψ γ (dyadicTime p)) F := by
    refine (iInf_le _ p).trans ?_
    rw [ite_eq_left ⟨hp2, lt_of_lt_of_le hp2 hTγ⟩]
  rw [hψg p hp2] at h1
  have h2 : Metric.infEDist (g (dyadicTime p)) F ≤ Metric.infEDist (g T) F + edist (g (dyadicTime p)) (g T) :=
    Metric.infEDist_le_infEDist_add_edist
  rw [Metric.infEDist_zero_of_mem hgT, zero_add] at h2
  rw [zero_add]
  exact h1.trans (h2.trans (hsub ⟨hpl, hpT⟩).le)

/-- **The first-hit rule at a hit**: on a record (stopped at `T > 0`) of a path `g`, continuous on `[0, T]`, off the
closed set `F` before `T` and in `F` at `T`, the rule is `T`. -/
theorem hitRule_eq_of_hit (hF : IsClosed F) {γ : HistorySpace nL nR} {g : ℝ≥0 → E} {T : ℝ≥0} (hT : 0 < T)
    (hγT : γ.1 = T) (hg : ContinuousOn g (Iic T)) (hoff : ∀ s < T, g s ∉ F) (hgT : g T ∈ F)
    (hψg : ∀ p : ℕ × ℕ, (dyadicTime p : ℝ≥0∞) < T → ψ γ (dyadicTime p) = g (dyadicTime p)) :
    hitRule ψ F γ = T := by
  have h0 : hitGap ψ F γ T = 0 :=
    hitGap_eq_zero hT hγT.ge ((hg T self_mem_Iic).mono Iio_subset_Iic_self) hgT hψg
  have hlt : ∀ t : ℝ≥0∞, t < T → 0 < hitGap ψ F γ t := by
    intro t ht
    have htop : t ≠ ⊤ := ne_top_of_lt ht
    have ht' : t.toNNReal < T := by
      rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal htop]
      exact ht
    refine pos_hitGap hF (hg.mono (Iic_subset_Iic.2 ht'.le)) (fun s hs => hoff s (lt_of_le_of_lt hs ht'))
      (fun p hp _ => hψg p (ENNReal.coe_lt_coe.2 (lt_of_le_of_lt hp ht'))) (by rw [ENNReal.coe_toNNReal htop])
  have hs : hitStart ψ F γ = T := by
    refine le_antisymm (hitStart_le hγT.ge h0) (le_hitStart fun t _ ht0 => ?_)
    by_contra h
    exact (hlt t (not_le.1 h)).ne' ht0
  unfold hitRule
  rw [ite_eq_left ⟨by rw [hs]; exact ENNReal.coe_lt_top, by rw [hs]; exact h0⟩, hs]

/-- **The first-hit rule is at least `e`** on a record of a path that is continuous and off the closed set `F` before
`e`. -/
theorem le_hitRule_of_off (hF : IsClosed F) {γ : HistorySpace nL nR} {g : ℝ≥0 → E} {e : ℝ≥0∞}
    (hg : ContinuousOn g {s | (s : ℝ≥0∞) < e}) (hoff : ∀ s : ℝ≥0, (s : ℝ≥0∞) < e → g s ∉ F)
    (hψg : ∀ p : ℕ × ℕ, (dyadicTime p : ℝ≥0∞) < e → (dyadicTime p : ℝ≥0∞) < γ.1 →
      ψ γ (dyadicTime p) = g (dyadicTime p)) :
    e ≤ hitRule ψ F γ := by
  refine le_trans (le_hitStart fun t _ ht0 => ?_) (hitStart_le_hitRule γ)
  by_contra h
  have ht : t < e := not_le.1 h
  have htop : t ≠ ⊤ := ne_top_of_lt ht
  have hsub : ∀ s : ℝ≥0, s ≤ t.toNNReal → (s : ℝ≥0∞) < e := fun s hs =>
    lt_of_le_of_lt (by rw [← ENNReal.coe_toNNReal htop]; exact ENNReal.coe_le_coe.2 hs) ht
  have hpos := pos_hitGap (ψ := ψ) hF (γ := γ) (g := g) (T := t.toNNReal) (hg.mono fun s hs => hsub s hs)
    (fun s hs => hoff s (hsub s hs)) (fun p hp hpγ => hψg p (hsub _ hp) hpγ)
    (by rw [ENNReal.coe_toNNReal htop])
  exact hpos.ne' ht0

/-! #### Countable unions -/

open Classical in
/-- **The first-hit rule of a countable union** `⋃ m, F m`: the infimum of the rules of the pieces when it is attained
by one of them, `⊤` otherwise. -/
def hitRuleSeq (ψ : HistorySpace nL nR → ℝ≥0 → E) (F : ℕ → Set E) (γ : HistorySpace nL nR) : ℝ≥0∞ :=
  if ∃ m, hitRule ψ (F m) γ = ⨅ k, hitRule ψ (F k) γ then ⨅ k, hitRule ψ (F k) γ else ⊤

theorem isStrongGalmarino_hitRuleSeq (hψ : IsNonAnticipating ψ) (F : ℕ → Set E) :
    IsStrongGalmarino (hitRuleSeq ψ F) := by
  intro γ γ' hγ hγ' r h1 h2 hag hle
  have hS : ∀ m, IsStrongGalmarino (hitRule ψ (F m)) := fun m => isStrongGalmarino_hitRule hψ (F m)
  by_cases hA : ∃ m, hitRule ψ (F m) γ = ⨅ k, hitRule ψ (F k) γ
  · obtain ⟨m₀, hm₀⟩ := hA
    have hR : hitRuleSeq ψ F γ = ⨅ k, hitRule ψ (F k) γ := ite_eq_left ⟨m₀, hm₀⟩
    rw [hR] at hle
    have hm₀' : hitRule ψ (F m₀) γ' = ⨅ k, hitRule ψ (F k) γ :=
      (hS m₀ γ γ' hγ hγ' r h1 h2 hag (hm₀ ▸ hle)).trans hm₀
    have hge : ∀ k, (⨅ k, hitRule ψ (F k) γ) ≤ hitRule ψ (F k) γ' := fun k => by
      by_cases hk : hitRule ψ (F k) γ ≤ r
      · rw [hS k γ γ' hγ hγ' r h1 h2 hag hk]
        exact iInf_le _ k
      · exact hle.trans ((hS k).lt_of_lt hγ hγ' h1 h2 hag (not_le.1 hk)).le
    have hinf : ⨅ k, hitRule ψ (F k) γ' = ⨅ k, hitRule ψ (F k) γ :=
      le_antisymm (hm₀' ▸ iInf_le _ m₀) (le_iInf hge)
    rw [hR]
    unfold hitRuleSeq
    rw [ite_eq_left ⟨m₀, hm₀'.trans hinf.symm⟩, hinf]
  · have hR : hitRuleSeq ψ F γ = ⊤ := ite_eq_right hA
    rw [hR, top_le_iff] at hle
    subst hle
    rw [eq_of_agreeBefore_top h1 h2 hag]

theorem measurable_hitRuleSeq [MeasurableSpace E] [OpensMeasurableSpace E]
    (hψ : ∀ p : ℕ × ℕ, Measurable fun γ : HistorySpace nL nR => ψ γ (dyadicTime p)) (F : ℕ → Set E) :
    Measurable (hitRuleSeq ψ F) := by
  have hm : ∀ m, Measurable (hitRule ψ (F m)) := fun m => measurable_hitRule hψ (F m)
  have hi : Measurable fun γ => ⨅ k, hitRule ψ (F k) γ := Measurable.iInf hm
  have hset : MeasurableSet {γ : HistorySpace nL nR | ∃ m, hitRule ψ (F m) γ = ⨅ k, hitRule ψ (F k) γ} := by
    rw [ofPred_exists]
    exact MeasurableSet.iUnion fun m => measurableSet_eq_fun (hm m) hi
  exact Measurable.ite hset hi measurable_const

theorem le_hitRuleSeq_of_off {F : ℕ → Set E} (hF : ∀ m, IsClosed (F m)) {γ : HistorySpace nL nR}
    {g : ℝ≥0 → E} {e : ℝ≥0∞} (hg : ContinuousOn g {s | (s : ℝ≥0∞) < e})
    (hoff : ∀ m, ∀ s : ℝ≥0, (s : ℝ≥0∞) < e → g s ∉ F m)
    (hψg : ∀ p : ℕ × ℕ, (dyadicTime p : ℝ≥0∞) < e → (dyadicTime p : ℝ≥0∞) < γ.1 →
      ψ γ (dyadicTime p) = g (dyadicTime p)) :
    e ≤ hitRuleSeq ψ F γ := by
  have h : e ≤ ⨅ k, hitRule ψ (F k) γ := le_iInf fun k => le_hitRule_of_off (hF k) hg (hoff k) hψg
  unfold hitRuleSeq
  split_ifs
  · exact h
  · exact le_top

theorem hitRuleSeq_eq_of_hit {F : ℕ → Set E} (hF : ∀ m, IsClosed (F m)) {γ : HistorySpace nL nR}
    {g : ℝ≥0 → E} {T : ℝ≥0} (hT : 0 < T) (hγT : γ.1 = T) (hg : ContinuousOn g (Iic T))
    (hoff : ∀ m, ∀ s < T, g s ∉ F m) {m₀ : ℕ} (hgT : g T ∈ F m₀)
    (hψg : ∀ p : ℕ × ℕ, (dyadicTime p : ℝ≥0∞) < T → ψ γ (dyadicTime p) = g (dyadicTime p)) :
    hitRuleSeq ψ F γ = T := by
  have hm₀ : hitRule ψ (F m₀) γ = T := hitRule_eq_of_hit (hF m₀) hT hγT hg (hoff m₀) hgT hψg
  have hge : ∀ k, (T : ℝ≥0∞) ≤ hitRule ψ (F k) γ := fun k =>
    le_hitRule_of_off (hF k) (hg.mono fun s hs => (show s ≤ T from ENNReal.coe_le_coe.1 (le_of_lt hs)))
      (fun s hs => hoff k s (ENNReal.coe_lt_coe.1 hs)) (fun p hp _ => hψg p hp)
  have hinf : ⨅ k, hitRule ψ (F k) γ = T := le_antisymm (hm₀ ▸ iInf_le _ m₀) (le_iInf hge)
  unfold hitRuleSeq
  rw [ite_eq_left ⟨m₀, hm₀.trans hinf.symm⟩, hinf]

end Hit

/-! ### Readers: the state and the trace point read from a history -/

section Readers

/-- **The state read from a history** at time `t`: the limit of the samples at the dyadic times below `t`. -/
def histState (γ : HistorySpace nL nR) (t : ℝ≥0) : DrivingValue nL nR :=
  limUnder atTop fun n => γ.2 (lowerDyadic t n)

theorem measurable_histState (t : ℝ≥0) : Measurable fun γ : HistorySpace nL nR => histState γ t :=
  (StronglyMeasurable.limUnder fun n =>
    ((measurable_pi_apply (lowerDyadic t n)).comp measurable_snd).stronglyMeasurable).measurable

theorem histState_congr {γ γ' : HistorySpace nL nR} {t : ℝ≥0}
    (h : ∀ p' : ℕ × ℕ, dyadicTime p' ≤ t → γ.2 p' = γ'.2 p') : histState γ t = histState γ' t := by
  unfold histState
  congr 1
  funext n
  exact h _ (dyadicTime_lowerDyadic_le t n)

theorem isNonAnticipating_histState : IsNonAnticipating (histState (nL := nL) (nR := nR)) :=
  fun _ _ _ h => histState_congr h

/-- On the killed history of a state continuous before the stop, the reader gives the state before the stop. -/
theorem histState_killedHistory {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {e : Ω → ℝ≥0∞} {ω : Ω}
    (hc : ContinuousOn (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)) {t | (t : ℝ≥0∞) < e ω})
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < e ω) :
    histState (killedHistory W VL VR e ω) t = (W t ω, fun i => VL i t ω, fun j => VR j t ω) := by
  refine Tendsto.limUnder_eq ((tendsto_lowerDyadic_of_continuousOn hc ht).congr fun n => ?_)
  have hn : (dyadicTime (lowerDyadic t n) : ℝ≥0∞) < e ω :=
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (dyadicTime_lowerDyadic_le t n)) ht
  simp only [killedHistory, hn, ↓reduceIte]

/-- **The trace point read from a history**: `y + LP.traceAt t (driver read from the history)`. -/
def histTrace (y : ℝ) (γ : HistorySpace nL nR) (t : ℝ≥0) : ℂ :=
  (y : ℂ) + LP.traceAt t fun s => (histState γ s).1

theorem measurable_histTrace (y : ℝ) (t : ℝ≥0) : Measurable fun γ : HistorySpace nL nR => histTrace y γ t :=
  measurable_const.add ((LP.measurable_traceAt t).comp
    (measurable_pi_iff.2 fun s => measurable_fst.comp (measurable_histState s)))

theorem isNonAnticipating_histTrace (y : ℝ) : IsNonAnticipating (histTrace (nL := nL) (nR := nR) y) := by
  intro γ γ' p h
  unfold histTrace
  rw [LP.traceAt_congr fun r hr => congrArg Prod.fst (histState_congr fun p' hp' => h p' (hp'.trans hr))]

/-- On the killed history of an evolution whose driver generates `η − y` through the stop, the trace reader gives
`η` before the stop. -/
theorem histTrace_killedHistory {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {e : Ω → ℝ≥0∞} {ω : Ω} {y : ℝ} {η : ℝ≥0 → ℂ}
    (hc : ContinuousOn (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)) {t | (t : ℝ≥0∞) < e ω})
    (hw0 : W 0 ω = 0) (hη : IsGeneratingTrace (fun t => W t ω) (e ω) (fun t => η t - y))
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < e ω) : histTrace y (killedHistory W VL VR e ω) t = η t := by
  have hwc : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < e ω} := continuous_fst.comp_continuousOn hc
  unfold histTrace
  rw [LP.traceAt_congr (w' := fun s => W s ω) fun r hr => by
      rw [histState_killedHistory hc (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) ht)],
    LP.traceAt_eq_of_isGeneratingTrace hη hwc hw0 ht]
  ring

end Readers

/-! ### The threshold set as a countable union of closed sets -/

section Threshold

/-- States whose colliding marks are exactly `CL` on the left and `CR` on the right, with the other marks at distance
at least `1/(m+1)` from the driver. -/
def collSet (m : ℕ) (CL : Finset (Fin nL)) (CR : Finset (Fin nR)) : Set (DrivingValue nL nR) :=
  ((⋂ (i : Fin nL) (_ : i ∈ CL), {s | s.2.1 i = s.1}) ∩
      ⋂ (i : Fin nL) (_ : i ∉ CL), {s | (1 : ℝ) / (m + 1) ≤ |s.2.1 i - s.1|}) ∩
    ((⋂ (j : Fin nR) (_ : j ∈ CR), {s | s.2.2 j = s.1}) ∩
      ⋂ (j : Fin nR) (_ : j ∉ CR), {s | (1 : ℝ) / (m + 1) ≤ |s.2.2 j - s.1|})

theorem isClosed_collSet (m : ℕ) (CL : Finset (Fin nL)) (CR : Finset (Fin nR)) : IsClosed (collSet m CL CR) := by
  have hL : ∀ i : Fin nL, Continuous fun s : DrivingValue nL nR => s.2.1 i :=
    fun i => (continuous_apply i).comp (continuous_fst.comp continuous_snd)
  have hR : ∀ j : Fin nR, Continuous fun s : DrivingValue nL nR => s.2.2 j :=
    fun j => (continuous_apply j).comp (continuous_snd.comp continuous_snd)
  refine ((isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_eq (hL i) continuous_fst).inter
    (isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_le continuous_const ((hL i).sub continuous_fst).abs)).inter
    ((isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (hR j) continuous_fst).inter
    (isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le continuous_const ((hR j).sub continuous_fst).abs))

/-- **The threshold states at separation `1/(m+1)`**: the states in some `collSet m CL CR` whose colliding weights
reach the continuation threshold on one side. -/
def thrSet (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (m : ℕ) : Set (DrivingValue nL nR) :=
  ⋃ C : {C : Finset (Fin nL) × Finset (Fin nR) // (∑ i ∈ C.1, ρL i) ≤ -2 ∨ (∑ j ∈ C.2, ρR j) ≤ -2},
    collSet m C.1.1 C.1.2

theorem isClosed_thrSet (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (m : ℕ) : IsClosed (thrSet ρL ρR m) :=
  isClosed_iUnion_of_finite fun C => isClosed_collSet m C.1.1 C.1.2

theorem filter_eq_of_mem_collSet {m : ℕ} {CL : Finset (Fin nL)} {CR : Finset (Fin nR)} {s : DrivingValue nL nR}
    (hs : s ∈ collSet m CL CR) :
    Finset.univ.filter (fun i => s.2.1 i = s.1) = CL ∧ Finset.univ.filter (fun j => s.2.2 j = s.1) = CR := by
  obtain ⟨⟨hL1, hL2⟩, hR1, hR2⟩ := hs
  simp only [mem_iInter, mem_ofPred_eq] at hL1 hL2 hR1 hR2
  have hm : (0 : ℝ) < 1 / (m + 1) := by positivity
  constructor
  · ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun h => ?_, fun h => hL1 i h⟩
    by_contra hi
    have := hL2 i hi
    rw [h, sub_self, abs_zero] at this
    linarith
  · ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun h => ?_, fun h => hR1 j h⟩
    by_contra hj
    have := hR2 j hj
    rw [h, sub_self, abs_zero] at this
    linarith

/-- The states of `thrSet` are threshold states. -/
theorem thresholdCondition_of_mem_thrSet {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {m : ℕ} {s : DrivingValue nL nR}
    (hs : s ∈ thrSet ρL ρR m) : ForceWord.ThresholdCondition ρL ρR s.1 s.2.1 s.2.2 := by
  obtain ⟨C, hC⟩ := mem_iUnion.1 hs
  obtain ⟨hL, hR⟩ := filter_eq_of_mem_collSet hC
  unfold ForceWord.ThresholdCondition
  rw [hL, hR]
  exact C.2

/-- Every threshold state lies in some `thrSet`. -/
theorem exists_mem_thrSet {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {s : DrivingValue nL nR}
    (hs : ForceWord.ThresholdCondition ρL ρR s.1 s.2.1 s.2.2) : ∃ m, s ∈ thrSet ρL ρR m := by
  have hL : ∀ i : Fin nL, ∃ k : ℕ, s.2.1 i ≠ s.1 → (1 : ℝ) / (k + 1) ≤ |s.2.1 i - s.1| := fun i => by
    by_cases h : s.2.1 i = s.1
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨k, hk⟩ := exists_nat_one_div_lt (abs_pos.2 (sub_ne_zero.2 h))
      exact ⟨k, fun _ => hk.le⟩
  have hR : ∀ j : Fin nR, ∃ k : ℕ, s.2.2 j ≠ s.1 → (1 : ℝ) / (k + 1) ≤ |s.2.2 j - s.1| := fun j => by
    by_cases h : s.2.2 j = s.1
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨k, hk⟩ := exists_nat_one_div_lt (abs_pos.2 (sub_ne_zero.2 h))
      exact ⟨k, fun _ => hk.le⟩
  choose kL hkL using hL
  choose kR hkR using hR
  set m : ℕ := Finset.univ.sup kL ⊔ Finset.univ.sup kR with hm
  have hmono : ∀ k : ℕ, k ≤ m → (1 : ℝ) / (m + 1) ≤ 1 / (k + 1) := fun k hk => by
    have : (k : ℝ) ≤ m := by exact_mod_cast hk
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  refine ⟨m, mem_iUnion.2 ⟨⟨(Finset.univ.filter fun i => s.2.1 i = s.1,
    Finset.univ.filter fun j => s.2.2 j = s.1), hs⟩, ?_⟩⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [mem_iInter, mem_ofPred_eq, Finset.mem_filter, Finset.mem_univ, true_and]
  · exact fun i h => h
  · exact fun i h => (hmono _ ((Finset.le_sup (Finset.mem_univ i)).trans le_sup_left)).trans (hkL i h)
  · exact fun j h => h
  · exact fun j h => (hmono _ ((Finset.le_sup (Finset.mem_univ j)).trans le_sup_right)).trans (hkR j h)

end Threshold

end FlowStopIdentG

end Restart

end InteractingSLE
