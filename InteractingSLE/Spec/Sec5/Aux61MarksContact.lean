/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61MarksRead
import InteractingSLE.Spec.Sec5.Aux61SlitWFirstHit
import InteractingSLE.Spec.Sec5.Aux61FibDataExit

/-!
# The absolute contact time as a measurable Galmarino rule of the records

Packet PROVE-AUX61-MARKS. The restart contact is the first time after the restart time `t₀` at which the restarted
path hits a closed obstacle `C` read from the records at time `t₀` (the counterflow record and the own record stopped at
`t₀`). Its absolute value `t₀ + T` is the first-hit rule of an explicit non-anticipating observable of the records:

* `contactObs C t₀ y γ t`: `1` up to `t₀`, then the distance of the record's trace to the obstacle normalized by its
  value at `t₀` (non-anticipating: `isNonAnticipating_contactObs`; continuous along a continuous trace starting off
  the obstacle: `continuous_contactObs`);
* `contactRule C t₀ := hitRule (contactObs C t₀ ·) {0} ∘ fullRecord`: **a Galmarino rule of the records**
  (`isGalmarinoRule_contactRule`, SLITW's uncapped first-hit rule) and **measurable** (`measurable_contactRule`);
* on a record whose trace is continuous, off the obstacle on `[t₀, t₀ + T)` and on it at `t₀ + T`, the rule is
  `t₀ + T` (`contactRule_eq_of_hit`); for the restarted path `ρ` equal to the record's trace after `t₀` and the contact
  its first hitting time of the obstacle, the rule is `t₀ + hitTime` (`contactRule_eq_add_hitTime`), almost surely on
  the restart event (`ae_contactRule_eq`).

These are exactly the clause `Ta (Y₀ x, R₀ x) = t₀ + T x` and the hypotheses `hTam`, `hTaG` of the `code_le` theorem
`codeFiltration_le_nullRuleMarks_of_record` (`Aux61MarksAlive`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Marks

open Aux61ULoc LawUnique Restart.FlowStopIdentG Aux61FibData
open Aux61SlitW (fullRecord)

/-! ### Records stopped at the restart time -/

section Congr

variable {nL nR : ℕ}

/-- The record stopped at `t₀` only reads the samples at dyadic times `≤ t₀`. -/
theorem stopRec_congr {t₀ : ℝ≥0} {γ γ' : HistorySpace nL nR}
    (h : ∀ p : ℕ × ℕ, dyadicTime p ≤ t₀ → γ.2 p = γ'.2 p) : stopRec t₀ γ = stopRec t₀ γ' := by
  refine Prod.ext rfl (funext fun p => ?_)
  show (if dyadicTime p ≤ t₀ then γ.2 p else 0) = (if dyadicTime p ≤ t₀ then γ'.2 p else 0)
  by_cases hp : dyadicTime p ≤ t₀
  · simp only [hp, ↓reduceIte, h p hp]
  · simp only [hp, ↓reduceIte]

/-- The trace read at a time `t ≤ d` only uses the samples at dyadic times `≤ d`. -/
theorem histTrace_congr_of_le {t d : ℝ≥0} (htd : t ≤ d) {γ γ' : HistorySpace nL nR}
    (h : ∀ p' : ℕ × ℕ, dyadicTime p' ≤ d → γ.2 p' = γ'.2 p') (y : ℝ) : histTrace y γ t = histTrace y γ' t := by
  unfold histTrace
  rw [LP.traceAt_congr fun r hr =>
    congrArg Prod.fst (histState_congr fun p' hp' => h p' (hp'.trans (hr.trans htd)))]

end Congr

/-! ### The contact observable and the contact rule -/

section Rule

variable {𝒴 : Type*} {nL nR : ℕ}

/-- **The contact observable**: `1` up to the restart time `t₀`, then the distance of the record's trace to the
obstacle `C` read at `t₀`, normalized by its value at `t₀`. -/
def contactObs (C : 𝒴 × HistorySpace nL nR → Set ℂ) (t₀ : ℝ≥0) (y : 𝒴) (γ : HistorySpace nL nR) (t : ℝ≥0) : ℝ :=
  if t ≤ t₀ then 1 else
    infDist (histTrace 0 γ t) (C (y, stopRec t₀ γ)) / infDist (histTrace 0 γ t₀) (C (y, stopRec t₀ γ))

/-- **The contact rule**: the uncapped first-hit rule of the contact observable at `0`. -/
def contactRule (C : 𝒴 × HistorySpace nL nR → Set ℂ) (t₀ : ℝ≥0) (p : 𝒴 × HistorySpace nL nR) : ℝ≥0∞ :=
  hitRule (contactObs C t₀ p.1) {0} (fullRecord p.2)

/-- The contact observable is non-anticipating. -/
theorem isNonAnticipating_contactObs (C : 𝒴 × HistorySpace nL nR → Set ℂ) (t₀ : ℝ≥0) (y : 𝒴) :
    IsNonAnticipating (contactObs C t₀ y) := by
  intro γ γ' p h
  unfold contactObs
  by_cases hp : dyadicTime p ≤ t₀
  · simp only [hp, ↓reduceIte]
  · have hlt : t₀ ≤ dyadicTime p := (not_le.1 hp).le
    have hst : stopRec t₀ γ = stopRec t₀ γ' := stopRec_congr fun p' hp' => h p' (hp'.trans hlt)
    simp only [hp, ↓reduceIte, hst, histTrace_congr_of_le le_rfl h 0, histTrace_congr_of_le hlt h 0]

/-- **The contact rule is a Galmarino rule of the records.** -/
theorem isGalmarinoRule_contactRule [MeasurableSpace 𝒴] (C : 𝒴 × HistorySpace nL nR → Set ℂ) (t₀ : ℝ≥0) :
    IsGalmarinoRule stopRec (contactRule C t₀) :=
  Aux61SlitW.isGalmarinoRule_firstHit (contactObs C t₀) (fun y => isNonAnticipating_contactObs C t₀ y) {0}

/-- **The contact rule is measurable**, for an obstacle whose distances are measurable in the records. -/
theorem measurable_contactRule [MeasurableSpace 𝒴] {C : 𝒴 × HistorySpace nL nR → Set ℂ}
    (hCm : ∀ z : ℂ, Measurable fun p : 𝒴 × HistorySpace nL nR => infDist z (C p)) (t₀ : ℝ≥0) :
    Measurable (contactRule C t₀) := by
  have hd : Measurable fun q : ℂ × (𝒴 × HistorySpace nL nR) => infDist q.1 (C q.2) :=
    measurable_uncurry_of_continuous_of_measurable (u := fun z p => infDist z (C p))
      (fun _ => continuous_infDist_pt _) hCm
  have hg : Measurable fun p : 𝒴 × HistorySpace nL nR => fullRecord p.2 :=
    Aux61SlitW.measurable_fullRecord.comp measurable_snd
  have hs : Measurable fun p : 𝒴 × HistorySpace nL nR => (p.1, stopRec t₀ (fullRecord p.2)) :=
    measurable_fst.prodMk (isRecordStop_stopRec.measurable.comp (measurable_const.prodMk hg))
  show Measurable fun p : 𝒴 × HistorySpace nL nR => hitRule (contactObs C t₀ p.1) {0} (fullRecord p.2)
  refine Aux61SlitW.measurable_param_hitRule hg (fun p => ?_) {0}
  by_cases hp : dyadicTime p ≤ t₀
  · simp only [contactObs, hp, ↓reduceIte]
    exact measurable_const
  · simp only [contactObs, hp, ↓reduceIte]
    have ha := (measurable_histTrace 0 (dyadicTime p)).comp hg
    have hb := (measurable_histTrace 0 t₀).comp hg
    have h1 := hd.comp (ha.prodMk hs)
    have h2 := hd.comp (hb.prodMk hs)
    exact h1.div h2

end Rule

/-! ### The value of the contact rule -/

section Value

variable {𝒴 : Type*} {nL nR : ℕ}

/-- Along a continuous trace starting off the obstacle the contact observable is continuous. -/
theorem continuous_contactObs {C : 𝒴 × HistorySpace nL nR → Set ℂ} {t₀ : ℝ≥0} {y : 𝒴} {γ : HistorySpace nL nR}
    (hc : Continuous (histTrace 0 γ)) (hd₀ : infDist (histTrace 0 γ t₀) (C (y, stopRec t₀ γ)) ≠ 0) :
    Continuous (contactObs C t₀ y γ) := by
  unfold contactObs
  refine Continuous.if_le continuous_const (((continuous_infDist_pt _).comp hc).div_const _) continuous_id
    continuous_const fun t ht => ?_
  have ht' : t = t₀ := ht
  rw [ht', div_self hd₀]

/-- **The contact rule at a hit**: on a record whose trace is continuous, off the closed nonempty obstacle on
`[t₀, t₀ + T)` (`T > 0`) and on it at `t₀ + T` when `T` is finite, the rule is `t₀ + T`. -/
theorem contactRule_eq_of_hit {C : 𝒴 × HistorySpace nL nR → Set ℂ} {t₀ : ℝ≥0} {y : 𝒴} {g : HistorySpace nL nR}
    (hc : Continuous (histTrace 0 g)) (hC : IsClosed (C (y, stopRec t₀ g))) (hCne : (C (y, stopRec t₀ g)).Nonempty)
    {T : ℝ≥0∞} (hT0 : 0 < T) (hoff : ∀ u : ℝ≥0, (u : ℝ≥0∞) < T → histTrace 0 g (t₀ + u) ∉ C (y, stopRec t₀ g))
    (hhit : ∀ T' : ℝ≥0, T = T' → histTrace 0 g (t₀ + T') ∈ C (y, stopRec t₀ g)) :
    contactRule C t₀ (y, g) = t₀ + T := by
  set C₀ := C (y, stopRec t₀ g) with hC₀
  have hd₀ : 0 < infDist (histTrace 0 g t₀) C₀ := by
    have h := hoff 0 (by simpa using hT0)
    rw [add_zero] at h
    exact (hC.notMem_iff_infDist_pos hCne).1 h
  have hf := continuous_contactObs (C := C) (y := y) hc hd₀.ne'
  -- the observable vanishes exactly on hits after `t₀`
  have hne : ∀ s : ℝ≥0, (s : ℝ≥0∞) < t₀ + T → contactObs C t₀ y g s ∉ ({0} : Set ℝ) := by
    intro s hs
    rw [mem_singleton_iff]
    unfold contactObs
    by_cases hst : s ≤ t₀
    · simp only [hst, ↓reduceIte, one_ne_zero, not_false_eq_true]
    · simp only [hst, ↓reduceIte]
      have hle : t₀ ≤ s := (not_le.1 hst).le
      have hsu : s = t₀ + (s - t₀) := (add_tsub_cancel_of_le hle).symm
      have hu : ((s - t₀ : ℝ≥0) : ℝ≥0∞) < T := by
        have hs' : (t₀ : ℝ≥0∞) + ((s - t₀ : ℝ≥0) : ℝ≥0∞) < t₀ + T := by
          rw [← ENNReal.coe_add, ← hsu]
          exact hs
        exact (ENNReal.add_lt_add_iff_left ENNReal.coe_ne_top).1 hs'
      have hoffs := hoff _ hu
      rw [← hsu] at hoffs
      exact div_ne_zero ((hC.notMem_iff_infDist_pos hCne).1 hoffs).ne' hd₀.ne'
  show hitRule (contactObs C t₀ y) {0} (fullRecord g) = t₀ + T
  induction T using ENNReal.recTopCoe with
  | top =>
    rw [add_top]
    refine le_antisymm le_top (le_hitRule_of_off isClosed_singleton (g := contactObs C t₀ y g) hf.continuousOn
      (fun s _ => hne s (by rw [add_top]; exact ENNReal.coe_lt_top)) fun p _ _ => rfl)
  | coe T' =>
    have hT'0 : 0 < T' := by exact_mod_cast hT0
    have hhit' : contactObs C t₀ y g (t₀ + T') ∈ ({0} : Set ℝ) := by
      rw [mem_singleton_iff]
      unfold contactObs
      have hn : ¬ t₀ + T' ≤ t₀ := not_le.2 (lt_add_of_pos_right t₀ hT'0)
      simp only [hn, ↓reduceIte]
      rw [← hC₀, infDist_zero_of_mem (hhit T' rfl), zero_div]
    rw [← ENNReal.coe_add]
    exact Aux61SlitW.firstHit_eq_of_hit (isNonAnticipating_contactObs C t₀ y) isClosed_singleton
      (add_pos_of_nonneg_of_pos zero_le hT'0) hf.continuousOn
      (fun s hs => hne s (by rw [← ENNReal.coe_add]; exact ENNReal.coe_lt_coe.2 hs)) hhit' fun p _ => rfl

/-- Two continuous functions agreeing on `(a, b)` agree at `a` and at `b`. -/
theorem eq_endpoints_of_eqOn_Ioo {f g : ℝ≥0 → ℂ} (hf : Continuous f) (hg : Continuous g) {a b : ℝ≥0} (hab : a < b)
    (h : ∀ u, a < u → u < b → f u = g u) : f a = g a ∧ f b = g b := by
  have he : EqOn f g (Icc a b) :=
    Set.EqOn.of_subset_closure (fun u hu => h u hu.1 hu.2) hf.continuousOn hg.continuousOn Ioo_subset_Icc_self
      (by rw [closure_Ioo hab.ne])
  exact ⟨he ⟨le_rfl, hab.le⟩, he ⟨hab.le, le_rfl⟩⟩

/-- **The contact rule is `t₀` plus the first hitting time** of the obstacle by the restarted path, when the path is
continuous, starts off the closed nonempty obstacle and is the record's continuous trace after `t₀` before that time. -/
theorem contactRule_eq_add_hitTime {X : Type*} {ρ : X → ℝ≥0 → ℂ} {C : 𝒴 × HistorySpace nL nR → Set ℂ} {t₀ : ℝ≥0}
    {Y₀ : X → 𝒴} {R₀ : X → HistorySpace nL nR} {x : X} (hρc : Continuous (ρ x))
    (hc : Continuous (histTrace 0 (R₀ x))) (hC : IsClosed (C (Y₀ x, stopRec t₀ (R₀ x))))
    (hCne : (C (Y₀ x, stopRec t₀ (R₀ x))).Nonempty) (h0 : ρ x 0 ∉ C (Y₀ x, stopRec t₀ (R₀ x)))
    (hρ : ∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < hitTime ρ (fun x => C (Y₀ x, stopRec t₀ (R₀ x))) x →
      ρ x u = histTrace 0 (R₀ x) (t₀ + u)) :
    contactRule C t₀ (Y₀ x, R₀ x) = t₀ + hitTime ρ (fun x => C (Y₀ x, stopRec t₀ (R₀ x))) x := by
  set T := hitTime ρ (fun x => C (Y₀ x, stopRec t₀ (R₀ x))) x with hTdef
  have hg : Continuous fun u : ℝ≥0 => histTrace 0 (R₀ x) (t₀ + u) := hc.comp (continuous_const.add continuous_id)
  -- the hitting time is positive
  have hT0 : 0 < T := by
    by_contra hn
    obtain ⟨u, hu, hmem⟩ := (hitTime_le_iff hρc hC 0).1 (by simpa using hn)
    have hu0 : u = 0 := le_antisymm (ENNReal.coe_le_coe.1 (by simpa using hu)) zero_le
    exact h0 (hu0 ▸ hmem)
  -- agreement at `0` and at a finite hitting time
  obtain ⟨b, hb0, hbT⟩ : ∃ b : ℝ≥0, 0 < b ∧ (b : ℝ≥0∞) ≤ T := by
    obtain ⟨b, hb0, hbT⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hT0
    exact ⟨b, by exact_mod_cast hb0, hbT.le⟩
  have hagree := eq_endpoints_of_eqOn_Ioo hρc hg hb0 fun u hu hub =>
    hρ u hu (lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hub) hbT)
  refine contactRule_eq_of_hit hc hC hCne hT0 (fun u hu => ?_) fun T' hT' => ?_
  · rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with rfl | hu0
    · rw [← hagree.1]
      exact h0
    · rw [← hρ u hu0 hu]
      exact notMem_of_lt_hitTime hu
  · -- the hit point is attained at `T'`, where the path is the trace by continuity
    have hT'0 : 0 < T' := by
      have h : (0 : ℝ≥0∞) < T' := lt_of_lt_of_eq hT0 hT'
      exact_mod_cast h
    obtain ⟨u, hu, hmem⟩ := (hitTime_le_iff hρc hC T').1 (le_of_eq hT')
    have huT : u = T' := by
      refine le_antisymm (ENNReal.coe_le_coe.1 hu) (not_lt.1 fun hlt => ?_)
      exact notMem_of_lt_hitTime (lt_of_lt_of_eq (ENNReal.coe_lt_coe.2 hlt) hT'.symm) hmem
    have hend := (eq_endpoints_of_eqOn_Ioo hρc hg hT'0 fun v hv hvT =>
      hρ v hv (lt_of_lt_of_eq (ENNReal.coe_lt_coe.2 hvT) hT'.symm)).2
    rw [← hend, ← huT]
    exact hmem

/-- **Almost surely on the restart event the contact rule is the absolute contact time**, when the restarted path is
continuous on the event, the record's trace is continuous, the contact is the first hitting time of the closed nonempty
obstacle read at `t₀` by a path starting off it, and the path is the record's trace after `t₀` before the contact. -/
theorem ae_contactRule_eq {X : Type*} [MeasurableSpace X] {μ : Measure X} {E : Set X} {ρ : X → ℝ≥0 → ℂ}
    {T : X → ℝ≥0∞} {C : 𝒴 × HistorySpace nL nR → Set ℂ} {t₀ : ℝ≥0} {Y₀ : X → 𝒴} {R₀ : X → HistorySpace nL nR}
    (hC : ∀ p, IsClosed (C p)) (hCne : ∀ p, (C p).Nonempty) (hcont : ∀ x ∈ E, Continuous (ρ x))
    (htr : ∀ᵐ x ∂μ, x ∈ E → Continuous (histTrace 0 (R₀ x)))
    (hT : ∀ᵐ x ∂μ, x ∈ E → T x = hitTime ρ (fun x => C (Y₀ x, stopRec t₀ (R₀ x))) x ∧
      ρ x 0 ∉ C (Y₀ x, stopRec t₀ (R₀ x)))
    (hρ : ∀ᵐ x ∂μ, x ∈ E → ∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < T x → ρ x u = histTrace 0 (R₀ x) (t₀ + u)) :
    ∀ᵐ x ∂μ, x ∈ E → contactRule C t₀ (Y₀ x, R₀ x) = t₀ + T x := by
  filter_upwards [htr, hT, hρ] with x hx1 hx2 hx3 hxE
  obtain ⟨hTx, h0⟩ := hx2 hxE
  rw [hTx]
  exact contactRule_eq_add_hitTime (hcont x hxE) (hx1 hxE) (hC _) (hCne _) h0 fun u hu huT =>
    hx3 hxE u hu (lt_of_lt_of_eq huT hTx.symm)

end Value

end InteractingSLE.Sec5.Aux61Marks
