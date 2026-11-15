/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513SchedulePrefix
import InteractingSLE.Spec.Sec5.Prop513SchedulePieces
import InteractingSLE.Spec.Sec7.StripWallVersion

/-!
# Continuous generating prefixes from the finitely many actual pieces

The last piece may be continued for this deterministic proof. Its driver agrees
with the frozen prefix through the terminal time. Loewner concatenation joins
the actual simple interior traces, supplied by the Borel good-path transfer.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Prop513Schedule

open LQGMetric Restart Exist Exist.Staged Exist.StagedLaw
open Sec7 Sec7.AdmCode Sec7.StripWall Prop513TreeExtract StripSideHeightProb QuantumZipper

theorem joinedDriver_continuous {Ω : Type*} (E : ℕ → Ω → Driver) (ω : Ω)
    (j : ℕ) (a : ℝ≥0) (l : List (ℝ × ℝ≥0))
    (he : ∀ i, j ≤ i → i < j + l.length → Continuous (E i ω).1 ∧ (E i ω).1 0 = 0) :
    Continuous (joinedDriver E j a l ω) ∧ joinedDriver E j a l ω 0 = 0 := by
  induction l generalizing j a with
  | nil => exact ⟨continuous_const, rfl⟩
  | cons p l ih =>
    have h0 := he j le_rfl (by simp only [List.length_cons]; omega)
    have h1 := ih (j + 1) p.2 (fun i hji hi => he i (by omega)
      (by simp only [List.length_cons]; omega))
    exact ⟨continuous_catPath h0.1 h1.1 h1.2, catPath_zero h0.2⟩

def continuedDriver {Ω : Type*} (E : ℕ → Ω → Driver) :
    ℕ → ℝ≥0 → List (ℝ × ℝ≥0) → Ω → ℝ≥0 → ℝ
  | _, _, [], _, _ => 0
  | j, _, [_], ω, t => (E j ω).1 t
  | j, a, p :: q :: l, ω, t =>
      catPath (E j ω).1 (p.2 - a) (continuedDriver E (j + 1) p.2 (q :: l) ω) t

theorem joinedDriver_eq_continued {Ω : Type*} (E : ℕ → Ω → Driver) (ω : Ω)
    (j : ℕ) (a : ℝ≥0) (l : List (ℝ × ℝ≥0)) (hl : TimeOrdered a l)
    {t : ℝ≥0} (ht : t ≤ lastTime a l - a) :
    joinedDriver E j a l ω t = continuedDriver E j a l ω t := by
  induction l generalizing j a t with
  | nil => rfl
  | cons p l ih =>
    cases l with
    | nil => exact catPath_of_le ht
    | cons q l =>
      change catPath (E j ω).1 (p.2 - a) (joinedDriver E (j + 1) p.2 (q :: l) ω) t =
        catPath (E j ω).1 (p.2 - a) (continuedDriver E (j + 1) p.2 (q :: l) ω) t
      by_cases htp : t ≤ p.2 - a
      · simp only [catPath, htp, ↓reduceIte]
      · simp only [catPath, htp, ↓reduceIte]
        congr 1
        apply ih (j + 1) p.2 (timeOrdered_tail hl)
        have hpa := hl.2 p List.mem_cons_self
        have hlast := le_lastTime (timeOrdered_tail hl)
        have htt : p.2 - a ≤ t := (lt_of_not_ge htp).le
        have ht' : (t : ℝ) ≤ (lastTime p.2 (q :: l) : ℝ) - a := by
          have ht'' := NNReal.coe_le_coe.2 ht
          change (t : ℝ) ≤ ((lastTime p.2 (q :: l) - a : ℝ≥0) : ℝ) at ht''
          rwa [NNReal.coe_sub (hpa.trans hlast)] at ht''
        rw [← NNReal.coe_le_coe, NNReal.coe_sub htt, NNReal.coe_sub hpa, NNReal.coe_sub hlast]
        linarith only [ht']

theorem continuedDriver_trace {Ω : Type*} (E : ℕ → Ω → Driver) (ω : Ω)
    (j : ℕ) (a : ℝ≥0) (l : List (ℝ × ℝ≥0)) (hl : l ≠ [])
    (he : ∀ i, j ≤ i → i < j + l.length →
      Continuous (E i ω).1 ∧ (E i ω).1 0 = 0 ∧
        ∃ η, IsGeneratingTrace (E i ω).1 ⊤ η ∧ Function.Injective η ∧
          ∀ t, 0 < t → η t ∈ H) :
    Continuous (continuedDriver E j a l ω) ∧ continuedDriver E j a l ω 0 = 0 ∧
      ∃ η, IsGeneratingTrace (continuedDriver E j a l ω) ⊤ η ∧ Function.Injective η ∧
        ∀ t, 0 < t → η t ∈ H := by
  induction l generalizing j a with
  | nil => exact False.elim (hl rfl)
  | cons p l ih =>
    have h0 := he j le_rfl (by simp only [List.length_cons]; omega)
    cases l with
    | nil => exact h0
    | cons q l =>
      have h1 := ih (j + 1) p.2 (List.cons_ne_nil _ _)
        (fun i hji hi => he i (by omega) (by simp only [List.length_cons] at hi ⊢; omega))
      obtain ⟨hc0, hz0, η0, hη0, hi0, hH0⟩ := h0
      obtain ⟨hc1, hz1, η1, hη1, hi1, hH1⟩ := h1
      have hs := joinedTrace_simple hc0 hz0 hη0 hi0 hH0 hi1 hH1 (a := p.2 - a)
      exact ⟨continuous_catPath hc0 hc1 hz1, catPath_zero hz0,
        LoewnerConcat.joinedTrace (E j ω).1 η0 (p.2 - a) η1,
        LoewnerConcat.isGeneratingTrace_catPath hc0 hz0 hc1 hz1
          (hη0.mono_horizon le_top) hη1 hH1, hs⟩

theorem timeOrdered_scheduleList (s : Schedule) : TimeOrdered 0 (scheduleList s) :=
  ⟨(isSchedule_scheduleList s).2.imp fun h => h.le, fun _ _ => zero_le⟩

/-- Lemma 5.6 regularity of every finite extreme-angle prefix. -/
theorem prefixTraceRegularity (h44 : Theorem12ParamCond44Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (c : BoundaryWord) (hc : ExtremeHeights κ c)
    (hh : IsGFFWithBoundaryData P h c.fn c.jumps)
    {E : Schedule → ℕ → Ω → Driver}
    (hE : ∀ s, IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) (E s))
    (hr : ∀ s j ω, IsRegularDriver (E s j ω)) :
    PrefixTraceRegularity P (fun _ => univ) E := by
  intro s
  filter_upwards [ae_schedule_goodPath h44 hκ hκ4 c hc hh s (hE s) (hr s)] with ω hg _
  have he : ∀ j, 0 ≤ j → j < 0 + (scheduleList s).length →
      Continuous (E s j ω).1 ∧ (E s j ω).1 0 = 0 ∧
        ∃ η, IsGeneratingTrace (E s j ω).1 ⊤ η ∧ Function.Injective η ∧
          ∀ t, 0 < t → η t ∈ H := by
    intro j _ hj
    have hj' : j < (scheduleSpec s).2.2.length := by
      simpa only [scheduleSpec, length_scheduleProgram, zero_add] using hj
    have hgood := hg j hj'
    have htop := (mem_goodPathSet.1 hgood).1
    have hcont := continuous_of_isRegularDriver (hr s j ω) htop
    refine ⟨hcont, (hr s j ω).2.1, ?_⟩
    have hgood' : WangWu.ImgDrv.GoodPath (E s j ω).1 ⊤ := by
      simpa only [htop] using (mem_goodPathSet.1 hgood)
    obtain ⟨η, hη, hinj, hH, _⟩ := exists_simple_trace_of_goodPath hcont (hr s j ω).2.1 hgood'
    exact ⟨η, hη, hinj, hH⟩
  have hcont := joinedDriver_continuous (E s) ω 0 0 (scheduleList s)
    (fun j hj hj' => ⟨(he j hj hj').1, (he j hj hj').2.1⟩)
  have hne : scheduleList s ≠ [] := fun h => s.2.1 (List.map_eq_nil_iff.1 h)
  obtain ⟨_, _, η, hη, _, _⟩ := continuedDriver_trace (E s) ω 0 0 (scheduleList s) hne he
  refine ⟨hcont.1.continuousOn, hcont.2, η, ?_⟩
  apply Sec7.IsGeneratingTrace.congr_lt (hη.mono_horizon le_top)
  intro t ht
  apply joinedDriver_eq_continued (E s) ω 0 0 (scheduleList s) (timeOrdered_scheduleList s)
  simpa only [← terminal_eq_lastTime, tsub_zero] using (ENNReal.coe_lt_coe.1 ht).le

end InteractingSLE.Sec5.Prop513Schedule
