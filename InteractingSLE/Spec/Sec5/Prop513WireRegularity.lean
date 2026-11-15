/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513TargetInputs

/-! # Interior Q prefixes from the finite-schedule construction

The previously proved good-piece event gives a simple interior continuation.
Its restriction through the terminal time is the actual frozen prefix. This
supplies the chart-domain facts independently of the reverse-visit law.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open scoped Real NNReal ENNReal
universe u

namespace InteractingSLE.Sec5.Prop513Wire
open QuantumZipper Sec4 Prop513Schedule Prop513TreeExtract Prop513Target
open LQGMetric Restart Exist Exist.Staged Exist.StagedLaw
open Sec7 Sec7.StripWall Theorem14.StagedReg StripSideHeightProb

/-- Good actual pieces give an interior generating trace of their frozen
finite prefix, including its terminal point. -/
theorem prefix_trace_of_good {Ω : Type*} (E : Schedule → ℕ → Ω → Driver)
    (s : Schedule) (ω : Ω) (hr : ∀ j, IsRegularDriver (E s j ω))
    (hg : ∀ j < (scheduleSpec s).2.2.length, E s j ω ∈ goodPathSet) :
    Continuous (prefixDriver E s ω) ∧ prefixDriver E s ω 0 = 0 ∧
      ∃ η, IsGeneratingTrace (prefixDriver E s ω) (terminal s) η ∧
        Function.Injective η ∧ ∀ t : ℝ≥0, 0 < t → η t ∈ H := by
  have he : ∀ j, 0 ≤ j → j < 0 + (scheduleList s).length →
      Continuous (E s j ω).1 ∧ (E s j ω).1 0 = 0 ∧
        ∃ η, IsGeneratingTrace (E s j ω).1 ⊤ η ∧ Function.Injective η ∧
          ∀ t, 0 < t → η t ∈ H := by
    intro j _ hj
    have hj' : j < (scheduleSpec s).2.2.length := by
      simpa only [scheduleSpec, length_scheduleProgram, zero_add] using hj
    have htop := (mem_goodPathSet.1 (hg j hj')).1
    have hcont := continuous_of_isRegularDriver (hr j) htop
    have hgood : WangWu.ImgDrv.GoodPath (E s j ω).1 ⊤ := by
      simpa only [htop] using (mem_goodPathSet.1 (hg j hj'))
    obtain ⟨η, hη, hinj, hH, _⟩ := exists_simple_trace_of_goodPath hcont (hr j).2.1 hgood
    exact ⟨hcont, (hr j).2.1, η, hη, hinj, hH⟩
  have hw := joinedDriver_continuous (E s) ω 0 0 (scheduleList s)
    (fun j hj hj' => ⟨(he j hj hj').1, (he j hj hj').2.1⟩)
  have hne : scheduleList s ≠ [] := fun h => s.2.1 (List.map_eq_nil_iff.1 h)
  obtain ⟨_, _, η, hη, hinj, hH⟩ := continuedDriver_trace (E s) ω 0 0 (scheduleList s) hne he
  refine ⟨hw.1, hw.2, η, ?_, hinj, hH⟩
  apply Sec7.IsGeneratingTrace.congr_lt (hη.mono_horizon le_top)
  intro t ht
  apply joinedDriver_eq_continued (E s) ω 0 0 (scheduleList s) (timeOrdered_scheduleList s)
  simpa only [← terminal_eq_lastTime, tsub_zero] using (ENNReal.coe_lt_coe.1 ht).le

/-- The canonical reconstruction starts at zero and stays in H through the
closed terminal time. -/
theorem prefix_interior_of_good {Ω : Type*} (E : Schedule → ℕ → Ω → Driver)
    (s : Schedule) (ω : Ω) (hr : ∀ j, IsRegularDriver (E s j ω))
    (hg : ∀ j < (scheduleSpec s).2.2.length, E s j ω ∈ goodPathSet) :
    prefixTrace (prefixDriver E) s ω 0 = 0 ∧
      ∀ t : ℝ, 0 < t → t ≤ (terminal s : ℝ) → prefixTrace (prefixDriver E) s ω t ∈ H := by
  obtain ⟨hw, hw0, η, hη, _, hH⟩ := prefix_trace_of_good E s ω hr hg
  have he : ∀ t ∈ Icc 0 (terminal s : ℝ), prefixTrace (prefixDriver E) s ω t = η t.toNNReal :=
    fun _ ht => prefixTrace_eq hw.continuousOn hw0 (fun _ _ => rfl) hη ht
  constructor
  · rw [he 0 ⟨le_rfl, (terminal s).coe_nonneg⟩]
    simpa only [Real.toNNReal_zero] using hη.1
  · intro t ht hT
    rw [he t ⟨ht.le, hT⟩]
    exact hH _ (Real.toNNReal_pos.2 ht)

/-- One conull event for the interiority and starting value of all original
R51 prefixes. No reverse-visit or no-return input is used. -/
theorem ae_driverTree_interior (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (c : BoundaryWord) (hc : ExtremeHeights κ c) (hh : IsGFFWithBoundaryData P h c.fn c.jumps)
    {E : Schedule → ℕ → Ω → Driver}
    (hE : ∀ s, IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ c.fn c.jumps P (scheduleSpec s) (E s)) :
    ∀ᵐ ω ∂P, ∀ n, driverTree E n ω 0 = 0 ∧
      ∀ t : ℝ, 0 < t → t ≤ treeTime n → driverTree E n ω t ∈ H := by
  let F : Schedule → ℕ → Ω → Driver := fun s => regHist (scheduleSpec s) (E s)
  have hg := fun s => ae_schedule_goodPath h44 hκ hκ4 c hc hh s
    (isStagedHistory_regHist c.isPiecewiseConstantBoundaryData (hE s) (hR s))
    (fun _ _ => isRegularDriver_regHist _ _)
  filter_upwards [ae_all_iff.2 hg, ae_prefixDriver_regHist h44 hκ hκ4 c hc hh hE hR]
    with ω hgω he n
  have hp := prefix_interior_of_good F (scheduleAt n) ω
    (fun _ => isRegularDriver_regHist _ _) (hgω (scheduleAt n))
  simpa only [F, driverTree, prefixTrace, treeTime, he] using hp

end InteractingSLE.Sec5.Prop513Wire
