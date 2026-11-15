/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513ScheduleExtract
import InteractingSLE.Spec.Supplement.StagedRegularize

/-!
# Using exactly the source's almost surely regular staged pieces

R51 supplies `StagedPiecesRegular`, rather than regular drivers at every sample.
The existing regularization preserves the runs and every stopped ordinary
piece. A finite concatenation sees only those stopped pieces, so its complete
frozen prefix driver is unchanged almost surely.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Prop513Schedule

open LQGMetric Restart Exist Exist.Staged Exist.StagedLaw
open Sec7 Sec7.AdmCode Prop513TreeExtract StripSideHeightProb
open Theorem14.StagedReg

theorem joinedDriver_congr_program {Ω : Type*} {E F : ℕ → Ω → Driver} (ω : Ω)
    (j : ℕ) (a : ℝ≥0) (l : List (ℝ × ℝ≥0))
    (he : ∀ k θ T, (scheduleProgram a l)[k]? = some (Sum.inl (θ, T)) →
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T → (E (j + k) ω).1 t = (F (j + k) ω).1 t) :
    joinedDriver E j a l ω = joinedDriver F j a l ω := by
  induction l generalizing j a with
  | nil => rfl
  | cons p l ih =>
    have h0 := he 0 p.1 ((p.2 - a : ℝ≥0) : ℝ≥0∞) rfl
    have htail := ih (j + 1) p.2 (fun k θ T hk t ht => by
      have hh := he (k + 1) θ T hk t ht
      simpa only [Nat.add_succ, Nat.succ_add] using hh)
    funext t
    change catPath (E j ω).1 (p.2 - a) (joinedDriver E (j + 1) p.2 l ω) t =
      catPath (F j ω).1 (p.2 - a) (joinedDriver F (j + 1) p.2 l ω) t
    rw [htail]
    by_cases ht : t ≤ p.2 - a
    · simpa only [catPath, ht, ↓reduceIte, Nat.add_zero] using
        h0 t (ENNReal.coe_le_coe.2 ht)
    · simp only [catPath, ht, ↓reduceIte]
      rw [show (E j ω).1 (p.2 - a) = (F j ω).1 (p.2 - a) from h0 _ le_rfl]

theorem ae_prefixDriver_regHist (h44 : Theorem12ParamCond44Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (c : BoundaryWord) (hc : ExtremeHeights κ c)
    (hh : IsGFFWithBoundaryData P h c.fn c.jumps)
    {E : Schedule → ℕ → Ω → Driver}
    (hE : ∀ s, IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ c.fn c.jumps P (scheduleSpec s) (E s)) :
    ∀ᵐ ω ∂P, ∀ s, prefixDriver (fun s => regHist (scheduleSpec s) (E s)) s ω =
      prefixDriver E s ω := by
  apply ae_all_iff.2
  intro s
  have hF := isStagedHistory_regHist c.isPiecewiseConstantBoundaryData (hE s) (hR s)
  have hD := ae_schedule_drivers h44 hκ hκ4 c hc hh s hF (fun _ _ => isRegularDriver_regHist _ _)
  filter_upwards [hD, ae_run_regHist (hR s), (hR s).ae_pieceRegular] with ω hd hrun hpieces
  apply joinedDriver_congr_program
  intro k θ T hk t ht
  have hk' : k < (scheduleSpec s).2.2.length := (List.getElem?_eq_some_iff.1 hk).1
  have hlF := launch_of_previous_top (κ := κ) (b := c.fn) (J := c.jumps) s
    (fun j => regHist (scheduleSpec s) (E s) j ω) hk' (fun j hj => (hd j (hj.trans hk')).1)
  have hl : (ExplState.run κ c.fn c.jumps (scheduleSpec s) (fun j => E s j ω)
      (k + 1)).2.2.2.1 k ≠ none := by rwa [hrun (k + 1)] at hlF
  obtain ⟨⟨chart, θ'⟩, hlaunch⟩ := Option.ne_none_iff_exists'.1 hl
  have hp := hpieces k chart θ' hlaunch
  have htime : instrTime (scheduleSpec s) k = T := by
    unfold instrTime scheduleSpec
    rw [hk]
  have htop : (E s k ω).2 = ⊤ := by
    simpa only [regHist_snd] using (hd k hk').1
  have hstop : (t : ℝ≥0∞) ≤ min (instrTime (scheduleSpec s) k) (E s k ω).2 := by
    simpa only [htop, min_top_right, htime] using ht
  simpa only [zero_add, regHist] using regularize_eq_of_le hp.1 hp.2.1 hstop

/-- The complete field-measurable enumeration under the R51 source premise. -/
theorem exists_measurable_extreme_tree_of_stagedPiecesRegular
    (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (c : BoundaryWord) (hc : ExtremeHeights κ c)
    (hh : IsGFFWithBoundaryData P h c.fn c.jumps)
    {E : Schedule → ℕ → Ω → Driver}
    (hE : ∀ s, IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ c.fn c.jumps P (scheduleSpec s) (E s))
    (hh𝒢 : Measurable[𝒢] h) :
    ∃ ξ : ℕ → Ω → ℝ → ℂ,
      (∀ n t, Measurable[𝒢] fun ω => ξ n ω t) ∧
      (∀ n ω, Continuous (ξ n ω)) ∧
      (∀ n m ω, ξ (descendantIndex n m) ω (terminal (scheduleAt n)) =
        extremeAngleTreeNode ξ (fun n => terminal (scheduleAt n)) n ω) ∧
      ∀ᵐ ω ∂P, ∀ n, ∀ η : ℝ≥0 → ℂ,
        IsGeneratingTrace (prefixDriver E (scheduleAt n) ω) (terminal (scheduleAt n)) η →
        EqOn (ξ n ω) (fun t : ℝ => η t.toNNReal) (Icc 0 (terminal (scheduleAt n) : ℝ)) := by
  obtain ⟨ξ, hm, hcont, hroot, he⟩ := exists_measurable_extreme_tree h44 hκ hκ4 c hc hh
    (fun s => isStagedHistory_regHist c.isPiecewiseConstantBoundaryData (hE s) (hR s))
    (fun _ _ _ => isRegularDriver_regHist _ _) hh𝒢
  refine ⟨ξ, hm, hcont, hroot, ?_⟩
  filter_upwards [he, ae_prefixDriver_regHist h44 hκ hκ4 c hc hh hE hR] with ω hξ hω n η hη
  apply hξ n η
  rwa [hω]

end InteractingSLE.Sec5.Prop513Schedule
