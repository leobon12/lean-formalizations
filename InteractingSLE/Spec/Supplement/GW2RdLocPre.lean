/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdSafeSplit
import InteractingSLE.Spec.Supplement.GW2FbMean

/-!
# GW2's union locality, part 3: the retained marks with the record, and the stop before the lifetime

Packet PROVE-GW2-RELDET (locality clause of `GW2Rd.HasGW2UnionLocality`). Two inputs of the assembly:

* **`exists_retained_marks_rec_gw2`**: `GW2Fb.exists_retained_marks_gw2` (from Theorems 1.2–1.3) with all of
  `Supp8.GB6LineL.exists_retained_marks`'s output kept — the marks of the inverted counterflow hull contain the null
  sets and the counterflow RECORD (the physical σ-algebra of K2's lines reads the record);
* **`ae_lt_lifetime_of_lt_stop`**: on the good event, before the stop (`a(t) < V`) the physical time `t` is before the
  flow's lifetime — the version's live clause and its cap give, below every `u < V`, a time `t₃ < min(T_c, ζα)` with
  clock above `u`; if `ζα ≤ t` the physical clock at `t` (a supremum over such times, `RelSafe.physClock_eq_iSup`)
  would be `≥ V`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Restart Exist Exist.StagedLaw WholeField LocalSets
open Supp8.GB6 Supp8.GB6LineL Supp8.GB6LMean Supp8.Q3Chain
open GW2JointKernel GW2TipSystem GW2Fb

section Retained

variable {κ θ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h h' X : Ω → DistOn upperHalfPlaneOpens} {b b' : ℝ → ℝ} {J J' : Finset ℝ}

/-- **The marks of GW2's retained set, with the null sets and the counterflow record**
(`GW2Fb.exists_retained_marks_gw2` with `GB6LineL.exists_retained_marks`'s full output). -/
theorem exists_retained_marks_rec_gw2 (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (htr : ∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (h ω) (X ω)) {uh u₀ : ℂ → ℝ}
    (huh : IsBoundedHarmonicExtension (cfData κ b J) (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) uh)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
      (flowLineXL b J 0) (flowLineXR b J 0)) (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) u₀)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField X u₀) P) (s : ℝ≥0) :
    ∃ ℋ : {m : MeasurableSpace Ω // m ≤ mΩ}, Ito.nullSets P ≤ ℋ.1 ∧ Measurable[ℋ.1] (gb6Rec s W ζ) ∧
      Measurable[ℋ.1, hittingSigma] (retSet s W ζ) ∧
      ℋ.1 ≤ aeSigma (MeasurableSpace.comap (centredField X u₀) inferInstance) P ∧
      WholeField.IsHistoryAvoidanceLocal ℋ.1 (retSet s W ζ) (centredField X u₀) P := by
  have hk : (0 : ℝ) < 16 / κ := by positivity
  have e16 : 16 / (16 / κ) = κ := by field_simp
  obtain ⟨c', hc'J, hc'b⟩ := BoundaryWord.exists_fn_eq hb'
  have hG' : IsGFFWithBoundaryData P h' b' J' :=
    Theorem14.GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hk hb' hcf
  have hGc' : IsGFFWithBoundaryData P h' c'.fn c'.jumps := by
    rw [hc'J]
    exact WangWu.isGFFWithBoundaryData_congr (fun y hy => (hc'b y hy).symm) hG'
  have hcfc : IsFlowLineDriver (16 / κ) c'.fn c'.jumps 0 P h' W ζ :=
    (isFlowLineDriver_congr_of_eqOn hb' c'.isPiecewiseConstantBoundaryData J' hc'b).2 hcf
  have hdet : LP.HasFieldDeterminedHistories.{u} (16 / κ) (flowLineXL c'.fn c'.jumps 0)
      (flowLineXR c'.fn c'.jumps 0) (flowLineRhoL (16 / κ) c'.fn c'.jumps 0 0)
      (flowLineRhoR (16 / κ) c'.fn c'.jumps 0 0) :=
    Exist.Param12.hasFieldDeterminedHistories h12 h13 hk (Theorem15.isOrderedForceWord_flowLine c'.fn c'.jumps 0)
  have hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC (16 / κ)))
      (chiC (16 / (16 / κ))) (h' ω) (h ω) := fun ω => isChartTransport_dual hκ (hT ω)
  have huh' : IsBoundedHarmonicExtension (cfData (16 / (16 / κ)) b J)
      (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) uh := by
    rw [e16]
    exact huh
  obtain ⟨uc', huc', -⟩ :=
    PiecewiseConstant.existsUnique_isBoundedHarmonicExtension c'.isPiecewiseConstantBoundaryData
  have hcen := centredField_eq_reflect (κ := 16 / κ) hk c'.isPiecewiseConstantBoundaryData hGc' hb hG hT' huc' huh'
  have hcX := (centredField_flow_eq hκ hb htr huh hu₀).2
  have hcen' : ∀ ω, centredField X u₀ ω = WangWu.reflectField (centredField h' uc' ω) := fun ω => by
    rw [← hcX]
    exact hcen ω
  obtain ⟨ℋ, hnull, hrecℋ, hℋd, hloc⟩ :=
    exists_retained_marks (κ := 16 / κ) (θ := 0) hk hcfc hdet huc' hh0.measurable hcen' s
  exact ⟨ℋ, hnull, hrecℋ, (measurable_retOfRec s).comp hrecℋ, hℋd, hloc⟩

end Retained

/-! ### Before the stop, the physical time is before the flow's lifetime -/

section Stop

open Supp8.RelSafe Supp8.GB6.RelDrv

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens} {W Wα : ℝ≥0 → Ω → ℝ} {ζ ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
  {GT : Set Ω} {s : ℝ≥0} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}

/-- **Before the stop, the physical time is before the flow's lifetime**, on the good event. -/
theorem ae_lt_lifetime_of_lt_stop (hfl : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hGT : ∀ ω ∈ GT, PhysGood s (regW s Wα ζα) W ζ (extTr s Wα ζα α) γ ω)
    (hver : IsGW2RelVersion s P W Wα ζ ζα γ α R V) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ GT → gw2LineClock s Wα ζα W ζ GT V t ω < V ω → (t : ℝ≥0∞) < ζα ω := by
  filter_upwards [hver.1.1.1.2.2.2.2.2.2, hver.2, ae_driver_zero_continuousOn hfl] with ω hlive hcap hd hωG hlt
  obtain ⟨-, -, hs, hsH, -, -⟩ := hGT ω hωG
  by_contra hcon
  have hζt : ζα ω ≤ t := le_of_not_gt hcon
  have hV : V ω ≤ physClock s (regW s Wα ζα) W ζ GT t ω := by
    rw [physClock_eq_iSup hGT hωG]
    refine ENNReal.le_of_forall_nnreal_lt fun u hu => ?_
    obtain ⟨t₁, ht₁, hu₁⟩ := (hlive hs hsH).2.1 u hu
    obtain ⟨t₂, ht₂, hu₂⟩ := hcap hsH u hu
    have ht₂t : t₂ < t := by
      have := lt_of_lt_of_le ht₂ hζt
      exact_mod_cast this
    -- the two clocks agree before the lifetime
    have hclock : gw2Clock s W Wα ω t₂ = gb6Clock s (regW s Wα ζα) W ω t₂ := by
      obtain ⟨t₄, ht₂₄, ht₄ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht₂
      unfold gw2Clock gb6Clock relClock
      rw [fwdHull_eq_of_eqOn (W := fun r : ℝ => Wα r.toNNReal ω) (W' := fun r : ℝ => regW s Wα ζα r.toNNReal ω)
        t₂.coe_nonneg (show (t₂ : ℝ) < t₄ by exact_mod_cast ht₂₄) fun r hr => ?_]
      have hr' : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < ζα ω := by
        refine lt_of_le_of_lt ?_ ht₄ζ
        exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hr.2
      exact (regW_eq_of_lt s hd.1 hd.2 hr').symm
    -- a time below both the contact and the lifetime, with clock above `u`
    have key : ∃ t₃ : ℝ≥0, (t₃ < t ∧ (t₃ : ℝ≥0∞) < gb6Tc s (extTr s Wα ζα α) γ ω) ∧
        (u : ℝ) < gb6Clock s (regW s Wα ζα) W ω t₃ := by
      rcases le_total t₁ t₂ with h12 | h12
      · exact ⟨t₁, ⟨lt_of_le_of_lt h12 ht₂t, ht₁⟩, hu₁⟩
      · exact ⟨t₂, ⟨ht₂t, lt_of_le_of_lt (ENNReal.coe_le_coe.2 h12) ht₁⟩, hclock ▸ hu₂⟩
    obtain ⟨t₃, ht₃, hu₃⟩ := key
    refine le_trans ?_ (le_iSup₂_of_le (f := fun (t' : ℝ≥0) (_ : t' < t ∧ (t' : ℝ≥0∞) <
      gb6Tc s (extTr s Wα ζα α) γ ω) => ENNReal.ofReal (gb6Clock s (regW s Wα ζα) W ω t')) t₃ ht₃ le_rfl)
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hu₃.le
  have : gw2LineClock s Wα ζα W ζ GT V t ω = V ω := min_eq_right hV
  rw [this] at hlt
  exact lt_irrefl _ hlt

end Stop

end InteractingSLE.Theorem14.GW2Rd
