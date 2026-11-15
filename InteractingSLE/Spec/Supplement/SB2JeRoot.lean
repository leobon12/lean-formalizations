/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JeStart
import InteractingSLE.Spec.Supplement.SB2JwAS
import InteractingSLE.Spec.Supplement.SB2JwZeroAS
import InteractingSLE.Spec.Supplement.SB2JvCap
import InteractingSLE.Spec.Supplement.SB2JvHead

/-!
# SB2(2) under the v6 rule: the relative root at one sample

Packet PROVE-SB2-LIFTSET (round 21). **`root_pkg`** (deterministic, one sample): from the actual start piece's facts
(`Stage0Act`, the corner lift, the launch at `relOff`), the root facts of the shifted start piece (`sb2LowerRootFull`
at the sample) and the relative root's rule (zero driver at a zero root or a corner; generation on the v6 mask), the
relative root's facts:

* the dense readings of the root stage curve in the initial chart (the v6 mask at stage `0`);
* the root is a regular piece, with a good record when finite;
* the root facts `RootFactsAt` (D25) and the stage-`0` lift of the actual start piece;
* the stage-`0` part of `StagesGeom4` (`Stage0Facts`, the corner lift) and of `Mn.StageFactsAll`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep GW1P
open Sec7.PocketTraversal Sec7.Lemma71C

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {c : Chart} {m : ℝ} {D₁ D₂ : ℕ → Drv}
  {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {A : Set ℂ}

/-- The initial state's chart is the identity (recentred at `0`). -/
theorem stChart_init_zero' : stChart (ExplState.init 0) = Chart.id.recenter 0 := rfl

/-- The initial chart's domain contains `ℍ`. -/
theorem H_subset_dom_init : H ⊆ ((stChart (ExplState.init 0)).dom : Set ℂ) := by
  intro w hw
  show w ∈ interior ((stChart (ExplState.init 0)).2.1 '' H)
  have hI : (stChart (ExplState.init 0)).2.1 '' H = H := by
    ext z
    simp [ExplState.init, stChart, Chart.id, Chart.recenter]
  rw [hI, QuantumZipper.isOpen_H.interior_eq]
  exact hw

/-- A lifted good point is in `ℍ`. -/
theorem liftPt_mem_H_of_good {p : ℝ≥0 → ℂ} {L : ℝ≥0∞} (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) {t : ℝ≥0}
    (ht : t ∈ goodTp c p L) : liftPt c m (p t) ∈ H := by
  obtain ⟨w, hw, hwe⟩ := ht.2
  unfold liftPt
  rw [← hwe, hc1 w hw]
  exact Mo.add_ofReal_mem_H hw _

/-- The shifted start piece is the root piece. -/
theorem shiftD_zero_eq (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (R : ℝ) (D₁ : ℕ → Drv) :
    shiftD κ θ b₁ J₁ R D₁ 0 = visitTime (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁)) R := by
  unfold shiftD; simp

/-- **The relative root at one sample** (v6 rule at stage `0`). -/
theorem root_pkg (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hO : IsOpen (c.2.1 '' H)) (hreg0 : IsRegularDriver (D₂ 0))
    (hZ0 : (ZeroRoot κ θ b₁ J₁ R D₁ ∨ (D₁ (relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0 = 0) →
      D₂ 0 = zeroDrv)
    (hgen0 : ¬ ZeroRoot κ θ b₁ J₁ R D₁ → (D₁ (relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0 ≠ 0 →
      Nv.DenseReads c m (rootPt (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁)) R)
        (rootLife (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁)) R) (ExplState.init 0) →
      (D₂ 0).2 = capLife (stCurvep c m (rootPt (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁))
        (D₁ (relOff κ θ b₁ J₁ R D₁)) R) (rootLife (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁))
        (D₁ (relOff κ θ b₁ J₁ R D₁)) R) (ExplState.init 0)) ∧
      ∀ T < capLife (stCurvep c m (rootPt (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁))
          (D₁ (relOff κ θ b₁ J₁ R D₁)) R) (rootLife (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁))
          (D₁ (relOff κ θ b₁ J₁ R D₁)) R) (ExplState.init 0)),
        IsGeneratingTrace (D₂ 0).1 T (capTrace (stCurvep c m (rootPt (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁))
          (D₁ (relOff κ θ b₁ J₁ R D₁)) R) (rootLife (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁))
          (D₁ (relOff κ θ b₁ J₁ R D₁)) R) (ExplState.init 0))))
    (hRF : ¬ ZeroRoot κ θ b₁ J₁ R D₁ →
      rootLife (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁)) R ≠ 0 →
      ∀ s₂ : ExplState, stChart s₂ = Chart.id.recenter 0 →
        IsDrivenCurve (stCurvep c m (rootPt (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁))
          (D₁ (relOff κ θ b₁ J₁ R D₁)) R) (rootLife (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁))
          (D₁ (relOff κ θ b₁ J₁ R D₁)) R) s₂) ∧
        ∀ e₂ : Drv, IsRegularDriver e₂ → e₂.2 = capLife (stCurvep c m (rootPt (wRun κ θ b₁ J₁ D₁
            (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁)) R) (rootLife (wRun κ θ b₁ J₁ D₁
            (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁)) R) s₂) →
          (∀ T < capLife (stCurvep c m (rootPt (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁))
              (D₁ (relOff κ θ b₁ J₁ R D₁)) R) (rootLife (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁))
              (D₁ (relOff κ θ b₁ J₁ R D₁)) R) s₂),
            IsGeneratingTrace e₂.1 T (capTrace (stCurvep c m (rootPt (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁))
              (D₁ (relOff κ θ b₁ J₁ R D₁)) R) (rootLife (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁))
              (D₁ (relOff κ θ b₁ J₁ R D₁)) R) s₂))) →
          StageRelP c m (rootPt (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁)) R)
              (rootLife (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁)) R) s₂ e₂ ∧
            Mn.StageFacts c m (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁))
              (shiftD κ θ b₁ J₁ R D₁ 0) s₂ e₂)
    (hlaunch0 : ¬ ZeroRoot κ θ b₁ J₁ R D₁ →
      (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁ + 1)).2.2.2.1 (relOff κ θ b₁ J₁ R D₁) ≠ none)
    (hS0A : ¬ ZeroRoot κ θ b₁ J₁ R D₁ →
      (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁ + 1)).2.2.2.1 (relOff κ θ b₁ J₁ R D₁) ≠ none →
      (D₁ (relOff κ θ b₁ J₁ R D₁)).2 ≠ 0 →
      (D₁ (relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0 ≠ 0 →
      Stage0Act c m β₀ tL (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁))
        (fun t => pcPt (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁))
          (shiftD κ θ b₁ J₁ R D₁ 0 + t))
        ((D₁ (relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0))
    (hcorner : ¬ ZeroRoot κ θ b₁ J₁ R D₁ →
      (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁ + 1)).2.2.2.1 (relOff κ θ b₁ J₁ R D₁) ≠ none →
      (D₁ (relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0 = 0 →
      ∀ e₂ : Drv, IsRegularDriver e₂ → e₂.2 = 0 →
        LiftRel β₀ tL γ (newPc (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁)))
          (newPc (ExplState.init 0) e₂))
    {R' : ℝ} (hγ : IsTailLiftCurve c R' m β₀ tL γ) (hU : UpperChartOK c) (hDom : c.2.1 '' H = H \ fillH A)
    (hK : β₀ '' Icc 0 tL ⊆ hullK A) (hβ : IsProperCurve β₀)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) :
    (¬ ZeroRoot κ θ b₁ J₁ R D₁ → (D₁ (relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0 ≠ 0 →
      Nv.DenseReads c m (rootPt (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁)) R)
        (rootLife (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁)) R)
        (ExplState.init 0)) ∧
    GW1P.PieceRegular (D₂ 0).1 (D₂ 0).2 ∧
    ((D₂ 0).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ (D₂ 0)))) ∧
    RootFactsAt κ θ b₁ J₁ b₂ J₂ R c m D₁ D₂ ∧
    (¬ ZeroRoot κ θ b₁ J₁ R D₁ →
      (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁ + 1)).2.2.2.1 (relOff κ θ b₁ J₁ R D₁) ≠ none →
      ((D₁ (relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0 ≠ 0 →
        Stage0Facts c m β₀ tL (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁))
          (fun t => pcPt (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁))
            (shiftD κ θ b₁ J₁ R D₁ 0 + t))
          ((D₁ (relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0) (wRun κ θ b₂ J₂ D₂ 0) (D₂ 0)) ∧
      LiftRel β₀ tL γ (newPc (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁)))
        (newPc (ExplState.init 0) (D₂ 0))) := by
  set o := relOff κ θ b₁ J₁ R D₁ with ho
  set s₁ := wRun κ θ b₁ J₁ D₁ o with hs₁
  set e₁ := D₁ o with he₁
  have hsh : shiftD κ θ b₁ J₁ R D₁ 0 = visitTime s₁ e₁ R := shiftD_zero_eq κ θ b₁ J₁ R D₁
  have hpE : (fun t => pcPt s₁ e₁ (shiftD κ θ b₁ J₁ R D₁ 0 + t)) = rootPt s₁ e₁ R := by
    funext t; rw [hsh]; rfl
  have hLE : e₁.2 - shiftD κ θ b₁ J₁ R D₁ 0 = rootLife s₁ e₁ R := by rw [hsh]; rfl
  have hinit : stChart (ExplState.init 0) = Chart.id.recenter 0 := rfl
  -- the nonzero case
  have hgood : ∀ hZ : ¬ ZeroRoot κ θ b₁ J₁ R D₁, e₁.2 - shiftD κ θ b₁ J₁ R D₁ 0 ≠ 0 →
      Nv.DenseReads c m (rootPt s₁ e₁ R) (rootLife s₁ e₁ R) (ExplState.init 0) ∧
      IsDrivenCurve (stCurvep c m (rootPt s₁ e₁ R) (rootLife s₁ e₁ R) (ExplState.init 0)) ∧
      StageRelP c m (rootPt s₁ e₁ R) (rootLife s₁ e₁ R) (ExplState.init 0) (D₂ 0) ∧
      Mn.StageFacts c m s₁ e₁ (shiftD κ θ b₁ J₁ R D₁ 0) (ExplState.init 0) (D₂ 0) ∧
      Stage0Act c m β₀ tL s₁ e₁ (fun t => pcPt s₁ e₁ (shiftD κ θ b₁ J₁ R D₁ 0 + t))
        (e₁.2 - shiftD κ θ b₁ J₁ R D₁ 0) ∧
      (D₂ 0).2 = capLife (stCurvep c m (rootPt s₁ e₁ R) (rootLife s₁ e₁ R) (ExplState.init 0)) ∧
      (∀ T < capLife (stCurvep c m (rootPt s₁ e₁ R) (rootLife s₁ e₁ R) (ExplState.init 0)),
        IsGeneratingTrace (D₂ 0).1 T (capTrace (stCurvep c m (rootPt s₁ e₁ R) (rootLife s₁ e₁ R)
          (ExplState.init 0)))) := by
    intro hZ hL
    have hl := hlaunch0 hZ
    have he0 : e₁.2 ≠ 0 := fun h => hL (by rw [h]; exact zero_tsub _)
    have hA := hS0A hZ hl he0 hL
    have hL' : rootLife s₁ e₁ R ≠ 0 := by rw [← hLE]; exact hL
    -- the dense readings of the root
    have hpcc := continuousOn_pcPt_launch hP₁ hl
    have hpc : ContinuousOn (rootPt s₁ e₁ R) {t : ℝ≥0 | (t : ℝ≥0∞) < rootLife s₁ e₁ R} := by
      refine hpcc.comp (continuous_const.add continuous_id).continuousOn fun t ht => ?_
      have ht' : (t : ℝ≥0∞) < e₁.2 - (visitTime s₁ e₁ R : ℝ≥0∞) := ht
      show ((visitTime s₁ e₁ R + t : ℝ≥0) : ℝ≥0∞) ≤ e₁.2
      rw [ENNReal.coe_add]
      exact (lt_tsub_iff_left.1 ht').le
    have hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < rootLife s₁ e₁ R} ⊆ closure (goodTp c (rootPt s₁ e₁ R) (rootLife s₁ e₁ R)) := by
      have h := hA.2.1
      rw [hpE, hLE] at h; exact h
    have hdense : Nv.DenseReads c m (rootPt s₁ e₁ R) (rootLife s₁ e₁ R) (ExplState.init 0) :=
      denseReads_of hL' hpc hO hgd fun t ht => H_subset_dom_init (liftPt_mem_H_of_good hc1 ht)
    obtain ⟨he₂, hg⟩ := hgen0 hZ hL hdense
    obtain ⟨hdr, hall⟩ := hRF hZ hL' (ExplState.init 0) hinit
    obtain ⟨hrel, hSF⟩ := hall (D₂ 0) hreg0 he₂ hg
    exact ⟨hdense, hdr, hrel, hSF, hA, he₂, hg⟩
  have hzero : ZeroRoot κ θ b₁ J₁ R D₁ ∨ e₁.2 - shiftD κ θ b₁ J₁ R D₁ 0 = 0 → D₂ 0 = zeroDrv := hZ0
  have hcont : (D₂ 0).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ (D₂ 0))) := fun hfin => by
    by_cases hz : ZeroRoot κ θ b₁ J₁ R D₁ ∨ e₁.2 - shiftD κ θ b₁ J₁ R D₁ 0 = 0
    · rw [hzero hz]; exact isDrvGood_zeroDrv
    · push Not at hz
      obtain ⟨-, -, hrel, -⟩ := hgood hz.1 hz.2
      have hmin : min (⊤ : ℝ≥0∞) (D₂ 0).2 = (D₂ 0).2 := min_eq_right le_top
      refine isDrvGood_of_continuousOn_le hreg0 (by rw [hmin]; exact hfin) ?_
      rw [hmin]
      by_cases hLt : rootLife s₁ e₁ R = ⊤
      · exact (hrel.2 hLt).1
      · exact (hrel.1 hLt).2.1
  have hpr : GW1P.PieceRegular (D₂ 0).1 (D₂ 0).2 := by
    by_cases hz : ZeroRoot κ θ b₁ J₁ R D₁ ∨ e₁.2 - shiftD κ θ b₁ J₁ R D₁ 0 = 0
    · rw [hzero hz]; exact Mn.pieceRegular_of_zero isRegularDriver_zeroDrv rfl
    · push Not at hz
      obtain ⟨-, -, -, hSF, -⟩ := hgood hz.1 hz.2
      exact hSF.2.2.2.2.2.2
  refine ⟨fun hZ hL => (hgood hZ hL).1, hpr, hcont, ⟨hzero, fun hZ hL => ?_, hcont⟩, fun hZ hl => ?_⟩
  · obtain ⟨-, hdr, -, hSF, -, he₂, -⟩ := hgood hZ hL
    refine ⟨?_, hSF⟩
    rw [he₂]; exact (capLife_pos_of_driven hdr).ne'
  · by_cases hL : e₁.2 - shiftD κ θ b₁ J₁ R D₁ 0 = 0
    · refine ⟨fun h => absurd hL h, ?_⟩
      rw [hzero (Or.inr hL)]
      exact hcorner hZ hl hL zeroDrv isRegularDriver_zeroDrv rfl
    · obtain ⟨-, hdr, hrel, -, hA, he₂, hg⟩ := hgood hZ hL
      have hF : Stage0Facts c m β₀ tL s₁ e₁ (fun t => pcPt s₁ e₁ (shiftD κ θ b₁ J₁ R D₁ 0 + t))
          (e₁.2 - shiftD κ θ b₁ J₁ R D₁ 0) (ExplState.init 0) (D₂ 0) := by
        refine hA.facts ?_
        rw [hpE, hLE]; exact hrel
      refine ⟨fun _ => hF, ?_⟩
      refine liftRel_of_stage0 hγ hU hDom hK hβ hβr hP₁ hl (fun hL₂ h => hL₂ (by rw [h]; exact ENNReal.top_sub_coe))
        hF (by rw [hpE, hLE]; exact hdr) (by rw [hpE, hLE]; exact he₂) (by rw [hpE, hLE]; exact hg) hreg0.2.1

end InteractingSLE.Theorem14.SB.Lk
