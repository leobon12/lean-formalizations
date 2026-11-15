/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1PropChain

/-!
# Proposition BW1: the relative configuration of the completed piece (up to the words)

Packet PROVE-BW1-PROP; the BHMean/Q3Rel configuration for BW1 (`planning/handoffs/PROVE-BW1.md` §1, first item).
Proposition BW1 retains the completed first piece `A = α[0, ζ]` of a staged history at a continuation threshold
(trace ending on `ℝ` at the new record `q`) and reads the counterflow in the chart `g_A − W` of the unbounded component.
In the counterflow's frame `w = −1/z` this is GB6's retained chart `Ψ = relMap U ζ` of the piece's driver `U` frozen
at the lifetime, and the relative configuration of the exceptional-point mean identification
(`Q3Rel.relUnionWordBoundaryOffStatement`, `Q3Rel.ae_eqOn_unionMean_of_relConfigOff`) is GB6's, at the stop `ζ`:

* `exists_isRelConfigOff_close`: `Q3Kernel.exists_isRelConfigOff_gb6` with `0 < s` in place of the interior tip
  (proof copied; that proof uses the interior tip only to get `0 < s`);
* `regOf`, `isRegularDriver_regOf`, `pieceRegular_regOf`, `launch_regOf`: the piece with its driver frozen after the
  lifetime (the frozen `IsStagedHistory` does not fix the driver after the lifetime; a launch only reads the stopped
  driver), regular when the piece is;
* **`bw1_piece_geometry`**: on the threshold event, for a regular piece whose trace does not return to `0` before the
  lifetime: the frozen driver `U` has a global Loewner trace equal to the piece's on `[0, ζ]`, ending at `q ≠ 0`; the
  retained chart of the completed piece is an `IsRetainedChartOff`; and the inverse of BW1's state chart is the inverse
  Loewner map `f_ζ` of `U` (so `((stateChart).trans infinitySourceChart).2.1 = −1/· ∘ Ψi`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd)

namespace InteractingSLE.Theorem14.BW1Prop

open Supp8 Supp8.Q3Kernel
open Supp8.GB6 (relMap relInv relClock firstContactTime sphereInv)
open Supp8.Q3Rel (invHull relLog relBad IsRelConfigOff)
open Exist Exist.Staged Exist.StagedLaw

/-! ### The relative configuration at a stop with positive own time -/

section Sample

variable {wα w : ℝ≥0 → ℝ} {Tα : ℝ≥0∞} {α γ : ℝ≥0 → ℂ} {s : ℝ≥0} {U : ℝ → ℝ} {αr : ℝ → ℂ} {t₂ : ℝ}

/-- **The relative configuration up to the words, at a stop with positive own time** (deterministic;
`Q3Kernel.exists_isRelConfigOff_gb6` with `0 < s` in place of the interior tip). For counterflow times
`0 < t < t₁ < T_c` there is a relative chain `(Wr, ηr)` at `u = a(t) > 0` (`Ψ(K'_t) = K̃_u`) such that any words and
means satisfying the word clauses and the candidate formula form an `IsRelConfigOff` with the retained chart. -/
theorem exists_isRelConfigOff_close (hα : IsGeneratingTrace wα Tα α)
    (hwα : ContinuousOn wα {t | (t : ℝ≥0∞) < Tα}) (hwα0 : wα 0 = 0) (hs : (s : ℝ≥0∞) < Tα) (hs0 : (0 : ℝ) < s)
    (hU : Continuous U) (hU0 : U 0 = 0) (hαr : IsLoewnerTrace U αr) (hNR : ∀ v ∈ Ioc (0 : ℝ) s, αr v ≠ 0)
    (hst₂ : (s : ℝ) < t₂) (hUeq : ∀ r ∈ Icc (0 : ℝ) t₂, U r = wα r.toNNReal)
    (hγ : IsGeneratingTrace w ⊤ γ) (hw : Continuous w) (hw0 : w 0 = 0) {t t₁ : ℝ≥0} (ht0 : 0 < t)
    (htt₁ : t < t₁)
    (ht₁ : (t₁ : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
      ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)) :
    ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ), Continuous Wr ∧ Wr 0 = 0 ∧ IsLoewnerTrace Wr ηr ∧
      0 < relClock U s (fun r : ℝ => w r.toNNReal) t ∧
      relMap U s '' fwdHull (fun r : ℝ => w r.toNNReal) t =
        fwdHull Wr (relClock U s (fun r : ℝ => w r.toNNReal) t) ∧
      ∀ (χ lam : ℝ) (β₀ βE βu : ℝ → ℝ) (S₀ SE Su : Finset ℝ) (G₀ GE G v : ℂ → ℝ),
        IsBoundedHarmonicExtension β₀ S₀ G₀ → IsBoundedHarmonicExtension βE SE GE →
        IsBoundedHarmonicExtension βu Su G →
        BHMean.IsSideWord βE SE (fwdMapInv (fun r : ℝ => w r.toNNReal) t)
          (fwdHull (fun r : ℝ => w r.toNNReal) t) lam →
        BHMean.IsSideWord βu Su (fwdMapInv Wr (relClock U s (fun r : ℝ => w r.toNNReal) t))
          (fwdHull Wr (relClock U s (fun r : ℝ => w r.toNNReal) t)) lam →
        BHMean.IsFlowedWord βu β₀ Su S₀ (fwdMapInv Wr (relClock U s (fun r : ℝ => w r.toNNReal) t))
          (fwdHull Wr (relClock U s (fun r : ℝ => w r.toNNReal) t)) →
        (∀ z, v z = G (fwdMap Wr (relClock U s (fun r : ℝ => w r.toNNReal) t) (relMap U s z)) -
          χ * ((logDerivFwd Wr (relClock U s (fun r : ℝ => w r.toNNReal) t) (relMap U s z)).im +
            (relLog U s z).im)) →
        IsRelConfigOff (invHull U s) (relMap U s) (relInv U s) (relLog U s) (relBad U s)
          (fun r : ℝ => w r.toNNReal) Wr (fun r : ℝ => γ r.toNNReal) ηr t
          (relClock U s (fun r : ℝ => w r.toNNReal) t) χ lam β₀ βE βu S₀ SE Su G₀ GE G v := by
  have hΨ := Q3Rel.isRetainedChartOff_relMap hU hU0 hαr hs0 hNR
  obtain ⟨Wr, ηr, hWr, hWr0, hηr, hu, hK, hd, htip⟩ :=
    exists_relChain_tip_close hα hwα hwα0 hs hs0 hU hU0 hst₂ hUeq hΨ hγ hw hw0 ht0 htt₁ ht₁
  refine ⟨Wr, ηr, hWr, hWr0, hηr, hu, hK, fun χ lam β₀ βE βu S₀ SE Su G₀ GE G v hG₀ hGE hG hsE hsu hflow hv => ?_⟩
  have hWc : Continuous fun r : ℝ => w r.toNNReal := hw.comp continuous_real_toNNReal
  have hWc0 : (fun r : ℝ => w r.toNNReal) 0 = 0 := by simp [hw0]
  exact Q3Rel.isRelConfigOff_gb6 hU hU0 hαr hs0 hNR hWc hWc0 (isLoewnerTrace_of_isGeneratingTrace hγ) t.2 hWr hWr0
    hηr hu.le hK hd htip hG₀ hGE hG hsE hsu hflow hv


end Sample

/-! ### The piece with its driver frozen after the lifetime -/

section Reg

/-- **The piece with its driver frozen after its lifetime** (the stopped driver of `CounterflowRange`). -/
def regOf (D : (ℝ≥0 → ℝ) × ℝ≥0∞) : (ℝ≥0 → ℝ) × ℝ≥0∞ := (fun r => D.1 (min (r : ℝ≥0∞) D.2).toNNReal, D.2)

variable {D : (ℝ≥0 → ℝ) × ℝ≥0∞}

theorem regOf_fst_of_le {r : ℝ≥0} (hr : (r : ℝ≥0∞) ≤ D.2) : (regOf D).1 r = D.1 r :=
  CounterflowRange.stopped_eq_of_lt hr

theorem min_coe_toNNReal_min (r : ℝ≥0) (a : ℝ≥0∞) :
    min (((min (r : ℝ≥0∞) a).toNNReal : ℝ≥0) : ℝ≥0∞) a = min (r : ℝ≥0∞) a := by
  have hne : min (r : ℝ≥0∞) a ≠ ⊤ := (lt_of_le_of_lt (min_le_left _ _) ENNReal.coe_lt_top).ne
  rw [ENNReal.coe_toNNReal hne]
  exact min_eq_left (min_le_right _ _)

/-- The frozen piece has the same stopped driver. -/
theorem retOf_regOf : (retOf ⊤ (regOf D)).1 = (retOf ⊤ D).1 := by
  funext r
  show D.1 (min (((min (r : ℝ≥0∞) (min ⊤ D.2)).toNNReal : ℝ≥0) : ℝ≥0∞) D.2).toNNReal =
    D.1 (min (r : ℝ≥0∞) (min ⊤ D.2)).toNNReal
  rw [min_eq_right (le_top : D.2 ≤ ⊤), min_coe_toNNReal_min]

theorem stopDrv_regOf : stopDrv ⊤ (regOf D) = stopDrv ⊤ D := by
  funext x
  simp only [stopDrv, retOf_regOf]

/-- **A launch reads its piece only through the stopped driver**: the frozen piece gives the same status. -/
theorem stStatus_launch_regOf (s : ExplState) (k : ℕ) (θ : ℝ) :
    stStatus (ExplState.launch s k (regOf D) θ ⊤) = stStatus (ExplState.launch s k D θ ⊤) :=
  BW1Term.stStatus_launch_congr retOf_regOf rfl

/-- The frozen piece gives the same chart (finite lifetime). -/
theorem stChart_launch_regOf (s : ExplState) (k : ℕ) (θ : ℝ) (hfin : D.2 ≠ ⊤) :
    stChart (ExplState.launch s k (regOf D) θ ⊤) = stChart (ExplState.launch s k D θ ⊤) := by
  rw [(launch_eq_of_ne_top s k (regOf D) θ ⊤ (GW1W.min_top_ne_top (D := regOf D) hfin)).1,
    (launch_eq_of_ne_top s k D θ ⊤ (GW1W.min_top_ne_top hfin)).1, stopDrv_regOf]
  rfl

/-- The frozen piece gives the same current point (finite lifetime). -/
theorem stPt_launch_regOf (s : ExplState) (k : ℕ) (θ : ℝ) (hfin : D.2 ≠ ⊤) :
    stPt (ExplState.launch s k (regOf D) θ ⊤) = stPt (ExplState.launch s k D θ ⊤) := by
  rw [(launch_eq_of_ne_top s k (regOf D) θ ⊤ (GW1W.min_top_ne_top (D := regOf D) hfin)).2.2.2.2.2,
    (launch_eq_of_ne_top s k D θ ⊤ (GW1W.min_top_ne_top hfin)).2.2.2.2.2]
  have ht : stopTime ⊤ (regOf D) = stopTime ⊤ D := rfl
  have h2 : (regOf D).2 = D.2 := rfl
  unfold lPt lRecR lRecL lHit lAlive
  rw [stopDrv_regOf, ht, h2]

/-- **The frozen piece of a piece continuous up to its lifetime is a regular driver.** -/
theorem isRegularDriver_regOf (hc : ContinuousOn D.1 {s | (s : ℝ≥0∞) ≤ D.2}) (h0 : D.1 0 = 0) :
    IsRegularDriver (regOf D) := by
  refine ⟨?_, ?_, fun s hs => ?_, fun hfin hpos c hlim => ?_⟩
  · exact (hc.mono fun s (hs : (s : ℝ≥0∞) < D.2) => hs.le).congr
      fun s (hs : (s : ℝ≥0∞) < D.2) => regOf_fst_of_le hs.le
  · rw [regOf_fst_of_le (by simp)]
    exact h0
  · change D.2 ≤ (s : ℝ≥0∞) at hs
    have hfin : D.2 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hs
    show D.1 (min (s : ℝ≥0∞) D.2).toNNReal = D.1 (min ((D.2.toNNReal : ℝ≥0) : ℝ≥0∞) D.2).toNNReal
    rw [min_eq_right hs, ENNReal.coe_toNNReal hfin, min_self]
  · change D.2 ≠ ⊤ at hfin
    change 0 < D.2 at hpos
    change Tendsto (regOf D).1 (𝓝[<] D.2.toNNReal) (𝓝 c) at hlim
    show (regOf D).1 D.2.toNNReal = c
    have hT : ((D.2.toNNReal : ℝ≥0) : ℝ≥0∞) = D.2 := ENNReal.coe_toNNReal hfin
    have hTpos : 0 < D.2.toNNReal := ENNReal.toNNReal_pos hpos.ne' hfin
    have hne : (𝓝[<] D.2.toNNReal).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hTpos⟩
    have hle : ∀ s ∈ Iio D.2.toNNReal, (s : ℝ≥0∞) ≤ D.2 := fun s hs => by
      rw [← hT]
      exact ENNReal.coe_le_coe.2 (le_of_lt hs)
    have hlim' : Tendsto D.1 (𝓝[<] D.2.toNNReal) (𝓝 c) :=
      hlim.congr' (eventually_nhdsWithin_of_forall fun s hs => regOf_fst_of_le (hle s hs))
    have hcont : Tendsto D.1 (𝓝[<] D.2.toNNReal) (𝓝 (D.1 D.2.toNNReal)) := by
      have h1 : ContinuousWithinAt D.1 {s | (s : ℝ≥0∞) ≤ D.2} D.2.toNNReal :=
        hc _ (show ((D.2.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ D.2 by rw [hT])
      exact h1.tendsto.mono_left (nhdsWithin_mono _ fun s hs => hle s hs)
    rw [regOf_fst_of_le (show ((D.2.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ D.2 by rw [hT])]
    exact tendsto_nhds_unique hcont hlim'

/-- **The frozen piece of a regular piece is regular.** -/
theorem pieceRegular_regOf (hP : GW1P.PieceRegular D.1 D.2) : GW1P.PieceRegular (regOf D).1 (regOf D).2 := by
  obtain ⟨h0, hc, α, hα, htr⟩ := hP
  refine ⟨by rw [regOf_fst_of_le (by simp)]; exact h0,
    hc.congr fun s hs => regOf_fst_of_le hs, α, ?_, htr⟩
  exact Sec7.IsGeneratingTrace.congr_lt hα fun s hs => regOf_fst_of_le hs.le

end Reg

/-! ### The completed piece at a threshold -/

section Geometry

variable {D : (ℝ≥0 → ℝ) × ℝ≥0∞} {θ : ℝ} {t : ℝ≥0∞} {r : Bool}

/-- **The driver of the piece stopped at its lifetime, read on `ℝ`** (`stopDrv` of the launch at its lifetime). -/
abbrev pieceDrv (D : (ℝ≥0 → ℝ) × ℝ≥0∞) : ℝ → ℝ := fun x => D.1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) D.2).toNNReal

/-- **The geometry of Proposition BW1's completed piece** (deterministic). For a piece launched from the root that is
regular up to its stop, whose trace `α` does not return to `0` before the lifetime `ζ`, on the event that it ends at a
threshold: `ζ` is finite and positive; the inverse of the state's chart is the inverse Loewner map of the stopped
driver `U = pieceDrv D` at `ζ`; the trace ends at the state's point `q ≠ 0`; `U` has a global Loewner trace equal to `α`
on `[0, ζ]`, not returning to `0` on `(0, ζ]`; and GB6's retained chart of the completed piece is an
`IsRetainedChartOff`. -/
theorem bw1_piece_geometry (hP : GW1P.PieceRegular D.1 (min t D.2)) {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace D.1 (min t D.2) α) (hNR : ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < D.2 → α v ≠ 0)
    (h : BW1.EndsAtThresholdSide (ExplState.launch (ExplState.init 0) 0 D θ t) r) :
    D.2 ≠ ⊤ ∧ 0 < D.2.toNNReal ∧ Continuous (pieceDrv D) ∧ pieceDrv D 0 = 0 ∧
      (BW1.stateChart (ExplState.launch (ExplState.init 0) 0 D θ t)).2.1 =
        fwdMapInv (pieceDrv D) (D.2.toNNReal : ℝ) ∧
      α D.2.toNNReal = (BW1.statePoint (ExplState.launch (ExplState.init 0) 0 D θ t) : ℂ) ∧
      BW1.statePoint (ExplState.launch (ExplState.init 0) 0 D θ t) ≠ 0 ∧
      ∃ αr : ℝ → ℂ, IsLoewnerTrace (pieceDrv D) αr ∧ (∀ x ∈ Icc (0 : ℝ) D.2.toNNReal, αr x = α x.toNNReal) ∧
        (∀ v ∈ Ioc (0 : ℝ) D.2.toNNReal, αr v ≠ 0) ∧
        Q3Rel.IsRetainedChartOff (invHull (pieceDrv D) D.2.toNNReal) (relMap (pieceDrv D) D.2.toNNReal)
          (relInv (pieceDrv D) D.2.toNNReal) (relLog (pieceDrv D) D.2.toNNReal)
          (relBad (pieceDrv D) D.2.toNNReal) := by
  have hle := le_of_endsAtThresholdSide h
  have hfin := ne_top_of_endsAtThresholdSide h
  rw [min_eq_right hle] at hP hα
  have hT : ((D.2.toNNReal : ℝ≥0) : ℝ≥0∞) = D.2 := ENNReal.coe_toNNReal hfin
  rw [launch_eq_top_of_le hle] at h ⊢
  have hst : stStatus (ExplState.launch (ExplState.init 0) 0 D θ ⊤) = stThr (some r) := h
  have hst' : stStatus (ExplState.launch (ExplState.init 0) 0 (regOf D) θ ⊤) = stThr (some r) := by
    rw [stStatus_launch_regOf]
    exact hst
  have h0 : D.2 ≠ 0 := by
    cases r
    · exact (GW1W.launch_thr_false hfin hst).1
    · exact (GW1W.launch_thr_true hfin hst).1
  have hS0 : 0 < D.2.toNNReal := ENNReal.toNNReal_pos h0 hfin
  have hreg := isRegularDriver_regOf hP.2.1 hP.1
  have hPr : GW1P.PieceRegular (regOf D).1 (min ⊤ (regOf D).2) := by
    rw [min_eq_right (le_top : (regOf D).2 ≤ ⊤)]
    exact pieceRegular_regOf hP
  have hαr' : IsGeneratingTrace (regOf D).1 (min ⊤ (regOf D).2) α := by
    rw [min_eq_right (le_top : (regOf D).2 ≤ ⊤)]
    exact Sec7.IsGeneratingTrace.congr_lt hα fun s hs => regOf_fst_of_le hs.le
  have hpt : stPt (ExplState.launch (ExplState.init 0) 0 (regOf D) θ ⊤) =
      stPt (ExplState.launch (ExplState.init 0) 0 D θ ⊤) := stPt_launch_regOf _ _ _ hfin
  have hq : α D.2.toNNReal = (stPt (ExplState.launch (ExplState.init 0) 0 D θ ⊤) : ℂ) := by
    rw [← hpt]
    exact trace_stop_eq_statePoint (D := regOf D) (θ := θ) (t := ⊤) (r := r) hreg hPr hαr' hst'
  have hq0 : stPt (ExplState.launch (ExplState.init 0) 0 D θ ⊤) ≠ 0 := by
    rw [← hpt]
    exact statePoint_ne_zero (D := regOf D) (θ := θ) (t := ⊤) (r := r) hreg hPr hst'
  have hchart : (BW1.stateChart (ExplState.launch (ExplState.init 0) 0 D θ ⊤)).2.1 =
      fwdMapInv (pieceDrv D) (D.2.toNNReal : ℝ) := funext (stChart_launch_init_inv hfin)
  have hαS : IsGeneratingTrace D.1 ((D.2.toNNReal : ℝ≥0) : ℝ≥0∞) α := by rw [hT]; exact hα
  have hwS : ContinuousOn D.1 {s : ℝ≥0 | (s : ℝ≥0∞) ≤ ((D.2.toNNReal : ℝ≥0) : ℝ≥0∞)} := by
    rw [hT]; exact hP.2.1
  have hNR' : ∀ v : ℝ≥0, 0 < v → v ≤ D.2.toNNReal → α v ≠ 0 := fun v hv hvS => by
    rcases hvS.lt_or_eq with hlt | heq
    · exact hNR v hv (by rw [← hT]; exact ENNReal.coe_lt_coe.2 hlt)
    · rw [heq, hq]
      exact_mod_cast hq0
  obtain ⟨αr, hαr, hαeq, hret⟩ := isRetainedChartOff_close hαS hwS hP.1 hS0 hNR'
  rw [hT] at hαr hret
  have hUc : Continuous (pieceDrv D) := (CounterflowRange.continuous_stopped hP.2.1).comp continuous_real_toNNReal
  have hU0 : pieceDrv D 0 = 0 := by
    show D.1 (min (((0 : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) D.2).toNNReal = 0
    rw [Real.toNNReal_zero, CounterflowRange.stopped_eq_of_lt (W := D.1) (t := 0) (by simp)]
    exact hP.1
  have hNRr : ∀ v ∈ Ioc (0 : ℝ) D.2.toNNReal, αr v ≠ 0 := fun v hv => by
    rw [hαeq v ⟨hv.1.le, hv.2⟩]
    refine hNR' v.toNNReal (Real.toNNReal_pos.2 hv.1) ?_
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hv.1.le]
    exact hv.2
  exact ⟨hfin, hS0, hUc, hU0, hchart, hq, hq0, αr, hαr, hαeq, hNRr, hret⟩

end Geometry

/-! ### Almost surely in Proposition BW1's setting -/

section Ae

universe u

/-- The first state of BW1's program is the launch of the first piece from the root. -/
theorem run_one_eq_launch (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (gw2 : Bool) (θ : ℝ) (t : ℝ≥0∞)
    (rest : List Instr) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ExplState.run κ b jumps ⟨0, gw2, Sum.inl (θ, t) :: rest⟩ D 1 =
      ExplState.launch (ExplState.init 0) 0 (D 0) θ t := rfl

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {θ : ℝ} {t : ℝ≥0∞}
  {gw2 : Bool} {rest : List Instr} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The hypotheses of `bw1_piece_geometry` hold almost surely** for the first piece of a staged history from the root
(`0 < κ < 4`): the piece is regular up to its stop (Theorem 1.3 for the trace, `GW1P.ae_pieceRegular_first`), and no
generating trace of it returns to `0` before the lifetime (Aux. lemma 25,
`Q3Kernel.ae_trace_ne_zero_of_isFlowLineDriver`; the first piece is a flow line of `h` under `P`,
`IsStagedHistory.isFlowLineDriver_first`). -/
theorem ae_bw1_piece_hyps (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hS : IsStagedHistory κ b jumps P h ⟨0, gw2, Sum.inl (θ, t) :: rest⟩ E) :
    ∀ᵐ ω ∂P, GW1P.PieceRegular (E 0 ω).1 (min t (E 0 ω).2) ∧
      ∀ α : ℝ≥0 → ℂ, IsGeneratingTrace (E 0 ω).1 (E 0 ω).2 α →
        ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < (E 0 ω).2 → α v ≠ 0 := by
  have hF := hS.isFlowLineDriver_first hκ hb hh rfl rfl
  have hreg := GW1P.ae_pieceRegular_first h13 hκ hb hh hS rfl rfl
  have ht : instrTime (⟨0, gw2, Sum.inl (θ, t) :: rest⟩ : ExplSpec) 0 = t := by simp [instrTime]
  rw [ht] at hreg
  filter_upwards [hreg, Supp8.Q3Kernel.ae_trace_ne_zero_of_isFlowLineDriver hκ hκ4 hF] with ω h1 h2
  exact ⟨h1, fun α hα v hv hvζ => h2 α hα v hv hvζ⟩

/-- **Proposition BW1's relative configuration up to the words, almost surely** (`0 < κ < 4`; the BW1 analogue of
`Q3Kernel.ae_exists_isRelConfigOff_gb6`). For the first piece of a staged history from the root and a continuous
counterflow driver `W` from `0` with complete generating traces `γ`, almost surely on the event that the piece ends at
a threshold on the side `r`: the piece has a generating trace `α` ending at the state's point `q ≠ 0`; the inverse of
the state's chart `g_A − W` is the inverse Loewner map of the stopped driver `U = pieceDrv (E 0 ω)` at the lifetime
`ζ`; and for all counterflow times `0 < t' < t₁` before the first contact of the physical counterflow with `α([0, ζ])`
there is a relative chain `(Wr, ηr)` at `u = a(t') > 0` such that any words and means satisfying the word clauses and
the candidate formula form an `IsRelConfigOff` with the retained chart of the completed piece. -/
theorem ae_exists_isRelConfigOff_bw1 (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hS : IsStagedHistory κ b jumps P h ⟨0, gw2, Sum.inl (θ, t) :: rest⟩ E) {W : ℝ≥0 → Ω → ℝ}
    {γ : Ω → ℝ≥0 → ℂ}
    (hW : ∀ᵐ ω ∂P, Continuous (fun s => W s ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (fun s => W s ω) ⊤ (γ ω)) :
    ∀ᵐ ω ∂P, ∀ r : Bool,
      BW1.EndsAtThresholdSide (ExplState.run κ b jumps ⟨0, gw2, Sum.inl (θ, t) :: rest⟩ (fun j => E j ω) 1) r →
      ∃ α : ℝ≥0 → ℂ, IsGeneratingTrace (E 0 ω).1 (min t (E 0 ω).2) α ∧
        α (E 0 ω).2.toNNReal =
          (BW1.statePoint (ExplState.run κ b jumps ⟨0, gw2, Sum.inl (θ, t) :: rest⟩ (fun j => E j ω) 1) : ℂ) ∧
        BW1.statePoint (ExplState.run κ b jumps ⟨0, gw2, Sum.inl (θ, t) :: rest⟩ (fun j => E j ω) 1) ≠ 0 ∧
        (BW1.stateChart (ExplState.run κ b jumps ⟨0, gw2, Sum.inl (θ, t) :: rest⟩ (fun j => E j ω) 1)).2.1 =
          fwdMapInv (pieceDrv (E 0 ω)) ((E 0 ω).2.toNNReal : ℝ) ∧
        ∀ t' t₁ : ℝ≥0, 0 < t' → t' < t₁ →
          (t₁ : ℝ≥0∞) < firstContactTime (fun s => sphereInv (γ ω s : OnePoint ℂ))
            ((fun s => (α s : OnePoint ℂ)) '' Icc 0 (E 0 ω).2.toNNReal) →
          ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ), Continuous Wr ∧ Wr 0 = 0 ∧ IsLoewnerTrace Wr ηr ∧
            0 < relClock (pieceDrv (E 0 ω)) (E 0 ω).2.toNNReal (fun x : ℝ => W x.toNNReal ω) t' ∧
            relMap (pieceDrv (E 0 ω)) (E 0 ω).2.toNNReal '' fwdHull (fun x : ℝ => W x.toNNReal ω) t' =
              fwdHull Wr (relClock (pieceDrv (E 0 ω)) (E 0 ω).2.toNNReal (fun x : ℝ => W x.toNNReal ω) t') ∧
            ∀ (χ lam : ℝ) (β₀ βE βu : ℝ → ℝ) (S₀ SE Su : Finset ℝ) (G₀ GE G v : ℂ → ℝ),
              IsBoundedHarmonicExtension β₀ S₀ G₀ → IsBoundedHarmonicExtension βE SE GE →
              IsBoundedHarmonicExtension βu Su G →
              BHMean.IsSideWord βE SE (fwdMapInv (fun x : ℝ => W x.toNNReal ω) t')
                (fwdHull (fun x : ℝ => W x.toNNReal ω) t') lam →
              BHMean.IsSideWord βu Su
                (fwdMapInv Wr (relClock (pieceDrv (E 0 ω)) (E 0 ω).2.toNNReal (fun x : ℝ => W x.toNNReal ω) t'))
                (fwdHull Wr (relClock (pieceDrv (E 0 ω)) (E 0 ω).2.toNNReal (fun x : ℝ => W x.toNNReal ω) t'))
                lam →
              BHMean.IsFlowedWord βu β₀ Su S₀
                (fwdMapInv Wr (relClock (pieceDrv (E 0 ω)) (E 0 ω).2.toNNReal (fun x : ℝ => W x.toNNReal ω) t'))
                (fwdHull Wr (relClock (pieceDrv (E 0 ω)) (E 0 ω).2.toNNReal (fun x : ℝ => W x.toNNReal ω) t')) →
              (∀ z, v z = G (fwdMap Wr (relClock (pieceDrv (E 0 ω)) (E 0 ω).2.toNNReal
                  (fun x : ℝ => W x.toNNReal ω) t') (relMap (pieceDrv (E 0 ω)) (E 0 ω).2.toNNReal z)) -
                χ * ((logDerivFwd Wr (relClock (pieceDrv (E 0 ω)) (E 0 ω).2.toNNReal
                  (fun x : ℝ => W x.toNNReal ω) t') (relMap (pieceDrv (E 0 ω)) (E 0 ω).2.toNNReal z)).im +
                  (relLog (pieceDrv (E 0 ω)) (E 0 ω).2.toNNReal z).im)) →
              IsRelConfigOff (invHull (pieceDrv (E 0 ω)) (E 0 ω).2.toNNReal)
                (relMap (pieceDrv (E 0 ω)) (E 0 ω).2.toNNReal) (relInv (pieceDrv (E 0 ω)) (E 0 ω).2.toNNReal)
                (relLog (pieceDrv (E 0 ω)) (E 0 ω).2.toNNReal) (relBad (pieceDrv (E 0 ω)) (E 0 ω).2.toNNReal)
                (fun x : ℝ => W x.toNNReal ω) Wr (fun x : ℝ => γ ω x.toNNReal) ηr t'
                (relClock (pieceDrv (E 0 ω)) (E 0 ω).2.toNNReal (fun x : ℝ => W x.toNNReal ω) t')
                χ lam β₀ βE βu S₀ SE Su G₀ GE G v := by
  filter_upwards [ae_bw1_piece_hyps h13 hκ hκ4 hb hh hS, hW] with ω hp hWω r hr
  rw [run_one_eq_launch] at hr ⊢
  obtain ⟨hP, hNRall⟩ := hp
  have hle := le_of_endsAtThresholdSide hr
  obtain ⟨α, hα, -⟩ := hP.2.2
  have hNR : ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < (E 0 ω).2 → α v ≠ 0 :=
    hNRall α (by rwa [min_eq_right hle] at hα)
  obtain ⟨-, hS0, hUc, hU0, hchart, hq, hq0, αr, hαr, hαeq, hNRr, -⟩ := bw1_piece_geometry hP hα hNR hr
  refine ⟨α, hα, hq, hq0, hchart, fun t' t₁ ht0 htt₁ ht₁ => ?_⟩
  have hαg : IsGeneratingTrace (regOf (E 0 ω)).1 ⊤ (fun s : ℝ≥0 => αr s) :=
    IsLoewnerTrace.isGeneratingTrace (w := (regOf (E 0 ω)).1) hαr
  have hwc : Continuous (regOf (E 0 ω)).1 := by
    have hc := hP.2.1
    rw [min_eq_right hle] at hc
    exact CounterflowRange.continuous_stopped hc
  have hw0 : (regOf (E 0 ω)).1 0 = 0 := by
    rw [regOf_fst_of_le (by simp)]
    exact hP.1
  have himg : (fun s : ℝ≥0 => ((αr s : ℂ) : OnePoint ℂ)) '' Icc 0 (E 0 ω).2.toNNReal =
      (fun s => (α s : OnePoint ℂ)) '' Icc 0 (E 0 ω).2.toNNReal := by
    refine Set.image_congr fun s hs => ?_
    rw [hαeq s ⟨s.2, by exact_mod_cast hs.2⟩, Real.toNNReal_coe]
  rw [← himg] at ht₁
  exact exists_isRelConfigOff_close (wα := (regOf (E 0 ω)).1) (Tα := ⊤) (α := fun s : ℝ≥0 => αr s)
    (t₂ := ((E 0 ω).2.toNNReal : ℝ) + 1) hαg hwc.continuousOn hw0 ENNReal.coe_lt_top (by exact_mod_cast hS0)
    hUc hU0 hαr hNRr (by linarith) (fun x _ => rfl) hWω.2.2 hWω.1 hWω.2.1 ht0 htt₁ ht₁

end Ae

end InteractingSLE.Theorem14.BW1Prop
