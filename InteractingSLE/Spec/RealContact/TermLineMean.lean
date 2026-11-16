/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermLineCfg
import InteractingSLE.Spec.Supplement.SB2KqWord
import InteractingSLE.Spec.Supplement.OrdGapFixed
import InteractingSLE.Spec.Supplement.OrdFstShift

/-!
# The line mean at the positive lines

Packet PROVE-RC-TERM, second run (ruling R124). K2's `hmean` equation for the first path against the completed second
path at a physical time `t > 0`:

* `lChart`, `lWord`, `lXL`, `lXR`: the physical chart, the chart word (the stop word of the second record recentred
  at the seed position) and its typed force coordinates;
* **`ae_lineMean_pos`**: for line data at `(t, N)` and a local-set mean `g` of the line set, almost surely on a good
  event of one force type, before the capacity lifetime and for every test off the relative hull,
  `chartTransport lChart 1 (θ₁χ) χ (g + 𝔥₀) = ∫ couplingMean κ W (clock t) (bheProc …)`.

The proof is SB2's line-mean theorem `Theorem14.SB.Om.ae_chartTransport_eq_of_cfg` with the translation stage chart,
the two individual means (`IsLineData.ae_eqOn_retMean`, `ae_eqOn_explMean`), the configuration record at each sample
(`Term.exists_isCfgDriver_sample`; the tip of the first path at the fixed time is interior,
`RLC.OrdLate.ae_mem_H_at`) and the driver congruence of the coupling mean.

R48-neutral (uses Lemma 7.5 through the line data only).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.RealContact

namespace Term

open Restart Restart.RetAux79 Restart.DomainMarkov Supp7 Sec7 Sec7.Lemma76F Sec7.PocketTraversal
  Exist.Staged Exist.StagedLaw Sec2.Assembly LocalSets WholeField RLC.AStopProc
open Theorem14 Theorem14.SB
open Exist.StagedLaw.BoundaryWord (shiftW)

section Defs

variable {Ω : Type*}

/-- The physical chart of the second record at own time `N`, recentred at the seed position. -/
def lChart (x₁ x₂ : ℝ) (N : ℝ≥0) (E₂ : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) : Chart :=
  physChart x₂ (pRec N E₂ ω) (pSeed N E₂ x₁ x₂ ω)

/-- The chart word: the stop word of the second record recentred at the seed position. -/
def lWord (κ θ₂ : ℝ) (c₂ : BoundaryWord) (N : ℝ≥0) (E₂ : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (x₁ x₂ : ℝ) (ω : Ω) :
    BoundaryWord :=
  shiftW (pSeed N E₂ x₁ x₂ ω) (pWord κ θ₂ c₂ N E₂ ω)

/-- The typed left force coordinates of the chart word. -/
def lXL (κ θ₁ θ₂ : ℝ) (c₂ : BoundaryWord) (N : ℝ≥0) (E₂ : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (x₁ x₂ : ℝ)
    (a : ForceWordType) (ω : Ω) : Fin a.nL → ℝ :=
  FCDet.typeXL κ θ₁ a.nL a.nR a.rhoL a.rhoR (lWord κ θ₂ c₂ N E₂ x₁ x₂ ω)

/-- The typed right force coordinates of the chart word. -/
def lXR (κ θ₁ θ₂ : ℝ) (c₂ : BoundaryWord) (N : ℝ≥0) (E₂ : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (x₁ x₂ : ℝ)
    (a : ForceWordType) (ω : Ω) : Fin a.nR → ℝ :=
  FCDet.typeXR κ θ₁ a.nL a.nR a.rhoL a.rhoR (lWord κ θ₂ c₂ N E₂ x₁ x₂ ω)

theorem isConformal_lChart (x₁ x₂ : ℝ) (N : ℝ≥0) (E₂ : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) :
    (lChart x₁ x₂ N E₂ ω).IsConformal :=
  isConformal_physChart _ _ _

theorem lXL_nonpos (κ θ₁ θ₂ : ℝ) (c₂ : BoundaryWord) (N : ℝ≥0) (E₂ : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (x₁ x₂ : ℝ)
    (a : ForceWordType) (ω : Ω) (i : Fin a.nL) : lXL κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a ω i ≤ 0 :=
  (FCDet.isOrderedForceWord_typeXL (κ := κ) (θ := θ₁) (nL := a.nL) (nR := a.nR) (ρL := a.rhoL)
    (ρR := a.rhoR) (lWord κ θ₂ c₂ N E₂ x₁ x₂ ω)).2.1 i

theorem lXR_nonneg (κ θ₁ θ₂ : ℝ) (c₂ : BoundaryWord) (N : ℝ≥0) (E₂ : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (x₁ x₂ : ℝ)
    (a : ForceWordType) (ω : Ω) (j : Fin a.nR) : 0 ≤ lXR κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a ω j :=
  (FCDet.isOrderedForceWord_typeXL (κ := κ) (θ := θ₁) (nL := a.nL) (nR := a.nR) (ρL := a.rhoL)
    (ρR := a.rhoR) (lWord κ θ₂ c₂ N E₂ x₁ x₂ ω)).2.2.2 j

end Defs

section Mean

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {κ : ℝ}
  {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}

/-- **The line mean at a positive line** (see the module docstring). -/
theorem ae_lineMean_pos (hκ : 0 < κ) (hκ4 : κ < 4) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {c₁ c₂ : BoundaryWord} {E₁ E₂ : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE₁m : Measurable E₁) (hreg₁ : ∀ ω, IsRegularDriver (E₁ ω)) (hE₁2 : ∀ ω, (E₁ ω).2 = ζ₁ ω)
    (hfl₁ : IsFlowLineDriver κ c₁.fn c₁.jumps θ₁ P (fun ω => Exist.flowField x₁ 0 (h ω))
      (fun s ω => (E₁ ω).1 s) (fun ω => (E₁ ω).2))
    (htrace₁ : ∀ᵐ ω ∂P, IsGeneratingTrace (E₁ ω).1 (ζ₁ ω) (fun s => η₁ ω s - x₁))
    (hE₂m : Measurable E₂) (hreg₂ : ∀ ω, IsRegularDriver (E₂ ω)) (hE₂2 : ∀ ω, (E₂ ω).2 = ζ₂ ω)
    (hfl₂ : IsFlowLineDriver κ c₂.fn c₂.jumps θ₂ P (fun ω => Exist.flowField x₂ 0 (h ω))
      (fun s ω => (E₂ ω).1 s) (fun ω => (E₂ ω).2))
    (htrace₂ : ∀ᵐ ω ∂P, IsGeneratingTrace (E₂ ω).1 (ζ₂ ω) (fun s => η₂ ω s - x₂))
    {N : ℝ≥0} {η₁' ηb₂ : Ω → ℝ≥0 → ℂ}
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    (hag₂ : ∀ᵐ ω ∂P, ∀ s, ηb₂ ω s = η₂ ω (capTime (capR 0 N) (ζ₂ ω) s))
    {M : Set Ω} (hMg : ∀ ω ∈ M, IsTermGood N E₂ ηb₂ η₁' ζ₁ x₁ x₂ ω)
    {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous (W · ω)) (hW0 : ∀ ω, W 0 ω = 0)
    (hgen : ∀ ω ∈ M, IsGeneratingTrace (W · ω)
      (aLife (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂) ω)
      (aPath (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂) ω))
    (a : ForceWordType)
    (htype : ∀ ω ∈ M, lWord κ θ₂ c₂ N E₂ x₁ x₂ ω ∈ FCDet.typeSet κ θ₁ a.nL a.nR a.rhoL a.rhoR)
    {t : ℝ≥0} (ht0 : 0 < t) {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ} (d : IsLineData P h u₀ η₁ η₂ ζ₁ ζ₂ x₁ x₂ t N ηc₁ ηc₂)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean (lineSet ηc₁ ηc₂ t N) (centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ω ∈ M → (aClock (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) t ω : ℝ≥0∞) <
        aLife (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂) ω →
      ∀ φ : TestOn upperHalfPlaneOpens,
        Disjoint (tsupport φ)
          (fwdHull (fun s : ℝ => W s.toNNReal ω) (aClock (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) t ω)) →
        Chart.chartTransport (isConformal_lChart x₁ x₂ N E₂ ω) 1 (θ₁ * chiC κ) (chiC κ)
            (g ω + smoothDist upperHalfPlaneOpens u₀) φ =
          ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) (aClock (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) t ω)
            (bheProc κ a.rhoL a.rhoR W (geomLW W (lXL κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a))
              (geomRW W (lXR κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a)) ω (aClock (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) t ω)) z *
              φ z := by
  classical
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hA₁m : Measurable[mΩ, hittingSigma] (fillOf ηc₂ N) :=
    d.measurable_ret.mono (retSigma76_le P η₁ η₂ ζ₁ ζ₂ t N) le_rfl
  have hA₂m : Measurable[mΩ, hittingSigma] (fillOf ηc₁ t) :=
    d.measurable_expl.mono (retSigma76_le P η₁ η₂ ζ₁ ζ₂ t N) le_rfl
  obtain ⟨g₁, hg₁⟩ := IsLocalSet.exists_isLocalSetMean hh0 hA₁m (d.isLocalSet_ret hh0)
  obtain ⟨g₂, hg₂⟩ := IsLocalSet.exists_isLocalSetMean hh0 hA₂m (d.isLocalSet_expl hh0)
  -- opaque names for the clock and the union extension
  obtain ⟨Q, hQ⟩ : ∃ Q : Ω → ℝ≥0, Q = fun ω => aClock (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) t ω := ⟨_, rfl⟩
  obtain ⟨Gu, hGudef⟩ : ∃ Gu : Ω → ℂ → ℝ, Gu = fun ω =>
      bheProc κ a.rhoL a.rhoR W (geomLW W (lXL κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a))
        (geomRW W (lXR κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a)) ω (Q ω) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : Set Ω, D = {ω | ω ∈ M ∧ (Q ω : ℝ≥0∞) <
      aLife (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂) ω} := ⟨_, rfl⟩
  have hQco : ∀ ω ∈ M, ((Q ω : ℝ≥0) : ℝ) = chartClock (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂ ω) t := fun ω hω => by
    rw [hQ]
    exact (hMg ω hω).isAGood.coe_aClock t
  -- the stage pull-back
  have hpb : ∀ᵐ ω ∂P, ω ∈ D → ∃ gb : ℂ → ℂ, Ln.IsStagePullback (Chart.id.recenter x₁) gb (fillOf ηc₂ N ω)
      (fillOf ηc₁ t ω) {z | (Chart.id.recenter x₁).2.1 z ∈ fillOf ηc₂ N ω}
      (fwdHull (rdrv (recOf (t : ℝ≥0∞) (E₁ ω))) (rtime (recOf (t : ℝ≥0∞) (E₁ ω)))) := by
    filter_upwards [ae_isDrvGood_of_isFlowLineDriver hκ (t : ℝ≥0∞) hreg₁ hfl₁, htrace₁, d.ae₁]
      with ω hgω htω haω _
    have hgood := hgω (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))
    have htω' : IsGeneratingTrace (E₁ ω).1 (E₁ ω).2 (fun s => η₁ ω s - x₁) := by rw [hE₁2]; exact htω
    have haω' : ∀ s, ηc₁ ω s = η₁ ω (capTime (capR t N) (E₁ ω).2 s) := fun s => by rw [hE₁2]; exact haω s
    have himg := image_add_fwdHull_recOf (hreg₁ ω) hgood htω' (lt_capR_left t N) haω'
    have hsp := isStagePullback_translate x₁ (fillOf ηc₂ N ω)
      (fwdHull (rdrv (recOf (t : ℝ≥0∞) (E₁ ω))) (rtime (recOf (t : ℝ≥0∞) (E₁ ω))))
    rw [himg] at hsp
    exact ⟨_, hsp⟩
  -- the physical chart
  have hrecm : Measurable (pRec N E₂) := measurable_recOf hE₂m hreg₂ _
  obtain ⟨-, hΦℓ, -⟩ := isMeasChart_physChart (m := mΩ) hrecm (measurable_pSeed hrecm x₁ x₂) x₂
  have hdom : ∀ᵐ ω ∂P, ω ∈ D → ((lChart x₁ x₂ N E₂ ω).dom : Set ℂ) = H \ fillOf ηc₂ N ω := by
    filter_upwards [ae_isDrvGood_of_isFlowLineDriver hκ (N : ℝ≥0∞) hreg₂ hfl₂, htrace₂, d.ae₂]
      with ω hgω htω haω _
    have hgood := hgω (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))
    have htω' : IsGeneratingTrace (E₂ ω).1 (E₂ ω).2 (fun s => η₂ ω s - x₂) := by rw [hE₂2]; exact htω
    have haω' : ∀ s, ηc₂ ω s = η₂ ω (capTime (capR t N) (E₂ ω).2 s) := fun s => by rw [hE₂2]; exact haω s
    have himg := image_add_fwdHull_recOf (hreg₂ ω) hgood htω' (lt_capR_right t N) haω'
    show ((physChart x₂ (pRec N E₂ ω) (pSeed N E₂ x₁ x₂ ω)).dom : Set ℂ) = _
    rw [coe_dom_physChart, image_add_real_H_diff]
    exact congrArg (fun S => H \ S) himg
  -- the configuration records
  have hex : ∀ᵐ ω ∂P, ω ∈ D → ∃ W' : ℝ → ℝ, IsCfgDriver κ θ₁ (Chart.id.recenter x₁) (lChart x₁ x₂ N E₂ ω)
      (fillOf ηc₂ N ω) (rdrv (recOf (t : ℝ≥0∞) (E₁ ω))) (rtime (recOf (t : ℝ≥0∞) (E₁ ω)))
      (fun r : ℝ => W r.toNNReal ω) (Q ω) (lWord κ θ₂ c₂ N E₂ x₁ x₂ ω)
      (stopWord κ (c₁, θ₁, recOf (t : ℝ≥0∞) (E₁ ω))).mean (Gu ω) W' := by
    filter_upwards [ae_isDrvGood_of_isFlowLineDriver hκ (t : ℝ≥0∞) hreg₁ hfl₁, htrace₁, ha₁,
      RLC.OrdLate.ae_mem_H_at hκ hκ4.le hη₁ t ht0, hag₂, d.ae₂] with ω hgω htω e₁ω htipω eb₂ ec₂ hωD
    rw [hD] at hωD
    obtain ⟨hωM, hlt⟩ := hωD
    have hG := hMg ω hωM
    have hgoodA := hG.isAGood
    have hlt' : (aClock (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) t ω : ℝ≥0∞) <
        aLife (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂) ω := by
      rw [hQ] at hlt
      exact hlt
    have htL : (t : ℝ≥0∞) < pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂ ω := hgoodA.aClock_lt_aLife_iff.1 hlt'
    have htζ : (t : ℝ≥0∞) < ζ₁ ω := lt_of_lt_of_le htL (physStop_le _ _ _ _ _)
    have hft := FCDet.isFlowType_of_mem_typeSet (htype ω hωM)
    have hA₁ : fillOf ηc₂ N ω =
        fillH ((fun s : ℝ≥0 => pRho₂ ηb₂ x₂ ω (s : ℝ) + (x₂ : ℂ)) '' Icc 0 (pT N E₂ ω)) := by
      rw [hG.image_ret (hE₂2 ω) eb₂ ec₂]
      rfl
    have hres := exists_isCfgDriver_sample hκ hG ht0 htL (hreg₁ ω) (hE₁2 ω)
      (hgω (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)))
      (show IsGeneratingTrace (E₁ ω).1 (E₁ ω).2 (fun s => η₁ ω s - x₁) by rw [hE₁2]; exact htω) e₁ω
      (htipω htζ) (hWc ω) (hW0 ω) (hgen ω hωM) hA₁ (c₁ := c₁) (hft : FCDet.IsFlowType κ θ₁
        (shiftW (pSeed N E₂ x₁ x₂ ω) (pWord κ θ₂ c₂ N E₂ ω)) (lXL κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a ω)
        (lXR κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a ω) a.rhoL a.rhoR) (lXL_nonpos κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a ω)
      (lXR_nonneg κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a ω) (Gu := Gu ω) (fun W' hW'c hW'0 hag G hG' => by
        rw [← hQco ω hωM] at hag hG'
        rw [hGudef]
        exact Lv.eqOn_bheProc_of_flowedData a.rhoL a.rhoR hWc hW0
          (xL := lXL κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a) (xR := lXR κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a)
          (lXL_nonpos κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a ω) (lXR_nonneg κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a ω) hW'c hW'0 hag hG')
    rw [hQco ω hωM]
    exact hres
  obtain ⟨Wc, hWcdef⟩ : ∃ Wc : Ω → ℝ → ℝ, Wc = fun ω => cfgDriverOf κ θ₁ (Chart.id.recenter x₁)
      (lChart x₁ x₂ N E₂ ω) (fillOf ηc₂ N ω) (rdrv (recOf (t : ℝ≥0∞) (E₁ ω)))
      (rtime (recOf (t : ℝ≥0∞) (E₁ ω))) (fun r : ℝ => W r.toNNReal ω) (Q ω) (lWord κ θ₂ c₂ N E₂ x₁ x₂ ω)
      (stopWord κ (c₁, θ₁, recOf (t : ℝ≥0∞) (E₁ ω))).mean (Gu ω) := ⟨_, rfl⟩
  have hdrv : ∀ᵐ ω ∂P, ω ∈ D → IsCfgDriver κ θ₁ (Chart.id.recenter x₁) (lChart x₁ x₂ N E₂ ω)
      (fillOf ηc₂ N ω) (rdrv (recOf (t : ℝ≥0∞) (E₁ ω))) (rtime (recOf (t : ℝ≥0∞) (E₁ ω)))
      (fun r : ℝ => W r.toNNReal ω) (Q ω) (lWord κ θ₂ c₂ N E₂ x₁ x₂ ω)
      (stopWord κ (c₁, θ₁, recOf (t : ℝ≥0∞) (E₁ ω))).mean (Gu ω) (Wc ω) := by
    filter_upwards [hex] with ω hω hωD
    rw [hWcdef]
    exact isCfgDriver_cfgDriverOf (hω hωD)
  have hrec : ∀ᵐ ω ∂P, ω ∈ D → ∃ dd, Om.IsCfg κ θ₁ (Chart.id.recenter x₁) (lChart x₁ x₂ N E₂ ω)
      (fillOf ηc₂ N ω) (rdrv (recOf (t : ℝ≥0∞) (E₁ ω))) (rtime (recOf (t : ℝ≥0∞) (E₁ ω))) (Wc ω)
      ((Q ω : ℝ≥0) : ℝ) (lWord κ θ₂ c₂ N E₂ x₁ x₂ ω) (stopWord κ (c₁, θ₁, recOf (t : ℝ≥0∞) (E₁ ω))).mean
      (Gu ω) dd := by
    filter_upwards [hdrv] with ω hω hωD
    exact (hω hωD).2.2.2.2
  -- the two individual means
  have hind₁ : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ fillOf ηc₂ N ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ fillOf ηc₂ N ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
      EqOn (fun z => w₁ z + u₀ z)
        (fun z => (lWord κ θ₂ c₂ N E₂ x₁ x₂ ω).mean ((lChart x₁ x₂ N E₂ ω).1 z) -
          chiC κ * (lChart x₁ x₂ N E₂ ω).2.2 z) (H \ fillOf ηc₂ N ω) := by
    filter_upwards [d.ae_eqOn_retMean hκ hh hu₀ hE₂m hreg₂ hE₂2 hfl₂ htrace₂ hg₁] with ω hω _ w₁ hw₁ hrep z hz
    have e := hω w₁ hw₁ hrep hz
    show w₁ z + u₀ z = (shiftW (pSeed N E₂ x₁ x₂ ω) (stopWord κ (c₂, θ₂, recOf (N : ℝ≥0∞) (E₂ ω)))).mean
        ((physChart x₂ (recOf (N : ℝ≥0∞) (E₂ ω)) (pSeed N E₂ x₁ x₂ ω)).1 z) -
      chiC κ * (physChart x₂ (recOf (N : ℝ≥0∞) (E₂ ω)) (pSeed N E₂ x₁ x₂ ω)).2.2 z
    rw [e, physChart_fst, physChart_lift, RLC.OrdDet.mean_shiftW, sub_add_cancel]
    unfold prefixMeanFn
    ring
  have hind₂ : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₂ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₂ (H \ fillOf ηc₁ t ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ fillOf ηc₁ t ω → g₂ ω φ = ∫ z, w₂ z * φ z) →
      EqOn (fun z => w₂ z + u₀ z)
        (fun z => (stopWord κ (c₁, θ₁, recOf (t : ℝ≥0∞) (E₁ ω))).mean
            (fwdMap (rdrv (recOf (t : ℝ≥0∞) (E₁ ω))) (rtime (recOf (t : ℝ≥0∞) (E₁ ω)))
              ((Chart.id.recenter x₁).1 z)) -
          chiC κ * ((logDerivFwd (rdrv (recOf (t : ℝ≥0∞) (E₁ ω))) (rtime (recOf (t : ℝ≥0∞) (E₁ ω)))
            ((Chart.id.recenter x₁).1 z)).im + (Chart.id.recenter x₁).2.2 z)) (H \ fillOf ηc₁ t ω) := by
    filter_upwards [d.ae_eqOn_explMean hκ hh hu₀ hE₁m hreg₁ hE₁2 hfl₁ htrace₁ hg₂] with ω hω _ w₂ hw₂ hrep z hz
    have e := hω w₂ hw₂ hrep hz
    show w₂ z + u₀ z = (stopWord κ (c₁, θ₁, recOf (t : ℝ≥0∞) (E₁ ω))).mean
        (fwdMap (rdrv (recOf (t : ℝ≥0∞) (E₁ ω))) (rtime (recOf (t : ℝ≥0∞) (E₁ ω))) (z - (x₁ : ℂ))) -
      chiC κ * ((logDerivFwd (rdrv (recOf (t : ℝ≥0∞) (E₁ ω))) (rtime (recOf (t : ℝ≥0∞) (E₁ ω)))
        (z - (x₁ : ℂ))).im + 0)
    rw [e]
    unfold prefixMeanFn
    ring
  -- the union theorem
  have hmain := Om.ae_chartTransport_eq_of_cfg (κ := κ) (ψ := θ₁) hh0 hu₀.1 hu₀.2.1 hA₁m hA₂m d.comap_ret_le
    (d.isLocalSet_ret hh0) (d.isLocalSet_expl hh0) (d.isLocalSet_lineSet hh0)
    (Eventually.of_forall d.unbounded_ret) (Eventually.of_forall d.unbounded_expl) hg hg₁ hg₂
    (c := fun _ => Chart.id.recenter x₁) (wB := fun ω => rdrv (recOf (t : ℝ≥0∞) (E₁ ω)))
    (sB := fun ω => rtime (recOf (t : ℝ≥0∞) (E₁ ω))) (D := D) hpb (Φ := lChart x₁ x₂ N E₂)
    (isConformal_lChart x₁ x₂ N E₂) hΦℓ hdom (W := Wc) (u := fun ω => ((Q ω : ℝ≥0) : ℝ))
    (β₁ := lWord κ θ₂ c₂ N E₂ x₁ x₂)
    (GE₀ := fun ω => (stopWord κ (c₁, θ₁, recOf (t : ℝ≥0∞) (E₁ ω))).mean) (Gu := Gu) hrec hind₁ hind₂
  filter_upwards [hmain, hdrv] with ω hω hdω hωM hlt φ hφ
  have hωD : ω ∈ D := by
    rw [hD, hQ]
    exact ⟨hωM, hlt⟩
  obtain ⟨-, -, hag, hhull, -⟩ := hdω hωD
  have hQω : Q ω = aClock (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) t ω := by rw [hQ]
  rw [← hQω] at hφ ⊢
  have hφ' : Disjoint (tsupport φ) (fwdHull (Wc ω) ((Q ω : ℝ≥0) : ℝ)) := by rw [hhull]; exact hφ
  rw [hω hωD φ hφ']
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show couplingMean κ (Wc ω) ((Q ω : ℝ≥0) : ℝ) (Gu ω) z * φ z = _
  rw [Sec7.Lemma71B.couplingMean_congr (Q ω).coe_nonneg hag κ _ z, hGudef]

end Mean

end Term

end InteractingSLE.RealContact
