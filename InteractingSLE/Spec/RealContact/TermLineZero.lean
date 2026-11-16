/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermLineMean
import InteractingSLE.Spec.Restart.RetAux79Word
import InteractingSLE.Spec.Restart.R1MeanChart

/-!
# The line mean at the zero line

Packet PROVE-RC-TERM, second run (ruling R124). K2's `hmean` equation for the first path against the completed second
path at the physical time `0`:

* `IsLineData.fillOf_expl_zero`, `IsLineData.lineSet_zero`: at `t = 0` the explored filled prefix is empty (the first
  version starts on the real line), so the line set is the retained filled prefix;
* `bheProc_zero_eqOn_mean`: for a flow type of a sorted word, the typed coupling data at time `0` are the word's mean
  plus `ψχ`;
* **`ae_lineMean_zero`**: for line data at `(0, N)` and a local-set mean `g` of the line set, almost surely on an event
  of one force type and for every test,
  `chartTransport lChart 1 (θ₁χ) χ (g + 𝔥₀) = ∫ couplingMean κ W (clock 0) (bheProc … (clock 0))`.

The proof reads the mean of the retained filled prefix (`IsLineData.ae_eqOn_retMean`) in the physical chart
(`Restart.chartTransport_eq_integral_of_eq_integral`) and applies the time-zero identity
`RetAux79.chartTransport_eq_integral_couplingMean_zero`.

R48-neutral.
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
open Exist.StagedLaw.BoundaryWord (shiftW isSorted_shiftW)

section Zero

variable {Ω : Type*}

/-- **For a flow type of a sorted word, the typed coupling data at time `0` are the word's mean plus `ψχ`.** -/
theorem bheProc_zero_eqOn_mean {κ ψ : ℝ} (hκ : 0 < κ) {β : BoundaryWord} (hs : β.IsSorted) {nL nR : ℕ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {ω : Ω}
    (hft : FCDet.IsFlowType κ ψ β (xL ω) (xR ω) ρL ρR) (hxL : ∀ i, xL ω i ≤ 0) (hxR : ∀ j, 0 ≤ xR ω j) :
    EqOn (bheProc κ ρL ρR W (geomLW W xL) (geomRW W xR) ω 0) (fun z => β.mean z + ψ * chiC κ) H := by
  have hL0 : ∀ i, geomLW W xL i 0 ω = xL ω i := fun i => geomLW_zero hWc hW0 (hxL i)
  have hR0 : ∀ j, geomRW W xR j 0 ω = xR ω j := fun j => geomRW_zero hWc hW0 (hxR j)
  have hu := Restart.DomainMarkov.isBoundedHarmonicExtension_bheProc (κ := κ) (ρL := ρL) (ρR := ρR) (W := W)
    (VL := geomLW W xL) (VR := geomRW W xR) ω 0
  simp only [hL0, hR0, hW0, sub_zero] at hu
  exact eqOn_mean_of_isFlowType hκ hs hft hu

end Zero

section Mean

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {κ : ℝ}
  {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {N : ℝ≥0} {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ}

omit [IsProbabilityMeasure P] in
/-- At the zero line the explored filled prefix is empty. -/
theorem IsLineData.fillOf_expl_zero (d : IsLineData P h u₀ η₁ η₂ ζ₁ ζ₂ x₁ x₂ 0 N ηc₁ ηc₂) (ω : Ω) :
    fillOf ηc₁ 0 ω = ∅ := by
  unfold fillOf
  refine YuanCharacterisation.fillH_eq_empty_of_subset ?_
  rintro _ ⟨s, hs, rfl⟩
  have hs0 : s = 0 := le_antisymm hs.2 hs.1
  show (ηc₁ ω s).im ≤ 0
  rw [hs0]
  exact d.im_zero₁ ω

omit [IsProbabilityMeasure P] in
/-- At the zero line the line set is the retained filled prefix. -/
theorem IsLineData.lineSet_zero (d : IsLineData P h u₀ η₁ η₂ ζ₁ ζ₂ x₁ x₂ 0 N ηc₁ ηc₂) :
    lineSet ηc₁ ηc₂ 0 N = fillOf ηc₂ N := by
  funext ω
  unfold lineSet
  rw [d.fillOf_expl_zero ω, union_empty]

/-- **The line mean at the zero line** (see the module docstring). -/
theorem ae_lineMean_zero (hκ : 0 < κ) (hh : IsGFFWithBoundaryData P h b jumps)
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {c₂ : BoundaryWord} {E₂ : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE₂m : Measurable E₂) (hreg₂ : ∀ ω, IsRegularDriver (E₂ ω)) (hE₂2 : ∀ ω, (E₂ ω).2 = ζ₂ ω)
    (hfl₂ : IsFlowLineDriver κ c₂.fn c₂.jumps θ₂ P (fun ω => Exist.flowField x₂ 0 (h ω))
      (fun s ω => (E₂ ω).1 s) (fun ω => (E₂ ω).2))
    (htrace₂ : ∀ᵐ ω ∂P, IsGeneratingTrace (E₂ ω).1 (ζ₂ ω) (fun s => η₂ ω s - x₂))
    (Γ : Ω → ℝ≥0 → ℂ) {M : Set Ω}
    {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous (W · ω)) (hW0 : ∀ ω, W 0 ω = 0)
    (a : ForceWordType)
    (htype : ∀ ω ∈ M, lWord κ θ₂ c₂ N E₂ x₁ x₂ ω ∈ FCDet.typeSet κ θ₁ a.nL a.nR a.rhoL a.rhoR)
    (d : IsLineData P h u₀ η₁ η₂ ζ₁ ζ₂ x₁ x₂ 0 N ηc₁ ηc₂)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean (lineSet ηc₁ ηc₂ 0 N) (centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ω ∈ M → ∀ φ : TestOn upperHalfPlaneOpens,
      Chart.chartTransport (isConformal_lChart x₁ x₂ N E₂ ω) 1 (θ₁ * chiC κ) (chiC κ)
          (g ω + smoothDist upperHalfPlaneOpens u₀) φ =
        ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) (aClock Γ 0 ω)
          (bheProc κ a.rhoL a.rhoR W (geomLW W (lXL κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a))
            (geomRW W (lXR κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a)) ω (aClock Γ 0 ω)) z * φ z := by
  classical
  rw [d.lineSet_zero] at hg
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  have hrecm : Measurable (pRec N E₂) := measurable_recOf hE₂m hreg₂ _
  obtain ⟨-, hΦℓ, -⟩ := isMeasChart_physChart (m := mΩ) hrecm (measurable_pSeed hrecm x₁ x₂) x₂
  have hdom : ∀ᵐ ω ∂P, ((lChart x₁ x₂ N E₂ ω).dom : Set ℂ) = H \ fillOf ηc₂ N ω := by
    filter_upwards [ae_isDrvGood_of_isFlowLineDriver hκ (N : ℝ≥0∞) hreg₂ hfl₂, htrace₂, d.ae₂]
      with ω hgω htω haω
    have hgood := hgω (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))
    have htω' : IsGeneratingTrace (E₂ ω).1 (E₂ ω).2 (fun s => η₂ ω s - x₂) := by rw [hE₂2]; exact htω
    have haω' : ∀ s, ηc₂ ω s = η₂ ω (capTime (capR 0 N) (E₂ ω).2 s) := fun s => by rw [hE₂2]; exact haω s
    have himg := image_add_fwdHull_recOf (hreg₂ ω) hgood htω' (lt_capR_right 0 N) haω'
    show ((physChart x₂ (pRec N E₂ ω) (pSeed N E₂ x₁ x₂ ω)).dom : Set ℂ) = _
    rw [coe_dom_physChart, image_add_real_H_diff]
    exact congrArg (fun S => H \ S) himg
  filter_upwards [hdom, hg.2.1, d.ae_eqOn_retMean hκ hh hu₀ hE₂m hreg₂ hE₂2 hfl₂ htrace₂ hg]
    with ω hdω hharm hmean hωM φ
  obtain ⟨v, hv, hrep⟩ := hharm
  have hveq := hmean v hv hrep
  have hvc : ContinuousOn v (H \ fillOf ηc₂ N ω) := fun z hz => (hv z hz).1.continuousAt.continuousWithinAt
  have hT : ∀ φ' : TestOn upperHalfPlaneOpens, tsupport φ' ⊆ (lChart x₁ x₂ N E₂ ω).dom →
      (g ω + smoothDist upperHalfPlaneOpens u₀) φ' =
        ∫ z, ((lWord κ θ₂ c₂ N E₂ x₁ x₂ ω).mean ((lChart x₁ x₂ N E₂ ω).1 z) -
          chiC κ * (lChart x₁ x₂ N E₂ ω).2.2 z) * φ' z := by
    intro φ' hφ'
    rw [hdω] at hφ'
    show g ω φ' + smoothDist upperHalfPlaneOpens u₀ φ' = _
    rw [hrep φ' hφ', Coupling.smoothDist_apply_eq hu₀c φ']
    have hi1 : Integrable (fun z => v z * φ' z) := WholeField.integrable_mul_testOn hvc φ' hφ'
    have hi2 := WholeField.integrable_mul_testOn hu₀c φ' φ'.tsupport_subset
    rw [← integral_add hi1 hi2]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ tsupport φ'
    · have e := hveq (hφ' hz)
      show v z * φ' z + u₀ z * φ' z =
        ((shiftW (pSeed N E₂ x₁ x₂ ω) (stopWord κ (c₂, θ₂, recOf (N : ℝ≥0∞) (E₂ ω)))).mean
            ((physChart x₂ (recOf (N : ℝ≥0∞) (E₂ ω)) (pSeed N E₂ x₁ x₂ ω)).1 z) -
          chiC κ * (physChart x₂ (recOf (N : ℝ≥0∞) (E₂ ω)) (pSeed N E₂ x₁ x₂ ω)).2.2 z) * φ' z
      rw [e, physChart_fst, physChart_lift, RLC.OrdDet.mean_shiftW, sub_add_cancel]
      unfold prefixMeanFn
      ring
    · show v z * φ' z + u₀ z * φ' z = _ * φ' z
      rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero, mul_zero, add_zero]
  have hmc : ContinuousOn (lWord κ θ₂ c₂ N E₂ x₁ x₂ ω).mean H := Restart.BoundaryWord.continuousOn_mean _
  have hid := fun φ'' : TestOn upperHalfPlaneOpens =>
    Restart.chartTransport_eq_integral_of_eq_integral (isConformal_lChart x₁ x₂ N E₂ ω) (hΦℓ ω) (chiC κ) hmc hT
      φ''
  have hWc' : Continuous fun s : ℝ => W s.toNNReal ω := (hWc ω).comp continuous_real_toNNReal
  have hW0' : (fun s : ℝ => W s.toNNReal ω) 0 = 0 := by
    show W (0 : ℝ).toNNReal ω = 0
    rw [Real.toNNReal_zero, hW0]
  have hft := FCDet.isFlowType_of_mem_typeSet (htype ω hωM)
  have hu : ∀ z ∈ H, bheProc κ a.rhoL a.rhoR W (geomLW W (lXL κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a))
      (geomRW W (lXR κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a)) ω 0 z =
        (lWord κ θ₂ c₂ N E₂ x₁ x₂ ω).mean z + θ₁ * chiC κ :=
    bheProc_zero_eqOn_mean hκ (isSorted_shiftW (isSorted_stopWord κ _) _) hWc hW0
      (xL := lXL κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a) (xR := lXR κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a) hft
      (lXL_nonpos κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a ω) (lXR_nonneg κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a ω)
  rw [RLC.AStopSafe.aClock_zero, NNReal.coe_zero]
  exact Restart.RetAux79.chartTransport_eq_integral_couplingMean_zero κ (isConformal_lChart x₁ x₂ N E₂ ω)
    ((isConformal_lChart x₁ x₂ N E₂ ω).continuousOn_lift_inv (hΦℓ ω)) hWc' hW0' hmc (θ₁ * chiC κ) hid hu φ

end Mean

end Term

end InteractingSLE.RealContact
