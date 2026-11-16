/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermKernel
import InteractingSLE.Spec.Supplement.AStopSafeLaw
import InteractingSLE.Spec.Supplement.AStopSafeLine
import InteractingSLE.Spec.Restart.RetFinGlue

/-!
# K2's (S) and (L) for the first path in the chart of the completed second path

Packet PROVE-RC-TERM, second run (ruling R124). For the processes of `TermProcMain` (the chart path `pPath`, its
physical stop `pStop`, the capacity-time filtration `aFilt` of `fstPhysFiltration … 0 N`, any continuous driver
from `0` generating `aPath` on the good event `M` of one force type):

* **`hasSafe_term`**: K2's (S) for the typed geometric force coordinates of the chart word `lWord`, and K2's (L),
  for the chart field `chartTransport lChart 1 (θ₁χ) χ h`.

Proof: `hasSafeLaw_of_lineKernel_indicator` and `RetAux79.hasSafeMembers_of_lineLocal_indicator` with the line sets
`B_t = fill(ηc₂[0,N]) ∪ fill(ηc₁[0,t])` of `IsLineData` at every line `(t, N)`, the kernel
`IsLineData.ae_condExp_lineKernel` given `germSigma B_t ⊔ retSigma76 … t N` (the domain `ℍ ∖ B_t` is the chart
image of `ℍ ∖ K̃`, `ae_lineSet_eq`, hence connected), and the line means `ae_lineMean_zero`, `ae_lineMean_pos`.
Uses Lemma 7.5 through the line data only (R48-neutral).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd chiC zeroGFFTestCov)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.RealContact

namespace Term

open Restart Restart.RetAux79 Restart.DomainMarkov Supp7 Sec7 Sec7.Lemma76F Sec7.PocketTraversal
  Exist.Staged Exist.StagedLaw Sec2.Assembly LocalSets WholeField RLC.AStopProc RLC.AStopSafe
open Restart.DomainMarkov.K2 Restart.DomainMarkov.Aux79
open Theorem14 Theorem14.SB

section Safe

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {κ : ℝ}
  {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}

/-- **K2's (S) and (L) for the first path in the chart of the completed second path** (see the module
docstring). -/
theorem hasSafe_term (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {c₂ : BoundaryWord} {E₂ : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE₂m : Measurable E₂) (hreg₂ : ∀ ω, IsRegularDriver (E₂ ω)) (hE₂2 : ∀ ω, (E₂ ω).2 = ζ₂ ω)
    (hfl₂ : IsFlowLineDriver κ c₂.fn c₂.jumps θ₂ P (fun ω => Exist.flowField x₂ 0 (h ω))
      (fun s ω => (E₂ ω).1 s) (fun ω => (E₂ ω).2))
    (htrace₂ : ∀ᵐ ω ∂P, IsGeneratingTrace (E₂ ω).1 (ζ₂ ω) (fun s => η₂ ω s - x₂))
    {N : ℝ≥0} {η₁' ηb₂ : Ω → ℝ≥0 → ℂ}
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    (hag₂ : ∀ᵐ ω ∂P, ∀ s, ηb₂ ω s = η₂ ω (capTime (capR 0 N) (ζ₂ ω) s))
    {M : Set Ω} (hM : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ 0 N] M)
    (hMg : ∀ ω ∈ M, IsTermGood N E₂ ηb₂ η₁' ζ₁ x₁ x₂ ω)
    (ho : AObs (fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ 0 N) M (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂)
      (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂))
    (a : ForceWordType)
    (htype : ∀ ω ∈ M, lWord κ θ₂ c₂ N E₂ x₁ x₂ ω ∈ FCDet.typeSet κ θ₁ a.nL a.nR a.rhoL a.rhoR)
    {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous (W · ω)) (hW0 : ∀ ω, W 0 ω = 0)
    (hgen : ∀ ω ∈ M, IsGeneratingTrace (W · ω)
      (aLife (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂) ω)
      (aPath (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂) ω))
    (hQa : ∀ t, Measurable[fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ 0 N t]
      (M.indicator (aClock (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) t))) :
    HasSafeLaw κ a.rhoL a.rhoR P
        (aFilt (fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ 0 N) M (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) hQa) M
        (M.indicator (aLife (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂))) W
        (geomLW W (lXL κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a)) (geomRW W (lXR κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a))
        (fun ω => Chart.chartTransport (isConformal_lChart x₁ x₂ N E₂ ω) 1 (θ₁ * chiC κ) (chiC κ) (h ω)) ∧
      HasSafeMembers P
        (aFilt (fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ 0 N) M (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) hQa) M
        (M.indicator (aLife (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂))) W
        (fun ω => Chart.chartTransport (isConformal_lChart x₁ x₂ N E₂ ω) 1 (θ₁ * chiC κ) (chiC κ) (h ω)) := by
  classical
  set Γ := pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂ with hΓ
  set L := pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂ with hL
  obtain ⟨c₁, E₁, -, -, -, hE₁m, hreg₁, hE₁2, hfl₁, htrace₁⟩ := exists_regular_driver hb hη₁
  choose ηc₁ ηc₂ d using fun t : ℝ≥0 => exists_isLineData hL75 hκ hκ4 hb hh hη₁ hη₂ hu₀ t N
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hAm : ∀ t, Measurable[mΩ, hittingSigma] (lineSet (ηc₁ t) (ηc₂ t) t N) := fun t =>
    (d t).measurable_lineSet.mono (retSigma76_le P η₁ η₂ ζ₁ ζ₂ t N) le_rfl
  choose g hg using fun t => IsLocalSet.exists_isLocalSetMean hh0 (hAm t) ((d t).isLocalSet_lineSet hh0)
  -- the chart is measurable at time `0`
  have hrecm : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ 0 N] (pRec N E₂) :=
    measurable_recOf_retSigma76 hκ hE₂m hreg₂ hE₂2 hfl₂ htrace₂ (measurable_lifetime_of_isFlowLine hη₂)
      (d 0).cont₂ (d 0).meas₂ (d 0).ae₂
  have h𝓖0 : fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ 0 N 0 = retSigma76 P η₁ η₂ ζ₁ ζ₂ 0 N := by
    rw [fstPhysFiltration_apply, add_zero]
  have hrec0 : Measurable[fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ 0 N 0] (pRec N E₂) := by
    rw [h𝓖0]; exact hrecm
  have hM0 : MeasurableSet[fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ 0 N 0] M := by
    rw [h𝓖0]; exact hM
  obtain ⟨-, hliftc, hlift, hdom, hfwd, -, hliftm⟩ :=
    isMeasChart_physChart hrec0 (measurable_pSeed hrec0 x₁ x₂) x₂
  -- good samples, reach and regularity
  have hgood : ∀ ω ∈ M, IsAGood Γ L ω := fun ω hω => (hMg ω hω).isAGood
  have hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ M → (q : ℝ≥0∞) < aLife Γ L ω → ∃ t, q ≤ aClock Γ t ω :=
    fun q => Eventually.of_forall fun ω hω hq => (hgood ω hω).exists_aClock_ge hq
  have hreg : ∀ᵐ ω ∂P, ω ∈ M → IsForceReg W (geomLW W (lXL κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a))
      (geomRW W (lXR κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a)) (aLife Γ L) ω :=
    Eventually.of_forall fun ω _ => FCDet.isForceReg_thr hW0 hWc _ _ _ ω
  -- the line kernel
  set 𝒢L : ℝ≥0 → MeasurableSpace Ω := fun t =>
    germSigma (lineSet (ηc₁ t) (ηc₂ t) t N) (centredField h u₀) ⊔ retSigma76 P η₁ η₂ ζ₁ ζ₂ t N with h𝒢Ldef
  have h𝒢L : ∀ t, fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ 0 N t ≤ 𝒢L t := fun t => by
    rw [fstPhysFiltration_apply, zero_add]
    exact le_sup_right
  have h𝒢Lm : ∀ t, 𝒢L t ≤ mΩ := fun t =>
    sup_le (germSigma_le (hAm t) hh0.measurable) (retSigma76_le P η₁ η₂ ζ₁ ζ₂ t N)
  have hker : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ M →
      (aClock Γ t ω : ℝ≥0∞) < aLife Γ L ω →
      tsupport φ ⊆ (lChart x₁ x₂ N E₂ ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (aClock Γ t ω)) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢L t] ω =
        Complex.exp (Complex.I * ((g t ω + smoothDist upperHalfPlaneOpens u₀) φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((lChart x₁ x₂ N E₂ ω).2.1 ''
            (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (aClock Γ t ω))) φ φ : ℝ) : ℂ)) := by
    intro t φ
    filter_upwards [(d t).ae_condExp_lineKernel hh hu₀ (hg t) φ,
      ae_lineSet_eq hE₂2 ha₁ hag₂ hMg hgen (d t)] with ω hk hD hω hlt hs
    have hHK : IsHPHull (fwdHull (fun s : ℝ => W s.toNNReal ω) (aClock Γ t ω)) :=
      isHPHull_fwdHull ((hWc ω).comp continuous_real_toNNReal) (NNReal.coe_nonneg _)
    have hcon := hHK.isConnected.image _ ((isConformal_lChart x₁ x₂ N E₂ ω).1.continuousOn.mono sdiff_subset)
    exact hk _ hcon.isPreconnected hcon.nonempty (hD hω hlt) hs
  -- the line means
  have hmean : ∀ (t : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ M →
      ω ∈ lineSafe (aClock Γ) W (aLife Γ L) (tsupport ψ) t →
      Chart.chartTransport (isConformal_lChart x₁ x₂ N E₂ ω) 1 (θ₁ * chiC κ) (chiC κ)
          (g t ω + smoothDist upperHalfPlaneOpens u₀) ψ =
        ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) (aClock Γ t ω)
          (bheProc κ a.rhoL a.rhoR W (geomLW W (lXL κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a))
            (geomRW W (lXR κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a)) ω (aClock Γ t ω)) z * ψ z := by
    intro t ψ
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | hpos
    · subst h0
      filter_upwards [ae_lineMean_zero hκ hh hu₀ hE₂m hreg₂ hE₂2 hfl₂ htrace₂ Γ hWc hW0 a htype (d 0) (hg 0)]
        with ω hω hωM _
      exact hω hωM ψ
    · filter_upwards [ae_lineMean_pos hκ hκ4 hh hη₁ hu₀ hE₁m hreg₁ hE₁2 hfl₁ htrace₁ hE₂m hreg₂ hE₂2 hfl₂
        htrace₂ ha₁ hag₂ hMg hWc hW0 hgen a htype hpos (d t) (hg t)] with ω hω hωM hs
      exact hω hωM hs.1 ψ hs.2
  -- (S)
  have hS := hasSafeLaw_of_lineKernel_indicator (P := P) (κ := κ) (ρL := a.rhoL) (ρR := a.rhoR) (W := W)
    (VL := geomLW W (lXL κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a)) (VR := geomRW W (lXR κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a))
    (ζ := aLife Γ L) (𝓖 := fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ 0 N) (F := M) (Qc := aClock Γ)
    (c := lChart x₁ x₂ N E₂) hM0 (isConformal_lChart x₁ x₂ N E₂) hdom hfwd hliftm hliftc hh.1
    (θ₁ * chiC κ) (chiC κ) (continuous_aClock Γ) (monotone_aClock Γ) (aClock_zero Γ) hQa hreach hreg
    (fun ψ t => measurableSet_lineSafe_aStop ho hgood hgen ψ.hasCompactSupport.isCompact t)
    𝒢L h𝒢L h𝒢Lm (fun t ω => g t ω + smoothDist upperHalfPlaneOpens u₀) hker hmean
  -- (L)
  have hL' := hasSafeMembers_of_lineLocal_indicator (P := P) (ζ := aLife Γ L) (W := W)
    (VL := geomLW W (lXL κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a)) (VR := geomRW W (lXR κ θ₁ θ₂ c₂ N E₂ x₁ x₂ a))
    (𝓖 := fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ 0 N) (F := M) (Qc := aClock Γ) hh.1 hu₀.1 hh0
    (c := lChart x₁ x₂ N E₂) (isConformal_lChart x₁ x₂ N E₂) hdom hfwd hliftm hliftc hlift (θ₁ * chiC κ) (chiC κ)
    (continuous_aClock Γ) (monotone_aClock Γ) (aClock_zero Γ) hQa hreach hreg
    (fun Fb t => measurableSet_lineSafe_aStop ho hgood hgen (Coupling.isCompact_ballsK Fb) t)
    (fun t => retSigma76 P η₁ η₂ ζ₁ ζ₂ t N)
    (fun t => by rw [fstPhysFiltration_apply, zero_add])
    (fun t => retSigma76_le P η₁ η₂ ζ₁ ζ₂ t N) (fun t => lineSet (ηc₁ t) (ηc₂ t) t N) hAm
    (fun t ω => ⟨lineSet_subset_H _ _ t N ω, isOpen_H_diff_lineSet (d t).cont₁ (d t).cont₂ t N ω⟩)
    (fun t => (d t).isHistoryAvoidanceLocal_lineSet)
    (fun t => ae_lineSet_eq hE₂2 ha₁ hag₂ hMg hgen (d t))
  exact ⟨hS, hL'⟩

end Safe

end Term

end InteractingSLE.RealContact
