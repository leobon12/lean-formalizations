/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvYLimit
import InteractingSLE.Spec.Coupling.WholeField7Label
import InteractingSLE.Spec.Restart.RetPlumbProofDriverAnnounce
import InteractingSLE.Spec.Coupling.MartMeans2Lemma71
import InteractingSLE.Spec.Exist.StagedCongr
import InteractingSLE.Spec.Dimension.TraceBridge
import InteractingSLE.Spec.Coupling.Locality11Gauss
import InteractingSLE.WangWu.Adapted
import InteractingSLE.Spec.Sec2.AssemblyTheorem
import InteractingSLE.Spec.Sec7.LocalExtA2Cond
import InteractingSLE.Spec.Sec2.CriticalLifetime
import InteractingSLE.Spec.Supplement.GW1Base
import InteractingSLE.Spec.Supplement.BW1PropConfig
import InteractingSLE.Spec.Coupling.Assembly11BProvider
import InteractingSLE.Spec.Supplement.Q3ChainRetLaw
import InteractingSLE.Foundations.Loewner.Capacity
import InteractingSLE.Spec.Restart.R1Flow

/-!
# BW1's lines, part 2: the completed piece is a local set ("the terminal `A` is already a local history")

Packet PROVE-BW1-LINES. Proposition BW1's proof (p. 614): "The terminal `A` is already a local marked history with
its full Gaussian kernel, by the available endpoint theorem and Aux. 9." The frozen optional hull coupling gives
locality of the hulls `K_τ` only at stopping times `τ < ζ` (strictly before the lifetime); BW1 retains the hull **at**
the finite lifetime (the continuation threshold). Here the terminal hull is reached by the proved Gaussian
hull-limit theorem (`Restart.FlowStopIdentCMI.cmiXHullLocalityLimitStatement`) along an announcing sequence:

* **`isLocalSet_fwdHull_min_life`**: for every optional hull coupling `(W, ζ, h)` and every deterministic level
  `N`, the hull at `min ζ N` (read through any driver that is continuous for every sample, starts at `0`, and agrees
  with `W` before `ζ`) is a local set of `h`;
* `isLocalSet_centred_fwdHull_min_life`: the same for the centred field;
* for the first piece of a staged history: `pieceVer` (its driver frozen at the lifetime, continuous for every
  sample), `ae_continuousOn_first` (a.s. continuous through a positive lifetime: Aux. lemma 3's left limit is the
  recorded value), `ae_pieceVer_eq`, `rpath_pieceVer_eq` (on good samples it is BW1's `pieceDrv`),
  **`isLocalSet_first_hull`** (the frozen piece's hull at `min ζ N` is a local set of `h`), `ae_first_hull_eq`
  (on `{0 < ζ ≤ N}` it is the completed hull `K_ζ` of `pieceDrv`), and **`exists_retained_terminal`** (its reflection
  `R(K)`, `R(z) = −1/z`, as a hitting-measurable relatively closed version, is a local set of the counterflow-frame
  centred field: BW1's `hlA`).

The level `N` replaces the lifetime by a finite time for every sample (on `{ζ = ⊤}` the hull at `ζ` is not defined);
on `{ζ ≤ N}` the set is the hull at the lifetime. In BW1 the live event `{ζ ≤ t, ζ < ∞}` is covered by the events
`{ζ ≤ N}` of the retained past.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.BW1Lines

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- The hulls of two drivers agreeing before `ζ` agree at every time before `ζ`. -/
theorem fwdHull_rpath_eq_of_lt {w w' : ℝ≥0 → ℝ} {z : ℝ≥0∞} (hww' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < z → w' t = w t)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < z) : fwdHull (Ito.rpath w') (s : ℝ) = fwdHull (fun r : ℝ => w r.toNNReal) (s : ℝ) := by
  obtain ⟨t₂, hst₂, ht₂z⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
  refine fwdHull_eq_of_eqOn s.coe_nonneg (by exact_mod_cast ENNReal.coe_lt_coe.1 hst₂) fun r hr => ?_
  refine hww' r.toNNReal (lt_of_le_of_lt ?_ ht₂z)
  exact ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)

/-- **The hull at `min ζ N` is a local set of the centred field** of an optional hull coupling (terminal hull through
the lifetime, by the Gaussian hull-limit theorem along an announcing sequence). -/
theorem isLocalSet_centred_fwdHull_min_life (hκ : 0 < κ)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    {W' : ℝ≥0 → Ω → ℝ} (hW'0 : ∀ ω, W' 0 ω = 0) (hW'c : ∀ ω, Continuous (W' · ω))
    (hW'W : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → W' t ω = W t ω) (N : ℝ≥0) :
    IsLocalSet (fun ω => fwdHull (Ito.rpath (W' · ω)) ((min (ζ ω) N).toNNReal : ℝ))
      (WholeField.centredField h u₀) P := by
  have hZ := WholeField.isZeroBoundaryGFF_centredField hC hu₀
  have hH := WholeField.isHarmonicDistOn_smoothDist hu₀.1
  obtain ⟨hX, hker⟩ := hC.2.2.2
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · -- an inadmissible seed: the lifetime is `0`, the hull is empty
    have hζ0 : ∀ᵐ ω ∂P, ζ ω = 0 := IsIntegratedSLEEvolution.ae_lifetime_eq_zero_of_threshold hC.1 hseed
    refine Exist.Staged.IsLocalSet.congr_ae (WangWu.isLocalSet_empty hZ) ?_
    filter_upwards [hζ0] with ω hω
    rw [hω, min_eq_left zero_le, ENNReal.toNNReal_zero, NNReal.coe_zero]
    exact QuantumZipper.RS.fwdHull_zero_eq_empty ((hW'c ω).comp continuous_real_toNNReal)
  obtain ⟨σ₀, hσ₀⟩ := WholeField.exists_isAnnouncingSeq_driving hC.1 hκ hX hseed
  set T : Ω → ℝ≥0 := fun ω => (min (ζ ω) N).toNNReal with hT
  have hTe : ∀ ω, (T ω : ℝ≥0∞) = min (ζ ω) N := fun ω =>
    ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))
  -- the stops before the lifetime and their caps by `T`
  set s' : ℕ → Ω → ℝ≥0 := fun n ω => min (σ₀ n ω) N with hs'
  set s : ℕ → Ω → ℝ≥0 := fun n ω => min (s' n ω) (T ω) with hs
  have hs'ζ : ∀ n, ∀ᵐ ω ∂P, (s' n ω : ℝ≥0∞) < ζ ω := fun n =>
    (hσ₀.2.2.1 n).mono fun ω hω => (ENNReal.coe_le_coe.2 (min_le_left _ _)).trans_lt hω
  have hss' : ∀ n, ∀ᵐ ω ∂P, s n ω = s' n ω := fun n => (hs'ζ n).mono fun ω hω => by
    refine min_eq_left ?_
    rw [← ENNReal.coe_le_coe, hTe]
    exact le_min hω.le (ENNReal.coe_le_coe.2 (min_le_right _ _))
  have hloc' : ∀ n, IsLocalSet (fun ω => fwdHull (Ito.rpath (W' · ω)) (s' n ω : ℝ))
      (WholeField.centredField h u₀) P := by
    intro n
    have hsn : IsStoppingTime (drivingFiltration P hX) fun ω => ((s' n ω : ℝ≥0) : WithTop ℝ≥0) := by
      simpa only [s', WithTop.coe_min] using (hσ₀.1 n).min (isStoppingTime_const _ N)
    have hlt : ∀ᵐ ω ∂P, ((((s' n ω : ℝ≥0) : WithTop ℝ≥0) : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := hs'ζ n
    have hl := (hker _ hsn hlt).1
    simp only [WithTop.untopD_coe] at hl
    refine (Exist.Staged.IsLocalSet.congr_ae (WholeField.IsLocalSet.sub_dist hl hH) ?_)
    filter_upwards [hW'W, hs'ζ n] with ω hω hωn
    exact fwdHull_rpath_eq_of_lt hω hωn
  have hloc : ∀ n, IsLocalSet (fun ω => fwdHull (Ito.rpath (W' · ω)) (s n ω : ℝ))
      (WholeField.centredField h u₀) P := fun n =>
    Exist.Staged.IsLocalSet.congr_ae (hloc' n) ((hss' n).mono fun ω hω => by rw [hω])
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => (s n ω : ℝ≥0∞)) atTop (𝓝 (T ω : ℝ≥0∞)) := by
    filter_upwards [Restart.RetAux79.ae_tendsto_of_isAnnouncingSeq hσ₀, ae_all_iff.2 hss'] with ω ht hss
    have h1 : Tendsto (fun n => (s' n ω : ℝ≥0∞)) atTop (𝓝 (min (ζ ω) N)) := by
      simpa only [s', ENNReal.coe_min] using ht.min (tendsto_const_nhds (x := (N : ℝ≥0∞)))
    rw [hTe]
    exact h1.congr fun n => by rw [hss n]
  exact Restart.FlowStopIdentCMI.cmiXHullLocalityLimitStatement P (WholeField.centredField h u₀) hZ W' hW'0 hW'c
    s T (fun ω a b hab => min_le_min_right _ (min_le_min_right _ (hσ₀.2.1 ω hab)))
    (fun _ _ => min_le_right _ _) hlim hloc

/-- **The hull at `min ζ N` is a local set of the field** of an optional hull coupling. -/
theorem isLocalSet_fwdHull_min_life (hκ : 0 < κ)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    {W' : ℝ≥0 → Ω → ℝ} (hW'0 : ∀ ω, W' 0 ω = 0) (hW'c : ∀ ω, Continuous (W' · ω))
    (hW'W : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → W' t ω = W t ω) (N : ℝ≥0) :
    IsLocalSet (fun ω => fwdHull (Ito.rpath (W' · ω)) ((min (ζ ω) N).toNNReal : ℝ)) h P := by
  have hu₀ := LocalExt.isBoundedHarmonicExtension_bheAt κ ρL ρR xL xR
  have hl := isLocalSet_centred_fwdHull_min_life hκ hC hu₀ hW'0 hW'c hW'W N
  have hadd := Coupling.IsLocalSet.add_dist hl (WholeField.isHarmonicDistOn_smoothDist hu₀.1)
  simpa only [WholeField.centredField, sub_add_cancel] using hadd

/-! ### The first piece of a staged history -/

section FirstPiece

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {θ : ℝ} {t : ℝ≥0∞} {rest : List Instr}

omit mΩ [StandardBorelSpace Ω] in
open Classical in
/-- **The first piece's driver frozen at its lifetime, continuous for every sample**: the stopped driver where it is
continuous through the lifetime and starts at `0`, and `0` elsewhere. -/
def pieceVer (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (s : ℝ≥0) (ω : Ω) : ℝ :=
  if ContinuousOn (E 0 ω).1 {r | (r : ℝ≥0∞) ≤ (E 0 ω).2} ∧ (E 0 ω).1 0 = 0 then
    (E 0 ω).1 (min (s : ℝ≥0∞) (E 0 ω).2).toNNReal else 0

omit mΩ [StandardBorelSpace Ω] in
theorem pieceVer_of_good {ω : Ω} (hc : ContinuousOn (E 0 ω).1 {r | (r : ℝ≥0∞) ≤ (E 0 ω).2})
    (h0 : (E 0 ω).1 0 = 0) (s : ℝ≥0) : pieceVer E s ω = (E 0 ω).1 (min (s : ℝ≥0∞) (E 0 ω).2).toNNReal := by
  simp only [pieceVer, hc, h0, and_self, ↓reduceIte]

omit mΩ [StandardBorelSpace Ω] in
theorem continuous_pieceVer (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) : Continuous (pieceVer E · ω) := by
  by_cases hg : ContinuousOn (E 0 ω).1 {r | (r : ℝ≥0∞) ≤ (E 0 ω).2} ∧ (E 0 ω).1 0 = 0
  · have e : (pieceVer E · ω) = fun s : ℝ≥0 => (E 0 ω).1 (min (s : ℝ≥0∞) (E 0 ω).2).toNNReal :=
      funext fun s => pieceVer_of_good hg.1 hg.2 s
    rw [e]
    exact CounterflowRange.continuous_stopped hg.1
  · have e : (pieceVer E · ω) = fun _ => 0 := funext fun s => by simp only [pieceVer, hg, ↓reduceIte]
    rw [e]
    exact continuous_const

omit mΩ [StandardBorelSpace Ω] in
theorem pieceVer_zero (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) : pieceVer E 0 ω = 0 := by
  by_cases hg : ContinuousOn (E 0 ω).1 {r | (r : ℝ≥0∞) ≤ (E 0 ω).2} ∧ (E 0 ω).1 0 = 0
  · rw [pieceVer_of_good hg.1 hg.2, ENNReal.coe_zero, min_eq_left zero_le, ENNReal.toNNReal_zero]
    exact hg.2
  · simp only [pieceVer, hg, ↓reduceIte]

omit mΩ [StandardBorelSpace Ω] in
/-- On a good sample the frozen version read on `ℝ` is BW1's stopped driver `pieceDrv`. -/
theorem rpath_pieceVer_eq {ω : Ω} (hc : ContinuousOn (E 0 ω).1 {r | (r : ℝ≥0∞) ≤ (E 0 ω).2})
    (h0 : (E 0 ω).1 0 = 0) : Ito.rpath (pieceVer E · ω) = BW1Prop.pieceDrv (E 0 ω) :=
  funext fun x => pieceVer_of_good hc h0 x.toNNReal

/-- **The first piece is continuous through a positive lifetime and starts at `0`**, almost surely: continuity before
the lifetime and the start are the integrated path's; at a finite positive lifetime the driver has a left limit
(Aux. lemma 3, `IsIntegratedSLEEvolution.ae_tendsto_threshold`), which is its recorded value (`IsStagedHistory`). -/
theorem ae_continuousOn_first (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hS : IsStagedHistory κ b jumps P h spec E) (hroot : spec.1 = 0)
    (hp : spec.2.2 = Sum.inl (θ, t) :: rest) :
    ∀ᵐ ω ∂P, 0 < (E 0 ω).2 → ContinuousOn (E 0 ω).1 {r | (r : ℝ≥0∞) ≤ (E 0 ω).2} ∧ (E 0 ω).1 0 = 0 := by
  obtain ⟨h'', 𝓕, VL, VR, B, -, hC⟩ := hS.isFlowLineDriver_first hκ hb hh hroot hp
  filter_upwards [hC.1.2.2.2.2, hC.1.ae_tendsto_threshold hκ, hS.2.2.1 0] with ω hpath hlim hval hζ0
  refine ⟨?_, hpath.1⟩
  rcases eq_or_ne (E 0 ω).2 ⊤ with htop | hfin
  · have e : {r : ℝ≥0 | (r : ℝ≥0∞) ≤ (E 0 ω).2} = {r : ℝ≥0 | (r : ℝ≥0∞) < (E 0 ω).2} := by
      ext r
      simp only [mem_ofPred_eq, htop, le_top, ENNReal.coe_lt_top]
    rw [e]
    exact hpath.2.2.2.1
  · set T : ℝ≥0 := (E 0 ω).2.toNNReal with hTdef
    have hTe : (T : ℝ≥0∞) = (E 0 ω).2 := ENNReal.coe_toNNReal hfin
    have hT0 : 0 < T := by
      rw [← ENNReal.coe_lt_coe, hTe, ENNReal.coe_zero]
      exact hζ0
    obtain ⟨w₀, _, _, htend, _⟩ := hlim T hT0 hTe
    have hW : Tendsto (E 0 ω).1 (𝓝[<] T) (𝓝 w₀) := (continuous_fst.tendsto _).comp htend
    have hv : (E 0 ω).1 T = w₀ := hval hfin hζ0 w₀ hW
    have hset : {r : ℝ≥0 | (r : ℝ≥0∞) ≤ (E 0 ω).2} = Iic T := by
      ext r
      simp only [mem_ofPred_eq, mem_Iic, ← hTe, ENNReal.coe_le_coe]
    have hopen : {r : ℝ≥0 | (r : ℝ≥0∞) < (E 0 ω).2} = Iio T := by
      ext r
      simp only [mem_ofPred_eq, mem_Iio, ← hTe, ENNReal.coe_lt_coe]
    have hco : ContinuousOn (E 0 ω).1 (Iio T) := hopen ▸ hpath.2.2.2.1
    rw [hset]
    intro r hr
    rcases (mem_Iic.1 hr).lt_or_eq with hlt | heq
    · exact ((hco.continuousAt (isOpen_Iio.mem_nhds hlt)).continuousWithinAt)
    · rw [heq, ← continuousWithinAt_Iio_iff_Iic, ContinuousWithinAt, hv]
      exact hW

/-- Almost surely the frozen version agrees with the first piece's driver before the lifetime. -/
theorem ae_pieceVer_eq (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hS : IsStagedHistory κ b jumps P h spec E) (hroot : spec.1 = 0)
    (hp : spec.2.2 = Sum.inl (θ, t) :: rest) :
    ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) < (E 0 ω).2 → pieceVer E s ω = (E 0 ω).1 s := by
  filter_upwards [ae_continuousOn_first hκ hb hh hS hroot hp] with ω hω s hs
  obtain ⟨hc, h0⟩ := hω (lt_of_le_of_lt zero_le hs)
  rw [pieceVer_of_good hc h0, min_eq_left hs.le, ENNReal.toNNReal_coe]

/-- **The completed first piece is a local set of the field**: for every level `N`, the hull of the frozen first
piece at `min ζ N` is a local set of `h` (on `{ζ ≤ N}` it is the hull at the lifetime, the terminal `A` of
Proposition BW1). -/
theorem isLocalSet_first_hull (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hS : IsStagedHistory κ b jumps P h spec E) (hroot : spec.1 = 0)
    (hp : spec.2.2 = Sum.inl (θ, t) :: rest) (N : ℝ≥0) :
    IsLocalSet (fun ω => fwdHull (Ito.rpath (pieceVer E · ω)) ((min (E 0 ω).2 N).toNNReal : ℝ)) h P := by
  obtain ⟨h'', 𝓕, VL, VR, B, htr, hC⟩ := hS.isFlowLineDriver_first hκ hb hh hroot hp
  have hl := isLocalSet_fwdHull_min_life hκ hC (pieceVer_zero E) (continuous_pieceVer E)
    (ae_pieceVer_eq hκ hb hh hS hroot hp) N
  have hT : IsHarmonicDistOn (smoothDist upperHalfPlaneOpens fun _ => θ * QuantumZipper.chiC κ) H :=
    WholeField.isHarmonicDistOn_smoothDist (InnerProductSpace.harmonicOnNhd_const _)
  have hsub := WholeField.IsLocalSet.sub_dist hl hT
  have e : (fun ω => h'' ω - smoothDist upperHalfPlaneOpens fun _ => θ * QuantumZipper.chiC κ) = h := by
    funext ω
    ext φ
    have hφ := htr ω φ φ (fun z => by rw [Complex.ofReal_zero, add_zero])
    have hs := Coupling.smoothDist_apply_eq (u₀ := fun _ => θ * QuantumZipper.chiC κ) continuousOn_const φ
    change h'' ω φ - smoothDist upperHalfPlaneOpens (fun _ => θ * QuantumZipper.chiC κ) φ = h ω φ
    rw [hs, hφ, MeasureTheory.integral_const_mul]
    ring
  rwa [e] at hsub

/-- **On `{0 < ζ ≤ N}` the local set is the completed piece's hull** `K_ζ` of BW1's stopped driver `pieceDrv`
(`BW1Prop.bw1_piece_geometry`'s `U`), almost surely. -/
theorem ae_first_hull_eq (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hS : IsStagedHistory κ b jumps P h spec E) (hroot : spec.1 = 0)
    (hp : spec.2.2 = Sum.inl (θ, t) :: rest) (N : ℝ≥0) :
    ∀ᵐ ω ∂P, 0 < (E 0 ω).2 → (E 0 ω).2 ≤ N →
      fwdHull (Ito.rpath (pieceVer E · ω)) ((min (E 0 ω).2 N).toNNReal : ℝ) =
        fwdHull (BW1Prop.pieceDrv (E 0 ω)) ((E 0 ω).2.toNNReal : ℝ) := by
  filter_upwards [ae_continuousOn_first hκ hb hh hS hroot hp] with ω hω h0 hN
  obtain ⟨hc, h00⟩ := hω h0
  rw [rpath_pieceVer_eq hc h00, min_eq_left hN]

/-- **BW1's retained set in the counterflow frame is a local set** (`hlA` of the union law; the terminal analogue of
`Supp8.Q3Chain.retained_at_stop`'s locality). For the first piece of a staged history, a level `N`, the centred
original field `h − 𝔥₀` and a counterflow-frame field `h'` whose centred field is its reflection by `R(z) = −1/z`:
there is a hitting-measurable random set `A`, relatively closed in `ℍ` on every sample, almost surely the reflection
`R(K_{min ζ N})` of the frozen piece's hull, which is a local set of the centred `h'`. -/
theorem exists_retained_terminal (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hS : IsStagedHistory κ b jumps P h spec E) (hroot : spec.1 = 0)
    (hp : spec.2.2 = Sum.inl (θ, t) :: rest) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {h' : Ω → DistOn upperHalfPlaneOpens} {u₀' : ℂ → ℝ}
    (hcen : ∀ ω, WholeField.centredField h' u₀' ω = WangWu.reflectField (WholeField.centredField h u₀ ω))
    (N : ℝ≥0) :
    ∃ A : Ω → Set ℂ, Measurable[mΩ, hittingSigma] A ∧ (∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) ∧
      (∀ᵐ ω ∂P, A ω = WangWu.negInv '' fwdHull (Ito.rpath (pieceVer E · ω)) ((min (E 0 ω).2 N).toNNReal : ℝ)) ∧
      IsLocalSet A (WholeField.centredField h' u₀') P := by
  classical
  set K : Ω → Set ℂ := fun ω => fwdHull (Ito.rpath (pieceVer E · ω)) ((min (E 0 ω).2 N).toNNReal : ℝ) with hKdef
  have hKH : ∀ ω, IsHPHull (K ω) := fun ω =>
    isHPHull_fwdHull ((continuous_pieceVer E ω).comp continuous_real_toNNReal) (NNReal.coe_nonneg _)
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hloc0 : IsLocalSet K (WholeField.centredField h u₀) P :=
    WholeField.IsLocalSet.sub_dist (isLocalSet_first_hull hκ hb hh hS hroot hp N)
      (WholeField.isHarmonicDistOn_smoothDist hu₀.1)
  obtain ⟨A₀, hA₀m, hA₀e, -⟩ := WholeField.IsLocalSet.exists_measurable_version hloc0 hh0.1
  -- a version that is a relatively closed subset of `ℍ` on every sample
  set N₀ : Set Ω := toMeasurable P {ω | A₀ ω ≠ K ω} with hN₀
  have hN₀m : MeasurableSet N₀ := measurableSet_toMeasurable P _
  have hN₀0 : P N₀ = 0 := by
    rw [hN₀, measure_toMeasurable]
    exact ae_iff.1 hA₀e
  have hgood : ∀ ω, ω ∉ N₀ → A₀ ω = K ω := fun ω hω => by
    by_contra hc
    exact hω (subset_toMeasurable P {ω | A₀ ω ≠ K ω} hc)
  set Ah : Ω → Set ℂ := fun ω => if ω ∈ N₀ then ∅ else A₀ ω with hAhdef
  have hAhm : Measurable[mΩ, hittingSigma] Ah :=
    Measurable.ite (mβ := hittingSigma) (p := fun ω => ω ∈ N₀) hN₀m
      (@measurable_const (Set ℂ) Ω hittingSigma mΩ ∅) hA₀m
  have hAhG : ∀ ω, Ah ω ⊆ H ∧ IsOpen (H \ Ah ω) := fun ω => by
    by_cases hω : ω ∈ N₀
    · simp only [hAhdef, hω, ↓reduceIte, empty_subset, sdiff_empty, true_and]
      exact QuantumZipper.isOpen_H
    · simp only [hAhdef, hω, ↓reduceIte, hgood ω hω]
      exact ⟨(hKH ω).1, (hKH ω).2.2.1⟩
  have hAhe : ∀ᵐ ω ∂P, Ah ω = K ω := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN₀0] with ω h1
    simp only [hAhdef, h1, ↓reduceIte, hgood ω h1]
  have hAhloc : IsLocalSet Ah (WholeField.centredField h u₀) P := Coupling.IsLocalSet.congr_set hloc0 hAhe
  refine ⟨fun ω => WangWu.negInv '' Ah ω, WangWu.measurable_image_negInv.comp hAhm, fun ω => ⟨?_, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact WangWu.negInv_mem_H ((hAhG ω).1 hw)
  · rw [WangWu.H_diff_image_negInv]
    exact WangWu.isOpen_image_negInv (hAhG ω).2 sdiff_subset
  · filter_upwards [hAhe] with ω h1
    rw [h1]
  · have h1 := WangWu.IsLocalSet.reflect hAhloc
    have e : (fun ω => WangWu.reflectField (WholeField.centredField h u₀ ω)) = WholeField.centredField h' u₀' :=
      funext fun ω => (hcen ω).symm
    rwa [e] at h1

end FirstPiece

end InteractingSLE.Theorem14.BW1Lines
