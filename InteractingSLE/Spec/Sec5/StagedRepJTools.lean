/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedRepLaterGlue
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Prop 5.9's later root stages: generic tools for the transfer of the killed comparison clause

Packet PROVE-STAGED-REPJ. PROVE-STAGED-REP2 carried the root stage's killed comparison clause (`CompClauseK`, ruling
R78) from the glued space to PROVE-PROP59-PIECES' space along the pair (field, counterflow history), with a dilation
that was a Borel function of the stage start. At a later stage `j + 1` three things change, and this file provides the
generic tools for them:

* **a frozen dilation**: the root dilation `λ` of PIECES' tree is a function of the past but not of the stage start, so
  REP2's `CompClauseK.dilate` does not apply. **`IsStoppedRep.compClauseK_dil`**: from a stopped representation, the
  comparison clause of the piece dilated by any past-measurable time factor `C` and started at any past-measurable
  start `y'` with the dilated marks (`le_dilSec_of_prem`: under almost every conditional law given the past the factor
  is frozen, and the premise is Brownian-scaling invariant);
* **conditioning back**: **`CompClauseK.of_cond`** (a clause under `μ[|A₀]` on events inside `A₀` is a clause under
  `μ`);
* **the transfer with almost-sure identifications**: **`compClauseK_transfer`** (pasts and observables agree with a
  common Borel observable only almost surely);
* **Lusin separation**: **`exists_measurableSet_inter_eq`** — on a standard Borel space, a Borel set saturated for a
  Borel map `Y` (within a Borel set `G`) is the trace on `G` of a `Y`-preimage of a Borel set (Mathlib's
  `AnalyticSet.measurablySeparable`).

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.StagedRepJ

open Prop59Stage Prop59Nodes StagedKill StagedKCand StagedRepLater Sec7.Aux122Disint

/-! ### Dilated samples are jointly Borel -/

section Meas

variable {nL nR : ℕ}

/-- **The dilated samples are jointly Borel in the factor and the samples.** -/
theorem measurable_dilSamp_uncurry : Measurable fun x : ℝ≥0 × Samp nL nR => dilSamp x.1 x.2 := by
  have hc : Measurable fun x : ℝ≥0 × Samp nL nR => x.1 := measurable_fst
  have hz : Measurable fun x : ℝ≥0 × Samp nL nR => x.2.1 / ((x.1 : ℝ≥0) : ℝ≥0∞) :=
    measurable_snd.fst.div (measurable_coe_nnreal_ennreal.comp hc)
  refine hz.prodMk (measurable_pi_iff.2 fun q => ?_)
  refine Measurable.ite (measurableSet_lt measurable_const hz) ?_ measurable_const
  exact measurable_dilV hc (measurable_sampExt measurable_snd.snd (hc.mul_const _))

/-- The section of a set of records at the start `y₀'`, read through the samples dilated by `c`. -/
def dilSec (y₀' : Start nL nR) (c : ℝ≥0) (S : Set (Start nL nR × Samp nL nR)) : Set (Start nL nR × Samp nL nR) :=
  {r | (y₀', dilSamp c r.2) ∈ S}

theorem measurableSet_dilSec (y₀' : Start nL nR) (c : ℝ≥0) {S : Set (Start nL nR × Samp nL nR)}
    (hS : MeasurableSet S) : MeasurableSet (dilSec y₀' c S) := by
  have hm : Measurable fun r : Start nL nR × Samp nL nR => (y₀', dilSamp c r.2) :=
    measurable_const.prodMk (measurable_dilSamp_uncurry.comp (measurable_const.prodMk measurable_snd))
  exact hm hS

end Meas

/-! ### The killed premise with a frozen dilation -/

section Prem

variable {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {iL : Fin nL} {iR : Fin nR}

/-- **The killed premise read through a fixed dilation.** If every traced evolution from every start charges `S` with
probability at least `p`, then every evolution from `y₀`, traced up to its killed lifetime, has killed samples whose
`c`-dilation, recorded with the start `y₀'` (whose marks are the dilated marks of `y₀`), lies in `S` with probability
at least `p` (Brownian scaling of the evolution, its trace and its killed lifetime). -/
theorem le_dilSec_of_prem {S : Set (Start nL nR × Samp nL nR)} {p : ℝ≥0∞}
    (h : CompPremiseFarK κ ρL ρR iL iR univ S p) {c : ℝ≥0} (hc : c ≠ 0) {y₀ y₀' : Start nL nR}
    (hy : y₀'.2 = (dilV c y₀).2) (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω')
    [IsProbabilityMeasure P'] (𝓕' : Filtration ℝ≥0 mΩ') (W' : ℝ≥0 → Ω' → ℝ) (VL' : Fin nL → ℝ≥0 → Ω' → ℝ)
    (VR' : Fin nR → ℝ≥0 → Ω' → ℝ) (B' : ℝ≥0 → Ω' → ℝ) (ζ' : Ω' → ℝ≥0∞)
    (hE : IsIntegratedSLEEvolution κ y₀.2.1 y₀.2.2 ρL ρR P' 𝓕' W' VL' VR' B' ζ')
    (htr : ∀ᵐ ω' ∂P', ∃ η : ℝ≥0 → ℂ,
      IsGeneratingTrace (fun t => W' t ω') (traceHorizon false iL iR W' VL' VR' ζ' ω') η) :
    p ≤ P' {ω' | (y₀, farSamp iL iR W' VL' VR' ζ' ω') ∈ dilSec y₀' c S} := by
  have hE' := ZhanGT4.UpMark.isIntegratedSLEEvolution_scale hc hE
  have hy1 : y₀'.2.1 = fun i => (Real.sqrt c)⁻¹ * y₀.2.1 i := by rw [hy]; rfl
  have hy2 : y₀'.2.2 = fun j => (Real.sqrt c)⁻¹ * y₀.2.2 j := by rw [hy]; rfl
  rw [← hy1, ← hy2] at hE'
  have htr' : ∀ᵐ ω' ∂P', ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => ZhanGT4.UpMark.scaleProc c W' t ω')
      (farLife iL iR (ZhanGT4.UpMark.scaleProc c W' · ω')
        (fun i t => ZhanGT4.UpMark.scaleProc c (VL' i) t ω')
        (fun k t => ZhanGT4.UpMark.scaleProc c (VR' k) t ω') (ζ' ω' / c)) η := by
    filter_upwards [htr] with ω' hω'
    obtain ⟨η, hη⟩ := hω'
    refine ⟨fun t => (((√(c : ℝ))⁻¹ : ℝ) : ℂ) * η (c * t), ?_⟩
    have hd := hη.dilate hc
    have hfl := farLife_scale hc iL iR (fun t => W' t ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω') (ζ' ω')
    simp only [ZhanGT4.UpMark.scaleProc]
    rw [hfl]
    exact hd
  have hb := h y₀' (mem_univ _) Ω' mΩ' P' _ _ _ _ _ _ hE' htr'
  refine hb.trans (le_of_eq (measure_congr ?_))
  filter_upwards [hE.2.2.2.2] with ω' hω'
  have hp := hω'.isSLEPathUpTo (le_refl _)
  have hsub : {t : ℝ≥0 | (t : ℝ≥0∞) < farLife iL iR (W' · ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω')
      (ζ' ω')} ⊆ {t | (t : ℝ≥0∞) < ζ' ω'} := fun t ht => lt_of_lt_of_le ht farLife_le
  have hfl := farLife_scale hc iL iR (fun t => W' t ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω') (ζ' ω')
  have e : samp (fun t => (√(c : ℝ))⁻¹ * W' (c * t) ω') (fun i t => (√(c : ℝ))⁻¹ * VL' i (c * t) ω')
      (fun k t => (√(c : ℝ))⁻¹ * VR' k (c * t) ω')
      (farLife iL iR (fun t => (√(c : ℝ))⁻¹ * W' (c * t) ω')
        (fun i t => (√(c : ℝ))⁻¹ * VL' i (c * t) ω') (fun k t => (√(c : ℝ))⁻¹ * VR' k (c * t) ω')
        (ζ' ω' / c)) =
      dilSamp c (samp (W' · ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω')
        (farLife iL iR (W' · ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω') (ζ' ω'))) := by
    rw [hfl]
    exact samp_scale hc (hp.continuousOn_w.mono hsub) (fun i => (hp.continuousOn_vL i).mono hsub)
      (fun k => (hp.continuousOn_vR k).mono hsub)
  show ((y₀', samp (fun t => (√(c : ℝ))⁻¹ * W' (c * t) ω')
      (fun i t => (√(c : ℝ))⁻¹ * VL' i (c * t) ω') (fun k t => (√(c : ℝ))⁻¹ * VR' k (c * t) ω')
      (farLife iL iR (fun t => (√(c : ℝ))⁻¹ * W' (c * t) ω')
        (fun i t => (√(c : ℝ))⁻¹ * VL' i (c * t) ω') (fun k t => (√(c : ℝ))⁻¹ * VR' k (c * t) ω')
        (ζ' ω' / c))) ∈ S) =
    ((y₀', dilSamp c (samp (W' · ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω')
        (farLife iL iR (W' · ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω') (ζ' ω')))) ∈ S)
  rw [e]

end Prem

/-! ### The comparison clause with a frozen dilation -/

section Frozen

variable {Ω : Type} {𝓠 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {nL nR : ℕ} {κ : ℝ} {R : Set Ω} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {iL : Fin nL}
  {iR : Fin nR} {y : Ω → Start nL nR} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {𝓕 : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL' : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR' : Fin nR → ℝ≥0 → Ω → ℝ} {B' : ℝ≥0 → Ω → ℝ}

/-- Under almost every conditional law given the past, a stopped representation represents the killed samples. -/
theorem _root_.InteractingSLE.Sec5.CrossCond.StagedKCand.IsStoppedRep.ae_hasKilledRep (hκ : 0 < κ)
    (h : IsStoppedRep κ P 𝓠 R ρL ρR iL iR y W VL VR B ζ 𝓕 W' VL' VR' B') (hR : MeasurableSet[𝓠] R)
    (hy : Measurable[𝓠] y) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ R →
      HasKilledRep κ false ρL ρR iL iR (y ω₀) ((condExpKernel P 𝓠 ω₀).map (pieceSamp W VL VR ζ)) := by
  obtain ⟨N, 𝓖, W'', VL'', VR'', B'', -, hN0, hpt, hev⟩ := h.ae_isSLEEvolutionUpTo hR hy
  have hle : 𝓠 ≤ mΩ := h.le0.trans (𝓕.le 0)
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  filter_upwards [hev, ae_ae_condExpKernel hle hNae, ae_ae_condExpKernel_mem hle hR, hNae] with
    ω₀ hE hνN hmemR hω₀N hω₀R
  have hgood : ∀ᵐ ω ∂(condExpKernel P 𝓠 ω₀), ω ∉ N ∧ ω ∈ R := hνN.and (hmemR hω₀R)
  have hrep := hasKilledRep_of_isSLEEvolutionUpTo (iL := iL) (iR := iR) hκ (hpt ω₀ hω₀N hω₀R).ordered (hE hω₀R)
    (by filter_upwards [hgood] with ω hω using (hpt ω hω.1 hω.2).killed)
    (by filter_upwards [hgood] with ω hω using (hpt ω hω.1 hω.2).trace)
  have hmap : (condExpKernel P 𝓠 ω₀).map (pieceSamp W VL VR ζ) =
      (condExpKernel P 𝓠 ω₀).map (pieceSamp W'' VL'' VR'' ζ) :=
    Measure.map_congr (by filter_upwards [hgood] with ω hω using samp_congr (hpt ω hω.1 hω.2).agree)
  rw [hmap]
  exact hrep

/-- **The comparison clause of a piece dilated by a past-measurable factor** (ruling R78's killed clause). Let the
piece have a stopped representation for the past `𝓠` with a `𝓠`-measurable stage event and start, measurable killed
samples, and paths continuous before the lifetime almost surely on the stage event. Then for every `𝓠`-measurable
time factor `C ≠ 0` and every `𝓠`-measurable start `y'` whose marks are, almost surely on the stage event, the marks
of `y` dilated by `C`, the piece `t ↦ (√C)⁻¹ X(C t)` with lifetime `ζ / C` and start `y'` obeys the comparison clause.
(Under almost every conditional law given `𝓠` the factor and `y'` are frozen, and the premise is invariant under
Brownian scaling by a fixed factor: `le_dilSec_of_prem`.) -/
theorem _root_.InteractingSLE.Sec5.CrossCond.StagedKCand.IsStoppedRep.compClauseK_dil (hκ : 0 < κ)
    (h : IsStoppedRep κ P 𝓠 R ρL ρR iL iR y W VL VR B ζ 𝓕 W' VL' VR' B') (hR : MeasurableSet[𝓠] R)
    (hy : Measurable[𝓠] y) (hobs : Measurable (pieceSamp W VL VR ζ)) {C : Ω → ℝ≥0} (hC : Measurable[𝓠] C)
    (hC0 : ∀ ω, C ω ≠ 0) {y' : Ω → Start nL nR} (hy' : Measurable[𝓠] y')
    (hy'e : ∀ᵐ ω ∂P, ω ∈ R → (y' ω).2 = (dilV (C ω) (y ω)).2)
    (hcont : ∀ᵐ ω ∂P, ω ∈ R → ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      (∀ i, ContinuousOn (VL i · ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧ ∀ k, ContinuousOn (VR k · ω) {t | (t : ℝ≥0∞) < ζ ω}) :
    CompClauseK κ P 𝓠 R ρL ρR iL iR y' (fun t ω => (√(C ω : ℝ))⁻¹ * W (C ω * t) ω)
      (fun i t ω => (√(C ω : ℝ))⁻¹ * VL i (C ω * t) ω) (fun k t ω => (√(C ω : ℝ))⁻¹ * VR k (C ω * t) ω)
      (fun ω => ζ ω / C ω) := by
  have hle : 𝓠 ≤ mΩ := h.le0.trans (𝓕.le 0)
  have hrep := h.ae_hasKilledRep hκ hR hy
  intro S hS p hprem A hA hAR
  set D : Ω → Start nL nR × Samp nL nR := fun ω => (y' ω, dilSamp (C ω) (pieceSamp W VL VR ζ ω)) with hDdef
  have hDm : Measurable D :=
    (hy'.mono hle le_rfl).prodMk (measurable_dilSamp_uncurry.comp ((hC.mono hle le_rfl).prodMk hobs))
  have hpt : ∀ᵐ ω₀ ∂P, ω₀ ∈ A → p ≤ condExpKernel P 𝓠 ω₀ (D ⁻¹' S) := by
    filter_upwards [hrep, ae_ae_condExpKernel_eq hle hy, ae_ae_condExpKernel_eq hle hy',
      ae_ae_condExpKernel_eq hle hC, hy'e] with ω₀ hr hyy hyy' hCC he hω₀A
    have hω₀R := hAR hω₀A
    have hcongr : condExpKernel P 𝓠 ω₀ (D ⁻¹' S) = condExpKernel P 𝓠 ω₀
        ((fun ω => (y ω, pieceSamp W VL VR ζ ω)) ⁻¹' dilSec (y' ω₀) (C ω₀) S) := by
      refine measure_congr ?_
      filter_upwards [hyy', hCC] with ω h1 h2
      show (D ω ∈ S) = ((y' ω₀, dilSamp (C ω₀) (pieceSamp W VL VR ζ ω)) ∈ S)
      rw [hDdef]
      dsimp only
      rw [h1, h2]
    rw [hcongr]
    exact le_condExpKernel_of_rep (full := false) hobs (measurableSet_dilSec (y' ω₀) (C ω₀) hS) hyy
      (fun Ω' mΩ' P' _ 𝓕' W' VL' VR' B' ζ' hE htr =>
        le_dilSec_of_prem hprem (hC0 ω₀) (he hω₀R) Ω' mΩ' P' 𝓕' W' VL' VR' B' ζ' hE htr) (hr hω₀R)
  have hae : (A ∩ D ⁻¹' S : Set Ω) =ᵐ[P] (A ∩ {ω | (y' ω, samp (fun t => (√(C ω : ℝ))⁻¹ * W (C ω * t) ω)
      (fun i t => (√(C ω : ℝ))⁻¹ * VL i (C ω * t) ω) (fun k t => (√(C ω : ℝ))⁻¹ * VR k (C ω * t) ω)
      (ζ ω / C ω)) ∈ S}) := by
    filter_upwards [hcont] with ω hω
    show (ω ∈ A ∧ D ω ∈ S) = (ω ∈ A ∧ _ ∈ S)
    by_cases hωA : ω ∈ A
    · obtain ⟨hw, hvL, hvR⟩ := hω (hAR hωA)
      rw [samp_scale (hC0 ω) hw hvL hvR]
    · simp only [hωA, false_and]
  calc p * P A = ∫⁻ _ in A, p ∂P := (setLIntegral_const A p).symm
    _ ≤ ∫⁻ ω₀ in A, condExpKernel P 𝓠 ω₀ (D ⁻¹' S) ∂P := setLIntegral_mono_ae' (hle _ hA) hpt
    _ = P (A ∩ D ⁻¹' S) := KernelTower.setLIntegral_condExpKernel hle hA (hDm hS)
    _ = _ := measure_congr hae

end Frozen

/-! ### Conditioning back and the almost-sure transfer -/

section Transfer

variable {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {iL : Fin nL} {iR : Fin nR}

/-- **A clause under a conditioned measure is a clause under the measure** on events inside the conditioning event. -/
theorem CompClauseK.of_cond {Ω : Type*} {𝓠 : MeasurableSpace Ω} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {A₀ : Set Ω} (hA₀ : MeasurableSet A₀) (h0 : μ A₀ ≠ 0) {R : Set Ω} (hRA : R ⊆ A₀)
    {y : Ω → Start nL nR} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (h : CompClauseK κ (μ[|A₀]) 𝓠 R ρL ρR iL iR y W VL VR ζ) :
    CompClauseK κ μ 𝓠 R ρL ρR iL iR y W VL VR ζ := by
  intro S hS p hp A hA hAR
  have hle := h S hS p hp A hA hAR
  rw [cond_apply hA₀, cond_apply hA₀] at hle
  have e1 : A₀ ∩ A = A := inter_eq_right.2 (hAR.trans hRA)
  have e2 : A₀ ∩ (A ∩ {ω | (y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)) ∈ S}) =
      A ∩ {ω | (y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)) ∈ S} :=
    inter_eq_right.2 (inter_subset_left.trans (hAR.trans hRA))
  rw [e1, e2, ← mul_assoc, mul_comm p, mul_assoc] at hle
  have hi0 : (μ A₀)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (measure_ne_top μ A₀)
  have hit : (μ A₀)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 h0
  exact (ENNReal.mul_le_mul_iff_right hi0 hit).1 hle

/-- **Transfer of the comparison clause along a common Borel observable, with almost-sure identifications.** The
laws of `Z` and `Z'` agree; every past event of the target stage event is almost surely the `Z`-preimage of an
`𝓜`-event inside `RΓ`; the target record is almost surely `o ∘ Z` on the stage event; and on the source the bound
holds for the `Z'`-preimages of these `𝓜`-events. -/
theorem compClauseK_transfer {Ω Ω' Γ : Type*} {𝓠 : MeasurableSpace Ω} {𝓜 : MeasurableSpace Γ}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [mΓ : MeasurableSpace Γ]
    {P : Measure Ω} {P' : Measure Ω'} {Z : Ω → Γ} {Z' : Ω' → Γ} (hZ : Measurable Z) (hZ' : Measurable Z')
    (hlaw : P.map Z = P'.map Z') (h𝓜 : 𝓜 ≤ mΓ) {RΓ : Set Γ}
    {o : Γ → Start nL nR × Samp nL nR} (ho : Measurable o) {R : Set Ω}
    {y : Ω → Start nL nR} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞}
    (hpast : ∀ A, MeasurableSet[𝓠] A → A ⊆ R → ∃ M, MeasurableSet[𝓜] M ∧ M ⊆ RΓ ∧ A =ᵐ[P] Z ⁻¹' M)
    (hobs : ∀ᵐ ω ∂P, ω ∈ R →
      (y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)) = o (Z ω))
    (h' : ∀ S : Set (Start nL nR × Samp nL nR), MeasurableSet S → ∀ p : ℝ≥0∞,
      CompPremiseFarK κ ρL ρR iL iR univ S p → ∀ M, MeasurableSet[𝓜] M → M ⊆ RΓ →
        p * P' (Z' ⁻¹' M) ≤ P' (Z' ⁻¹' M ∩ {ω | o (Z' ω) ∈ S})) :
    CompClauseK κ P 𝓠 R ρL ρR iL iR y W VL VR ζ := by
  intro S hS p hp A hA hAR
  obtain ⟨M, hM, hMR, hAM⟩ := hpast A hA hAR
  have hMm : MeasurableSet M := h𝓜 _ hM
  have hT : MeasurableSet (M ∩ o ⁻¹' S) := hMm.inter (ho hS)
  have e1 : P (Z ⁻¹' M) = P' (Z' ⁻¹' M) := by
    rw [← Measure.map_apply hZ hMm, hlaw, Measure.map_apply hZ' hMm]
  have e2 : P (Z ⁻¹' M ∩ {ω | o (Z ω) ∈ S}) = P' (Z' ⁻¹' M ∩ {ω | o (Z' ω) ∈ S}) := by
    have a : Z ⁻¹' M ∩ {ω | o (Z ω) ∈ S} = Z ⁻¹' (M ∩ o ⁻¹' S) := rfl
    have b : Z' ⁻¹' M ∩ {ω | o (Z' ω) ∈ S} = Z' ⁻¹' (M ∩ o ⁻¹' S) := rfl
    rw [a, b, ← Measure.map_apply hZ hT, hlaw, Measure.map_apply hZ' hT]
  have e3 : P (Z ⁻¹' M ∩ {ω | o (Z ω) ∈ S}) =
      P (A ∩ {ω | (y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)) ∈ S}) := by
    refine measure_congr ?_
    filter_upwards [hAM, hobs] with ω h1 h2
    show (ω ∈ Z ⁻¹' M ∧ o (Z ω) ∈ S) = (ω ∈ A ∧ _ ∈ S)
    by_cases hωA : ω ∈ A
    · have hm : ω ∈ Z ⁻¹' M := by rw [← h1]; exact hωA
      rw [h2 (hAR hωA)]
      simp only [hm, hωA, true_and]
    · have hm : ω ∉ Z ⁻¹' M := by rw [← h1]; exact hωA
      simp only [hm, hωA, false_and]
  rw [measure_congr hAM, e1, ← e3, e2]
  exact h' S hS p hp M hM hMR

/-- **The source bound from a comparison clause**: if every `𝓜`-event inside `RΓ` pulls back almost surely to a past
event of the source stage event, and the source record is almost surely `o ∘ Z'` there, the source clause gives the
bound needed by `compClauseK_transfer`. -/
theorem bound_of_compClauseK {Ω' Γ : Type*} {𝓠' : MeasurableSpace Ω'} {𝓜 : MeasurableSpace Γ}
    [MeasurableSpace Ω'] [MeasurableSpace Γ] {P' : Measure Ω'}
    {Z' : Ω' → Γ} {RΓ : Set Γ} {o : Γ → Start nL nR × Samp nL nR} {R' : Set Ω'} {y' : Ω' → Start nL nR}
    {W' : ℝ≥0 → Ω' → ℝ}
    {VL' : Fin nL → ℝ≥0 → Ω' → ℝ} {VR' : Fin nR → ℝ≥0 → Ω' → ℝ} {ζ' : Ω' → ℝ≥0∞}
    (hG : CompClauseK κ P' 𝓠' R' ρL ρR iL iR y' W' VL' VR' ζ')
    (hpast : ∀ M, MeasurableSet[𝓜] M → M ⊆ RΓ → ∃ A, MeasurableSet[𝓠'] A ∧ A ⊆ R' ∧ A =ᵐ[P'] Z' ⁻¹' M)
    (hobs : ∀ᵐ ω ∂P', ω ∈ R' → Z' ω ∈ RΓ →
      (y' ω, samp (W' · ω) (fun i t => VL' i t ω) (fun k t => VR' k t ω) (ζ' ω)) = o (Z' ω)) :
    ∀ S : Set (Start nL nR × Samp nL nR), MeasurableSet S → ∀ p : ℝ≥0∞,
      CompPremiseFarK κ ρL ρR iL iR univ S p → ∀ M, MeasurableSet[𝓜] M → M ⊆ RΓ →
        p * P' (Z' ⁻¹' M) ≤ P' (Z' ⁻¹' M ∩ {ω | o (Z' ω) ∈ S}) := by
  intro S hS p hp M hM hMR
  obtain ⟨A, hA, hAR, hAM⟩ := hpast M hM hMR
  have e3 : P' (A ∩ {ω | (y' ω, samp (W' · ω) (fun i t => VL' i t ω) (fun k t => VR' k t ω) (ζ' ω)) ∈ S}) =
      P' (Z' ⁻¹' M ∩ {ω | o (Z' ω) ∈ S}) := by
    refine measure_congr ?_
    filter_upwards [hAM, hobs] with ω h1 h2
    show (ω ∈ A ∧ _ ∈ S) = (ω ∈ Z' ⁻¹' M ∧ o (Z' ω) ∈ S)
    by_cases hωA : ω ∈ A
    · have hm : ω ∈ Z' ⁻¹' M := by rw [← h1]; exact hωA
      rw [h2 (hAR hωA) (hMR hm)]
      simp only [hm, hωA, true_and]
    · have hm : ω ∉ Z' ⁻¹' M := by rw [← h1]; exact hωA
      simp only [hm, hωA, false_and]
  rw [← measure_congr hAM, ← e3]
  exact hG S hS p hp A hA hAR

end Transfer

/-! ### Lusin separation for saturated sets -/

section Lusin

/-- **A Borel set saturated for a Borel map is a preimage** (Lusin separation). On a standard Borel space `X`, let
`Y : X → V` be Borel into a countably separated space and `D`, `G` Borel. If membership in `D` of points of `G` is
determined by their `Y`-values, then `D ∩ G = G ∩ Y⁻¹(C)` for a Borel `C`. -/
theorem exists_measurableSet_inter_eq {X V : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace V] [MeasurableSpace.CountablySeparated V] {Y : X → V} (hY : Measurable Y) {D G : Set X}
    (hD : MeasurableSet D) (hG : MeasurableSet G)
    (hsat : ∀ x ∈ D ∩ G, ∀ x' ∈ G, Y x' = Y x → x' ∈ D) :
    ∃ C : Set V, MeasurableSet C ∧ D ∩ G = G ∩ Y ⁻¹' C := by
  obtain ⟨τ, _, _, _⟩ := exists_opensMeasurableSpace_of_countablySeparated V
  have ha := (hD.inter hG).analyticSet_image hY
  have hb := (hG.diff hD).analyticSet_image hY
  have hdisj : Disjoint (Y '' (D ∩ G)) (Y '' (G \ D)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨x', hx', he⟩
    exact hx'.2 (hsat x hx x' hx'.1 he)
  obtain ⟨C, hsub, hCd, hCm⟩ := ha.measurablySeparable hb hdisj
  refine ⟨C, hCm, Subset.antisymm (fun x hx => ⟨hx.2, hsub ⟨x, hx, rfl⟩⟩) fun x hx => ⟨?_, hx.1⟩⟩
  by_contra hxD
  exact Set.disjoint_left.1 hCd ⟨x, ⟨hx.1, hxD⟩, rfl⟩ hx.2

end Lusin

end InteractingSLE.Sec5.CrossCond.StagedRepJ
