/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6RestartProofR1
import InteractingSLE.Spec.Supplement.GB6LawFinal

/-!
# Proposition GB6, step (d): everything but the pathwise identification

Packet PROVE-GB6-RESTART. PROVE-GB6D reduced `GB6RestartStatement` (GB6's conditional-law half) to the named input
`GB6CondDetStatement` (step (d): the σ-algebra of the marked prefix, the conditional word and its junctions, their
measurability, the word clauses (W), the conditional Gaussian law (R1), and the identification (Det)). This file proves
all of (d) except the pathwise identification (Det), for the explicit conditional word:

* the σ-algebra `𝒢` is that of the record of the flow prefix at the own time `s`;
* the event `M` reads from the record "`s` is before the lifetime, the tip is interior, and both seed images are
  nondegenerate"; almost surely it is the event `{s < ζα, α(s) ∈ ℍ}` (`gb6_rec_spec`: the seed images are
  nondegenerate at an interior tip);
* the conditional word is the returned stop word `gb6WordOfRec` and the junctions are `jLOfRec`, `jROfRec`; (W)'s word
  clauses are `isGB6AdmData_gb6WordOfRec` (with the counterflow's admissibility transported by `gb6_admL`, `gb6_admR`)
  and `isGB6TailData_gb6WordOfRec`;
* (R1) is `ae_condExp_returnRecField` (and is vacuous when the seed is at threshold: then `ζα = 0`).

What remains is **`GB6RelDetStatement`** (named): the good-code clause of (W) and (Det), almost surely on
`{s < ζα, α(s) ∈ ℍ}`, for the explicit conditional word `gb6Word κ θ c s Wα`. It is the counterflow's conditional
coupling with the conditional field before its first contact with the flow prefix (Astra's follow-up 3, Q3 §§3.2–3.7).

## Main results

* `gb6_rec_spec`: the record of the flow prefix on one sample before its lifetime;
* **`GB6RelDetStatement`** (named input);
* **`gb6CondDetStatement_of_relDet`**: `GB6RelDetStatement → GB6CondDetStatement`;
* **`gb6RestartStatement_of_relDet`**, `gb6FirstContactStatement_of_relDet`: GB6's conditional-law half and
  first-contact assertion from it (with Theorems 1.2–1.3 at `16/κ`, as in `gb6RestartStatement_of_param_complete`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Supp8

namespace GB6

open Restart Exist.Staged Exist.StagedLaw Sec7.StripSysField Theorem14.GW2JointKernel

/-! ### The record of the flow prefix on one sample -/

section Sample

variable {Ω : Type*} (s : ℝ≥0) {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {α : Ω → ℝ≥0 → ℂ} {ω : Ω}

/-- **The record of the flow prefix on one sample before its lifetime**: the record driver is a continuous driver
agreeing with the flow driver on `[0, s]`, its trace at `s` is the tip, its Loewner chart gives the chart of `U`, its
seed images are the junctions, and they are nondegenerate at an interior tip. -/
theorem gb6_rec_spec (hW0 : W 0 ω = 0) (hWc : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hα : IsGeneratingTrace (fun t => W t ω) (ζ ω) (α ω)) (hs : (s : ℝ≥0∞) < ζ ω) :
    LP.traceAt s (fun t : ℝ≥0 => rdrv (recOf (s : ℝ≥0∞) (cfE s W ζ ω)) t) = α ω s ∧
      ownComponentChart (rdrv (recOf (s : ℝ≥0∞) (cfE s W ζ ω))) s =
        ownComponentChart (fun r : ℝ => W r.toNNReal ω) s ∧
      jLOfRec (recOf (s : ℝ≥0∞) (cfE s W ζ ω)) = junctionL (fun r : ℝ => W r.toNNReal ω) s ∧
      jROfRec (recOf (s : ℝ≥0∞) (cfE s W ζ ω)) = junctionR (fun r : ℝ => W r.toNNReal ω) s ∧
      (α ω s ∈ H → 0 < markPos (rdrv (recOf (s : ℝ≥0∞) (cfE s W ζ ω)))
          (rtime (recOf (s : ℝ≥0∞) (cfE s W ζ ω))) 0 ∧
        markPosL (rdrv (recOf (s : ℝ≥0∞) (cfE s W ζ ω))) (rtime (recOf (s : ℝ≥0∞) (cfE s W ζ ω))) 0 < 0) := by
  set r := recOf (s : ℝ≥0∞) (cfE s W ζ ω) with hr
  set U := rdrv r with hU
  have hUc : Continuous U := continuous_rdrv r
  have hU0 : U 0 = 0 := rdrv_zero r
  have hrt : rtime r = s := rtime_recOf_cfE s hs
  have hUW : ∀ x : ℝ, x ≤ s → U x = W x.toNNReal ω := fun x hx => rdrv_recOf_cfE s hW0 hWc hs hx
  obtain ⟨t₂, hst₂, ht₂⟩ := exists_real_btwn_of_lt hs
  set U' := frozenDrive (fun t => W t ω) t₂ with hU'def
  have hU' : Continuous U' := continuous_frozenDrive_of_lt hWc ht₂
  have ht₂0 : (0 : ℝ) ≤ t₂ := s.coe_nonneg.trans hst₂.le
  have hU'0 : U' 0 = 0 := by rw [hU'def, frozenDrive_zero ht₂0, hW0]
  have hU'W : ∀ x ∈ Icc (0 : ℝ) t₂, U' x = W x.toNNReal ω := fun x hx => frozenDrive_eq hx
  have hwc : ContinuousOn (fun r : ℝ => W r.toNNReal ω) (Icc 0 t₂) :=
    hU'.continuousOn.congr fun x hx => (hU'W x hx).symm
  have hagree : EqOn U (fun r : ℝ => W r.toNNReal ω) (Icc 0 s) := fun x hx => hUW x hx.2
  have hagree' : EqOn U U' (Icc 0 s) := fun x hx => by
    rw [hUW x hx.2, hU'W x ⟨hx.1, hx.2.trans hst₂.le⟩]
  have hinv : QuantumZipper.fwdMapInv U s = QuantumZipper.fwdMapInv (fun r : ℝ => W r.toNNReal ω) s :=
    funext fun z => LocalExt.fwdMapInv_congr_of_continuousOn hUc.continuousOn hwc s.coe_nonneg hst₂ hagree z
  have hinv' : QuantumZipper.fwdMapInv U s = QuantumZipper.fwdMapInv U' s :=
    funext fun z => LocalExt.fwdMapInv_congr_of_continuousOn hUc.continuousOn hU'.continuousOn s.coe_nonneg
      hst₂ hagree' z
  have hbR : baseR (fun r : ℝ => W r.toNNReal ω) s = baseR U s :=
    baseR_congr hUc s.coe_nonneg fun x hx => (hagree hx).symm
  have hbL : baseL (fun r : ℝ => W r.toNNReal ω) s = baseL U s :=
    baseL_congr hUc s.coe_nonneg fun x hx => (hagree hx).symm
  have hmR : markPos U (rtime r) 0 = baseR U s := by
    rw [hrt]; exact markPos_zero_eq_baseR hUc hU0 s.coe_nonneg
  have hmL : markPosL U (rtime r) 0 = baseL U s := by
    rw [hrt]; exact markPosL_zero_eq_baseL hUc hU0 s.coe_nonneg
  refine ⟨?_, ?_, ?_, ?_, fun hαs => ?_⟩
  · rw [← LP.traceAt_eq_of_isGeneratingTrace hα hWc hW0 hs]
    refine LP.traceAt_congr fun t ht => ?_
    rw [hUW (t : ℝ) (by exact_mod_cast ht), Real.toNNReal_coe]
  · unfold ownComponentChart
    rw [LocalExt.id_loewner_congr hUc.continuousOn hwc s.coe_nonneg hst₂ hagree]
  · rw [jLOfRec, junctionL, hmR, hbR]
  · rw [jROfRec, junctionR, hmL, hbL]
  · have hB : HasBdryLimits (QuantumZipper.fwdMapInv U s) := by
      rw [hinv']
      exact (hα.isLoewnerTraceLT ht₂).hasBdryLimits hU' hU'0 s.coe_nonneg hst₂
    have htip : Tendsto (QuantumZipper.fwdMapInv U s) (𝓝[H] 0) (𝓝 (α ω s)) := by
      rw [hinv]
      exact hα.tendsto_fwdMapInv_tip hWc hW0 hs
    rw [hmR, hmL]
    exact ⟨baseR_pos_of_tip hUc hU0 s.coe_nonneg hB hαs htip, baseL_neg_of_tip hUc hU0 s.coe_nonneg hB hαs htip⟩

end Sample

/-! ### The residual: the pathwise identification for the explicit conditional word -/

/-- The record of GB6's flow prefix at the own time `s` (the regularized driver read at `s`). -/
def gb6Rec {Ω : Type*} (s : ℝ≥0) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (ω : Ω) : RecData :=
  recOf (s : ℝ≥0∞) (cfE s Wα ζα ω)

/-- **Named input: GB6's (Det), for the explicit conditional word** (supplement p. 519–520: "Theorem 2.4 and
integrated uniqueness identify the relative driving law through every such stopped buffer"; Astra's follow-up 3, Q3
§§3.2–3.7: marked locality by censored records, the mean at deterministic times, optional Gaussian kernels, relative
locality with filled hulls, random charts and the time-changed filtration, Theorem 2.4 in that filtration). Binders of
`GB6CondDetStatement` verbatim, and a word `c` representing the flow data `(b, J)`. Almost surely on
`{s < ζα, α(s) ∈ ℍ}`, with `β = gb6Word κ θ c s Wα` (the conditional word: the flow's stop word returned through `R`):

* the canonical driver code `F (β, Hc)` of the conditional field is good, and
* **before the first contact `T_c`** of the physical counterflow with `α([0, s])`, the canonical counterflow of the
  conditional field generates the chart images `Ψ(K'_t)` of the physical counterflow hulls in the relative clock.

These are exactly the clauses of `GB6CondDetStatement` that `gb6CondDetStatement_of_relDet` does not prove: the
σ-algebra, the event, the word, the junctions, their measurability, the word's sortedness, admissibility and tails,
the junction identification and (R1) are proved there. -/
def GB6RelDetStatement : Prop :=
  ∀ (κ θ : ℝ), 0 < κ → κ < 4 → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζ ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ)
    (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsPiecewiseConstantBoundaryData b' J' →
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω)) →
    IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ →
    (∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l) →
    (∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l) →
    (∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop) →
    IsFlowLineDriver κ b J θ P h Wα ζα →
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) →
    ∀ (s : ℝ≥0) (Hc : Ω → DistOn upperHalfPlaneOpens), Measurable Hc →
    (∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      IsChartTransport (ownComponentChart (fun r : ℝ => Wα r.toNNReal ω) s) (-1)
        (-(Real.pi * QuantumZipper.chiC κ)) (QuantumZipper.chiC (16 / κ)) (h ω) (Hc ω)) →
    ∀ F : BoundaryWord × DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞,
      IsCanonicalDriverCode (16 / κ) 0 F →
    ∀ c : BoundaryWord, c.jumps = J → (∀ y ∉ J, c.fn y = b y) →
      ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
        IsGoodDrvCode (F (gb6Word κ θ c s (fun t => Wα t ω), Hc ω)) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
            ((fun t => (α ω t : OnePoint ℂ)) '' Icc 0 s) →
          QuantumZipper.fwdHull (fun r : ℝ => drvDec (F (gb6Word κ θ c s (fun t => Wα t ω), Hc ω)) r.toNNReal)
              (relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t) =
            relMap (fun r : ℝ => Wα r.toNNReal ω) s '' QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) t

/-! ### The event and the record facts -/

/-- The event read from a record: `s` before the lifetime, interior tip, nondegenerate seed images. -/
def gb6TS (s : ℝ≥0) : Set RecData :=
  {r | r.2.2 = false ∧ LP.traceAt s (fun t : ℝ≥0 => rdrv r t) ∈ H ∧
    0 < markPos (rdrv r) (rtime r) 0 ∧ markPosL (rdrv r) (rtime r) 0 < 0}

theorem measurableSet_gb6TS (s : ℝ≥0) : MeasurableSet (gb6TS s) :=
  (measurableSet_eq_fun (measurable_snd.comp measurable_snd) measurable_const).inter
    ((((LP.measurable_traceAt s).comp (measurable_pi_iff.2 fun t => measurable_rdrv_apply (t : ℝ)))
      QuantumZipper.isOpen_H.measurableSet).inter
      ((measurableSet_lt measurable_const measurable_markPos_rec).inter
        (measurableSet_lt measurable_markPosL_rec measurable_const)))

/-- The facts of the record on one sample before the lifetime (`gb6_rec_spec`, `recOf_cfE_eq`). -/
def GB6RecGood (s : ℝ≥0) {Ω : Type*} (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (α : Ω → ℝ≥0 → ℂ) (ω : Ω) : Prop :=
  (LP.traceAt s (fun t : ℝ≥0 => rdrv (gb6Rec s Wα ζα ω) t) = α ω s ∧
    ownComponentChart (rdrv (gb6Rec s Wα ζα ω)) s = ownComponentChart (fun r : ℝ => Wα r.toNNReal ω) s ∧
    jLOfRec (gb6Rec s Wα ζα ω) = junctionL (fun r : ℝ => Wα r.toNNReal ω) s ∧
    jROfRec (gb6Rec s Wα ζα ω) = junctionR (fun r : ℝ => Wα r.toNNReal ω) s ∧
    (α ω s ∈ H → 0 < markPos (rdrv (gb6Rec s Wα ζα ω)) (rtime (gb6Rec s Wα ζα ω)) 0 ∧
      markPosL (rdrv (gb6Rec s Wα ζα ω)) (rtime (gb6Rec s Wα ζα ω)) 0 < 0)) ∧
  gb6Rec s Wα ζα ω = recOf (s : ℝ≥0∞) (fun t => Wα t ω, ⊤) ∧ rtime (gb6Rec s Wα ζα ω) = s

theorem ae_gb6RecGood {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {α : Ω → ℝ≥0 → ℂ}
    (hfl : IsFlowLineDriver κ b J θ P h Wα ζα) (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (s : ℝ≥0) : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → GB6RecGood s Wα ζα α ω := by
  filter_upwards [ae_driver_zero_continuousOn hfl, hα] with ω hω hαω hs
  exact ⟨gb6_rec_spec s hω.1 hω.2 hαω hs, recOf_cfE_eq s hω.1 hω.2 hs, rtime_recOf_cfE s hs⟩

/-- **The record event is the interior-tip event before the lifetime.** -/
theorem mem_gb6TS_iff {s : ℝ≥0} {Ω : Type*} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {α : Ω → ℝ≥0 → ℂ} {ω : Ω}
    (hg : (s : ℝ≥0∞) < ζα ω → GB6RecGood s Wα ζα α ω) :
    ((s : ℝ≥0∞) < ζα ω ∧ α ω s ∈ H) ↔ gb6Rec s Wα ζα ω ∈ gb6TS s := by
  constructor
  · rintro ⟨hs, hαs⟩
    obtain ⟨⟨htr, -, -, -, hpos⟩, -, -⟩ := hg hs
    exact ⟨(flag_recOf_cfE s).2 hs, by rw [htr]; exact hαs, hpos hαs⟩
  · rintro ⟨hfl', htr', -, -⟩
    have hs := (flag_recOf_cfE s).1 hfl'
    obtain ⟨⟨htr, -⟩, -, -⟩ := hg hs
    exact ⟨hs, htr ▸ htr'⟩

/-- On an interior-tip sample, the chart field is the returned record field. -/
theorem eq_returnField_of_gb6RecGood {κ : ℝ} (hκ : 0 < κ) {s : ℝ≥0} {Ω : Type*} {Wα : ℝ≥0 → Ω → ℝ}
    {ζα : Ω → ℝ≥0∞} {α : Ω → ℝ≥0 → ℂ} {ω : Ω} (hg : GB6RecGood s Wα ζα α ω) {f Hcω : DistOn upperHalfPlaneOpens}
    (hHcω : IsChartTransport (ownComponentChart (fun r : ℝ => Wα r.toNNReal ω) s) (-1)
      (-(Real.pi * chiC κ)) (chiC (16 / κ)) f Hcω) :
    Hcω = returnField (Real.pi * chiC κ) (chiC κ) (recField κ (gb6Rec s Wα ζα ω) f) := by
  obtain ⟨⟨-, hchart, -⟩, -, hrt⟩ := hg
  have h₂ : IsChartTransport (Chart.id.loewner (rdrv (gb6Rec s Wα ζα ω)) s) 1 0 (chiC κ) f
      (recField κ (gb6Rec s Wα ζα ω) f) := by
    have h1 := isChartTransport_recField κ (gb6Rec s Wα ζα ω) f
    rwa [recChart_eq, hrt] at h1
  have h3 := isChartTransport_ownComponentChart_returnField hκ (continuous_rdrv _) (rdrv_zero _) s.coe_nonneg h₂
  have hconf := isConformal_ownComponentChart (continuous_rdrv (gb6Rec s Wα ζα ω)) (rdrv_zero _) s.coe_nonneg
  rw [hchart] at h3 hconf
  exact hHcω.unique hconf h3

/-! ### (R1) and (W) for the record event -/

/-- **(R1) of GB6's (d)**: on the record event, conditionally on the record, the chart field has the Gaussian
characteristic functional of the conditional word (vacuous when the flow's seed is at threshold: then `ζα = 0`). -/
theorem gb6_condDet_r1 {κ θ : ℝ} (hκ : 0 < κ) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {b : ℝ → ℝ} {J : Finset ℝ}
    (hG : IsGFFWithBoundaryData P h b J) {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {α : Ω → ℝ≥0 → ℂ}
    {c : BoundaryWord} (hflc : IsFlowLineDriver κ c.fn c.jumps θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) (s : ℝ≥0)
    {Hc : Ω → DistOn upperHalfPlaneOpens} (hHcm : Measurable Hc)
    (hHc : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      IsChartTransport (ownComponentChart (fun r : ℝ => Wα r.toNNReal ω) s) (-1)
        (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (Hc ω)) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, gb6Rec s Wα ζα ω ∈ gb6TS s →
      P[fun ω' => Complex.exp (Complex.I * (Hc ω' φ : ℂ)) | MeasurableSpace.comap (gb6Rec s Wα ζα) inferInstance] ω =
        gaussCF (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)) φ := by
  by_cases hseed : ForceWord.ThresholdCondition (flowLineRhoL κ c.fn c.jumps 0 θ)
    (flowLineRhoR κ c.fn c.jumps 0 θ) 0 (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
  · obtain ⟨_, _, _, _, _, _, hC⟩ := hflc
    have h0 := IsIntegratedSLEEvolution.ae_lifetime_eq_zero_of_threshold hC.1 hseed
    filter_upwards [h0] with ω hω hωM
    exfalso
    have hs := (flag_recOf_cfE s).1 hωM.1
    rw [hω] at hs
    exact ENNReal.not_lt_zero hs
  have hrecm : Measurable (gb6Rec s Wα ζα) := (measurable_recOf_cfE hflc s).2
  have hM : MeasurableSet[MeasurableSpace.comap (gb6Rec s Wα ζα) inferInstance] (gb6Rec s Wα ζα ⁻¹' gb6TS s) :=
    ⟨gb6TS s, measurableSet_gb6TS s, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : Ω → DistOn upperHalfPlaneOpens,
      Y = fun ω => returnField (Real.pi * chiC κ) (chiC κ) (recField κ (gb6Rec s Wα ζα ω) (h ω)) := ⟨_, rfl⟩
  have hYm : Measurable Y := by
    have h1 := (measurable_recField κ).comp (hrecm.prodMk hG.1)
    have h2 := (measurable_returnField (Real.pi * chiC κ) (chiC κ)).comp h1
    rw [hYdef]
    exact h2
  have hident : ∀ᵐ ω ∂P, ω ∈ gb6Rec s Wα ζα ⁻¹' gb6TS s → Hc ω = Y ω := by
    filter_upwards [ae_gb6RecGood hflc hα s, hHc] with ω hg hHcω hωM
    obtain ⟨hs, hsH⟩ := (mem_gb6TS_iff hg).2 hωM
    have e := eq_returnField_of_gb6RecGood hκ (hg hs) (hHcω hs hsH)
    rw [e, hYdef]
  have hint₁ : Integrable (fun ω => Complex.exp (Complex.I * (Hc ω φ : ℂ))) P :=
    GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hHcm)
  have hint₂ : Integrable (fun ω => Complex.exp (Complex.I * (Y ω φ : ℂ))) P :=
    GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hYm)
  have h1 := ae_condExp_eq_of_ae_eq_on (P := P) hM hint₁ hint₂ (by
    filter_upwards [hident] with ω hω hωM
    rw [hω hωM])
  have h2 := ae_condExp_returnRecField hκ hflc hseed s φ
  filter_upwards [h1, h2] with ω e1 e2 hωM
  rw [e1 hωM, hYdef]
  exact e2

/-- **The word clauses of (W) on the record event** (sortedness, admissibility, tails). -/
theorem gb6_word_of_mem {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₁ : -(Real.pi / 2) ≤ θ) (hθ₂ : θ ≤ Real.pi / 2)
    (c : BoundaryWord) {s : ℝ≥0} {r : RecData} (hr : r ∈ gb6TS s) (E : Finset ℝ)
    (hcL : ∀ u, u < 0 → u ∉ E → u ∉ c.jumps → -bigLambda κ < -c.fn u + Real.pi * chiC κ)
    (hcR : ∀ u, 0 < u → u ∉ E → u ∉ c.jumps → -c.fn u - Real.pi * chiC κ < bigLambda κ) :
    (gb6WordOfRec κ θ c r).IsSorted ∧ IsGB6AdmData κ (gb6WordOfRec κ θ c r) ∧
      IsGB6TailData κ (gb6WordOfRec κ θ c r) (jLOfRec r) (jROfRec r) := by
  obtain ⟨-, -, hR, hL⟩ := hr
  exact ⟨isSorted_gb6WordOfRec κ θ c r, isGB6AdmData_gb6WordOfRec hκ hκ4 hθ₁ hθ₂ c r hR hL E hcL hcR,
    isGB6TailData_gb6WordOfRec hκ hκ4 hθ₁ hθ₂ c r hR hL⟩

/-! ### GB6's (d) from the residual -/

/-- **GB6's step (d) from its pathwise identification.** `GB6RelDetStatement` (the good-code clause and (Det) for the
explicit conditional word) implies `GB6CondDetStatement`: `𝒢` is the σ-algebra of the record of the flow prefix at
`s`, `M` reads from it "`s` before the lifetime, interior tip, nondegenerate seed images" (almost surely the event
`{s < ζα, α(s) ∈ ℍ}`), the word is the returned stop word and the junctions are read from its seed positions. -/
theorem gb6CondDetStatement_of_relDet (hD : GB6RelDetStatement.{u}) : GB6CondDetStatement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf hadmL hadmR hcomp hfl hα s Hc
    hHcm hHc F hF
  obtain ⟨c, hcJ, hcb⟩ := BoundaryWord.exists_fn_eq hb
  have hDω := hD κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf hadmL hadmR hcomp hfl
    hα s Hc hHcm hHc F hF c hcJ hcb
  have hG' : IsGFFWithBoundaryData P h' b' J' :=
    Theorem14.GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver (by positivity) hb' hcf
  have hflc : IsFlowLineDriver κ c.fn c.jumps θ P h Wα ζα :=
    (isFlowLineDriver_congr_of_eqOn hb c.isPiecewiseConstantBoundaryData J hcb).2 hfl
  have hrecm : Measurable (gb6Rec s Wα ζα) := (measurable_recOf_cfE hfl s).2
  have hRec := ae_gb6RecGood hfl hα s
  have hR1 := fun φ => gb6_condDet_r1 hκ hG hflc hα s hHcm hHc φ
  refine ⟨⟨MeasurableSpace.comap (gb6Rec s Wα ζα) inferInstance, hrecm.comap_le⟩, gb6Rec s Wα ζα ⁻¹' gb6TS s,
    fun ω => gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω), fun ω => jLOfRec (gb6Rec s Wα ζα ω),
    fun ω => jROfRec (gb6Rec s Wα ζα ω), ⟨gb6TS s, measurableSet_gb6TS s, rfl⟩,
    (measurable_gb6WordOfRec κ θ c).comp (comap_measurable _), measurable_jLOfRec.comp (comap_measurable _),
    measurable_jROfRec.comp (comap_measurable _), ?_, hR1, ?_⟩
  · filter_upwards [hRec, hDω] with ω hg hDω' hωM
    obtain ⟨hs, hsH⟩ := (mem_gb6TS_iff hg).2 hωM
    obtain ⟨h1, h2, h3⟩ := gb6_word_of_mem hκ hκ4 hθ₁ hθ₂ c hωM (J'.image fun w => -w⁻¹)
      (gb6_admL hκ hb hG hb' hG' hT hadmR hcJ hcb) (gb6_admR hκ hb hG hb' hG' hT hadmL hcJ hcb)
    have hβ : gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω) = gb6Word κ θ c s (fun t => Wα t ω) := by
      rw [gb6Word, (hg hs).2.1]
    refine ⟨h1, h2, h3, ?_⟩
    rw [hβ]
    exact (hDω' hs hsH).1
  · filter_upwards [hRec, hDω] with ω hg hDω' hs hsH
    obtain ⟨⟨-, -, hjL, hjR, -⟩, hrec, -⟩ := hg hs
    have hβ : gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω) = gb6Word κ θ c s (fun t => Wα t ω) := by
      rw [gb6Word, hrec]
    refine ⟨(mem_gb6TS_iff hg).1 ⟨hs, hsH⟩, hjL, hjR, ?_⟩
    rw [hβ]
    exact (hDω' hs hsH).2

/-- **GB6's conditional-law half** (`GB6RestartStatement`) from the pathwise identification (conditional helper):
`gb6CondDetStatement_of_relDet` and PROVE-GB6D's `gb6RestartStatement_of_param_complete` (Theorems 1.2–1.3 as
hypotheses, and Theorem 1.3 at `16/κ`; GB6 serves Theorem 1.4). -/
theorem gb6RestartStatement_of_relDet (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hC : CompleteSixteenDivStatement) (hD : GB6RelDetStatement.{u}) :
    GB6RestartStatement.{u} :=
  gb6RestartStatement_of_param_complete h12p h13 hC (gb6CondDetStatement_of_relDet hD)

/-- **GB6's first-contact assertion** from the pathwise identification (conditional helper). -/
theorem gb6FirstContactStatement_of_relDet (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hC : CompleteSixteenDivStatement) (hD : GB6RelDetStatement.{u}) :
    GB6FirstContactStatement.{u} :=
  gb6FirstContactStatement_of_param_complete h12p h13 hC (gb6CondDetStatement_of_relDet hD)

end GB6

end Supp8

end InteractingSLE
