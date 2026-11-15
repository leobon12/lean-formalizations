/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdExt
import InteractingSLE.Spec.Supplement.GW2aPieceChart

/-!
# GW2's relative determination, part 2: GW2's (Det) from versions and the relative safe law

Packet PROVE-GW2-RELDET. GW2's root determination `GW2JointKernel.GW2JointDetC2Statement` (the flow line read in the
joint chart of a stopped counterflow prefix is, before its lifetime and its first contact, the canonical flow line of
the conditional field) is GB6's determination with the two curves exchanged (PROVE-GW2-FABLE). GB6's chain ends with
GB6's engine (Astra's follow-up 3, Q3; supplement pp. 519–520): K2's inputs (S), (L) for every R-form version of the
relative exploration, under the joint law of the record and the relative variable, give the stopped driver matches,
and announced versions exhausting the pre-contact relative clock give the hull identity. Here this ending is proved
for GW2, with the two differences of GW2's explored flow line:

* its LIFETIME may be finite: GB6's versions are read for the EXTENDED flow driver `regW s Wα ζα` with its trace
  `extTr s Wα ζα α` (`GW2RdExt`: the flow before `ζα`, frozen from `ζα` on), capped at the flow's lifetime, and they
  exhaust the relative clock before the END TIME `min(ζα, T_c)` (`gw2End`); back on the flow,
  `hull_clock_contact_of_ext`, and the deterministic step `GW2Rd.fwdHull_drvDec_eq_of_family`;
* its ANGLE `θ` is read as a height shift (`GW2RdShift`): the engine runs at angle `0` on the raised word
  `gw2Word κ θ c′ = jointWord + θχ` and the raised chart field `Hc + θχ`, with the shifted code `shiftCode κ θ F`;
* an inadmissible seed gives `ζα = 0` (`IsIntegratedSLEEvolution.ae_lifetime_eq_zero_of_threshold`): then the
  hull clause is empty.

Definitions: `gw2End`, `gw2Clock`, `gw2Word`, **`IsGW2RelVersion`** (GB6's announced R-form version
`Q3Stop.IsGB6RelVersionA` for the extended flow and the counterflow record, capped at `ζα`). Named statements (NOT
proved here), both for an admissible seed of the flow line:

* **`GW2RdVersionStatement`**: exhausting capped versions exist (GB6's `Q3Stop.GB6RelVersionAStatement` with the
  curves exchanged; the gauge must also detect the flow's continuation threshold);
* **`GW2RdSafeStatement`**: GB6's relative safe law (`Q3Stop.HasRelSafe`, K2's (S), (L), the threshold clause and
  integrability) for every such version and word type of the raised word.

Proved:

* `ae_isStopDrvMatch_gw2`: the stopped driver match of every version, from the safe law (the engine
  `Q3Stop.ae_isStopDrvMatch_of_hasRelSafe`, the shifted code, countably many word types);
* **`gw2JointDetC2Statement_of_versions_safe`**: `GW2JointDetC2Statement` from Theorems 1.2–1.3 at universe `0` (for
  the angle-`θ` good code), `GW2RdVersionStatement` and `GW2RdSafeStatement`.

R48: GW2 serves Theorem 1.4; Theorems 1.2–1.3 enter only as hypotheses. Conditional helpers with distinct names.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Restart Sec2.Assembly Exist.Staged Exist.StagedLaw Sec7.StripSysField Supp8.GB6 Supp8.GB6.RelDrv
  Supp8.GB6.HullId Theorem14.GW2JointKernel GW2TipSystem

/-! ### GW2's end time, clock, raised word and versions -/

section Defs

variable {Ω : Type*}

/-- **GW2's end time**: the flow line's lifetime or its first contact with the inverted counterflow prefix
`R(γ[0, s])`, whichever comes first. -/
def gw2End (s : ℝ≥0) (ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ) (ω : Ω) : ℝ≥0∞ :=
  min (ζα ω) (firstContactTime (fun t => (α ω t : OnePoint ℂ))
    ((fun r => sphereInv (γ ω r : OnePoint ℂ)) '' Icc 0 s))

/-- **GW2's relative clock** `a(t) = hcap(Ψ(K^α_t))/2`, `Ψ = relMap W s`. -/
def gw2Clock (s : ℝ≥0) (W Wα : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ≥0) : ℝ :=
  relClock (fun r : ℝ => W r.toNNReal ω) s (fun r : ℝ => Wα r.toNNReal ω) t

/-- **GW2's raised conditional word**: the joint-chart word of the counterflow record, raised by `θχ(κ)` (the angle
of the flow line read as a height). -/
def gw2Word (κ θ : ℝ) (c' : BoundaryWord) (r : RecData) : BoundaryWord :=
  upW (θ * chiC κ) (jointWordOfRec (specOffset κ) κ c' r)

theorem measurable_gw2Word (κ θ : ℝ) (c' : BoundaryWord) : Measurable (gw2Word κ θ c') :=
  (measurable_upW _).comp (measurable_jointWordOfRec _ _ _)

/-- **An announced R-form version of GW2's relative exploration, capped at the flow's lifetime.** GB6's announced
R-form version (`Q3Stop.IsGB6RelVersionA`) with the curves exchanged: the explored curve is the EXTENDED flow driver
`regW s Wα ζα` with its trace `extTr s Wα ζα α` (`GW2RdExt`: the flow before `ζα`, frozen from `ζα` on), the
retained curve the counterflow `(W, ζ, γ)` with its record `gb6Rec s W ζ`; and almost surely on `{γ(s) ∈ ℍ}` every
relative time before the stop is the relative clock of a time before the flow's lifetime `ζα` (so the stop never
reads the frozen part). -/
def IsGW2RelVersion [MeasurableSpace Ω] (s : ℝ≥0) (P : Measure Ω) (W Wα : ℝ≥0 → Ω → ℝ) (ζ ζα : Ω → ℝ≥0∞)
    (γ α : Ω → ℝ≥0 → ℂ) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) : Prop :=
  Supp8.Q3Stop.IsGB6RelVersionA s P (regW s Wα ζα) W ζ (extTr s Wα ζα α) γ R V ∧
    ∀ᵐ ω ∂P, γ ω s ∈ H → ∀ u : ℝ≥0, (u : ℝ≥0∞) < V ω →
      ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζα ω ∧ (u : ℝ) < gw2Clock s W Wα ω t

end Defs

/-! ### The named statements -/

/-- **Named statement (NOT proved here): exhausting announced versions of GW2's relative exploration.** Binders of
`GW2JointDetC2Statement` (without the chart field and the code) and an admissible seed of the flow line (otherwise
`ζα = 0` and GW2's hull clause is empty). For every `s` there are announced R-form versions
`(R m, V m)` before the end time such that almost surely on `{γ(s) ∈ ℍ}` the relative clock of every time before the
end time `min(ζα, T_c)` is below some `V m`. (GB6's `Q3Stop.GB6RelVersionAStatement` for an explored curve killed at
its lifetime: the gauge readout must detect both the first contact and the flow's continuation threshold.) -/
def GW2RdVersionStatement : Prop :=
  ∀ (κ θ : ℝ), 0 < κ → κ < 4 → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (h : Ω → DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζ ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ)
    (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsPiecewiseConstantBoundaryData b' J' →
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω)) →
    IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ →
    (∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l) →
    (∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l) →
    (∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop) →
    IsFlowLineDriver κ b J θ P h Wα ζα →
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) →
    ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) 0 (flowLineXL b J 0)
      (flowLineXR b J 0) →
    ∀ s : ℝ≥0, ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ m, IsGW2RelVersion s P W Wα ζ ζα γ α (R m) (V m)) ∧
      ∀ᵐ ω ∂P, γ ω s ∈ H → ∀ t : ℝ≥0, (t : ℝ≥0∞) < gw2End s ζα γ α ω →
        ∃ m, ENNReal.ofReal (gw2Clock s W Wα ω t) < V m ω

/-- **Named statement (NOT proved here): GW2's relative safe law.** Binders of `GW2JointDetC2Statement` (without the
code), an admissible seed of the flow line, and an announced R-form version `(R, V)` of GW2's relative exploration:
for every word type `w` of the raised conditional word `gw2Word κ θ c′`, the joint law of the counterflow record and
of the relative variable `(Hc + θχ, R, V)`, conditioned on the record event of type `w`, has K2's inputs (S) and (L)
at `κ` with lifetime the stop, the stop is before the continuation threshold of the raised word, and the raised
chart field is integrable (`Supp8.Q3Stop.HasRelSafe`). (GB6's `Q3Stop.GB6RelSafeRStatement` with the curves
exchanged, at the raised word.) -/
def GW2RdSafeStatement : Prop :=
  ∀ (κ θ : ℝ), 0 < κ → κ < 4 → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (h : Ω → DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζ ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ)
    (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsPiecewiseConstantBoundaryData b' J' →
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω)) →
    IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ →
    (∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l) →
    (∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l) →
    (∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop) →
    IsFlowLineDriver κ b J θ P h Wα ζα →
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) →
    ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) 0 (flowLineXL b J 0)
      (flowLineXR b J 0) →
    ∀ (s : ℝ≥0) (Hc : Ω → DistOn upperHalfPlaneOpens), Measurable Hc →
    (∀ᵐ ω ∂P, γ ω s ∈ H →
      IsChartTransport (jointChart (fun r : ℝ => W r.toNNReal ω) s) 1 (specOffset κ) (chiC κ) (h ω) (Hc ω)) →
    ∀ c' : BoundaryWord, c'.jumps = J' → (∀ y ∉ J', c'.fn y = b' y) →
    ∀ (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞), IsGW2RelVersion s P W Wα ζ ζα γ α R V →
    ∀ w : Supp8.Q3Stop.WordType, Supp8.Q3Stop.HasRelSafe κ w (gw2Word κ θ c') (gb6TS s)
      (P.map fun ω => (gb6Rec s W ζ ω, relVar (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω)) R V ω))

/-! ### The stopped driver match of a version -/

/-- **The stopped driver match of a GW2 version from the safe law** (GB6's engine at angle `0` on the raised word and
field, with the shifted code). Almost surely on `{γ(s) ∈ ℍ}` the angle-`θ` canonical code of the chart field and the
joint word matches the version's driver up to its stop. -/
theorem ae_isStopDrvMatch_gw2 {κ θ : ℝ} (hκ : 0 < κ) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {b' : ℝ → ℝ} {J' : Finset ℝ} {h' : Ω → DistOn upperHalfPlaneOpens}
    {W Wα : ℝ≥0 → Ω → ℝ} {ζ ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (s : ℝ≥0)
    {Hc : Ω → DistOn upperHalfPlaneOpens} (hHcm : Measurable Hc)
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞} (hF : IsCanonicalDriverCode κ θ F)
    (c' : BoundaryWord) {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} (hver : IsGW2RelVersion s P W Wα ζ ζα γ α R V)
    (hS : ∀ w : Supp8.Q3Stop.WordType, Supp8.Q3Stop.HasRelSafe κ w (gw2Word κ θ c') (gb6TS s)
      (P.map fun ω => (gb6Rec s W ζ ω, relVar (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω)) R V ω))) :
    ∀ᵐ ω ∂P, γ ω s ∈ H →
      IsStopDrvMatch (F (jointWord (specOffset κ) κ c' s (fun t => W t ω), Hc ω)) (fun t => R t ω) (V ω) := by
  obtain ⟨⟨⟨⟨hRm, hRc, hR0, -, hVm, -, hlive⟩, ρ, hρm, hρ, hVρ⟩, ρs, hρsm, hρs, hρsfin, hρsmono, hann⟩, -⟩ :=
    hver
  have hrecm : Measurable (gb6Rec s W ζ) := (measurable_recOf_cfE hcf s).2
  have hβ := measurable_gw2Word κ θ c'
  have hHcm' : Measurable fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω) :=
    (Exist.measurable_flowField 0 _).comp hHcm
  have hFd := isCanonicalDriverCode_shiftCode hF
  have hgoodrec := ae_gb6RecGood hcf hγ s
  have hV0 : ∀ᵐ ω ∂P, gb6Rec s W ζ ω ∈ gb6TS s → 0 < V ω := by
    filter_upwards [hlive, hgoodrec] with ω hω hg hm
    obtain ⟨hs, hsH⟩ := (mem_gb6TS_iff hg).2 hm
    exact (hω hs hsH).1
  have hw : ∀ w : Supp8.Q3Stop.WordType, ∀ᵐ ω ∂P, gb6Rec s W ζ ω ∈ gb6TS s →
      Supp8.Q3Stop.wordType κ (gw2Word κ θ c' (gb6Rec s W ζ ω)) = w →
      IsStopDrvMatch (shiftCode κ θ F (gw2Word κ θ c' (gb6Rec s W ζ ω), Exist.flowField 0 (θ * chiC κ) (Hc ω)))
        (fun t => R t ω) (V ω) := fun w =>
    Supp8.Q3Stop.ae_isStopDrvMatch_of_hasRelSafe hκ hFd hβ (measurableSet_gb6TS s) w hrecm hHcm' hRm hRc hR0 hVm
      (hS w) hV0 hρm hρ hVρ hρsm hρs hρsfin hρsmono (hann.mono fun ω h hm => (h hm).1)
      (hann.mono fun ω h hm => (h hm).2)
  have hcount : (range fun r : RecData => Supp8.Q3Stop.wordType κ (gw2Word κ θ c' r)).Countable :=
    countable_range_wordType_upW_retStop κ (16 / κ) 0 (retA κ + specOffset κ) (retL κ) (θ * chiC κ) c'
  have hall := (ae_ball_iff hcount).2 fun w _ => hw w
  filter_upwards [hall, hgoodrec, hζ] with ω hω hg hz hsH
  have hs : (s : ℝ≥0∞) < ζ ω := by rw [hz]; exact ENNReal.coe_lt_top
  have hm : gb6Rec s W ζ ω ∈ gb6TS s := (mem_gb6TS_iff hg).1 ⟨hs, hsH⟩
  have h1 := hω _ ⟨_, rfl⟩ hm rfl
  rw [gw2Word, shiftCode_upW] at h1
  have hrec : gb6Rec s W ζ ω = recOf (s : ℝ≥0∞) (fun t => W t ω, ⊤) := (hg hs).2.1
  rwa [hrec] at h1

/-! ### From the extended flow back to the flow before its lifetime -/

/-- **Before the lifetime and the first contact, the extended flow is the flow** (one sample): if `wb = wα` before
`Tα` and `αb = α` on `[0, Tα]`, then at every `t < Tα` before the first contact of `α` with the inverted retained
prefix the hulls and relative clocks agree, and `t` is before GB6's contact time of `αb`. -/
theorem hull_clock_contact_of_ext {s : ℝ≥0} {w : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {wα wb : ℝ≥0 → ℝ} {Tα : ℝ≥0∞}
    {α αb : ℝ≥0 → ℂ} (heq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tα → wb t = wα t)
    (hαα : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ Tα → αb u = α u) {t : ℝ≥0} (htα : (t : ℝ≥0∞) < Tα)
    (htc : (t : ℝ≥0∞) < firstContactTime (fun t => (α t : OnePoint ℂ))
      ((fun r => sphereInv (γ r : OnePoint ℂ)) '' Icc 0 s)) :
    QuantumZipper.fwdHull (fun r : ℝ => wb r.toNNReal) t = QuantumZipper.fwdHull (fun r : ℝ => wα r.toNNReal) t ∧
      relClock (fun r : ℝ => w r.toNNReal) s (fun r : ℝ => wb r.toNNReal) t =
        relClock (fun r : ℝ => w r.toNNReal) s (fun r : ℝ => wα r.toNNReal) t ∧
      (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (αb t : OnePoint ℂ))
        ((fun u => (γ u : OnePoint ℂ)) '' Icc 0 s) := by
  obtain ⟨t₂, htt₂, ht₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 htα
  have htt₂' : t < t₂ := by exact_mod_cast htt₂
  have hK : QuantumZipper.fwdHull (fun r : ℝ => wb r.toNNReal) t =
      QuantumZipper.fwdHull (fun r : ℝ => wα r.toNNReal) t :=
    fwdHull_eq_of_eqOn t.2 (NNReal.coe_lt_coe.2 htt₂') fun r hr => heq r.toNNReal
      (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)) ht₂)
  refine ⟨hK, by unfold relClock; rw [hK], ?_⟩
  rw [GW2JDetR4.firstContactTime_sphereInv αb γ s]
  exact GW2Fb.lt_firstContactTime_of_prefix htt₂' (fun u hu => by
    rw [hαα u ((ENNReal.coe_le_coe.2 hu).trans ht₂.le)]) htc

/-! ### GW2's (Det) -/

/-- **GW2's joint (Det) from versions and the relative safe law** (conditional helper): Theorems 1.2–1.3 at universe
`0` give the good code at the flow's angle; at an inadmissible seed the flow's lifetime is `0` and the hull clause is
empty; otherwise `GW2RdVersionStatement` and `GW2RdSafeStatement` give the stopped matches of exhausting versions,
the extended flow agrees with the flow before its lifetime, and the frozen deterministic step gives the hull
identity before `min(ζα, T_c)`. -/
theorem gw2JointDetC2Statement_of_versions_safe (h12p₀ : Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hV : GW2RdVersionStatement.{u}) (hS : GW2RdSafeStatement.{u}) :
    GW2JointDetC2Statement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hh hb' hT hcf hpL hpR hreg hfl hα s Hc hHcm
    hHc F hF c' hc'J hc'b
  have hk : (0 : ℝ) < 16 / κ := by positivity
  have e16 : 16 / (16 / κ) = κ := by field_simp
  have hG' : IsGFFWithBoundaryData P h' b' J' :=
    Theorem14.GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hk hb' hcf
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := hreg.mono fun ω hω => hω.1
  have hγ' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω) := hreg.mono fun ω hω => by
    rw [hω.1]
    exact hω.2.1
  have hdrv := Supp8.GB6.ae_driver_zero_continuousOn hcf
  -- the chart field in the counterflow's own chart (dual parameter)
  have hHc' : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζ ω → γ ω s ∈ H →
      IsChartTransport (ownComponentChart (fun r : ℝ => W r.toNNReal ω) s) (-1)
        (-(Real.pi * chiC (16 / κ))) (chiC (16 / (16 / κ))) (h' ω) (Hc ω) := by
    filter_upwards [hHc, hdrv, hζ] with ω hω hd hz _ hsH
    have hcont : ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := hd.2
    rw [hz] at hcont
    have hc : Continuous fun t => W t ω := continuousOn_univ.1 (hcont.mono fun t _ => ENNReal.coe_lt_top)
    have h0 : (fun r : ℝ => W r.toNNReal ω) 0 = 0 := by
      show W (0 : ℝ).toNNReal ω = 0
      rw [Real.toNNReal_zero]
      exact hd.1
    exact GW2Fb.isChartTransport_own_of_joint hκ (hc.comp continuous_real_toNNReal) h0 s.coe_nonneg (hT ω)
      (hω hsH)
  -- the good code at the flow's angle
  have hF' : IsCanonicalDriverCode (16 / (16 / κ)) θ F := by
    rw [e16]
    exact hF
  have hgood := ae_isGoodDrvCode_ret_theta (θ := 0) h12p₀ h13₀ hk hb' hG' hcf hγ' s hHcm hHc' hF' hc'b
  have hgood' : ∀ᵐ ω ∂P, γ ω s ∈ H →
      IsGoodDrvCode (F (jointWord (specOffset κ) κ c' s (fun t => W t ω), Hc ω)) := by
    filter_upwards [hgood, hζ] with ω hgω hz hsH
    have hs : (s : ℝ≥0∞) < ζ ω := by rw [hz]; exact ENNReal.coe_lt_top
    have hj : gb6Word (16 / κ) 0 c' s (fun t => W t ω) = jointWord (specOffset κ) κ c' s (fun t => W t ω) :=
      (GW2Fb.jointWordOfRec_specOffset hκ c' _).symm
    have := hgω hs hsH
    rwa [hj] at this
  by_cases hseed : ForceWord.ThresholdCondition (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) 0
    (flowLineXL b J 0) (flowLineXR b J 0)
  · -- an inadmissible seed: the flow line dies at once
    obtain ⟨_, _, _, _, _, _, hC⟩ := id hfl
    filter_upwards [hgood', IsIntegratedSLEEvolution.ae_lifetime_eq_zero_of_threshold hC.1 hseed]
      with ω hgω hz hsH
    refine ⟨hgω hsH, fun t htζ _ => ?_⟩
    rw [hz] at htζ
    exact absurd htζ not_lt_zero
  -- versions and their matches
  obtain ⟨R, V, hver, hexh⟩ := hV κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hh hb' hT hcf hpL
    hpR hreg hfl hα hseed s
  have hmatch : ∀ m, ∀ᵐ ω ∂P, γ ω s ∈ H →
      IsStopDrvMatch (F (jointWord (specOffset κ) κ c' s (fun t => W t ω), Hc ω)) (fun t => R m t ω) (V m ω) :=
    fun m => ae_isStopDrvMatch_gw2 hκ hcf hγ' hζ s hHcm hF c' (hver m)
      (hS κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hh hb' hT hcf hpL hpR hreg hfl hα hseed s
        Hc hHcm hHc c' hc'J hc'b (R m) (V m) (hver m))
  have hlive : ∀ m, ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζ ω → γ ω s ∈ H → 0 < V m ω ∧
      (∀ u : ℝ≥0, (u : ℝ≥0∞) < V m ω → ∃ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s (extTr s Wα ζα α) γ ω ∧
        (u : ℝ) < gb6Clock s (regW s Wα ζα) W ω t) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s (extTr s Wα ζα α) γ ω →
        ENNReal.ofReal (gb6Clock s (regW s Wα ζα) W ω t) ≤ V m ω →
        QuantumZipper.fwdHull (fun r : ℝ => R m r.toNNReal ω) (gb6Clock s (regW s Wα ζα) W ω t) =
          relMap (fun r : ℝ => W r.toNNReal ω) s '' QuantumZipper.fwdHull (fun r : ℝ => regW s Wα ζα r.toNNReal ω) t :=
    fun m => (hver m).1.1.1.2.2.2.2.2.2
  filter_upwards [hgood', ae_all_iff.2 hmatch, ae_all_iff.2 hlive, hexh, hζ, hreg, hdrv,
    Supp8.GB6.ae_driver_zero_continuousOn hfl, hα, ae_extTr_spec hκ hfl hα s] with ω hgω hmω hlω hexω hz hrω hdω
    hdαω hαω hextω hsH
  have hs : (s : ℝ≥0∞) < ζ ω := by rw [hz]; exact ENNReal.coe_lt_top
  have hp := hgω hsH
  refine ⟨hp, fun t htζ htc => ?_⟩
  have hcont : ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := hdω.2
  rw [hz] at hcont
  have hwc : Continuous fun t => W t ω := continuousOn_univ.1 (hcont.mono fun t _ => ENNReal.coe_lt_top)
  have hγω : IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) := hrω.2.1
  have hRK : ∀ m (t : ℝ≥0), (t : ℝ≥0∞) < ζα ω →
      (t : ℝ≥0∞) < firstContactTime (fun t => (α ω t : OnePoint ℂ))
        ((fun r => sphereInv (γ ω r : OnePoint ℂ)) '' Icc 0 s) →
      ENNReal.ofReal (relClock (fun r : ℝ => W r.toNNReal ω) s (fun r : ℝ => Wα r.toNNReal ω) t) ≤ V m ω →
      QuantumZipper.fwdHull (fun r : ℝ => R m r.toNNReal ω)
          (relClock (fun r : ℝ => W r.toNNReal ω) s (fun r : ℝ => Wα r.toNNReal ω) t) =
        relMap (fun r : ℝ => W r.toNNReal ω) s '' QuantumZipper.fwdHull (fun r : ℝ => Wα r.toNNReal ω) t := by
    intro m t ht1 ht2 hle
    have hpos : 0 < ζα ω := lt_of_le_of_lt (zero_le : (0 : ℝ≥0∞) ≤ t) ht1
    obtain ⟨-, -, heqω, -, hαα⟩ := hextω hpos
    obtain ⟨hK, hC, hT⟩ := hull_clock_contact_of_ext (w := fun t => W t ω) heqω hαα ht1 ht2
    have h1 := (hlω m hs hsH).2.2 t hT (by
      show ENNReal.ofReal (relClock (fun r : ℝ => W r.toNNReal ω) s
        (fun r : ℝ => regW s Wα ζα r.toNNReal ω) t) ≤ V m ω
      rw [hC]
      exact hle)
    have h1' : QuantumZipper.fwdHull (fun r : ℝ => R m r.toNNReal ω)
        (relClock (fun r : ℝ => W r.toNNReal ω) s (fun r : ℝ => regW s Wα ζα r.toNNReal ω) t) =
        relMap (fun r : ℝ => W r.toNNReal ω) s ''
          QuantumZipper.fwdHull (fun r : ℝ => regW s Wα ζα r.toNNReal ω) t := h1
    rw [hC, hK] at h1'
    exact h1'
  exact fwdHull_drvDec_eq_of_family hp hγω hwc hdω.1 hsH hαω hdαω.2 hdαω.1
    (fun m => (hver m).1.1.1.2.1 ω) (fun m => (hver m).1.1.1.2.2.1 ω) (fun m => hmω m hsH) hRK
    (fun t ht1 ht2 => hexω hsH t (lt_min ht1 ht2)) t htζ htc

end InteractingSLE.Theorem14.GW2Rd
