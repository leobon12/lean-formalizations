/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.LP4Cluster
import InteractingSLE.Spec.Supplement.LPDilation
import InteractingSLE.Spec.Supplement.LPAssembly
import InteractingSLE.Spec.Sec7.TraceCodingUse
import InteractingSLE.Foundations.Loewner.TraceCodingTop

/-!
# Proposition LP4: from positive probability of avoiding `0` to transience

Packet PROVE-LP14. Supplement §6.3, Proposition LP4 (`source/spec/p481-528.md` L37–L70, pp. 482–483): "Let `k > 4`
and `−2 < r_L, r_R < c`. Suppose the canonical two-seed driving law has a continuous trace on every finite capacity
interval. Then this trace tends to infinity almost surely."

LP4's proof has two parts. The first (pp. 482–483, through "We have established positive probability that `0` is
absent from the terminal cluster set") builds a positive-probability stopping time with straddling swallowed extremes
(Lemma LP2, the Jacobi accessibility, LP1's bounded-energy deletion) and applies LP3 and Zhan's ordinary-SLE theorem
[Zha10, Corollary 6.1]. The second (p. 483) is:

"The event `0 ∉ Q` is a measurable dilation-invariant event of the full canonical driving law. Aux. lemma 128
therefore makes its probability one. […] Set `Z = inf{|z| : z ∈ Q ∩ ℂ}`. The absence of `0` and compactness of `Q`
give `Z > 0`. Exact dilation invariance of the trace law gives `Z =ᵈ aZ` for every `a > 0`. A random variable in
`(0, ∞]` with this property equals `∞` almost surely […]. Thus `Q = {∞}` and `η(t) → ∞`."

This file proves the second part completely, from two named inputs:

* `Aux128DriverStatement`: Aux. lemma 128 (pp. 403–404) for events of the driving path ("Every measurable event of its
  full path law that is invariant under all positive dilations has probability zero or one");
* `LP4AvoidStatement`: the first part of LP4's proof ("positive probability that `0` is absent from the terminal
  cluster set").

Proved here:

* `measurableSet_avoidSet`, `mem_avoidSet_iff`, `dilPath_mem_avoidSet_iff`: the event "the driver has a continuous
  generating trace on `[0, ∞)` with `Z > 0`" is a measurable set of driving paths, invariant under every positive
  dilation (the measurable trace coding `Sec7.topTraceCodingStatement` and `LP4Cluster.lean`);
* `map_terminalModulus_mul`: exact dilation invariance of the law of `Z`, from the dilation of evolutions
  (`IsIntegratedSLEEvolution.dilate_zero`) and Theorem 2.2's uniqueness in law (`Sec7.map_killedRestrict_eq`);
* `ae_tendsto_norm_of_frequently_avoid`: the second part of LP4's proof for every two-seed evolution with weights
  `> −2` and an almost surely continuous trace;
* **`lp4Statement_of_inputs`**: the named input `LP4Statement` of LP11's assembly.

These are conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal NNRat

universe u

namespace InteractingSLE.LP

open Sec7.Dilation

/-! ### The named inputs -/

/-- **Named input: Aux. lemma 128 for events of the driver** (Specification §7.4, `source/spec/p385-432.md` L335–L353,
pp. 403–404: "Fix `k > 0` and `r_L, r_R > −2`. Let `X = (W, V^L, V^R)` be the canonical integrated two-seed driving
evolution, with all three initial coordinates zero. Every measurable event of its full path law that is invariant
under all positive dilations has probability zero or one. Here a dilation acts by `(Θ_c X)(t) = c^{-1} X(c² t)`").
Stated for events of the driving path `W` (a measurable set `G` of paths, product σ-algebra), with invariance required
on the continuous paths vanishing at `0`, which carry the driving law ("invariance up to a path-law null set, which is
sufficient"); the dilation `Θ_c` is `dilPath (c²)`. -/
def Aux128DriverStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
    ∀ G : Set (ℝ≥0 → ℝ), MeasurableSet G →
      (∀ c : ℝ≥0, c ≠ 0 → ∀ w : ℝ≥0 → ℝ, Continuous w → w 0 = 0 → (dilPath c w ∈ G ↔ w ∈ G)) →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ →
        (∀ᵐ ω ∂P, (fun t => W t ω) ∈ G) ∨ ∀ᵐ ω ∂P, (fun t => W t ω) ∉ G

/-- **Named input: the positive-probability part of Proposition LP4** (supplement pp. 482–483, from "First obtain a
positive-probability finite own stopping time at which the physical leftmost and rightmost swallowed real points
straddle `0` strictly" to "We have established positive probability that `0` is absent from the terminal cluster
set"; its inputs are Lemma LP2, the Jacobi endpoint accessibility, LP1's bounded-energy deletion of the separated left
drift, Lemma LP3, the geometric force endpoint identities and [Zha10, Corollary 6.1]). Under LP4's hypotheses, for
every two-seed evolution, with positive probability the driver has a continuous generating trace on `[0, ∞)` whose
terminal cluster set `Q ∩ ℂ = ⋂_n closure(η([n, ∞)))` does not contain `0`. -/
def LP4AvoidStatement : Prop :=
  ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 2 → -2 < rR → rR < κ / 2 - 2 →
    (∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η) →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ →
        ∃ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η ∧ (0 : ℂ) ∉ terminalClusterSet η

/-! ### Dilations of continuous drivers and their traces -/

section DilatedPaths

variable {c : ℝ≥0}

theorem continuous_dilPath (w : ℝ≥0 → ℝ) (hw : Continuous w) : Continuous (dilPath c w) :=
  continuous_const.mul (hw.comp (continuous_const.mul continuous_id))

theorem dilPath_zero {w : ℝ≥0 → ℝ} (hw0 : w 0 = 0) : dilPath c w 0 = 0 := by
  simp [dilPath, hw0]

/-- A dilated trace on `[0, ∞)` is a trace on `[0, ∞)` of the dilated driver, with `Z` multiplied by `(√c)⁻¹`. -/
theorem exists_dilate_trace (hc : c ≠ 0) {w : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ⊤ η) :
    ∃ η' : ℝ≥0 → ℂ, IsGeneratingTrace (dilPath c w) ⊤ η' ∧
      terminalModulus η' = ‖(((√(c : ℝ))⁻¹ : ℝ) : ℂ)‖ₑ * terminalModulus η := by
  refine ⟨_, ?_, terminalModulus_dilate hc η⟩
  have h := hη.dilate hc
  rwa [ENNReal.top_div_coe] at h

end DilatedPaths

/-! ### The avoiding event as a measurable dilation-invariant set of drivers -/

section AvoidSet

/-- The restriction of a path to the nonnegative rational times. -/
def ratRestrict (w : ℝ≥0 → ℝ) : ℚ≥0 → ℝ := fun q => w q

theorem measurable_ratRestrict : Measurable ratRestrict :=
  measurable_pi_iff.2 fun q => measurable_pi_apply (q : ℝ≥0)

/-- The trace-coding set of `Sec7.topTraceCodingStatement`. -/
def topCodeSet : Set (ℚ≥0 → ℝ) := Sec7.topTraceCodingStatement.choose

theorem measurableSet_topCodeSet : MeasurableSet topCodeSet := Sec7.topTraceCodingStatement.choose_spec.1

theorem mem_topCodeSet_iff {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) :
    ratRestrict w ∈ topCodeSet ↔ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w ⊤ η :=
  Sec7.topTraceCodingStatement.choose_spec.2 w hw hw0

/-- **The event of LP4 on driving paths**: the driver has a continuous generating trace on `[0, ∞)` (coded at rational
times) and the coded terminal modulus `Z` is positive. -/
def avoidSet : Set (ℝ≥0 → ℝ) := {w | ratRestrict w ∈ topCodeSet ∧ 0 < ratTerminalModulus (ratRestrict w)}

theorem measurableSet_avoidSet : MeasurableSet avoidSet :=
  (measurable_ratRestrict measurableSet_topCodeSet).inter
    (measurableSet_lt measurable_const (measurable_ratTerminalModulus.comp measurable_ratRestrict))

theorem mem_avoidSet_iff {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) :
    w ∈ avoidSet ↔ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w ⊤ η ∧ 0 < terminalModulus η := by
  show ratRestrict w ∈ topCodeSet ∧ 0 < ratTerminalModulus (ratRestrict w) ↔ _
  rw [mem_topCodeSet_iff hw hw0]
  constructor
  · rintro ⟨⟨η, hη⟩, hpos⟩
    exact ⟨η, hη, by rwa [← ratTerminalModulus_eq hw hw0 hη]⟩
  · rintro ⟨η, hη, hpos⟩
    refine ⟨⟨η, hη⟩, ?_⟩
    rw [show ratRestrict w = fun q : ℚ≥0 => w q from rfl, ratTerminalModulus_eq hw hw0 hη]
    exact hpos

theorem dilPath_mem_avoidSet_of_mem {c : ℝ≥0} (hc : c ≠ 0) {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    (h : w ∈ avoidSet) : dilPath c w ∈ avoidSet := by
  obtain ⟨η, hη, hpos⟩ := (mem_avoidSet_iff hw hw0).1 h
  obtain ⟨η', hη', hZ⟩ := exists_dilate_trace hc hη
  refine (mem_avoidSet_iff (continuous_dilPath w hw) (dilPath_zero hw0)).2 ⟨η', hη', ?_⟩
  rw [hZ]
  have hk : ‖(((√(c : ℝ))⁻¹ : ℝ) : ℂ)‖ₑ ≠ 0 := by
    rw [enorm_ne_zero]
    exact_mod_cast inv_sqrt_ne_zero hc
  exact ENNReal.mul_pos hk hpos.ne'

/-- **The avoiding event is dilation invariant** (LP4, p. 483: "The event `0 ∉ Q` is a measurable dilation-invariant
event"). -/
theorem dilPath_mem_avoidSet_iff {c : ℝ≥0} (hc : c ≠ 0) {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) :
    dilPath c w ∈ avoidSet ↔ w ∈ avoidSet := by
  refine ⟨fun h => ?_, dilPath_mem_avoidSet_of_mem hc hw hw0⟩
  have h' := dilPath_mem_avoidSet_of_mem (inv_ne_zero hc) (continuous_dilPath w hw) (dilPath_zero hw0) h
  rwa [dilPath_inv_dilPath hc] at h'

end AvoidSet

/-! ### The law of `Z` -/

section Law

variable {κ rL rR : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- LP4's `Z` as a measurable function of the killed driver. -/
def zOf (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ratTerminalModulus (Sec7.killedRestrict W ζ ω)

theorem measurable_zOf (hW : AdaptedBefore 𝓕 ζ W) : Measurable (zOf W ζ) :=
  measurable_ratTerminalModulus.comp (Sec7.measurable_killedRestrict hW)

/-- The pathwise good event: infinite lifetime, a continuous driver vanishing at `0`. -/
theorem ae_good (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR)
    (hE : IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ Continuous (fun t => W t ω) ∧ W 0 ω = 0 := by
  filter_upwards [Sec7.ae_lifetime_eq_top_twoSeed (ρL := fun _ => rL) (ρR := fun _ => rR) hκ hL hR
    Sec7.jacobiDiffusionExistsStatement hE, hE.2.2.2.2] with ω hζ hpath
  rw [hζ] at hpath
  exact ⟨hζ, continuousOn_univ.1 (by simpa using hpath.2.2.2.1), hpath.1⟩

/-- On the good event, `Z` is the terminal modulus of every generating trace on `[0, ∞)`. -/
theorem zOf_eq {ω : Ω} (hζ : ζ ω = ⊤) (hw : Continuous fun t => W t ω) (hw0 : W 0 ω = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace (fun t => W t ω) ⊤ η) : zOf W ζ ω = terminalModulus η := by
  rw [zOf, Sec7.killedRestrict_eq_of_top hζ]
  exact ratTerminalModulus_eq hw hw0 hη

/-- The norm of a positive real constant, as an extended real. -/
theorem enorm_inv_sqrt_eq {a : ℝ≥0∞} (ha : a ≠ 0) (hat : a ≠ ⊤) :
    ‖(((√((((a.toNNReal) ^ 2)⁻¹ : ℝ≥0) : ℝ))⁻¹ : ℝ) : ℂ)‖ₑ = a := by
  have hs : (0 : ℝ) < (a.toNNReal : ℝ) := by
    rw [NNReal.coe_pos]; exact ENNReal.toNNReal_pos ha hat
  have hsq : (√((((a.toNNReal) ^ 2)⁻¹ : ℝ≥0) : ℝ))⁻¹ = (a.toNNReal : ℝ) := by
    rw [NNReal.coe_inv, NNReal.coe_pow, Real.sqrt_inv, Real.sqrt_sq hs.le, inv_inv]
  rw [hsq, enorm_eq_nnnorm, Complex.nnnorm_real, Real.nnnorm_of_nonneg hs.le]
  simp [ENNReal.coe_toNNReal hat]

/-- **Exact dilation invariance of the law of `Z`** (LP4, p. 483: "Exact dilation invariance of the trace law gives
`Z =ᵈ aZ` for every `a > 0`"): for a two-seed evolution with weights `> −2` whose trace exists almost surely, the law of
`aZ` is the law of `Z` for every `0 < a < ∞`. The dilated processes are again an evolution of the two-seed word on
the same space (`IsIntegratedSLEEvolution.dilate_zero`), Theorem 2.2's uniqueness gives the same rational-time driving
law (`Sec7.map_killedRestrict_eq`), and pathwise `Z` of the dilated driver is `a Z` (`exists_dilate_trace`). -/
theorem map_zOf_mul (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR)
    (hE : IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ)
    (htr : ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η)
    {a : ℝ≥0∞} (ha : a ≠ 0) (hat : a ≠ ⊤) :
    P.map (fun ω => a * zOf W ζ ω) = P.map (zOf W ζ) := by
  set c : ℝ≥0 := ((a.toNNReal) ^ 2)⁻¹ with hcdef
  have hc : c ≠ 0 := inv_ne_zero (pow_ne_zero 2 (ENNReal.toNNReal_pos ha hat).ne')
  have hE' := hE.dilate_zero hc
  have hlaw := Sec7.map_killedRestrict_eq (ρL := fun _ => rL) (ρR := fun _ => rR) hκ hL hR
    Sec7.jacobiDiffusionExistsStatement hE' hE
  have hm := Sec7.measurable_killedRestrict hE.2.1
  have hm' := Sec7.measurable_killedRestrict hE'.2.1
  -- the laws of `Z` for the dilated and the original evolution agree
  have hZ : P.map (zOf (dilProc c W) (fun ω => ζ ω / c)) = P.map (zOf W ζ) := by
    show P.map (ratTerminalModulus ∘ Sec7.killedRestrict (dilProc c W) fun ω => ζ ω / c) =
      P.map (ratTerminalModulus ∘ Sec7.killedRestrict W ζ)
    rw [← Measure.map_map measurable_ratTerminalModulus hm', ← Measure.map_map measurable_ratTerminalModulus hm,
      hlaw]
  -- pathwise, `Z` of the dilated driver is `a Z`
  have hpath : (fun ω => a * zOf W ζ ω) =ᵐ[P] zOf (dilProc c W) (fun ω => ζ ω / c) := by
    filter_upwards [ae_good hκ hL hR hE, htr] with ω ⟨hζ, hw, hw0⟩ ⟨η, hη⟩
    rw [hζ] at hη
    obtain ⟨η', hη', hZ'⟩ := exists_dilate_trace hc hη
    have hζ' : ζ ω / c = ⊤ := by rw [hζ]; exact ENNReal.top_div_coe
    have e1 := zOf_eq hζ hw hw0 hη
    have e2 : zOf (dilProc c W) (fun ω => ζ ω / c) ω = terminalModulus η' :=
      zOf_eq (W := dilProc c W) (ζ := fun ω => ζ ω / c) hζ' (continuous_dilPath (c := c) _ hw)
        (dilPath_zero (c := c) (w := fun t => W t ω) hw0) hη'
    rw [e1, e2, hZ', hcdef, enorm_inv_sqrt_eq ha hat]
  rw [Measure.map_congr hpath, hZ]

end Law

/-! ### The second part of LP4's proof -/

/-- **LP4's dilation argument** (p. 483), for one two-seed evolution with weights `> −2` and an almost surely
continuous trace: if with positive probability the trace on `[0, ∞)` avoids `0` eventually, then almost surely every
generating trace on an infinite lifetime tends to infinity. Aux. lemma 128 upgrades the avoiding event to probability
one, so `Z > 0` almost surely; the law of `Z` is dilation invariant (`map_zOf_mul`), so `Z = ∞` almost surely
(`ae_eq_top_of_map_const_mul_eq`). -/
theorem ae_tendsto_norm_of_frequently_avoid (h128 : Aux128DriverStatement.{u}) {κ rL rR : ℝ} (hκ : 0 < κ)
    (hL : -2 < rL) (hR : -2 < rR) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ)
    (htr : ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η)
    (hpos : ∃ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η ∧
      (0 : ℂ) ∉ terminalClusterSet η) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η → ζ ω = ⊤ →
      Tendsto (fun t => ‖η t‖) atTop atTop := by
  have hgood := ae_good hκ hL hR hE
  -- Aux. lemma 128: the avoiding event has probability one
  have hinv : ∀ c : ℝ≥0, c ≠ 0 → ∀ w : ℝ≥0 → ℝ, Continuous w → w 0 = 0 →
      (dilPath c w ∈ avoidSet ↔ w ∈ avoidSet) := fun c hc w hw hw0 => dilPath_mem_avoidSet_iff hc hw hw0
  have hall : ∀ᵐ ω ∂P, (fun t => W t ω) ∈ avoidSet := by
    rcases h128 κ hκ rL rR hL hR avoidSet measurableSet_avoidSet hinv P 𝓕 W VL VR B ζ hE with h | h
    · exact h
    · exfalso
      have hfr : ∃ᵐ ω ∂P, (fun t => W t ω) ∈ avoidSet ∧ (fun t => W t ω) ∉ avoidSet := by
        refine (hpos.and_eventually (hgood.and h)).mono fun ω ⟨⟨η, hη, h0⟩, ⟨_, hw, hw0⟩, hn⟩ => ⟨?_, hn⟩
        exact (mem_avoidSet_iff hw hw0).2 ⟨η, hη, terminalModulus_pos_of_notMem h0⟩
      obtain ⟨ω, h1, h2⟩ := hfr.exists
      exact h2 h1
  -- hence `Z > 0` almost surely
  have hZpos : ∀ᵐ ω ∂P, 0 < zOf W ζ ω := by
    filter_upwards [hall, hgood] with ω hω ⟨hζ, hw, hw0⟩
    obtain ⟨η, hη, hpos⟩ := (mem_avoidSet_iff hw hw0).1 hω
    rw [zOf_eq hζ hw hw0 hη]
    exact hpos
  -- dilation invariance of the law of `Z` gives `Z = ∞` almost surely
  have hZtop := ae_eq_top_of_map_const_mul_eq (measurable_zOf hE.2.1) hZpos
    fun a ha hat => map_zOf_mul hκ hL hR hE htr ha hat
  filter_upwards [hZtop, hgood] with ω hZ ⟨hζ, hw, hw0⟩ η hη _
  rw [hζ] at hη
  rw [zOf_eq hζ hw hw0 hη] at hZ
  exact tendsto_norm_of_terminalModulus_eq_top hZ

/-- **Proposition LP4** (supplement p. 482) in the form consumed by LP11's assembly (`LP4Statement`), from Aux. lemma 128
and the positive-probability part of its proof. Conditional helper. -/
theorem lp4Statement_of_inputs (h128 : Aux128DriverStatement.{u}) (hpos : LP4AvoidStatement.{u}) :
    LP4Statement.{u} := by
  intro κ hκ rL rR hL hLc hR hRc hcont Ω mΩ P _ 𝓕 W VL VR B ζ hE
  exact ae_tendsto_norm_of_frequently_avoid h128 (by linarith) hL hR hE (hcont P 𝓕 W VL VR B ζ hE)
    (hpos κ hκ rL rR hL hLc hR hRc hcont P 𝓕 W VL VR B ζ hE)

end InteractingSLE.LP
