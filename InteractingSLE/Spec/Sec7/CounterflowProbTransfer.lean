/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.CounterflowProbLemma725
import InteractingSLE.Spec.Sec2.TwoSeedLaw
import Mathlib.MeasureTheory.Constructions.Projective

/-!
# §7.4, Aux. lemma 126: transferring the stopped trace event between two-seed evolutions

Packet PROVE-SEC7-D2. Aux. lemma 126's proof (`source/spec/p385-432.md` L256–L316, pp. 399–401) first obtains one
two-seed coupling whose trace is continuous through the buffered stop `S_r` (the change of measure (FS11.2)–(FS11.4)
and the extension Aux. lemma 54), and then transfers this to every two-seed evolution: "All trace statements used
below are measurable statements about the driving history … This gives standard Borel versions of the curve and the
relevant continuous-trace event" and "Fix any full original two-seed coupling provided by Theorem 1.1. Its stopped
driving marginal at `S_r` agrees with the one just obtained".

This file proves the transfer. For weights `> −2`, two integrated two-seed evolutions have the same finite-dimensional
killed-state laws (Theorem 2.2's uniqueness, landed: `Sec2.TwoSeed.measure_killedState_eq_twoSeed_of_gt`) and
infinite lifetimes (`ae_lifetime_eq_top_twoSeed`), so the laws of their drivers at nonnegative rational times agree
(`map_killedRestrict_eq`, through Mathlib's uniqueness of projective limits). A continuous driver is determined by
its rational values, so any event of the driving path that is coded by a measurable set of rational-time values
transfers (`ae_stoppedTrace_transfer`). The coding of the stopped-trace event itself is a deterministic Loewner
statement, kept as the named input `StoppedTraceCodingStatement`.

## Named inputs

| Input | Source |
|---|---|
| `StoppedTraceCodingStatement` | Aux. lemma 126's proof, p. 399–400 (measurable coding of the continuous-trace event) |
| `Aux126GirsanovStatement` | Aux. lemma 126's proof, (FS11.1)–(FS11.4) and Aux. lemma 54 (pp. 399–401; Aux. 55's (HL3)–(HL9), pp. 247–249) |
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal NNRat

universe u v

namespace InteractingSLE

namespace Sec7

/-! ### The killed driver and its rational-time law -/

/-- The driver killed at the lifetime (value `0` from `ζ` on). -/
def killedProc {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : ℝ≥0∞) < ζ ω then W t ω else 0

theorem measurable_killedProc {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} (hW : AdaptedBefore 𝓕 ζ W) (t : ℝ≥0) :
    Measurable (killedProc W ζ t) := by
  intro s hs
  have h1 : MeasurableSet {ω | (t : ℝ≥0∞) < ζ ω ∧ W t ω ∈ s} := 𝓕.le t _ (hW t s hs)
  have h2 : MeasurableSet {ω | (t : ℝ≥0∞) < ζ ω} := by
    have h := 𝓕.le t _ (hW t univ MeasurableSet.univ)
    simpa using h
  have hset : killedProc W ζ t ⁻¹' s =
      {ω | (t : ℝ≥0∞) < ζ ω ∧ W t ω ∈ s} ∪ ({ω | (t : ℝ≥0∞) < ζ ω}ᶜ ∩ {_ω | (0 : ℝ) ∈ s}) := by
    ext ω
    by_cases h : (t : ℝ≥0∞) < ζ ω <;> simp [killedProc, h]
  rw [hset]
  exact h1.union (h2.compl.inter (MeasurableSet.const _))

/-- The killed driver at the nonnegative rational times. -/
def killedRestrict {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : ℚ≥0 → ℝ :=
  fun q => killedProc W ζ q ω

theorem measurable_killedRestrict {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} (hW : AdaptedBefore 𝓕 ζ W) :
    Measurable (killedRestrict W ζ) :=
  measurable_pi_iff.2 fun q => measurable_killedProc hW q

theorem killedRestrict_eq_of_top {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω}
    (hω : ζ ω = ⊤) : killedRestrict W ζ ω = fun q : ℚ≥0 => W q ω := by
  funext q
  simp [killedRestrict, killedProc, hω]

/-- With infinite lifetime, a box event of the killed driver at finitely many rational times is the killed-state
event of Theorem 2.2's uniqueness statement, up to a null set. -/
theorem measure_box_eq_killedState {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
    {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {I : Finset ℚ≥0} {n : ℕ}
    (e : Fin n ≃ I) (A : I → Set ℝ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    P {ω | ∀ i : I, killedProc W ζ (i : ℚ≥0) ω ∈ A i} =
      P {ω | ∀ j, (((e j : ℚ≥0) : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
        (W ((e j : ℚ≥0) : ℝ≥0) ω, (fun i => VL i ((e j : ℚ≥0) : ℝ≥0) ω),
          (fun i => VR i ((e j : ℚ≥0) : ℝ≥0) ω), B ((e j : ℚ≥0) : ℝ≥0) ω) ∈ A (e j) ×ˢ univ} := by
  refine measure_congr ?_
  filter_upwards [hζ] with ω hω
  apply propext
  simp only [killedProc, hω, ENNReal.coe_lt_top, ↓reduceIte, true_and, mem_prod, mem_univ, and_true]
  exact ⟨fun h j => h (e j), fun h i => by simpa using h (e.symm i)⟩

section Law

variable {κ : ℝ} {ρL ρR : Fin 1 → ℝ}

/-- **The rational-time driving law of a two-seed evolution is unique** (weights `> −2`). -/
theorem map_killedRestrict_eq (hκ : 0 < κ) (hρL : -2 < ρL 0) (hρR : -2 < ρR 0)
    (hJ : JacobiDiffusionExistsStatement)
    {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ : Fin 1 → ℝ≥0 → Ω₁ → ℝ}
    {VR₁ : Fin 1 → ℝ≥0 → Ω₁ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞}
    (h₁ : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ}
    {VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (h₂ : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂) :
    P₁.map (killedRestrict W₁ ζ₁) = P₂.map (killedRestrict W₂ ζ₂) := by
  have hm₁ := measurable_killedRestrict h₁.2.1
  have hm₂ := measurable_killedRestrict h₂.2.1
  have hζ₁ := ae_lifetime_eq_top_twoSeed hκ hρL hρR hJ h₁
  have hζ₂ := ae_lifetime_eq_top_twoSeed hκ hρL hρR hJ h₂
  -- the box probabilities agree
  have key : ∀ (I : Finset ℚ≥0) (A : I → Set ℝ), (∀ i, MeasurableSet (A i)) →
      P₁ {ω | ∀ i : I, killedProc W₁ ζ₁ (i : ℚ≥0) ω ∈ A i} =
        P₂ {ω | ∀ i : I, killedProc W₂ ζ₂ (i : ℚ≥0) ω ∈ A i} := by
    intro I A hA
    set e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
    set ts : Fin (Fintype.card I) → ℝ≥0 := fun j => ((e j : ℚ≥0) : ℝ≥0)
    set A' : Fin (Fintype.card I) → Set (ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ) × ℝ) :=
      fun j => A (e j) ×ˢ univ
    have hA' : ∀ j, MeasurableSet (A' j) := fun j => (hA _).prod MeasurableSet.univ
    have hK := Sec2.TwoSeed.measure_killedState_eq_twoSeed_of_gt hκ hρL hρR h₁ h₂ _ ts A' hA'
    rw [measure_box_eq_killedState e A (VL := VL₁) (VR := VR₁) (B := B₁) hζ₁,
      measure_box_eq_killedState e A (VL := VL₂) (VR := VR₂) (B := B₂) hζ₂]
    exact hK
  have hfd : ∀ I : Finset ℚ≥0, (P₁.map (killedRestrict W₁ ζ₁)).map I.restrict =
      (P₂.map (killedRestrict W₂ ζ₂)).map I.restrict := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) hm₁,
      Measure.map_map (Finset.measurable_restrict I) hm₂]
    refine ext_of_generate_finite _ generateFrom_pi.symm isPiSystem_pi (fun s hs => ?_) ?_
    · obtain ⟨A, hA', rfl⟩ := hs
      have hA : ∀ i, MeasurableSet (A i) := fun i => hA' i (mem_univ i)
      rw [Measure.map_apply ((Finset.measurable_restrict I).comp hm₁) (MeasurableSet.univ_pi hA),
        Measure.map_apply ((Finset.measurable_restrict I).comp hm₂) (MeasurableSet.univ_pi hA)]
      have h := key I A hA
      simpa [Set.preimage, Set.mem_univ_pi, killedRestrict] using h
    · rw [Measure.map_apply ((Finset.measurable_restrict I).comp hm₁) MeasurableSet.univ,
        Measure.map_apply ((Finset.measurable_restrict I).comp hm₂) MeasurableSet.univ]
      simp
  exact IsProjectiveLimit.unique (P := fun I => (P₁.map (killedRestrict W₁ ζ₁)).map I.restrict)
    (fun I => rfl) (fun I => (hfd I).symm)

/-- **Transfer of a coded driving-path event** between two-seed evolutions (weights `> −2`): if `G` is a measurable
set of rational-time values coding a property of continuous drivers vanishing at `0`, and the property holds almost
surely for one evolution, it holds almost surely for every evolution. -/
theorem ae_transfer_of_coding (hκ : 0 < κ) (hρL : -2 < ρL 0) (hρR : -2 < ρR 0)
    (hJ : JacobiDiffusionExistsStatement) {p : (ℝ≥0 → ℝ) → Prop} {G : Set (ℚ≥0 → ℝ)}
    (hG : MeasurableSet G)
    (hGp : ∀ w : ℝ≥0 → ℝ, Continuous w → w 0 = 0 → ((fun q : ℚ≥0 => w q) ∈ G ↔ p w))
    {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ : Fin 1 → ℝ≥0 → Ω₁ → ℝ}
    {VR₁ : Fin 1 → ℝ≥0 → Ω₁ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞}
    (h₁ : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hp₁ : ∀ᵐ ω ∂P₁, p fun t => W₁ t ω)
    {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ}
    {VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (h₂ : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂) :
    ∀ᵐ ω ∂P₂, p fun t => W₂ t ω := by
  have hm₁ := measurable_killedRestrict h₁.2.1
  have hm₂ := measurable_killedRestrict h₂.2.1
  have hζ₁ := ae_lifetime_eq_top_twoSeed hκ hρL hρR hJ h₁
  have hζ₂ := ae_lifetime_eq_top_twoSeed hκ hρL hρR hJ h₂
  -- continuity of a driver with infinite lifetime
  have hcont : ∀ {w : ℝ≥0 → ℝ} {vL vR : Fin 1 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ},
      IsIntegratedSLEPath κ (fun _ => 0) (fun _ => 0) ρL ρR w vL vR b ⊤ → Continuous w ∧ w 0 = 0 := by
    intro w vL vR b hpath
    refine ⟨continuousOn_univ.1 ?_, hpath.1⟩
    simpa using hpath.2.2.2.1
  have hgood₁ : ∀ᵐ ω ∂P₁, killedRestrict W₁ ζ₁ ω ∈ G := by
    filter_upwards [hp₁, hζ₁, h₁.2.2.2.2] with ω hω hζω hpath
    rw [hζω] at hpath
    obtain ⟨hc, h0⟩ := hcont hpath
    rw [killedRestrict_eq_of_top hζω]
    exact (hGp _ hc h0).2 hω
  have hgood₂ : ∀ᵐ ω ∂P₂, killedRestrict W₂ ζ₂ ω ∈ G := by
    have h := (ae_map_iff hm₁.aemeasurable hG).2 hgood₁
    rw [map_killedRestrict_eq hκ hρL hρR hJ h₁ h₂] at h
    exact (ae_map_iff hm₂.aemeasurable hG).1 h
  filter_upwards [hgood₂, hζ₂, h₂.2.2.2.2] with ω hω hζω hpath
  rw [hζω] at hpath
  obtain ⟨hc, h0⟩ := hcont hpath
  rw [killedRestrict_eq_of_top hζω] at hω
  exact (hGp _ hc h0).1 hω

end Law

/-! ### Named inputs and the stopped transfer -/

/-- **Named input (§7.4): the measurable coding of the stopped-trace event** (Aux. lemma 126's proof, pp. 399–400:
"At each rational time the inverse Loewner map, and its vertical tip limit along `1/n` when it exists, are measurable
functions of that history … Existence of a continuous extension is a countable uniform continuity condition, and
equality of its filled hulls with the driving hulls can be checked at rational times by their complements and a
countable rational planar basis. This gives standard Borel versions of the curve and the relevant continuous-trace
event."): for every `r > 0` there is a measurable set of rational-time values whose members are exactly the
restrictions of the continuous drivers (vanishing at `0`) that have a generating trace through the buffered stop
`S_r`. -/
def StoppedTraceCodingStatement : Prop :=
  ∀ r : ℝ, 0 < r → ∃ G : Set (ℚ≥0 → ℝ), MeasurableSet G ∧
    ∀ w : ℝ≥0 → ℝ, Continuous w → w 0 = 0 →
      ((fun q : ℚ≥0 => w q) ∈ G ↔ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w (Dilation.bufferedStop r w) η)

/-- **Named input (§7.4): the change of measure of Aux. lemma 126** ((FS11.1)–(FS11.4), pp. 399–401, with the
extension Aux. lemma 54, p. 246; the local comparison (HL3)–(HL9) of Aux. lemma 55, pp. 247–249): from a reference
as in `Aux126Reference`, there are a buffer radius `r > 0` and one integrated two-seed evolution with the seed weights
`rL, rR` whose driver almost surely has a generating trace through its buffered stop `S_r` ("Equivalence in (FS11.2)
preserves continuity of the reference trace through `S_r` … Aux. lemma 54 extends our stopped pair to a full
original two-seed coupling"). -/
def Aux126GirsanovStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR → Aux126Reference.{v} κ rL rR →
    ∃ r : ℝ, 0 < r ∧
      ∃ (Ω : Type v) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ)
        (VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
        IsIntegratedSLEEvolution κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ ∧
          ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ,
            IsGeneratingTrace (fun t => W t ω) (Dilation.bufferedStop r fun t => W t ω) η

/-- **Aux. lemma 126, the stopped transfer**: `Aux126StoppedTraceStatement` from the change of measure (one two-seed
evolution with a stopped trace), the measurable coding of the stopped-trace event and the existence of a Jacobi
diffusion; the law transfer (`ae_transfer_of_coding`) is proved. -/
theorem aux126StoppedTraceStatement_of_inputs (hJ : JacobiDiffusionExistsStatement)
    (hcode : StoppedTraceCodingStatement) (hGir : Aux126GirsanovStatement.{v}) :
    Aux126StoppedTraceStatement.{u, v} := by
  intro κ hκ rL rR hL hR href
  obtain ⟨r, hr, Ω₀, m₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hE₀, htr₀⟩ := hGir κ hκ rL rR hL hR href
  obtain ⟨G, hG, hGp⟩ := hcode r hr
  refine ⟨r, hr, fun P _ 𝓕 W VL VR B ζ hE => ?_⟩
  exact ae_transfer_of_coding (ρL := fun _ => rL) (ρR := fun _ => rR) hκ hL hR hJ hG hGp hE₀ htr₀ hE

/-- **Lemma 7.25, finite-time continuity** (p. 413), `LP.Lemma725TraceStatement`, from the reference of Lemma 7.25
(Aux. lemmas 130, 125, 127), the change of measure of Aux. lemma 126, the measurable coding of the stopped-trace event
and the existence of a Jacobi diffusion. -/
theorem lemma725TraceStatement_of_girsanov (hJ : JacobiDiffusionExistsStatement)
    (hRef : Lemma725ReferenceStatement.{v}) (hGir : Aux126GirsanovStatement.{v})
    (hcode : StoppedTraceCodingStatement) : LP.Lemma725TraceStatement.{u} :=
  lemma725TraceStatement_of_inputs hJ hRef (aux126StoppedTraceStatement_of_inputs hJ hcode hGir)

end Sec7

end InteractingSLE
