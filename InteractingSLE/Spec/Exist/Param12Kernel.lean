/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedDet
import InteractingSLE.Spec.Sec7.DeterminationGraph

/-!
# Theorem 1.2 jointly measurable in the force word, from the per-word Theorem 1.2 and a measurable coupling law

Packet PROVE-PARAM12 (ruling R44). PROVE-STAGED named `Exist.Staged.Theorem12ParamStatement`: the frozen Theorem 1.2
with the determination map `Φ` jointly Borel in the word data `w = ((xL, xR), (ρL, ρR))` and the field. This file
derives it from

* the frozen per-word Theorem 1.2 (`Exist.Theorem12Statement`, its anchor type; the DRAFT anchor is not imported),
* the frozen Theorem 1.3 (`Exist.Theorem13Statement`; it gives the generating trace, so that the trace code determines
  the driver code), and
* **`CouplingLawKernelStatement`** (named input): a Borel *family* of Theorem 1.1's couplings, in the weakest form the
  argument uses. There is a finite kernel `μ` from word data to (field, killed driver code) such that for every
  ordered word some optional hull coupling of that word has joint law `μ w` of its field and its killed driver code
  (`fieldCode`).

**The argument** (`theorem12ParamStatement_of_couplingLawKernel`):

1. *One law per word.* By Theorems 1.2–1.3 every coupling of a word has a field-determined killed history
   (`hasFieldDeterminedHistories`). The mixture argument of §D.2.3 (`Determination.exists_common_graph`) then gives one
   graph for any two couplings, and the field law is the same in all couplings (`Determination.map_field_eq`). Hence the
   joint law of the field and the killed driver code is the same in every coupling of the word (`map_fieldCode_eq`). In
   particular it is `μ w`.
2. *A jointly measurable conditional law.* `K = Kernel.condKernel μ` is a Markov kernel on (word data) × (field),
   jointly measurable, with `μ w = (μ w).fst ⊗ K(w, ·)` for **every** `w` (`Kernel.disintegrate`; the field space is
   standard Borel, `LQGMetric.standardBorelSpace_distOn`).
3. *Dirac for every word.* In a given coupling of `w`, the killed driver code is `G(h)` almost surely, for a Borel
   `G` (`exists_graph_fieldCode`, from Theorem 1.2 through PROVE-STAGED's `ae_detCode_eq`). So `μ w` is carried by the
   graph of `G`, and `K(w, f) = δ_{G f}` for almost every field `f` (`ae_condKernel_eq_zero`).
4. *Read off the point.* `ptOf ν = L(∫⁻ g dν)` for a bounded Borel injection `g` of the driver codes and a Borel left
   inverse `L` (Lusin–Souslin) returns `z` at every probability measure carried by `{z}` (`ptOf_eq`). The
   determination map is `Φ(w, f) = drivingTrace(ptOf K(w, f))` (`LP.drivingTrace`, the deterministic reconstruction of
   LP11). It is jointly measurable, and on every coupling it returns the lifetime and the trace
   (`LP.drivingTrace_eq`).

Step 1 is why no "almost every word" appears: the disintegration identity holds at every `w`, and the per-word
uniqueness of the law identifies `μ w` for every ordered word.

`CouplingLawKernelStatement` is equivalent to `Theorem12ParamStatement` given Theorems 1.1–1.3 (the converse
direction pushes the field law forward by `(f ↦ (f, detCode Φ (w, f)))`), so it is the exact remaining input. Its
content is that Theorem 1.1's coupling law depends measurably on the word. See the handoff `PROVE-PARAM12.md`, §5.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Exist

namespace Param12

open Sec2.Assembly LQGMetric Staged

/-! ### The field and the killed driver code of a coupling -/

/-- The field and the killed driver code (lifetime and killed dyadic code of the driver) of a coupling. -/
def fieldCode {Ω : Type*} (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) :
    DistOn upperHalfPlaneOpens × DCode :=
  (h ω, (ζ ω, killedCode W 0 ζ ω))

theorem measurable_fieldCode {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) : Measurable (fieldCode h W ζ) :=
  hC.2.1.prodMk ((measurable_lifetime hC.1.2.1).prodMk (measurable_killedCode hC.1.2.1 0))

/-- **Named input: Theorem 1.1's coupling law is a Borel kernel in the word.** For `κ > 0` and numbers of marks, a
finite kernel `μ` from word data to (field, killed driver code) such that, for every ordered word, some optional hull
coupling of the word (at universe `u`) has joint law `μ w` of its field and its killed driver code. (For unordered
words `μ` is unconstrained.) -/
def CouplingLawKernelStatement : Prop :=
  ∀ (κ : ℝ) (_ : 0 < κ) (nL nR : ℕ),
    ∃ μ : Kernel (WordData nL nR) (DistOn upperHalfPlaneOpens × DCode), IsFiniteKernel μ ∧
      ∀ (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR →
        ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
          (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
          (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
          (h : Ω → DistOn upperHalfPlaneOpens),
          IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h ∧
            P.map (fieldCode h W ζ) = μ (((xL, xR), (ρL, ρR)))

/-! ### Step 1: one law per word -/

/-- **Theorems 1.2–1.3 give field-determined killed histories** for every coupling of an ordered word
(`Exist.exists_fieldDetermination`, read through the decoding maps). -/
theorem hasFieldDeterminedHistories (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u}) {κ : ℝ}
    (hκ : 0 < κ) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) : LP.HasFieldDeterminedHistories.{u} κ xL xR ρL ρR := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ h hC
  obtain ⟨Ψ, S, ηf, hΨm, hS, hΨ, htr⟩ := exists_fieldDetermination h12 h13 hκ hF hC
  refine ⟨fun f => (cζ (Ψ f), cw (Ψ f), cvL (Ψ f), cvR (Ψ f)), ?_, ?_⟩
  · refine (measurable_cζ.comp hΨm).prodMk ((measurable_cw.comp hΨm).prodMk
      ((measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun t => (measurable_cvL_at i t).comp hΨm).prodMk
        (measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun t => (measurable_cvR_at j t).comp hΨm)))
  · filter_upwards [hΨ] with ω hω
    exact ⟨hω.2.1, hω.2.2⟩

/-- The killed driver code read off a killed history. -/
def histCode {nL nR : ℕ} (p : ℝ≥0∞ × (ℝ≥0 → ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) : DCode :=
  (p.1, fun n k => if dyad n k = 0 then 0 else if (dyad n k : ℝ≥0∞) < p.1 then (p.2 (dyad n k)).1 else 0)

theorem measurable_histCode {nL nR : ℕ} : Measurable (histCode (nL := nL) (nR := nR)) := by
  refine measurable_fst.prodMk (measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k => ?_)
  by_cases h0 : dyad n k = 0
  · simp only [h0, ↓reduceIte]
    exact measurable_const
  · simp only [h0, ↓reduceIte]
    exact Measurable.ite (measurableSet_lt measurable_const measurable_fst)
      (measurable_fst.comp ((measurable_pi_apply _).comp measurable_snd)) measurable_const

theorem histCode_killedHistory {nL nR : ℕ} {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) :
    histCode (Determination.killedHistory W VL VR ζ ω) = (ζ ω, killedCode W 0 ζ ω) := by
  refine Prod.ext rfl (funext fun n => funext fun k => ?_)
  simp only [histCode, Determination.killedHistory, killedCode]
  by_cases h0 : dyad n k = 0
  · simp only [h0, ↓reduceIte]
  · by_cases hlt : (dyad n k : ℝ≥0∞) < ζ ω
    · simp only [h0, hlt, ↓reduceIte]
    · simp only [h0, hlt, ↓reduceIte]

/-- **The joint law of the field and the killed driver code is the same in every coupling** of an ordered word
(from Theorems 1.2–1.3 and the mixture argument, `Determination.exists_common_graph`). -/
theorem map_fieldCode_eq (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) {Ω₁ Ω₂ : Type u} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂} {W₁ : ℝ≥0 → Ω₁ → ℝ} {W₂ : ℝ≥0 → Ω₂ → ℝ}
    {VL₁ : Fin nL → ℝ≥0 → Ω₁ → ℝ} {VL₂ : Fin nL → ℝ≥0 → Ω₂ → ℝ} {VR₁ : Fin nR → ℝ≥0 → Ω₁ → ℝ}
    {VR₂ : Fin nR → ℝ≥0 → Ω₂ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞}
    {ζ₂ : Ω₂ → ℝ≥0∞} {h₁ : Ω₁ → DistOn upperHalfPlaneOpens} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}
    (hC₁ : IsOptionalHullCoupling κ xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ h₁)
    (hC₂ : IsOptionalHullCoupling κ xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂) :
    P₁.map (fieldCode h₁ W₁ ζ₁) = P₂.map (fieldCode h₂ W₂ ζ₂) := by
  obtain ⟨Ψ, hΨm, g₁, g₂⟩ :=
    Determination.exists_common_graph (hasFieldDeterminedHistories h12 h13 hκ hF) hC₁ hC₂
  set F : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens × DCode :=
    fun f => (f, histCode (Determination.graphHistory (Ψ f))) with hFdef
  have hFm : Measurable F :=
    measurable_id.prodMk (measurable_histCode.comp (Determination.measurable_graphHistory.comp hΨm))
  have a₁ : fieldCode h₁ W₁ ζ₁ =ᵐ[P₁] F ∘ h₁ := by
    filter_upwards [g₁.killedHistory_ae_eq] with ω hω
    simp only [fieldCode, Function.comp_apply, hFdef, ← hω, histCode_killedHistory]
  have a₂ : fieldCode h₂ W₂ ζ₂ =ᵐ[P₂] F ∘ h₂ := by
    filter_upwards [g₂.killedHistory_ae_eq] with ω hω
    simp only [fieldCode, Function.comp_apply, hFdef, ← hω, histCode_killedHistory]
  rw [Measure.map_congr a₁, Measure.map_congr a₂, ← Measure.map_map hFm hC₁.2.1,
    ← Measure.map_map hFm hC₂.2.1, Determination.map_field_eq hC₁ hC₂]

/-! ### Step 3: the killed driver code is a Borel function of the field -/

/-- On the good set, the driver code of a history code is the killed code of any path that agrees with its decoded
driver before the lifetime. -/
theorem dOf_eq_killedCode {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {x₀ : XCode nL nR} (hx : x₀ ∈ DetSet a xL xR ρL ρR) {Ω : Type*} {W : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {ω : Ω} (hζ : cζ x₀ = ζ ω) (hw : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → cw x₀ t = W t ω) :
    dOf x₀ = (ζ ω, killedCode W 0 ζ ω) := by
  have hz := dOf_mem_DSet hx
  have h1 : (dOf x₀).1 = ζ ω := hζ
  refine Prod.ext hζ (funext fun n => funext fun k => ?_)
  show (dOf x₀).2 n k = killedCode W 0 ζ ω n k
  simp only [killedCode]
  by_cases h0 : dyad n k = 0
  · simp only [h0, ↓reduceIte]
    exact hz.2.1 n k h0
  · simp only [h0, ↓reduceIte]
    by_cases hlt : (dyad n k : ℝ≥0∞) < ζ ω
    · simp only [hlt, ↓reduceIte]
      have hlt' : (dyad n k : ℝ≥0∞) < (dOf x₀).1 := by rw [h1]; exact hlt
      rw [← (hz.1 n k hlt').dec_dyad le_rfl]
      exact hw _ hlt
    · simp only [hlt, ↓reduceIte]
      exact hz.2.2.1 n k (by rw [h1]; exact hlt)

/-- **The killed driver code is almost surely a Borel function `G` of the field** in every coupling of an ordered
word, and it decodes to the driver before the lifetime (from Theorems 1.2–1.3 through `Staged.ae_detCode_eq`). -/
theorem exists_graph_fieldCode (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u}) {κ : ℝ}
    (hκ : 0 < κ) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) :
    ∃ G : DistOn upperHalfPlaneOpens → DCode, Measurable G ∧ ∀ᵐ ω ∂P,
      (ζ ω, killedCode W 0 ζ ω) = G (h ω) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → dec (killedCode W 0 ζ ω) t = W t ω := by
  obtain ⟨Φ, hΦm, hΦ⟩ := h12 κ hκ xL xR ρL ρR hF hC
  set Φ' : WordData nL nR × DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ) := fun p => Φ p.2 with hΦ'
  refine ⟨fun f => detCode Φ' (((xL, xR), (ρL, ρR)), f),
    (measurable_detCode (hΦm.comp measurable_snd)).comp (measurable_const.prodMk measurable_id), ?_⟩
  filter_upwards [ae_detCode_eq (Φ := Φ') hκ hF h13 hC hΦ] with ω hω
  obtain ⟨x₀, hx₀, hζx, hcw, hdet⟩ := hω
  have hd : dOf x₀ = (ζ ω, killedCode W 0 ζ ω) := dOf_eq_killedCode hx₀ hζx fun t ht => (hcw t ht).1
  refine ⟨by rw [hdet, hd], fun t ht => ?_⟩
  have h2 : killedCode W 0 ζ ω = x₀.2.2.1 := (congrArg Prod.snd hd).symm
  rw [h2]
  exact (hcw t ht).1

/-! ### Step 4: reading the point of a Dirac law of driver codes -/

/-- A bounded Borel injection of the driver codes into `[0, ∞)` (through a Borel embedding into `ℝ` and `arctan`). -/
theorem exists_dcodeEnc : ∃ g : DCode → ℝ≥0∞, Measurable g ∧ Function.Injective g := by
  obtain ⟨e, he⟩ := exists_measurableEmbedding_real DCode
  have hpos : ∀ z, 0 ≤ Real.arctan (e z) + 2 := fun z => by
    have h1 := Real.neg_pi_div_two_lt_arctan (e z)
    have h2 := Real.pi_le_four
    linarith
  refine ⟨fun z => ENNReal.ofReal (Real.arctan (e z) + 2), ?_, fun z z' hzz => ?_⟩
  · exact ENNReal.measurable_ofReal.comp ((Real.continuous_arctan.measurable.comp he.measurable).add_const 2)
  · have h := (ENNReal.ofReal_eq_ofReal_iff (hpos z) (hpos z')).1 hzz
    exact he.injective (Real.arctan_strictMono.injective (by linarith))

/-- The chosen bounded Borel injection of driver codes. -/
def dcodeEnc : DCode → ℝ≥0∞ := exists_dcodeEnc.choose

theorem measurable_dcodeEnc : Measurable dcodeEnc := exists_dcodeEnc.choose_spec.1

theorem injective_dcodeEnc : Function.Injective dcodeEnc := exists_dcodeEnc.choose_spec.2

theorem exists_dcodeDec : ∃ L : ℝ≥0∞ → DCode, Measurable L ∧ ∀ z, L (dcodeEnc z) = z := by
  obtain ⟨L, hLm, hL⟩ := exists_measurable_leftInverse_of_injOn measurable_dcodeEnc MeasurableSet.univ
    injective_dcodeEnc.injOn
  exact ⟨L, hLm, fun z => hL z (mem_univ z)⟩

/-- A Borel left inverse of `dcodeEnc` (Lusin–Souslin). -/
def dcodeDec : ℝ≥0∞ → DCode := exists_dcodeDec.choose

theorem measurable_dcodeDec : Measurable dcodeDec := exists_dcodeDec.choose_spec.1

theorem dcodeDec_dcodeEnc (z : DCode) : dcodeDec (dcodeEnc z) = z := exists_dcodeDec.choose_spec.2 z

/-- The point read off a law of driver codes: `dcodeDec (∫⁻ dcodeEnc dν)`. -/
def ptOf (ν : Measure DCode) : DCode := dcodeDec (∫⁻ z, dcodeEnc z ∂ν)

/-- `ptOf` composed with a kernel is measurable. -/
theorem measurable_ptOf_kernel {α : Type*} [MeasurableSpace α] (K : Kernel α DCode) :
    Measurable fun a => ptOf (K a) :=
  measurable_dcodeDec.comp measurable_dcodeEnc.lintegral_kernel

/-- **`ptOf` returns the point of a probability law carried by one point.** -/
theorem ptOf_eq {ν : Measure DCode} [IsProbabilityMeasure ν] {a : DCode} (h : ν {z | z ≠ a} = 0) :
    ptOf ν = a := by
  have hae : ∀ᵐ z ∂ν, dcodeEnc z = dcodeEnc a := by
    have : ∀ᵐ z ∂ν, z ∉ {z | z ≠ a} := measure_eq_zero_iff_ae_notMem.1 h
    filter_upwards [this] with z hz
    simp only [not_not] at hz
    rw [hz]
  rw [ptOf, lintegral_congr_ae hae, lintegral_const, measure_univ, mul_one, dcodeDec_dcodeEnc]

/-! ### Step 2–3: the conditional kernel is Dirac at the graph for every word -/

/-- If a finite kernel at `w` is the law of `(f, G f)` under a law `γ` of fields, its conditional kernel at `(w, f)` is
carried by `G f` for `γ`-almost every `f`. -/
theorem ae_condKernel_eq_zero {α : Type*} [MeasurableSpace α]
    (μ : Kernel α (DistOn upperHalfPlaneOpens × DCode)) [IsFiniteKernel μ] (w : α)
    (γ : Measure (DistOn upperHalfPlaneOpens)) {G : DistOn upperHalfPlaneOpens → DCode} (hG : Measurable G)
    (hμ : μ w = γ.map fun f => (f, G f)) :
    ∀ᵐ f ∂γ, Kernel.condKernel μ (w, f) {z | z ≠ G f} = 0 := by
  have hGg : Measurable fun f : DistOn upperHalfPlaneOpens => (f, G f) := measurable_id.prodMk hG
  set S : Set (DistOn upperHalfPlaneOpens × DCode) := {q | q.2 ≠ G q.1} with hSdef
  have hSeq : S = ((fun q : DistOn upperHalfPlaneOpens × DCode => (q.2, G q.1)) ⁻¹' diagonal DCode)ᶜ := by
    ext q
    simp [hSdef]
  have hS : MeasurableSet S := by
    rw [hSeq]
    exact (measurableSet_diagonal.preimage (measurable_snd.prodMk (hG.comp measurable_fst))).compl
  have h0 : μ w S = 0 := by
    rw [hμ, Measure.map_apply hGg hS]
    have : (fun f => (f, G f)) ⁻¹' S = ∅ := by
      ext f
      simp [hSdef]
    rw [this, measure_empty]
  have hfst : Kernel.fst μ w = γ := by
    rw [Kernel.fst_apply, hμ, Measure.map_map measurable_fst hGg]
    exact Measure.map_id
  have hdis : (Kernel.fst μ ⊗ₖ Kernel.condKernel μ) w S = μ w S := by
    rw [Kernel.disintegrate μ (Kernel.condKernel μ)]
  rw [Kernel.compProd_apply hS, hfst, h0] at hdis
  have hm := Kernel.measurable_kernel_prodMk_left' (η := Kernel.condKernel μ) hS w
  have hz := (lintegral_eq_zero_iff hm).1 hdis
  filter_upwards [hz] with f hf
  exact hf

/-! ### The theorem -/

/-- **Theorem 1.2 jointly measurable in the force word** (`Staged.Theorem12ParamStatement`) from the per-word
Theorems 1.2 and 1.3 and the named input `CouplingLawKernelStatement` (Theorem 1.1's coupling law, Borel in the
word). The determination map is `Φ(w, f) = drivingTrace(ptOf (condKernel μ (w, f)))`. -/
theorem theorem12ParamStatement_of_couplingLawKernel (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) (hK : CouplingLawKernelStatement.{u}) : Theorem12ParamStatement.{u} := by
  intro κ hκ nL nR
  obtain ⟨μ, hμf, hμ⟩ := hK κ hκ nL nR
  set K := Kernel.condKernel μ with hKdef
  have hpt := measurable_ptOf_kernel K
  refine ⟨fun p => LP.drivingTrace ((ptOf (K p)).1, dec (ptOf (K p)).2),
    LP.measurable_drivingTrace.comp ((measurable_fst.comp hpt).prodMk (measurable_dec_snd.comp hpt)), ?_⟩
  intro xL xR ρL ρR hF Ω mΩ P _ 𝓕 W VL VR B ζ h hC
  obtain ⟨Ω', mΩ', P', hP', 𝓕', W', VL', VR', B', ζ', h', hC', hlaw'⟩ := hμ xL xR ρL ρR hF
  have hlaw : P.map (fieldCode h W ζ) = μ (((xL, xR), (ρL, ρR))) :=
    (map_fieldCode_eq h12 h13 hκ hF hC hC').trans hlaw'
  obtain ⟨G, hGm, hG⟩ := exists_graph_fieldCode h12 h13 hκ hF hC
  have hGg : Measurable fun f : DistOn upperHalfPlaneOpens => (f, G f) := measurable_id.prodMk hGm
  have hμw : μ (((xL, xR), (ρL, ρR))) = (P.map h).map fun f => (f, G f) := by
    rw [← hlaw, Measure.map_map hGg hC.2.1]
    refine Measure.map_congr ?_
    filter_upwards [hG] with ω hω
    simp only [fieldCode, Function.comp_apply, hω.1]
  have hdirac := ae_condKernel_eq_zero μ (((xL, xR), (ρL, ρR))) (P.map h) hGm hμw
  have hptω : ∀ᵐ ω ∂P, ptOf (K (((xL, xR), (ρL, ρR)), h ω)) = G (h ω) := by
    filter_upwards [ae_of_ae_map hC.2.1.aemeasurable hdirac] with ω hω
    exact ptOf_eq hω
  filter_upwards [hptω, hG, hC.1.2.2.2.2] with ω hpω hGω hpath
  obtain ⟨hw0, -, -, hcw, -⟩ := hpath
  obtain ⟨hGe, hdec⟩ := hGω
  have hE : LP.drivingTrace ((ptOf (K (((xL, xR), (ρL, ρR)), h ω))).1,
      dec (ptOf (K (((xL, xR), (ρL, ρR)), h ω))).2) = LP.drivingTrace (ζ ω, dec (killedCode W 0 ζ ω)) := by
    rw [hpω, ← hGe]
  refine ⟨by rw [hE]; rfl, fun η hη t => ?_⟩
  rw [hE, LP.drivingTrace_eq hη hcw hw0 hdec]

end Param12

end Exist

end InteractingSLE
