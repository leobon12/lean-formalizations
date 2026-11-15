/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.Param12Canonical
import InteractingSLE.Spec.Sec7.Lemma71HInputs
import InteractingSLE.Spec.Zhan.TransienceTrace

/-!
# Theorem 1.2 jointly measurable in the word, for words satisfying (4.4), without Theorems 1.2–1.3

Packet PROVE-STRIPSYS21, item (i) (ruling R48). PROVE-PARAM12/12B/12C derive the word-measurable Theorem 1.2
(`Exist.Staged.Theorem12ParamStatement`) from the frozen Theorems 1.2–1.3, so it may not be used in the proofs of
Theorems 1.2–1.3 themselves. The restart of an angle-varying path (specification §7.4, p. 410: "Conditional field
determination makes the continuation measurable from the first prefix and the original field") needs the
determination map jointly measurable in the conditional word, but only for words satisfying (4.4). This file proves
that restricted statement from §4.2 alone:

* **`Theorem12ParamCond44Statement`**: for `0 < κ < 4` and numbers of marks, one Borel map `Φ` of the word data and the
  field returns, for every optional hull coupling of every ordered word satisfying (4.4), almost surely the lifetime and
  the capacity-parametrized trace frozen after the lifetime (the conclusion of `Theorem12ParamStatement`);
* **`theorem12ParamCond44Statement_of_reference`**: it holds given the §4.2 reference coupling
  (`Lemma71H.Cond44ReferenceStatement`, the reference half of §4.2's proof of Theorem 1.2 under (4.4); an input of
  Theorems 1.2–1.3 that does not use them).

Proof (PROVE-PARAM12's argument with the hypotheses replaced, `Param12Kernel.lean`): on (4.4) words every coupling has a
field-determined killed history (§4.2 with Aux. lemma 23, `Lemma71H.hasFieldDeterminedHistories_of_cond44`), so all
couplings of a word have one joint law of field and killed driver code (`map_fieldCode_eq_of_det`); PROVE-PARAM12C's
Borel descriptions (`Exist.Param12.borelCanonicalCouplingStatement`, no hypotheses) and Souslin's theorem
(`Exist.Param12.exists_kernel_of_unique`) on the measurable set of (4.4) words make this law a kernel; its conditional
kernel given the field is Dirac at the field-determined driver code; `ptOf` reads the point and LP11's deterministic
reconstruction (`LP.drivingTrace`) the trace.

The file also gives the driver-code determination without Theorem 1.3 (`ae_detCode_eq_of_trace`: PROVE-STAGED's
`Exist.Staged.ae_detCode_eq` with the trace supplied, for (4.4) words by Remark 2.3, `ae_trace_of_cond44`) and the
field-determined staged driver built from the restricted map (`admDrv`, PROVE-STAGED's `stagedDrv` with `Φ` restricted
to (4.4) words).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace AdmCode

open Sec2.Assembly LQGMetric Exist.Staged Exist.Param12

/-! ### The words satisfying (4.4) -/

/-- The ordered words satisfying (4.4) (left partial sums `≥ κ/2 − 2`, right partial sums `≥ 0`). -/
def cond44Words (κ : ℝ) (nL nR : ℕ) : Set (WordData nL nR) :=
  {w | IsOrderedForceWord w.1.1 w.1.2 ∧ Sec4.Cond44 κ w.2.1 w.2.2}

theorem measurableSet_cond44Words (κ : ℝ) (nL nR : ℕ) : MeasurableSet (cond44Words κ nL nR) := by
  have hρL : ∀ i : Fin nL, Measurable fun w : WordData nL nR => w.2.1 i := fun i =>
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  have hρR : ∀ j : Fin nR, Measurable fun w : WordData nL nR => w.2.2 j := fun j =>
    (measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)
  have hle : ∀ {f g : WordData nL nR → ℝ}, Measurable f → Measurable g → Measurable fun w => f w ≤ g w :=
    fun hf hg => measurableSet_setOfPred.1 (measurableSet_le hf hg)
  have h44 : MeasurableSet {w : WordData nL nR | Sec4.Cond44 κ w.2.1 w.2.2} := by
    refine measurableSet_setOfPred.2 ?_
    unfold Sec4.Cond44
    refine Measurable.and ?_ ?_
    · refine Measurable.forall fun j => measurable_const_imp _ (measurable_const_imp _ ?_)
      exact hle measurable_const (Finset.measurable_sum _ fun i _ => hρL i)
    · refine Measurable.forall fun j => measurable_const_imp _ (measurable_const_imp _ ?_)
      exact hle measurable_const (Finset.measurable_sum _ fun i _ => hρR i)
  exact (measurableSet_isOrderedForceWord nL nR).inter h44

/-! ### One law per word, and the driver code as a function of the field -/

section Det

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The joint law of the field and the killed driver code is the same in every coupling** of a word whose
couplings have field-determined killed histories (PROVE-PARAM12's `map_fieldCode_eq` with determination as the
hypothesis instead of Theorems 1.2–1.3). -/
theorem map_fieldCode_eq_of_det (hdet : LP.HasFieldDeterminedHistories.{u} κ xL xR ρL ρR)
    {Ω₁ Ω₂ : Type u} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂} {W₁ : ℝ≥0 → Ω₁ → ℝ} {W₂ : ℝ≥0 → Ω₂ → ℝ}
    {VL₁ : Fin nL → ℝ≥0 → Ω₁ → ℝ} {VL₂ : Fin nL → ℝ≥0 → Ω₂ → ℝ} {VR₁ : Fin nR → ℝ≥0 → Ω₁ → ℝ}
    {VR₂ : Fin nR → ℝ≥0 → Ω₂ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞}
    {ζ₂ : Ω₂ → ℝ≥0∞} {h₁ : Ω₁ → DistOn upperHalfPlaneOpens} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}
    (hC₁ : IsOptionalHullCoupling κ xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ h₁)
    (hC₂ : IsOptionalHullCoupling κ xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂) :
    P₁.map (fieldCode h₁ W₁ ζ₁) = P₂.map (fieldCode h₂ W₂ ζ₂) := by
  obtain ⟨Ψ, hΨm, g₁, g₂⟩ := Determination.exists_common_graph hdet hC₁ hC₂
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

/-- **The killed driver code is almost surely a Borel function of the field** in a coupling with a field-determined
killed history, and it decodes to the driver before the lifetime. -/
theorem exists_graph_fieldCode_of_det {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hdet : ∃ Ψ, Measurable Ψ ∧ Determination.IsHistoryGraph P h W VL VR ζ Ψ) :
    ∃ G : DistOn upperHalfPlaneOpens → DCode, Measurable G ∧ ∀ᵐ ω ∂P,
      (ζ ω, killedCode W 0 ζ ω) = G (h ω) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → dec (killedCode W 0 ζ ω) t = W t ω := by
  obtain ⟨Ψ, hΨm, hg⟩ := hdet
  refine ⟨fun f => histCode (Determination.graphHistory (Ψ f)),
    measurable_histCode.comp (Determination.measurable_graphHistory.comp hΨm), ?_⟩
  filter_upwards [hg.killedHistory_ae_eq, hC.1.2.2.2.2] with ω hω hpath
  obtain ⟨hw0, -, -, hcw, -⟩ := hpath
  refine ⟨?_, fun t ht => dec_killedCode hw0 hcw ht⟩
  rw [← histCode_killedHistory W VL VR ζ ω]
  exact congrArg histCode hω

end Det

/-! ### The coupling law on (4.4) words is a kernel -/

/-- **Theorem 1.1's coupling law is a Borel kernel on the (4.4) words**, from the §4.2 reference: a finite kernel `μ`
from word data to (field, killed driver code) such that every ordered (4.4) word has an optional hull coupling with
joint law `μ w` of its field and killed driver code. -/
theorem exists_couplingLawKernel_cond44 (href : Lemma71H.Cond44ReferenceStatement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) (nL nR : ℕ) :
    ∃ μ : Kernel (WordData nL nR) (DistOn upperHalfPlaneOpens × DCode), IsFiniteKernel μ ∧
      ∀ w ∈ cond44Words κ nL nR,
        ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
          (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
          (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
          (h : Ω → DistOn upperHalfPlaneOpens),
          IsOptionalHullCoupling κ w.1.1 w.1.2 w.2.1 w.2.2 P 𝓕 W VL VR B ζ h ∧ P.map (fieldCode h W ζ) = μ w := by
  classical
  obtain ⟨Z, mZ, hZ, C, L, hC, hdesc⟩ :=
    borelDescription_of_borelCanonical borelCanonicalCouplingStatement.{u} κ hκ nL nR
  set Θ₀ : Set (WordData nL nR) := cond44Words κ nL nR with hΘ₀def
  have hΘ₀ : MeasurableSet Θ₀ := measurableSet_cond44Words κ nL nR
  have hne : ∀ w ∈ Θ₀, ∃ z, (w, z) ∈ C := fun w hw => (hdesc w.1.1 w.1.2 w.2.1 w.2.2 hw.1).1
  let m : WordData nL nR → Measure (DistOn upperHalfPlaneOpens × DCode) := fun w =>
    if hw : w ∈ Θ₀ then L (w, (hne w hw).choose) else 0
  have hval : ∀ w ∈ Θ₀, ∀ z, (w, z) ∈ C → L (w, z) = m w := by
    intro w hw z hz
    obtain ⟨Ω₁, m₁, P₁, hP₁, 𝓕₁, W₁, VL₁, VR₁, B₁, ζ₁, h₁, hC₁, hl₁⟩ :=
      (hdesc w.1.1 w.1.2 w.2.1 w.2.2 hw.1).2 z hz
    obtain ⟨Ω₂, m₂, P₂, hP₂, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, h₂, hC₂, hl₂⟩ :=
      (hdesc w.1.1 w.1.2 w.2.1 w.2.2 hw.1).2 _ (hne w hw).choose_spec
    simp only [m, hw, ↓reduceDIte]
    rw [← hl₁, ← hl₂]
    exact map_fieldCode_eq_of_det (Lemma71H.hasFieldDeterminedHistories_of_cond44 href hκ hκ4 hw.1 hw.2) hC₁ hC₂
  obtain ⟨μ, hμ, hμ0⟩ := exists_kernel_of_unique hC hΘ₀ L m hne hval
  have hprob : ∀ w ∈ Θ₀, IsProbabilityMeasure (μ w) := by
    intro w hw
    obtain ⟨Ω₂, m₂, P₂, hP₂, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, h₂, -, hl₂⟩ :=
      (hdesc w.1.1 w.1.2 w.2.1 w.2.2 hw.1).2 _ (hne w hw).choose_spec
    rw [hμ w hw]
    simp only [m, hw, ↓reduceDIte]
    rw [← hl₂]
    infer_instance
  refine ⟨μ, ⟨⟨1, ENNReal.one_lt_top, fun w => ?_⟩⟩, fun w hw => ?_⟩
  · by_cases hw : w ∈ Θ₀
    · have := hprob w hw
      exact prob_le_one
    · rw [hμ0 w hw]
      exact zero_le
  · obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, h, hCp, hl⟩ :=
      (hdesc w.1.1 w.1.2 w.2.1 w.2.2 hw.1).2 _ (hne w hw).choose_spec
    refine ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, h, hCp, ?_⟩
    rw [hl, hμ _ hw]
    simp only [m, hw, ↓reduceDIte]

/-! ### The theorem -/

/-- **Theorem 1.2 jointly measurable in the word, for words satisfying (4.4)**: for `0 < κ < 4` and numbers of marks,
one Borel map `Φ` of the word data and the field returns, for every optional hull coupling (at universe `u`) of every
ordered word satisfying (4.4), almost surely the lifetime and the capacity-parametrized trace frozen after the
lifetime. (`Exist.Staged.Theorem12ParamStatement` restricted to (4.4) words.) -/
def Theorem12ParamCond44Statement : Prop :=
  ∀ (κ : ℝ) (_ : 0 < κ) (_ : κ < 4) (nL nR : ℕ),
    ∃ Φ : WordData nL nR × DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ), Measurable Φ ∧
      ∀ (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
        (_ : IsOrderedForceWord xL xR) (_ : Sec4.Cond44 κ ρL ρR)
        {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
        {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
        {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
        {h : Ω → DistOn upperHalfPlaneOpens}
        (_ : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h),
        ∀ᵐ ω ∂P, (Φ (((xL, xR), (ρL, ρR)), h ω)).1 = ζ ω ∧
          ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
            ∀ t : ℝ≥0, (Φ (((xL, xR), (ρL, ρR)), h ω)).2 t = η (min (t : ℝ≥0∞) (ζ ω)).toNNReal

/-- **`Theorem12ParamCond44Statement` from the §4.2 reference** (no Theorem 1.2/1.3; ruling R48). The determination
map is `Φ(w, f) = drivingTrace(ptOf (condKernel μ (w, f)))` for the kernel `μ` of `exists_couplingLawKernel_cond44`. -/
theorem theorem12ParamCond44Statement_of_reference (href : Lemma71H.Cond44ReferenceStatement.{u}) :
    Theorem12ParamCond44Statement.{u} := by
  intro κ hκ hκ4 nL nR
  obtain ⟨μ, hμf, hμ⟩ := exists_couplingLawKernel_cond44 href hκ hκ4 nL nR
  set K := Kernel.condKernel μ with hKdef
  have hpt := measurable_ptOf_kernel K
  refine ⟨fun p => LP.drivingTrace ((ptOf (K p)).1, dec (ptOf (K p)).2),
    LP.measurable_drivingTrace.comp ((measurable_fst.comp hpt).prodMk (measurable_dec_snd.comp hpt)), ?_⟩
  intro xL xR ρL ρR hF h44 Ω mΩ P _ 𝓕 W VL VR B ζ h hC
  have hw : (((xL, xR), (ρL, ρR)) : WordData nL nR) ∈ cond44Words κ nL nR := ⟨hF, h44⟩
  have hdet : LP.HasFieldDeterminedHistories.{u} κ xL xR ρL ρR :=
    Lemma71H.hasFieldDeterminedHistories_of_cond44 href hκ hκ4 hF h44
  obtain ⟨Ω', mΩ', P', hP', 𝓕', W', VL', VR', B', ζ', h', hC', hlaw'⟩ := hμ _ hw
  have hlaw : P.map (fieldCode h W ζ) = μ (((xL, xR), (ρL, ρR))) :=
    (map_fieldCode_eq_of_det hdet hC hC').trans hlaw'
  obtain ⟨G, hGm, hG⟩ := exists_graph_fieldCode_of_det hC (hdet P 𝓕 W VL VR B ζ h hC)
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

end AdmCode

end Sec7

end InteractingSLE
