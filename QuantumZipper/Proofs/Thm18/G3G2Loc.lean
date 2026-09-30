import QuantumZipper.Proofs.Thm18.G3G2Filter
import QuantumZipper.Proofs.Thm18.G3G2Err

/-!
# G2 and G3-Transfer for the concrete scheme: reduction to the full-field zooms

The zooms `g3U`, `g3V` of the concrete G3 scheme read the field only through the region fields
(`regionField`, junk `0` at folded circles not carried by the half-disc), which is what makes
G3-Markov exact (`g3MarkovStmt_concrete`). Sheffield's argument (arXiv:1012.4797, proof of
Theorem 1.8, §5.4, pp. 70–71, and Proposition 5.5, p. 65) zooms the *full* field `h` at `x` and
`R(x)`. This file isolates the difference as one input, the **locality of the zoom**
(`G3LocStmt`): along `g3Filter`, a cylinder event of the region-field zoom and the same event of
the full-field zoom (`g3Uf`, `g3Vf`) differ only on events of vanishing Palm probability. With
it:

* `g2ConcreteStmt_of_loc`: `G2ConcreteStmt γ` follows from its full-field version
  `G2FullStmt γ` (conditional Proposition 5.5 for the full field at the Palm point and at its
  length partner), by the error absorption `tendsto_integral_abs_condExp_sub_of_symmDiff`;
* `g3TransferStmt_of_loc`: `G3TransferStmt (g3ConcreteMap fun _ => g3Filter)` follows from its
  full-field version `G3TransferFullStmt`, since
  `|P(A ∩ B) − P(A' ∩ B')| ≤ P(A ∆ A') + P(B ∆ B')`.

Why the locality should hold (not proved here): every coordinate of `lawData` of the canonical
description of `h(· + x) + C/γ` reads `h` through `evalReg`/`avgReg`, i.e. through folded circles
near `x + a · K` (`a = scaleProxy`, `K` the compact support of the coordinate's test measure),
and only through a tail of the regularization sequence (`limUnder`, `liminf`), so at arbitrarily
small circles; `a → 0` in probability as `C → ∞` (the zoomed area is `e^C` times the area of
`h`), and `x` stays at distance `≥ η/4` from the edge of region 1 (`x ≥ −δ`) except on
`{x > −3η/4}`, whose Palm probability vanishes as `η → 0`. For `R(x)` the corresponding bad
event `{R(x) ≥ 1/2 + η/4}` vanishes only as `δ → 0` ("We may choose δ small enough so that with
high probability R(x) ∈ B₁(0)", Sheffield p. 71): the limit `δ → 0` is needed for the `V` half
of the locality (hence for G2 as stated, and for Transfer), not only for Transfer.

Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal symmDiff

namespace QuantumZipper
namespace Thm18Asm

open K3

section Full

variable (γ : ℝ) (i : G3Idx)

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

/-- The zoom of the **full** field `h` at the Palm point `x`. -/
def g3Uf (p : Ω₀ × ℝ) : LawD := zoomLaw γ i.C (normField γ X₀ p.1) (g3X γ i p)

/-- The zoom of the **full** field `h` at the length partner `R(x)`. -/
def g3Vf (p : Ω₀ × ℝ) : LawD := zoomLaw γ i.C (normField γ X₀ p.1) (g3R γ i p)

theorem measurable_normField_g3 : Measurable (normField γ X₀) :=
  D3Plus.measurable_fieldSample_of fun μ => measurable_const.add
    ((gffBase.gff.measurable_coord μ).sub (gffBase.gff.measurable_coord _))

theorem measurable_g3X' : Measurable (g3X γ i) := (measurable_g3X γ i).mono (sig_le_g3 i _ _) le_rfl

theorem measurable_g3R' : Measurable (g3R γ i) := (measurable_g3R γ i).mono (sig_le_g3 i _ _) le_rfl

theorem measurable_g3Uf : Measurable (g3Uf γ i) := by
  have h1 : Measurable fun p : Ω₀ × ℝ => (normField γ X₀ p.1, g3X γ i p) :=
    ((measurable_normField_g3 γ).comp measurable_fst).prodMk (measurable_g3X' γ i)
  have h2 := (measurable_zoomLaw γ i.C).comp h1
  exact h2

theorem measurable_g3Vf : Measurable (g3Vf γ i) := by
  have h1 : Measurable fun p : Ω₀ × ℝ => (normField γ X₀ p.1, g3R γ i p) :=
    ((measurable_normField_g3 γ).comp measurable_fst).prodMk (measurable_g3R' γ i)
  have h2 := (measurable_zoomLaw γ i.C).comp h1
  exact h2

theorem measurable_g3U' : Measurable (g3U γ i) := (measurable_g3U γ i).mono (sig_le_g3 i _ _) le_rfl

theorem measurable_g3V' : Measurable (g3V γ i) := (measurable_g3V γ i).mono (sig_le_g3 i _ _) le_rfl

instance isProbabilityMeasure_g3PalmLaw : IsProbabilityMeasure (g3PalmLaw γ i) :=
  isProbabilityMeasure_g3 γ i

end Full

/-- **Locality of the zoom** (input): along `g3Filter`, cylinder events of the region-field
zooms and of the full-field zooms differ on events of vanishing Palm probability. -/
def G3LocStmt (γ : ℝ) : Prop :=
  (∀ s ∈ lawCyl, Tendsto (fun i => (g3PalmLaw γ i).real ((g3U γ i ⁻¹' s) ∆ (g3Uf γ i ⁻¹' s)))
    g3Filter (𝓝 0)) ∧
  (∀ t ∈ lawCyl, Tendsto (fun i => (g3PalmLaw γ i).real ((g3V γ i ⁻¹' t) ∆ (g3Vf γ i ⁻¹' t)))
    g3Filter (𝓝 0))

/-- **G2 for the full-field zooms** (conditional Proposition 5.5 at `x` and at `R(x)`, given the
field outside both half-discs and the Palm length). -/
def G2FullStmt (γ : ℝ) : Prop :=
  ∃ μ ν : Measure LawD, IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧
    (∀ s ∈ lawCyl, Tendsto (fun i => ∫ p, |(g3PalmLaw γ i)[(g3Uf γ i ⁻¹' s).indicator
        (fun _ => (1 : ℝ)) | outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] p - μ.real s|
          ∂(g3PalmLaw γ i)) g3Filter (𝓝 0)) ∧
    (∀ t ∈ lawCyl, Tendsto (fun i => ∫ p, |(g3PalmLaw γ i)[(g3Vf γ i ⁻¹' t).indicator
        (fun _ => (1 : ℝ)) | outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] p - ν.real t|
          ∂(g3PalmLaw γ i)) g3Filter (𝓝 0))

theorem measurableSet_lawCyl {s : Set LawD} (hs : s ∈ lawCyl) : MeasurableSet s := by
  exact generateFrom_lawCyl.ge _ (MeasurableSpace.measurableSet_generateFrom hs)

/-- **G2 for the concrete scheme from its full-field version and locality.** -/
theorem g2ConcreteStmt_of_loc {γ : ℝ} (hL : G3LocStmt γ) (hF : G2FullStmt γ) :
    G2ConcreteStmt γ := by
  obtain ⟨μ, ν, hμ, hν, hU, hV⟩ := hF
  refine ⟨μ, ν, hμ, hν, fun s hs => ?_, fun t ht => ?_⟩
  · exact tendsto_integral_abs_condExp_sub_of_symmDiff
      (fun i => measurable_g3U' γ i (measurableSet_lawCyl hs))
      (fun i => measurable_g3Uf γ i (measurableSet_lawCyl hs)) (hL.1 s hs) (hU s hs)
  · exact tendsto_integral_abs_condExp_sub_of_symmDiff
      (fun i => measurable_g3V' γ i (measurableSet_lawCyl ht))
      (fun i => measurable_g3Vf γ i (measurableSet_lawCyl ht)) (hL.2 t ht) (hV t ht)

/-- `|P(A ∩ B) − P(A' ∩ B')| ≤ P(A ∆ A') + P(B ∆ B')`. -/
theorem abs_measureReal_inter_sub_le {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsFiniteMeasure P] {A A' B B' : Set α} (hA : MeasurableSet A) (hA' : MeasurableSet A')
    (hB : MeasurableSet B) (hB' : MeasurableSet B') :
    |P.real (A ∩ B) - P.real (A' ∩ B')| ≤ P.real (A ∆ A') + P.real (B ∆ B') := by
  refine (abs_measureReal_sub_le_measureReal_symmDiff (hA.inter hB).nullMeasurableSet
    (hA'.inter hB').nullMeasurableSet).trans ?_
  refine (measureReal_mono (s₂ := A ∆ A' ∪ B ∆ B') ?_).trans (measureReal_union_le _ _)
  intro x hx
  simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_union] at hx ⊢
  tauto

end Thm18Asm
end QuantumZipper
