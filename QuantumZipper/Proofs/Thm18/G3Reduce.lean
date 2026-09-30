import Mathlib.MeasureTheory.Constructions.Cylinders
import QuantumZipper.Proofs.Thm18.Assembly
import QuantumZipper.Proofs.Thm18.G3Core

/-!
# G3: independence of the two wedges, reduced to its three inputs

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, proof of Theorem 1.8
(§5.4), last paragraph (pp. 70–71): "we condition on the restriction of the GFF to the complement
of `B₁ := B_ε(x)` and `B₂ := B_ε(R(x))`, and we also condition on the quantum lengths … Proposition
5.5 implies that even with this conditioning … the zoomed-in figures converge in law to a
`γ`-quantum wedge … Now if we condition on the GFF values on `∂B₁(0)` together with the values on
the line `iℝ`, together with the lengths …, then the conditional law of the restrictions of `h` to
the two halves of `B₁(0) ∩ ℍ` are independent by the standard GFF Markov property … We conclude
that in the `ε → 0` limit the `γ`-quantum wedges are independent of each other."

Blueprint `SECTION5_BLUEPRINT.md` node G3 (deps G2, D2, L10, F1, G1). The approximation scheme
(the zoomed surfaces near `x` and `R(x)` of Figure 1.7, on their own probability spaces, and the
conditioning σ-algebras) is a parameter `sch : G3SchemeMap`, as `Thm13Asm.LocMap` is for E5/E6.
The three inputs are stated as explicit node hypotheses:

* `G3MarkovStmt sch` (L10, GFF domain Markov, with D2): the two zooms are conditionally
  independent given the conditioning σ-algebra (and the scheme is well formed);
* `G2TwoPointStmt sch` (G2, Proposition 5.5 generalized, two-point version): given the
  conditioning σ-algebra, each zoom's conditional probabilities of cylinder sets converge in `L¹`
  to deterministic limits (intended witness: both limits are the `γ`-wedge law `𝒲_γ`);
* `G3TransferStmt sch` (E5 + G0 + KT2, both sides, with F1 for the Palm property of `R(x)`): the
  joint probabilities of the zoom pair on cylinder rectangles converge to those of the pair of
  `componentSurface`s of the Theorem 1.8 sample.

`g3_of_scheme` proves `G3Stmt` from them with the abstract core
`indepFun_of_asymptotic_condIndep` (`G3Core.lean`). The a.e.-measurability of the two component
data is not assumed: it follows from G1's conclusion by
`WedgeMeasND.aemeasurable_dataFull_of_isQuantumWedge`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set MeasurableSpace
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

/-! ## Cylinder sets of the law data -/

/-- The codomain of `lawData`: circle coordinates and test-function pairings. -/
abbrev LawD : Type := (ℕ → ℝ) × (TestFun H → ℝ)

/-- Cylinder rectangles of `LawD`: products of measurable cylinders (finitely many circle
coordinates) × (finitely many test pairings). A π-system generating the σ-algebra of `LawD`
(`isPiSystem_lawCyl`, `generateFrom_lawCyl`). -/
def lawCyl : Set (Set LawD) :=
  image2 (· ×ˢ ·) (measurableCylinders fun _ : ℕ => ℝ) (measurableCylinders fun _ : TestFun H => ℝ)

theorem isPiSystem_lawCyl : IsPiSystem lawCyl :=
  isPiSystem_measurableCylinders.prod isPiSystem_measurableCylinders

theorem univ_mem_lawCyl : (univ : Set LawD) ∈ lawCyl :=
  ⟨univ, univ_mem_measurableCylinders _, univ, univ_mem_measurableCylinders _, univ_prod_univ⟩

theorem generateFrom_lawCyl : (inferInstance : MeasurableSpace LawD) = generateFrom lawCyl := by
  have h1 := (generateFrom_measurableCylinders (α := fun _ : ℕ => ℝ)).symm
  have h2 := (generateFrom_measurableCylinders (α := fun _ : TestFun H => ℝ)).symm
  have hc1 : IsCountablySpanning (measurableCylinders fun _ : ℕ => ℝ) :=
    ⟨fun _ => univ, fun _ => univ_mem_measurableCylinders _, iUnion_const _⟩
  have hc2 : IsCountablySpanning (measurableCylinders fun _ : TestFun H => ℝ) :=
    ⟨fun _ => univ, fun _ => univ_mem_measurableCylinders _, iUnion_const _⟩
  unfold lawCyl
  rw [← generateFrom_prod_eq hc1 hc2, ← h1, ← h2]

/-! ## The approximation scheme and the node hypotheses -/

/-- An approximation scheme for G3: a directed family (filter `l` on `ι`; in the paper
`ε → 0`, `C → ∞`, `δ → 0`) of probability spaces `(Ω' i, P' i)` with a conditioning σ-algebra
`𝒢 i` and the two zoomed surfaces' law data `U i` (near `x`, left side) and `V i` (near `R(x)`,
right side). -/
structure G3Scheme where
  ι : Type
  l : Filter ι
  Ω' : ι → Type
  𝒢 : ∀ i, MeasurableSpace (Ω' i)
  m : ∀ i, MeasurableSpace (Ω' i)
  P' : ∀ i, Measure[m i] (Ω' i)
  U : ∀ i, Ω' i → LawD
  V : ∀ i, Ω' i → LawD

/-- A choice of approximation scheme for every Theorem 1.8 sample (the Figure 1.7 construction
zoomed near `x` and `R(x)`). -/
abbrev G3SchemeMap : Type 1 :=
  ∀ (_ : ℝ) (Ω : Type) [MeasurableSpace Ω] (_ : Measure Ω) (_ : ℝ≥0 → Ω → ℝ)
    (_ : Ω → FieldSample), G3Scheme

/-! ## The reduction -/

/-- The component data are a.e.-measurable once G1 holds (WEDGE-MEAS). -/
theorem aemeasurable_lawData_component {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample} (hγ : 0 < γ) (hγ2 : γ < 2) (left : Bool)
    (hW : IsQuantumWedge γ γ (componentSurface γ B Y left) P) :
    AEMeasurable (lawData (componentSurface γ B Y left)) P :=
  WedgeMeasND.aemeasurable_dataFull_of_isQuantumWedge
    (WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hW.1)
    (WedgeInf.wedgeInfiniteTotal hγ hγ2 hW.1) hγ hγ2 hW

end Thm18Asm
end QuantumZipper
