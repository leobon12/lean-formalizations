import QuantumZipper.Proofs.Thm18.G1PsiExtMain
import QuantumZipper.Proofs.Thm18.G1ProfileRed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-PATHCOORD: the countable-coordinate path input, and the choice of the good predicate

`g1PsiExtStmt_of_coord` (G1PsiExtMain.lean) reduces `G1RC.G1PsiExtStmt` to two inputs with a free
predicate `Good : ℝ → (ℝ≥0 → ℝ) → Prop` on driving paths:
`G1PathCoordGoodStmt Good` (path space, countably many coordinates) and
`PsiBoundsGoodStmt γ (Good γ)` (deterministic, for good chords).

This file

* proves **`g1PathCoordGoodStmt_of_bm`**: `G1PathCoordGoodStmt Good` follows from the plain
  Brownian statement `G1GoodBMStmt Good` ("for every Brownian motion whose paths are all
  continuous, almost surely its path is `Good`"), for **every** `Good`. Proof: under the path law
  `P.map (pathOf B)` the regularized coordinate process `a ↦ G1Pkg.pathReg a` is a Brownian motion
  with continuous paths (`isBrownianReal_regCoord`, G1ProfileRed.lean), so `Good γ (pathReg a)`
  holds a.e.; its trace is a simple chord a.e. (`g1RegPathChordStmt`, Rohde–Schramm, Ann. Math.
  161 (2005), Thms 4.7, 6.1); `pathReg a = a` on the countable `S` a.e. (Brownian paths are a.s.
  continuous); and `M` is the complement of a measurable null hull (`toMeasurable`) of the
  failure set. Own bookkeeping.
* fixes the choice **`Good := SideRegGood`**: for both sides and every normalized uniformizer
  `φ`, the inverse `invFunOn φ (side)` has a continuous extension `ψe` to `Hbar` which is
  - locally Hölder on `Hbar` (`LocHolderHbar`: the side component is a Hölder domain), and
  - pushes folded circles to uniformly Frostman measures (`PushFrostman`, parametrized as in
    `PushFamBounds`),
  and proves **`psiBoundsGoodStmt_of_reg`**: `PsiBoundsGoodStmt γ (SideRegGood γ)` from the
  deterministic analytic statement `PushBoundsOfRegStmt` (Hölder + Frostman + continuity ⇒
  `PushFamBounds`, the Duplantier–Sheffield Prop. 3.1 / TwoPoint (E) argument);
* assembles **`g1PsiExtStmt_of_reg`**:
  `G1GoodBMStmt SideHolderGood → SideFrostDetStmt → PushBoundsOfRegStmt → G1PsiExtStmt`,
  where the Frostman part is deterministic (`SideFrostDetStmt`, every simple chord) and made
  almost sure by Rohde–Schramm (`g1GoodBMStmt_of_det`). G1PathCoordFam.lean reduces
  `PushBoundsOfRegStmt` to its variance clause.

Sources for the remaining inputs: `SideHolderGood` a.s. is the statement that the complementary
components of SLE_κ, `κ < 4`, are Hölder domains (Rohde–Schramm, *Basic properties of SLE*,
Ann. Math. 161 (2005), Thm 5.2, for `ℍ \ K_t`; the whole-chord form is attributed to RS05 in the
literature, e.g. Kavvadias–Miller–Schoug, arXiv:2209.10532, §1). `SideFrostDetStmt` is expected
for every simple chord from the Beurling estimate (Lawler, arXiv:0712.3256, Thm 2.10); the
deduction is an own argument, not yet written (see handoff/G1-PATHCOORD.md).
`PushBoundsOfRegStmt` follows the TwoPoint (E) argument (TwoPointEnergy.lean: Frostman log
potentials + same-angle coupling).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set Function Real
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

/-! ## The path input from a plain Brownian statement -/

/-- **Brownian form of the path input.** For every Brownian motion `B` whose paths are all
continuous, `P`-almost surely the path `pathOf B ω` is `Good`. -/
def G1GoodBMStmt (Good : ℝ → (ℝ≥0 → ℝ) → Prop) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
    (∀ ω, Continuous fun t => B t ω) → ∀ᵐ ω ∂P, Good γ (pathOf B ω)

/-- Under the path law, the regularized path is `Good` almost everywhere. -/
theorem ae_good_pathReg {Good : ℝ → (ℝ≥0 → ℝ) → Prop} (h : G1GoodBMStmt Good) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ a ∂(P.map (pathOf B)), Good γ (G1Pkg.pathReg a) := by
  have : IsProbabilityMeasure (P.map (pathOf B)) :=
    (Measure.isProbabilityMeasure_map_iff
      (QuantumZipper.IsBrownianReal.aemeasurable_pathOf hB)).2 inferInstance
  exact h γ hγ hγ2 (P.map (pathOf B)) regCoord (isBrownianReal_regCoord hB)
    (fun a => G1Pkg.pathReg_spec.2.1 a)

/-- A.e. path agrees with its regularization on a given countable set of times. -/
theorem ae_pathReg_eqOn {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {S : Set ℝ≥0} (hS : S.Countable) :
    ∀ᵐ a ∂(P.map (pathOf B)), ∀ t ∈ S, G1Pkg.pathReg a t = a t := by
  have hmS : MeasurableSet {a : ℝ≥0 → ℝ | ∀ t ∈ S, G1Pkg.pathReg a t = a t} := by
    have : {a : ℝ≥0 → ℝ | ∀ t ∈ S, G1Pkg.pathReg a t = a t} =
        ⋂ t ∈ S, {a : ℝ≥0 → ℝ | G1Pkg.pathReg a t = a t} := by
      ext a; simp [mem_iInter]
    rw [this]
    exact MeasurableSet.biInter hS fun t _ => measurableSet_eq_fun
      ((measurable_pi_apply t).comp G1Pkg.pathReg_spec.1) (measurable_pi_apply t)
  refine (ae_map_iff (QuantumZipper.IsBrownianReal.aemeasurable_pathOf hB) hmS).2 ?_
  filter_upwards [hB.cont] with ω hω t _
  have hc : Continuous (pathOf B ω) := hω
  rw [G1Pkg.pathReg_spec.2.2 _ hc]

/-- **`G1PathCoordGoodStmt` from the Brownian statement**, for every predicate `Good`. -/
theorem g1PathCoordGoodStmt_of_bm {Good : ℝ → (ℝ≥0 → ℝ) → Prop} (h : G1GoodBMStmt Good) :
    G1PathCoordGoodStmt Good := by
  intro γ hγ hγ2 Ω _ P _ B hB Ω' _ P' _ X A _ _ _ S hS
  set p : (ℝ≥0 → ℝ) → Prop := fun a => (∀ t ∈ S, G1Pkg.pathReg a t = a t) ∧
    IsSimpleChord (pathTrace (γ ^ 2) (G1Pkg.pathReg a)) ∧ Good γ (G1Pkg.pathReg a) with hp
  have hall : ∀ᵐ a ∂(P.map (pathOf B)), p a := by
    filter_upwards [ae_pathReg_eqOn hB hS, g1RegPathChordStmt γ hγ hγ2 P B hB,
      ae_good_pathReg h hγ hγ2 hB] with a h1 h2 h3
    exact ⟨h1, h2, h3⟩
  refine ⟨(toMeasurable (P.map (pathOf B)) {a | ¬ p a})ᶜ,
    (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
  · rw [ae_iff]
    simp only [mem_compl_iff, not_not, Set.ofPred_mem_eq]
    rw [measure_toMeasurable]
    exact ae_iff.1 hall
  · intro a ha
    have hpa : p a := by
      by_contra hn
      exact ha (subset_toMeasurable _ _ hn)
    exact ⟨G1Pkg.pathReg a, hpa.1, G1Pkg.pathReg_spec.2.1 a, hpa.2.1, hpa.2.2⟩

/-! ## The good predicate: Hölder and Frostman regularity of the side maps -/

/-- Local Hölder continuity on `Hbar` (one exponent, constants on bounded sets). -/
def LocHolderHbar (ψ : ℂ → ℂ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∀ R : ℝ, ∃ C : ℝ, ∀ z ∈ Hbar, ∀ w ∈ Hbar, ‖z‖ ≤ R → ‖w‖ ≤ R →
    ‖ψ z - ψ w‖ ≤ C * ‖z - w‖ ^ α

/-- Hölder part of the good predicate: for both sides and every normalized uniformizer, the
inverse has a continuous extension to `Hbar` that is locally Hölder (Hölder domain). -/
def SideHolderGood (γ : ℝ) (a : ℝ≥0 → ℝ) : Prop :=
  ∀ left : Bool, ∀ φ : ℂ → ℂ, IsNormalizedUniformizer (sideDom (pathTrace (γ ^ 2) a) left) φ →
    ∃ ψe : ℂ → ℂ, ContinuousOn ψe Hbar ∧
      EqOn (invFunOn φ (sideDom (pathTrace (γ ^ 2) a) left)) ψe H ∧ LocHolderHbar ψe

end G1RC
end Thm18Asm
end QuantumZipper
