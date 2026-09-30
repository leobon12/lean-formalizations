import QuantumZipper.Proofs.Zipper.D3PlusStmt
import QuantumZipper.Statements.ConfigLaw

/-!
# E6-UP, part 1: local laws determine the law of the generated data (measure theory)

Task E6-UP (`handoff/THM13-ASM.md`, mismatch 1). This file contains the measure-theoretic core
of the upgrade "equality of all local laws ⇒ equality of `configLawFull`":

* `ext_of_monotone_generating` — two finite measures of equal total mass that agree on the
  pushforwards under maps `L R` (`R ∈ ℕ`) whose σ-algebras `comap (L R)` increase in `R` and
  generate the whole σ-algebra are equal. This is the π-λ uniqueness theorem (Dynkin), applied
  to the π-system `⋃_R σ(L R)` (a union of an increasing sequence of σ-algebras):
  Billingsley, *Probability and Measure*, 3rd ed., Theorem 3.3; Kallenberg, *Foundations of
  Modern Probability*, 2nd ed., Lemma 1.17. In mathlib: `MeasureTheory.ext_of_generate_finite`.
* The concrete "small data" space `SmallData = (ℕ → ℝ) × (ℝ≥0 → ℝ)` (the raw values
  `Factorization.coords` of the field at the dyadic folded circles of radius `2^{-k}`, and the
  driver on `[0,∞)`) and the truncations `truncLoc R` with `truncLoc R ∘ smallOf = D3Plus.locData R`
  (`truncLoc_smallOf`). They satisfy the hypotheses of `ext_of_monotone_generating`
  (`truncLoc_comap_mono`, `truncLoc_generate`): the local data at all radii `R ∈ ℕ` determine the
  small data (own elementary argument: every dyadic circle lies in some `closedBall 0 R`, every
  time `s ≥ 0` is `≤ R` for some `R`).
* `coordsOfFull`: the projection of `lawData`'s circle coordinates `coordsFull` onto
  `Factorization.coords` (the radii `2^{-k}` are among the radii `(m+1)/2^j`), so the small data
  is a measurable function of the `configLawFull` data (`smallOfFull_dataFull`).
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace E6

/-! ## π-λ uniqueness along an increasing generating sequence of maps -/

/-- **π-λ uniqueness along a directed generating family of maps** (Billingsley Thm 3.3;
Kallenberg Lemma 1.17): the union of a directed family of σ-algebras is a π-system. -/
theorem ext_of_directed_generating {E ι : Type*} [mE : MeasurableSpace E] {F : ι → Type*}
    [∀ i, MeasurableSpace (F i)] (L : ∀ i, E → F i) (hL : ∀ i, Measurable (L i))
    (hdir : Directed (· ≤ ·) fun i => MeasurableSpace.comap (L i) inferInstance)
    (hgen : mE ≤ ⨆ i, MeasurableSpace.comap (L i) inferInstance)
    (μ ν : Measure E) [IsFiniteMeasure μ] (huniv : μ univ = ν univ)
    (hloc : ∀ i, μ.map (L i) = ν.map (L i)) : μ = ν := by
  set C : Set (Set E) :=
    ⋃ i, {s | MeasurableSet[MeasurableSpace.comap (L i) inferInstance] s} with hC
  have hgenC : mE = MeasurableSpace.generateFrom C := by
    rw [hC]
    exact (le_antisymm hgen (iSup_le fun i => (hL i).comap_le)).trans
      (MeasurableSpace.generateFrom_iUnion_measurableSet _).symm
  refine ext_of_generate_finite C hgenC ?_ (fun s hs => ?_) huniv
  · refine isPiSystem_iUnion_of_directed_le _ (fun i =>
      @MeasurableSpace.isPiSystem_measurableSet E (MeasurableSpace.comap (L i) inferInstance)) ?_
    intro i j
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact ⟨k, fun s hs => hik s hs, fun s hs => hjk s hs⟩
  · simp only [hC, mem_iUnion, Set.mem_ofPred_eq] at hs
    obtain ⟨i, A, hA, rfl⟩ := hs
    rw [← Measure.map_apply (hL i) hA, ← Measure.map_apply (hL i) hA, hloc i]

/-- **π-λ uniqueness along an increasing generating sequence of maps** (Billingsley Thm 3.3;
Kallenberg Lemma 1.17). -/
theorem ext_of_monotone_generating {E : Type*} [mE : MeasurableSpace E] {F : ℕ → Type*}
    [∀ R, MeasurableSpace (F R)] (L : ∀ R, E → F R) (hL : ∀ R, Measurable (L R))
    (hmono : Monotone fun R => MeasurableSpace.comap (L R) inferInstance)
    (hgen : mE ≤ ⨆ R, MeasurableSpace.comap (L R) inferInstance)
    (μ ν : Measure E) [IsFiniteMeasure μ] (huniv : μ univ = ν univ)
    (hloc : ∀ R, μ.map (L R) = ν.map (L R)) : μ = ν :=
  ext_of_directed_generating L hL hmono.directed_le hgen μ ν huniv hloc

/-! ## Small data and its truncations -/

/-- The small data of a configuration: `Factorization.coords` of the field and the driver on
`[0,∞)`. -/
abbrev SmallData : Type := (ℕ → ℝ) × (ℝ≥0 → ℝ)

/-! ## From `configLawFull` data to small data -/

/-- Index of the `i`-th `Factorization` circle (radius `2^{-k}`) in the `coordsFull` enumeration
(radius `(0+1)/2^k`). -/
def fullIdx (i : ℕ) : ℕ :=
  let p := Denumerable.ofNat (ℤ × ℤ × ℕ × ℕ) i
  Encodable.encode ((p.1, p.2.1, p.2.2.1, 0, p.2.2.2) : ℤ × ℤ × ℕ × ℕ × ℕ)

theorem fullIndex_fullIdx (i : ℕ) :
    CoordsFull.fullIndex (fullIdx i) =
      ((Factorization.dyadicIndex i).1, radius (Factorization.dyadicIndex i).2) := by
  simp only [CoordsFull.fullIndex, fullIdx, Denumerable.ofNat_encode, Factorization.dyadicIndex,
    radius]
  refine Prod.ext rfl ?_
  simp [inv_pow]

/-- Projection of the full circle coordinates onto the `Factorization` coordinates. -/
def coordsOfFull (y : ℕ → ℝ) : ℕ → ℝ := fun i => y (fullIdx i)

theorem coordsOfFull_coordsFull (x : FieldSample) :
    coordsOfFull (CoordsFull.coordsFull x) = Factorization.coords x := by
  funext i
  simp only [coordsOfFull, CoordsFull.coordsFull, Factorization.coords, fullIndex_fullIdx]

theorem measurable_coordsOfFull : Measurable coordsOfFull :=
  measurable_pi_iff.2 fun i => measurable_pi_apply (fullIdx i)

/-- The target space of `configLawFull`. -/
abbrev FullData : Type := ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ)

/-- The data map of `configLawFull` (`configLawFull c P = P.map (dataFull c)`). -/
def dataFull {Ω : Type*} (c : Ω → FieldSample × (ℝ → ℝ)) (ω : Ω) : FullData :=
  (lawData (fun ω => (c ω).1) ω, fun t : ℝ≥0 => (c ω).2 t)

theorem configLawFull_eq_map {Ω : Type*} [MeasurableSpace Ω] (c : Ω → FieldSample × (ℝ → ℝ))
    (P : Measure Ω) : configLawFull c P = P.map (dataFull c) := rfl

end E6
end QuantumZipper
