import QuantumZipper.Proofs.Thm18.G1ZB2CMain
import QuantumZipper.Proofs.Thm18.G1ZMeasNode
import QuantumZipper.Proofs.Thm18.G3ConcreteMaps

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-B2R (1): measurability tools for the Palm rerooting with a constant

Theorem 1.8, G1 zoom, node B2-R (`G1PalmConstStmt`). Sheffield, arXiv:1012.4797, proof of
Proposition 1.7 (pp. 25–26).

The functional `y ↦ Γ(loc(canonical(y + C)))` of a canonical field reads the field only through
its dyadic circle coordinates `coordsFull` (a countable family), so all a.e.-measurability and
law-equality statements are made for the coordinates.

* `g1zB2r_coordsFull_of_loc` (and its `Measurable` form): the coordinates `coordsFull` of a
  family of fields are (a.e.-)measurable as soon as all the local data `locFieldFull R` are.
* `g1zB2r_map_eq`: two a.e.-measurable coordinate families on a probability space with the same
  local truncated integrals have the same law (π-λ, `E6.ext_of_monotone_generating`).
* `g1zB2rPhi γ C`: the measurable map `coordsFull(y) ↦ data(canonProxy(y + C))`
  (`canonOfCoords`, `measurable_lawOf_canon`, G3ConcreteMaps.lean).
* `g1zB2r_ae_aemeasurable_snd`: a.e.-measurability of the sections of an a.e.-measurable function
  on a product.

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open D3Plus Factorization CoordsFull

open Classical in
/-- The truncation of a coordinate sequence to the circles inside `closedBall 0 R`. -/
def g1zTrunc (R : ℕ) (c : ℕ → ℝ) : ℕ → ℝ := fun i => if inBallFull R i then c i else 0

theorem measurable_g1zTrunc (R : ℕ) : Measurable (g1zTrunc R) := by
  classical
  refine measurable_pi_iff.2 fun i => ?_
  by_cases h : inBallFull R i
  · simp only [g1zTrunc, h, ite_true]; exact measurable_pi_apply i
  · simp only [g1zTrunc, h, ite_false]; exact measurable_const

theorem locFieldFull_fst (R : ℕ) (y : FieldSample) :
    (locFieldFull R y).1 = g1zTrunc R (coordsFull y) := rfl

theorem exists_inBallFull (i : ℕ) : ∃ R : ℕ, inBallFull R i := by
  obtain ⟨R, hR⟩ := exists_nat_ge (‖(fullIndex i).1‖ + (fullIndex i).2)
  exact ⟨R, hR⟩

theorem inBallFull_mono {R R' : ℕ} (h : R ≤ R') {i : ℕ} (hi : inBallFull R i) :
    inBallFull R' i :=
  hi.trans (by exact_mod_cast h)

/-- The coordinates of a family of fields with a.e.-measurable local data are a.e.-measurable. -/
theorem g1zB2r_coordsFull_of_loc {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → FieldSample} (h : ∀ R : ℕ, AEMeasurable (fun a => locFieldFull R (f a)) μ) :
    AEMeasurable (fun a => coordsFull (f a)) μ := by
  classical
  refine aemeasurable_pi_iff.2 fun i => ?_
  obtain ⟨R, hi⟩ := exists_inBallFull i
  have e : (fun a => coordsFull (f a) i) = fun a => (locFieldFull R (f a)).1 i := by
    funext a
    simp only [locFieldFull, hi, ite_true]
  rw [e]
  exact (measurable_pi_apply i).comp_aemeasurable (h R).fst

/-- The `Measurable` form of `g1zB2r_coordsFull_of_loc`. -/
theorem g1zB2r_measurable_coordsFull_of_loc {α : Type*} [MeasurableSpace α]
    {f : α → FieldSample} (h : ∀ R : ℕ, Measurable fun a => locFieldFull R (f a)) :
    Measurable fun a => coordsFull (f a) := by
  classical
  refine measurable_pi_iff.2 fun i => ?_
  obtain ⟨R, hi⟩ := exists_inBallFull i
  have e : (fun a => coordsFull (f a) i) = fun a => (locFieldFull R (f a)).1 i := by
    funext a
    simp only [locFieldFull, hi, ite_true]
  rw [e]
  exact (measurable_pi_apply i).comp (h R).fst

/-- **Law of coordinates from local truncated integrals** (π-λ). -/
theorem g1zB2r_map_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ ξ' : Ω → ℕ → ℝ} (hξ : AEMeasurable ξ P) (hξ' : AEMeasurable ξ' P)
    (hloc : ∀ R : ℕ, ∀ Γ : (ℕ → ℝ) → ℝ≥0∞, Measurable Γ → (∀ c, Γ c ≤ 1) →
      ∫⁻ ω, Γ (g1zTrunc R (ξ ω)) ∂P = ∫⁻ ω, Γ (g1zTrunc R (ξ' ω)) ∂P) :
    P.map ξ = P.map ξ' := by
  classical
  have : IsProbabilityMeasure (P.map ξ) := (Measure.isProbabilityMeasure_map_iff hξ).2 inferInstance
  have : IsProbabilityMeasure (P.map ξ') := (Measure.isProbabilityMeasure_map_iff hξ').2 inferInstance
  refine E6.ext_of_monotone_generating (fun R => g1zTrunc R) measurable_g1zTrunc ?_ ?_
    _ _ (by simp) fun R => ?_
  · intro R R' hRR'
    have e : g1zTrunc R = g1zTrunc R ∘ g1zTrunc R' := by
      funext c i
      by_cases hi : inBallFull R i
      · simp [g1zTrunc, hi, inBallFull_mono hRR' hi]
      · simp [g1zTrunc, hi]
    show MeasurableSpace.comap (g1zTrunc R) _ ≤ MeasurableSpace.comap (g1zTrunc R') _
    rw [e, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_g1zTrunc R).comap_le
  · show MeasurableSpace.pi ≤ _
    refine iSup_le fun i => ?_
    obtain ⟨R, hi⟩ := exists_inBallFull i
    have e : (fun c : ℕ → ℝ => c i) = (fun c : ℕ → ℝ => c i) ∘ g1zTrunc R := by
      funext c; simp [g1zTrunc, hi]
    calc MeasurableSpace.comap (fun c : ℕ → ℝ => c i) inferInstance
        = MeasurableSpace.comap (g1zTrunc R)
            (MeasurableSpace.comap (fun c : ℕ → ℝ => c i) inferInstance) := by
          rw [MeasurableSpace.comap_comp, ← e]
      _ ≤ MeasurableSpace.comap (g1zTrunc R) inferInstance :=
          MeasurableSpace.comap_mono (measurable_pi_apply i).comap_le
      _ ≤ ⨆ R, MeasurableSpace.comap (g1zTrunc R) inferInstance :=
          le_iSup (fun R => MeasurableSpace.comap (g1zTrunc R) inferInstance) R
  · ext A hA
    have key : ∀ (ζ : Ω → ℕ → ℝ), AEMeasurable ζ P →
        ((P.map ζ).map (g1zTrunc R)) A = ∫⁻ ω, A.indicator 1 (g1zTrunc R (ζ ω)) ∂P := by
      intro ζ hζ
      rw [AEMeasurable.map_map_of_aemeasurable (measurable_g1zTrunc R).aemeasurable hζ,
        ← lintegral_indicator_one hA,
        lintegral_map' (measurable_one.indicator hA).aemeasurable
          ((measurable_g1zTrunc R).comp_aemeasurable hζ)]
      rfl
    rw [key ξ hξ, key ξ' hξ']
    refine hloc R (A.indicator 1) (measurable_one.indicator hA) fun c => ?_
    by_cases hc : c ∈ A <;> simp [hc]

/-- The measurable map `coordsFull(y) ↦ data(canonProxy(y + C))`, through the dyadic coordinates
(`piC (coordsFull y) = coords y`). -/
def g1zB2rPhi (γ C : ℝ) (c : ℕ → ℝ) : (ℕ → ℝ) × (TestFun H → ℝ) :=
  lawOf (canonOfCoords γ (fun j => WedgeCan4.piC c j + C))

theorem measurable_g1zB2rPhi (γ C : ℝ) : Measurable (g1zB2rPhi γ C) :=
  (measurable_lawOf_canon γ).comp
    (measurable_pi_iff.2 fun j =>
      ((measurable_pi_apply j).comp WedgeCan4.measurable_piC).add_const C)

/-- `g1zB2rPhi` at the coordinates of a field: the canonical proxy of the shifted field. -/
theorem g1zB2rPhi_coordsFull (γ C : ℝ) (y : FieldSample) :
    g1zB2rPhi γ C (coordsFull y) = lawOf (canonProxy γ (addConst y C)) := by
  unfold g1zB2rPhi
  rw [canonProxy_recon]
  have : (fun j => WedgeCan4.piC (coordsFull y) j + C) = coords (addConst y C) := by
    rw [F1.coords_addConst]
    funext j
    simp only [WedgeCan4.piC_coordsFull]
  rw [this]
  rfl

/-- Sections of an a.e.-measurable function on a product are a.e.-measurable. -/
theorem g1zB2r_ae_aemeasurable_snd {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {f : α × β → γ} (hf : AEMeasurable f (μ.prod ν)) :
    ∀ᵐ y ∂ν, AEMeasurable (fun x => f (x, y)) μ := by
  have hs := hf.prod_swap
  have hae := hs.ae_eq_mk
  have hae' := Measure.ae_ae_of_ae_prod hae
  filter_upwards [hae'] with y hy
  refine (hs.measurable_mk.comp (measurable_prodMk_left (x := y))).aemeasurable.congr ?_
  filter_upwards [hy] with x hx
  simpa using hx.symm

end Thm18Asm
end QuantumZipper
