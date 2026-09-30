import QuantumZipper.Proofs.Zipper.E1TransferMain

/-!
# TR-MEAS, deterministic part: constant invariance of `trInt` (M3) and the field from coordinates

`handoff/E1-TR.md` (TR-MEAS, M3). Notation of `E1Transfer`/`E1TransferMain`.

* `evalReg_addConst_of_regShift`: if at `ν` (a probability measure) the raw circle averages of `y`
  converge `ν`-a.e. at every level, `avgReg y k` is `ν`-integrable and `∫ avgReg y k dν` converges,
  then `evalReg (y + c) ν = evalReg y ν + c` for **every** constant `c` (`RegShift y ν`).
* `trInt_addConst`: if `RegShift y` holds at `ϖ_t` and at every pushed dyadic folded circle
  `fc_i.map (revMap v t)`, then `trInt … v d (y + c) = trInt … v d y`.
* `fromC`, `coordsFull_fromC`: a field sample rebuilt from its coordinates.
* `trInt_eq_fromC_nrm`: under the same hypotheses, `trInt … v d y` is `trInt` at the field rebuilt
  from `coordsFull (nrm y)`.

Own bookkeeping (cost rule of `AGENT_GUIDE.md`): `evalReg`/`avgReg` are `limUnder`s, which commute
with adding a constant only where the limits exist. Source of the statement being formalized:
Sheffield, arXiv:1012.4797, Lemma 5.6 and its proof (pp. 66–68), §5.2 (pp. 57–59).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E1

open B2 CharFun UnzipInvariance UnzipFull CoordsFull

/-- Hypotheses under which `evalReg · ν` commutes with adding constants to `y`. -/
def RegShift (y : FieldSample) (ν : Measure ℂ) : Prop :=
  (∀ᵐ z ∂ν, ∀ k : ℕ, ∃ l, Tendsto (fun n => y (foldedCircle (dyadicRoundC n z) (radius k)))
      atTop (𝓝 l)) ∧
    (∀ k : ℕ, Integrable (fun z => avgReg y k z) ν) ∧
    ∃ L, Tendsto (fun k => ∫ z, avgReg y k z ∂ν) atTop (𝓝 L)

theorem evalReg_addConst_of_regShift {y : FieldSample} {ν : Measure ℂ} [IsProbabilityMeasure ν]
    (h : RegShift y ν) (c : ℝ) : evalReg (addConst y c) ν = evalReg y ν + c := by
  obtain ⟨hraw, hint, L, hL⟩ := h
  have hk : ∀ k : ℕ, ∫ z, avgReg (addConst y c) k z ∂ν = ∫ z, avgReg y k z ∂ν + c := by
    intro k
    rw [integral_congr_ae (hraw.mono fun z hz => LocalRule.avgReg_addConst_of_tendsto (hz k) c),
      integral_add (hint k) (integrable_const c)]
    simp
  have h2 : Tendsto (fun k => ∫ z, avgReg (addConst y c) k z ∂ν) atTop (𝓝 (L + c)) := by
    simpa only [hk] using hL.add_const c
  unfold evalReg
  rw [h2.limUnder_eq, hL.limUnder_eq]

variable {κ t : ℝ} {ϖ : Measure ℂ}

/-- The pushed dyadic folded circles at which `coordChange y (revMap v t) Q` is read. -/
abbrev pfc (v : ℝ → ℝ) (t : ℝ) (i : ℕ) : Measure ℂ :=
  (foldedCircle (fullIndex i).1 (fullIndex i).2).map (revMap v t)

/-- **M3: constant invariance of `trInt`.** -/
theorem trInt_addConst {v : ℝ → ℝ} [IsProbabilityMeasure ϖ]
    (δ : ℝ) (Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞) (Φ : (ℕ → ℝ) → ℝ≥0∞)
    (d : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) {y : FieldSample}
    (hϖ : RegShift y (varpiT v t ϖ)) (hfc : ∀ i, RegShift y (pfc v t i)) (c : ℝ) :
    trInt κ t δ ϖ Ψ Φ v d (addConst y c) = trInt κ t δ ϖ Ψ Φ v d y := by
  have : IsProbabilityMeasure (varpiT v t ϖ) := by unfold varpiT; infer_instance
  have : ∀ i, IsProbabilityMeasure (pfc v t i) := fun i => by unfold pfc; infer_instance
  set m := evalReg y (varpiT v t ϖ) + qt κ v t ϖ with hmdef
  have hm' : evalReg (addConst y c) (varpiT v t ϖ) + qt κ v t ϖ = m + c := by
    rw [evalReg_addConst_of_regShift hϖ c]; ring
  have h1 : coordsFull (addConst (addConst y c) (-(m + c))) = coordsFull (addConst y (-m)) := by
    funext i; simp only [coordsFull_addConst]; ring
  have h2 : coordsFull (addConst (coordChange (addConst y c) (revMap v t) (Qc (Real.sqrt κ)))
      (-(m + c))) = coordsFull (addConst (coordChange y (revMap v t) (Qc (Real.sqrt κ))) (-m)) := by
    funext i
    simp only [coordsFull_addConst]
    simp only [coordsFull, coordChange]
    rw [evalReg_addConst_of_regShift (hfc i) c]
    ring
  unfold trInt
  rw [hm', h1, qBoundaryMeasureOn, qBoundaryMeasureOn,
    Factorization.bdryApprox_congr (avgReg_congr_full h2)]

open Classical in
/-- A field sample rebuilt from coordinates `c` (value `c i` at the `i`-th dyadic folded circle,
with the least such index; `0` at all other measures). -/
def fromC (c : ℕ → ℝ) : FieldSample := fun μ =>
  if h : ∃ i, foldedCircle (fullIndex i).1 (fullIndex i).2 = μ then c (Nat.find h) else 0

theorem coordsFull_fromC (y : FieldSample) : coordsFull (fromC (coordsFull y)) = coordsFull y := by
  classical
  funext i
  have h : ∃ j, foldedCircle (fullIndex j).1 (fullIndex j).2 =
      foldedCircle (fullIndex i).1 (fullIndex i).2 := ⟨i, rfl⟩
  simp only [coordsFull, fromC, h, ↓reduceDIte]
  exact congrArg y (Nat.find_spec h)

/-- **M3, representation form.** -/
theorem trInt_eq_fromC_nrm {v : ℝ → ℝ} [IsProbabilityMeasure ϖ] (δ : ℝ) (Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞)
    (Φ : (ℕ → ℝ) → ℝ≥0∞) (d : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) {y : FieldSample}
    (hϖ : RegShift y (varpiT v t ϖ)) (hfc : ∀ i, RegShift y (pfc v t i)) :
    trInt κ t δ ϖ Ψ Φ v d y = trInt κ t δ ϖ Ψ Φ v d (fromC (coordsFull (B1Full.nrm y))) := by
  rw [trInt_congr_coordsFull δ Ψ Φ v d (coordsFull_fromC _), B1Full.nrm,
    trInt_addConst δ Ψ Φ d hϖ hfc]

end E1
end QuantumZipper
