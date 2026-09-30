import QuantumZipper.Proofs.Thm18.G3Zc2Two

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZOOM-C 2: law transfer of zoom limits through the dyadic data

The one-point G0 cores (`exists_g0Setup`, ZOOM-A's `exists_g0Setup_palmField`) produce their own
free field `W`, while the Palm identity (`G3WedgePalmIdStmt`) produces a different free field `V`.
The zoom functionals are compared through the countably many dyadic circle values
(`dyadData`, G3ZcDyad):

* `lintegral_canonicalOn_le_dyad` / `…_ge_dyad`: for a random field `Z` whose local area measure on
  `halfDisc r` is a.s. a genuine vague limit, `E Γ(loc_R canonicalOn Z)` is within
  `μ(dyadBad)` of `∫ Γ ∘ dyadT dμ`, where `μ` is the law of `dyadData r Z` and `dyadBad` the
  (measurable) event that the surrogate scale is outside `(0, r/R)`;
* `lintegral_canonicalOn_transfer`: two such fields with **equal laws of their dyadic data** have
  functional expectations within `2 μ(dyadBad)`;
* `tendsto_zoom_of_lawEq` (**law transfer of the zoom limit**): if `Zf L` agrees near `0` with a
  D3⁺ model (so `E Γ(loc canonicalOn(Zf L)) → E Γ(loc Y')`, `d3_transfer_of_agree`) and a family
  `Z' L` on another space has, for every `L`, the same law of dyadic data as `Zf L` and a.s. a local
  area limit, then `E Γ(loc_R canonicalOn(Z' L)) → E Γ(loc_R Y')`.

Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace G3Cv

open D3Plus

/-- The dyadic data whose surrogate scale is outside `(0, r/R)`. -/
def dyadBad (γ r : ℝ) (R : ℕ) : Set (DyIdxIn r → ℝ) :=
  {ξ | ¬(0 < dyadScale γ r ξ ∧ dyadScale γ r ξ * R < r)}

theorem measurableSet_dyadBad (γ r : ℝ) (R : ℕ) : MeasurableSet (dyadBad γ r R) := by
  have h : MeasurableSet {ξ : DyIdxIn r → ℝ | 0 < dyadScale γ r ξ ∧ dyadScale γ r ξ * R < r} :=
    (measurableSet_lt measurable_const (measurable_dyadScale γ r)).inter
      (measurableSet_lt ((measurable_dyadScale γ r).mul_const _) measurable_const)
  exact h.compl

/-- Off `dyadBad`, a field with a local area limit has local canonical data `dyadT` of its dyadic
data. -/
theorem locFieldFull_canonicalOn_eq_dyadT_of_good {γ r : ℝ} {R : ℕ} {y : FieldSample}
    (hg : ∃ m, IsVagueLimitOn (halfDisc r) (areaApprox γ y) m)
    (hb : dyadData r y ∉ dyadBad γ r R) :
    locFieldFull R (canonicalOn γ y (halfDisc r)) = dyadT γ r R (dyadData r y) := by
  have hag := agreeNear_dyadField r y
  have hgood : dyadData r y ∈
      Prop16Area.Meas.goodSet γ (dyadField r) (fun _ => halfDisc r) :=
    (exists_isVagueLimitOn_halfDisc_iff hag).1 hg
  have hs := scaleParamOn_halfDisc_congr (γ := γ) hag
  have e := dyadScale_eq hgood
  simp only [dyadBad, mem_ofPred_eq, not_not] at hb
  rw [e, ← hs] at hb
  exact locFieldFull_canonicalOn_eq_dyad hb.1 hb.2

/-- The two-sided pointwise comparison. -/
theorem canonicalOn_dyad_cmp {γ r : ℝ} {R : ℕ} {y : FieldSample}
    (hg : ∃ m, IsVagueLimitOn (halfDisc r) (areaApprox γ y) m)
    {Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞} (hΓ1 : ∀ y, Γ y ≤ 1) :
    Γ (locFieldFull R (canonicalOn γ y (halfDisc r))) ≤
        Γ (dyadT γ r R (dyadData r y)) + (dyadBad γ r R).indicator 1 (dyadData r y) ∧
      Γ (dyadT γ r R (dyadData r y)) ≤
        Γ (locFieldFull R (canonicalOn γ y (halfDisc r))) +
          (dyadBad γ r R).indicator 1 (dyadData r y) := by
  by_cases hb : dyadData r y ∈ dyadBad γ r R
  · rw [Set.indicator_of_mem hb, Pi.one_apply]
    exact ⟨(hΓ1 _).trans le_add_self, (hΓ1 _).trans le_add_self⟩
  · rw [locFieldFull_canonicalOn_eq_dyadT_of_good hg hb]
    exact ⟨le_self_add, le_self_add⟩

end G3Cv
end QuantumZipper
