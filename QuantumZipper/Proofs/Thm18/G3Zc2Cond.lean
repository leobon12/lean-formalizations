import QuantumZipper.Proofs.Thm18.G3Zc2Law2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZOOM-C 2: the conditional zoom limit, transferred through the joint dyadic law

`cond_zoom_of_lawEq`: let `Zf L` agree near `0` with a D3⁺ model (`Setup`, any `α`) and let `V` be
a conditioning variable which is a.s. a measurable function of the `Setup`'s `Ξ` (e.g. far field
increments, `exists_g0Setup_palm_far`, or outside coordinates and cut lengths). Let `(Z' L, V')`
on another space have, for every `L`, the same **joint** law of (dyadic data, conditioning
variable) as `(Zf L, V)`, with a.s. local area limits. Then, **uniformly over measurable events
`B` of the conditioning variable**, eventually in `L`,

  `E'[1_B(V') Γ(loc canonicalOn(Z' L))] ≈ P'(V' ∈ B) · E Γ(loc Y')`   (within `η`).

This is the conditional fixed-point zoom (the form of the G2 leaves `G2RootXFixStmt`,
`G2RootRFixStmt`: Sheffield, arXiv:1012.4797, Prop. 1.6 and the proof of Prop. 5.5, pp. 24–25,
65) for any field whose joint law of zoom data and conditioning data is that of a coupled D3⁺
model, e.g. the Palm field of `G3WedgePalmIdStmt` zoomed through the local maps of the curve.
Proof: D3⁺(i) for `Zf` with `Φ(ω, y) = 1_B(G(Ξ ω)) Γ(y)` (`d3_transfer_of_agree`), and the
comparison through `dyadT` on both spaces (G3Zc2Law). Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace G3Cv

open D3Plus

/-- Expectation bounds for `1_B(V) Γ(zoom)` through the joint law of (dyadic data, `V`). -/
theorem lintegral_cond_dyad {γ r : ℝ} {R : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {Eb : Type} [MeasurableSpace Eb] {Z : Ω → FieldSample} {V : Ω → Eb}
    (hm : AEMeasurable (fun ω => (dyadData r (Z ω), V ω)) P)
    (hg : ∀ᵐ ω ∂P, ∃ m, IsVagueLimitOn (halfDisc r) (areaApprox γ (Z ω)) m)
    {Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞} (hΓ : Measurable Γ) (hΓ1 : ∀ y, Γ y ≤ 1)
    {B : Set Eb} (hB : MeasurableSet B) :
    ∫⁻ ω, B.indicator 1 (V ω) * Γ (locFieldFull R (canonicalOn γ (Z ω) (halfDisc r))) ∂P ≤
        ∫⁻ q, B.indicator 1 q.2 * Γ (dyadT γ r R q.1) ∂(P.map fun ω => (dyadData r (Z ω), V ω)) +
          (P.map fun ω => (dyadData r (Z ω), V ω)) (Prod.fst ⁻¹' dyadBad γ r R) ∧
      ∫⁻ q, B.indicator 1 q.2 * Γ (dyadT γ r R q.1) ∂(P.map fun ω => (dyadData r (Z ω), V ω)) ≤
        ∫⁻ ω, B.indicator 1 (V ω) * Γ (locFieldFull R (canonicalOn γ (Z ω) (halfDisc r))) ∂P +
          (P.map fun ω => (dyadData r (Z ω), V ω)) (Prod.fst ⁻¹' dyadBad γ r R) := by
  set J := fun ω => (dyadData r (Z ω), V ω) with hJ
  have hBd : MeasurableSet (Prod.fst ⁻¹' dyadBad γ r R : Set ((DyIdxIn r → ℝ) × Eb)) :=
    measurable_fst (measurableSet_dyadBad γ r R)
  have hGm : Measurable fun q : (DyIdxIn r → ℝ) × Eb =>
      B.indicator (1 : Eb → ℝ≥0∞) q.2 * Γ (dyadT γ r R q.1) :=
    ((measurable_const.indicator hB).comp measurable_snd).mul
      (hΓ.comp ((measurable_dyadT γ r R).comp measurable_fst))
  have hIm : Measurable ((Prod.fst ⁻¹' dyadBad γ r R : Set ((DyIdxIn r → ℝ) × Eb)).indicator
      (1 : (DyIdxIn r → ℝ) × Eb → ℝ≥0∞)) := measurable_const.indicator hBd
  have e0 := lintegral_map' hGm.aemeasurable hm
  have e1 : (P.map J) (Prod.fst ⁻¹' dyadBad γ r R) = ∫⁻ ω, (Prod.fst ⁻¹' dyadBad γ r R :
      Set ((DyIdxIn r → ℝ) × Eb)).indicator 1 (J ω) ∂P := by
    rw [← lintegral_indicator_one hBd]; exact lintegral_map' hIm.aemeasurable hm
  have hA : AEMeasurable (fun ω => (Prod.fst ⁻¹' dyadBad γ r R :
      Set ((DyIdxIn r → ℝ) × Eb)).indicator (1 : (DyIdxIn r → ℝ) × Eb → ℝ≥0∞) (J ω)) P :=
    hIm.comp_aemeasurable hm
  have ind : ∀ ω, (Prod.fst ⁻¹' dyadBad γ r R : Set ((DyIdxIn r → ℝ) × Eb)).indicator
      (1 : (DyIdxIn r → ℝ) × Eb → ℝ≥0∞) (J ω) =
      (dyadBad γ r R).indicator 1 (dyadData r (Z ω)) := fun ω => by
    by_cases h : dyadData r (Z ω) ∈ dyadBad γ r R
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show J ω ∈ _ from h)]; rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show J ω ∉ _ from h)]
  have hpt : ∀ᵐ ω ∂P,
      B.indicator 1 (V ω) * Γ (locFieldFull R (canonicalOn γ (Z ω) (halfDisc r))) ≤
        B.indicator 1 (J ω).2 * Γ (dyadT γ r R (J ω).1) +
          (dyadBad γ r R).indicator 1 (dyadData r (Z ω)) ∧
      B.indicator 1 (J ω).2 * Γ (dyadT γ r R (J ω).1) ≤
        B.indicator 1 (V ω) * Γ (locFieldFull R (canonicalOn γ (Z ω) (halfDisc r))) +
          (dyadBad γ r R).indicator 1 (dyadData r (Z ω)) := by
    filter_upwards [hg] with ω h
    obtain ⟨a1, a2⟩ := canonicalOn_dyad_cmp (R := R) h hΓ1
    have hi : B.indicator (1 : Eb → ℝ≥0∞) (V ω) ≤ 1 := Set.indicator_le (fun _ _ => le_rfl) _
    have k : ∀ x y e : ℝ≥0∞, x ≤ y + e →
        B.indicator (1 : Eb → ℝ≥0∞) (V ω) * x ≤ B.indicator (1 : Eb → ℝ≥0∞) (V ω) * y + e :=
      fun x y e hxy => calc
        _ ≤ B.indicator (1 : Eb → ℝ≥0∞) (V ω) * (y + e) := mul_le_mul' le_rfl hxy
        _ = B.indicator (1 : Eb → ℝ≥0∞) (V ω) * y + B.indicator (1 : Eb → ℝ≥0∞) (V ω) * e :=
          mul_add _ _ _
        _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_left' hi)
    exact ⟨k _ _ _ a1, k _ _ _ a2⟩
  rw [e0, e1]
  simp only [ind]
  have hA' := hA
  simp only [ind] at hA'
  constructor
  · exact (lintegral_mono_ae (hpt.mono fun ω h => h.1)).trans_eq (lintegral_add_right' _ hA')
  · exact (lintegral_mono_ae (hpt.mono fun ω h => h.2)).trans_eq (lintegral_add_right' _ hA')

end G3Cv
end QuantumZipper
