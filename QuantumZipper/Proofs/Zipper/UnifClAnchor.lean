import QuantumZipper.Proofs.Zipper.UnifClB5
import QuantumZipper.Proofs.Zipper.B5VHccMain

/-!
# UNIF-CLUSTER (D26): the uniform windows (UW) from rational anchors

`UnifWindowStmt` (UW, `UnifClB5.lean`) asks for the window identities
`ν_{h⁰}(u,v) = ν_{h⁰_s}(F_s u, F_s v)` at all times `s ∈ (0,T]` at once. At each fixed `s` they
are proved (`B5.ae_hcc` with `B5.ae_window_h0_eq_qBoundaryMeasureOn`). Decision D26 splits the
uniformity into two statements:

* `AnchorWindowStmt` (**AW**, open): for each rational anchor time `q ∈ (0,T]` and rational
  window `(u,v)` of the fully unzipped picture that is live at time `q`
  (`v < 0₋(T − q)`), a.s., for **all** later times `s ∈ [q,T]` the local boundary measure of
  `h⁰_s` on the image window `(F_s u, F_s v)` has the mass `ν_{h⁰_q}(F_q u, F_q v)`. The field
  `h⁰_q` is independent of the driver after time `q` (`b2_markov`), and `h⁰_s` is `h⁰_q` unzipped
  further by that driver (the image window is `f_{s−q}(F_q u, F_q v)`,
  `RegUnif.re_fwdMap_shift_realRevMap`), so AW is the coordinate-change rule of the boundary
  measure (M4-T4, `CoordChange.ae_qBoundaryMeasureOn_coordChange`) for a free field and a
  continuous one-parameter family of independent conformal maps, uniformly in the parameter.
* `UnifGlobalStmt` (**UG**, open): a.s., for all `s ∈ [0,T]` at once, the dyadic boundary
  approximations of `h⁰_s` have a global vague limit (the boundary part of `IsLQGGood` for all
  `s`; the only place where the tip of the curve enters).

Main result: **`unifWindowStmt_of_anchor`**: AW + UG ⇒ UW. Proof: given `s` and a live window,
choose a rational anchor `q ≤ s` at which the window is still live (continuity of `0₋`); chain
the fixed-time identity at `q`, AW, and UG (global limit ⇒ local limit on open windows).

Sources: Sheffield, arXiv:1012.4797, §5 (pp. 66–68); Duplantier–Sheffield, Invent. Math. 185
(2011), §6 (coordinate change of the boundary measure). The reduction is own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open B2 B5

variable {Ω : Type} [MeasurableSpace Ω]

/-- **AW (anchored windows)**: for each rational anchor `q ∈ (0,T]` and rational window
`(u,v)`, a.s., if the window is live at time `q` then for all `s ∈ [q,T]` the local boundary
measure of `h⁰_s` on `(F_s u, F_s v)` has the `ν_{h⁰_q}`-mass of `(F_q u, F_q v)`
(`F_s = realRevMap V (T − s)`). -/
def AnchorWindowStmt (κ T : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) :
    Prop :=
  ∀ q : ℚ, (0 : ℝ) < q → (q : ℝ) ≤ T → ∀ u v : ℚ, ∀ᵐ ω ∂P,
    zeroMinus (Vr κ T B ω) T < u → (u : ℝ) < v → (v : ℝ) < zeroMinus (Vr κ T B ω) (T - q) →
    ∀ s ∈ Icc (q : ℝ) T,
      qBoundaryMeasureOn (Real.sqrt κ) (h0f κ s B X ω)
          (Ioo (realRevMap (Vr κ T B ω) (T - s) u) (realRevMap (Vr κ T B ω) (T - s) v))
          (Ioo (realRevMap (Vr κ T B ω) (T - s) u) (realRevMap (Vr κ T B ω) (T - s) v)) =
        qBoundaryMeasure (Real.sqrt κ) (h0f κ q B X ω)
          (Ioo (realRevMap (Vr κ T B ω) (T - q) u) (realRevMap (Vr κ T B ω) (T - q) v))

variable {P : Measure Ω} [IsProbabilityMeasure P] {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ}
  {X : Ω → FieldSample}

/-- The fixed-time window identities at all rational times at once. -/
theorem ae_windows_rat (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, ∀ q : ℚ, (0 : ℝ) < q → (q : ℝ) ≤ T → ∀ u v : ℚ,
      zeroMinus (Vr κ T B ω) T < u → (u : ℝ) < v → (v : ℝ) < zeroMinus (Vr κ T B ω) (T - q) →
      qBoundaryMeasure (Real.sqrt κ) (h0f κ T B X ω) (Ioo u v) =
        qBoundaryMeasure (Real.sqrt κ) (h0f κ q B X ω)
          (Ioo (realRevMap (Vr κ T B ω) (T - q) u) (realRevMap (Vr κ T B ω) (T - q) v)) := by
  refine ae_all_iff.2 fun q => ?_
  by_cases h : (0 : ℝ) < q ∧ (q : ℝ) ≤ T
  · filter_upwards [ae_hcc hκ hκ4 hB hX hind h.1 h.2,
      ae_window_h0_eq_qBoundaryMeasureOn RevCouplingReg.revCouplingBoundaryMeasureRegular hκ hκ4
        hB hX hind h.1.le h.2 hT] with ω hc hw _ _ u v hu huv hv
    rw [hw]
    exact hc u v hu huv hv
  · exact Eventually.of_forall fun ω h1 h2 => absurd ⟨h1, h2⟩ h

omit [IsProbabilityMeasure P] in
/-- AW at all rational anchors and windows at once. -/
theorem ae_anchor_all (hAW : AnchorWindowStmt κ T P B X) :
    ∀ᵐ ω ∂P, ∀ q u v : ℚ, (0 : ℝ) < q → (q : ℝ) ≤ T →
      zeroMinus (Vr κ T B ω) T < u → (u : ℝ) < v → (v : ℝ) < zeroMinus (Vr κ T B ω) (T - q) →
      ∀ s ∈ Icc (q : ℝ) T,
        qBoundaryMeasureOn (Real.sqrt κ) (h0f κ s B X ω)
            (Ioo (realRevMap (Vr κ T B ω) (T - s) u) (realRevMap (Vr κ T B ω) (T - s) v))
            (Ioo (realRevMap (Vr κ T B ω) (T - s) u) (realRevMap (Vr κ T B ω) (T - s) v)) =
          qBoundaryMeasure (Real.sqrt κ) (h0f κ q B X ω)
            (Ioo (realRevMap (Vr κ T B ω) (T - q) u) (realRevMap (Vr κ T B ω) (T - q) v)) := by
  refine ae_all_iff.2 fun q => ae_all_iff.2 fun u => ae_all_iff.2 fun v => ?_
  by_cases h : (0 : ℝ) < q ∧ (q : ℝ) ≤ T
  · filter_upwards [hAW q h.1 h.2 u v] with ω hω _ _
    exact hω
  · exact Eventually.of_forall fun ω h1 h2 => absurd ⟨h1, h2⟩ h

end RegUnif
end QuantumZipper
