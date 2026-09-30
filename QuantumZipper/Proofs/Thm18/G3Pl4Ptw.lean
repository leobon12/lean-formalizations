import QuantumZipper.Proofs.Thm18.G3Pl4Win
import QuantumZipper.Proofs.Thm18.G3Pl4Loc
import QuantumZipper.Proofs.Thm18.LenPos

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T, (G-b), part (b): pathwise locality of the capped Palm functional

Sheffield, arXiv:1012.4797, pp. 71–72 and Remark 5.7: at a large zoom level the Palm-window
functional only sees the field near the boundary segment where the Palm point and its length
partner live. Precisely (`g3pl4_phiCap_le_of_agree`): let `y`, `y'` agree on all folded circles
inside the unit disc, with the same boundary measure on `[−1/2, 1/2]`; let `δ ≤ 1/4` with
`ν[−δ, 0] < ν[−1/2, 0]` (so the capped window lies in `(−1/2, 0)`) and `ν[−δ, 0] ≤ ν[0, 1/4]` (so
the length partners lie in `[0, 1/4]`); let the translates of `y'` be good with positive area on
every half-ball. Then for every `ε > 0`, for all large levels `L`,
`Φcap_L(y) ≤ Φcap_L(y') + ε`.

Proof: on the window both the window and the partner are read from `ν` on `[−1/2, 1/2]`
(`lenRight_eq_of_agree`), the zoom events at a fixed point agree for all large levels
(`g3pl4_eventually_zoom_iff_ball`), and the `ν`-mass of the disagreement set tends to `0` by
dominated convergence (bound `1` on the finite window). Own elementary argument on top of the
cited locality (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Topology symmDiff

namespace QuantumZipper
namespace R18

open Thm18Asm Prop16Area.G

section Ptw

variable {γ δ U : ℝ} {s t : Set LawD} {y y' : FieldSample}

theorem g3pl4_measurable_Icc_zero (ν : Measure ℝ) : Measurable fun x : ℝ => ν (Icc x 0) :=
  Antitone.measurable fun _ _ hab => measure_mono (Icc_subset_Icc_left hab)

theorem g3pl4_measurable_partner (γ : ℝ) (y : FieldSample) :
    Measurable fun x : ℝ => g3zPartner γ y x := by
  unfold g3zPartner
  exact measurable_lenRight.comp (f := fun x : ℝ =>
    ((qBoundaryMeasure γ y, (qBoundaryMeasure γ y (Icc x 0)).toReal) : Measure ℝ × ℝ))
    (measurable_const.prodMk (ENNReal.measurable_toReal.comp (g3pl4_measurable_Icc_zero _)))

/-- The capped window. -/
def g3pl4W (γ δ U : ℝ) (y : FieldSample) : Set ℝ :=
  {b | b < 0 ∧ qBoundaryMeasure γ y (Icc b 0) ≤ ENNReal.ofReal U ∧
    qBoundaryMeasure γ y (Icc b 0) ≤ qBoundaryMeasure γ y (Icc (-δ) 0)}

theorem g3pl4_measurableSet_W (γ δ U : ℝ) (y : FieldSample) : MeasurableSet (g3pl4W γ δ U y) :=
  measurableSet_Iio.inter ((measurableSet_le (g3pl4_measurable_Icc_zero _) measurable_const).inter
    (measurableSet_le (g3pl4_measurable_Icc_zero _) measurable_const))

variable (hag : FcAgree (ball (0 : ℂ) 1) y y')
  (hνr : (qBoundaryMeasure γ y).restrict (Icc (-(1 / 2)) (1 / 2)) =
    (qBoundaryMeasure γ y').restrict (Icc (-(1 / 2)) (1 / 2)))
  (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4)
  (hsep : qBoundaryMeasure γ y (Icc (-δ) 0) < qBoundaryMeasure γ y (Icc (-(1 / 2)) 0))
  (hR : qBoundaryMeasure γ y (Icc (-δ) 0) ≤ qBoundaryMeasure γ y (Icc 0 (1 / 4)))

include hνr in
theorem g3pl4_Icc_eq {a b : ℝ} (ha : -(1 / 2) ≤ a) (hb : b ≤ 1 / 2) :
    qBoundaryMeasure γ y (Icc a b) = qBoundaryMeasure γ y' (Icc a b) := by
  have hsub : Icc a b ⊆ Icc (-(1 / 2) : ℝ) (1 / 2) := Icc_subset_Icc ha hb
  have e := congrArg (fun m : Measure ℝ => m (Icc a b)) hνr
  simp only [Measure.restrict_apply measurableSet_Icc, inter_eq_left.2 hsub] at e
  exact e

include hsep in
theorem g3pl4_W_gt {x : ℝ} (hx : x ∈ g3pl4W γ δ U y) : -(1 / 2) < x := by
  by_contra h
  push Not at h
  exact absurd (hx.2.2.trans_lt hsep) (not_lt.2 (measure_mono (Icc_subset_Icc_left h)))

include hνr hδ hδ4 hsep in
theorem g3pl4_W_eq : g3pl4W γ δ U y = g3pl4W γ δ U y' := by
  have hδ' : -(1 / 2) ≤ -δ := by linarith
  ext x
  constructor
  · intro hx
    have hx2 := g3pl4_W_gt hsep hx
    rw [g3pl4W, mem_ofPred_eq, ← g3pl4_Icc_eq hνr hx2.le (by norm_num),
      ← g3pl4_Icc_eq hνr hδ' (by norm_num)]
    exact hx
  · intro hx
    by_cases h2 : -(1 / 2) < x
    · rw [g3pl4W, mem_ofPred_eq, g3pl4_Icc_eq hνr h2.le (by norm_num),
        g3pl4_Icc_eq hνr hδ' (by norm_num)]
      exact hx
    · push Not at h2
      exfalso
      have e1 := g3pl4_Icc_eq (y := y) (y' := y') hνr (le_refl (-(1 / 2) : ℝ))
        (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      have e2 := g3pl4_Icc_eq (y := y) (y' := y') hνr hδ' (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      have := hx.2.2.trans_lt (e2 ▸ e1 ▸ hsep)
      exact absurd this (not_lt.2 (measure_mono (Icc_subset_Icc_left h2)))

include hνr hδ hδ4 hsep hR in
theorem g3pl4_partner_eq {x : ℝ} (hx : x ∈ g3pl4W γ δ U y) :
    g3zPartner γ y x = g3zPartner γ y' x ∧ 0 ≤ g3zPartner γ y x ∧ g3zPartner γ y x ≤ 1 / 4 := by
  have hx2 := g3pl4_W_gt hsep hx
  have hfin : qBoundaryMeasure γ y (Icc x 0) ≠ ⊤ := (qBoundaryMeasure_Icc_lt_top γ y x 0).ne
  have hℓ : ENNReal.ofReal (qBoundaryMeasure γ y (Icc x 0)).toReal ≤
      qBoundaryMeasure γ y (Icc 0 (1 / 4)) := by
    rw [ENNReal.ofReal_toReal hfin]; exact hx.2.2.trans hR
  refine ⟨?_, Real.sInf_nonneg fun _ h => h.1.le, lenRight_le (by norm_num) hℓ⟩
  unfold g3zPartner
  rw [← g3pl4_Icc_eq hνr hx2.le (by norm_num)]
  exact lenRight_eq_of_agree (by norm_num) hℓ fun z hz hz4 =>
    g3pl4_Icc_eq hνr (by linarith) (by linarith)

end Ptw

end R18
end QuantumZipper
