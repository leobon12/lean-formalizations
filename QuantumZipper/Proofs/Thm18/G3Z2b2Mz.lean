import QuantumZipper.Proofs.Thm18.G3Z2b2Cmp
import QuantumZipper.Proofs.Thm18.ASepGCEval
import QuantumZipper.Proofs.Thm18.G3FidProxy

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3Z2B-2 (5): the zoom law through the measurable local maps is jointly measurable

For the field `W`, the path `a`, a scale `b > 0` and a boundary point `x`, the zoom of `W` at `x`
through the measurable local map `g3mapB Ψ left a b (x/b) = b · Λ(a, x/b, ·)` has a law datum
`lawOf (canonProxy γ ·)` that is a **jointly measurable** function of `(W, a, b, x)`
(`measurable_g3zoomLawM`, `g3zoomLawM_eq`). This is the measurable `G` that the Fubini step Z2a
(`G3PathFubiniStmt`) needs for the Palm-window integrand through the curve maps. Take `b = 1`
for the wedge representative itself, or `b = scaleParam γ W` after the dilation of
`wedgePalm_canonical_eq`.

Route (the pattern of `G3ConcreteMaps.measurable_zoomLaw`): the canonical proxy only reads the
dyadic circle coordinates (`canonProxy_recon`). Each coordinate is a regularized evaluation along
a parametrized pushforward (`ASep.GC.measurable_evalReg_map_family`), plus `Q ∫ log|f'|`. The
log-derivative term is read from the measurable selection (`G1PsiSel`, second clause) through
the chain rule `f' = b Ψ'(· + B)`, which holds a.e. on folded circles (they are carried by `ℍ`,
where `Ψ' ≠ 0`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Complex
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Z2b2

open D3Plus Factorization

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- The parameter space: field, path, scale, point. -/
abbrev G3Par : Type := FieldSample × (ℝ≥0 → ℝ) × ℝ × ℝ

/-- The measurable local map of a parameter. -/
def g3mapP (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (p : G3Par) : ℂ → ℂ :=
  g3mapB Ψ left p.2.1 p.2.2.1 (p.2.2.2 / p.2.2.1)

/-- The `i`-th dyadic folded circle. -/
abbrev fcI (i : ℕ) : Measure ℂ := foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2)

/-- The measurable version of the circle coordinates of the zoom through the measurable map. -/
def g3coordsM (γ L : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (p : G3Par) : ℕ → ℝ :=
  fun i => (evalReg (translate p.1 (p.2.2.2 : ℂ)) ((fcI i).map (g3mapP Ψ left p)) +
    Qc γ * ∫ w, (Real.log |p.2.2.1| + Real.log ‖deriv (Ψ left p.2.1)
      (w + (g3bpre Ψ left p.2.1 (p.2.2.2 / p.2.2.1) : ℂ))‖) ∂(fcI i)) + L / γ

/-- The measurable zoom law datum. -/
def g3zoomLawM (γ L : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (p : G3Par) : LawD :=
  lawOf (canonOfCoords γ (g3coordsM γ L Ψ left p))

theorem g3m_hx : Measurable fun p : G3Par => p.2.2.2 :=
  measurable_snd.comp (measurable_snd.comp measurable_snd)

theorem g3m_hb : Measurable fun p : G3Par => p.2.2.1 :=
  measurable_fst.comp (measurable_snd.comp measurable_snd)

theorem g3m_ha : Measurable fun p : G3Par => p.2.1 := measurable_fst.comp measurable_snd

theorem g3m_hxb : Measurable fun p : G3Par => p.2.2.2 / p.2.2.1 := g3m_hx.div g3m_hb

theorem g3m_hT (d : ℂ) (k : ℕ) :
    Measurable fun p : G3Par => translate p.1 (p.2.2.2 : ℂ) (foldedCircle d (radius k)) := by
  have hY : ∀ k : ℕ, Measurable fun q : G3Par × ℂ => avgReg q.1.1 k q.2 := fun k =>
    (measurable_avgReg k).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hφ : Measurable fun q : G3Par × ℂ => q.2 + (q.1.2.2.2 : ℂ) :=
    measurable_snd.add (Complex.measurable_ofReal.comp (g3m_hx.comp measurable_fst))
  exact ASep.GC.measurable_evalReg_map_family (fun p : G3Par => p.1) hY _
    (fun p z => z + (p.2.2.2 : ℂ)) hφ

theorem g3m_hTa (k : ℕ) : Measurable fun q : G3Par × ℂ =>
    avgReg (translate q.1.1 (q.1.2.2.2 : ℂ)) k q.2 :=
  ASep.GC.measurable_avgReg_family (fun p : G3Par => translate p.1 (p.2.2.2 : ℂ)) g3m_hT k

theorem g3m_hM {γ : ℝ} (hsel : G1PsiSel γ Ψ) (left : Bool) :
    Measurable fun q : G3Par × ℂ => g3mapP Ψ left q.1 q.2 := by
  have h1 : Measurable fun q : G3Par × ℂ =>
      g3locM Ψ left (q.1.2.1, q.1.2.2.2 / q.1.2.2.1, q.2) :=
    (measurable_g3locM hsel.1 left).comp ((g3m_ha.comp measurable_fst).prodMk
      ((g3m_hxb.comp measurable_fst).prodMk measurable_snd))
  exact (Complex.measurable_ofReal.comp (g3m_hb.comp measurable_fst)).mul h1

theorem g3m_hL {γ : ℝ} (hsel : G1PsiSel γ Ψ) (left : Bool) (i : ℕ) :
    Measurable fun p : G3Par => ∫ w, (Real.log |p.2.2.1| + Real.log ‖deriv
      (Ψ left p.2.1) (w + (g3bpre Ψ left p.2.1 (p.2.2.2 / p.2.2.1) : ℂ))‖) ∂(fcI i) := by
  have hB : Measurable fun p : G3Par => g3bpre Ψ left p.2.1 (p.2.2.2 / p.2.2.1) :=
    (measurable_g3bpre hsel.1 left).comp (f := fun p : G3Par => (p.2.1, p.2.2.2 / p.2.2.1))
      (g3m_ha.prodMk g3m_hxb)
  have hj : Measurable fun q : G3Par × ℂ => Real.log |q.1.2.2.1| + Real.log ‖deriv
      (Ψ left q.1.2.1) (q.2 + (g3bpre Ψ left q.1.2.1 (q.1.2.2.2 / q.1.2.2.1) : ℂ))‖ := by
    have habs : Measurable fun q : G3Par × ℂ => Real.log |q.1.2.2.1| :=
      Real.measurable_log.comp (continuous_abs.measurable.comp (g3m_hb.comp measurable_fst))
    refine habs.add ?_
    have hB' : Measurable fun q : G3Par × ℂ =>
        ((g3bpre Ψ left q.1.2.1 (q.1.2.2.2 / q.1.2.2.1) : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp (hB.comp measurable_fst)
    have hz : Measurable fun q : G3Par × ℂ =>
        (q.1.2.1, q.2 + ((g3bpre Ψ left q.1.2.1 (q.1.2.2.2 / q.1.2.2.1) : ℝ) : ℂ)) :=
      (g3m_ha.comp measurable_fst).prodMk (measurable_snd.add hB')
    exact (hsel.2.1 left).comp (f := fun q : G3Par × ℂ =>
      (q.1.2.1, q.2 + ((g3bpre Ψ left q.1.2.1 (q.1.2.2.2 / q.1.2.2.1) : ℝ) : ℂ))) hz
  exact (StronglyMeasurable.integral_prod_right' (f := fun q : G3Par × ℂ =>
    Real.log |q.1.2.2.1| + Real.log ‖deriv (Ψ left q.1.2.1)
      (q.2 + (g3bpre Ψ left q.1.2.1 (q.1.2.2.2 / q.1.2.2.1) : ℂ))‖)
    hj.stronglyMeasurable).measurable

theorem measurable_g3coordsM {γ : ℝ} (hsel : G1PsiSel γ Ψ) (L : ℝ) (left : Bool) :
    Measurable (g3coordsM γ L Ψ left) := by
  refine measurable_pi_iff.2 fun i => ?_
  have h1 : Measurable fun p : G3Par =>
      evalReg (translate p.1 (p.2.2.2 : ℂ)) ((fcI i).map (g3mapP Ψ left p)) :=
    ASep.GC.measurable_evalReg_map_family (fun p : G3Par => translate p.1 (p.2.2.2 : ℂ)) g3m_hTa
      (fcI i) (g3mapP Ψ left) (g3m_hM hsel left)
  exact (h1.add (measurable_const.mul (g3m_hL hsel left i))).add measurable_const

/-- **The measurable zoom law datum is measurable.** -/
theorem measurable_g3zoomLawM {γ : ℝ} (hsel : G1PsiSel γ Ψ) (L : ℝ) (left : Bool) :
    Measurable (g3zoomLawM γ L Ψ left) :=
  (measurable_lawOf_canon γ).comp (measurable_g3coordsM hsel L left)

/-- On good paths and positive scales the measurable coordinates are the circle coordinates of
the zoom through the measurable map. -/
theorem g3coordsM_eq {γ : ℝ} (hsel : G1PsiSel γ Ψ) (L : ℝ) (left : Bool) {p : G3Par}
    (hac : Continuous p.2.1) (hs : IsSimpleChord (pathTrace (γ ^ 2) p.2.1)) (hb : 0 < p.2.2.1) :
    g3coordsM γ L Ψ left p = coords (zoomFieldVia γ L p.1 p.2.2.2 (g3mapP Ψ left p)) := by
  obtain ⟨φ, hφ, hΨa⟩ := hsel.2.2 p.2.1 hac hs left
  obtain ⟨-, hd0, -, -⟩ := G1.invFunOn_props (G1.isOpen_component hs left) hφ
  funext i
  set B : ℂ := (g3bpre Ψ left p.2.1 (p.2.2.2 / p.2.2.1) : ℂ) with hBdef
  have hder : ∀ w, deriv (g3mapP Ψ left p) w = (p.2.2.1 : ℂ) * deriv (Ψ left p.2.1) (w + B) := by
    intro w
    show deriv (fun w => (p.2.2.1 : ℂ) * (Ψ left p.2.1 (w + B) - ((p.2.2.2 / p.2.2.1 : ℝ) : ℂ)))
      w = _
    rw [deriv_const_mul_field']
    beta_reduce
    rw [deriv_sub_const, deriv_comp_add_const]
  have hfc : ∀ᵐ w ∂(fcI i), w ∈ H := TwoPoint.foldedCircle_ae_mem_H _ (radius_pos _)
  have hlog : ∫ w, Real.log ‖deriv (g3mapP Ψ left p) w‖ ∂(fcI i) =
      ∫ w, (Real.log |p.2.2.1| + Real.log ‖deriv (Ψ left p.2.1) (w + B)‖) ∂(fcI i) := by
    refine integral_congr_ae ?_
    filter_upwards [hfc] with w hw
    have hwB : w + B ∈ H := by
      have hw' : 0 < w.im := hw
      show 0 < (w + B).im
      simpa [hBdef] using hw'
    have hne : deriv (Ψ left p.2.1) (w + B) ≠ 0 := by rw [hΨa]; exact hd0 _ hwB
    rw [hder, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Real.log_mul (abs_pos.2 hb.ne').ne' (norm_ne_zero_iff.2 hne)]
  show _ = (evalReg (translate p.1 (p.2.2.2 : ℂ)) ((fcI i).map (g3mapP Ψ left p)) +
      Qc γ * ∫ w, Real.log ‖deriv (g3mapP Ψ left p) w‖ ∂(fcI i)) + L / γ * ((fcI i) univ).toReal
  rw [hlog, measure_univ, ENNReal.toReal_one, mul_one]
  rfl

end G3Z2b2
end Thm18Asm
end QuantumZipper
