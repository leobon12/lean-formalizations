import QuantumZipper.Proofs.Thm18.G3Z2b2Cmp
import QuantumZipper.Proofs.Thm18.G1RegLogDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3Z2B-2 (10): the deterministic part of the regularity conditions of the measurable maps

On a good path, the measurable local maps `g3mapB Ψ left a b x' = b · (Ψ_a(· + B) − x')` are
holomorphic and injective on `ℍ`. So `log |f'|` is integrable on every folded circle
(`G1.integrable_log_norm_deriv_foldedCircle_of_injOn`, Koebe distortion), and the first clause
of `G1.ChoiceRegular` holds deterministically (`choiceRegular_g3mapB`). Only the analytic
clauses `ChoiceRest` (RC3 exactness, goodness, positive scale, scale consistency) remain as
inputs. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Complex
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Z2b2

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- The measurable local maps are injective on `ℍ` on good paths. -/
theorem injOn_g3mapB {γ : ℝ} (hsel : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ} (hac : Continuous a)
    (hs : IsSimpleChord (pathTrace (γ ^ 2) a)) (left : Bool) {b : ℝ} (hb : 0 < b) (x' : ℝ) :
    InjOn (g3mapB Ψ left a b x') H := by
  obtain ⟨φ, hφ, hΨa⟩ := hsel.2.2 a hac hs left
  have hinj : InjOn (Ψ left a) H := by
    rw [hΨa]; exact hφ.1.invOn_invFunOn.2.injOn
  set B : ℂ := (g3bpre Ψ left a x' : ℂ) with hBdef
  intro w hw v hv hwv
  have hb0 : (b : ℂ) ≠ 0 := ofReal_ne_zero.2 hb.ne'
  have hwB : w + B ∈ H := by
    have hw' : 0 < w.im := hw
    show 0 < (w + B).im
    simpa [hBdef] using hw'
  have hvB : v + B ∈ H := by
    have hv' : 0 < v.im := hv
    show 0 < (v + B).im
    simpa [hBdef] using hv'
  have e : Ψ left a (w + B) = Ψ left a (v + B) := by
    have h1 : (b : ℂ) * (Ψ left a (w + B) - (x' : ℂ)) = (b : ℂ) * (Ψ left a (v + B) - (x' : ℂ)) :=
      hwv
    have h2 := mul_left_cancel₀ hb0 h1
    exact sub_left_inj.1 h2
  have := hinj hwB hvB e
  exact add_right_cancel this

/-- The analytic clauses of `DilRegAt` (the regularity identities). -/
def DilRegCore (γ : ℝ) (y : FieldSample) (b x : ℝ) (f : ℂ → ℂ) (σ : Measure ℂ) : Prop :=
  evalReg (translate (rescale y (Qc γ) b) ((x / b : ℝ) : ℂ)) (σ.map f) =
      translate (rescale y (Qc γ) b) ((x / b : ℝ) : ℂ) (σ.map f) ∧
    evalReg (rescale y (Qc γ) b) ((σ.map f).map (· + ((x / b : ℝ) : ℂ))) =
      rescale y (Qc γ) b ((σ.map f).map (· + ((x / b : ℝ) : ℂ))) ∧
    evalReg (translate y (x : ℂ)) (σ.map fun w => (b : ℂ) * f w) =
      translate y (x : ℂ) (σ.map fun w => (b : ℂ) * f w)

/-- **The curve maps satisfy the deterministic clauses of `DilReg`** (holomorphic, injective
with non-vanishing derivative on `ℍ`; folded circles are carried by `ℍ`). -/
theorem dilReg_g1zLocMap {γ : ℝ} {a : ℝ≥0 → ℝ} (hs : IsSimpleChord (pathTrace (γ ^ 2) a))
    (left : Bool) (hN : IsNormalizedUniformizer (sideDom (pathTrace (γ ^ 2) a) left)
      (uniformizer (sideDom (pathTrace (γ ^ 2) a) left)))
    {y : FieldSample} {b x x' : ℝ}
    (h : ∀ (d : ℂ) (k : ℕ), DilRegCore γ y b x (g1zLocMap left (pathDrive (γ ^ 2) a) x')
      (foldedCircle d (radius k))) :
    DilReg γ y b x (g1zLocMap left (pathDrive (γ ^ 2) a) x') := by
  obtain ⟨hd, hd0, -, -⟩ := G1.invFunOn_props (G1.isOpen_component hs left) hN
  set ψ := g1zSideMap left (pathDrive (γ ^ 2) a) with hψ
  set B : ℂ := (g1zBdryPre left (pathDrive (γ ^ 2) a) x' : ℂ) with hBdef
  have hmemH : ∀ w ∈ H, w + B ∈ H := fun w hw => by
    have hw' : 0 < w.im := hw
    show 0 < (w + B).im
    simpa [hBdef] using hw'
  have hH : IsOpen H := isOpen_lt continuous_const Complex.continuous_im
  have hfeq : g1zLocMap left (pathDrive (γ ^ 2) a) x' = fun w => ψ (w + B) - (x' : ℂ) := rfl
  have hder : ∀ w ∈ H, HasDerivAt (g1zLocMap left (pathDrive (γ ^ 2) a) x')
      (deriv ψ (w + B)) w := fun w hw => by
    have h1 : DifferentiableAt ℂ ψ (w + B) := hd.differentiableAt (hH.mem_nhds (hmemH w hw))
    rw [hfeq]
    exact (h1.hasDerivAt.comp_add_const w B).sub_const (x' : ℂ)
  have hfd : DifferentiableOn ℂ (g1zLocMap left (pathDrive (γ ^ 2) a) x') H := fun w hw =>
    (hder w hw).differentiableAt.differentiableWithinAt
  have hinjψ : InjOn ψ H := hN.1.invOn_invFunOn.2.injOn
  have hinj : InjOn (g1zLocMap left (pathDrive (γ ^ 2) a) x') H := by
    intro w hw v hv hwv
    rw [hfeq] at hwv
    have e : ψ (w + B) = ψ (v + B) := sub_left_inj.1 hwv
    exact add_right_cancel (hinjψ (hmemH w hw) (hmemH v hv) e)
  intro d k
  obtain ⟨h1, h2, h3⟩ := h d k
  refine ⟨h1, h2, h3, G1.integrable_log_norm_deriv_foldedCircle_of_injOn hfd hinj d
    (radius_pos k), ?_⟩
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H d (radius_pos k)] with w hw
  rw [(hder w hw).deriv]
  exact hd0 _ (hmemH w hw)

end G3Z2b2
end Thm18Asm
end QuantumZipper
