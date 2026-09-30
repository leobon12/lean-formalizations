import QuantumZipper.Proofs.Thm18.G3Pl4Norm
import QuantumZipper.Proofs.Thm18.G3Pl4Good
import QuantumZipper.Proofs.Thm18.G3Pl4Bdry
import QuantumZipper.Proofs.LQG.PalmNormLocal
import QuantumZipper.Proofs.LQG.LogSingGood

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3Z2B (Z2b): the Palm identity for the boundary measure of the wedge near the root

For the `(γ − 2/γ)`-quantum wedge in its circle-average embedding (the unscaled wedge field
`F2.zU γ X A = wedgeField (lateralPart X) A Q`, the explicit representative of `IsQuantumWedge`
before the unit-area dilation `canonical`), and a window `[a, b] ⊆ [−1/2, 1/2]` not containing
the root `0`, the rooted (Palm) measure `E ∫ w(x) φ(·, x) ν_h(dx)` of the wedge boundary measure
is the integral over `x` of the Palm density times the expectation of `φ` at the Palm-shifted
field `N_S(V + (γ − 2/γ)(−log|·|) + (γ/2)(G_N(x, ·) − k_S))`, where `V` is a free field on the
same space, `S` the unit semicircle, and `φ` reads the field through folded circles inside the
unit disc.

Sources:
* Palm (rooted) measure of the boundary measure: Duplantier–Sheffield, *Liouville quantum gravity
  and KPZ*, Invent. Math. 185 (2011), arXiv:0808.1560, §3.3 (p. 22), in the normalized form
  `PalmNorm.palm_formula_norm_local` (the mean `h` only needs to be continuous near the window).
* The wedge near the root: Sheffield, arXiv:1012.4797, §1.6 and p. 28 — restricted to the unit
  half-disc the wedge is a free field with mean zero on the unit semicircle plus
  `(γ − 2/γ)(−log|·|)`; in Lean `g3pl4_wedge_fcAgree_norm` (pathwise wedge decomposition,
  Duplantier–Miller–Sheffield arXiv:1409.7055 §4.1). The outside radial part of the wedge only
  enters through the part of the field outside the unit disc, which the window and the
  functional do not see (locality of the boundary measure, `g3pl4_restrict_eq_of_agree`).

Own bookkeeping on top of these (AGENT_GUIDE cost rule): the continuous modification of the log
singularity away from `0` and the transfer of both sides through the coupling.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace R18

open Thm18Asm PalmNorm Prop16Area.G

/-- The unit semicircle, the normalizer of the circle-average embedding. -/
abbrev g3zS : Measure ℂ := foldedCircle 0 1

/-- **Z2b (Palm identity for the wedge boundary measure near the root).** On the probability space
of the wedge representative there is a free field `V` such that for every window
`[a, b] ⊆ [−1/2, 1/2]` avoiding `0`, every continuous weight `w ≥ 0` vanishing off `[a, b]`, every
family of folded circles `fc(c_j, r_j)` inside the unit disc and every measurable `φ ≥ 0`:
`E ∫ w(x) φ((h(fc_j))_j, x) ν_h(dx) = ∫ w(x) ρ(x) E φ((h^x(fc_j))_j, x) dx`, `h = F2.zU γ X A`,
`h^x = N_S(ofFun (shiftFun γ Lf S x) + V)`, `ρ = rhoNorm γ Lf S`, `Lf = (γ − 2/γ)(−log|·|)`. -/
def G3WedgePalmIdStmt : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ),
    IsFreeGFFModConstH X P' → IsWedgeProcess (γ - 2 / γ) (Qc γ) A P' →
    IndepFun X (fun ω t => A t ω) P' →
    ∃ V : Ω' → FieldSample, IsFreeGFFModConstH V P' ∧
      ∀ a b : ℝ, Icc a b ⊆ Icc (-(1 / 2)) (1 / 2) → (0 : ℝ) ∉ Icc a b →
      ∀ (c : ℕ → ℂ) (r : ℕ → ℝ), (∀ j, c j ∈ Hbar) → (∀ j, 0 < r j) →
        (∀ j, closedBall (c j) (r j) ∩ Hbar ⊆ ball (0 : ℂ) 1) →
      ∀ w : ℝ → ℝ, Continuous w → (∀ x, 0 ≤ w x) → (∀ x ∉ Icc a b, w x = 0) →
      ∀ φ : (ℕ → ℝ) → ℝ → ℝ≥0∞, Measurable (Function.uncurry φ) →
        ∫⁻ ω, ∫⁻ x, ENNReal.ofReal (w x) *
            φ (fun j => F2.zU γ X A ω (foldedCircle (c j) (r j))) x
            ∂(qBoundaryMeasure γ (F2.zU γ X A ω)) ∂P' =
          ∫⁻ x, ENNReal.ofReal (w x * rhoNorm γ (LogSingGood.Lf (γ - 2 / γ)) g3zS x) *
            ∫⁻ ω, φ (fun j => normAt g3zS (ofFun (shiftFun γ (LogSingGood.Lf (γ - 2 / γ)) g3zS x) +
              V ω) (foldedCircle (c j) (r j))) x ∂P'

/-- A window avoiding `0` stays a positive distance away from `0`. -/
theorem g3z_exists_margin {a b : ℝ} (h0 : (0 : ℝ) ∉ Icc a b) :
    ∃ m : ℝ, 0 < m ∧ ∀ t ∈ Icc a b, m < |t| := by
  by_cases hab : a ≤ b
  · have hne : 0 < a ∨ b < 0 := by
      by_contra hc
      push_neg at hc
      exact h0 ⟨hc.1, hc.2⟩
    rcases hne with ha | hb
    · refine ⟨a / 2, by linarith, fun t ht => ?_⟩
      rw [abs_of_pos (by linarith [ht.1])]; linarith [ht.1]
    · refine ⟨-b / 2, by linarith, fun t ht => ?_⟩
      rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.2]
  · exact ⟨1, one_pos, fun t ht => absurd (ht.1.trans ht.2) hab⟩

/-- The normalized field `N_S(Lf + V)` is `V + logSing` when `V(S) = 0`. -/
theorem g3z_normAt_eq {γ : ℝ} (hγ : 0 < γ) {v : FieldSample} (hv : v g3zS = 0) :
    normAt g3zS (ofFun (LogSingGood.Lf (γ - 2 / γ)) + v) = v + F2.logSingField (γ ^ 2) := by
  have hnorm : ∀ᵐ u ∂foldedCircle 0 1, ‖u‖ = 1 := by
    simpa using WedgeTK.fc_ae_norm (r := 1) one_pos
  have hS : ofFun (LogSingGood.Lf (γ - 2 / γ)) g3zS = 0 := by
    unfold ofFun
    refine integral_eq_zero_of_ae (hnorm.mono fun u hu => ?_)
    simp [LogSingGood.Lf, hu]
  rw [g3pl4_logSingField_eq hγ]
  funext μ
  simp only [normAt, addConst, Pi.add_apply, hS, hv]
  ring

/-- **Z2b proved.** -/
theorem g3WedgePalmIdStmt_holds : G3WedgePalmIdStmt := by
  intro γ hγ hγ2 Ω' _ P' _ X A hX hA hI
  obtain ⟨V, hV, hV0, hag⟩ := g3pl4_wedge_fcAgree_norm hγ hX hA hI
  refine ⟨V, hV, ?_⟩
  intro a b hab h0 c r hc hr hin w hw hw0 hwab φ hφ
  set α : ℝ := γ - 2 / γ with hα
  obtain ⟨m, hm, hmab⟩ := g3z_exists_margin h0
  set h' : ℂ → ℝ := fun v => α * -Real.log (max ‖v‖ m) with hh'
  have hh'c : Continuous h' := by
    refine continuous_const.mul (Continuous.neg ?_)
    exact Real.continuousOn_log.comp_continuous (continuous_norm.max continuous_const)
      fun v => by
        simp only [mem_compl_iff, mem_singleton_iff]
        exact ne_of_gt (lt_of_lt_of_le hm (le_max_right _ _))
  set W : Set ℂ := {v | m < ‖v‖} with hWdef
  have hW : IsOpen W := isOpen_lt continuous_const continuous_norm
  have habW : ∀ t ∈ Icc a b, (t : ℂ) ∈ W := fun t ht => by
    show m < ‖(t : ℂ)‖
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hmab t ht
  have hEq : EqOn (LogSingGood.Lf α) h' W := fun v hv => by
    simp only [hh', LogSingGood.Lf, max_eq_left (le_of_lt (show m < ‖v‖ from hv))]
  have hN : Icc a b ⊆ Icc (-((1 : ℕ) : ℝ)) ((1 : ℕ) : ℝ) := fun t ht => by
    have := hab ht
    push_cast
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hϖ : IsAdmissibleH g3zS := isAdmissibleH_foldedCircle (by simp [Hbar]) one_pos
  have hϖ1 : g3zS univ = 1 := measure_univ
  have hμ : ∀ j, IsAdmissibleH (foldedCircle (c j) (r j)) := fun j =>
    isAdmissibleH_foldedCircle (hc j) (hr j)
  have hint : ∀ (d : ℂ) (ρ : ℝ), Integrable (LogSingGood.Lf α) (foldedCircle d ρ) := fun d ρ =>
    (CoordReg.integrable_log_norm_foldedCircle d ρ).neg.const_mul α
  have hgV := g3pl4_ae_isAreaGood_logSing hγ hγ2 hV
  have hex : ∀ᵐ ω ∂P', ∃ ν, IsVagueLimitR
      (bdryApprox γ (normAt g3zS (ofFun (LogSingGood.Lf α) + V ω))) ν := by
    filter_upwards [hV0, hgV] with ω h0 hg
    rw [g3z_normAt_eq hγ h0]
    exact ⟨_, isVagueLimitR_qBoundaryMeasure_of_isLQGGood hg.1⟩
  have hwc : HasCompactSupport w := HasCompactSupport.intro isCompact_Icc hwab
  have H := palm_formula_norm_local (P := P') (μ := fun j => foldedCircle (c j) (r j)) hV hγ hγ2
    hN hh'c hW habW hEq hϖ hϖ1 hμ (hint 0 1) (fun j => hint (c j) (r j)) hex hw hwc hw0 hwab hφ
  rw [← H]
  have hgZ : ∀ᵐ ω ∂P', IsLQGGood γ (F2.zU γ X A ω) :=
    LogSingGood.wedgeRefGoodAS_holds hγ hγ2 (alpha_lt_Qc hγ hγ2) Ω' _ P' X A inferInstance hX hA hI
  refine lintegral_congr_ae ?_
  filter_upwards [hV0, hag, hgZ, hgV] with ω h0 hagω hgZω hgVω
  rw [g3z_normAt_eq hγ h0]
  have hpair : (fun j => F2.zU γ X A ω (foldedCircle (c j) (r j))) =
      fun j => (V ω + F2.logSingField (γ ^ 2)) (foldedCircle (c j) (r j)) :=
    funext fun j => hagω (c j) (hc j) (r j) (hr j) (hin j)
  rw [hpair]
  set f : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (w x) *
    φ (fun j => (V ω + F2.logSingField (γ ^ 2)) (foldedCircle (c j) (r j))) x with hf
  have hsupp : Function.support f ⊆ Icc (-(1 / 2)) (1 / 2) := by
    intro x hx
    by_contra hxK
    apply hx
    have : w x = 0 := hwab x fun hx' => hxK (hab hx')
    simp [hf, this]
  show ∫⁻ x, f x ∂(qBoundaryMeasure γ (F2.zU γ X A ω)) =
    ∫⁻ x, f x ∂(qBoundaryMeasure γ (V ω + F2.logSingField (γ ^ 2)))
  rw [← setLIntegral_eq_of_support_subset (μ := qBoundaryMeasure γ (F2.zU γ X A ω)) hsupp,
    ← setLIntegral_eq_of_support_subset
      (μ := qBoundaryMeasure γ (V ω + F2.logSingField (γ ^ 2))) hsupp,
    g3pl4_restrict_eq_of_agree hgZω hgVω.1 hagω]

end R18
end QuantumZipper
