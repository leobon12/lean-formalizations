import QuantumZipper.Proofs.LQG.CoordChangeAvg
import QuantumZipper.Proofs.LQG.BoundaryExistence

/-!
# M4-T4: a jointly measurable version of the comparison semicircles

For the comparison of M4-T4 step 3 we need, jointly measurably in `(t, ω)`, the normalized
field at the semicircle `fc(ψ t, ψ'(t) r)`:

  `wProc X ψ R r t ω = X ω (fc(ψ t, ψ'(t) r)) − X ω (fc(0, R))`  (a.s., for each `t`).

It is built from `evalReg` along the dyadic roundings of `t`; the identification uses the
every-circle regularity of the free field (`ae_isRegularSample`, M4-R3) and the regularization
at boundary semicircles (`ae_evalReg_pc` with `ψ = id`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology ComplexConjugate
open scoped ENNReal NNReal

namespace QuantumZipper
namespace CoordChange

open GaussTK

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The identity map -/

theorem data_id (s : ℝ) : Data id s s 1 1 0 where
  δpos := one_pos
  mpos := one_pos
  diff := fun _ _ => differentiableOn_id
  refl := fun _ _ _ _ => rfl
  d2 := fun _ _ z _ => by
    have : deriv (deriv (id : ℂ → ℂ)) = fun _ => 0 := by
      rw [deriv_id']; funext z; exact deriv_const z 1
    rw [this, norm_zero]
  dre := fun _ _ => by rw [deriv_id]; simp
  dim := fun _ _ => by rw [deriv_id]; simp

theorem r0_id : Data.r0 1 1 0 = 1 / 4 := by
  unfold Data.r0; norm_num

theorem pc_id (s r : ℝ) : pc id s r = foldedCircle (s : ℂ) r := by
  unfold pc; exact Measure.map_id

/-- Regularization at boundary semicircles of radius `≤ 1/4`. -/
theorem ae_evalReg_fc_real {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) (s : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) :
    ∀ᵐ ω ∂P, evalReg (X ω) (foldedCircle (s : ℂ) ρ) = X ω (foldedCircle (s : ℂ) ρ) := by
  have := (data_id s).ae_evalReg_pc hX (t := s) ⟨le_rfl, le_rfl⟩ hρ.le (by rw [r0_id]; exact hρ4)
    (s := s) (r := ρ) hρ (by simp)
  simpa [pc_id] using this

/-! ### The process -/

/-- Raw values at a point `d`: `evalReg` at `fc(ψ d, ψ'(d) r)`, normalized. -/
def wRaw (X : Ω → FieldSample) (ψ : ℂ → ℂ) (R r : ℝ) (d : ℝ) (ω : Ω) : ℝ :=
  evalReg (X ω) (foldedCircle (((ψ d).re : ℝ) : ℂ) ((deriv ψ d).re * r)) -
    X ω (foldedCircle 0 R)

/-- The jointly measurable version. -/
def wProc (X : Ω → FieldSample) (ψ : ℂ → ℂ) (R r : ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  limUnder atTop fun n => wRaw X ψ R r (dyadicRound n t) ω

theorem measurable_wProc {P : Measure Ω} {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    (ψ : ℂ → ℂ) (R r : ℝ) : Measurable (fun p : ℝ × Ω => wProc X ψ R r p.1 p.2) := by
  have hn : ∀ n, Measurable (fun p : ℝ × Ω => wRaw X ψ R r (dyadicRound n p.1) p.2) := by
    intro n
    refine measurable_comp_dyadicRound (fun d => ?_) n
    exact ((measurable_evalReg _).comp (measurable_fieldSample hX)).sub (hX.measurable_coord _)
  unfold wProc
  exact (StronglyMeasurable.limUnder (fun n => (hn n).stronglyMeasurable)).measurable

theorem tendsto_dyadicRound (t : ℝ) : Tendsto (fun n => dyadicRound n t) atTop (𝓝 t) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  rw [Real.norm_eq_abs]
  refine (CircleCont.abs_dyadicRound_sub_le n t).trans (le_of_eq ?_)
  rw [one_div_pow]

namespace Data

variable {ψ : ℂ → ℂ} {a b δ m C : ℝ}

theorem continuousAt_re_psi (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) :
    ContinuousAt (fun d : ℝ => (ψ d).re) t := by
  have hc : ContinuousAt ψ (t : ℂ) :=
    ((h.diff t ht) _ (mem_ball_self (by linarith [h.δpos]))).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self (by linarith [h.δpos]))) |>.continuousAt
  exact Complex.continuous_re.continuousAt.comp (hc.comp Complex.continuous_ofReal.continuousAt)

theorem continuousAt_re_deriv (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) :
    ContinuousAt (fun d : ℝ => (deriv ψ d).re) t := by
  have hc : ContinuousAt (deriv ψ) (t : ℂ) :=
    (((h.diff t ht).deriv isOpen_ball) _ (mem_ball_self (by linarith [h.δpos]))).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self (by linarith [h.δpos]))) |>.continuousAt
  exact Complex.continuous_re.continuousAt.comp (hc.comp Complex.continuous_ofReal.continuousAt)

/-- **Identification of `wProc`** at a fixed point. -/
theorem ae_wProc_eq {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) (R : ℝ)
    {r : ℝ} (hr : 0 < r) (hr4 : (deriv ψ t).re * r ≤ 1 / 4) :
    ∀ᵐ ω ∂P, wProc X ψ R r t ω =
      fcPairVal X ((((ψ t).re : ℝ) : ℂ), (deriv ψ t).re * r, 0, R) ω := by
  have hρ : 0 < (deriv ψ t).re * r := mul_pos (h.deriv_re_pos ht) hr
  filter_upwards [RegSample.ae_isRegularSample hX, ae_evalReg_fc_real hX (ψ t).re hρ hr4]
    with ω hreg hev
  obtain ⟨F, hF⟩ := hreg
  set p : ℝ → ℂ × ℝ := fun d => ((((ψ d).re : ℝ) : ℂ), (deriv ψ d).re * r)
  have hpc : ContinuousAt p t :=
    ((Complex.continuous_ofReal.continuousAt.comp (h.continuousAt_re_psi ht))).prodMk
      ((h.continuousAt_re_deriv ht).mul continuousAt_const)
  have hpS : ∀ᶠ d in 𝓝 t, p d ∈ Hbar ×ˢ Ioi (0 : ℝ) := by
    have hc : ContinuousAt (fun d : ℝ => (deriv ψ (d : ℂ)).re * r) t :=
      (h.continuousAt_re_deriv ht).mul continuousAt_const
    have h1 : ∀ᶠ d : ℝ in 𝓝 t, 0 < (deriv ψ (d : ℂ)).re * r := hc.eventually (lt_mem_nhds hρ)
    filter_upwards [h1] with d hd
    exact ⟨show (0 : ℝ) ≤ (((ψ d).re : ℝ) : ℂ).im by simp, hd⟩
  have hmem : p t ∈ Hbar ×ˢ Ioi (0 : ℝ) := hpS.self_of_nhds
  have hcw : ContinuousWithinAt F (Hbar ×ˢ Ioi 0) (p t) := hF.1 (p t) hmem
  have htend : Tendsto p (𝓝 t) (𝓝[Hbar ×ˢ Ioi 0] (p t)) :=
    tendsto_nhdsWithin_iff.2 ⟨hpc.tendsto, hpS⟩
  have hlim : Tendsto (fun n => F (p (dyadicRound n t)) - X ω (foldedCircle 0 R)) atTop
      (𝓝 (F (p t) - X ω (foldedCircle 0 R))) :=
    ((hcw.tendsto.comp htend).comp (tendsto_dyadicRound t)).sub_const _
  have hev' : ∀ᶠ n in atTop, wRaw X ψ R r (dyadicRound n t) ω =
      F (p (dyadicRound n t)) - X ω (foldedCircle 0 R) := by
    filter_upwards [(tendsto_dyadicRound t).eventually hpS] with n hn
    have e := hF.evalReg_fc_of_mem hn.1 hn.2
    unfold wRaw
    exact congrArg (· - X ω (foldedCircle 0 R)) e
  unfold wProc
  rw [(hlim.congr' (hev'.mono fun n hn => hn.symm)).limUnder_eq]
  have e1 : F (p t) = evalReg (X ω) (foldedCircle (p t).1 (p t).2) :=
    (hF.evalReg_fc_of_mem hmem.1 hmem.2).symm
  rw [e1]
  show evalReg (X ω) (foldedCircle ((((ψ t).re : ℝ) : ℂ)) ((deriv ψ t).re * r)) - _ = _
  rw [hev]
  rfl

end Data

end CoordChange
end QuantumZipper
