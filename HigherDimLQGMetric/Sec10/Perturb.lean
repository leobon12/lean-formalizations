import HigherDimLQGMetric.Sec10.Pure
import HigherDimLQGMetric.Metric.WeylCompose

/-!
# Algebra of rescaling a continuously perturbed LGF

The field identities here isolate the continuous Weyl weight in Lemma 10.1.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The continuous perturbation after coordinate scaling and sphere-average recentering. -/
def s8a_scaledWeight (f : C(Rd d, ℝ)) (r : ℝ) : C(Rd d, ℝ) :=
  f.comp (affinePt r 0) - ContinuousMap.const (Rd d) (sphereAvg (ofCont f) r 0)

/-- The sphere mean of a globally bounded continuous function obeys the same bound. -/
theorem s8a_abs_sphereAvg_ofCont_le_ae (hd : 1 ≤ d) (f : C(Rd d, ℝ)) (r M : ℝ)
    (hM : ∀ᵐ u ∂(unitSphereProb d), |f (r • u)| ≤ M) :
    |sphereAvg (ofCont f) r 0| ≤ M := by
  have := isProbabilityMeasure_unitSphereProb hd
  have hi : Integrable (fun u : Rd d => f (r • u)) (unitSphereProb d) :=
    integrable_unitSphereProb_of_continuous (by fun_prop)
  rw [sphereAvg_ofCont]
  simp only [zero_add]
  calc
    |∫ u : Rd d, f (r • u) ∂(unitSphereProb d)| ≤
        ∫ u : Rd d, |f (r • u)| ∂(unitSphereProb d) := abs_integral_le_integral_abs
    _ ≤ ∫ _u : Rd d, M ∂(unitSphereProb d) :=
        integral_mono_ae hi.abs (integrable_const M) hM
    _ = M := by simp

/-- The sphere mean of a globally bounded continuous function obeys the same bound. -/
theorem s8a_abs_sphereAvg_ofCont_le (hd : 1 ≤ d) (f : C(Rd d, ℝ)) (r M : ℝ)
    (hM : ∀ x, |f x| ≤ M) : |sphereAvg (ofCont f) r 0| ≤ M :=
  s8a_abs_sphereAvg_ofCont_le_ae hd f r M (ae_of_all _ fun u => hM (r • u))

/-- A global bound on `f` gives a global bound on its scaled Weyl weight. -/
theorem s8a_abs_scaledWeight_le (hd : 1 ≤ d) (f : C(Rd d, ℝ)) (r M : ℝ)
    (hM : ∀ x, |f x| ≤ M) (x : Rd d) : |s8a_scaledWeight f r x| ≤ 2 * M := by
  simp only [s8a_scaledWeight, ContinuousMap.sub_apply, ContinuousMap.comp_apply,
    ContinuousMap.const_apply]
  calc
    |f (affinePt r 0 x) - sphereAvg (ofCont f) r 0| ≤
        |f (affinePt r 0 x)| + |sphereAvg (ofCont f) r 0| := by
          simpa only [sub_zero, zero_sub, abs_neg] using
            (abs_sub_le (f (affinePt r 0 x)) 0 (sphereAvg (ofCont f) r 0))
    _ ≤ M + M := add_le_add (hM _) (s8a_abs_sphereAvg_ofCont_le hd f r M hM)
    _ = 2 * M := by ring

/-- The pointwise Weyl weight needs only a bound at the point and on the sphere. -/
theorem s8a_abs_scaledWeight_le_of_ae (hd : 1 ≤ d) (f : C(Rd d, ℝ))
    (r M : ℝ) (x : Rd d) (hx : |f (r • x)| ≤ M)
    (hs : ∀ᵐ u ∂(unitSphereProb d), |f (r • u)| ≤ M) :
    |s8a_scaledWeight f r x| ≤ 2 * M := by
  simp only [s8a_scaledWeight, ContinuousMap.sub_apply, ContinuousMap.comp_apply,
    ContinuousMap.const_apply, affinePt, ContinuousMap.coe_mk, add_zero]
  calc
    |f (r • x) - sphereAvg (ofCont f) r 0| ≤
        |f (r • x)| + |sphereAvg (ofCont f) r 0| := by
          simpa only [sub_zero, zero_sub, abs_neg] using
            (abs_sub_le (f (r • x)) 0 (sphereAvg (ofCont f) r 0))
    _ ≤ M + M := add_le_add hx (s8a_abs_sphereAvg_ofCont_le_ae hd f r M hs)
    _ = 2 * M := by ring

/-- Measurable supremum of the absolute value of a continuous function on a fixed dense set.
For bounded functions it is the global supremum. -/
def s8a_supAbs (f : C(Rd d, ℝ)) : ℝ :=
  (⨆ n : ℕ, ENNReal.ofReal |f (TopologicalSpace.denseSeq (Rd d) n)|).toReal

theorem s8a_measurable_supAbs {Ω : Type} [MeasurableSpace Ω]
    {f : Ω → C(Rd d, ℝ)} (hf : Measurable f) :
    Measurable (fun ω => s8a_supAbs (f ω)) :=
  ENNReal.measurable_toReal.comp (Measurable.iSup fun n =>
    (continuous_abs.measurable.comp
      ((continuous_eval_const (TopologicalSpace.denseSeq (Rd d) n)).measurable.comp hf)).ennreal_ofReal)

theorem s8a_abs_le_supAbs {f : C(Rd d, ℝ)} {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) (x : Rd d) : |f x| ≤ s8a_supAbs f := by
  have hfin : (⨆ n : ℕ,
      ENNReal.ofReal |f (TopologicalSpace.denseSeq (Rd d) n)|) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (iSup_le fun n => ENNReal.ofReal_le_ofReal (hM _))
  have hseq : ∀ n, |f (TopologicalSpace.denseSeq (Rd d) n)| ≤ s8a_supAbs f := by
    intro n
    unfold s8a_supAbs
    rw [← ENNReal.ofReal_le_iff_le_toReal hfin]
    exact le_iSup (fun n : ℕ =>
      ENNReal.ofReal |f (TopologicalSpace.denseSeq (Rd d) n)|) n
  exact (TopologicalSpace.denseRange_denseSeq (Rd d)).induction_on x
    (isClosed_le (continuous_abs.comp f.continuous) continuous_const) hseq

/-- Rescaling and sphere recentering distribute over a continuous perturbation. -/
private theorem affinePerturb_eq (g : DistRd d) (f : C(Rd d, ℝ))
    {r : ℝ} (hr : 0 < r) (Q : ℝ) :
    addConst (affineComp r 0 (addFun g f)) (Q * Real.log r) =
      addFun (addConst (affineComp r 0 g) (-sphereAvg g r 0))
        (f.comp (affinePt r 0) +
          ContinuousMap.const (Rd d) (sphereAvg g r 0 + Q * Real.log r)) := by
  rw [affineComp_addFun hr]
  rw [addConst_addFun, addFun_addConst, addConst_addFun]
  congr 1
  ext x
  simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
  ring

/-- The normalized metric of `h + f` is the Weyl transform of the rescaled normalized LGF
with weight `f(r·) - f_r(0)`. -/
theorem IsStrongExpMetric.ae_normalizedAtScale_perturb
    {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} (hd : 2 ≤ d)
    (hD : IsStrongExpMetric d ξ Q D) (hh : IsWholeSpaceLGF h P)
    {f : Ω → C(Rd d, ℝ)} (hf : Measurable f) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ u v : Rd d,
      ENNReal.ofReal
        (normalizedAtScale ξ D (fun s => s ^ (ξ * Q)) (addFun (h ω) (f ω)) r (u, v)) =
        weylScale ξ (s8a_scaledWeight (f ω) r) (D (s8a_pureRescaled h r ω)) u v := by
  let X : Ω → DistRd d := fun ω => addFun (h ω) (f ω)
  let g := s8a_pureRescaled h r
  have hX : IsLGFPlusCont X P := hh.isLGFPlusCont.addFun hf
  have hg : IsWholeSpaceLGF g P := s8a_pureRescaled_isLGF hh hr
  filter_upwards [hD.coord P X hX r hr 0, hD.weyl P g hg.isLGFPlusCont,
    hh.ae_exists_tendsto_sphereAvgSeq hd hr 0] with ω hc hw hconv u v
  let a := sphereAvg (h ω) r 0
  let b := sphereAvg (ofCont (f ω)) r 0
  let c := a + Q * Real.log r
  let F := (f ω).comp (affinePt r 0)
  have hs : sphereAvg (X ω) r 0 = a + b := by
    change sphereAvg (addFun (h ω) (f ω)) r 0 = _
    rw [sphereAvg_addFun_of_tendsto (tendsto_sphereAvgSeq_sphereAvg hconv)]
    exact congrArg (a + ·) (sphereAvg_ofCont (f ω) r 0).symm
  have he : addFun (g ω) (F + ContinuousMap.const (Rd d) c) =
      addConst (affineComp r 0 (X ω)) (Q * Real.log r) := by
    exact (affinePerturb_eq (h ω) (f ω) hr Q).symm
  have hc' := hc u v
  simp only [X, add_zero] at hc'
  have hw' := hw (F + ContinuousMap.const (Rd d) c) u v
  rw [he] at hw'
  have hweight : s8a_scaledWeight (f ω) r = F + ContinuousMap.const (Rd d) (-b) := by
    ext x
    simp only [s8a_scaledWeight, ContinuousMap.sub_apply, ContinuousMap.add_apply,
      ContinuousMap.const_apply]
    ring
  rw [hweight, weylScale_add_const]
  have hpow : 0 ≤ (r ^ (ξ * Q))⁻¹ * Real.exp (-ξ * (a + b)) := by
    positivity
  have hfactor : (r ^ (ξ * Q))⁻¹ * Real.exp (-ξ * (a + b)) *
      Real.exp (ξ * c) = Real.exp (ξ * -b) := by
    rw [Real.rpow_def_of_pos hr, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]
    rw [show -(Real.log r * (ξ * Q)) + -ξ * (a + b) + ξ * c = ξ * -b by
      dsimp [c]; ring]
  simp only [normalizedAtScale, ContinuousMap.smul_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, smul_eq_mul] at *
  rw [hs, hc', ENNReal.ofReal_mul hpow]
  dsimp only [X, g] at hw'
  rw [← hw', weylScale_add_const]
  rw [← mul_assoc, ← ENNReal.ofReal_mul hpow, hfactor]

/-- A bounded perturbation gives a scale-independent comparison with the pure metric.
The metric bounds are asserted separately for each scale, as in ruling M15(ii). -/
theorem IsStrongExpMetric.ae_normalizedAtScale_bdd_compare
    {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} (hd : 2 ≤ d) (hξ : 0 < ξ)
    (hD : IsStrongExpMetric d ξ Q D) (hh : IsWholeSpaceLGF h P)
    {f : Ω → C(Rd d, ℝ)} (hf : Measurable f)
    (M : Ω → ℝ) (hM : ∀ ω x, |f ω x| ≤ M ω)
    {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ u v : Rd d,
      Real.exp (-ξ * (2 * M ω)) * (D (s8a_pureRescaled h r ω)).1 (u, v) ≤
        normalizedAtScale ξ D (fun s => s ^ (ξ * Q))
          (addFun (h ω) (f ω)) r (u, v) ∧
      normalizedAtScale ξ D (fun s => s ^ (ξ * Q))
          (addFun (h ω) (f ω)) r (u, v) ≤
        Real.exp (ξ * (2 * M ω)) * (D (s8a_pureRescaled h r ω)).1 (u, v) := by
  have hg := s8a_pureRescaled_isLGF hh hr
  filter_upwards [hD.ae_normalizedAtScale_perturb hd hh hf hr,
    hD.length P (s8a_pureRescaled h r) hg.isLGFPlusCont] with ω he hlen u v
  let E := D (s8a_pureRescaled h r ω)
  let F := s8a_scaledWeight (f ω) r
  have hpoint : ∀ x, |F x| ≤ 2 * M ω := fun x =>
    s8a_abs_scaledWeight_le (show 1 ≤ d by omega) (f ω) r (M ω) (hM ω) x
  have hleft : ∀ x, -ξ * (2 * M ω) ≤ ξ * F x := by
    intro x
    have h := (abs_le.mp (hpoint x)).1
    nlinarith
  have hright : ∀ x, ξ * F x ≤ ξ * (2 * M ω) := by
    intro x
    have h := (abs_le.mp (hpoint x)).2
    nlinarith
  obtain ⟨hlo, hup⟩ := weylScale_mem_Icc_of_isLength
    (D := E) (z := u) (w := v) hlen hleft hright
  rw [← he] at hlo hup
  have hnonneg : 0 ≤ normalizedAtScale ξ D (fun s => s ^ (ξ * Q))
      (addFun (h ω) (f ω)) r (u, v) := by
    simp only [normalizedAtScale, ContinuousMap.smul_apply, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, smul_eq_mul]
    exact mul_nonneg (by positivity) ((D (addFun (h ω) (f ω))).nonneg _ _)
  exact ⟨(ENNReal.ofReal_le_ofReal_iff hnonneg).1 hlo,
    (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (Real.exp_pos _).le (E.nonneg u v))).1 hup⟩

end HigherDimLQGMetric
