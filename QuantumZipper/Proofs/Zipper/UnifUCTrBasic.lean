import QuantumZipper.Proofs.Zipper.UnifRC3Split
import QuantumZipper.Proofs.Zipper.MeasUnzipFlow

/-!
# UNIF-RC3-TR (1/2): a jointly measurable proxy for `PhiW`

Task UNIF-RC3-TR (decision D33): the transfer `FixedUCStmt ⇒ UnifUCStmt`, i.e. from a fixed
Hölder driver to the Brownian driver by conditioning on the path. As in `RegContRandom`
(`RegCont.PsiKm` for `PsiK`) the event that carries the almost-sure statement must be
measurable in the *pair* (path, field), so the regularized values `PhiW` of a fixed driver
`Wof κ T hT f` are rewritten here as an integral over the circle parametrization `θ ↦
foldH (circleMap c r θ)` of the folded circle. Then every measure occurring in the expression
is the *fixed* measure `circLeb = (2π)⁻¹ • Leb|[0,2π)`, all the dependence on the path and the
field sits in the integrand (`flowJ`, `logJ`, `avgReg`), and the whole composite is jointly
measurable (`measurable_PWm`).

The agreement of `PWm` with `PhiW` along a good path is proved in `UnifUCTr.lean`.

Sources: the conditioning/transfer device is that of `RegContRandom` / `CharFun.ae_indep`
(Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1; Revuz–Yor, 3rd ed., Ch. I,
Thm (2.1)); the circle parametrization is the definition of `circleUnif` (own bookkeeping).
-/

noncomputable section

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open CharFun TwoPoint RegCont MeasUnzip

variable {T : ℝ} (hT : 0 ≤ T)

/-! ## The circle parametrization of the folded circle -/

/-- `(2π)⁻¹ • Leb|[0,2π)`: the source measure of `circleUnif`. -/
def circLeb : Measure ℝ := (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Set.Ico 0 (2 * Real.pi))

instance instIsProbabilityMeasureCircLeb : IsProbabilityMeasure circLeb := by
  constructor
  rw [circLeb, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Real.volume_Ico, sub_zero]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 (by positivity)).ne' ENNReal.ofReal_ne_top

theorem circleUnif_eq_map_circLeb (c : ℂ) (r : ℝ) :
    circleUnif c r = circLeb.map (circleMap c r) := by
  rw [circleUnif, circLeb, Measure.map_smul]
  exact (measurable_circleMap c r).aemeasurable

theorem meas_circleMap_joint (r : ℝ) : Measurable fun q : ℂ × ℝ => circleMap q.1 r q.2 := by
  have h : (fun q : ℂ × ℝ => circleMap q.1 r q.2) =
      fun q => q.1 + (r : ℂ) * Complex.exp ((q.2 : ℂ) * Complex.I) := rfl
  rw [h]
  exact (continuous_fst.add (continuous_const.mul (Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)))).measurable

theorem measurable_dyadicRoundC_tr (n : ℕ) : Measurable (dyadicRoundC n) := by
  have h : (fun z : ℂ => dyadicRoundC n z) =
      fun z => (dyadicRound n z.re : ℂ) + (dyadicRound n z.im : ℂ) * Complex.I := by
    funext z
    unfold dyadicRoundC
    exact Complex.mk_eq_add_mul_I _ _
  rw [show dyadicRoundC n = fun z : ℂ =>
    (dyadicRound n z.re : ℂ) + (dyadicRound n z.im : ℂ) * Complex.I from h]
  unfold dyadicRound
  fun_prop

/-- **Folded circle as a parametrized integral.** -/
theorem integral_foldedCircle_eq (F : ℂ → ℝ) (hF : Measurable F) (c : ℂ) (r : ℝ) :
    ∫ w, F w ∂foldedCircle c r = ∫ θ, F (foldH (circleMap c r θ)) ∂circLeb := by
  rw [foldedCircle, circleUnif_eq_map_circLeb c r,
    Measure.map_map measurable_foldH (measurable_circleMap c r)]
  exact integral_map (measurable_foldH.comp (measurable_circleMap c r)).aemeasurable
    hF.aestronglyMeasurable

/-- The same for a folded circle pushed forward by a measurable map. -/
theorem integral_map_foldedCircle_eq (F : ℂ → ℝ) (hF : Measurable F) {R : ℂ → ℂ}
    (hR : Measurable R) (c : ℂ) (r : ℝ) :
    ∫ z, F z ∂(foldedCircle c r).map R = ∫ θ, F (R (foldH (circleMap c r θ))) ∂circLeb := by
  exact (integral_map hR.aemeasurable hF.aestronglyMeasurable).trans
    (integral_foldedCircle_eq (fun w => F (R w)) (hF.comp hR) c r)

/-- **Joint measurability in the centre**: for a jointly measurable integrand, the folded-circle
average is measurable in the centre. -/
theorem measurable_integral_foldedCircle {α : Type*} [MeasurableSpace α] {G : α × ℂ → ℝ}
    (hG : Measurable G) (r : ℝ) :
    Measurable fun p : α × ℂ => ∫ w, G (p.1, w) ∂foldedCircle p.2 r := by
  have hm : Measurable fun q : (α × ℂ) × ℝ => G (q.1.1, foldH (circleMap q.1.2 r q.2)) :=
    hG.comp ((measurable_fst.comp measurable_fst).prodMk (measurable_foldH.comp
      ((meas_circleMap_joint r).comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))))
  rw [show (fun p : α × ℂ => ∫ w, G (p.1, w) ∂foldedCircle p.2 r) =
      fun p : α × ℂ => ∫ θ, G (p.1, foldH (circleMap p.2 r θ)) ∂circLeb from
    funext fun p => integral_foldedCircle_eq (fun w => G (p.1, w))
      (hG.comp (measurable_const.prodMk measurable_id)) p.2 r]
  exact (StronglyMeasurable.integral_prod_right' hm.stronglyMeasurable).measurable

/-! ## The jointly measurable proxy of `PhiW` -/

variable {κ γ : ℝ}

/-- The raw value of the unzipped field at the folded circle `foldedCircle z (radius j)`, with
the unzipping itself written through the jointly measurable `flowJ`, `logJ`. -/
def RawQ (κ γ : ℝ) (u : ℝ) (j : ℕ) (q : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℂ) : ℝ :=
  unzRawJ hT γ κ (foldedCircle q.2 (radius j)) ((q.1.1, ofFun (h0rev κ) + q.1.2), u)

theorem measurable_RawQ (κ γ : ℝ) (u : ℝ) (j : ℕ) : Measurable (RawQ hT κ γ u j) := by
  have hG : ∀ k : ℕ, Measurable fun z : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℂ =>
      avgReg (ofFun (h0rev κ) + z.1.2) k (flowJ hT κ (z.1.1, (u, z.2))) := by
    intro k
    refine (measurable_avgReg k).comp ((measurable_const.add
      (measurable_snd.comp measurable_fst)).prodMk ?_)
    exact (measurable_flowJ hT κ).comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_const.prodMk measurable_snd))
  have hL : Measurable fun z : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℂ =>
      logJ hT κ (z.1.1, (u, z.2)) :=
    (measurable_logJ hT κ).comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_const.prodMk measurable_snd))
  rw [show RawQ hT κ γ u j = fun q : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℂ =>
      limUnder atTop (fun k => ∫ w, avgReg (ofFun (h0rev κ) + q.1.2) k
          (flowJ hT κ (q.1.1, (u, w))) ∂foldedCircle q.2 (radius j)) +
        Qc γ * ∫ w, logJ hT κ (q.1.1, (u, w)) ∂foldedCircle q.2 (radius j) from rfl]
  refine ((StronglyMeasurable.limUnder fun k =>
    (measurable_integral_foldedCircle (hG k) (radius j)).stronglyMeasurable).measurable).add
    (((measurable_integral_foldedCircle hL (radius j)).const_mul (Qc γ)))

/-- **The proxy of `avgReg y_u j z`**: the regularized folded-circle average of the unzipped
field, as a function of `(path, field, point)`. -/
def AvgQ (κ γ : ℝ) (u : ℝ) (j : ℕ) (q : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℂ) : ℝ :=
  limUnder atTop fun n => RawQ hT κ γ u j (q.1, dyadicRoundC n q.2)

theorem measurable_AvgQ (κ γ : ℝ) (u : ℝ) (j : ℕ) : Measurable (AvgQ hT κ γ u j) :=
  (StronglyMeasurable.limUnder fun n => ((measurable_RawQ hT κ γ u j).comp
    (measurable_id.fst.prodMk ((measurable_dyadicRoundC_tr n).comp measurable_id.snd))).stronglyMeasurable).measurable

/-- The reversal of the path `f` at time `u + s`, truncated to `[0, s]`: the path whose driver
`Wof κ s hs` is the reversed driver `vrev (Wof κ T hT f) (u+s)` on `[0,s]`. -/
def revPathUS (u s : ℝ) (_huS : 0 ≤ u + s) (f : C(Icc (0 : ℝ) T, ℝ)) : C(Icc (0 : ℝ) s, ℝ) :=
  ⟨fun r => f (projIcc 0 T hT (u + s - r.1)) - f (projIcc 0 T hT (u + s)),
    (f.continuous.comp (continuous_projIcc.comp (continuous_const.sub continuous_subtype_val))).sub
      continuous_const⟩

theorem measurable_revPathUS (u s : ℝ) (huS : 0 ≤ u + s) : Measurable (revPathUS hT u s huS) :=
  ContinuousMap.measurable_iff_eval.2 fun r =>
    ((continuous_eval_const (projIcc 0 T hT (u + s - (r : ℝ)))).measurable).sub
      ((continuous_eval_const (projIcc 0 T hT (u + s))).measurable)

/-- The reverse map `R_{u,s} = revMap (vrev W (u+s)) s` of the driver `W = Wof κ T hT f`,
written through the jointly measurable reverse flow `Fm` of the time-reversed path (junk `0`
unless `0 ≤ u` and `0 ≤ s`). -/
def Rm (κ : ℝ) (u s : ℝ) (p : C(Icc (0 : ℝ) T, ℝ) × FieldSample) (w : ℂ) : ℂ :=
  if h : 0 ≤ u ∧ 0 ≤ s then Fm κ s h.2 (revPathUS hT u s (add_nonneg h.1 h.2) p.1, w) else 0

theorem measurable_Rm (κ u s : ℝ) :
    Measurable fun q : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℂ => Rm hT κ u s q.1 q.2 := by
  by_cases h : 0 ≤ u ∧ 0 ≤ s
  · rw [show (fun q : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℂ => Rm hT κ u s q.1 q.2) =
        fun q => Fm κ s h.2 (revPathUS hT u s (add_nonneg h.1 h.2) q.1.1, q.2) from by
      funext q; rw [Rm, dite_eq_left h]]
    exact (measurable_Fm κ s h.2).comp (((measurable_revPathUS hT u s _).comp
      (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
  · rw [show (fun q : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℂ => Rm hT κ u s q.1 q.2) =
        fun _ => (0 : ℂ) from by funext q; rw [Rm, dite_eq_right h]]
    exact measurable_const

/-- **The jointly measurable proxy of `PhiW`**: the regularized values of the time-`u` field at
the pushed circle, with the pushed circle written through the circle parametrization. -/
def PWm (κ : ℝ) (d : ℂ) (k j : ℕ) (u s : ℝ)
    (p : C(Icc (0 : ℝ) T, ℝ) × FieldSample) : ℝ :=
  ∫ θ, AvgQ hT κ (Real.sqrt κ) u j
    (p, Rm hT κ u s p (foldH (circleMap d (radius k) θ))) ∂circLeb

set_option maxHeartbeats 1000000 in
-- the `whnf`/`isDefEq` steps here unfold the nested integral proxy; the default budget is not enough
set_option maxHeartbeats 1000000 in
theorem measurable_PWm (κ : ℝ) (d : ℂ) (k j : ℕ) (u s : ℝ) : Measurable (PWm hT κ d k j u s) := by
  have hG : Measurable fun z : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℝ =>
      AvgQ hT κ (Real.sqrt κ) u j (z.1, Rm hT κ u s z.1
        (foldH (circleMap d (radius k) z.2))) :=
    (measurable_AvgQ hT κ (Real.sqrt κ) u j).comp (measurable_id.fst.prodMk
      ((measurable_Rm hT κ u s).comp (measurable_id.fst.prodMk
        (measurable_foldH.comp ((measurable_circleMap d (radius k)).comp measurable_id.snd)))))
  exact (StronglyMeasurable.integral_prod_right' hG.stronglyMeasurable).measurable

end RegUnif
end QuantumZipper
