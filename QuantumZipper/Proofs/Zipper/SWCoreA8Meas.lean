import QuantumZipper.Proofs.Zipper.SWCoreA7Fix
import QuantumZipper.Proofs.Zipper.SWCoreA7Fam
import QuantumZipper.Proofs.Zipper.RegContRandom
import QuantumZipper.Proofs.Zipper.JointModRandom
import QuantumZipper.Proofs.LQG.IndepParams

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A8 (1): measurable proxies and the fixed-path fibre for the flow distortion bound

Transfer of `a7_flowErr_fixed`-type information from a fixed driver to the independent Brownian
driver (decision D64, open issue of SWC-A6). The driver is encoded by a continuous path
`f ∈ C([0,T])` through `CharFun.Wof`, and the flow maps by the jointly measurable reverse maps of
the reversed path (`CharFun.Fm`, `CharFun.Dm`, `RegCont.revPath`), exactly as in the D33 / XFLOW-UC
transfers (`RegCont.PsiKm`, `F1.PWf`).

* `a8Phi`, `a8Rd`: measurable proxies of the smoothed pushed pairing
  `∫ avgReg x j d(fc(z,2^{-k}).map f_t⁻¹)` and of the round value
  `evalReg x (fc(f_t⁻¹ z, 2^{-k}|(f_t⁻¹)'(z)|))`;
* `a8Ev`: the countable event (rational times and centres): uniform Cauchy property in `j`
  for all large `k`, and closeness of the smoothed pairing to the round value;
* `a8_fibre`: for every good path, almost surely in the free field, `a8Ev` holds
  (finite-parameter primed core `swcNA2I_primed` for the family `a7Map`).

Own bookkeeping (as `RegCont.UCm`, `F1.UCsetF`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Metric
open scoped Topology NNReal

namespace QuantumZipper
namespace SWCore

open CharFun RegCont

variable (κ : ℝ) {T : ℝ} (hT : 0 ≤ T)

/-- Rational points of `ℂ`. -/
def zQ (z : ℚ × ℚ) : ℂ := ⟨z.1, z.2⟩

/-- Proxy of the smoothed pushed pairing. -/
def a8Phi (j k : ℕ) (s : ℝ) (hs : 0 ≤ s) (z : ℂ) (p : C(Icc (0 : ℝ) T, ℝ) × FieldSample) : ℝ :=
  PsiKm hT κ z (radius k) s hs j p

/-- Proxy of the round value. -/
def a8Rd (k : ℕ) (s : ℝ) (hs : 0 ≤ s) (z : ℂ) (p : C(Icc (0 : ℝ) T, ℝ) × FieldSample) : ℝ :=
  evalReg p.2 (foldedCircle (Fm κ s hs (revPath hT s hs p.1, z))
    (radius k * ‖Dm κ s hs (revPath hT s hs p.1, z)‖))

theorem measurable_a8Phi (j k : ℕ) (s : ℝ) (hs : 0 ≤ s) (z : ℂ) :
    Measurable (a8Phi κ hT j k s hs z) :=
  measurable_PsiKm hT κ z (radius k) s hs j

set_option maxHeartbeats 1000000 in
-- the proxies unfold through `revPath` and `Fm`
theorem measurable_a8Rd (k : ℕ) (s : ℝ) (hs : 0 ≤ s) (z : ℂ) :
    Measurable (a8Rd κ hT k s hs z) := by
  unfold a8Rd
  have hG : Measurable fun p : C(Icc (0 : ℝ) T, ℝ) × FieldSample =>
      (revPath hT s hs p.1, z) := ((measurable_revPath hT s hs).comp measurable_fst).prodMk
        measurable_const
  have h1 : Measurable fun p : C(Icc (0 : ℝ) T, ℝ) × FieldSample =>
      (p.2, (Fm κ s hs (revPath hT s hs p.1, z),
        radius k * ‖Dm κ s hs (revPath hT s hs p.1, z)‖)) :=
    measurable_snd.prodMk (((measurable_Fm κ s hs).comp hG).prodMk
      (measurable_const.mul ((measurable_Dm κ s hs).comp hG).norm))
  exact (IndepParams.measurable_evalReg_fc₂.comp h1 :)

/-- The countable event on `C([0,T]) × FieldSample` for the rectangle `[A,B] × [C,D]`. -/
def a8Ev (A B C D : ℚ) (p : C(Icc (0 : ℝ) T, ℝ) × FieldSample) : Prop :=
  (∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k → ∀ m : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ j' : ℕ, J ≤ j' →
    ∀ q : ℚ, ∀ hq : (q : ℝ) ∈ Icc (0 : ℝ) T, ∀ z : ℚ × ℚ, zQ z ∈ rectC A B C D →
      |a8Phi κ hT j k q hq.1 (zQ z) p - a8Phi κ hT j' k q hq.1 (zQ z) p| ≤ 1 / ((m : ℝ) + 1)) ∧
  ∀ n : ℕ, ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
    ∀ q : ℚ, ∀ hq : (q : ℝ) ∈ Icc (0 : ℝ) T, ∀ z : ℚ × ℚ, zQ z ∈ rectC A B C D →
      |a8Phi κ hT j k q hq.1 (zQ z) p - a8Rd κ hT k q hq.1 (zQ z) p| ≤ 1 / ((n : ℝ) + 1)

theorem measurableSet_a8Ev (A B C D : ℚ) : MeasurableSet {p | a8Ev κ hT A B C D p} := by
  refine measurableSet_setOfPred.2 ?_
  unfold a8Ev
  refine Measurable.and ?_ ?_
  · refine Measurable.exists fun K₀ => Measurable.forall fun k => Measurable.forall fun _ =>
      Measurable.forall fun m => Measurable.exists fun J => Measurable.forall fun j =>
      Measurable.forall fun _ => Measurable.forall fun j' => Measurable.forall fun _ =>
      Measurable.forall fun q => Measurable.forall fun hq => Measurable.forall fun z =>
      Measurable.forall fun _ => ?_
    exact measurableSet_setOfPred.1 (measurableSet_le (continuous_abs.measurable.comp
      ((measurable_a8Phi κ hT _ _ _ _ _).sub (measurable_a8Phi κ hT _ _ _ _ _))) measurable_const)
  · refine Measurable.forall fun n => Measurable.exists fun K => Measurable.forall fun k =>
      Measurable.forall fun _ => Measurable.exists fun J => Measurable.forall fun j =>
      Measurable.forall fun _ => Measurable.forall fun q => Measurable.forall fun hq =>
      Measurable.forall fun z => Measurable.forall fun _ => ?_
    exact measurableSet_setOfPred.1 (measurableSet_le (continuous_abs.measurable.comp
      ((measurable_a8Phi κ hT _ _ _ _ _).sub (measurable_a8Rd κ hT _ _ _ _))) measurable_const)

/-! ## Identification with the flow maps of `Wof f` -/

variable {κ hT}

theorem a8_Fm_eq {f : C(Icc (0 : ℝ) T, ℝ)} (hf0 : Wof κ T hT f 0 = 0) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) {w : ℂ} (hw : w ∈ H) :
    Fm κ s hs.1 (revPath hT s hs.1 f, w) = fwdMapInv (Wof κ T hT f) s w := by
  rw [UnzipInvariance.fwdMapInv_eq_revMap_timeRev _ (continuous_Wof κ T hT f) hf0 hs.1 hw]
  exact ReverseFlow.revMap_congr_drive w (Wof_revPath_eqOn hT κ hs f)

theorem a8_Dm_eq {f : C(Icc (0 : ℝ) T, ℝ)} (hf0 : Wof κ T hT f 0 = 0) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) {w : ℂ} (hw : w ∈ H) :
    Dm κ s hs.1 (revPath hT s hs.1 f, w) = deriv (fwdMapInv (Wof κ T hT f) s) w := by
  rw [Dm_eq κ s hs.1 _ hw]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_H.mem_nhds hw] with u hu
  exact a8_Fm_eq hf0 hs hu

theorem a8Phi_eq {f : C(Icc (0 : ℝ) T, ℝ)} (hf0 : Wof κ T hT f 0 = 0) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) (j k : ℕ) (z : ℂ) (x : FieldSample) :
    a8Phi κ hT j k s hs.1 z (f, x) =
      ∫ u, avgReg x j u ∂((foldedCircle z (radius k)).map (fwdMapInv (Wof κ T hT f) s)) :=
  PsiKm_eq hT κ z (radius_pos k) hs j f hf0 x

theorem a8Rd_eq {f : C(Icc (0 : ℝ) T, ℝ)} (hf0 : Wof κ T hT f 0 = 0) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) (k : ℕ) {z : ℂ} (hz : z ∈ H) (x : FieldSample) :
    a8Rd κ hT k s hs.1 z (f, x) = evalReg x (foldedCircle (fwdMapInv (Wof κ T hT f) s z)
      (radius k * ‖deriv (fwdMapInv (Wof κ T hT f) s) z‖)) := by
  unfold a8Rd
  rw [a8_Fm_eq hf0 hs hz, a8_Dm_eq hf0 hs hz]

end SWCore
end QuantumZipper
