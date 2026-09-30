import QuantumZipper.Proofs.Thm14.WeldingData
import QuantumZipper.Proofs.Loewner.Algebra
import QuantumZipper.Proofs.Loewner.ReverseHolo

/-!
# Theorem 1.8, node G4: Borel welding data of drivers at a random time

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1). Task
G4-READ2.

A driver at a *random* time `T > 0` is parametrized by a pair `p = (g, T)` with `g` a path on
`[0,1]`: `sclDrv p s = √T · g(s/T)` (Brownian scaling, `LoewnerAlgebra.revMap_scale`). On the
standard Borel space `C([0,1], ℝ) × ℝ` the reverse map at time `T` is jointly measurable
(`measurable_rvS`, via `measurable_uncurry_of_continuous_of_measurable`: continuous in the path,
measurable in the time), and so are the Borel versions `zmS`, `whS` of `0₋` and of the welding
homeomorphism. They agree with `zeroMinus`, `weldingHom` whenever the reverse map has a
Carathéodory extension (`zmS_eq_of_car`, `whS_eq_of_car`).

These are the random-time versions of `Thm14WeldingData.zmSeq`, `whSeq` (same proofs). **Own
elementary argument** (measurability bookkeeping).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

open Thm14WeldingData

/-- A path on `[0,1]` together with a time `T`. -/
abbrev PathT : Type := C(Icc (0 : ℝ) 1, ℝ) × ℝ

/-- The driver at time `T = p.2` built from the path `g = p.1` on `[0,1]`: `s ↦ √T · g(s/T)`. -/
def sclDrv (p : PathT) : ℝ → ℝ := fun s => Real.sqrt p.2 * extIccPath zero_le_one p.1 (s / p.2)

theorem continuous_sclDrv (p : PathT) : Continuous (sclDrv p) :=
  continuous_const.mul ((continuous_extIccPath _ _).comp (continuous_id.div_const _))

/-- The measurable form of the reverse map of `sclDrv p` at time `p.2` (`0` if `p.2 ≤ 0`). -/
def rvS (p : PathT) (z : ℂ) : ℂ :=
  revMap (extIccPath zero_le_one p.1) 1 ((((Real.sqrt p.2)⁻¹ : ℝ) : ℂ) * z) /
    (((Real.sqrt p.2)⁻¹ : ℝ) : ℂ)

theorem revMap_sclDrv {p : PathT} (hT : 0 < p.2) {z : ℂ} (hz : 0 < z.im) :
    revMap (sclDrv p) p.2 z = rvS p z := by
  have hs : 0 < Real.sqrt p.2 := Real.sqrt_pos.2 hT
  have ha : 0 < (Real.sqrt p.2)⁻¹ := inv_pos.2 hs
  have ha2 : ((Real.sqrt p.2)⁻¹) ^ 2 = p.2⁻¹ := by rw [inv_pow, Real.sq_sqrt hT.le]
  have hfun : sclDrv p = fun s =>
      extIccPath zero_le_one p.1 (((Real.sqrt p.2)⁻¹) ^ 2 * s) / (Real.sqrt p.2)⁻¹ := by
    funext s
    show Real.sqrt p.2 * extIccPath zero_le_one p.1 (s / p.2) = _
    rw [ha2, div_inv_eq_mul, div_eq_inv_mul, mul_comm (Real.sqrt p.2)]
  rw [hfun, LoewnerAlgebra.revMap_scale _ (continuous_extIccPath _ _) ha hT.le hz, ha2,
    inv_mul_cancel₀ hT.ne']
  rfl

theorem measurable_rvS {z : ℂ} (hz : 0 < z.im) : Measurable fun p : PathT => rvS p z := by
  let u : C(Icc (0 : ℝ) 1, ℝ) → ℝ → ℂ := fun g T => rvS (g, T) z
  have hcont : ∀ T : ℝ, Continuous fun g => u g T := by
    intro T
    by_cases hT : 0 < T
    · have hw : 0 < ((((Real.sqrt T)⁻¹ : ℝ) : ℂ) * z).im := by
        rw [Complex.im_ofReal_mul]
        exact mul_pos (inv_pos.2 (Real.sqrt_pos.2 hT)) hz
      exact ((continuous_revMap_extIccPath zero_le_one hw).div_const
        ((((Real.sqrt T)⁻¹ : ℝ) : ℂ))).congr fun g => rfl
    · have h0 : Real.sqrt T = 0 := Real.sqrt_eq_zero'.2 (not_lt.1 hT)
      have : (fun g => u g T) = fun _ => 0 := by
        funext g
        simp only [u, rvS, h0, inv_zero, Complex.ofReal_zero, div_zero]
      rw [this]
      exact continuous_const
  have hmeas : ∀ g, Measurable (u g) := by
    intro g
    have hpw : u g = (Ioi (0 : ℝ)).piecewise (u g) (fun _ => 0) := by
      funext T
      by_cases hT : 0 < T
      · simp [piecewise, hT]
      · have h0 : Real.sqrt T = 0 := Real.sqrt_eq_zero'.2 (not_lt.1 hT)
        simp only [piecewise, mem_Ioi, hT, ite_false, u, rvS, h0, inv_zero, Complex.ofReal_zero,
          div_zero]
    rw [hpw]
    refine ContinuousOn.measurable_piecewise ?_ continuousOn_const measurableSet_Ioi
    intro T hT
    have hT' : 0 < T := hT
    have hsc : ContinuousAt (fun T : ℝ => (((Real.sqrt T)⁻¹ : ℝ) : ℂ)) T :=
      Complex.continuous_ofReal.continuousAt.comp
        ((Real.continuous_sqrt.continuousAt).inv₀ (Real.sqrt_pos.2 hT').ne')
    have hw : ((((Real.sqrt T)⁻¹ : ℝ) : ℂ) * z) ∈ H := by
      show 0 < ((((Real.sqrt T)⁻¹ : ℝ) : ℂ) * z).im
      rw [Complex.im_ofReal_mul]
      exact mul_pos (inv_pos.2 (Real.sqrt_pos.2 hT')) hz
    have hd := (differentiableOn_revMap (extIccPath zero_le_one g)
      (continuous_extIccPath _ _) zero_le_one).differentiableAt
      (isOpen_H.mem_nhds hw)
    have hin : ContinuousAt (fun T : ℝ => (((Real.sqrt T)⁻¹ : ℝ) : ℂ) * z) T :=
      hsc.mul continuousAt_const
    have hcomp : ContinuousAt
        (fun T : ℝ => revMap (extIccPath zero_le_one g) 1 ((((Real.sqrt T)⁻¹ : ℝ) : ℂ) * z)) T :=
      ContinuousAt.comp (g := revMap (extIccPath zero_le_one g) 1) hd.continuousAt hin
    refine (ContinuousAt.div hcomp hsc ?_).continuousWithinAt
    exact_mod_cast (inv_pos.2 (Real.sqrt_pos.2 hT')).ne'
  exact measurable_uncurry_of_continuous_of_measurable (u := u) hcont hmeas

/-- Boundary values of `rvS p` read along the heights `1/(n+1)`. -/
def bdryS (p : PathT) (x : ℝ) : ℂ :=
  limUnder atTop fun n : ℕ => rvS p (x + (height n : ℂ) * Complex.I)

theorem measurable_bdryS (x : ℝ) : Measurable fun p => bdryS p x :=
  (StronglyMeasurable.limUnder (l := atTop)
    (f := fun (n : ℕ) (p : PathT) => rvS p (x + (height n : ℂ) * Complex.I))
    fun n => (measurable_rvS (im_add_height x n)).stronglyMeasurable).measurable

theorem bdryS_eq_of_car {p : PathT} (hT : 0 < p.2) {F : ℂ → ℂ}
    (hF : Blueprint.IsCaratheodoryRevExt (sclDrv p) p.2 F) (x : ℝ) : bdryS p x = F x := by
  refine (((tendsto_revMap_of_car hF x).comp tendsto_height).congr fun n => ?_).limUnder_eq
  simp only [Function.comp_apply]
  rw [revMap_sclDrv hT (im_add_height x n)]

/-- Borel version of `0₋` at the random time. -/
def zmS (p : PathT) : ℝ :=
  sSup (((↑) : ℚ → ℝ) '' {q : ℚ | (q : ℝ) < 0 ∧ (bdryS p q).im = 0})

theorem measurable_zmS : Measurable zmS :=
  measurable_sSup_rat _
    (fun q => measurableSet_setOfPred.2 (measurable_const.and (measurableSet_setOfPred.1
      (measurableSet_eq_fun (Complex.measurable_im.comp (measurable_bdryS q))
        measurable_const))))
    (fun _ => ⟨0, by rintro _ ⟨q, hq, rfl⟩; exact hq.1.le⟩)

theorem zmS_eq_of_car {p : PathT} (hT : 0 < p.2) {F : ℂ → ℂ}
    (hF : Blueprint.IsCaratheodoryRevExt (sclDrv p) p.2 F) :
    zmS p = zeroMinus (sclDrv p) p.2 := by
  have hb := zeroPlus_nonneg (sclDrv p) p.2
  have hset : {q : ℚ | (q : ℝ) < 0 ∧ (bdryS p q).im = 0} =
      {q : ℚ | (q : ℝ) < 0 ∧ (q : ℝ) ≤ zeroMinus (sclDrv p) p.2} := by
    ext q
    simp only [mem_ofPred_eq, bdryS_eq_of_car hT hF]
    constructor
    · rintro ⟨hq, h⟩
      refine ⟨hq, ?_⟩
      rcases (hF.2.2.2.2.2.1 q).1 h with h' | h'
      · exact h'
      · linarith
    · rintro ⟨hq, h⟩
      exact ⟨hq, (hF.2.2.2.2.2.1 q).2 (Or.inl h)⟩
  unfold zmS
  rw [hset]
  have ha := WeldingUniqueness.zeroMinus_nonpos (sclDrv p) p.2
  obtain ⟨q₀, hq₀⟩ := exists_rat_lt (zeroMinus (sclDrv p) p.2 - 1)
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt
    ⟨_, q₀, ⟨by linarith, by linarith⟩, rfl⟩ ?_ ?_
  · rintro _ ⟨q, hq, rfl⟩
    exact hq.2
  · intro c hc
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hc
    exact ⟨_, ⟨q, ⟨by linarith, hq2.le⟩, rfl⟩, hq1⟩

/-- Borel version of the welding homeomorphism at the random time. -/
def whS (p : PathT) (x : ℝ) : ℝ :=
  sInf (((↑) : ℚ → ℝ) '' {r : ℚ | 0 ≤ (r : ℝ) ∧ ∀ n : ℕ, ∃ y : ℚ, 0 ≤ (y : ℝ) ∧
    (y : ℝ) ≤ r ∧ ‖bdryS p y - bdryS p x‖ < height n})

theorem measurable_whS (x : ℝ) : Measurable fun p => whS p x :=
  measurable_sInf_rat _
    (fun r => measurableSet_setOfPred.2 (measurable_const.and (Measurable.forall fun n =>
      Measurable.exists fun y => measurable_const.and (measurable_const.and
        (measurableSet_setOfPred.1 (measurableSet_lt
          ((measurable_bdryS y).sub (measurable_bdryS x)).norm measurable_const))))))
    (fun _ => ⟨0, by rintro _ ⟨r, hr, rfl⟩; exact hr.1⟩)

theorem whS_eq_of_car {p : PathT} (hT : 0 < p.2) {F : ℂ → ℂ}
    (hF : Blueprint.IsCaratheodoryRevExt (sclDrv p) p.2 F) {s : ℝ}
    (hs : s ∈ Icc (zeroMinus (sclDrv p) p.2) 0) :
    whS p s = weldingHom (sclDrv p) p.2 s := by
  obtain ⟨hm0, hmF⟩ := weldingHom_mem_of_car hF hs
  unfold whS
  simp only [bdryS_eq_of_car hT hF]
  exact sInf_rat_cond_eq (G := fun y : ℝ => F y) (continuous_car_real hF) (F s) hm0 hmF
    fun y hy hyF => (eq_weldingHom_of_car hF hs hy hyF).ge

end Thm18Asm
end QuantumZipper
