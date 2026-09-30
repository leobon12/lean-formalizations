import QuantumZipper.Proofs.Zipper.B5VHccMeas
import QuantumZipper.Proofs.Zipper.E5Palm2Zeta
import QuantumZipper.Proofs.Zipper.E1TransferM4Live
import QuantumZipper.Proofs.Zipper.SWCoreB7dAw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7d (3): path-space proxies for the window flows and the liveness guard

On the path space `C([0,T'], ℝ)` (the shifted Brownian path after the anchor), with the driver
`Wof κ T' e` and its reversal `V_e = vrev (Wof κ T' e) T' = Wof 1 T' (revC e)`:

* `revC`, `Wof_revC`: the reversed path as a continuous function of `e`;
* `FmR`, `measurable_FmR`, `FmR_eq`: the real flow `realRevMap V_e σ x` (at every intermediate
  time `σ ≤ T'`) read through the tamed flows `revZ`, a measurable function of `e`, equal to the
  real flow for live `x < 0`;
* `measurable_hitGuard`: `e ↦ realHitTime V_e x` is measurable (`x < 0`).

Mirrors `B5.Fm` (`B5VHccMeas.lean`) and `E5.measurable_realHitTime_drive_of`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace QuantumZipper
namespace SWCore

open CharFun Collision

variable {T' : ℝ} (hT' : 0 ≤ T')

/-- The reversed path `r ↦ √κ (e (T' − r) − e T')`. -/
def revC (κ : ℝ) (e : C(Icc (0 : ℝ) T', ℝ)) : C(Icc (0 : ℝ) T', ℝ) :=
  ⟨fun r => Real.sqrt κ * (e (projIcc 0 T' hT' (T' - r)) - e ⟨T', hT', le_rfl⟩), by
    refine continuous_const.mul (Continuous.sub ?_ continuous_const)
    exact e.continuous.comp (continuous_projIcc.comp (continuous_const.sub continuous_subtype_val))⟩

theorem Wof_revC (κ : ℝ) (e : C(Icc (0 : ℝ) T', ℝ)) :
    Wof 1 T' hT' (revC hT' κ e) = B2.vrev (Wof κ T' hT' e) T' := by
  funext r
  simp only [Wof, revC, ContinuousMap.coe_mk, Real.sqrt_one, one_mul, B2.vrev]
  have h1 : projIcc 0 T' hT' (T' - (projIcc 0 T' hT' r : ℝ)) =
      projIcc 0 T' hT' (T' - min (max r 0) T') := by
    congr 1
    rw [coe_projIcc]
    congr 1
    simp only [max_def, min_def]
    split_ifs <;> linarith
  have h2 : projIcc 0 T' hT' T' = ⟨T', hT', le_rfl⟩ := projIcc_right _
  rw [h1, h2]
  ring

theorem continuous_revC (κ : ℝ) : Continuous (revC hT' κ) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  have hg : Continuous fun r : Icc (0 : ℝ) T' => projIcc 0 T' hT' (T' - r) :=
    continuous_projIcc.comp (continuous_const.sub continuous_subtype_val)
  have := (continuous_const.mul ((continuous_eval.comp
    (continuous_fst.prodMk (hg.comp continuous_snd))).sub
    (continuous_eval_const (⟨T', hT', le_rfl⟩ : Icc (0 : ℝ) T')
      |>.comp continuous_fst)) : Continuous fun p : C(Icc (0 : ℝ) T', ℝ) × Icc (0 : ℝ) T' =>
        Real.sqrt κ * (p.1 (projIcc 0 T' hT' (T' - p.2)) - p.1 ⟨T', hT', le_rfl⟩))
  exact this

/-- The real flow at time `σ` of the reversed driver, read through the tamed flows. -/
def FmR (κ σ x : ℝ) (e : C(Icc (0 : ℝ) T', ℝ)) : ℝ :=
  limUnder atTop fun n : ℕ => (revZ (Wof 1 T' hT' (revC hT' κ e)) (1 / ((n : ℝ) + 1)) x σ).re

theorem measurable_FmR (κ : ℝ) {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) T') (x : ℝ) :
    Measurable (FmR hT' κ σ x) := by
  unfold FmR
  exact (StronglyMeasurable.limUnder fun n => (Complex.continuous_re.comp
    ((E1.M4.continuous_revZ_Wof hT' (by positivity) (x : ℂ) hσ).comp
      (continuous_revC hT' κ))).measurable.stronglyMeasurable).measurable

theorem FmR_eq (κ : ℝ) {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) T') {x : ℝ}
    (e : C(Icc (0 : ℝ) T', ℝ)) (hx : E1.IsLive (B2.vrev (Wof κ T' hT' e) T') σ x) (hx0 : x < 0) :
    FmR hT' κ σ x e = realRevMap (B2.vrev (Wof κ T' hT' e) T') σ x := by
  set W := Wof 1 T' hT' (revC hT' κ e) with hWdef
  have hWe : W = B2.vrev (Wof κ T' hT' e) T' := Wof_revC hT' κ e
  have hW : Continuous W := continuous_Wof 1 T' hT' _
  rw [← hWe] at hx ⊢
  have hW0 : W 0 = 0 := by rw [hWe]; exact B2.vrev_zero hT'
  obtain ⟨u, hu⟩ := (E1.isLive_iff_exists hW hσ.1).1 hx
  obtain ⟨c, hc, K, hcK⟩ := exists_bounds_isRealRevSol hu hσ.1 (by rw [hW0]; exact hx0)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hc
  have hev : ∀ n ≥ N, (revZ W (1 / ((n : ℝ) + 1)) x σ).re = u σ := by
    intro n hn
    have hle : 1 / ((n : ℝ) + 1) ≤ c := (Nat.one_div_le_one_div hn).trans hN.le
    rw [revZ_eq_of_isRealRevSol hW (by positivity) hu (fun r hr => hle.trans (hcK r hr).1) σ
      ⟨hσ.1, le_rfl⟩, Complex.ofReal_re]
  unfold FmR
  rw [← hWdef, RealLine.realRevMap_eq hW hu hσ.1 le_rfl]
  exact (tendsto_atTop_of_eventually_const hev).limUnder_eq

/-- The coordinate process of the reversed path (for the hitting-time measurability). -/
def revProc (κ : ℝ) (r : ℝ≥0) (e : C(Icc (0 : ℝ) T', ℝ)) : ℝ :=
  revC hT' κ e (projIcc 0 T' hT' r)

theorem drive_revProc (κ : ℝ) (e : C(Icc (0 : ℝ) T', ℝ)) :
    drive 1 (revProc hT' κ) e = B2.vrev (Wof κ T' hT' e) T' := by
  rw [← Wof_revC hT' κ e]
  funext t
  simp only [drive, revProc, Wof, Real.sqrt_one, one_mul]
  rcases le_or_gt 0 t with ht | ht
  · rw [Real.coe_toNNReal t ht]
  · rw [Real.toNNReal_of_nonpos ht.le, NNReal.coe_zero, projIcc_of_le_left hT' ht.le,
      projIcc_left]

/-- **The hitting times of the reversed driver are measurable in the path.** -/
theorem measurable_hitGuard (κ : ℝ) {x : ℝ} (hx : x < 0) :
    Measurable fun e : C(Icc (0 : ℝ) T', ℝ) => realHitTime (B2.vrev (Wof κ T' hT' e) T') x := by
  have hm : ∀ r, Measurable (revProc hT' κ r) := fun r =>
    ((continuous_eval_const _).comp (continuous_revC hT' κ)).measurable
  have hc : ∀ e, Continuous fun t => revProc hT' κ t e := fun e =>
    (revC hT' κ e).continuous.comp (continuous_projIcc.comp NNReal.continuous_coe)
  have h0 : ∀ e, x < drive 1 (revProc hT' κ) e 0 := fun e => by
    rw [drive_revProc]; rw [B2.vrev_zero hT']; exact hx
  have := E5.measurable_realHitTime_drive_of hm hc 1 h0
  simpa only [drive_revProc] using this

end SWCore
end QuantumZipper
