import QuantumZipper.Proofs.Zipper.E1TransferMeas
import QuantumZipper.Proofs.Zipper.Collision
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# E1-TR, M4: joint measurability of the live negative set in (driver path, point)

`handoff/E1-TR.md`, step M4. Context: Sheffield, *Conformal weldings of random surfaces*,
arXiv:1012.4797, §5.2 (the zipped-coordinate data are functions of the stopped driver).

For a path `w ∈ C([0,t], ℝ)` with `w 0 = 0` and the driver `W = Wof 1 t ht w`, the set
`liveNeg W t` is open (`E1.isOpen_liveNeg`) and downward closed (`Collision.realHitTime_anti`,
since `W 0 = 0`), so `x ∈ liveNeg W t ↔ ∃ q : ℚ, x < q ∧ q ∈ liveNeg W t`. For a fixed real
`q < 0`, liveness is `∃ n, ∀ s ∈ ℚ ∩ [0,t], 1/(n+1) ≤ −Re revZ W (1/(n+1)) q s`
(`E1.isLive_iff_exists`, `Collision.exists_isRealRevSol_iff`), and `w ↦ revZ W ε q s` is
continuous in the sup norm by Grönwall (mathlib `dist_le_of_approx_trajectories_ODE`).

We prove the version restricted to paths starting at `0` (the Brownian driver is a.s. `0` at
time `0`); for `W 0 < x < 0` liveness is not monotone in `x` and is not needed.

Source: **own elementary proof** (continuous dependence of an ODE on its driver, and a
countable description of an open, downward closed set).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E1
namespace M4

open Collision RealLine

/-- Grönwall comparison of the tamed flows of two drivers that are `d`-close on `[0,T]`. -/
theorem dist_revUnc_le {W W' : ℝ → ℝ} (hW : Continuous W) (hW' : Continuous W') {ε : ℝ}
    (hε : 0 < ε) {T d : ℝ} (hT : 0 ≤ T) (hd : ∀ r ∈ Icc (0 : ℝ) T, |W r - W' r| ≤ d)
    (x : ℂ) : ∀ s ∈ Icc (0 : ℝ) T, dist (revUnc W ε x s) (revUnc W' ε x s) ≤
      gronwallBound 0 (Real.toNNReal (2 / ε ^ 2)) (0 + Real.toNNReal (2 / ε ^ 2) * d) (s - 0) := by
  have hIci : ∀ (V : ℝ → ℝ), Continuous V → ∀ t ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt (revUnc V ε x) (revField ε (revZ V ε x t)) (Ici t) t := by
    intro V hV t ht
    exact (revUnc_hasDerivWithinAt hV hε hT x t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1))
  have hcont : ∀ (V : ℝ → ℝ), Continuous V → ContinuousOn (revUnc V ε x) (Icc 0 T) :=
    fun V hV t ht => (revUnc_hasDerivWithinAt hV hε hT x t ht).continuousWithinAt
  have hfb : ∀ r ∈ Ico (0 : ℝ) T, dist (revField ε (revZ W ε x r))
      ((fun r y => revField ε (y - (W r : ℂ))) r (revUnc W ε x r)) ≤ 0 := by
    intro r _
    rw [dist_le_zero]
    rfl
  have hgb : ∀ r ∈ Ico (0 : ℝ) T, dist (revField ε (revZ W' ε x r))
      ((fun r y => revField ε (y - (W r : ℂ))) r (revUnc W' ε x r)) ≤
        (Real.toNNReal (2 / ε ^ 2) : ℝ) * d := by
    intro r hr
    have hr' : r ∈ Icc (0 : ℝ) T := Ico_subset_Icc_self hr
    have hL := (revField_lipschitz hε).dist_le_mul (revZ W' ε x r) (revUnc W' ε x r - W r)
    refine hL.trans (mul_le_mul_of_nonneg_left ?_ (NNReal.coe_nonneg _))
    have e : dist (revZ W' ε x r) (revUnc W' ε x r - (W r : ℂ)) = |W r - W' r| := by
      rw [revZ, dist_sub_left, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_sub_comm]
    rw [e]
    exact hd r hr'
  have ha : dist (revUnc W ε x 0) (revUnc W' ε x 0) ≤ 0 := by
    rw [revUnc_zero hW hε, revUnc_zero hW' hε, dist_self]
  exact dist_le_of_approx_trajectories_ODE (v := fun r y => revField ε (y - (W r : ℂ)))
    (K := Real.toNNReal (2 / ε ^ 2)) (f := revUnc W ε x) (g := revUnc W' ε x)
    (f' := fun r => revField ε (revZ W ε x r)) (g' := fun r => revField ε (revZ W' ε x r))
    (a := 0) (b := T) (εf := 0) (εg := (Real.toNNReal (2 / ε ^ 2) : ℝ) * d) (δ := 0)
    (fun r => lipschitz_revField_shift hε _) (hcont W hW) (hIci W hW) hfb (hcont W' hW')
    (hIci W' hW') hgb ha

/-- The tamed flow at a fixed time `s ∈ [0,t]` depends continuously on the driver path. -/
theorem continuous_revZ_Wof {t : ℝ} (ht : 0 ≤ t) {ε : ℝ} (hε : 0 < ε) (x : ℂ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) t) :
    Continuous fun w : C(Icc (0 : ℝ) t, ℝ) => revZ (CharFun.Wof 1 t ht w) ε x s := by
  set K : ℝ≥0 := Real.toNNReal (2 / ε ^ 2)
  set φ : ℝ → ℝ := fun d => gronwallBound 0 K (0 + K * d) (s - 0) + d with hφ
  have hφc : Continuous φ :=
    ((gronwallBound_continuous_ε 0 K (s - 0)).comp
      (continuous_const.add (continuous_const.mul continuous_id))).add continuous_id
  have hWd : ∀ w w0 : C(Icc (0 : ℝ) t, ℝ), ∀ r ∈ Icc (0 : ℝ) t,
      |CharFun.Wof 1 t ht w r - CharFun.Wof 1 t ht w0 r| ≤ dist w w0 := by
    intro w w0 r _
    simp only [CharFun.Wof, Real.sqrt_one, one_mul]
    rw [← Real.dist_eq]
    exact ContinuousMap.dist_apply_le_dist _
  rw [continuous_iff_continuousAt]
  intro w0
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hbound : ∀ w : C(Icc (0 : ℝ) t, ℝ),
      dist (revZ (CharFun.Wof 1 t ht w) ε x s) (revZ (CharFun.Wof 1 t ht w0) ε x s) ≤
        φ (dist w w0) := by
    intro w
    have h1 := dist_revUnc_le (CharFun.continuous_Wof 1 t ht w)
      (CharFun.continuous_Wof 1 t ht w0) hε ht (hWd w w0) x s hs
    have h2 := hWd w w0 s hs
    simp only [revZ, hφ]
    rw [dist_eq_norm] at h1 ⊢
    have e : revUnc (CharFun.Wof 1 t ht w) ε x s - (CharFun.Wof 1 t ht w s : ℂ) -
        (revUnc (CharFun.Wof 1 t ht w0) ε x s - (CharFun.Wof 1 t ht w0 s : ℂ)) =
        (revUnc (CharFun.Wof 1 t ht w) ε x s - revUnc (CharFun.Wof 1 t ht w0) ε x s) -
          ((CharFun.Wof 1 t ht w s - CharFun.Wof 1 t ht w0 s : ℝ) : ℂ) := by
      push_cast; ring
    rw [e]
    refine (norm_sub_le _ _).trans (add_le_add h1 ?_)
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact h2
  have hlim : Tendsto (fun w : C(Icc (0 : ℝ) t, ℝ) => φ (dist w w0)) (𝓝 w0) (𝓝 0) := by
    have hc : Continuous fun w : C(Icc (0 : ℝ) t, ℝ) => φ (dist w w0) :=
      hφc.comp (continuous_id.dist continuous_const)
    have h0 : φ 0 = 0 := by
      simp [hφ, gronwallBound_ε0_δ0]
    have := hc.tendsto w0
    rwa [dist_self, h0] at this
  exact squeeze_zero (fun _ => dist_nonneg) hbound hlim

/-- For a fixed real point `x`, the set of paths starting at `0` for which `x` is live
and negative is measurable. -/
theorem measurableSet_liveNeg_pt (t : ℝ) (ht : 0 ≤ t) (x : ℝ) :
    MeasurableSet {w : C(Icc (0 : ℝ) t, ℝ) |
      w ⟨0, ⟨le_rfl, ht⟩⟩ = 0 ∧ x ∈ liveNeg (CharFun.Wof 1 t ht w) t} := by
  have hz : MeasurableSet {w : C(Icc (0 : ℝ) t, ℝ) | w ⟨0, ⟨le_rfl, ht⟩⟩ = 0} :=
    (isClosed_eq (continuous_eval_const _) continuous_const).measurableSet
  by_cases hx : x < 0
  · have e : {w : C(Icc (0 : ℝ) t, ℝ) |
          w ⟨0, ⟨le_rfl, ht⟩⟩ = 0 ∧ x ∈ liveNeg (CharFun.Wof 1 t ht w) t} =
        {w : C(Icc (0 : ℝ) t, ℝ) | w ⟨0, ⟨le_rfl, ht⟩⟩ = 0} ∩
          ⋃ n : ℕ, ⋂ q : ℚ, {w | (q : ℝ) ∈ Icc 0 t →
            (1 / ((n : ℝ) + 1)) ≤ -(revZ (CharFun.Wof 1 t ht w) (1 / ((n : ℝ) + 1)) x q).re} := by
      ext w
      simp only [mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_iInter, liveNeg, IsLive]
      constructor
      · rintro ⟨h0, -, hl⟩
        refine ⟨h0, ?_⟩
        have hW := CharFun.continuous_Wof 1 t ht w
        have hW0 : CharFun.Wof 1 t ht w 0 = 0 := by
          simp [CharFun.Wof, projIcc_left, h0]
        exact (exists_isRealRevSol_iff hW (by rw [hW0]; exact hx) ht).1
          ((isLive_iff_exists hW ht).1 hl)
      · rintro ⟨h0, hn⟩
        refine ⟨h0, hx, ?_⟩
        have hW := CharFun.continuous_Wof 1 t ht w
        have hW0 : CharFun.Wof 1 t ht w 0 = 0 := by
          simp [CharFun.Wof, projIcc_left, h0]
        exact (isLive_iff_exists hW ht).2
          ((exists_isRealRevSol_iff hW (by rw [hW0]; exact hx) ht).2 hn)
    rw [e]
    refine hz.inter (MeasurableSet.iUnion fun n => MeasurableSet.iInter fun q => ?_)
    by_cases hq : (q : ℝ) ∈ Icc 0 t
    · simp only [hq, true_implies]
      exact measurableSet_le measurable_const
        (Complex.continuous_re.comp (continuous_revZ_Wof ht (by positivity) _ hq)).neg.measurable
    · simp [hq]
  · have e : {w : C(Icc (0 : ℝ) t, ℝ) |
        w ⟨0, ⟨le_rfl, ht⟩⟩ = 0 ∧ x ∈ liveNeg (CharFun.Wof 1 t ht w) t} = ∅ := by
      ext w
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨-, h, -⟩
      exact hx h
    rw [e]; exact MeasurableSet.empty

/-- **M4 (live set).** Joint measurability in (driver path, point) of the live negative set,
for paths starting at `0`. -/
theorem measurableSet_liveNeg_Wof (t : ℝ) (ht : 0 ≤ t) :
    MeasurableSet {p : C(Icc (0 : ℝ) t, ℝ) × ℝ |
      p.1 ⟨0, ⟨le_rfl, ht⟩⟩ = 0 ∧ p.2 ∈ liveNeg (CharFun.Wof 1 t ht p.1) t} := by
  have e : {p : C(Icc (0 : ℝ) t, ℝ) × ℝ |
      p.1 ⟨0, ⟨le_rfl, ht⟩⟩ = 0 ∧ p.2 ∈ liveNeg (CharFun.Wof 1 t ht p.1) t} =
      ⋃ q : ℚ, {w : C(Icc (0 : ℝ) t, ℝ) |
        w ⟨0, ⟨le_rfl, ht⟩⟩ = 0 ∧ (q : ℝ) ∈ liveNeg (CharFun.Wof 1 t ht w) t} ×ˢ Iio (q : ℝ) := by
    ext ⟨w, x⟩
    simp only [mem_ofPred_eq, mem_iUnion, mem_prod, mem_Iio, liveNeg, IsLive]
    have hW := CharFun.continuous_Wof 1 t ht w
    constructor
    · rintro ⟨h0, hl⟩
      obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (isOpen_liveNeg hW t) x hl
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x < x + δ by linarith)
      refine ⟨q, ⟨h0, hball ?_⟩, hq1⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
      linarith
    · rintro ⟨q, ⟨h0, hq, hql⟩, hxq⟩
      have hW0 : CharFun.Wof 1 t ht w 0 = 0 := by
        simp [CharFun.Wof, projIcc_left, h0]
      refine ⟨h0, hxq.trans hq, ?_⟩
      exact hql.trans_le (realHitTime_anti hW hxq.le (by rw [hW0]; exact hq))
  rw [e]
  exact MeasurableSet.iUnion fun q => (measurableSet_liveNeg_pt t ht q).prod measurableSet_Iio

end M4
end E1
end QuantumZipper
