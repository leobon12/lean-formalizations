/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5WallLate
import InteractingSLE.Spec.Sec7.R5WallCore
import InteractingSLE.Spec.Sec7.SideC8Visits
import InteractingSLE.Spec.Sec7.SideC11Marks
import InteractingSLE.Spec.Restart.FCAux79MeanFlow

/-!
# The late incoming selection at the wall coordinates (R5-WALL's `hIncoming`, PROVED)

Packet PROVE-COLLAR-COVER. R5-WALL's late split (`Wire.visitReferenceHeightCoverPosExc_of_wall_split`) takes the
incoming selection at the wall coordinates (outside the open seed interval) as the named pathwise input
`Wire.VisitReferenceIncomingWallCoverPosExc`. It is proved here, with no input, for the references at the rational
original times:

* `exists_alive_lt` (real flow): an alive point is approached from the left by alive points;
* `eq_of_rightImg_eq_gImg`: the geometric image `rightImg w m t` of any index equals the image `g_t(r)` of an alive
  point `r` only for `m = r`;
* **`exists_incoming_of_wall`** (real flow): a real coordinate outside the closed seed interval, off the jumps at `q`,
  is the image at `q` of a surviving real point `x`, which is off the initial marks and whose image at every earlier
  `p ≤ q` is off the jumps at `p` (signed marks: left marks `≤ 0`, right marks `≥ 0`);
* **`visitReferenceIncomingWallCoverPosExc_rational`**: the late statement, with the reference at a rational original
  visit before the capacity (`SideTest.exists_rational_reference_before_capacity`).

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.ColCov

open MartChar.RealFlow

/-! ### Real flow -/

/-- **Alive points are approached from the left by alive points.** -/
theorem exists_alive_lt {w : ℝ → ℝ} (hw : Continuous w) {r t : ℝ} (ht : 0 ≤ t) (hr : Alive w r t) {m : ℝ}
    (hm : m < r) : ∃ y, m < y ∧ y < r ∧ Alive w y t := by
  have hc : ContinuousOn (cflow w r) (Icc 0 t) := by
    have h := (hr.isPosSol hw).1
    exact h
  obtain ⟨u₀, hu₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 ht) hc
  have hc₀ : 0 < cflow w r u₀ := hr.cflow_pos hw hu₀
  have hr0 : 0 < r - w 0 := alive_zero_iff.1 (hr.mono ht)
  set δ := min (min (cflow w r u₀ / 2) (r - w 0)) (r - m) with hδdef
  have hδ : 0 < δ := lt_min (lt_min (by linarith) hr0) (by linarith)
  have hδ1 : δ ≤ cflow w r u₀ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ r - w 0 := (min_le_left _ _).trans (min_le_right _ _)
  have hδ3 : δ ≤ r - m := min_le_right _ _
  refine ⟨r - δ / 2, by linarith, by linarith, ?_⟩
  have hy0 : Alive w (r - δ / 2) 0 := alive_zero_iff.2 (by linarith)
  refine hy0.of_forall_le_cflow hw le_rfl (show 0 < cflow w r u₀ / 2 by linarith) fun u hu hyu => ?_
  have h1 := (cflow_lt_and_sub_le hw hyu (show r - δ / 2 < r by linarith) hu.1 ⟨hu.1, le_rfl⟩).2
  have h2 : cflow w r u₀ ≤ cflow w r u := hmin hu
  linarith

/-- **The geometric image of an index meets the image of an alive point only at that point.** -/
theorem eq_of_rightImg_eq_gImg {w : ℝ → ℝ} (hw : Continuous w) {m r t : ℝ} (ht : 0 ≤ t) (hr : Alive w r t)
    (h : rightImg w m t = gImg w r t) : m = r := by
  rcases lt_trichotomy m r with hmr | hmr | hmr
  · obtain ⟨y, hmy, hyr, hy⟩ := exists_alive_lt hw ht hr hmr
    have h1 := rightImg_le_gImg hw ht hmy hy
    have h2 := Restart.FCAux79.gImg_lt_gImg hw ht hy hyr
    linarith
  · exact hmr
  · have hm : Alive w m t := hr.of_le hw hmr.le ht
    have h1 := rightImg_eq_gImg hw ht hm
    have h2 := Restart.FCAux79.gImg_lt_gImg hw ht hr hmr
    linarith

/-- The positions at time `0` of signed marks are the marks. -/
theorem positions_zero {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {nL nR : ℕ} {mL : Fin nL → ℝ}
    {mR : Fin nR → ℝ} (hmL : ∀ a, mL a ≤ 0) (hmR : ∀ b, 0 ≤ mR b) :
    forceJumpSet (fun a => -rightImg (fun s => -W s) (-mL a) 0 - W 0) (fun b => rightImg W (mR b) 0 - W 0) =
      forceJumpSet mL mR := by
  have hWn : Continuous fun s => -W s := hW.neg
  have hWn0 : (fun s => -W s) 0 = 0 := by simp only [hW0, neg_zero]
  have hL : (fun a => -rightImg (fun s => -W s) (-mL a) 0 - W 0) = mL := by
    funext a
    rw [rightImg_zero hWn hWn0 (by linarith [hmL a]), hW0]
    ring
  have hR : (fun b => rightImg W (mR b) 0 - W 0) = mR := by
    funext b
    rw [rightImg_zero hW hW0 (hmR b), hW0, sub_zero]
  rw [hL, hR]

/-- **The surviving real point at a wall coordinate and its jump exclusions** (real flow, signed marks): a real
coordinate `ξ` off the jumps at `q`, strictly outside the seed images, is the image at `q` of a real point `x` alive up
to `q`, off the marks (= the jumps at `0`), and whose image at every `p ∈ [0, q]` is off the jumps at `p`. -/
theorem exists_incoming_of_wall {W : ℝ → ℝ} (hW : Continuous W) {nL nR : ℕ}
    {mL : Fin nL → ℝ} {mR : Fin nR → ℝ} (hmL : ∀ a, mL a ≤ 0) (hmR : ∀ b, 0 ≤ mR b) {q p : ℝ} (hp : 0 ≤ p)
    (hpq : p ≤ q) {ξ : ℝ}
    (hξ : ξ ∉ forceJumpSet (fun a => -rightImg (fun s => -W s) (-mL a) q - W q)
      (fun b => rightImg W (mR b) q - W q))
    (hside : ξ < -rightImg (fun s => -W s) 0 q - W q ∨ rightImg W 0 q - W q < ξ) :
    ∃ (x : ℝ) (a : ℝ → ℂ), QuantumZipper.IsForwardSol W (x : ℂ) q a ∧ (a q).re = ξ ∧
      x ∉ forceJumpSet mL mR ∧
      (a p).re ∉ forceJumpSet (fun a => -rightImg (fun s => -W s) (-mL a) p - W p)
        (fun b => rightImg W (mR b) p - W p) := by
  have hq : 0 ≤ q := hp.trans hpq
  have hWn : Continuous fun s => -W s := hW.neg
  rcases hside with hξL | hξR
  · -- a surviving point on the left: the reflected flow
    obtain ⟨r, hr, hAlive, hg⟩ := ZhanGT4.A2X.P3.exists_alive_gImg_eq_of_rightImg_lt hWn hq
      (x := 0) (u := -ξ - W q) (by linarith)
    have hsol := QuantumZipper.RS.isForwardSol_neg (WangWu.isForwardSol_of_alive hWn hAlive)
    simp only [neg_neg] at hsol
    have hcq : cflow (fun s => -W s) r q = -ξ := by
      simp only [gImg] at hg
      linarith
    refine ⟨-r, fun t => -((cflow (fun s => -W s) r t : ℝ) : ℂ), ?_, ?_, ?_, ?_⟩
    · rw [Complex.ofReal_neg]
      exact hsol
    · simp only [Complex.neg_re, Complex.ofReal_re, hcq, neg_neg]
    · rintro (h | ⟨a, ha⟩ | ⟨b, hb⟩)
      · linarith
      · -- a left mark at `-r` would put `ξ` on its position at `q`
        apply hξ
        refine Or.inr (Or.inl ⟨a, ?_⟩)
        show -rightImg (fun s => -W s) (-mL a) q - W q = ξ
        rw [ha, neg_neg, rightImg_eq_gImg hWn hq hAlive, hg]
        ring
      · linarith [hmR b]
    · have hrp : Alive (fun s => -W s) r p := hAlive.mono hpq
      have hpos : 0 < cflow (fun s => -W s) r p := hAlive.cflow_pos hWn ⟨hp, hpq⟩
      simp only [Complex.neg_re, Complex.ofReal_re]
      rintro (h | ⟨a, ha⟩ | ⟨b, hb⟩)
      · linarith
      · -- equal left positions force the mark to be `-r`
        have himg : rightImg (fun s => -W s) (-mL a) p = gImg (fun s => -W s) r p := by
          simp only [gImg]
          linarith
        have hm := eq_of_rightImg_eq_gImg hWn hp hrp himg
        apply hξ
        refine Or.inr (Or.inl ⟨a, ?_⟩)
        show -rightImg (fun s => -W s) (-mL a) q - W q = ξ
        rw [hm, rightImg_eq_gImg hWn hq hAlive, hg]
        ring
      · have := le_rightImg hW (mR b) hp
        linarith
  · -- a surviving point on the right
    obtain ⟨r, hr, hAlive, hg⟩ := ZhanGT4.A2X.P3.exists_alive_gImg_eq_of_rightImg_lt hW hq
      (x := 0) (u := ξ + W q) (by linarith)
    have hcq : cflow W r q = ξ := by
      simp only [gImg] at hg
      linarith
    refine ⟨r, _, WangWu.isForwardSol_of_alive hW hAlive, ?_, ?_, ?_⟩
    · simp only [Complex.ofReal_re, hcq]
    · rintro (h | ⟨a, ha⟩ | ⟨b, hb⟩)
      · linarith
      · linarith [hmL a]
      · apply hξ
        refine Or.inr (Or.inr ⟨b, ?_⟩)
        show rightImg W (mR b) q - W q = ξ
        rw [hb, rightImg_eq_gImg hW hq hAlive, hg]
        ring
    · have hrp : Alive W r p := hAlive.mono hpq
      have hpos : 0 < cflow W r p := hAlive.cflow_pos hW ⟨hp, hpq⟩
      simp only [Complex.ofReal_re]
      rintro (h | ⟨a, ha⟩ | ⟨b, hb⟩)
      · linarith
      · have := le_rightImg hWn (-mL a) hp
        linarith
      · have himg : rightImg W (mR b) p = gImg W r p := by
          simp only [gImg]
          linarith
        have hm := eq_of_rightImg_eq_gImg hW hp hrp himg
        apply hξ
        refine Or.inr (Or.inr ⟨b, ?_⟩)
        show rightImg W (mR b) q - W q = ξ
        rw [hm, rightImg_eq_gImg hW hq hAlive, hg]
        ring

/-! ### The late statement -/

open Wire Wire.Current Wire.Current.SideTest PocketStop PocketStopSide PocketTraversal Lemma71C
open Wire.Current.SideTest (rationalOriginalTime)

variable {Ω : Type} [MeasurableSpace Ω]

/-- **R5-WALL's `hIncoming` at the rational original times, PROVED** (no input): at every positive live relative
capacity, every current coordinate off the jumps and outside the open seed interval is the image of a surviving initial
real point off the initial marks, whose image at the capacity of a rational original visit before `q` is off the jumps
there. -/
theorem visitReferenceIncomingWallCoverPosExc_rational (i : BothLow) (d : WordObjects Ω)
    (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) :
    VisitReferenceIncomingWallCoverPosExc i d (fun _ => rationalOriginalTime) X := by
  intro j hj q hq0
  refine Eventually.of_forall fun ω hω hlive ξ hξ _ hwall => ?_
  obtain ⟨r, hvisit, hcap0, hcapq⟩ := exists_rational_reference_before_capacity hj hω hq0 hlive
  have hγ := isDrivenCurve_target (i := i) hj ω hω
  obtain ⟨W, hW, hW0, q', hqq', hEq, -⟩ := exists_relChart_eq_loewner (c := (j.target i d).baseChart) hγ hlive
  set p := (j.visitCapacity d ω (rationalOriginalTime r)).toNNReal with hpdef
  have hpq : p ≤ q := hcapq.le
  have hEqAt : ∀ t : ℝ≥0, t ≤ q → EqOn (fun u : ℝ => (fun t ω => segDriver ((j.target i d).curve ω) t)
      u.toNNReal ω) W (Icc 0 (t : ℝ)) := fun t ht u hu =>
    hEq u ⟨hu.1, hu.2.trans ((NNReal.coe_le_coe.2 ht).trans hqq'.le)⟩
  obtain ⟨hLq, hRq⟩ := geom_positions_eq_of_driver_eqOn (fun t ω => segDriver ((j.target i d).curve ω) t)
    (j.target i d).marksL (j.target i d).marksR hW (hEqAt q le_rfl)
  obtain ⟨hLp, hRp⟩ := geom_positions_eq_of_driver_eqOn (fun t ω => segDriver ((j.target i d).curve ω) t)
    (j.target i d).marksL (j.target i d).marksR hW (hEqAt p hpq)
  obtain ⟨hL0, hR0⟩ := geom_positions_eq_of_driver_eqOn (fun t ω => segDriver ((j.target i d).curve ω) t)
    (j.target i d).marksL (j.target i d).marksR hW (hEqAt 0 zero_le)
  obtain ⟨hsL, hsR⟩ := initial_marks_signed_of_ready hj hω
  obtain ⟨hmL, hmR⟩ := target_seed_marks j i d ω
  have hξ' : ξ ∉ forceJumpSet (fun a => -rightImg (fun s => -W s) (-(j.target i d).marksL ω a) q - W q)
      (fun b => rightImg W ((j.target i d).marksR ω b) q - W q) := by
    rw [← hLq, ← hRq]
    exact hξ
  have hzL : geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL
      (Late.leftZero i d j) q ω - segDriver ((j.target i d).curve ω) q = -rightImg (fun s => -W s) 0 q - W q := by
    have h := congrFun hLq (Late.leftZero i d j)
    simp only [hmL, neg_zero] at h
    exact h
  have hzR : geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR
      (Late.rightZero i d j) q ω - segDriver ((j.target i d).curve ω) q = rightImg W 0 q - W q := by
    have h := congrFun hRq (Late.rightZero i d j)
    simp only [hmR] at h
    exact h
  have hside : ξ < -rightImg (fun s => -W s) 0 q - W q ∨ rightImg W 0 q - W q < ξ := by
    have hne1 : ξ ≠ -rightImg (fun s => -W s) 0 q - W q := fun h =>
      hξ (Or.inr (Or.inl ⟨Late.leftZero i d j, hzL.trans h.symm⟩))
    have hne2 : ξ ≠ rightImg W 0 q - W q := fun h =>
      hξ (Or.inr (Or.inr ⟨Late.rightZero i d j, hzR.trans h.symm⟩))
    rw [hzL, hzR] at hwall
    simp only [mem_Ioo, not_and_or, not_lt] at hwall
    rcases hwall with h | h
    · exact Or.inl (lt_of_le_of_ne h hne1)
    · exact Or.inr (lt_of_le_of_ne h (Ne.symm hne2))
  obtain ⟨x, a, ha, haq, hx, hxp⟩ := exists_incoming_of_wall hW hsL hsR p.coe_nonneg
    (NNReal.coe_le_coe.2 hpq) hξ' hside
  refine ⟨r, W, q', x, a, hvisit, hpq, hW, hW0, hqq', fun u hu => hEq u hu, ha, haq, hx, ?_, ?_⟩
  · show x ∉ forceJumpSet _ _
    rw [hL0, hR0]
    simp only [NNReal.coe_zero]
    rw [positions_zero hW hW0 hsL hsR]
    exact hx
  · show (a p).re ∉ forceJumpSet _ _
    rw [hLp, hRp]
    exact hxp

end InteractingSLE.Sec7.ColCov
