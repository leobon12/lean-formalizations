/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2LaterMeas
import InteractingSLE.Spec.Supplement.GW2aContStepAux
import InteractingSLE.Spec.Exist.StagedLaw4
import InteractingSLE.Spec.Zhan.ConstDriftHeightMeas

/-!
# The inverse charts of a staged run are measurable

Packet PROVE-T14-SBLEAVES6, first step of SB3's measurability inputs (I2), (I2′): a measurable dense family of the
retained lower prefix needs the physical points of the pieces, which are boundary values of the launch charts'
inverses. `RunMeasStatement` (PROVE-STAGEDLAW2) gives only the forward charts; here the inverses.

* `measurable_fwdMapInv_recDrv_stop`: the inverse Loewner map of a piece's record driver at its (random) stop, at a
  fixed point of `ℍ` (Carathéodory in time: `t ↦ F_t(w)` is continuous);
* **`measurable_runChart_inv`**: if every launched piece is regular at every sample (`RegLaunches`), the inverse of
  the run's chart after `n` instructions is measurable at every point of `ℍ`. A step without launch recentres the
  chart by `Re (c(i) − c'(i))` (forward values, measurable by `runMeasStatement`); a launch composes with the inverse
  Loewner map of the stopped driver, which is the record driver (`isDrvGood_of_continuousOn_le`);
* `bdVal` (the boundary value of a chart's inverse read along `z + i/(m+1)`), `bdVal_eq_of_tendsto`,
  **`measurable_bdVal`** (at a measurable point).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMapInv)

namespace InteractingSLE.Theorem14.SB.LuM

open Exist.Staged Exist.StagedLaw

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The inverse Loewner map at the stop -/

theorem recDrv_toNNReal_coe (t : ℝ≥0∞) (e : (ℝ≥0 → ℝ) × ℝ≥0∞) :
    (fun x : ℝ => recDrv t e (x.toNNReal : ℝ)) = recDrv t e := by
  funext x
  simp only [recDrv, Real.toNNReal_coe]

theorem recDrv_coe_zero (t : ℝ≥0∞) (e : (ℝ≥0 → ℝ) × ℝ≥0∞) : recDrv t e ((0 : ℝ≥0) : ℝ) = 0 := by
  rw [NNReal.coe_zero]
  exact recDrv_zero t e

/-- The inverse Loewner map of a piece's record driver at a fixed time and point of `ℍ` is measurable. -/
theorem measurable_fwdMapInv_recDrv_time {D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hD : Measurable D)
    (hreg : ∀ ω, IsRegularDriver (D ω)) (t : ℝ≥0∞) {w : ℂ} (hw : w ∈ H) (s : ℝ≥0) :
    Measurable fun ω => fwdMapInv (recDrv t (D ω)) s w := by
  have h := GW2Later.measurable_fwdMapInv_apply (B := fun (r : ℝ≥0) ω => recDrv t (D ω) r)
      (fun r => measurable_recDrv_apply t hD hreg r)
      (fun ω => (continuous_recDrv t (D ω)).comp NNReal.continuous_coe)
      (fun ω => recDrv_coe_zero t (D ω)) (T := (s : ℝ)) s.coe_nonneg ⟨w, hw⟩
  simp only [recDrv_toNNReal_coe] at h
  exact h

/-- **The inverse Loewner map of a piece's record driver at its stop**, at a fixed point of `ℍ`, is measurable
(Carathéodory in time). -/
theorem measurable_fwdMapInv_recDrv_stop {D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hD : Measurable D)
    (hreg : ∀ ω, IsRegularDriver (D ω)) (t : ℝ≥0∞) {w : ℂ} (hw : w ∈ H) :
    Measurable fun ω => fwdMapInv (recDrv t (D ω)) (stopTime t (D ω)) w := by
  have hc : ∀ ω, Continuous fun s : ℝ≥0 => fwdMapInv (recDrv t (D ω)) s w := fun ω =>
    Zhan.HeightLaw.continuous_fwdMapInv_time (continuous_recDrv t (D ω)) (recDrv_zero t (D ω)) hw
  have hU : Measurable (Function.uncurry fun (s : ℝ≥0) ω => fwdMapInv (recDrv t (D ω)) s w) :=
    measurable_uncurry_of_continuous_of_measurable hc (measurable_fwdMapInv_recDrv_time hD hreg t hw)
  have hs : Measurable fun ω => (min t (D ω).2).toNNReal :=
    (measurable_const.min (measurable_snd.comp hD)).ennreal_toNNReal
  have h2 := hU.comp (hs.prodMk measurable_id)
  unfold stopTime
  exact h2

theorem fwdMapInv_recDrv_mem_H (t : ℝ≥0∞) (e : (ℝ≥0 → ℝ) × ℝ≥0∞) {w : ℂ} (hw : w ∈ H) :
    fwdMapInv (recDrv t e) (stopTime t e) w ∈ H :=
  QuantumZipper.RS.fwdMapInv_mem_H (continuous_recDrv t e) (recDrv_zero t e) (stopTime_nonneg t e) hw

/-! ### The inverse chart of a run -/

/-- **Every launched piece of the run is regular** (the hypothesis of `GW1P.isClosed_pieces_run`). -/
def RegLaunches (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  ∀ (k : ℕ) (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ) →
    GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- Along a run with regular launches every chart is conformal. -/
theorem isConformal_runChart_of_reg (spec : ExplSpec) {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps spec D) (n : ℕ) : (stChart (ExplState.run κ b jumps spec D n)).IsConformal :=
  (GW2aCont.isConformal_runChart (κ := κ) (b := b) (jumps := jumps) spec D n
    fun j _ c θ h => hP j c θ h).1

/-- Carathéodory at a random point of `ℍ` for the run's inverse chart. -/
theorem measurable_runChart_inv_at (spec : ExplSpec) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : ∀ ω, RegLaunches κ b jumps spec fun j => E j ω) {n : ℕ}
    (hn : ∀ w ∈ H, Measurable fun ω => (stChart (ExplState.run κ b jumps spec (fun j => E j ω) n)).2.1 w)
    {Z : Ω → ℂ} (hZ : Measurable Z) (hZH : ∀ ω, Z ω ∈ H) :
    Measurable fun ω => (stChart (ExplState.run κ b jumps spec (fun j => E j ω) n)).2.1 (Z ω) :=
  GW2Later.measurable_apply_subtype_H
    (u := fun w ω => (stChart (ExplState.run κ b jumps spec (fun j => E j ω) n)).2.1 w)
    (fun ω => (isConformal_runChart_of_reg spec (hP ω) n).1.continuousOn.comp_continuous continuous_subtype_val
      fun w => w.2)
    (fun w => hn w w.2) hZ hZH

/-- **The inverse chart of a run with regular launches is measurable at every point of `ℍ`.** -/
theorem measurable_runChart_inv (hb : IsPiecewiseConstantBoundaryData b jumps) (spec : ExplSpec)
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hP : ∀ ω, RegLaunches κ b jumps spec fun j => E j ω) :
    ∀ n, ∀ w ∈ H, Measurable fun ω => (stChart (ExplState.run κ b jumps spec (fun j => E j ω) n)).2.1 w
  | 0, w, _ => by
    have e : ∀ ω, ExplState.run κ b jumps spec (fun j => E j ω) 0 = ExplState.init spec.1 := fun ω => by
      simp [ExplState.run]
    simp_rw [e]
    exact measurable_const
  | n + 1, w, hw => by
    classical
    have ih := measurable_runChart_inv hb spec hE hreg hP n
    set c : Ω → Chart := fun ω => stChart (ExplState.run κ b jumps spec (fun j => E j ω) n) with hc
    set c' : Ω → Chart := fun ω => stChart (ExplState.run κ b jumps spec (fun j => E j ω) (n + 1)) with hc'
    set L := {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (n + 1)).2.2.2.1 n ≠ none} with hL
    have hLm : MeasurableSet L := (runMeasStatement κ b jumps hb spec E hE hreg n).1
    set t := instrTime spec n with ht
    set T := {ω | min t (E n ω).2 = ⊤} with hT
    have hTm : MeasurableSet T := measurableSet_stop_top t (hE n)
    set a : Ω → ℝ := fun ω => ((c ω).1 Complex.I - (c' ω).1 Complex.I).re with ha
    have ham : Measurable a :=
      Complex.measurable_re.comp (((runMeasStatement κ b jumps hb spec E hE hreg n).2 Complex.I).sub
        ((runMeasStatement κ b jumps hb spec E hE hreg (n + 1)).2 Complex.I))
    set F : Ω → ℂ := fun ω => fwdMapInv (recDrv t (E n ω)) (stopTime t (E n ω)) w with hF
    have heq : ∀ ω, (c' ω).2.1 w = L.piecewise (T.piecewise (fun ω => (c ω).2.1 w) fun ω => (c ω).2.1 (F ω))
        (fun ω => (c ω).2.1 (w + (a ω : ℂ))) ω := by
      intro ω
      by_cases hωL : ω ∈ L
      · rw [piecewise_eq_of_mem _ _ _ hωL]
        obtain ⟨⟨c₀, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hωL
        obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec _ hcθ
        have hPR := hP ω n c₀ θ hcθ
        by_cases hωT : ω ∈ T
        · rw [piecewise_eq_of_mem _ _ _ hωT]
          simp only [hc', hc, stChart, he]
          rw [GW2aCont.chart_launch_of_top _ _ _ _ _ hωT]
        · rw [piecewise_eq_of_notMem _ _ _ hωT]
          have hfin : min t (E n ω).2 ≠ ⊤ := hωT
          have hg := isDrvGood_of_continuousOn_le (hreg n ω) hfin hPR.2.1
          have hrd := recDrv_eq_stopDrv (hreg n ω) hg
          simp only [hc', hc, hF, stChart, he]
          rw [chart_launch _ _ _ _ _ hfin, hrd]
          rfl
      · rw [piecewise_eq_of_notMem _ _ _ hωL]
        have hnone : (ExplState.run κ b jumps spec (fun j => E j ω) (n + 1)).2.2.2.1 n = none := by
          simpa [hL] using hωL
        obtain ⟨a', ha'⟩ := chart_run_succ_of_noLaunch (κ := κ) (b := b) (jumps := jumps) spec _ hnone
        have haa : a ω = a' := by
          simp only [ha, hc, hc', stChart, ha', Chart.recenter]
          simp
        rw [haa]
        simp only [hc', hc, stChart, ha', Chart.recenter]
    have hfun : (fun ω => (c' ω).2.1 w) = L.piecewise (T.piecewise (fun ω => (c ω).2.1 w)
        fun ω => (c ω).2.1 (F ω)) (fun ω => (c ω).2.1 (w + (a ω : ℂ))) := funext heq
    show Measurable fun ω => (c' ω).2.1 w
    rw [hfun]
    refine Measurable.piecewise hLm (Measurable.piecewise hTm (ih w hw) ?_) ?_
    · exact measurable_runChart_inv_at spec hP ih (measurable_fwdMapInv_recDrv_stop (hE n) (hreg n) t hw)
        fun ω => fwdMapInv_recDrv_mem_H t (E n ω) hw
    · refine measurable_runChart_inv_at spec hP ih (measurable_const.add (Complex.measurable_ofReal.comp ham))
        fun ω => ?_
      show 0 < (w + (a ω : ℂ)).im
      simpa using (show 0 < w.im from hw)

/-! ### Boundary values of an inverse chart -/

/-- The point `z`, pushed into `ℍ̄` and lifted by `1/(m+1)`. -/
def liftPt (z : ℂ) (m : ℕ) : ℂ := (z.re : ℂ) + ((max z.im 0 + 1 / ((m : ℝ) + 1) : ℝ) : ℂ) * Complex.I

theorem liftPt_mem_H (z : ℂ) (m : ℕ) : liftPt z m ∈ H := by
  show 0 < (liftPt z m).im
  simp only [liftPt, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    mul_zero, Complex.I_im, mul_one, zero_add]
  positivity

theorem measurable_liftPt {Z : Ω → ℂ} (hZ : Measurable Z) (m : ℕ) : Measurable fun ω => liftPt (Z ω) m :=
  (Complex.measurable_ofReal.comp (Complex.measurable_re.comp hZ)).add
    ((Complex.measurable_ofReal.comp (((Complex.measurable_im.comp hZ).max measurable_const).add
      measurable_const)).mul measurable_const)

theorem tendsto_liftPt {z : ℂ} (hz : 0 ≤ z.im) : Tendsto (liftPt z) atTop (𝓝[H] z) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun m => liftPt_mem_H z m⟩
  have e : ∀ m : ℕ, liftPt z m = z + ((1 / ((m : ℝ) + 1) : ℝ) : ℂ) * Complex.I := fun m => by
    apply Complex.ext <;> simp [liftPt, max_eq_left hz]
  rw [show liftPt z = fun m : ℕ => z + ((1 / ((m : ℝ) + 1) : ℝ) : ℂ) * Complex.I from funext e]
  have h : Tendsto (fun m : ℕ => ((1 / ((m : ℝ) + 1) : ℝ) : ℂ) * Complex.I) atTop (𝓝 0) := by
    have h1 := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using h1.mul_const Complex.I
  simpa using tendsto_const_nhds.add h

/-- The boundary value of the chart's inverse at `z`, read along `z + i/(m+1)`. -/
def bdVal (c : Chart) (z : ℂ) : ℂ := limUnder atTop fun m : ℕ => c.2.1 (liftPt z m)

theorem bdVal_eq_of_tendsto {c : Chart} {z y : ℂ} (hz : 0 ≤ z.im) (h : Tendsto c.2.1 (𝓝[H] z) (𝓝 y)) :
    bdVal c z = y :=
  (h.comp (tendsto_liftPt hz)).limUnder_eq

theorem bdVal_eq_of_mem_H {c : Chart} {z : ℂ} (hc : ContinuousOn c.2.1 H) (hz : z ∈ H) : bdVal c z = c.2.1 z :=
  bdVal_eq_of_tendsto (le_of_lt (show 0 < z.im from hz)) (hc z hz)

/-- **Boundary values of measurable inverse charts at a measurable point are measurable.** -/
theorem measurable_bdVal {c : Ω → Chart} (hm : ∀ w ∈ H, Measurable fun ω => (c ω).2.1 w)
    (hc : ∀ ω, ContinuousOn (c ω).2.1 H) {Z : Ω → ℂ} (hZ : Measurable Z) :
    Measurable fun ω => bdVal (c ω) (Z ω) := by
  have hseq : ∀ m, Measurable fun ω => (c ω).2.1 (liftPt (Z ω) m) := fun m =>
    GW2Later.measurable_apply_subtype_H (u := fun w ω => (c ω).2.1 w)
      (fun ω => (hc ω).comp_continuous continuous_subtype_val fun w => w.2) (fun w => hm w w.2)
      (measurable_liftPt hZ m) fun _ => liftPt_mem_H _ m
  exact (StronglyMeasurable.limUnder fun m => (hseq m).stronglyMeasurable).measurable

end InteractingSLE.Theorem14.SB.LuM
