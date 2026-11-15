/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LwStop
import InteractingSLE.Spec.Supplement.GW1ActiveChart
import InteractingSLE.Spec.Supplement.CounterflowRange
import InteractingSLE.Spec.Supplement.GW2aContArc
import InteractingSLE.Foundations.Loewner.RealPoints
import InteractingSLE.Foundations.SLE.SpaceFilling.SwallowReal
import QuantumZipper.Proofs.Thm11.ExtMeasCont
import QuantumZipper.Proofs.RS.TraceShift

/-!
# SB2(2)'s word: the state of the upper schedule at a launch (deterministic)

Packet PROVE-T14-SB2LOW (ruling R99). The upper own-angle history of SB2(2) is the GW2 schedule program
`⟨u, true, scheduleProgram 0 l⟩`: every launched piece after the first starts at the interior tip of the previous one,
stopped strictly before its lifetime. At such a state `s` the chart and the physical prefix satisfy `UState u s`:

* the chart is conformal, real on the real line, and maps the untouched ray right of the right record `stRecR s`
  continuously and increasingly into `(0, ∞)`, with boundary values there (`Tendsto c.fwd (𝓝[ℍ] x) (𝓝[ℍ] c.fwd x)`);
* the root `u` is at most the right record, there are no connectors, and **every real point of a launched piece is at
  most the right record** (a physical piece cannot touch an untouched real point: in the launch chart its trace would
  approach an alive point, whose image under the centred map is not the tip `0`).

`uState_init` is the root; **`uState_launch`** is the step through a piece stopped at an interior tip, together with
the relation between the old and the new right profiles (the real flow of the stopped driver) and the fact that the
real points between the two records are swallowed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol chiC fwdMap fwdMapInv fwdHull H)

namespace InteractingSLE.Theorem14.SB.Lh

open Exist Exist.StagedLaw Exist.Staged Restart GW1W

/-- **The state part of SB2(2)'s upper invariant** at a state `s` of the upper schedule run from `u`. -/
def UState (u : ℝ) (s : ExplState) : Prop :=
  (stChart s).IsConformal ∧ IsRealChart (stChart s) ∧ RightGood (rProf (stChart s)) (stRecR s) ∧
    (∀ x, stRecR s < x → 0 < rProf (stChart s) x) ∧
    (∀ x, stRecR s < x → Tendsto (stChart s).1 (𝓝[H] (x : ℂ)) (𝓝[H] ((stChart s).1 x))) ∧
    u ≤ stRecR s ∧ s.2.1 = [] ∧ ∀ p ∈ s.1, ∀ z ∈ p.1.tipSet p.2.1 p.2.2, z.im = 0 → z.re ≤ stRecR s

/-- The chart of the root state is the translation `z ↦ z − u`. -/
theorem rProf_init (u : ℝ) : rProf (stChart (ExplState.init u)) = fun x => x - u := by
  funext x
  simp [rProf, ExplState.init, InteractingSLE.Chart.recenter, InteractingSLE.Chart.id]

/-- **The root state** satisfies the state invariant. -/
theorem uState_init (u : ℝ) : UState u (ExplState.init u) := by
  have hR : stRecR (ExplState.init u) = u := rfl
  have hch : stChart (ExplState.init u) = Chart.id.recenter u := rfl
  refine ⟨?_, fun x => ?_, ?_, fun x hx => ?_, fun x hx => ?_, le_of_eq hR.symm, rfl, fun p hp => ?_⟩
  · rw [hch]; exact Chart.isConformal_id.recenter u
  · simp [hch, InteractingSLE.Chart.recenter, InteractingSLE.Chart.id]
  · rw [rProf_init, hR]
    exact ⟨fun x _ y _ hxy => by linarith, continuousOn_id.sub continuousOn_const,
      fun M => ⟨u + max M 0 + 1, by linarith [le_max_right M 0],
        by show M < u + max M 0 + 1 - u; linarith [le_max_left M 0]⟩⟩
  · rw [rProf_init]; rw [hR] at hx; linarith
  · rw [hch]
    change Tendsto (fun z : ℂ => z - u) (𝓝[H] (x : ℂ)) (𝓝[H] ((x : ℂ) - u))
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz => ?_⟩
    · exact ((continuous_id.sub continuous_const).tendsto _).mono_left nhdsWithin_le_nhds
    · change 0 < (z - (u : ℂ)).im
      simpa using (show 0 < z.im from hz)
  · exact absurd hp (by simp [ExplState.init])

/-- Between the old and the new right record every real point is swallowed. -/
theorem not_alive_of_lt_newRec {m : ℝ → ℝ} {a : ℝ} {A : ℝ → Prop} {f : ℝ → ℝ} (hm : RightGood m a)
    (hpos : ∀ x, a < x → 0 < m x) (hA : IsRealHalf A f) {z : ℝ} (hz : a < z) (hz' : z < newRec m a A) :
    ¬ A (m z) := by
  intro hAz
  have : newRec m a A ≤ z := by
    refine csSup_le (insert_nonempty _ _) fun x hx => ?_
    rcases hx with rfl | ⟨hxa, hxA⟩
    · exact hz.le
    · by_contra hxz
      push Not at hxz
      exact hxA (hA.2.1 (m z) (m x) (hpos z hz) (hm.1 hz hxa hxz) hAz)
  linarith

/-- Near an alive point, the forward map stays in `ℍ`. -/
theorem eventually_fwdMap_mem_H {W : ℝ → ℝ} (hW : Continuous W) {p : ℂ} {T : ℝ} {v : ℝ → ℂ} (hT : 0 ≤ T)
    (hv : IsForwardSol W p T v) : ∀ᶠ q in 𝓝[H] p, fwdMap W T q ∈ H := by
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol hT hv
  have hc : Continuous fun q : ℂ => ‖q - p‖ * Real.exp (2 / δ ^ 2 * T) := by fun_prop
  have hev : ∀ᶠ q in 𝓝 p, ‖q - p‖ * Real.exp (2 / δ ^ 2 * T) < δ :=
    hc.continuousAt.eventually_lt continuousAt_const (by simp [hδ])
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with q hq hqH
  have hK := not_mem_fwdHull_of_isForwardSol hW hv hδ hlow hqH hq
  exact QuantumZipper.Thm11Asm.MeasCont.fwdMap_im_pos_of_not_mem_fwdHull hW hqH hT hK ⟨hT, le_rfl⟩

section Launch

variable {s : ExplState} {D : (ℝ≥0 → ℝ) × ℝ≥0∞} {t : ℝ≥0∞}

/-- The record of a piece stopped strictly before its lifetime is good. -/
theorem isDrvGood_recOf_tip (hreg : IsRegularDriver D) (ht : t ≠ ⊤) (htD : t < D.2) :
    LocalExt.IsDrvGood (recHist (recOf t D)) := by
  have h := isDrvGood_recOf_of_lt hreg (r := t.toNNReal) (by rwa [ENNReal.coe_toNNReal ht])
  rwa [ENNReal.coe_toNNReal ht] at h

/-- **The step of the state invariant through a piece stopped at an interior tip**, with the relation between the
profiles (the real flow of the record driver) and the swallowed points between the records. -/
theorem uState_launch {u : ℝ} (hs : UState u s) (k : ℕ) (θ : ℝ) (hreg : IsRegularDriver D) (ht : t ≠ ⊤)
    (htD : t < D.2) :
    UState u (ExplState.launch s k D θ t) ∧ stRecR s ≤ stRecR (ExplState.launch s k D θ t) ∧
      (∀ z, stRecR s < z → z < stRecR (ExplState.launch s k D θ t) →
        ¬ ∃ v, IsForwardSol (rdrv (recOf t D)) (rProf (stChart s) z : ℂ) (rtime (recOf t D)) v) ∧
      ∀ x, stRecR (ExplState.launch s k D θ t) < x →
        stRecR s < x ∧ (∃ v, IsForwardSol (rdrv (recOf t D)) (rProf (stChart s) x : ℂ) (rtime (recOf t D)) v) ∧
        rProf (stChart (ExplState.launch s k D θ t)) x =
          (fwdMap (rdrv (recOf t D)) (rtime (recOf t D)) (rProf (stChart s) x)).re := by
  obtain ⟨hconf, hc, hm, hpos, hcont, hu, harc, hphys⟩ := hs
  have hmin : min t D.2 ≠ ⊤ := by rw [min_eq_left htD.le]; exact ht
  obtain ⟨hch, -, hrec, -, -, -⟩ := launch_eq_of_ne_top s k D θ t hmin
  have hgood := isDrvGood_recOf_tip hreg ht htD
  have hWr : rdrv (recOf t D) = stopDrv t D := by rw [rdrv_recOf]; exact recDrv_eq_stopDrv hreg hgood
  rw [hWr, rtime_recOf]
  set W := stopDrv t D with hWdef
  set T := stopTime t D with hTdef
  have hW : Continuous W := by rw [← hWr]; exact continuous_rdrv _
  have hW0 : W 0 = 0 := stopDrv_zero hreg t
  have hT0 : 0 ≤ T := stopTime_nonneg t D
  have hH := (isRealFlow_stop hreg hgood).1
  set A : ℝ → Prop := fun y : ℝ => ∃ v, IsForwardSol W (y : ℂ) T v with hAdef
  set f : ℝ → ℝ := fun y => (fwdMap W T y).re with hfdef
  set m := rProf (stChart s) with hmdef
  have hrec' : stRecR (ExplState.launch s k D θ t) = newRec m (stRecR s) A := by
    rw [hrec, lRecR_eq_newRec hc]
  have hprof : rProf (stChart (ExplState.launch s k D θ t)) = fun x => f (m x) := by
    funext x
    rw [hch]
    change (fwdMap W T ((stChart s).1 x)).re = (fwdMap W T (m x : ℂ)).re
    rw [hc.eq_ofReal x]
  have hle := le_newRec hm hH
  -- the new chart at an untouched point
  have hnew : ∀ x, newRec m (stRecR s) A < x → stRecR s < x ∧ 0 < m x ∧ A (m x) := fun x hx =>
    ⟨hle.trans_lt hx, pos_alive_of_newRec_lt hm hH hx⟩
  refine ⟨⟨?_, fun x => ?_, ?_, fun x hx => ?_, fun x hx => ?_, ?_, ?_, ?_⟩, ?_, ?_, fun x hx => ?_⟩
  · rw [hch]; exact hconf.loewner hW hW0 hT0
  · rw [hch]
    change (fwdMap W T ((stChart s).1 x)).im = 0
    rw [hc.eq_ofReal x]
    exact im_fwdMap_ofReal W hT0 _
  · rw [hprof, hrec']; exact rightGood_comp hm hH
  · rw [hrec'] at hx
    obtain ⟨-, h0, hA⟩ := hnew x hx
    rw [hprof]; exact hH.2.2.2.1 _ h0 hA
  · rw [hrec'] at hx
    obtain ⟨hx0, -, v, hv⟩ := hnew x hx
    have h1 := hcont x hx0
    rw [hc.eq_ofReal x] at h1
    have h2 := tendsto_fwdMap_of_isForwardSol hW hT0 hv
    have h3 : fwdMap W T (m x : ℂ) = v T := fwdMap_eq_of_isForwardSol hW hv ⟨hT0, le_rfl⟩
    rw [hch]
    change Tendsto (fun z => fwdMap W T ((stChart s).1 z)) (𝓝[H] (x : ℂ))
      (𝓝[H] (fwdMap W T ((stChart s).1 x)))
    rw [hc.eq_ofReal x, h3]
    exact tendsto_nhdsWithin_iff.2 ⟨h2.comp h1,
      h1.eventually (eventually_fwdMap_mem_H hW hT0 hv)⟩
  · rw [hrec']; exact hu.trans hle
  · rw [arcs_launch]; exact harc
  · -- every real point of a piece is at most the new record
    intro p hp z hz him
    rw [CounterflowRange.pieces_launch, List.mem_append, List.mem_singleton] at hp
    rw [hrec']
    rcases hp with hp | rfl
    · exact (hphys p hp z hz him).trans hle
    · by_contra hgt
      push Not at hgt
      obtain ⟨hx0, -, v, hv⟩ := hnew z.re hgt
      obtain ⟨t', ht', hlim⟩ := hz
      change Tendsto (fun y : ℝ => (stChart s).2.1 (fwdMapInv W t' (y * Complex.I))) (𝓝[>] 0) (𝓝 z) at hlim
      have ht'0 : (0 : ℝ) ≤ t' := t'.coe_nonneg
      have ht'T : (t' : ℝ) ≤ T := by
        have h1 : t' ≤ (min t D.2).toNNReal := by
          have := ENNReal.toNNReal_mono hmin ht'
          rwa [ENNReal.toNNReal_coe] at this
        exact_mod_cast h1
      have hz' : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him])
      have hvH : ∀ y : ℝ, 0 < y → fwdMapInv W t' (y * Complex.I) ∈ H := fun y hy =>
        QuantumZipper.RS.fwdMapInv_mem_H hW hW0 ht'0 (by change 0 < ((y : ℂ) * Complex.I).im; simpa using hy)
      have hA1 : Tendsto (fun y : ℝ => (stChart s).2.1 (fwdMapInv W t' (y * Complex.I))) (𝓝[>] 0)
          (𝓝[H] (z.re : ℂ)) := by
        rw [hz'] at hlim
        exact tendsto_nhdsWithin_iff.2 ⟨hlim, eventually_nhdsWithin_of_forall fun y hy =>
          hconf.2.1 (hvH y hy)⟩
      have hA2 := (hcont z.re hx0).comp hA1
      rw [hc.eq_ofReal z.re] at hA2
      have hA3 : Tendsto (fun y : ℝ => fwdMapInv W t' (y * Complex.I)) (𝓝[>] 0) (𝓝[H] (m z.re : ℂ)) :=
        hA2.congr' (eventually_nhdsWithin_of_forall fun y hy => hconf.2.2 _ (hvH y hy))
      have hv' := QuantumZipper.isForwardSol_restrict hv ht'0 ht'T
      have h4 := (tendsto_fwdMap_of_isForwardSol hW ht'0 hv').comp hA3
      have h5 : (fun y : ℝ => fwdMap W t' (fwdMapInv W t' (y * Complex.I))) =ᶠ[𝓝[>] 0]
          fun y : ℝ => (y : ℂ) * Complex.I :=
        eventually_nhdsWithin_of_forall fun y hy =>
          QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 ht'0
            (by change 0 < ((y : ℂ) * Complex.I).im; simpa using hy)
      have h6 : Tendsto (fun y : ℝ => (y : ℂ) * Complex.I) (𝓝[>] 0) (𝓝 0) := by
        have : Continuous fun y : ℝ => (y : ℂ) * Complex.I := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      have h7 : v t' = 0 := tendsto_nhds_unique (h4.congr' h5) h6
      exact (hv'.2 t' ⟨ht'0, le_rfl⟩).1 h7
  · rw [hrec']; exact hle
  · intro z hz hz'
    rw [hrec'] at hz'
    exact not_alive_of_lt_newRec hm hpos hH hz hz'
  · rw [hrec'] at hx
    obtain ⟨hx0, -, hA⟩ := hnew x hx
    refine ⟨hx0, hA, ?_⟩
    rw [hprof]

end Launch

end InteractingSLE.Theorem14.SB.Lh
