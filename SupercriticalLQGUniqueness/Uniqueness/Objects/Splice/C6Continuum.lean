import SupercriticalLQGUniqueness.Uniqueness.Objects.Splice.C6Index
import SupercriticalLQGUniqueness.Uniqueness.Objects.Compare.GridCover



 
set_option autoImplicit false
noncomputable section
open Set Metric
namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Splice
open SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent

 
theorem narrow_scale_geometry (C : Constants) (n : ℕ) :
    narrowScale C n = (2:ℝ)^(-(n:ℝ))*C.r/2 ∧
    (2:ℝ)^(-(n:ℝ)-4)*C.r = (2:ℝ)^(-(n:ℝ))*C.r/16 := by
  constructor
  · unfold narrowScale
    rw [show -(n:ℝ)-1 = -(n:ℝ)-1 by ring,
      Real.rpow_sub (by norm_num : (0:ℝ)<2)]
    norm_num
    ring
  · rw [Real.rpow_sub (by norm_num : (0:ℝ)<2)]
    norm_num
    ring

 

theorem narrow_pair_power (C : Constants) {n : ℕ} {d : ℝ}
    (hd : 0 ≤ d) (hhi : d ≤ (2:ℝ)^(-(n:ℝ)+1)*C.r) :
    (d/C.r)^(C.ξ*(C.Q+3)) ≤
      (2:ℝ)^(-(((n:ℝ)-1)*(C.ξ*(C.Q+3)))) := by
  have ha : 0 ≤ C.ξ*(C.Q+3) :=
    mul_nonneg C.ξPos.le (by linarith [C.QPos])
  have hfrac : d/C.r ≤ (2:ℝ)^(-(n:ℝ)+1) := by
    apply (div_le_iff₀ C.rPos).2
    simpa only [mul_comm] using hhi
  have hp := Real.rpow_le_rpow (div_nonneg hd C.rPos.le) hfrac ha
  have heq : ((2:ℝ)^(-(n:ℝ)+1))^(C.ξ*(C.Q+3)) =
      (2:ℝ)^(-(((n:ℝ)-1)*(C.ξ*(C.Q+3)))) := by
    rw [← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    congr 1
    ring
  exact hp.trans_eq heq

 
theorem large_ann_subset (C : Constants) :
    ann 0 (1.5*C.r) (3*C.r) ⊆ ann 0 C.r (4*C.r) := by
  intro z hz
  exact ⟨by nlinarith [hz.1, C.rPos], by nlinarith [hz.2, C.rPos]⟩

 

theorem narrow_continuum_pair (C : Constants) (D : LSCMetric)
    (g : LQGMetric.DistC) (hS6 : S6 C D g)
    (p : (ann 0 C.r (4*C.r)) × (ann 0 C.r (4*C.r)))
    (hz : (p.1 : ℂ) ∈ ann 0 (1.5*C.r) (3*C.r))
    (_hw : (p.2 : ℂ) ∈ ann 0 (1.5*C.r) (3*C.r))
    (hwindow : dist (p.1 : ℂ) (p.2 : ℂ) ≤
      C.A_nar/C.lamConst*C.r) :
    ENNReal.ofReal
      ((dist (p.1 : ℂ) (p.2 : ℂ) / C.r)^(C.ξ*(C.Q+3))) *
        normalizer C g C.r 0 ≤ D.internal (ann 0 C.r (4*C.r)) p := by
  let d := dist (p.1 : ℂ) (p.2 : ℂ)
  by_cases hd0 : d = 0
  · have hexp : C.ξ*(C.Q+3) ≠ 0 :=
      (mul_pos C.ξPos (by linarith [C.QPos])).ne'
    simp [d, hd0, hexp]
  have hd : 0 < d := lt_of_le_of_ne dist_nonneg (Ne.symm hd0)
  obtain ⟨n, hn, hlo, hhi⟩ := exists_narrow_index C hd hwindow
  let t : ℝ := (2:ℝ)^(-(n:ℝ))*C.r
  let a : ℝ := (2:ℝ)^(-(n:ℝ)-4)*C.r
  let s : ℝ := narrowScale C n
  have ht : 0 < t := mul_pos (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _) C.rPos
  have hgeom := narrow_scale_geometry C n
  have hs : s = t/2 := hgeom.1
  have ha : a = t/16 := hgeom.2
  have haPos : 0 < a := by rw [ha]; positivity
  have hmesh : a ≤ s/4 := by rw [ha, hs]; linarith
  have hfar : s+a < d := by rw [hs, ha]; linarith
  let U : Set ℂ := ann 0 C.r (4*C.r)
  have hUK : U ⊆ closedBall 0 (4*C.r) := by
    intro x hx
    exact Metric.mem_closedBall.mpr hx.2.le
  have hsite : (p.1 : ℂ) ∈ cann 0 (1.5*C.r) (3*C.r) :=
    ⟨hz.1.le, hz.2.le⟩
  obtain ⟨v, hvgrid, hvnear, hacr⟩ :=
    Objects.Compare.narrow_grid_acr_le_internal D (p := p)
      (S := cann 0 (1.5*C.r) (3*C.r))
      (K := closedBall 0 (4*C.r)) (isCompact_closedBall 0 (4*C.r)) hUK
      haPos hmesh hfar hsite
  have hv : v ∈ narrowSites C n := ⟨hvgrid, hvnear⟩
  have htest := narrow_test_lower C D g hS6 hn hv
  have hpow := narrow_pair_power C dist_nonneg hhi
  calc
    ENNReal.ofReal ((d/C.r)^(C.ξ*(C.Q+3))) * normalizer C g C.r 0
      ≤ ENNReal.ofReal
          ((2:ℝ)^(-(((n:ℝ)-1)*(C.ξ*(C.Q+3))))) *
          normalizer C g C.r 0 := by
            gcongr
    _ ≤ acr D v (narrowScale C n/4) (narrowScale C n) := htest
    _ ≤ D.internal U p := by
      simpa only [a, s, U] using hacr

 
theorem narrow_continuum (C : Constants) (D : LSCMetric)
    (g : LQGMetric.DistC) (hS6 : S6 C D g)
    {z w : ℂ} (hz : z ∈ ann 0 (1.5*C.r) (3*C.r))
    (hw : w ∈ ann 0 (1.5*C.r) (3*C.r))
    (hwindow : dist z w ≤ C.A_nar/C.lamConst*C.r) :
    ENNReal.ofReal ((dist z w/C.r)^(C.ξ*(C.Q+3))) *
      normalizer C g C.r 0 ≤
      D.internal (ann 0 C.r (4*C.r))
        (⟨z, large_ann_subset C hz⟩, ⟨w, large_ann_subset C hw⟩) := by
  exact narrow_continuum_pair C D g hS6
    (⟨z, large_ann_subset C hz⟩, ⟨w, large_ann_subset C hw⟩)
    hz hw hwindow

 
theorem event_narrow_continuum {C : Constants} {T : TubeData}
    {hData : DataMatch C T} {F : ℂ → LQGMetric.DistC → Prop}
    {D D' : LQGMetric.DistC → LSCMetric} {g : LQGMetric.DistC}
    (h : correctedEvent C T hData F D D' g)
    {z w : ℂ} (hz : z ∈ ann 0 (1.5*C.r) (3*C.r))
    (hw : w ∈ ann 0 (1.5*C.r) (3*C.r))
    (hwindow : dist z w ≤ C.A_nar/C.lamConst*C.r) :
    ENNReal.ofReal ((dist z w/C.r)^(C.ξ*(C.Q+3))) *
      normalizer C g C.r 0 ≤
      (D g).internal (ann 0 C.r (4*C.r))
        (⟨z, large_ann_subset C hz⟩, ⟨w, large_ann_subset C hw⟩) := by
  obtain ⟨_, _, _, _, _, hS6, _, _, _⟩ := h
  exact narrow_continuum C (D g) g hS6 hz hw hwindow

end SupercriticalLQGUniqueness.Uniqueness.Objects.Splice
