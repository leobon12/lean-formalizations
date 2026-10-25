import SupercriticalLQGUniqueness.Uniqueness.Objects.Compare.GridCover
import SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEventNumerics.Numeric




 





set_option autoImplicit false
noncomputable section
open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Compare

 

theorem compare_continuum (C : Objects.CorrectedEvent.Constants) (D : LSCMetric)
    (hS5 : Objects.CorrectedEvent.S5 C D) {y : ℂ} (hy : y ∈ Objects.CorrectedEvent.ann 0 (1.5*C.r) (3*C.r))
    {δ : ℝ} (hδ : 0 < δ) (hδnar : δ ≤ C.A_nar) :
    Objects.CorrectedEvent.around D y (2*δ*C.r) (3*δ*C.r) ≤
      ENNReal.ofReal (δ ^ (-(1:ℝ)/4)) *
        Objects.CorrectedEvent.acr D y (δ*C.r/4) (δ*C.r/2) := by
  have hδq : δ ≤ (20:ℝ)/21 := hδnar.trans C.narLeQ
  obtain ⟨k, htpos, htlow, htδ⟩ := exists_compare_scale hδ hδq
  let t := Objects.CorrectedEvent.compareScale k
  let e := t*C.r/100
  have he : 0 < e := by
    dsimp [e, t]
    exact div_pos (mul_pos htpos C.rPos) (by norm_num)
  obtain ⟨z, hzgrid, hyz⟩ := exists_grid_near he y
  have hzy : dist z y ≤ e := (dist_comm z y ▸ hyz.le)
  have hsite : z ∈ Objects.CorrectedEvent.compareSites C k := by
    change z ∈ Objects.CorrectedEvent.grid e ∧
      Metric.infDist z (Objects.CorrectedEvent.cann 0 (1.5*C.r) (3*C.r)) ≤ e
    refine ⟨hzgrid, ?_⟩
    have hyc : y ∈ Objects.CorrectedEvent.cann 0 (1.5*C.r) (3*C.r) := ⟨hy.1.le, hy.2.le⟩
    exact (Metric.infDist_le_dist_of_mem hyc).trans hzy
  have hδt : δ < ((21:ℝ)/20)*t := by
    have h := (div_lt_iff₀ (by norm_num : 0 < (21:ℝ)/20)).mp htlow
    nlinarith
  obtain ⟨h1, h2, h3, h4⟩ := Objects.CorrectedEventNumerics.compare_inclusions htpos htδ hδt
  have hgeomAround := nested_annulus_geometry
    (y := y) (z := z) (e := e)
    (a := 2*δ*C.r) (b := 3*δ*C.r)
    (c := (11/5)*t*C.r) (d := (14/5)*t*C.r) hyz.le
    (by
      dsimp [e]
      have h := mul_le_mul_of_nonneg_right h1 C.rPos.le
      nlinarith only [h])
    (by
      dsimp [e]
      have h := mul_le_mul_of_nonneg_right h2 C.rPos.le
      nlinarith only [h])
  have hgeomAcr := nested_annulus_geometry
    (y := y) (z := z) (e := e)
    (a := δ*C.r/4) (b := δ*C.r/2)
    (c := (3/10)*t*C.r) (d := (9/20)*t*C.r) hyz.le
    (by
      dsimp [e]
      have h := mul_le_mul_of_nonneg_right h3.le C.rPos.le
      nlinarith only [h])
    (by
      dsimp [e]
      have h := mul_le_mul_of_nonneg_right h4 C.rPos.le
      nlinarith only [h])
  have hcdAround : (11/5)*t*C.r ≤ (14/5)*t*C.r := by
    nlinarith [htpos, C.rPos]
  have hcdAcr : (3/10)*t*C.r ≤ (9/20)*t*C.r := by
    nlinarith [htpos, C.rPos]
  have hAround := around_le_of_nested_annuli D hcdAround
    hgeomAround.1 hgeomAround.2.1 hgeomAround.2.2
  have hAcr := acr_le_of_nested_annuli D hcdAcr
    hgeomAcr.1 hgeomAcr.2.1
  have htest := hS5 k (htδ.trans hδnar) z hsite
  have hδq' : δ ≤ 1 / ((21:ℝ)/20) := by
    simpa only [show (1:ℝ) / ((21:ℝ)/20) = 20/21 by norm_num] using hδq
  have hpow : t ^ (-(1:ℝ)/8) ≤ δ ^ (-(1:ℝ)/4) :=
    Objects.CorrectedEventNumerics.compare_power (by norm_num : (1:ℝ) < 21/20) hδ hδq' htlow
  have hcoeff : ENNReal.ofReal (t ^ (-(1:ℝ)/8)) ≤
      ENNReal.ofReal (δ ^ (-(1:ℝ)/4)) := ENNReal.ofReal_le_ofReal hpow
  calc
    Objects.CorrectedEvent.around D y (2*δ*C.r) (3*δ*C.r)
        ≤ Objects.CorrectedEvent.around D z ((11/5)*t*C.r) ((14/5)*t*C.r) := hAround
    _ ≤ ENNReal.ofReal (t ^ (-(1:ℝ)/8)) *
        Objects.CorrectedEvent.acr D z ((3/10)*t*C.r) ((9/20)*t*C.r) := htest.1
    _ ≤ ENNReal.ofReal (δ ^ (-(1:ℝ)/4)) *
        Objects.CorrectedEvent.acr D z ((3/10)*t*C.r) ((9/20)*t*C.r) := by gcongr
    _ ≤ ENNReal.ofReal (δ ^ (-(1:ℝ)/4)) *
        Objects.CorrectedEvent.acr D y (δ*C.r/4) (δ*C.r/2) := by gcongr

 
theorem event_compare_continuum {C : Objects.CorrectedEvent.Constants} {T : Objects.CorrectedEvent.TubeData}
    {hData : Objects.CorrectedEvent.DataMatch C T} {F : ℂ → LQGMetric.DistC → Prop}
    {D D' : LQGMetric.DistC → LSCMetric} {g : LQGMetric.DistC}
    (h : Objects.CorrectedEvent.correctedEvent C T hData F D D' g)
    {y : ℂ} (hy : y ∈ Objects.CorrectedEvent.ann 0 (1.5*C.r) (3*C.r))
    {δ : ℝ} (hδ : 0 < δ) (hδnar : δ ≤ C.A_nar) :
    Objects.CorrectedEvent.around (D g) y (2*δ*C.r) (3*δ*C.r) ≤
      ENNReal.ofReal (δ ^ (-(1:ℝ)/4)) *
        Objects.CorrectedEvent.acr (D g) y (δ*C.r/4) (δ*C.r/2) := by
  exact compare_continuum C (D g) h.2.2.2.2.1 hy hδ hδnar


end SupercriticalLQGUniqueness.Uniqueness.Objects.Compare
