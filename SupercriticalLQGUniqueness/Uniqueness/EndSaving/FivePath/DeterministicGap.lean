import SupercriticalLQGUniqueness.Uniqueness.EndSaving.FivePath.Rate




 



set_option autoImplicit false
noncomputable section

open scoped ENNReal
open LQGMetric (DistC)

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.FivePath

 


theorem deterministic_gap_at_scales
    {Ω : Type} [MeasurableSpace Ω] (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (ω : Ω) (c : NNReal) (hc : 0 < c)
    (b : Set.Ioi (0 : ℝ)) (a : Set.Ioo (3 / 4 : ℝ) 1)
    (θ ν δ : Set.Ioi (0 : ℝ))
    (hmesh : 100 * (δ : ℝ) ^ (ν : ℝ) ≤ 1 - (a : ℝ))
    (hinner : 2 * (δ : ℝ) ^ (ν : ℝ) ≤ (1 - (a : ℝ)) ^ 4)
    (herror :
      2 * (c : ℝ) *
        ((2 * (δ : ℝ) ^ (ν : ℝ)) ^ ((θ : ℝ) / 2) +
          (2 * (δ : ℝ) ^ (ν : ℝ)) ^ (θ : ℝ)) <
        ((1 - (a : ℝ)) / 4) * (δ : ℝ))
    (hcoef : ((1 - (a : ℝ)) / 4) * (δ : ℝ) < (c : ℝ))
    (hDlen : (D (h ω)).IsLengthSpace)
    (hD'len : (D' (h ω)).IsLengthSpace)
    (hDreg : ∀ (P : ℝ → ℂ) (t₁ t₂ : ℝ),
      (D (h ω)).IsCurve P t₁ t₂ → ContinuousOn P (Set.Icc t₁ t₂))
    (hD'reg : ∀ (P : ℝ → ℂ) (t₁ t₂ : ℝ),
      (D' (h ω)).IsCurve P t₁ t₂ → ContinuousOn P (Set.Icc t₁ t₂))
    (hcomp : ∀ z w : ℂ,
      (D' (h ω)) (z, w) ≤ (c : ℝ≥0∞) * (D (h ω)) (z, w))
    (hEnd : ω ∈ EndSaving.Interfaces.ClosedEndSaving h D D' ξ Q (c : ℝ≥0∞)
      b ν δ ⟨(1 - (a : ℝ)) / 2,
        by exact div_pos (sub_pos.mpr a.property.2) (by norm_num)⟩)
    (u v : ℂ)
    (hu : u ∈ Metric.sphere (0 : ℂ) ((a : ℝ) * b))
    (hv : v ∈ Metric.sphere (0 : ℂ) b)
    (hDfinite : (D (h ω)) (u, v) < ⊤)
    (hLoopU : OptimalConstants.Ratios.EndpointLoop (D (h ω)) b a θ u v u)
    (hLoopV : OptimalConstants.Ratios.EndpointLoop (D (h ω)) b a θ u v v)
    (hbrH : ℝ) (hCircleH : IsCircleAverage (h ω) b 0 hbrH)
    (hDist : (D (h ω)) (u, v) ≤ ENNReal.ofReal
      ((1 - (a : ℝ))⁻¹ * (b : ℝ) ^ ((ξ : ℝ) * Q) *
        Real.exp ((ξ : ℝ) * hbrH))) :
    (D' (h ω)) (u, v) <
      ENNReal.ofReal ((c : ℝ) - ((1 - (a : ℝ)) / 4) * (δ : ℝ)) *
        (D (h ω)) (u, v) := by
  obtain ⟨hbr, hCircle, hAll⟩ := hEnd
  let s : ℝ := (δ : ℝ) ^ (ν : ℝ) * (b : ℝ)
  have hs : 0 < s := mul_pos (Real.rpow_pos_of_pos δ.property _) b.property
  have hmeshB : 100 * s ≤ (1 - (a : ℝ)) * (b : ℝ) := by
    dsimp [s]
    have h := mul_le_mul_of_nonneg_right hmesh b.property.le
    nlinarith only [h]
  obtain ⟨i, j, hz, hw, huz, hvw, hsep, hclear⟩ :=
    endpoint_mesh_centers b a s hs hmeshB u v hu hv
  let z := LQGMetric.GM.gridPt (s / 100) i
  let w := LQGMetric.GM.gridPt (s / 100) j
  have hgap : OptimalConstants.Ratios.setDist (D' (h ω)) (Metric.closedBall z s)
        (Metric.closedBall w s) +
      ENNReal.ofReal ((δ : ℝ) * (b : ℝ) ^ ((ξ : ℝ) * Q) *
        Real.exp ((ξ : ℝ) * hbr)) <
      (c : ℝ≥0∞) * OptimalConstants.Ratios.setDist (D (h ω))
        (Metric.closedBall z s) (Metric.closedBall w s) := by
    exact hAll i j hz hw hsep hclear
  let inner : ℝ := 2 * (δ : ℝ) ^ (ν : ℝ)
  have hInner0 : 0 < inner := by
    dsimp [inner]
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos δ.property _)
  have hRadius : inner * (b : ℝ) = 2 * s := by
    dsimp [inner, s]
    ring
  let N : ℝ := (b : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hbr)
  let x : ℝ := ((1 - (a : ℝ)) / 4) * (δ : ℝ)
  let err : ℝ := 2 * (c : ℝ) *
    (inner ^ ((θ : ℝ) / 2) + inner ^ (θ : ℝ))
  have hx0 : 0 < x := by
    dsimp [x]
    exact mul_pos (div_pos (sub_pos.mpr a.property.2) (by norm_num)) δ.property
  have herr0 : 0 ≤ err := by
    dsimp [err, inner]
    positivity
  have herr : err < x := herror
  have hxC : x < (c : ℝ) := hcoef
  have hN0 : 0 < N := by
    dsimp [N]
    exact mul_pos (Real.rpow_pos_of_pos b.property _) (Real.exp_pos _)
  have hDist' : (D (h ω)) (u, v) ≤ ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * N) := by
    have hEq : hbrH = hbr := tendsto_nhds_unique hCircleH hCircle
    rw [hEq] at hDist
    simpa only [N, mul_assoc] using hDist
  have haGap : 0 < 1 - (a : ℝ) := sub_pos.mpr a.property.2
  have hScoef : 0 ≤ (1 - (a : ℝ)) * (δ : ℝ) :=
    mul_nonneg haGap.le δ.property.le
  have hSave : ENNReal.ofReal (4 * x) * (D (h ω)) (u, v) ≤
      ENNReal.ofReal ((δ : ℝ) * N) := by
    have h4x : 4 * x = (1 - (a : ℝ)) * (δ : ℝ) := by
      dsimp [x]
      ring
    calc
      ENNReal.ofReal (4 * x) * (D (h ω)) (u, v) ≤
          ENNReal.ofReal (4 * x) *
            ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * N) := by gcongr
      _ = ENNReal.ofReal ((δ : ℝ) * N) := by
        rw [h4x, ← ENNReal.ofReal_mul hScoef]
        congr 1
        field_simp [haGap.ne']
  have hFive := five_path_closed_ball_bound (D (h ω)) (D' (h ω))
    c hc hDlen hD'len hDreg hD'reg hcomp b a θ
    inner s hInner0 (by simpa only [inner] using hinner)
    hRadius u v z w huz hvw hu hv hLoopU hLoopV
    (ENNReal.ofReal ((δ : ℝ) * N))
    (by simpa only [N, mul_assoc] using hgap)
  have hPaid : (D' (h ω)) (u, v) +
      ENNReal.ofReal (4 * x) * (D (h ω)) (u, v) ≤
      ENNReal.ofReal (c : ℝ) * (D (h ω)) (u, v) +
        ENNReal.ofReal err * (D (h ω)) (u, v) := by
    calc
      _ ≤ (D' (h ω)) (u, v) + ENNReal.ofReal ((δ : ℝ) * N) :=
        add_le_add_right hSave _
      _ ≤ (c : ℝ≥0∞) * (D (h ω)) (u, v) +
          ENNReal.ofReal err * (D (h ω)) (u, v) := hFive
      _ = _ := by rw [ENNReal.ofReal_coe_nnreal]
  have hu0 : dist u (0 : ℂ) = (a : ℝ) * b := by
    simpa only [Metric.mem_sphere] using hu
  have hv0 : dist v (0 : ℂ) = (b : ℝ) := by
    simpa only [Metric.mem_sphere] using hv
  have huv : u ≠ v := by
    intro heq
    rw [heq] at hu0
    have hlt := mul_lt_mul_of_pos_right a.property.2 b.property
    rw [one_mul] at hlt
    linarith only [hu0, hv0, hlt]
  have hD0 : 0 < (D (h ω)) (u, v) := by
    apply pos_iff_ne_zero.mpr
    intro hzero
    exact huv ((D (h ω)).isExtMetric.2.1 u v hzero)
  exact strict_ratio_of_paid_saving ((D (h ω)) (u, v)) ((D' (h ω)) (u, v))
    hD0 hDfinite (c : ℝ) x err hx0 hxC herr0 herr hPaid

 


theorem deterministic_five_path_gap
    {Ω : Type} [MeasurableSpace Ω] (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (c : NNReal) (hc : 0 < c)
    (a : Set.Ioo (3 / 4 : ℝ) 1) (θ ν : Set.Ioi (0 : ℝ))
    (hν : 2 / (θ : ℝ) < (ν : ℝ)) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧
      ∀ δ : ℝ, (hδ : 0 < δ) → δ ≤ δ₀ →
      ∀ b : Set.Ioi (0 : ℝ), ∀ ω : Ω,
      (D (h ω)).IsLengthSpace →
      (D' (h ω)).IsLengthSpace →
      (∀ (P : ℝ → ℂ) (t₁ t₂ : ℝ),
        (D (h ω)).IsCurve P t₁ t₂ → ContinuousOn P (Set.Icc t₁ t₂)) →
      (∀ (P : ℝ → ℂ) (t₁ t₂ : ℝ),
        (D' (h ω)).IsCurve P t₁ t₂ → ContinuousOn P (Set.Icc t₁ t₂)) →
      (∀ z w : ℂ,
        (D' (h ω)) (z, w) ≤ (c : ℝ≥0∞) * (D (h ω)) (z, w)) →
      ω ∈ EndSaving.Interfaces.ClosedEndSaving h D D' ξ Q (c : ℝ≥0∞)
        b ν ⟨δ, hδ⟩
        ⟨(1 - (a : ℝ)) / 2,
          by exact div_pos (sub_pos.mpr a.property.2) (by norm_num)⟩ →
      ∀ u v : ℂ,
      u ∈ Metric.sphere (0 : ℂ) ((a : ℝ) * b) →
      v ∈ Metric.sphere (0 : ℂ) b →
      (D (h ω)) (u, v) < ⊤ →
      OptimalConstants.Ratios.EndpointLoop (D (h ω)) b a θ u v u →
      OptimalConstants.Ratios.EndpointLoop (D (h ω)) b a θ u v v →
      ∀ hbrH : ℝ, IsCircleAverage (h ω) b 0 hbrH →
      (D (h ω)) (u, v) ≤ ENNReal.ofReal
        ((1 - (a : ℝ))⁻¹ * (b : ℝ) ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * hbrH)) →
      (D' (h ω)) (u, v) <
        ENNReal.ofReal ((c : ℝ) - ((1 - (a : ℝ)) / 4) * δ) *
          (D (h ω)) (u, v) := by
  obtain ⟨δ₀, hδ₀, hδ₀one, hsmall⟩ :=
    exists_uniform_R53_scale a θ c hc ν hν
  refine ⟨δ₀, hδ₀, hδ₀one, ?_⟩
  intro δ hδ hδle b ω hDlen hD'len hDreg hD'reg hcomp hEnd
    u v hu hv hDfinite hLoopU hLoopV hbrH hCircleH hDist
  obtain ⟨hmesh, hinner, herror, hcoef⟩ := hsmall δ hδ hδle
  exact deterministic_gap_at_scales h D D' ξ Q ω c hc b a θ ν
    ⟨δ, hδ⟩ hmesh hinner herror hcoef hDlen hD'len hDreg
    hD'reg hcomp hEnd u v hu hv hDfinite hLoopU hLoopV
    hbrH hCircleH hDist


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.FivePath
