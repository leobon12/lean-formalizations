import SupercriticalLQGUniqueness.B2.Median.PathSelection

 







set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Median

 




theorem ae_shifted_circle_convergence_of_subseqLimit
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (D : LQGMetric.DistC → LSCMetric)
    (hsub : B2.Iface.SubseqLimit ξ m ε D)
    (h : Ω → LQGMetric.DistC) (hh : LQGMetric.IsGFFPlusBddCont h P)
    (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ z, |f z| ≤ M)
    (O₁ O₂ : Set ℂ) (hO₁ : B2.Iface.IsRationalCircle O₁)
    (hO₂ : B2.Iface.IsRationalCircle O₂) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n => ENNReal.ofReal ((m (ε n) : ℝ)⁻¹) *
        B2.Iface.setDistance
          (lfppDistance (ξ : ℝ)
            (X (ε n) ω + LQGMetric.LFPP.mollCont (ε n : ℝ)
              (ε n).property.ne' f M hM)) O₁ O₂) atTop
        (𝓝 (B2.Iface.setDistance (D (LQGMetric.addFun (h ω) f)).1 O₁ O₂)) := by
  have hh' := isGFFPlusBddCont_addFun P h hh f M hM
  have hX' : ∀ δ, IsHeatSmoothing P
      (fun ω => LQGMetric.addFun (h ω) f) δ
      (fun ω => X δ ω + LQGMetric.LFPP.mollCont (δ : ℝ)
        δ.property.ne' f M hM) := by
    intro δ
    exact isHeatSmoothing_addFun P h δ (X δ) (hX δ) f M hM
  exact (hsub P (fun ω => LQGMetric.addFun (h ω) f) hh' _ hX').2
    O₁ O₂ hO₁ hO₂

 


theorem ae_shifted_circle_convergence_weyl_of_inputs
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (D : LQGMetric.DistC → LSCMetric)
    (hsub : B2.Iface.SubseqLimit ξ m ε D)
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hweak : B2.Iface.IsPfeWeakMetric ξ D c)
    (h : Ω → LQGMetric.DistC) (hh : LQGMetric.IsGFFPlusBddCont h P)
    (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ z, |f z| ≤ M)
    (O₁ O₂ : Set ℂ) (hO₁ : B2.Iface.IsRationalCircle O₁)
    (hO₂ : B2.Iface.IsRationalCircle O₂) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n => ENNReal.ofReal ((m (ε n) : ℝ)⁻¹) *
        B2.Iface.setDistance
          (lfppDistance (ξ : ℝ)
            (X (ε n) ω + LQGMetric.LFPP.mollCont (ε n : ℝ)
              (ε n).property.ne' f M hM)) O₁ O₂) atTop
        (𝓝 (B2.Iface.setDistance (weylScale (ξ : ℝ) f (D (h ω))) O₁ O₂)) := by
  obtain ⟨_, _, _, hweyl, _, _, _⟩ := hweak
  have hhcont : LQGMetric.IsGFFPlusCont h P := by
    obtain ⟨hm, g, hgm, _, hgff⟩ := hh
    exact ⟨hm, g, hgm, hgff⟩
  have hconv := ae_shifted_circle_convergence_of_subseqLimit
    P ξ m ε D hsub h hh X hX f M hM O₁ O₂ hO₁ hO₂
  filter_upwards [hconv, hweyl P h hhcont] with ω hlim hw
  simpa only [← hw f] using hlim

 

theorem ae_lfppMetric_tendsto_of_subseqLimit
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (D : LQGMetric.DistC → LSCMetric)
    (hsub : B2.Iface.SubseqLimit ξ m ε D)
    (h : Ω → LQGMetric.DistC) (hh : LQGMetric.IsGFFPlusBddCont h P)
    (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ)) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n => lfppMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω))
      atTop (𝓝 (D (h ω))) := by
  have hlim := (hsub P h hh X hX).1
  filter_upwards [hlim] with ω hω
  apply LSCMetric.tendsto_iff.mpr
  apply LSCMetric.lscTendsto_toLSCFun_iff.mp
  simpa only [lfppMetric_toLSCFun] using hω

theorem barrier_crossing_eventually_lt
    (ξ : Set.Ioi (0 : ℝ))
    (ε a : ℕ → Set.Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (φ : ℕ → C(ℂ, ℝ)) (d : LSCMetric)
    (hG : Tendsto (fun n => lfppMetric (ξ : ℝ) (a n) (φ n)) atTop (𝓝 d))
    (N : Set ℂ) (ρ : Set.Ioi (0 : ℝ)) (M : ℝ) (hM : 0 < M)
    (R : ℝ) (hR : 0 < R)
    (hK : IsCompact {z : ℂ | Metric.infDist z N ≤ (ρ : ℝ)})
    (hKball : {z : ℂ | Metric.infDist z N ≤ (ρ : ℝ)} ⊆ closedBall 0 R)
    (hne : ({p : ℂ × ℂ |
      Metric.infDist p.1 N ≤ (ρ : ℝ) ∧
      Metric.infDist p.2 N ≤ (ρ : ℝ) ∧
      (ρ : ℝ) / 2 ≤ dist p.1 p.2}).Nonempty)
    (hstrip : ∀ z : ℂ, Metric.infDist z N ≤ (ρ : ℝ) →
      0 ≤ z.im ∧ z.im ≤ 1)
    (O₁ O₂ : Set ℂ) (hO₁N : O₁ ⊆ N)
    (hO₁left : ∀ z ∈ O₁, z.re ≤ 0)
    (hO₂right : ∀ w ∈ O₂, 1 ≤ w.re) :
    ∃ μ : ℝ≥0∞, 0 < μ ∧
      ∀ (W L : ℝ≥0∞),
        Tendsto (fun n => ENNReal.ofReal ((a n : ℝ)⁻¹) *
          B2.Iface.setDistance
            (lfppDistance (ξ : ℝ)
              (φ n + LQGMetric.LFPP.mollCont (ε n : ℝ)
                (ε n).property.ne' (penaltyField N ρ M) M
                (penaltyField_abs_le N ρ hM.le))) O₁ O₂) atTop (𝓝 W) →
        W < L →
        L ≤ ENNReal.ofReal (Real.exp ((ξ : ℝ) * (M / 4))) * μ →
        ∀ᶠ n in atTop,
          ENNReal.ofReal ((a n : ℝ)⁻¹) *
            lfppCrossingLength (ξ : ℝ) (φ n) < L := by
  obtain ⟨μ, hμ, hbar⟩ :=
    eventually_crossing_le_shifted_path_of_barrier ξ ε a hε φ d hG
      N ρ M hM R hR hK hKball hne hstrip
  refine ⟨μ, hμ, ?_⟩
  intro W L hlim hWL hLT
  let F : ℕ → C(ℂ, ℝ) := fun n => φ n +
    LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne'
      (penaltyField N ρ M) M (penaltyField_abs_le N ρ hM.le)
  have hbar' : ∀ᶠ n in atTop, ∀ (P : ℝ → ℂ) (z w : ℂ),
      LQGMetric.IsPiecewiseC1Path P z w → z ∈ O₁ → w ∈ O₂ →
      ENNReal.ofReal ((a n : ℝ)⁻¹) *
        LQGMetric.lfppLen (ξ : ℝ) (F n) P <
          ENNReal.ofReal (Real.exp ((ξ : ℝ) * (M / 4))) * μ →
      ENNReal.ofReal ((a n : ℝ)⁻¹) *
        lfppCrossingLength (ξ : ℝ) (φ n) ≤
      ENNReal.ofReal ((a n : ℝ)⁻¹) *
        LQGMetric.lfppLen (ξ : ℝ) (F n) P := by
    filter_upwards [hbar] with n hn P z w hP hz hw hcost
    exact hn P z w hP (hO₁N hz) (hO₁left z hz) (hO₂right w hw) hcost
  exact eventually_crossing_lt_of_barrier (ξ : ℝ) a φ F O₁ O₂
    (ENNReal.ofReal (Real.exp ((ξ : ℝ) * (M / 4))) * μ)
    W L hbar' hlim hWL hLT

 


theorem ae_barrier_crossing_eventually_lt_of_inputs
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : LQGMetric.DistC → LSCMetric)
    (hsub : B2.Iface.SubseqLimit ξ m ε D)
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hweak : B2.Iface.IsPfeWeakMetric ξ D c)
    (h : Ω → LQGMetric.DistC) (hh : LQGMetric.IsGFFPlusBddCont h P)
    (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (N : Set ℂ) (ρ : Set.Ioi (0 : ℝ)) (M : ℝ) (hM : 0 < M)
    (R : ℝ) (hR : 0 < R)
    (hK : IsCompact {z : ℂ | Metric.infDist z N ≤ (ρ : ℝ)})
    (hKball : {z : ℂ | Metric.infDist z N ≤ (ρ : ℝ)} ⊆ closedBall 0 R)
    (hne : ({p : ℂ × ℂ |
      Metric.infDist p.1 N ≤ (ρ : ℝ) ∧
      Metric.infDist p.2 N ≤ (ρ : ℝ) ∧
      (ρ : ℝ) / 2 ≤ dist p.1 p.2}).Nonempty)
    (hstrip : ∀ z : ℂ, Metric.infDist z N ≤ (ρ : ℝ) →
      0 ≤ z.im ∧ z.im ≤ 1)
    (O₁ O₂ : Set ℂ) (hO₁ : B2.Iface.IsRationalCircle O₁)
    (hO₂ : B2.Iface.IsRationalCircle O₂)
    (hO₁N : O₁ ⊆ N)
    (hO₁left : ∀ z ∈ O₁, z.re ≤ 0)
    (hO₂right : ∀ w ∈ O₂, 1 ≤ w.re) :
    ∀ᵐ ω ∂P, ∃ μ : ℝ≥0∞, 0 < μ ∧
      ∀ L : ℝ≥0∞,
        B2.Iface.setDistance
          (weylScale (ξ : ℝ) (penaltyField N ρ M) (D (h ω))) O₁ O₂ < L →
        L ≤ ENNReal.ofReal (Real.exp ((ξ : ℝ) * (M / 4))) * μ →
        ∀ᶠ n in atTop,
          ENNReal.ofReal ((m (ε n) : ℝ)⁻¹) *
            lfppCrossingLength (ξ : ℝ) (X (ε n) ω) < L := by
  have hmetric := ae_lfppMetric_tendsto_of_subseqLimit
    P ξ m ε D hsub h hh X hX
  have hshift := ae_shifted_circle_convergence_weyl_of_inputs
    P ξ m ε D hsub c hweak h hh X hX
    (penaltyField N ρ M) M (penaltyField_abs_le N ρ hM.le)
    O₁ O₂ hO₁ hO₂
  filter_upwards [hmetric, hshift] with ω hG hlim
  obtain ⟨μ, hμ, hbound⟩ := barrier_crossing_eventually_lt
    ξ ε (fun n => m (ε n)) hε (fun n => X (ε n) ω)
    (D (h ω)) hG N ρ M hM R hR hK hKball hne hstrip
    O₁ O₂ hO₁N hO₁left hO₂right
  exact ⟨μ, hμ, fun L hWL hLT => hbound _ L hlim hWL hLT⟩

 

theorem limsup_le_of_eventually_lt_between
    (Y : ℕ → ℝ≥0∞) (W T : ℝ≥0∞) (hWT : W < T)
    (hbound : ∀ L : ℝ≥0∞, W < L → L ≤ T →
      ∀ᶠ n in atTop, Y n < L) :
    limsup Y atTop ≤ W := by
  apply (Filter.limsup_le_iff).mpr
  intro y hWy
  have hmin : W < min y T := lt_min hWy hWT
  exact (hbound (min y T) hmin (min_le_right _ _)).mono
    (fun n hn => hn.trans_le (min_le_left _ _))

 


structure BarrierTuple where
  N : Set ℂ
  ρ : Set.Ioi (0 : ℝ)
  M : Set.Ioi (0 : ℝ)
  hNcompact : IsCompact N
  hNnonempty : N.Nonempty
  hstrip : ∀ z : ℂ, Metric.infDist z N ≤ (ρ : ℝ) →
    0 ≤ z.im ∧ z.im ≤ 1
  O₁ : Set ℂ
  O₂ : Set ℂ
  hO₁rat : B2.Iface.IsRationalCircle O₁
  hO₂rat : B2.Iface.IsRationalCircle O₂
  hO₁N : O₁ ⊆ N
  hO₂N : O₂ ⊆ N
  hO₁left : ∀ z ∈ O₁, z.re ≤ 0
  hO₂right : ∀ w ∈ O₂, 1 ≤ w.re

 


theorem ae_forall_barrier_limsup_le_of_inputs
    {Ω ι : Type} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : LQGMetric.DistC → LSCMetric)
    (hsub : B2.Iface.SubseqLimit ξ m ε D)
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hweak : B2.Iface.IsPfeWeakMetric ξ D c)
    (h : Ω → LQGMetric.DistC) (hh : LQGMetric.IsGFFPlusBddCont h P)
    (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (β : ι → BarrierTuple) :
    ∀ᵐ ω ∂P, ∀ i : ι, ∃ μ : ℝ≥0∞, 0 < μ ∧
      (B2.Iface.setDistance
        (weylScale (ξ : ℝ)
          (penaltyField (β i).N (β i).ρ (β i).M) (D (h ω)))
        (β i).O₁ (β i).O₂ <
          ENNReal.ofReal (Real.exp ((ξ : ℝ) * ((β i).M / 4))) * μ →
        limsup (fun n => ENNReal.ofReal ((m (ε n) : ℝ)⁻¹) *
          lfppCrossingLength (ξ : ℝ) (X (ε n) ω)) atTop ≤
        B2.Iface.setDistance
          (weylScale (ξ : ℝ)
            (penaltyField (β i).N (β i).ρ (β i).M) (D (h ω)))
          (β i).O₁ (β i).O₂) := by
  apply (eventually_countable_forall).mpr
  intro i
  let b := β i
  obtain ⟨R, hR, hball⟩ :=
    exists_ball_for_infDist_thickening b.N b.hNcompact b.hNnonempty b.ρ
  have hsingle := ae_barrier_crossing_eventually_lt_of_inputs
    P ξ m ε hε D hsub c hweak h hh X hX
    b.N b.ρ (b.M : ℝ) b.M.property R hR
    (isCompact_infDist_thickening b.N b.hNcompact b.hNnonempty b.ρ)
    hball (separated_pair_in_infDist_thickening b.N b.hNnonempty b.ρ)
    b.hstrip b.O₁ b.O₂ b.hO₁rat b.hO₂rat b.hO₁N b.hO₁left b.hO₂right
  filter_upwards [hsingle] with ω hω
  obtain ⟨μ, hμ, hbound⟩ := hω
  refine ⟨μ, hμ, fun hWT => ?_⟩
  exact limsup_le_of_eventually_lt_between _ _ _ hWT
    (fun L hWL hLT => hbound L hWL hLT)

end SupercriticalLQGUniqueness.B2.Median
