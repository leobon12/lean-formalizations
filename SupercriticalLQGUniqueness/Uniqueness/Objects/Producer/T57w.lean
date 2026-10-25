import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.T57c




 












set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Producer

 


structure T57Witness (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (hData : Objects.CorrectedEvent.DataMatch C T)
    (hE : C.A_endpt ≤ 1) (D Dt Db Dtb : LSCMetric) (V : Set ℂ) (N Cmid0 : ℝ) (P : ℝ → ℂ)
    (L τ' τ σ σ' : ℝ) : Type where
   
  k : Fin T.K
   
  u : ℂ
   
  v : ℂ
   
  dt : ℝ
  dt_pos : 0 < dt
  u_mem : u ∈ closedBall (Objects.CorrectedEvent.innerCenter T k) T.blockRadius
  u_near : dist u (Objects.CorrectedEvent.innerCenter T k) < T.blockRadius / 2
  v_mem : v ∈ closedBall (Objects.CorrectedEvent.outerCenter T k) T.blockRadius
  v_near : dist v (Objects.CorrectedEvent.outerCenter T k) < T.blockRadius / 2
  dt_eq : Dt (u, v) = ENNReal.ofReal dt
   
  ratio : ENNReal.ofReal dt ≤ ENNReal.ofReal Cmid0 * D (u, v)
   
  block_cost : ∀ (hu : u ∈ Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (hv : v ∈ Objects.CorrectedEvent.ann 0 C.r (4 * C.r)),
    Dtb.internal (Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (⟨u, hu⟩, ⟨v, hv⟩) ≤
      ENNReal.ofReal (Real.exp (-C.ξ * C.A_max) * dt)
   
  bad_u : Objects.Shadow.circleOuter (Objects.CorrectedEvent.innerCenter T k)
      ⟨T.blockRadius, (blockRadius_bounds C T hData hE).1.le⟩ 0
      (sphere (Objects.CorrectedEvent.innerCenter T k) T.blockRadius \
        goodSet D (Objects.CorrectedEvent.innerCenter T k) u T.blockRadius (C.lamConst * dt) u_mem) ≤
    ENNReal.ofReal (C.lamConst * T.blockRadius / 2)
   
  bad_v : Objects.Shadow.circleOuter (Objects.CorrectedEvent.outerCenter T k)
      ⟨T.blockRadius, (blockRadius_bounds C T hData hE).1.le⟩ 0
      (sphere (Objects.CorrectedEvent.outerCenter T k) T.blockRadius \
        goodSet D (Objects.CorrectedEvent.outerCenter T k) v T.blockRadius (C.lamConst * dt) v_mem) ≤
    ENNReal.ofReal (C.lamConst * T.blockRadius / 2)
   
  τ₀ : ℝ
  σ₀ : ℝ
  τ₀_nonneg : 0 ≤ τ₀
  τ₀_le : τ₀ ≤ τ
  σ₀_ge : σ ≤ σ₀
  σ₀_le : σ₀ ≤ L
  σ₀_norm : ‖P σ₀‖ = 3 * C.r
  σ₀_time : σ₀ - τ₀ ≤ 2 * C.A_around * N
   
  tube : ∀ x ∈ Icc τ σ, P x ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r)
   
  short : σ - τ < C.A_nar ^ (C.ξ * (C.Q + 3)) * N
   
  carrier : ∀ t ∈ Icc τ' σ', P t ∈ Objects.CorrectedEvent.cann 0 C.r (4 * C.r)
   
  carrier_geo : ∀ (ha : P τ' ∈ Objects.CorrectedEvent.cann 0 C.r (4 * C.r)) (hb : P σ' ∈ Objects.CorrectedEvent.cann 0 C.r (4 * C.r)),
    Db.len P τ' σ' = Db.internal (Objects.CorrectedEvent.cann 0 C.r (4 * C.r)) (⟨P τ', ha⟩, ⟨P σ', hb⟩)
   
  au : ℝ
  bu : ℝ
   
  av : ℝ
  bv : ℝ
  τ_le_au : τ ≤ au
  au_lt_bu : au < bu
  bu_le_σ : bu ≤ σ
  τ_le_av : τ ≤ av
  av_lt_bv : av < bv
  bv_le_σ : bv ≤ σ
  Pau : ‖P au - Objects.CorrectedEvent.innerCenter T k‖ = T.blockRadius + C.A_sup * C.r
  Pbu : ‖P bu - Objects.CorrectedEvent.innerCenter T k‖ = T.blockRadius + C.A_sup * C.r
  Pav : ‖P av - Objects.CorrectedEvent.outerCenter T k‖ = T.blockRadius + C.A_sup * C.r
  Pbv : ‖P bv - Objects.CorrectedEvent.outerCenter T k‖ = T.blockRadius + C.A_sup * C.r
  far_u : T.blockRadius / 8 ≤ dist (P au) (P bu)
  far_v : T.blockRadius / 8 ≤ dist (P av) (P bv)
  mid_u : ∀ t ∈ Icc au bu,
    P t ∈ ball (Objects.CorrectedEvent.innerCenter T k) (T.blockRadius + C.A_sup * C.r + C.A_nar * C.r)
  mid_v : ∀ t ∈ Icc av bv,
    P t ∈ ball (Objects.CorrectedEvent.outerCenter T k) (T.blockRadius + C.A_sup * C.r + C.A_nar * C.r)
  win_u : ∀ t ∈ Ioo au bu, P t ∈ V → P t ∈ ball (Objects.CorrectedEvent.innerCenter T k) (T.blockRadius + C.A_sup * C.r)
  win_v : ∀ t ∈ Ioo av bv, P t ∈ V → P t ∈ ball (Objects.CorrectedEvent.outerCenter T k) (T.blockRadius + C.A_sup * C.r)

 
def cInc (C : Objects.CorrectedEvent.Constants) : ℝ := Real.exp (-C.ξ * C.A_max) * C.A_nar ^ (C.ξ * (C.Q + 3))

 
def radius (C : Objects.CorrectedEvent.Constants) : Set.Ioi (0 : ℝ) := ⟨C.r, C.rPos⟩

 
theorem t57_of_witness (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (hData : Objects.CorrectedEvent.DataMatch C T)
    (hE : C.A_endpt ≤ 1) (D Dt Db Dtb : LSCMetric) (f : C(ℂ, ℝ))
    (hLD : D.IsLengthSpace) (hforgetD : Continuous (BiLipschitz.Barrier.forget D)) (hLDt : Dt.IsLengthSpace)
    (hforgetDt : Continuous (BiLipschitz.Barrier.forget Dt))
    (hWD : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    (hWDt : ∀ x y : ℂ, Dtb (x, y) = weylScale C.ξ (-f) Dt (x, y))
    (hf : ∀ x : ℂ, 0 ≤ f x ∧ f x ≤ C.A_max)
    {V : Set ℂ} (hV : IsOpen V) (hfV : ∀ x ∉ V, f x = 0)
    {Cp Cmid0 Cmid : ℝ} (hCp : 0 < Cp) (hCmid0 : 0 ≤ Cmid0) (hCmid : 0 ≤ Cmid)
    (hle : ∀ x y : ℂ, Dt (x, y) ≤ ENNReal.ofReal Cp * D (x, y))
    (hratio : (1 + 10 * Cp * C.lamConst) * Cmid0 ≤ Cmid * (1 - 10 * Cp * C.lamConst))
    {N : ℝ} (hN : 0 < N)
    (hlam : C.lamConst ≤ 1 / 48) (hnar1 : C.A_nar < 1)
    (hsup_s : C.A_sup * C.r ≤ T.blockRadius) (hnar_s : 3 * C.A_nar * C.r ≤ T.blockRadius / 2)
    (hcount : ∀ k : ℕ, (1 / 2 : ℝ) ^ (k + 1) < C.A_nar →
      21 * (((k : ℝ) + 3) * (C.ξ * (C.Q + 3)) + Real.logb 2 (2 * C.A_around) + 2) ≤
        cSel * (T.blockRadius / C.r) * (2 : ℝ) ^ ((k : ℝ) / 4))
    (hnarrow : ∀ (z w : ℂ) (hz : z ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r))
      (hw : w ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r)), dist z w ≤ C.A_nar / C.lamConst * C.r →
      ENNReal.ofReal ((dist z w / C.r) ^ (C.ξ * (C.Q + 3))) * ENNReal.ofReal N ≤
        D.internal (Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (⟨z, mid_ann_subset C hz⟩, ⟨w, mid_ann_subset C hw⟩))
    (hcompare : ∀ y ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r), ∀ δ : ℝ, 0 < δ → δ ≤ C.A_nar →
      Objects.CorrectedEvent.around D y (2 * δ * C.r) (3 * δ * C.r) ≤
        ENNReal.ofReal (δ ^ (-(1 : ℝ) / 4)) * Objects.CorrectedEvent.acr D y (δ * C.r / 4) (δ * C.r / 2))
    (hfB_in : ∀ k : Fin T.K, ∀ x ∈ closedBall (Objects.CorrectedEvent.innerCenter T k) T.blockRadius, f x = C.A_max)
    (hfB_out : ∀ k : Fin T.K, ∀ x ∈ closedBall (Objects.CorrectedEvent.outerCenter T k) T.blockRadius, f x = C.A_max)
    (hAnn_in : ∀ k : Fin T.K, ball (Objects.CorrectedEvent.innerCenter T k)
      (T.blockRadius + C.A_sup * C.r + 3 * C.A_nar * C.r) ⊆ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r))
    (hAnn_out : ∀ k : Fin T.K, ball (Objects.CorrectedEvent.outerCenter T k)
      (T.blockRadius + C.A_sup * C.r + 3 * C.A_nar * C.r) ⊆ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r))
    (hBinA_in : ∀ k : Fin T.K,
      closedBall (Objects.CorrectedEvent.innerCenter T k) T.blockRadius ⊆ Objects.CorrectedEvent.ann 0 C.r (4 * C.r))
    (hBinA_out : ∀ k : Fin T.K,
      closedBall (Objects.CorrectedEvent.outerCenter T k) T.blockRadius ⊆ Objects.CorrectedEvent.ann 0 C.r (4 * C.r))
    (hsepB : ∀ k : Fin T.K,
      ∀ x ∈ ball (Objects.CorrectedEvent.innerCenter T k) (T.blockRadius + (C.A_sup + C.A_nar) * C.r),
      ∀ y ∈ ball (Objects.CorrectedEvent.outerCenter T k) (T.blockRadius + (C.A_sup + C.A_nar) * C.r),
        C.A_nar * C.r ≤ dist x y)
    {P : ℝ → ℂ} {L τ' τ σ σ' : ℝ} (hPb : Db.IsCurve P 0 L)
    (hunit : HasUnitSpeedOn (Db.pt ∘ P) (Icc 0 L)) (hgeoP : Db.len P 0 L = Db (P 0, P L))
    (hτ'τ : τ' ≤ τ) (hσσ' : σ ≤ σ')
    (hnear : ∀ k : Fin T.K,
      Objects.Shadow.circleOuter (Objects.CorrectedEvent.innerCenter T k)
          ⟨T.blockRadius, (blockRadius_bounds C T hData hE).1.le⟩ 0
          (hitSet P τ' σ' (2 * C.A_sup * C.r)) ≤ ENNReal.ofReal (C.lamConst * T.blockRadius) ∧
      Objects.Shadow.circleOuter (Objects.CorrectedEvent.outerCenter T k)
          ⟨T.blockRadius, (blockRadius_bounds C T hData hE).1.le⟩ 0
          (hitSet P τ' σ' (2 * C.A_sup * C.r)) ≤ ENNReal.ofReal (C.lamConst * T.blockRadius))
    (w : T57Witness C T hData hE D Dt Db Dtb V N Cmid0 P L τ' τ σ σ') :
    ∃ s t : ℝ, τ ≤ s ∧ s < t ∧ t ≤ σ ∧
      Real.exp (-C.ξ * C.A_max) * (C.A_nar ^ (C.ξ * (C.Q + 3)) * N) ≤ t - s ∧
      ∃ (hs : P s ∈ Metric.ball (0 : ℂ) (4 * C.r)) (ht : P t ∈ Metric.ball (0 : ℂ) (4 * C.r)),
        Dtb.internal (Metric.ball (0 : ℂ) (4 * C.r)) (⟨P s, hs⟩, ⟨P t, ht⟩) ≤
          ENNReal.ofReal (Cmid * (t - s)) :=
  t57_centre0 C D Dt Db Dtb f hLD hforgetD hLDt hforgetDt hWD hWDt hf hV hfV hCp hCmid0 hCmid hle
    hratio (R₀ := ⟨T.blockRadius, (blockRadius_bounds C T hData hE).1.le⟩) (dt := w.dt) (N := N)
    (NNReal.coe_pos.1 (blockRadius_bounds C T hData hE).1) w.dt_pos hN hlam hsup_s hnar_s hnar1
    hcount hnarrow hcompare hPb hunit hgeoP w.τ₀_nonneg w.τ₀_le w.σ₀_ge w.σ₀_le hτ'τ hσσ'
    w.σ₀_norm w.σ₀_time w.tube (hfB_in w.k) (hfB_out w.k) w.u_mem w.u_near w.v_mem w.v_near
    (hAnn_in w.k) (hAnn_out w.k) (hBinA_in w.k) (hBinA_out w.k) (hsepB w.k) w.dt_eq w.ratio
    (w.block_cost _ _) w.bad_u w.bad_v (hnear w.k).1 (hnear w.k).2 w.τ_le_au w.au_lt_bu w.bu_le_σ
    w.τ_le_av w.av_lt_bv w.bv_le_σ w.Pau w.Pbu w.Pav w.Pbv w.far_u w.far_v w.mid_u w.mid_v
    w.win_u w.win_v w.short

end SupercriticalLQGUniqueness.Uniqueness.Objects.Producer
