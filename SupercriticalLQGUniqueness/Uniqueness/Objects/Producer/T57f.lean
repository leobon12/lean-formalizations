import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.T57w
import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.TLC
import SupercriticalLQGUniqueness.Uniqueness.Objects.Splice.C6Continuum
import SupercriticalLQGUniqueness.Uniqueness.Objects.Compare.CompareContinuum




 
















set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Producer

open LQGMetric (DistC addFun)

 

theorem narrow_of_event {C : Objects.CorrectedEvent.Constants} {T : Objects.CorrectedEvent.TubeData} {hData : Objects.CorrectedEvent.DataMatch C T}
    {F : ℂ → DistC → Prop} {D D' : DistC → LSCMetric} {g : DistC}
    (hev : Objects.CorrectedEvent.correctedEvent C T hData F D D' g) {c : ℝ}
    (hc : IsCircleAverage g (radius C) 0 c) :
    ∀ (z w : ℂ) (hz : z ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r))
      (hw : w ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r)), dist z w ≤ C.A_nar / C.lamConst * C.r →
      ENNReal.ofReal ((dist z w / C.r) ^ (C.ξ * (C.Q + 3))) *
          ENNReal.ofReal (C.r ^ (C.ξ * C.Q) * Real.exp (C.ξ * c)) ≤
        (D g).internal (Objects.CorrectedEvent.ann 0 C.r (4 * C.r))
          (⟨z, mid_ann_subset C hz⟩, ⟨w, mid_ann_subset C hw⟩) := by
  intro z w hz hw hzw
  have hca : LQGMetric.circleAvg g C.r 0 = c := by
    have h := circleAvg_eq_of_isCircleAverage hc
    exact h
  have hnorm : Objects.CorrectedEvent.normalizer C g C.r 0 =
      ENNReal.ofReal (C.r ^ (C.ξ * C.Q) * Real.exp (C.ξ * c)) := by
    rw [Objects.CorrectedEvent.normalizer, hca]
  rw [← hnorm]
  exact Objects.Splice.event_narrow_continuum hev hz hw hzw

 

theorem near_of_event (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (hData : Objects.CorrectedEvent.DataMatch C T)
    (hK : 0 ≤ C.K_ann) (hE : C.A_endpt ≤ 1) (hρ : C.ρ < 1 / 64)
    (F : ℂ → DistC → Prop) (D D' : DistC → LSCMetric) (g : DistC)
    (hev : Objects.CorrectedEvent.correctedEvent C T hData F D D' g) (hW : WeylReg C.ξ D g)
    (hforgetD : Continuous (BiLipschitz.Barrier.forget (D g)))
    {g₀ : C(ℂ, ℝ)} (hf : ∀ x : ℂ, 0 ≤ g₀ x ∧ g₀ x ≤ C.A_max)
    {P : ℝ → ℂ} {L τ' σ' : ℝ} (hgeo : EndSaving.Interfaces.BumpedGeodesic (D (addFun g (-g₀))) P L)
    (h0 : 0 ≤ τ') (hτσ : τ' ≤ σ') (hL : σ' ≤ L)
    (ha : P τ' ∈ frontier (ball (0 : ℂ) (4 * C.r)))
    (hb : P σ' ∈ frontier (ball (0 : ℂ) (4 * C.r)))
    (hPK : ∀ t ∈ Icc τ' σ', P t ∈ Objects.CorrectedEvent.cann 0 C.r (4 * C.r))
    (hPgeo : ∀ (ha : P τ' ∈ Objects.CorrectedEvent.cann 0 C.r (4 * C.r)) (hb : P σ' ∈ Objects.CorrectedEvent.cann 0 C.r (4 * C.r)),
      (D (addFun g (-g₀))).len P τ' σ' =
        (D (addFun g (-g₀))).internal (Objects.CorrectedEvent.cann 0 C.r (4 * C.r)) (⟨P τ', ha⟩, ⟨P σ', hb⟩))
    (k : Fin T.K) :
    Objects.Shadow.circleOuter (Objects.CorrectedEvent.innerCenter T k)
        ⟨T.blockRadius, (blockRadius_bounds C T hData hE).1.le⟩ 0
        (hitSet P τ' σ' (2 * C.A_sup * C.r)) ≤ ENNReal.ofReal (C.lamConst * T.blockRadius) ∧
    Objects.Shadow.circleOuter (Objects.CorrectedEvent.outerCenter T k)
        ⟨T.blockRadius, (blockRadius_bounds C T hData hE).1.le⟩ 0
        (hitSet P τ' σ' (2 * C.A_sup * C.r)) ≤ ENNReal.ofReal (C.lamConst * T.blockRadius) := by
  have hr := C.rPos
  have hPb' : (D (addFun g (-g₀))).IsCurve P τ' σ' :=
    ⟨hτσ, hgeo.1.2.mono (Icc_subset_Icc h0 hL)⟩
  have hfin : (D (addFun g (-g₀))).len P τ' σ' ≠ ⊤ := by
    have hmono : (D (addFun g (-g₀))).len P τ' σ' ≤ (D (addFun g (-g₀))).len P 0 L :=
      eVariationOn.mono _ (Icc_subset_Icc h0 hL)
    exact ne_top_of_le_ne_top (by rw [hgeo.2.2.1]; exact hgeo.2.2.2.ne) hmono
  have hsph : ∀ t, P t ∈ frontier (ball (0 : ℂ) (4 * C.r)) → ‖P t‖ = 4 * C.r := by
    intro t ht
    rw [frontier_ball (0 : ℂ) (mul_pos four_pos hr).ne', mem_sphere_zero_iff_norm] at ht
    exact ht
  have hC8 := c8_of_event' C T hData hK hE hρ F D D' g hev hW hforgetD g₀ hf hPb' hPK
    (hPgeo _ _) hfin (hsph τ' ha) (hsph σ' hb) k
  have hlamb : ENNReal.ofReal (C.lamConst * C.A_endpt * C.ρ * C.r) ≤
      ENNReal.ofReal (C.lamConst * T.blockRadius) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : C.A_endpt * C.ρ * C.r ≤ T.blockRadius := hData.2.2.2.2.2.2.2.2.2.1
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (by rw [← mul_assoc]; exact h1) C.lamPos.le
  exact ⟨hC8.1.trans hlamb, hC8.2.trans hlamb⟩

 




theorem shortcutAt_zero_of_t57 (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (hData : Objects.CorrectedEvent.DataMatch C T)
    (F : ℂ → DistC → Prop) (D D' : DistC → LSCMetric) (g : DistC)
    (hev : Objects.CorrectedEvent.correctedEvent C T hData F D D' g)
    (hW : WeylReg C.ξ D g) (hW' : WeylReg C.ξ D' g)
    (hforgetD : Continuous (BiLipschitz.Barrier.forget (D g))) (hforgetDt : Continuous (BiLipschitz.Barrier.forget (D' g)))
    {Cp Cmid0 Cmid Ctime : ℝ} (hCp : 0 < Cp) (hCmid0 : 0 ≤ Cmid0) (hCmid : 0 ≤ Cmid)
    (hle : ∀ x y : ℂ, D' g (x, y) ≤ ENNReal.ofReal Cp * D g (x, y))
    (hratio : (1 + 10 * Cp * C.lamConst) * Cmid0 ≤ Cmid * (1 - 10 * Cp * C.lamConst))
    (hK : 0 ≤ C.K_ann) (hE : C.A_endpt ≤ 1) (hρ : C.ρ < 1 / 64)
    (hlam : C.lamConst ≤ 1 / 48) (hnar1 : C.A_nar < 1)
    (hsup_s : C.A_sup * C.r ≤ T.blockRadius) (hnar_s : 3 * C.A_nar * C.r ≤ T.blockRadius / 2)
    (hcount : ∀ k : ℕ, (1 / 2 : ℝ) ^ (k + 1) < C.A_nar →
      21 * (((k : ℝ) + 3) * (C.ξ * (C.Q + 3)) + Real.logb 2 (2 * C.A_around) + 2) ≤
        cSel * (T.blockRadius / C.r) * (2 : ℝ) ^ ((k : ℝ) / 4))
    {V₀ : TopologicalSpace.Opens ℂ} {g₀ : C(ℂ, ℝ)}
    (hf : ∀ x : ℂ, 0 ≤ g₀ x ∧ g₀ x ≤ C.A_max) (hfV : ∀ x ∉ (V₀ : Set ℂ), g₀ x = 0)
    (hVW : closure (V₀ : Set ℂ) ⊆ ball (0 : ℂ) (4 * C.r))
    (hfB_in : ∀ k : Fin T.K, ∀ x ∈ closedBall (Objects.CorrectedEvent.innerCenter T k) T.blockRadius, g₀ x = C.A_max)
    (hfB_out : ∀ k : Fin T.K, ∀ x ∈ closedBall (Objects.CorrectedEvent.outerCenter T k) T.blockRadius, g₀ x = C.A_max)
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
    (hwit : ∀ c : ℝ, IsCircleAverage g (radius C) 0 c →
      ∀ (P : ℝ → ℂ) (L τ' τ σ σ' : ℝ),
        EndSaving.Interfaces.BumpedGeodesic (D (addFun g (-g₀))) P L →
        P 0 ∉ ball (0 : ℂ) (4 * C.r) → P L ∉ ball (0 : ℂ) (4 * C.r) →
        EndSaving.Interfaces.Excursion P L (ball (0 : ℂ) (4 * C.r)) V₀ τ' τ σ σ' →
        ∀ (hτ : P τ ∈ ball (0 : ℂ) (4 * C.r)) (hσ : P σ ∈ ball (0 : ℂ) (4 * C.r)),
          ENNReal.ofReal Ctime * ENNReal.ofReal (C.r ^ (C.ξ * C.Q) * Real.exp (C.ξ * c)) ≤
            (D g).internal (ball (0 : ℂ) (4 * C.r)) (⟨P τ, hτ⟩, ⟨P σ, hσ⟩) →
          Nonempty (T57Witness C T hData hE (D g) (D' g) (D (addFun g (-g₀)))
            (D' (addFun g (-g₀))) (V₀ : Set ℂ) (C.r ^ (C.ξ * C.Q) * Real.exp (C.ξ * c)) Cmid0 P L
            τ' τ σ σ')) :
    ShortcutAt D D' C.ξ C.Q Ctime (cInc C) Cmid 0 (radius C) V₀ g₀ g := by
  intro c hc P L τ' τ σ σ' hgeo hP0 hPL hexc
  have hr := C.rPos
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ := hexc
  have hτ : P τ ∈ ball (0 : ℂ) (4 * C.r) := hVW e9
  have hσ : P σ ∈ ball (0 : ℂ) (4 * C.r) := hVW e10
  refine ⟨hτ, hσ, fun hCt => ?_⟩
  obtain ⟨w⟩ := hwit c hc P L τ' τ σ σ' hgeo hP0 hPL
    ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ hτ hσ hCt
  have hN : 0 < C.r ^ (C.ξ * C.Q) * Real.exp (C.ξ * c) :=
    mul_pos (Real.rpow_pos_of_pos hr _) (Real.exp_pos _)
  have hWD : ∀ x y : ℂ, D (addFun g (-g₀)) (x, y) = weylScale C.ξ (-g₀) (D g) (x, y) :=
    fun x y => (congrFun (hW.2 (-g₀)) (x, y)).symm
  have hWDt : ∀ x y : ℂ, D' (addFun g (-g₀)) (x, y) = weylScale C.ξ (-g₀) (D' g) (x, y) :=
    fun x y => (congrFun (hW'.2 (-g₀)) (x, y)).symm
  have hnear := near_of_event C T hData hK hE hρ F D D' g hev hW hforgetD hf hgeo e1
    (e2.trans (e3.trans e4)) e5 e6 e7 w.carrier w.carrier_geo
  obtain ⟨s, t, hτs, hst, htσ, hinc, hs, ht, hcost⟩ := t57_of_witness C T hData hE (D g) (D' g)
    (D (addFun g (-g₀))) (D' (addFun g (-g₀))) g₀ hW.1 hforgetD hW'.1 hforgetDt hWD hWDt hf
    V₀.isOpen hfV hCp hCmid0 hCmid hle hratio hN hlam hnar1 hsup_s hnar_s hcount
    (narrow_of_event hev hc) (fun y hy δ hδ hδnar => Objects.Compare.event_compare_continuum hev hy hδ hδnar)
    hfB_in hfB_out hAnn_in hAnn_out hBinA_in hBinA_out hsepB hgeo.1 hgeo.2.1 hgeo.2.2.1 e2 e4
    hnear w
  refine ⟨s, t, hτs, hst, htσ, ?_, hs, ht, hcost⟩
  have hc0 : 0 ≤ cInc C := by
    unfold cInc
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg C.narPos.le _)
  rw [← ENNReal.ofReal_mul hc0]
  refine ENNReal.ofReal_le_ofReal ?_
  calc cInc C * (C.r ^ (C.ξ * C.Q) * Real.exp (C.ξ * c))
      = Real.exp (-C.ξ * C.A_max) * (C.A_nar ^ (C.ξ * (C.Q + 3)) *
          (C.r ^ (C.ξ * C.Q) * Real.exp (C.ξ * c))) := by
        rw [cInc]; ring
    _ ≤ t - s := hinc

 



theorem shortcutAt_of_t57 (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (hData : Objects.CorrectedEvent.DataMatch C T)
    (F : ℂ → DistC → Prop) (D D' : DistC → LSCMetric) {Wc : Set ℂ}
    {Cc : Set (Set.Ioi (0 : ℝ) × ℂ)} {u : DistC} (hgood : LocalGood C.ξ D D' Wc Cc u) {z : ℂ}
    (hz : z ∈ Wc) (hev : Objects.CorrectedEvent.correctedEvent C T hData F D D' (normTranslate z u))
    {Cp Cmid0 Cmid Ctime : ℝ} (hCp : 0 < Cp) (hCmid0 : 0 ≤ Cmid0) (hCmid : 0 ≤ Cmid)
    (hle : ∀ x y : ℂ, D' (normTranslate z u) (x, y) ≤ ENNReal.ofReal Cp * D (normTranslate z u) (x, y))
    (hratio : (1 + 10 * Cp * C.lamConst) * Cmid0 ≤ Cmid * (1 - 10 * Cp * C.lamConst))
    (hK : 0 ≤ C.K_ann) (hE : C.A_endpt ≤ 1) (hρ : C.ρ < 1 / 64)
    (hlam : C.lamConst ≤ 1 / 48) (hnar1 : C.A_nar < 1)
    (hsup_s : C.A_sup * C.r ≤ T.blockRadius) (hnar_s : 3 * C.A_nar * C.r ≤ T.blockRadius / 2)
    (hcount : ∀ k : ℕ, (1 / 2 : ℝ) ^ (k + 1) < C.A_nar →
      21 * (((k : ℝ) + 3) * (C.ξ * (C.Q + 3)) + Real.logb 2 (2 * C.A_around) + 2) ≤
        cSel * (T.blockRadius / C.r) * (2 : ℝ) ^ ((k : ℝ) / 4))
    {V V₀ : TopologicalSpace.Opens ℂ} (hV : ∀ w : ℂ, w ∈ (V₀ : Set ℂ) ↔ w + z ∈ (V : Set ℂ))
    {g g₀ : C(ℂ, ℝ)} (hg : ∀ x, g₀ x = g (x + z))
    (hf : ∀ x : ℂ, 0 ≤ g₀ x ∧ g₀ x ≤ C.A_max) (hfV : ∀ x ∉ (V₀ : Set ℂ), g₀ x = 0)
    (hVW : closure (V₀ : Set ℂ) ⊆ ball (0 : ℂ) (4 * C.r))
    (hfB_in : ∀ k : Fin T.K, ∀ x ∈ closedBall (Objects.CorrectedEvent.innerCenter T k) T.blockRadius, g₀ x = C.A_max)
    (hfB_out : ∀ k : Fin T.K, ∀ x ∈ closedBall (Objects.CorrectedEvent.outerCenter T k) T.blockRadius, g₀ x = C.A_max)
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
    (hwit : ∀ c : ℝ, IsCircleAverage (normTranslate z u) (radius C) 0 c →
      ∀ (P : ℝ → ℂ) (L τ' τ σ σ' : ℝ),
        EndSaving.Interfaces.BumpedGeodesic (D (addFun (normTranslate z u) (-g₀))) P L →
        P 0 ∉ ball (0 : ℂ) (4 * C.r) → P L ∉ ball (0 : ℂ) (4 * C.r) →
        EndSaving.Interfaces.Excursion P L (ball (0 : ℂ) (4 * C.r)) V₀ τ' τ σ σ' →
        ∀ (hτ : P τ ∈ ball (0 : ℂ) (4 * C.r)) (hσ : P σ ∈ ball (0 : ℂ) (4 * C.r)),
          ENNReal.ofReal Ctime * ENNReal.ofReal (C.r ^ (C.ξ * C.Q) * Real.exp (C.ξ * c)) ≤
            (D (normTranslate z u)).internal (ball (0 : ℂ) (4 * C.r)) (⟨P τ, hτ⟩, ⟨P σ, hσ⟩) →
          Nonempty (T57Witness C T hData hE (D (normTranslate z u)) (D' (normTranslate z u))
            (D (addFun (normTranslate z u) (-g₀))) (D' (addFun (normTranslate z u) (-g₀)))
            (V₀ : Set ℂ) (C.r ^ (C.ξ * C.Q) * Real.exp (C.ξ * c)) Cmid0 P L τ' τ σ σ')) :
    ShortcutAt D D' C.ξ C.Q Ctime (cInc C) Cmid z (radius C) V g u := by
  have hκ : 0 < Real.exp (C.ξ * -(LQGMetric.circleAvg u 1 z)) := Real.exp_pos _
  have hW := hgood.weylReg_normTranslate hz
  have hfD : Continuous (BiLipschitz.Barrier.forget (D (normTranslate z u))) :=
    continuous_forget_shift hκ (tlc_metric hgood hz)
      (BiLipschitz.Barrier.continuous_forget_of_barrier _ hgood.1.2 hgood.1.1.1)
  have hfDt : Continuous (BiLipschitz.Barrier.forget (D' (normTranslate z u))) :=
    continuous_forget_shift hκ (tlc_metric' hgood hz)
      (BiLipschitz.Barrier.continuous_forget_of_barrier _ hgood.2.1.2 hgood.2.1.1.1)
  exact shortcutAt_of_normTranslate hgood hz hV hg
    (shortcutAt_zero_of_t57 C T hData F D D' (normTranslate z u) hev hW.1 hW.2 hfD hfDt hCp hCmid0
      hCmid hle hratio hK hE hρ hlam hnar1 hsup_s hnar_s hcount hf hfV hVW hfB_in hfB_out hAnn_in
      hAnn_out hBinA_in hBinA_out hsepB hwit)

end SupercriticalLQGUniqueness.Uniqueness.Objects.Producer
