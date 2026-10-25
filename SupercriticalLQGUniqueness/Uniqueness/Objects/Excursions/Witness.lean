import SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions.L5b
import SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions.Block
import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.T58




 




















set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions

open SupercriticalLQGUniqueness.Uniqueness.Objects.Tube
open LQGMetric (DistC addFun testCont)

section Geometry

variable {C : Objects.CorrectedEvent.Constants} {T : Objects.CorrectedEvent.TubeData}

 

theorem closure_tubeV_near_circle (hData : Objects.CorrectedEvent.DataMatch C T) (hlam : C.lamConst < 1 / 10 ^ 100)
    (hAloc : 3 < C.A_loc) (hKann : 3 / 4 < C.K_ann)
    (hendpt : C.A_endpt ≤ C.lamConst * (1 - C.K_ann) ^ 2)
    (hrho2 : C.ρ ≤ 10 * C.lamConst ^ 2 / (Real.pi ^ 2 * C.A_loc ^ 2)) {x : ℂ}
    (hx : x ∈ closure (Objects.CorrectedEvent.tubeV T C.A_sup)) : |‖x‖ - 2 * C.r| ≤ 11 * (C.ρ * C.r) := by
  obtain ⟨hr, hρ, -, -, hα, -, hn4, -, -, -, -⟩ := dataMatch_basic hData
  have hGood := good_toParams hData hlam hAloc hKann hendpt hrho2
  have hr0 : 0 < T.r := hr ▸ C.rPos
  have hρr : T.rho * T.r ≠ 0 := by rw [hρ, hr]; exact (mul_pos C.rhoPos C.rPos).ne'
  have hn : ‖T.orientation‖ = 1 := Objects.Producer.norm_orientation hn4
  have hsp23 : Objects.CorrectedEvent.sPrime T ≤ 2 / 3 := by
    have h1 := hGood.sp_le; have h2 := hGood.α_gt
    change 100 * Objects.CorrectedEvent.sPrime T ≤ 1 - T.alpha at h1
    change 3 / 4 < T.alpha at h2
    linarith
  have hpos : 0 ≤ T.alpha - 3 * Objects.CorrectedEvent.sPrime T / 4 := by
    have h1 := hGood.sp_le; have h2 := hGood.α_gt; have h3 := hGood.sp_pos
    change 100 * Objects.CorrectedEvent.sPrime T ≤ 1 - T.alpha at h1
    change 3 / 4 < T.alpha at h2
    linarith
  have hsmall := TubeParams.small_of_DG (toParams T) (lam := C.lamConst) (Aendpt := C.A_endpt)
    (Anar := C.A_nar) (Asup := C.A_sup) C.lamPos hlam hGood.α_gt C.endptPos
    (sPrime_bounds hData).1 hGood.ρ_pos C.supPos (C.supLtSet.trans C.setLtNar)
    (by simp only [toParams]; rw [hα, hρ]; exact C.narLe)
  rw [tubeV_eq T hn hsp23 hpos hρr] at hx
  have h := TubeParams.closure_nbhd_near_circle hGood hr0 hsmall.1 hx
  rw [show (toParams T).ρ = C.ρ from hρ, hr] at h
  exact h

 

theorem tube_geometry (hData : Objects.CorrectedEvent.DataMatch C T) (hlam : C.lamConst < 1 / 10 ^ 100)
    (hAloc : 3 < C.A_loc) (hKann : 3 / 4 < C.K_ann)
    (hendpt : C.A_endpt ≤ C.lamConst * (1 - C.K_ann) ^ 2)
    (hrho2 : C.ρ ≤ 10 * C.lamConst ^ 2 / (Real.pi ^ 2 * C.A_loc ^ 2)) :
    closure (Objects.CorrectedEvent.tubeV T C.A_sup) ⊆ {x : ℂ | 3 / 2 * C.r < ‖x‖ ∧ ‖x‖ < 5 / 2 * C.r} ∧
    (∀ x y, y ∈ closure (Objects.CorrectedEvent.tubeV T C.A_sup) → dist x y ≤ C.A_nar * C.r → x ∈ midAnn C) ∧
    (∀ x ∈ Objects.CorrectedEvent.tubeSet T, 3 / 2 * C.r < ‖x‖) ∧ Objects.CorrectedEvent.tubeSet T ⊆ ball 0 (2.5 * C.r) := by
  have hlam48 : C.lamConst ≤ 1 / 48 := by
    have : (1 : ℝ) / 10 ^ 100 ≤ 1 / 48 := by norm_num
    linarith
  have hK0 : 0 ≤ C.K_ann := by linarith
  have hρ64 := Objects.Producer.rho_lt_of_constants C hlam48
  have hK1 := Objects.Producer.kann_lt_one C
  have hE1 : C.A_endpt ≤ 1 := by
    have h1 : C.lamConst * (1 - C.K_ann) ^ 2 ≤ 1 := by
      have : (1 - C.K_ann) ^ 2 ≤ 1 := by nlinarith
      nlinarith [C.lamPos]
    linarith
  have hnar := Objects.Producer.nar_le_endpt C hK0 hlam48
  have hr := C.rPos
  have hρp := C.rhoPos
  have hloc : ∀ x ∈ closure (Objects.CorrectedEvent.tubeV T C.A_sup), |‖x‖ - 2 * C.r| ≤ 11 * (C.ρ * C.r) :=
    fun x hx => closure_tubeV_near_circle hData hlam hAloc hKann hendpt hrho2 hx
  have hρr : C.ρ * C.r < C.r / 64 := by nlinarith
  have hnr : C.A_nar * C.r ≤ C.r / 64 := by
    have h1 : C.A_nar ≤ 1 / 64 := by
      have : C.A_endpt * C.ρ ≤ 1 / 64 := by nlinarith [C.endptPos]
      linarith
    nlinarith
  have hsub : Objects.CorrectedEvent.tubeSet T ⊆ closure (Objects.CorrectedEvent.tubeV T C.A_sup) := fun x hx =>
    subset_closure ⟨x, hx, by rw [dist_self, hData.1]; exact mul_pos C.supPos hr⟩
  refine ⟨fun x hx => ?_, fun x y hy hxy => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have h := abs_le.1 (hloc x hx)
    constructor <;> linarith [h.1, h.2]
  · have h := abs_le.1 (hloc y hy)
    have h1 := norm_sub_norm_le y x
    have h2 := norm_sub_norm_le x y
    rw [dist_eq_norm] at hxy
    rw [norm_sub_rev] at h1
    show 3 / 2 * C.r < ‖x‖ ∧ ‖x‖ < 3 * C.r
    constructor <;> linarith [h.1, h.2]
  · have h := abs_le.1 (hloc x (hsub hx))
    linarith [h.1]
  · have h := abs_le.1 (hloc x (hsub hx))
    rw [mem_ball, dist_zero_right]
    linarith [h.2]

 
theorem closure_tubeV_near_tube {R : ℝ} (hU : Objects.CorrectedEvent.tubeSet T ⊆ closedBall 0 R) (A : ℝ) :
    ∀ y ∈ closure (Objects.CorrectedEvent.tubeV T A), ∃ x ∈ closure (Objects.CorrectedEvent.tubeSet T), dist y x ≤ A * T.r := by
  intro y hy
  have hK : IsCompact (closure (Objects.CorrectedEvent.tubeSet T)) :=
    (isCompact_closedBall 0 R).of_isClosed_subset isClosed_closure
      (closure_minimal hU isClosed_closedBall)
  have hsub : Objects.CorrectedEvent.tubeV T A ⊆ {x | infDist x (closure (Objects.CorrectedEvent.tubeSet T)) ≤ A * T.r} := by
    rintro x ⟨t, ht, hxt⟩
    exact (infDist_le_dist_of_mem (subset_closure ht)).trans hxt.le
  have hcl : IsClosed {x | infDist x (closure (Objects.CorrectedEvent.tubeSet T)) ≤ A * T.r} :=
    isClosed_le (continuous_infDist_pt _) continuous_const
  have hyK : infDist y (closure (Objects.CorrectedEvent.tubeSet T)) ≤ A * T.r := closure_minimal hsub hcl hy
  have hne : (closure (Objects.CorrectedEvent.tubeSet T)).Nonempty := by
    obtain ⟨x, t, ht, -⟩ := closure_nonempty_iff.1 ⟨y, hy⟩
    exact ⟨t, subset_closure ht⟩
  obtain ⟨x, hx, hxd⟩ := hK.exists_infDist_eq_dist hne y
  exact ⟨x, hx, hxd ▸ hyK⟩

end Geometry

 
theorem dataMatch_bump {C : Objects.CorrectedEvent.Constants} {T : Objects.CorrectedEvent.TubeData} (hData : Objects.CorrectedEvent.DataMatch C T) :
    (∀ x, 0 ≤ T.bump x ∧ T.bump x ≤ C.A_max) ∧ (∀ x ∈ closure (Objects.CorrectedEvent.tubeSet T), T.bump x = C.A_max) ∧
      (∀ x ∉ Objects.CorrectedEvent.tubeV T C.A_sup, T.bump x = 0) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h1, h2, h3⟩ := hData
  exact ⟨h1, h2, h3⟩

 

theorem t57_witness (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (hData : Objects.CorrectedEvent.DataMatch C T)
    (hE : C.A_endpt ≤ 1) (F : ℂ → DistC → Prop) (D D' : DistC → LSCMetric) (Ksh : ℕ)
    (Cmid0 Ctime : ℝ) (hF : ∀ z g, F z g → blockEvent C T Ksh Cmid0 D D' z g)
    {V₀ : TopologicalSpace.Opens ℂ} (hV₀ : (V₀ : Set ℂ) = Objects.CorrectedEvent.tubeV T C.A_sup)
    {g₀ : C(ℂ, ℝ)} (hg₀ : ∀ x, 0 ≤ g₀ x ∧ g₀ x ≤ C.A_max)
    (hg₀max : ∀ x ∈ closure (Objects.CorrectedEvent.tubeSet T), g₀ x = C.A_max)
    (hg₀off : ∀ x ∉ Objects.CorrectedEvent.tubeV T C.A_sup, g₀ x = 0) {Target : Set DistC}
    (hTarget : ∀ g ∈ Target, Objects.CorrectedEvent.correctedEvent C T hData F D D' g ∧
      Objects.Producer.LocalGood C.ξ D D' (range (Objects.CorrectedEvent.site T)) ∅ g)
    (hlam : C.lamConst < 1 / 10 ^ 100) (hAloc : 3 < C.A_loc) (hKann : 3 / 4 < C.K_ann)
    (hendpt : C.A_endpt ≤ C.lamConst * (1 - C.K_ann) ^ 2)
    (hrho2 : C.ρ ≤ 10 * C.lamConst ^ 2 / (Real.pi ^ 2 * C.A_loc ^ 2))
    (hline4 : C.c_reg⁻¹ ^ 2 * (1 + C.c_reg) ^ 3 * (2 : ℝ) ^ (2 * theta C) *
      ((2 : ℝ) ^ (-(C.k0 : ℝ))) ^ theta C ≤ 1)
    (hline5 : 4 * C.A_sp ^ theta C * C.A_around < C.A_across ^ 2 / (16 * C.A_around))
    (hline8 : 4 * (2 * C.A_set) ^ theta C * C.A_around ≤
      C.lamConst * C.A_nar ^ (C.ξ * (C.Q + 3)))
    (hmaxint : Real.exp (-C.ξ * C.A_max) * C.A_internal ≤ C.lamConst * C.A_across)
    (hmaxnar : Real.exp (-C.ξ * C.A_max) * C.A_internal ≤ C.lamConst * C.A_nar ^ (C.ξ * (C.Q + 3)))
    (hCtime : C.A_across ^ 2 / (4 * C.A_around) ≤ Ctime) :
    ∀ g ∈ Target, ∀ c : ℝ, IsCircleAverage g (Objects.Producer.radius C) 0 c →
      ∀ (P : ℝ → ℂ) (L τ' τ σ σ' : ℝ),
        EndSaving.Interfaces.BumpedGeodesic (D (addFun g (-g₀))) P L →
        P 0 ∉ ball (0 : ℂ) (4 * C.r) → P L ∉ ball (0 : ℂ) (4 * C.r) →
        EndSaving.Interfaces.Excursion P L (ball (0 : ℂ) (4 * C.r)) V₀ τ' τ σ σ' →
        ∀ (hτ : P τ ∈ ball (0 : ℂ) (4 * C.r)) (hσ : P σ ∈ ball (0 : ℂ) (4 * C.r)),
          ENNReal.ofReal Ctime * ENNReal.ofReal (C.r ^ (C.ξ * C.Q) * Real.exp (C.ξ * c)) ≤
            (D g).internal (ball (0 : ℂ) (4 * C.r)) (⟨P τ, hτ⟩, ⟨P σ, hσ⟩) →
          Nonempty (Objects.Producer.T57Witness C T hData hE (D g) (D' g) (D (addFun g (-g₀)))
            (D' (addFun g (-g₀))) (V₀ : Set ℂ) (C.r ^ (C.ξ * C.Q) * Real.exp (C.ξ * c)) Cmid0 P L
            τ' τ σ σ') := by
  intro g hg c hc P L τ' τ σ σ' hgeo _ _ hexc hτ hσ hCt
  obtain ⟨hev, hgood⟩ := hTarget g hg
  have hr := C.rPos
  have hN : 0 < C.r ^ (C.ξ * C.Q) * Real.exp (C.ξ * c) :=
    mul_pos (Real.rpow_pos_of_pos hr _) (Real.exp_pos _)
  have hNe : Objects.CorrectedEvent.normalizer C g C.r 0 =
      ENNReal.ofReal (C.r ^ (C.ξ * C.Q) * Real.exp (C.ξ * c)) := by
    have h := Objects.Producer.circleAvg_eq_of_isCircleAverage hc
    have hca : LQGMetric.circleAvg g C.r 0 = c := h
    rw [Objects.CorrectedEvent.normalizer, hca]
  generalize C.r ^ (C.ξ * C.Q) * Real.exp (C.ξ * c) = N at hN hNe hCt ⊢
  
  have hlam48 : C.lamConst ≤ 1 / 48 := by
    have : (1 : ℝ) / 10 ^ 100 ≤ 1 / 48 := by norm_num
    linarith
  have hlam1 : C.lamConst ≤ 1 := by linarith
  have hlam3 : 3 * C.lamConst < 1 := by linarith
  have hK0 : 0 ≤ C.K_ann := by linarith
  
  obtain ⟨hVloc, hloc, htube, hU⟩ := tube_geometry hData hlam hAloc hKann hendpt hrho2
  have hVnear := closure_tubeV_near_tube (hU.trans ball_subset_closedBall) C.A_sup
  rw [hData.1] at hVnear
  
  have hgD := hgood.1
  have S : ExcSetting C (D g) (D (addFun g (-g₀))) g₀ V₀ P L τ' τ σ σ' :=
    { forget := BiLipschitz.Barrier.continuous_forget_of_barrier _ hgD.2 hgD.1.1
      length := hgD.1.1
      weyl := fun x y => (congrFun (hgD.1.2 (-g₀)) (x, y)).symm
      f_bd := hg₀
      f_off := fun x hx => hg₀off x (by rw [← hV₀]; exact hx)
      V_loc := by rw [hV₀]; exact hVloc
      geo := hgeo
      exc := hexc }
  
  have hS2 : Objects.CorrectedEvent.around (D g) 0 (3 * C.r) (4 * C.r) ≤
      ENNReal.ofReal C.A_around * ENNReal.ofReal N := by
    have h := Objects.CorrectedEvent.event_around hev
    rwa [hNe] at h
  have hS3 := Objects.CorrectedEvent.event_reg hev
  have hS1 : ENNReal.ofReal C.A_across * ENNReal.ofReal N ≤ Objects.CorrectedEvent.acr (D g) 0 C.r (1.5 * C.r) := by
    have h := hev.1.1
    rwa [hNe] at h
  obtain ⟨π, ts, us, hnet⟩ := event_network hev hU
  rw [hNe] at hnet
  have hfmax : ∀ x ∈ Objects.CorrectedEvent.tubeSet T, g₀ x = C.A_max := fun x hx => hg₀max x (subset_closure hx)
  
  have hcar : ∀ t ∈ Icc τ' σ', P t ∈ Objects.CorrectedEvent.cann 0 C.r (4 * C.r) :=
    fun t ht => x1_carrier S hN hnet hS1 hmaxint hlam1 htube hfmax ht
  
  obtain ⟨τ₀, σ₀, hτ'τ₀, hτ₀τ, hσσ₀, hσ₀σ', -, hσ₀n, hτσ₀⟩ := x2a_times S hN hS2
  
  have hsep := x2c_sep S hS3 hline4 hline5 hN hS2 hCtime hτ hσ hCt
  
  have hshort := x3_short S hS3 hline4 hline8 hmaxnar (two_set_le_ep C hK0 hE hlam48) hN hS2 hnet
    htube hfmax (by rw [hV₀]; exact hVnear)
  
  have htub := x4_tube S hev hN hNe (by rw [hV₀]; exact hloc) hlam3 hshort.le
  
  obtain ⟨k, hFk, ⟨au, bu, wu1, wu2, wu3, wu4, wu5, wu6, wu7, wu8⟩,
      ⟨av, bv, wv1, wv2, wv3, wv4, wv5, wv6, wv7, wv8⟩⟩ :=
    l5_windows S hev hV₀ hN hNe hlam hAloc hKann hendpt hrho2 hsep hshort.le
  
  obtain ⟨u, v, dt, hu, hv, hun, hvn, hdt, hdteq, hrat, hcost, hbu, hbv⟩ :=
    block_content hData hE hlam48 hgood k ⟨k, rfl⟩ (hF _ _ hFk) hg₀ hg₀max
  have hshort' : σ - τ < C.A_nar ^ (C.ξ * (C.Q + 3)) * N := by
    have hA : 0 < C.A_nar ^ (C.ξ * (C.Q + 3)) * N := mul_pos (Real.rpow_pos_of_pos C.narPos _) hN
    have h := mul_lt_mul_of_pos_right hlam3 hA
    linarith
  exact ⟨{
    k := k, u := u, v := v, dt := dt, dt_pos := hdt, u_mem := hu, u_near := hun
    v_mem := hv, v_near := hvn, dt_eq := hdteq, ratio := hrat, block_cost := hcost
    bad_u := hbu, bad_v := hbv, τ₀ := τ₀, σ₀ := σ₀, τ₀_nonneg := S.τ'_nonneg.trans hτ'τ₀
    τ₀_le := hτ₀τ, σ₀_ge := hσσ₀, σ₀_le := hσ₀σ'.trans S.σ'_le_L, σ₀_norm := hσ₀n
    σ₀_time := hτσ₀.le, tube := htub, short := hshort', carrier := hcar
    carrier_geo := x1_geo S hcar, au := au, bu := bu, av := av, bv := bv
    τ_le_au := wu1, au_lt_bu := wu2, bu_le_σ := wu3, τ_le_av := wv1, av_lt_bv := wv2
    bv_le_σ := wv3, Pau := wu4, Pbu := wu5, Pav := wv4, Pbv := wv5, far_u := wu6
    far_v := wv6, mid_u := wu7, mid_v := wv7, win_u := wu8, win_v := wv8 }⟩

 


def mkT57Inputs {D D' : DistC → LSCMetric} {ξ : Set.Ioi (0 : ℝ)} {Q cMid : ℝ}
    {par : EndSaving.Interfaces.Parameters ξ} {r : Set.Ioi (0 : ℝ)} {U₀ V₀ : TopologicalSpace.Opens ℂ}
    {Target : Set DistC} (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (hData : Objects.CorrectedEvent.DataMatch C T)
    (Ksh : ℕ) (Cmid0 : ℝ) (ξ_eq : C.ξ = ξ) (Q_eq : C.Q = Q) (r_eq : C.r = r)
    (max_eq : C.A_max = par.Cmax) (inc_eq : Objects.Producer.cInc C = par.Cinc)
    (event : ∀ g ∈ Target, Objects.CorrectedEvent.correctedEvent C T hData (blockEvent C T Ksh Cmid0 D D') D D' g)
    (good : ∀ g ∈ Target, Objects.Producer.LocalGood C.ξ D D' (range (Objects.CorrectedEvent.site T)) ∅ g)
    (Cp : ℝ) (Cp_pos : 0 < Cp)
    (comp : ∀ g ∈ Target, ∀ x y : ℂ, D' g (x, y) ≤ ENNReal.ofReal Cp * D g (x, y))
    (Cmid0_nonneg : 0 ≤ Cmid0) (cMid_nonneg : 0 ≤ cMid)
    (ratio : (1 + 10 * Cp * C.lamConst) * Cmid0 ≤ cMid * (1 - 10 * Cp * C.lamConst))
    (K_nonneg : 0 ≤ C.K_ann) (endpt_le : C.A_endpt ≤ 1) (lam_le : C.lamConst ≤ 1 / 48)
    (count : ∀ k : ℕ, (1 / 2 : ℝ) ^ (k + 1) < C.A_nar →
      21 * (((k : ℝ) + 3) * (C.ξ * (C.Q + 3)) + Real.logb 2 (2 * C.A_around) + 2) ≤
        Objects.Producer.cSel * (T.blockRadius / C.r) * (2 : ℝ) ^ ((k : ℝ) / 4))
    (tube_sub : Objects.CorrectedEvent.tubeSet T ⊆ (U₀ : Set ℂ))
    (sep_small : 2 * Real.sqrt C.A_endpt * C.ρ + 2 * C.A_sup + 3 * C.A_nar ≤ C.ρ * (1 - C.K_ann))
    (hV₀ : (V₀ : Set ℂ) = Objects.CorrectedEvent.tubeV T C.A_sup)
    (hlam : C.lamConst < 1 / 10 ^ 100) (hAloc : 3 < C.A_loc) (hKann : 3 / 4 < C.K_ann)
    (hendpt : C.A_endpt ≤ C.lamConst * (1 - C.K_ann) ^ 2)
    (hrho2 : C.ρ ≤ 10 * C.lamConst ^ 2 / (Real.pi ^ 2 * C.A_loc ^ 2))
    (hline4 : C.c_reg⁻¹ ^ 2 * (1 + C.c_reg) ^ 3 * (2 : ℝ) ^ (2 * theta C) *
      ((2 : ℝ) ^ (-(C.k0 : ℝ))) ^ theta C ≤ 1)
    (hline5 : 4 * C.A_sp ^ theta C * C.A_around < C.A_across ^ 2 / (16 * C.A_around))
    (hline8 : 4 * (2 * C.A_set) ^ theta C * C.A_around ≤
      C.lamConst * C.A_nar ^ (C.ξ * (C.Q + 3)))
    (hmaxint : Real.exp (-C.ξ * C.A_max) * C.A_internal ≤ C.lamConst * C.A_across)
    (hmaxnar : Real.exp (-C.ξ * C.A_max) * C.A_internal ≤ C.lamConst * C.A_nar ^ (C.ξ * (C.Q + 3)))
    (hCtime : C.A_across ^ 2 / (4 * C.A_around) ≤ par.Ctime) :
    Objects.Producer.T57Inputs D D' ξ Q cMid par r U₀ V₀ (testCont T.bump) Target where
  C := C
  T := T
  hData := hData
  F := blockEvent C T Ksh Cmid0 D D'
  ξ_eq := ξ_eq
  Q_eq := Q_eq
  r_eq := r_eq
  max_eq := max_eq
  inc_eq := inc_eq
  event := event
  Cp := Cp
  Cp_pos := Cp_pos
  comp := comp
  Cmid0 := Cmid0
  Cmid0_nonneg := Cmid0_nonneg
  cMid_nonneg := cMid_nonneg
  ratio := ratio
  K_nonneg := K_nonneg
  endpt_le := endpt_le
  lam_le := lam_le
  count := count
  tube_sub := tube_sub
  sep_small := sep_small
  witness := t57_witness C T hData endpt_le _ D D' Ksh Cmid0 par.Ctime (fun _ _ h => h) hV₀
    (dataMatch_bump hData).1 (dataMatch_bump hData).2.1 (dataMatch_bump hData).2.2
    (fun g hg => ⟨event g hg, good g hg⟩) hlam hAloc hKann hendpt hrho2 hline4 hline5 hline8
    hmaxint hmaxnar hCtime

end SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions
