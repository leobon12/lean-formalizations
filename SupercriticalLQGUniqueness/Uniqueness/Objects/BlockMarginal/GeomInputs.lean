import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.NineLocal
import SupercriticalLQGUniqueness.Uniqueness.Objects.TubeBridge.ForwardTube
import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.C8




 













set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric Filter
open LQGMetric.Blueprint
open scoped ENNReal Topology

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal

open LQGMetric (DistC)

theorem norm_le_of_mem_bigAnn (C : Objects.CorrectedEvent.Constants) {x : ℂ} (hx : x ∈ bigAnn C) :
    C.r ≤ ‖x‖ ∧ ‖x‖ ≤ 4 * C.r := by
  have := hx
  simp only [bigAnn, Objects.CorrectedEvent.cann, mem_ofPred_eq, dist_zero_right] at this
  exact this

theorem mem_bigAnn_of_norm (C : Objects.CorrectedEvent.Constants) {x : ℂ} (h1 : C.r ≤ ‖x‖) (h2 : ‖x‖ ≤ 4 * C.r) :
    x ∈ bigAnn C := by
  simp only [bigAnn, Objects.CorrectedEvent.cann, mem_ofPred_eq, dist_zero_right]
  exact ⟨h1, h2⟩

 
theorem closedBall_subset_bigAnn_of_norm (C : Objects.CorrectedEvent.Constants) {c : ℂ} {R a b : ℝ}
    (hca : a ≤ ‖c‖) (hcb : ‖c‖ ≤ b) (h1 : C.r ≤ a - R) (h2 : b + R ≤ 4 * C.r) :
    closedBall c R ⊆ bigAnn C := by
  intro x hx
  rw [mem_closedBall, dist_eq_norm] at hx
  have t1 := norm_sub_norm_le c x
  have t2 := norm_le_insert' x c
  rw [norm_sub_rev] at t1
  apply mem_bigAnn_of_norm C
  · linarith
  · linarith

 
theorem tubeV_subset (C : Objects.CorrectedEvent.Constants) (P : Objects.Tube.TubeParams) (hP : P.Good)
    (hSmall : 100 * C.A_sup ≤ P.sp * P.ρ) (ρ₀ : ℝ) (X : Finset ℂ)
    (hwp : P.wp = C.lamConst * C.A_endpt) :
    Objects.CorrectedEvent.tubeV (Objects.TubeBridge.tubeDataOf C P hP hSmall ρ₀ X) C.A_sup ⊆
      {x : ℂ | (3 / 2) * C.r < ‖x‖ ∧ ‖x‖ < (5 / 2) * C.r} := by
  rw [Objects.TubeBridge.tubeDataOf_tubeV_eq C P hP hSmall ρ₀ X hwp]
  exact (Objects.Tube.TubeParams.nbhd_and_thickening_subset_annulus (P := P) (r := C.r) (Asup := C.A_sup) hP C.rPos hSmall).1

theorem tubeSet_subset_tubeV (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (hTr : 0 < T.r) :
    Objects.CorrectedEvent.tubeSet T ⊆ Objects.CorrectedEvent.tubeV T C.A_sup := by
  intro x hx
  exact ⟨x, hx, by rw [dist_self]; exact mul_pos C.supPos hTr⟩

theorem closure_tubeV_subset_bigAnn (C : Objects.CorrectedEvent.Constants) (P : Objects.Tube.TubeParams) (hP : P.Good)
    (hSmall : 100 * C.A_sup ≤ P.sp * P.ρ) (ρ₀ : ℝ) (X : Finset ℂ)
    (hwp : P.wp = C.lamConst * C.A_endpt) :
    closure (Objects.CorrectedEvent.tubeV (Objects.TubeBridge.tubeDataOf C P hP hSmall ρ₀ X) C.A_sup) ⊆ bigAnn C := by
  have hr := C.rPos
  have hcl : IsClosed {x : ℂ | (3 / 2) * C.r ≤ ‖x‖ ∧ ‖x‖ ≤ (5 / 2) * C.r} :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  refine (closure_minimal ((tubeV_subset C P hP hSmall ρ₀ X hwp).trans ?_) hcl).trans ?_
  · intro x hx
    exact ⟨hx.1.le, hx.2.le⟩
  · intro x hx
    exact mem_bigAnn_of_norm C (by linarith [hx.1]) (by linarith [hx.2])

 
theorem bump_tsupport_subset (C : Objects.CorrectedEvent.Constants) (P : Objects.Tube.TubeParams) (hP : P.Good)
    (hSmall : 100 * C.A_sup ≤ P.sp * P.ρ) (ρ₀ : ℝ) (X : Finset ℂ)
    (hwp : P.wp = C.lamConst * C.A_endpt) :
    tsupport ((Objects.TubeBridge.tubeDataOf C P hP hSmall ρ₀ X).bump : ℂ → ℝ) ⊆ bigAnn C := by
  refine (closure_mono ?_).trans (closure_tubeV_subset_bigAnn C P hP hSmall ρ₀ X hwp)
  intro x hx
  by_contra hxV
  exact hx ((Objects.TubeBridge.tubeDataOf_bump_shape C P hP hSmall ρ₀ X hwp).2.2 x hxV)

 
theorem netBall_subset (C : Objects.CorrectedEvent.Constants) (P : Objects.Tube.TubeParams) (hP : P.Good)
    (hSmall : 100 * C.A_sup ≤ P.sp * P.ρ) (ρ₀ : ℝ) (X : Finset ℂ)
    (hwp : P.wp = C.lamConst * C.A_endpt)
    (hData : Objects.CorrectedEvent.DataMatch C (Objects.TubeBridge.tubeDataOf C P hP hSmall ρ₀ X)) :
    ∀ x ∈ (Objects.TubeBridge.tubeDataOf C P hP hSmall ρ₀ X).netSites,
      closedBall x (2 * (Objects.TubeBridge.tubeDataOf C P hP hSmall ρ₀ X).netRadius) ⊆ bigAnn C := by
  intro x hx
  have hM1 : ∀ y ∈ (Objects.TubeBridge.tubeDataOf C P hP hSmall ρ₀ X).netSites,
      closedBall y (2 * (Objects.TubeBridge.tubeDataOf C P hP hSmall ρ₀ X).netRadius) ⊆
        Objects.CorrectedEvent.tubeSet (Objects.TubeBridge.tubeDataOf C P hP hSmall ρ₀ X) := by
    unfold Objects.CorrectedEvent.DataMatch at hData
    tauto
  refine (hM1 x hx).trans ((tubeSet_subset_tubeV C _ C.rPos).trans
    (subset_closure.trans (closure_tubeV_subset_bigAnn C P hP hSmall ρ₀ X hwp)))

 
theorem cellBall_subset (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (hData : Objects.CorrectedEvent.DataMatch C T)
    (hlam : C.lamConst ≤ 1 / 48) (hE : C.A_endpt ≤ 1) (hK0 : 0 ≤ C.K_ann) :
    ∀ k : Fin T.K, ∀ l : Objects.CorrectedEvent.Cell, ∀ j ∈ Finset.Icc 1 (Objects.CorrectedEvent.supK C),
      closedBall (Objects.CorrectedEvent.cellCenter (Objects.CorrectedEvent.innerCenter T k) T.blockRadius l)
          (3 * Objects.CorrectedEvent.supRadius C j) ⊆ bigAnn C ∧
        closedBall (Objects.CorrectedEvent.cellCenter (Objects.CorrectedEvent.outerCenter T k) T.blockRadius l)
          (3 * Objects.CorrectedEvent.supRadius C j) ⊆ bigAnn C := by
  intro k l j hj
  have hr : T.r = C.r := hData.1
  have hρ : T.rho = C.ρ := hData.2.1
  have hα : T.alpha = C.K_ann := hData.2.2.2.2.1
  have hn4 : T.orientation ^ 4 = 1 := hData.2.2.2.2.2.2.1
  have hn := Objects.Producer.norm_orientation hn4
  have hrp := C.rPos
  have hρp := C.rhoPos
  have hρ1 := Objects.Producer.rho_lt_of_constants C hlam
  have hK1 := Objects.Producer.kann_lt_one C
  obtain ⟨hb0, hb1⟩ := Objects.Producer.blockRadius_bounds C T hData hE
  have hR := (Objects.Producer.supRadius_bounds C hj).2
  have hsite : ‖Objects.CorrectedEvent.site T k‖ = 2 * C.r := by rw [Objects.Producer.norm_site T (hr ▸ hrp) k, hr]
  have hTρ : 0 < T.rho := hρ ▸ hρp
  have hTr : 0 < T.r := hr ▸ hrp
  
  have hin : ‖Objects.CorrectedEvent.innerCenter T k - Objects.CorrectedEvent.site T k‖ ≤ C.ρ * C.r := by
    rw [Objects.CorrectedEvent.innerCenter, Objects.Producer.norm_moduleMap_sub_site T hTρ hTr hn, Objects.CorrectedEvent.uNorm, Objects.Producer.norm_polar,
      hα, abs_of_nonneg hK0, hρ, hr]
    nlinarith
  have hout : ‖Objects.CorrectedEvent.outerCenter T k - Objects.CorrectedEvent.site T k‖ ≤ C.ρ * C.r := by
    rw [Objects.CorrectedEvent.outerCenter, Objects.Producer.norm_moduleMap_sub_site T hTρ hTr hn, Objects.CorrectedEvent.vNorm, Objects.Producer.norm_polar,
      abs_one, mul_one, hρ, hr]
  have key : ∀ c : ℂ, ‖c - Objects.CorrectedEvent.site T k‖ ≤ C.ρ * C.r →
      closedBall (Objects.CorrectedEvent.cellCenter c T.blockRadius l) (3 * Objects.CorrectedEvent.supRadius C j) ⊆ bigAnn C := by
    intro c hc
    have hcell : ‖Objects.CorrectedEvent.cellCenter c T.blockRadius l - c‖ = T.blockRadius :=
      Objects.Producer.norm_cellCenter_sub c hb0.le l
    have hd : ‖Objects.CorrectedEvent.cellCenter c T.blockRadius l - Objects.CorrectedEvent.site T k‖ ≤ 2 * (C.ρ * C.r) := by
      calc _ = ‖(Objects.CorrectedEvent.cellCenter c T.blockRadius l - c) + (c - Objects.CorrectedEvent.site T k)‖ := by
            congr 1; ring
        _ ≤ ‖Objects.CorrectedEvent.cellCenter c T.blockRadius l - c‖ + ‖c - Objects.CorrectedEvent.site T k‖ := norm_add_le _ _
        _ ≤ C.ρ * C.r + C.ρ * C.r := by rw [hcell]; linarith
        _ = 2 * (C.ρ * C.r) := by ring
    have t1 := norm_sub_norm_le (Objects.CorrectedEvent.cellCenter c T.blockRadius l) (Objects.CorrectedEvent.site T k)
    have t2 := norm_sub_norm_le (Objects.CorrectedEvent.site T k) (Objects.CorrectedEvent.cellCenter c T.blockRadius l)
    rw [norm_sub_rev (Objects.CorrectedEvent.site T k)] at t2
    apply closedBall_subset_bigAnn_of_norm C (a := 2 * C.r - 2 * (C.ρ * C.r))
      (b := 2 * C.r + 2 * (C.ρ * C.r))
    · linarith
    · linarith
    · nlinarith
    · nlinarith
  exact ⟨key _ hin, key _ hout⟩

 
theorem siteBall_subset (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (hData : Objects.CorrectedEvent.DataMatch C T)
    (hloc : 3 * C.A_loc * C.ρ < 1) :
    ∀ k : Fin T.K, ball (Objects.CorrectedEvent.site T k) (3 * C.A_loc * (C.ρ * C.r)) ⊆ bigAnn C := by
  intro k
  have hr : T.r = C.r := hData.1
  have hrp := C.rPos
  have hsite : ‖Objects.CorrectedEvent.site T k‖ = 2 * C.r := by rw [Objects.Producer.norm_site T (hr ▸ hrp) k, hr]
  have hR : 3 * C.A_loc * (C.ρ * C.r) ≤ C.r := by nlinarith
  refine (ball_subset_closedBall).trans ?_
  apply closedBall_subset_bigAnn_of_norm C (a := 2 * C.r) (b := 2 * C.r) hsite.ge hsite.le
  · linarith
  · linarith

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal
