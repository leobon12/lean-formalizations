import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.LowerV2
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents.ObjectAroundV2




 












set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Finset LQGMetric.MetricGeometry Filter
open scoped ENNReal Topology

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices

open LQGMetric (DistC TestC)

section BumpAlgebra

variable {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r : Set.Ioi (0 : ℝ))
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)

theorem bumpSum_union (Keep R : Finset (ℤ × ℤ)) (hKR : Disjoint Keep R) :
    EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj (Keep ∪ R) =
      EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj Keep +
        EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj R := by
  unfold EndSaving.FiniteEvents.bumpSumV2
  exact Finset.sum_union hKR

 
theorem addFun_subtract_union (Keep R : Finset (ℤ × ℤ)) (hKR : Disjoint Keep R)
    (g : DistC) :
    LQGMetric.addFun (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj (Keep ∪ R) g)
      (LQGMetric.testCont (EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj R)) =
      EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Keep g := by
  unfold EndSaving.FiniteEvents.subtractBumpsV2
  rw [bumpSum_union μ h D D' ξ Q cMid par pbar r obj Keep R hKR]
  exact addFun_subTest_part g _ _

 
theorem addFun_subtract_self (W : Finset (ℤ × ℤ)) (g : DistC) :
    LQGMetric.addFun (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj W g)
      (LQGMetric.testCont (EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj W)) = g := by
  unfold EndSaving.FiniteEvents.subtractBumpsV2
  exact addFun_subTest_self g _

 
theorem bumpSum_zero_near_site (b : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (Z W : Finset (ℤ × ℤ)) (hconfig : EndSaving.Interfaces.Configuration r b K₁ K₂ Z) (hW : W ⊆ Z)
    (i : ℤ × ℤ) (hi : i ∈ Z) (x : ℂ)
    (hx : x ∈ ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) (4 * (r : ℝ)))
    (hxV : x ∉ ((obj i).V : Set ℂ)) :
    EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj W x = 0 := by
  rw [bumpSum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hji : j = i
  · subst hji; exact (obj j).f_off_V x hxV
  · apply (obj j).f_off_V x
    intro hxj
    have hj4 : x ∈ ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) j) (4 * (r : ℝ)) := by
      have h3 := ((obj j).V_annular).1 hxj
      rw [mem_ball]
      have hr : (0 : ℝ) < r := r.property
      change (r : ℝ) < dist x (LQGMetric.GM.gridPt ((r : ℝ) / 100) j) ∧
        dist x (LQGMetric.GM.gridPt ((r : ℝ) / 100) j) < 3 * (r : ℝ) at h3
      linarith [h3.2]
    exact Set.disjoint_left.mp (hconfig.1 j (hW hj) i hi hji) hj4 hx

 
theorem bumpSum_zero_off_tubes (W : Finset (ℤ × ℤ)) (x : ℂ)
    (hx : ∀ i ∈ W, x ∉ ((obj i).V : Set ℂ)) :
    EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj W x = 0 := by
  rw [bumpSum_apply]
  exact Finset.sum_eq_zero fun i hi => (obj i).f_off_V x (hx i hi)

 
theorem bumpSum_le_Cmax (b : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (Z W : Finset (ℤ × ℤ)) (hconfig : EndSaving.Interfaces.Configuration r b K₁ K₂ Z) (hW : W ⊆ Z) (x : ℂ) :
    EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj W x ≤ par.Cmax := by
  rw [bumpSum_apply]
  have hdisj := EndSaving.FiniteEvents.configuration_V_disjoint_v2 μ h D D' ξ Q cMid par pbar r b K₁ K₂ Z obj
    hconfig
  exact (EndSaving.FiniteEvents.finite_bump_values_bounds_v2 μ h D D' ξ Q cMid par pbar r W
    (fun j => LQGMetric.GM.gridPt ((r : ℝ) / 100) j) obj
    (fun i hi j hj hij => hdisj i (hW hi) j (hW hj) hij) x).2

end BumpAlgebra

 
theorem setDist_sphere_tube_ge (D : LSCMetric) (V S S' : Set ℂ) (hS : S ⊆ S') :
    OptimalConstants.Ratios.setDist D V S' ≤ OptimalConstants.Ratios.setDist D S V := by
  refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
  rw [D.isExtMetric.2.2.1 x y]
  exact iInf₂_le_of_le y hy (iInf₂_le x (hS hx))

 

theorem lower_general_v2 {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z Keep R : Finset (ℤ × ℤ)) (hconfig : EndSaving.Interfaces.Configuration r b K₁ K₂ Z)
    (hKeep : Keep ⊆ Z) (hR : R ⊆ Z) (hKR : Disjoint Keep R)
    (ω : Ω)
    (hreg : RegularAt D (ξ : ℝ)
      (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj (Keep ∪ R) (h ω)))
    (hE : ∀ i ∈ R, h ω ∈ (obj i).E)
    (P : ℝ → ℂ) (T : ℝ)
    (hgeod : EndSaving.FiniteEvents.SetGeodesic
      (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj (Keep ∪ R) (h ω)))
      K₁ K₂ P T) :
    ∃ hfin : ∀ i ∈ R, (ovSet P T
        (ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) (4 * (r : ℝ))) (obj i).V).Finite,
      (∀ i (hi : i ∈ R), ((hfin i hi).toFinset.card : ℝ) * par.Cacross ≤ par.Caround) ∧
      OptimalConstants.Ratios.setDist (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Keep (h ω)))
          K₁ K₂ ≤
        OptimalConstants.Ratios.setDist
            (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj (Keep ∪ R) (h ω)))
            K₁ K₂ +
          ∑ i ∈ R.attach, ∑ e ∈ (hfin i.1 i.2).toFinset,
            D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Keep (h ω))
              (P e.2.1, P e.2.2.1) := by
  set W := Keep ∪ R with hWdef
  have hWZ : W ⊆ Z := Finset.union_subset hKeep hR
  set d1 := D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj W (h ω)) with hd1
  set d0 := D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Keep (h ω)) with hd0
  set Dh := D (h ω) with hDh
  set fW := EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj W with hfW
  set fR := EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj R with hfR
  set z : ℤ × ℤ → ℂ := fun i => LQGMetric.GM.gridPt ((r : ℝ) / 100) i with hz
  have hr0 : (0 : ℝ) < r := r.property
  have hξ : (0 : ℝ) ≤ ξ := ξ.property.le
  have hW0 : ∀ p : ℂ × ℂ, d0 p = weylScale ξ (LQGMetric.testCont fR) d1 p := by
    intro p
    rw [hreg.weyl, hd0, ← addFun_subtract_union μ h D D' ξ Q cMid par pbar r obj Keep R hKR]
  have hWh : ∀ p : ℂ × ℂ, Dh p = weylScale ξ (LQGMetric.testCont fW) d1 p := by
    intro p
    rw [hreg.weyl, hDh, addFun_subtract_self]
  have hG : IsGeodesicCurve (d1.pt ∘ P) 0 T := EndSaving.FiniteEvents.SetGeodesic.isGeodesic d1 K₁ K₂ P T hgeod
  have hu : HasUnitSpeedOn (d1.pt ∘ P) (Icc 0 T) := hgeod.1.2.1
  have hP : ContinuousOn P (Icc 0 T) := hreg.continuousOn ⟨hG.1, hG.2.1⟩
  have hout : ∀ i ∈ Z, ∀ x ∈ K₁ ∪ K₂, x ∉ ball (z i) (4 * (r : ℝ)) := by
    intro i hi x hx hball
    exact Set.disjoint_left.mp (hconfig.2 i hi) hball (Or.inl hx)
  have hP0 : ∀ i ∈ R, P 0 ∉ ball (z i) (4 * (r : ℝ)) :=
    fun i hi => hout i (hR hi) (P 0) (Or.inl hgeod.2.1)
  have hPT : ∀ i ∈ R, P T ∉ ball (z i) (4 * (r : ℝ)) :=
    fun i hi => hout i (hR hi) (P T) (Or.inr hgeod.2.2.1)
  have hV : ∀ i ∈ R, closure (((obj i).V : Set ℂ)) ⊆ ball (z i) (3 * (r : ℝ)) :=
    fun i _ x hx => mem_ball.mpr ((obj i).closure_V_annulus hx).2
  have hfWn : ∀ x, 0 ≤ (LQGMetric.testCont fW) x := fun x =>
    bumpSum_nonneg μ h D D' ξ Q cMid par pbar r obj W x
  have hfWC : ∀ x, (ξ : ℝ) * (LQGMetric.testCont fW) x ≤ (ξ : ℝ) * par.Cmax := fun x =>
    mul_le_mul_of_nonneg_left
      (bumpSum_le_Cmax μ h D D' ξ Q cMid par pbar r obj b K₁ K₂ Z W hconfig hWZ x) hξ
  
  have hsite : ∀ i ∈ R, ∃ hfin : (ovSet P T (ball (z i) (4 * (r : ℝ))) (obj i).V).Finite,
      (hfin.toFinset.card : ℝ) * par.Cacross ≤ par.Caround := by
    intro i hi
    obtain ⟨c, hc⟩ := (obj i).E_circle (h ω) (hE i hi)
    set N := scaleN ξ Q r c with hN
    have hNpos : 0 < N := scaleN_pos ξ Q r c
    obtain ⟨hcross, _, _⟩ := (obj i).E_bounds (h ω) (hE i hi) c hc
    have hcharge : ENNReal.ofReal (par.Cacross * N) ≤
        OptimalConstants.Ratios.setDist Dh (sphere (z i) (3 * (r : ℝ))) ((obj i).V : Set ℂ) := by
      rw [ENNReal.ofReal_mul par.across_pos.le]
      exact hcross.trans (setDist_sphere_tube_ge Dh _ _ _ subset_union_right)
    have hf0 : ∀ x ∈ ball (z i) (4 * (r : ℝ)), x ∉ ((obj i).V : Set ℂ) →
        (LQGMetric.testCont fW) x = 0 := fun x hx hxV =>
      bumpSum_zero_near_site μ h D D' ξ Q cMid par pbar r obj b K₁ K₂ Z W hconfig hWZ i
        (hR hi) x hx hxV
    have haround : (EndSaving.Spent.closedContactTimes P ((obj i).V : Set ℂ) T).Nonempty →
        ENNReal.ofReal (EndSaving.Spent.lastClosedContact P ((obj i).V : Set ℂ) T -
          EndSaving.Spent.firstClosedContact P ((obj i).V : Set ℂ) T) ≤
          ENNReal.ofReal (par.Caround * N) := by
      intro hne
      have h4 : ∀ x : ℂ, x ∉ ball (z i) (4 * (r : ℝ)) → 4 * (r : ℝ) ≤ dist x (z i) := by
        intro x hx
        simpa only [mem_ball, not_lt] using hx
      rw [ENNReal.ofReal_mul par.around_pos.le]
      exact EndSaving.FiniteEvents.objectAtV2_around_closed_contacts μ h D D' ξ Q cMid par pbar (z i) r (obj i)
        ω (hE i hi) c hc d1 (LQGMetric.testCont fW) hreg.barrier hreg.length hWh hfWn P hG hu
        (h4 _ (hP0 i hi)) (h4 _ (hPT i hi)) hne
    obtain ⟨hfin, hcard⟩ := ovSet_finite_card d1 Dh ξ ((ξ : ℝ) * par.Cmax)
      (par.Cacross * N) (par.Caround * N) (LQGMetric.testCont fW) hWh P hG hu hP (z i) r hr0
      (obj i).V (hV i hi) hf0 hfWC hcharge (mul_pos par.across_pos hNpos)
      (mul_le_mul_of_nonneg_right par.around_gt_across.le hNpos.le) haround
    refine ⟨hfin, ?_⟩
    have : (hfin.toFinset.card : ℝ) * par.Cacross * N ≤ par.Caround * N := by
      simpa only [mul_assoc] using hcard
    exact le_of_mul_le_mul_right this hNpos
  choose hfin hcard using hsite
  refine ⟨hfin, hcard, ?_⟩
  have hfRzero : ∀ x, (∀ i ∈ R, x ∉ ((obj i).V : Set ℂ)) → (LQGMetric.testCont fR) x = 0 :=
    fun x hx => bumpSum_zero_off_tubes μ h D D' ξ Q cMid par pbar r obj R x hx
  have hmain := lower0_pathwise d1 d0 ξ (LQGMetric.testCont fR) hW0 P hG hu hP R z r hr0
    (fun i => (obj i).V) hV (fun i hi j hj hij => hconfig.1 i (hR hi) j (hR hj) hij)
    hP0 hPT hfRzero hfin
  have hset0 : OptimalConstants.Ratios.setDist d0 K₁ K₂ ≤ d0 (P 0, P T) :=
    iInf₂_le_of_le (P 0) hgeod.2.1 (iInf₂_le (P T) hgeod.2.2.1)
  rw [hgeod.2.2.2] at hmain
  exact hset0.trans hmain

 
theorem sum_le_ratio_iSup {α : Type*} (S : Set α) (F : Finset α) (hF : ↑F ⊆ S)
    (φ : α → ℝ≥0∞) (κ : ℝ) (hcard : (F.card : ℝ) ≤ κ) :
    ∑ e ∈ F, φ e ≤ ENNReal.ofReal κ * ⨆ e ∈ S, φ e := by
  calc ∑ e ∈ F, φ e ≤ ∑ _e ∈ F, ⨆ e ∈ S, φ e :=
        Finset.sum_le_sum fun e he => le_iSup₂_of_le e (hF he) le_rfl
    _ = (F.card : ℝ≥0∞) * ⨆ e ∈ S, φ e := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal κ * ⨆ e ∈ S, φ e := by
        gcongr
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal hcard

 
theorem lower_general_max_v2 {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z Keep R : Finset (ℤ × ℤ)) (hconfig : EndSaving.Interfaces.Configuration r b K₁ K₂ Z)
    (hKeep : Keep ⊆ Z) (hR : R ⊆ Z) (hKR : Disjoint Keep R)
    (ω : Ω)
    (hreg : RegularAt D (ξ : ℝ)
      (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj (Keep ∪ R) (h ω)))
    (hE : ∀ i ∈ R, h ω ∈ (obj i).E)
    (P : ℝ → ℂ) (T : ℝ)
    (hgeod : EndSaving.FiniteEvents.SetGeodesic
      (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj (Keep ∪ R) (h ω)))
      K₁ K₂ P T) :
    OptimalConstants.Ratios.setDist (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Keep (h ω)))
        K₁ K₂ ≤
      OptimalConstants.Ratios.setDist
          (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj (Keep ∪ R) (h ω)))
          K₁ K₂ +
        ENNReal.ofReal (par.Caround / par.Cacross) * ∑ i ∈ R,
          ⨆ e ∈ ovSet P T (ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) (4 * (r : ℝ)))
              (obj i).V,
            D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Keep (h ω))
              (P e.2.1, P e.2.2.1) := by
  obtain ⟨hfin, hcard, hmain⟩ := lower_general_v2 μ h D D' ξ Q cMid par pbar r b K₁ K₂ obj
    Z Keep R hconfig hKeep hR hKR ω hreg hE P T hgeod
  refine hmain.trans (add_le_add le_rfl ?_)
  rw [Finset.mul_sum, ← Finset.sum_attach R]
  refine Finset.sum_le_sum fun i _ => ?_
  apply sum_le_ratio_iSup _ _ (by simp)
  rw [le_div_iff₀ par.across_pos]
  exact hcard i.1 i.2


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices
