import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.T58
import LQGMetric.Field.MarkovWeyl2Rad




 



















set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Laplacian
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Producer

open LQGMetric (DistC TestC addFun testCont)

 

 
theorem disconnects_preimage_homeomorph (φ : ℂ ≃ₜ ℂ) {K E F : Set ℂ} :
    Disconnects (φ ⁻¹' K) (φ ⁻¹' E) (φ ⁻¹' F) ↔ Disconnects K E F := by
  unfold Disconnects
  refine not_congr ⟨?_, ?_⟩
  · rintro ⟨S, hS, hK, ⟨x, hxS, hxE⟩, ⟨y, hyS, hyF⟩⟩
    refine ⟨φ '' S, hS.image φ φ.continuous.continuousOn, ?_, ⟨φ x, ⟨x, hxS, rfl⟩, hxE⟩,
      ⟨φ y, ⟨y, hyS, rfl⟩, hyF⟩⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hK hw
  · rintro ⟨S, hS, hK, ⟨x, hxS, hxE⟩, ⟨y, hyS, hyF⟩⟩
    refine ⟨φ ⁻¹' S, ?_, fun w hw => hK hw, ⟨φ.symm x, ?_, ?_⟩, ⟨φ.symm y, ?_, ?_⟩⟩
    · rw [← φ.image_symm]
      exact hS.image φ.symm φ.symm.continuous.continuousOn
    · show φ (φ.symm x) ∈ S; rw [φ.apply_symm_apply]; exact hxS
    · show φ (φ.symm x) ∈ E; rw [φ.apply_symm_apply]; exact hxE
    · show φ (φ.symm y) ∈ S; rw [φ.apply_symm_apply]; exact hyS
    · show φ (φ.symm y) ∈ F; rw [φ.apply_symm_apply]; exact hyF

 
theorem lqgDisconnects_shift {z : ℂ} {X X₀ E E₀ F F₀ : Set ℂ} (hX : ∀ w, w ∈ X₀ ↔ w + z ∈ X)
    (hE : ∀ w, w ∈ E₀ ↔ w + z ∈ E) (hF : ∀ w, w ∈ F₀ ↔ w + z ∈ F)
    (h : LQGMetric.Disconnects X₀ E₀ F₀) : LQGMetric.Disconnects X E F := by
  intro x y γ hx hy
  have hx₀ : x - z ∈ E₀ := (hE _).2 (by rw [sub_add_cancel]; exact hx)
  have hy₀ : y - z ∈ F₀ := (hF _).2 (by rw [sub_add_cancel]; exact hy)
  obtain ⟨p, ⟨t, rfl⟩, hp⟩ := h (x - z) (y - z) (γ.map (continuous_sub_right z)) hx₀ hy₀
  refine ⟨γ t, ⟨t, rfl⟩, ?_⟩
  have := (hX _).1 hp
  rwa [Path.map_coe, Function.comp_apply, sub_add_cancel] at this

 

section shift

variable {D E : LSCMetric} {k : ℝ} {z : ℂ}

 
theorem setDist_shift (hk : 0 < k)
    (hE : ∀ a b : ℂ, E (a, b) = ENNReal.ofReal k * D (a + z, b + z)) {A A₀ B B₀ : Set ℂ}
    (hA : ∀ w, w ∈ A₀ ↔ w + z ∈ A) (hB : ∀ w, w ∈ B₀ ↔ w + z ∈ B) :
    OptimalConstants.Ratios.setDist E A₀ B₀ = ENNReal.ofReal k * OptimalConstants.Ratios.setDist D A B := by
  have hk0 : ENNReal.ofReal k ≠ 0 := by simpa using hk
  unfold OptimalConstants.Ratios.setDist
  apply le_antisymm
  · simp_rw [ENNReal.mul_iInf_of_ne hk0 ENNReal.ofReal_ne_top]
    refine le_iInf₂ fun a ha => le_iInf₂ fun b hb => ?_
    have ha₀ : a - z ∈ A₀ := (hA _).2 (by rw [sub_add_cancel]; exact ha)
    have hb₀ : b - z ∈ B₀ := (hB _).2 (by rw [sub_add_cancel]; exact hb)
    refine iInf₂_le_of_le (a - z) ha₀ (iInf₂_le_of_le (b - z) hb₀ (le_of_eq ?_))
    exact shift_apply hE a b
  · refine le_iInf₂ fun a ha => le_iInf₂ fun b hb => ?_
    rw [hE]
    gcongr
    exact iInf₂_le_of_le (a + z) ((hA a).1 ha) (iInf₂_le (b + z) ((hB b).1 hb))

 
def annulusShift (A : EuclideanAnnulus) (z : ℂ) : EuclideanAnnulus := ⟨(A.center + z, A.1.2), A.2⟩

theorem annulusShift_center (A : EuclideanAnnulus) (z : ℂ) :
    (annulusShift A z).center = A.center + z := rfl

theorem annulusShift_innerRadius (A : EuclideanAnnulus) (z : ℂ) :
    (annulusShift A z).innerRadius = A.innerRadius := rfl

theorem annulusShift_outerRadius (A : EuclideanAnnulus) (z : ℂ) :
    (annulusShift A z).outerRadius = A.outerRadius := rfl

theorem mem_ball_add (c z w : ℂ) (ρ : ℝ) : w ∈ ball c ρ ↔ w + z ∈ ball (c + z) ρ := by
  rw [mem_ball, mem_ball, dist_add_right]

theorem mem_closedBall_add (c z w : ℂ) (ρ : ℝ) : w ∈ closedBall c ρ ↔ w + z ∈ closedBall (c + z) ρ := by
  rw [mem_closedBall, mem_closedBall, dist_add_right]

theorem mem_sphere_add (c z w : ℂ) (ρ : ℝ) : w ∈ sphere c ρ ↔ w + z ∈ sphere (c + z) ρ := by
  rw [mem_sphere, mem_sphere, dist_add_right]

theorem mem_toSet_shift (A : EuclideanAnnulus) (z w : ℂ) :
    w ∈ A.toSet ↔ w + z ∈ (annulusShift A z).toSet := by
  have h1 : (0 : ℝ) < A.innerRadius := A.2.1
  unfold EuclideanAnnulus.toSet
  rw [annulusShift_center, annulusShift_innerRadius, annulusShift_outerRadius,
    closure_ball _ h1.ne', closure_ball _ h1.ne', Set.mem_sdiff, Set.mem_sdiff, mem_ball_add A.center z w,
    mem_closedBall_add A.center z w]

 
theorem aroundDist_shift (hk : 0 < k)
    (hE : ∀ a b : ℂ, E (a, b) = ENNReal.ofReal k * D (a + z, b + z)) (A : EuclideanAnnulus) :
    aroundDist E A = ENNReal.ofReal k * aroundDist D (annulusShift A z) := by
  have hk0 : ENNReal.ofReal k ≠ 0 := by simpa using hk
  
  have hdisc : ∀ (Q : ℝ → ℂ) (a b : ℝ),
      Disconnects (Q '' Icc a b) A.innerBoundary A.outerBoundary ↔
        Disconnects ((fun t => Q t + z) '' Icc a b) (annulusShift A z).innerBoundary
          (annulusShift A z).outerBoundary := by
    intro Q a b
    have e1 : (Homeomorph.addRight z) ⁻¹' ((fun t => Q t + z) '' Icc a b) = Q '' Icc a b := by
      ext w
      simp only [mem_preimage, Homeomorph.coe_addRight, mem_image]
      constructor
      · rintro ⟨t, ht, h⟩; exact ⟨t, ht, add_right_cancel h⟩
      · rintro ⟨t, ht, h⟩; exact ⟨t, ht, by rw [h]⟩
    have e2 : (Homeomorph.addRight z) ⁻¹' (annulusShift A z).innerBoundary = A.innerBoundary := by
      ext w
      simp only [mem_preimage, Homeomorph.coe_addRight, EuclideanAnnulus.innerBoundary,
        annulusShift_center, annulusShift_innerRadius]
      exact (mem_sphere_add A.center z w A.innerRadius).symm
    have e3 : (Homeomorph.addRight z) ⁻¹' (annulusShift A z).outerBoundary = A.outerBoundary := by
      ext w
      simp only [mem_preimage, Homeomorph.coe_addRight, EuclideanAnnulus.outerBoundary,
        annulusShift_center, annulusShift_outerRadius]
      exact (mem_sphere_add A.center z w A.outerRadius).symm
    have key := disconnects_preimage_homeomorph (Homeomorph.addRight z)
      (K := (fun t => Q t + z) '' Icc a b) (E := (annulusShift A z).innerBoundary)
      (F := (annulusShift A z).outerBoundary)
    rw [e1, e2, e3] at key
    exact key
  apply le_antisymm
  · show _ ≤ ENNReal.ofReal k * ⨅ (P : ℝ → ℂ) (a : ℝ) (b : ℝ) (_ : D.IsCurve P a b)
        (_ : ∀ t ∈ Icc a b, P t ∈ (annulusShift A z).toSet)
        (_ : Disconnects (P '' Icc a b) (annulusShift A z).innerBoundary
          (annulusShift A z).outerBoundary), D.len P a b
    simp_rw [ENNReal.mul_iInf_of_ne hk0 ENNReal.ofReal_ne_top]
    refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hc => le_iInf fun hin =>
      le_iInf fun hdis => ?_
    rw [← len_sub hE]
    have hQ : (fun t => (P t - z) + z) = P := funext fun t => sub_add_cancel (P t) z
    refine iInf_le_of_le (fun t => P t - z) <| iInf_le_of_le a <| iInf_le_of_le b <|
      iInf_le_of_le ((isCurve_sub_iff hk hE P a b).2 hc) <| iInf_le_of_le ?_ <| iInf_le _ ?_
    · intro t ht
      rw [mem_toSet_shift A z, sub_add_cancel]
      exact hin t ht
    · rw [hdisc, hQ]
      exact hdis
  · refine le_iInf fun Q => le_iInf fun a => le_iInf fun b => le_iInf fun hc => le_iInf fun hin =>
      le_iInf fun hdis => ?_
    have hQ : (fun t => (Q t + z) - z) = Q := funext fun t => add_sub_cancel_right (Q t) z
    have hc' : D.IsCurve (fun t => Q t + z) a b :=
      (isCurve_sub_iff hk hE (fun t => Q t + z) a b).1 (by rw [hQ]; exact hc)
    have hlen : E.len Q a b = ENNReal.ofReal k * D.len (fun t => Q t + z) a b := by
      rw [← len_sub hE, hQ]
    rw [hlen]
    gcongr
    refine iInf_le_of_le (fun t => Q t + z) <| iInf_le_of_le a <| iInf_le_of_le b <|
      iInf_le_of_le hc' <| iInf_le_of_le ?_ <| iInf_le _ ?_
    · intro t ht
      exact (mem_toSet_shift A z (Q t)).1 (hin t ht)
    · exact (hdisc Q a b).1 hdis

 

theorem hasTubeSeparator_shift (hk : 0 < k)
    (hE : ∀ a b : ℂ, E (a, b) = ENNReal.ofReal k * D (a + z, b + z)) {r : Set.Ioi (0 : ℝ)}
    {U U₀ : TopologicalSpace.Opens ℂ} (hU : ∀ w, w ∈ (U₀ : Set ℂ) ↔ w + z ∈ (U : Set ℂ)) {B : ℝ≥0∞}
    (h : EndSaving.Interfaces.HasTubeSeparator E 0 r U₀ (ENNReal.ofReal k * B)) : EndSaving.Interfaces.HasTubeSeparator D z r U B := by
  obtain ⟨π, a, b, hc, hin, hdis, hlen⟩ := h
  have hQ : (fun t => (π t + z) - z) = π := funext fun t => add_sub_cancel_right (π t) z
  refine ⟨fun t => π t + z, a, b, (isCurve_sub_iff hk hE (fun t => π t + z) a b).1 (by rw [hQ]; exact hc),
    fun t ht => (hU _).1 (hin t ht), ?_, ?_⟩
  · refine lqgDisconnects_shift (z := z) (X₀ := π '' Icc a b) ?_ ?_ ?_ hdis
    · intro w
      simp only [mem_image]
      constructor
      · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
      · rintro ⟨t, ht, h⟩; exact ⟨t, ht, add_right_cancel h⟩
    · intro w; rw [mem_sphere_add 0 z w, zero_add]
    · intro w; rw [mem_sphere_add 0 z w, zero_add]
  · have h2 : E.len π a b = ENNReal.ofReal k * D.len (fun t => π t + z) a b := by
      rw [← len_sub hE, hQ]
    rw [h2] at hlen
    exact ennreal_cancel hk hlen

end shift

 

 

theorem boundsAt_of_normTranslate {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {par : EndSaving.Interfaces.Parameters ξ}
    {D D' : DistC → LSCMetric} {Wc : Set ℂ} {Cc : Set (Set.Ioi (0 : ℝ) × ℂ)} {u : DistC}
    (hgood : LocalGood (ξ : ℝ) D D' Wc Cc u) {z : ℂ} (hz : z ∈ Wc) {r : Set.Ioi (0 : ℝ)}
    {U U₀ V V₀ : TopologicalSpace.Opens ℂ} (hU : ∀ w, w ∈ (U₀ : Set ℂ) ↔ w + z ∈ (U : Set ℂ))
    (hV : ∀ w, w ∈ (V₀ : Set ℂ) ↔ w + z ∈ (V : Set ℂ))
    (h0 : BoundsAt D ξ Q par 0 r U₀ V₀ (normTranslate z u)) : BoundsAt D ξ Q par z r U V u := by
  intro c hc
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = Real.exp ((ξ : ℝ) * -(LQGMetric.circleAvg u 1 z)) := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; exact Real.exp_pos _
  have hD0 : ∀ a b : ℂ, D (normTranslate z u) (a, b) = ENNReal.ofReal κ * D u (a + z, b + z) := by
    rw [hκdef]; exact tlc_metric hgood hz
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = (r : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * c) := ⟨_, rfl⟩
  have hN0 : (r : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * (c + -(LQGMetric.circleAvg u 1 z))) =
      κ * N := by
    rw [hNdef, hκdef, mul_add, Real.exp_add]; ring
  have h := h0 _ (isCircleAverage_normTranslate hc)
  dsimp only at h ⊢
  rw [hN0, ENNReal.ofReal_mul hκ.le] at h
  rw [← hNdef]
  obtain ⟨h1, ⟨A₀, hA0, hA1, hA2, hA⟩, h3⟩ := h
  have hsph : ∀ ρ : ℝ, ∀ w, w ∈ sphere (0 : ℂ) ρ ↔ w + z ∈ sphere z ρ := fun ρ w => by
    rw [mem_sphere_add 0 z w, zero_add]
  have hS : ∀ w, w ∈ sphere (0 : ℂ) r ∪ sphere 0 (3 * (r : ℝ)) ↔
      w + z ∈ sphere z r ∪ sphere z (3 * (r : ℝ)) := fun w => by
    rw [mem_union, mem_union, hsph, hsph]
  refine ⟨?_, ⟨annulusShift A₀ z, ?_, hA1, hA2, ?_⟩, ?_⟩
  · rw [setDist_shift hκ hD0 hV hS] at h1
    refine ennreal_cancel hκ ?_
    calc ENNReal.ofReal κ * (ENNReal.ofReal par.Cacross * ENNReal.ofReal N)
        = ENNReal.ofReal par.Cacross * (ENNReal.ofReal κ * ENNReal.ofReal N) := by ring
      _ ≤ _ := h1
  · rw [annulusShift_center, hA0, zero_add]
  · rw [aroundDist_shift hκ hD0 A₀] at hA
    refine ennreal_cancel hκ ?_
    calc ENNReal.ofReal κ * aroundDist (D u) (annulusShift A₀ z) ≤
        ENNReal.ofReal par.Caround * (ENNReal.ofReal κ * ENNReal.ofReal N) := hA
      _ = ENNReal.ofReal κ * (ENNReal.ofReal par.Caround * ENNReal.ofReal N) := by ring
  · refine hasTubeSeparator_shift hκ hD0 hU ?_
    have e : ENNReal.ofReal par.Ctube * (ENNReal.ofReal κ * ENNReal.ofReal N) =
        ENNReal.ofReal κ * (ENNReal.ofReal par.Ctube * ENNReal.ofReal N) := by ring
    rw [← e]
    exact h3

 

 
theorem gradEnergy_comp_sub (f : ℂ → ℝ) (z : ℂ) :
    LQGMetric.gradEnergy (fun y => f (y - z)) = LQGMetric.gradEnergy f := by
  unfold LQGMetric.gradEnergy
  congr 1
  simp_rw [fderiv_comp_sub]
  exact integral_sub_right_eq_self (fun x => ‖fderiv ℝ f x‖ ^ 2) z

 

theorem cmDensity_translate {f f₀ : TestC} {z : ℂ} (hf : ∀ x, f x = f₀ (x - z)) (u : DistC) :
    LQGMetric.cmDensity f (LQGMetric.pair0 u) =
      LQGMetric.cmDensity f₀ (LQGMetric.pair0 (normTranslate z u)) := by
  have hfun : (⇑f : ℂ → ℝ) = fun y => f₀ (y - z) := funext hf
  have hcm : LQGMetric.cmTest f = testTranslate z (LQGMetric.cmTest f₀) := by
    ext x
    rw [testTranslate_apply, LQGMetric.cmTest_apply, LQGMetric.cmTest_apply, hfun,
      LQGMetric.MarkovWeyl2.laplacian_comp_sub]
  have hpair : LQGMetric.pair0 u (LQGMetric.cmTest0 f) =
      LQGMetric.pair0 (normTranslate z u) (LQGMetric.cmTest0 f₀) := by
    show u (LQGMetric.cmTest f) = normTranslate z u (LQGMetric.cmTest f₀)
    rw [hcm, normTranslate, LQGMetric.GFFInv.addConst_apply, LQGMetric.integral_cmTest, zero_mul,
      add_zero]
    rfl
  have hen : LQGMetric.gradEnergy f = LQGMetric.gradEnergy f₀ := by
    rw [hfun, gradEnergy_comp_sub]
  unfold LQGMetric.cmDensity
  rw [hpair, hen]

 

 

theorem bounds_input_of_centre0 {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {par : EndSaving.Interfaces.Parameters ξ}
    {D D' : DistC → LSCMetric} {z : ℂ} {r : Set.Ioi (0 : ℝ)} {U U₀ V V₀ : TopologicalSpace.Opens ℂ}
    (hU : ∀ w, w ∈ (U₀ : Set ℂ) ↔ w + z ∈ (U : Set ℂ))
    (hV : ∀ w, w ∈ (V₀ : Set ℂ) ↔ w + z ∈ (V : Set ℂ)) {Target : Set DistC}
    (h0 : ∀ g ∈ Target, BoundsAt D ξ Q par 0 r U₀ V₀ g) :
    ∀ u, LocalGood (ξ : ℝ) D D' {z} (circleFamily z r) u → normTranslate z u ∈ Target →
      BoundsAt D ξ Q par z r U V u :=
  fun _ hgood hT => boundsAt_of_normTranslate hgood (Set.mem_singleton z) hU hV (h0 _ hT)

 

theorem rn_input_of_centre0 {ξ : Set.Ioi (0 : ℝ)} {par : EndSaving.Interfaces.Parameters ξ} {D D' : DistC → LSCMetric}
    {z : ℂ} {r : Set.Ioi (0 : ℝ)} {f f₀ : TestC} (hf : ∀ x, f x = f₀ (x - z)) {Target : Set DistC}
    (h0 : ∀ g ∈ Target, par.Crn⁻¹ ≤ LQGMetric.cmDensity f₀ (LQGMetric.pair0 g) ∧
      LQGMetric.cmDensity f₀ (LQGMetric.pair0 g) ≤ par.Crn) :
    ∀ u, LocalGood (ξ : ℝ) D D' {z} (circleFamily z r) u → normTranslate z u ∈ Target →
      par.Crn⁻¹ ≤ LQGMetric.cmDensity f (LQGMetric.pair0 u) ∧
        LQGMetric.cmDensity f (LQGMetric.pair0 u) ≤ par.Crn := by
  intro u _ hT
  rw [cmDensity_translate hf u]
  exact h0 _ hT

end SupercriticalLQGUniqueness.Uniqueness.Objects.Producer
