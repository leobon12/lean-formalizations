import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.TLC2




 



















set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Producer

open LQGMetric (DistC TestC addFun testCont)

 

 
def translateOpens (U : TopologicalSpace.Opens ℂ) (z : ℂ) : TopologicalSpace.Opens ℂ :=
  ⟨(fun w => w - z) ⁻¹' (U : Set ℂ), U.isOpen.preimage (continuous_sub_right z)⟩

theorem mem_translateOpens (U : TopologicalSpace.Opens ℂ) (z w : ℂ) :
    w ∈ (translateOpens U z : Set ℂ) ↔ w - z ∈ (U : Set ℂ) := Iff.rfl

theorem mem_translateOpens_add (U : TopologicalSpace.Opens ℂ) (z w : ℂ) :
    w ∈ (U : Set ℂ) ↔ w + z ∈ (translateOpens U z : Set ℂ) := by
  rw [mem_translateOpens, add_sub_cancel_right]

theorem closure_translateOpens (U : TopologicalSpace.Opens ℂ) (z : ℂ) :
    closure (translateOpens U z : Set ℂ) = (Homeomorph.subRight z) ⁻¹' closure (U : Set ℂ) := by
  rw [Homeomorph.preimage_closure]
  rfl

theorem dist_sub_zero (x z : ℂ) : dist (x - z) 0 = dist x z := by
  rw [dist_zero_right, dist_eq_norm]

 
theorem isOpenAnnularTubeV2_translate {r : Set.Ioi (0 : ℝ)} {U : TopologicalSpace.Opens ℂ}
    (h : EndSaving.InterfaceV2.IsOpenAnnularTubeV2 0 r U) (z : ℂ) :
    EndSaving.InterfaceV2.IsOpenAnnularTubeV2 z r (translateOpens U z) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun x hx => ?_, ?_⟩
  · have := h1 hx
    simp only [Set.mem_ofPred_eq, dist_sub_zero] at this
    exact this
  · refine lqgDisconnects_shift (z := z) (fun w => mem_translateOpens_add U z w) ?_ ?_ h2
    · intro w; rw [mem_sphere_add 0 z w, zero_add]
    · intro w; rw [mem_sphere_add 0 z w, zero_add]

theorem closure_translate_annulus {r : Set.Ioi (0 : ℝ)} {V : TopologicalSpace.Opens ℂ}
    (h : closure (V : Set ℂ) ⊆ {x : ℂ | r < dist x 0 ∧ dist x 0 < 3 * (r : ℝ)}) (z : ℂ) :
    closure (translateOpens V z : Set ℂ) ⊆ {x : ℂ | r < dist x z ∧ dist x z < 3 * (r : ℝ)} := by
  rw [closure_translateOpens]
  intro x hx
  have := h hx
  simp only [Set.mem_ofPred_eq, Homeomorph.coe_subRight, dist_sub_zero] at this
  exact this

 

 
structure RadiusInputs {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ) (par : EndSaving.Interfaces.Parameters ξ)
    (pbar : Set.Ioo (0 : ℝ) 1) (r : Set.Ioi (0 : ℝ)) where
   
  U₀ : TopologicalSpace.Opens ℂ
  V₀ : TopologicalSpace.Opens ℂ
  f₀ : TestC
  U_annular : EndSaving.InterfaceV2.IsOpenAnnularTubeV2 0 r U₀
  V_annular : EndSaving.InterfaceV2.IsOpenAnnularTubeV2 0 r V₀
  closure_U_V : closure (U₀ : Set ℂ) ⊆ (V₀ : Set ℂ)
  closure_V_annulus : closure (V₀ : Set ℂ) ⊆ {x : ℂ | r < dist x 0 ∧ dist x 0 < 3 * (r : ℝ)}
  f_nonneg : ∀ x : ℂ, 0 ≤ f₀ x
  f_le : ∀ x : ℂ, f₀ x ≤ par.Cmax
  f_on_U : ∀ x ∈ (U₀ : Set ℂ), f₀ x = par.Cmax
  f_off_V : ∀ x ∉ (V₀ : Set ℂ), f₀ x = 0
   
  Target : Set DistC
   
  bounds : ∀ g ∈ Target, BoundsAt D ξ Q par 0 r U₀ V₀ g
   
  rn : ∀ g ∈ Target, par.Crn⁻¹ ≤ LQGMetric.cmDensity f₀ (LQGMetric.pair0 g) ∧
    LQGMetric.cmDensity f₀ (LQGMetric.pair0 g) ≤ par.Crn
   
  t57 : T57Inputs D D' ξ Q cMid par r U₀ V₀ (testCont f₀) Target
   
  L : ℂ → Set DistC
  L_local : ∀ z : ℂ, @MeasurableSet DistC (LQGMetric.Blueprint.fieldSigmaClosed0 (id : DistC → DistC)
    {x : ℂ | r ≤ dist x z ∧ dist x z ≤ 4 * (r : ℝ)}) (L z)
  L_null : ∀ z : ℂ, (P.map h) (L z \ centreTarget Target z) = 0
   
  L_prob : ∀ z : ℂ, ENNReal.ofReal (pbar : ℝ) ≤ (P.map h) (L z)

 
def RadiusInputs.toObjectInputs {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    {D D' : DistC → LSCMetric} {ξ : Set.Ioi (0 : ℝ)} {Q cMid : ℝ} {par : EndSaving.Interfaces.Parameters ξ}
    {pbar : Set.Ioo (0 : ℝ) 1} {r : Set.Ioi (0 : ℝ)}
    (R : RadiusInputs P h D D' ξ Q cMid par pbar r) (z : ℂ) :
    ObjectInputs P h D D' ξ Q cMid par pbar z r where
  U := translateOpens R.U₀ z
  V := translateOpens R.V₀ z
  f := testTranslate z R.f₀
  U_annular := isOpenAnnularTubeV2_translate R.U_annular z
  V_annular := isOpenAnnularTubeV2_translate R.V_annular z
  closure_U_V := by
    rw [closure_translateOpens]
    exact fun x hx => R.closure_U_V hx
  closure_V_annulus := closure_translate_annulus R.closure_V_annulus z
  f_nonneg := fun x => R.f_nonneg (x - z)
  f_le := fun x => R.f_le (x - z)
  f_on_U := fun x hx => R.f_on_U (x - z) hx
  f_off_V := fun x hx => R.f_off_V (x - z) hx
  Target := R.Target
  L := R.L z
  L_local := R.L_local z
  L_null := R.L_null z
  L_prob := R.L_prob z
  bounds := bounds_input_of_centre0 (fun w => mem_translateOpens_add R.U₀ z w)
    (fun w => mem_translateOpens_add R.V₀ z w) R.bounds
  rn := rn_input_of_centre0 (fun x => testTranslate_apply z R.f₀ x) R.rn
  shortcut := R.t57.shortcut (fun w => mem_translateOpens_add R.U₀ z w)
    (fun w => mem_translateOpens_add R.V₀ z w)
    (fun x => by
      show R.f₀ x = R.f₀ (x + z - z)
      rw [add_sub_cancel_right])
    (fun x => R.f_nonneg (x - z)) (fun x => R.f_le (x - z)) (fun x hx => R.f_on_U (x - z) hx)
    (fun x hx => R.f_off_V (x - z) hx) (closure_translate_annulus R.closure_V_annulus z)

 

 

structure CentreT58Inputs {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (cMinus cPlus : ℝ≥0∞)
    (pbar : Set.Ioo (0 : ℝ) 1) where
   
  cMid' : ℝ
  cMid'_lower : cMinus.toReal < cMid'
  cMid'_upper : cMid' < EndSaving.Interfaces.midpoint cMinus cPlus
   
  radii : EndSaving.Interfaces.AdmissibleRadii
  params : EndSaving.Interfaces.Parameters ξ
   
  density : ∀ κ : Set.Ioi (0 : ℝ), ∃ ε₀ : Set.Ioo (0 : ℝ) 1,
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ j : ℕ,
      let b : Set.Ioi (0 : ℝ) := EndSaving.Interfaces.dyadicRadius j
      ENNReal.ofReal (κ : ℝ) ≤
        P (h ⁻¹' OptimalConstants.Ratios.GtildeEvent D D' b κ
          ⟨cMid', lt_of_le_of_lt ENNReal.toReal_nonneg cMid'_lower⟩) →
      ∃ F : Finset ℝ,
        (F : Set ℝ) = radii.radii ∩ Set.Icc (ε ^ 2 * (b : ℝ)) (ε * (b : ℝ)) ∧
        (5 / 8 : ℝ) * (Real.log ε⁻¹ / Real.log 8) ≤ F.card
   
  radius : ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ radii.radii →
    RadiusInputs P h D D' ξ Q (EndSaving.Interfaces.midpoint cMinus cPlus) params pbar r

 
def CentreT58Inputs.toT58Inputs {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    {D D' : DistC → LSCMetric} {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {cMinus cPlus : ℝ≥0∞}
    {pbar : Set.Ioo (0 : ℝ) 1} (I : CentreT58Inputs P h D D' ξ Q cMinus cPlus pbar) :
    T58Inputs P h D D' ξ Q cMinus cPlus pbar :=
  ⟨I.cMid', I.cMid'_lower, I.cMid'_upper, I.radii, I.params, I.density,
    fun z r hr => (I.radius r hr).toObjectInputs z⟩

 
theorem t58_of_centre0_inputs {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hGFF : IsNormalizedWholePlaneGFF h P) (cMinus cPlus : ℝ≥0∞)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (hstrict : cMinus < cPlus)
    (hInputs : ∀ pbar : Set.Ioo (0 : ℝ) 1,
      Nonempty (CentreT58Inputs P h D D' ξ Q cMinus cPlus pbar)) :
    EndSaving.InterfaceV2.T58Statement P h ξ Q D D' hD hD' hGFF cMinus cPlus hMinus hPlus hstrict :=
  t58_of_inputs P h ξ Q D D' hD hD' hGFF cMinus cPlus hMinus hPlus hstrict
    (fun pbar => (hInputs pbar).map CentreT58Inputs.toT58Inputs)

end SupercriticalLQGUniqueness.Uniqueness.Objects.Producer
