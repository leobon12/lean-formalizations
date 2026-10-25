import SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2.ShiftV2
import LQGMetric.Papers.GM.S5.Prop43Out




 




set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2
open LQGMetric (DistC TestC)

 


private theorem raw_closed_local_shift
    (K : Set ℂ) (φ : TestC)
    (hφ : ∃ ε > 0,
      Disjoint (tsupport (φ : ℂ → ℝ)) (Metric.thickening ε K))
    (E₀ : Set DistC)
    (hE₀ : @MeasurableSet DistC
      (LQGMetric.Blueprint.fieldSigmaClosed0 (id : DistC → DistC) K) E₀) :
    MeasurableSet E₀ ∧
    (∀ g : DistC, ∀ c : ℝ,
      g ∈ E₀ ↔ LQGMetric.addConst g c ∈ E₀) ∧
    (∀ g : DistC, LQGMetric.GM.subTest g φ ∈ E₀ ↔ g ∈ E₀) := by
  have hG : ∀ ψ ∈ ({φ} : Finset TestC), ∃ ε > 0,
      Disjoint (tsupport (ψ : ℂ → ℝ)) (Metric.thickening ε K) := by
    intro ψ hψ
    have : ψ = φ := Finset.mem_singleton.mp hψ
    subst ψ
    exact hφ
  obtain ⟨C, hC, hEq, hShift⟩ :=
    LQGMetric.GM.shiftInv_fieldSigmaClosed0
      (h := (id : DistC → DistC)) K {φ} hG E₀ hE₀
  have hpairConst : ∀ g : DistC, ∀ c : ℝ,
      LQGMetric.pair0 (LQGMetric.addConst g c) = LQGMetric.pair0 g := by
    intro g c
    funext ψ
    simp only [LQGMetric.pair0, LQGMetric.GFFInv.addConst_apply,
      ψ.2, zero_mul, add_zero]
  constructor
  · rw [hEq]
    exact hC.preimage LQGMetric.measurable_pair0
  constructor
  · intro g c
    rw [hEq]
    change LQGMetric.pair0 g ∈ C ↔
      LQGMetric.pair0 (LQGMetric.addConst g c) ∈ C
    rw [hpairConst]
  · intro g
    rw [hEq]
    change LQGMetric.pair0 (LQGMetric.GM.subTest g φ) ∈ C ↔
      LQGMetric.pair0 g ∈ C
    exact hShift φ (Finset.mem_singleton_self φ) g

 


theorem local_event_subTest_ae {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (K : Set ℂ) (φ : TestC)
    (hφ : ∃ ε > 0,
      Disjoint (tsupport (φ : ℂ → ℝ)) (Metric.thickening ε K))
    (E : Set DistC) (hE : MeasurableSet E)
    (hconst : ∀ (g : DistC) (c : ℝ),
      g ∈ E ↔ LQGMetric.addConst g c ∈ E)
    (hlocal : ∃ E₀ : Set DistC,
      @MeasurableSet DistC
        (LQGMetric.Blueprint.fieldSigmaClosed0 (id : DistC → DistC) K) E₀ ∧
      E =ᵐ[P.map h] E₀) :
    ∀ᵐ ω ∂P, LQGMetric.GM.subTest (h ω) φ ∈ E ↔ h ω ∈ E := by
  obtain ⟨E₀, hE₀raw, hae⟩ := hlocal
  obtain ⟨hE₀, hconst₀, hrawShift⟩ := raw_closed_local_shift K φ hφ E₀ hE₀raw
  let B : Set DistC := (E \ E₀) ∪ (E₀ \ E)
  have hBmeas : MeasurableSet B := hE.diff hE₀ |>.union (hE₀.diff hE)
  have hBconst : ∀ g : DistC, ∀ c : ℝ,
      g ∈ B ↔ LQGMetric.addConst g c ∈ B := by
    intro g c
    dsimp [B]
    simp only [Set.mem_union, Set.mem_sdiff]
    rw [← hconst g c, ← hconst₀ g c]
  have hAe : ∀ᵐ ω ∂P, h ω ∈ E ↔ h ω ∈ E₀ := by
    filter_upwards [ae_of_ae_map hh.1.measurable.aemeasurable hae] with ω hω
    rw [hω]
  have hzero : P (sampleEvent h B) = 0 := by
    apply (measure_eq_zero_iff_ae_notMem).2
    filter_upwards [hAe] with ω hω
    simp only [sampleEvent, Set.mem_preimage, B, Set.mem_union, Set.mem_sdiff]
    tauto
  have hshiftZero := oneBump_event_ac P h hh (-φ) B hBmeas hBconst hzero
  have hshiftAe : ∀ᵐ ω ∂P,
      LQGMetric.GM.subTest (h ω) φ ∈ E ↔
        LQGMetric.GM.subTest (h ω) φ ∈ E₀ := by
    have hnull : ∀ᵐ ω ∂P,
        LQGMetric.addFun (h ω) (LQGMetric.testCont (-φ)) ∉ B :=
      (measure_eq_zero_iff_ae_notMem).1 hshiftZero
    filter_upwards [hnull] with ω hω
    rw [← LQGMetric.GM.subTest_eq_addFun_neg_cm] at hω
    dsimp [B] at hω
    simp only [Set.mem_union, Set.mem_sdiff] at hω
    tauto
  filter_upwards [hAe, hshiftAe] with ω hω hωshift
  exact hωshift.trans ((hrawShift (h ω)).trans hω.symm)

 
theorem ObjectAtV2.oneBump_local_shift_ae {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} {D D' : DistC → LSCMetric}
    {ξ : Set.Ioi (0 : ℝ)} {Q cMid : ℝ} {par : EndSaving.Interfaces.Parameters ξ}
    {pbar : Set.Ioo (0 : ℝ) 1} {z : ℂ} {r : Set.Ioi (0 : ℝ)}
    (obj : ObjectAtV2 P h D D' ξ Q cMid par pbar z r)
    (hh : IsNormalizedWholePlaneGFF h P) (φ : TestC)
    (hφ : ∃ ε > 0, Disjoint (tsupport (φ : ℂ → ℝ))
      (Metric.thickening ε
        {x : ℂ | r ≤ dist x z ∧ dist x z ≤ 4 * (r : ℝ)})) :
    ∀ᵐ ω ∂P, LQGMetric.GM.subTest (h ω) φ ∈ obj.E ↔ h ω ∈ obj.E :=
  local_event_subTest_ae P h hh _ φ hφ obj.E
    obj.E_measurable obj.E_constant obj.E_local

 


theorem ObjectAtV2.finiteBump_local_shift_ae {Ω ι : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    {D D' : DistC → LSCMetric}
    {ξ : Set.Ioi (0 : ℝ)} {Q cMid : ℝ} {par : EndSaving.Interfaces.Parameters ξ}
    {pbar : Set.Ioo (0 : ℝ) 1} {z : ℂ} {r : Set.Ioi (0 : ℝ)}
    (obj : ObjectAtV2 P h D D' ξ Q cMid par pbar z r)
    (hh : IsNormalizedWholePlaneGFF h P)
    (Z : Finset ι) (f : ι → TestC)
    (hZ : ∃ ε > 0, Disjoint
      (tsupport ((∑ i ∈ Z, f i : TestC) : ℂ → ℝ))
      (Metric.thickening ε
        {x : ℂ | r ≤ dist x z ∧ dist x z ≤ 4 * (r : ℝ)})) :
    ∀ᵐ ω ∂P,
      LQGMetric.GM.subTest (h ω) (∑ i ∈ Z, f i) ∈ obj.E ↔ h ω ∈ obj.E :=
  obj.oneBump_local_shift_ae hh (∑ i ∈ Z, f i) hZ

 
private theorem disjoint_tsupport_finset_sum {ι : Type} (Z : Finset ι)
    (f : ι → TestC) (V : Set ℂ)
    (hf : ∀ i ∈ Z, Disjoint (tsupport ((f i : TestC) : ℂ → ℝ)) V) :
    Disjoint (tsupport ((∑ i ∈ Z, f i : TestC) : ℂ → ℝ)) V := by
  classical
  induction Z using Finset.induction_on with
  | empty =>
      simp
  | @insert i Z hi ih =>
      have hhead := hf i (Finset.mem_insert_self i Z)
      have htail : ∀ j ∈ Z, Disjoint (tsupport ((f j : TestC) : ℂ → ℝ)) V := by
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)
      have hrest := ih htail
      have hsub : tsupport (((f i + ∑ j ∈ Z, f j : TestC) : TestC) : ℂ → ℝ) ⊆
          tsupport ((f i : TestC) : ℂ → ℝ) ∪
            tsupport ((∑ j ∈ Z, f j : TestC) : ℂ → ℝ) :=
        tsupport_add _ _
      apply Set.disjoint_left.mpr
      intro x hx hxV
      have hx' : x ∈ tsupport ((f i : TestC) : ℂ → ℝ) ∪
          tsupport ((∑ j ∈ Z, f j : TestC) : ℂ → ℝ) := by
        apply hsub
        simpa only [Finset.sum_insert hi] using hx
      rcases hx' with hxHead | hxRest
      · exact Set.disjoint_left.mp hhead hxHead hxV
      · exact Set.disjoint_left.mp hrest hxRest hxV

 
private theorem finite_remote_sum {ι : Type} (Z : Finset ι)
    (f : ι → TestC) (K : Set ℂ)
    (hf : ∀ i ∈ Z, ∃ ε > 0,
      Disjoint (tsupport ((f i : TestC) : ℂ → ℝ))
        (Metric.thickening ε K)) :
    ∃ ε > 0, Disjoint
      (tsupport ((∑ i ∈ Z, f i : TestC) : ℂ → ℝ))
      (Metric.thickening ε K) := by
  classical
  have hG : ∀ φ ∈ Z.image f, ∃ ε > 0,
      Disjoint (tsupport (φ : ℂ → ℝ)) (Metric.thickening ε K) := by
    intro φ hφ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hφ
    exact hf i hi
  obtain ⟨ε, hε, hAll⟩ := LQGMetric.GM.exists_eps_disjoint_cm K (Z.image f) hG
  refine ⟨ε, hε, disjoint_tsupport_finset_sum Z f _ ?_⟩
  intro i hi
  exact hAll (f i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

 


theorem ObjectAtV2.finiteBump_local_shift_ae_of_each {Ω ι : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    {D D' : DistC → LSCMetric}
    {ξ : Set.Ioi (0 : ℝ)} {Q cMid : ℝ} {par : EndSaving.Interfaces.Parameters ξ}
    {pbar : Set.Ioo (0 : ℝ) 1} {z : ℂ} {r : Set.Ioi (0 : ℝ)}
    (obj : ObjectAtV2 P h D D' ξ Q cMid par pbar z r)
    (hh : IsNormalizedWholePlaneGFF h P)
    (Z : Finset ι) (f : ι → TestC)
    (hf : ∀ i ∈ Z, ∃ ε > 0,
      Disjoint (tsupport ((f i : TestC) : ℂ → ℝ))
        (Metric.thickening ε
          {x : ℂ | r ≤ dist x z ∧ dist x z ≤ 4 * (r : ℝ)})) :
    ∀ᵐ ω ∂P,
      LQGMetric.GM.subTest (h ω) (∑ i ∈ Z, f i) ∈ obj.E ↔ h ω ∈ obj.E :=
  obj.finiteBump_local_shift_ae hh Z f (finite_remote_sum Z f _ hf)


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2
