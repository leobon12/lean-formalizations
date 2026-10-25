import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.LowerSourceV2
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents.FVSpentV2




 











set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Finset LQGMetric.MetricGeometry Filter
open scoped ENNReal Topology

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices

open LQGMetric (DistC TestC)

 
def SampleRegularV2 {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1) (r : Set.Ioi (0 : ℝ))
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (ω : Ω) : Prop :=
  RegularAt D (ξ : ℝ) (h ω) ∧
    ∀ W : Finset (ℤ × ℤ),
      RegularAt D (ξ : ℝ) (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj W (h ω))

 

theorem ae_sampleRegularV2 {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (hD : IsWeakLQGMetric ξ Q D)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1) (r : Set.Ioi (0 : ℝ))
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r) :
    ∀ᵐ ω ∂μ, SampleRegularV2 μ h D D' ξ Q cMid par pbar r obj ω := by
  filter_upwards [ae_regularAt_family hD μ h hh
    (fun W : Finset (ℤ × ℤ) => -EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj W)]
    with ω hω
  refine ⟨hω.1, fun W => ?_⟩
  rw [subtractBumps_eq_addFun]
  exact hω.2 W

 
theorem subtractBumps_empty {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1) (r : Set.Ioi (0 : ℝ))
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r) (g : DistC) :
    EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj ∅ g = g := by
  unfold EndSaving.FiniteEvents.subtractBumpsV2 EndSaving.FiniteEvents.bumpSumV2
  rw [Finset.sum_empty, subTest_eq_addFun, neg_zero]
  have h0 : LQGMetric.testCont (0 : TestC) = 0 := by ext x; rfl
  rw [h0, addFun_zero]

 
theorem finset_sum_le_tsum_set {α : Type*} (S : Set α) (F : Finset α) (hF : ↑F ⊆ S)
    (φ : α → ℝ≥0∞) : ∑ e ∈ F, φ e ≤ ∑' x : S, φ x := by
  classical
  have h := ENNReal.sum_le_tsum (f := fun x : S => φ x)
    (F.attach.map ⟨fun x => ⟨x.1, hF x.2⟩, fun x y hxy => by
      apply Subtype.ext
      have := congrArg (fun s : S => (s : α)) hxy
      simpa using this⟩)
  rw [Finset.sum_map] at h
  exact (Finset.sum_attach F φ).symm.trans_le h

 
theorem lem_new_dist_lower0_v2 {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (hD : IsWeakLQGMetric ξ Q D)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1) (r : Set.Ioi (0 : ℝ))
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r) :
    ∀ᵐ ω ∂μ, ∀ (b : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ) (Z : Finset (ℤ × ℤ)),
      EndSaving.Interfaces.Configuration r b K₁ K₂ Z → (∀ i ∈ Z, h ω ∈ (obj i).E) →
      ∀ (P : ℝ → ℂ) (T : ℝ),
        EndSaving.FiniteEvents.SetGeodesic (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z (h ω)))
          K₁ K₂ P T →
        ∃ hfin : ∀ i ∈ Z, (ovSet P T
            (ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) (4 * (r : ℝ))) (obj i).V).Finite,
          OptimalConstants.Ratios.setDist (D (h ω)) K₁ K₂ ≤
            OptimalConstants.Ratios.setDist (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z (h ω)))
              K₁ K₂ +
            ∑ i ∈ Z.attach, ∑ e ∈ (hfin i.1 i.2).toFinset, D (h ω) (P e.2.1, P e.2.2.1) := by
  filter_upwards [ae_sampleRegularV2 μ h hh D D' ξ Q cMid hD par pbar r obj] with ω hω
  intro b K₁ K₂ Z hconfig hE P T hgeod
  have hreg := hω.2 Z
  rw [← Finset.empty_union Z] at hreg hgeod
  obtain ⟨hfin, _, hmain⟩ := lower_general_v2 μ h D D' ξ Q cMid par pbar r b K₁ K₂ obj Z ∅ Z
    hconfig (Finset.empty_subset _) le_rfl (Finset.disjoint_empty_left Z) ω hreg hE P T hgeod
  rw [subtractBumps_empty, Finset.empty_union] at hmain
  exact ⟨hfin, hmain⟩

 
theorem lem_new_dist_lower0_printed_v2 {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (hD : IsWeakLQGMetric ξ Q D)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1) (r : Set.Ioi (0 : ℝ))
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r) :
    ∀ᵐ ω ∂μ, ∀ (b : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ) (Z : Finset (ℤ × ℤ)),
      EndSaving.Interfaces.Configuration r b K₁ K₂ Z → (∀ i ∈ Z, h ω ∈ (obj i).E) →
      ∀ (P : ℝ → ℂ) (T : ℝ),
        EndSaving.FiniteEvents.SetGeodesic (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z (h ω)))
          K₁ K₂ P T →
          OptimalConstants.Ratios.setDist (D (h ω)) K₁ K₂ ≤
            OptimalConstants.Ratios.setDist (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z (h ω)))
              K₁ K₂ +
            ∑ i ∈ Z, ∑' e : excSet P T
                (ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) (4 * (r : ℝ))) (obj i).V,
              D (h ω) (P e.1.2.1, P e.1.2.2.1) := by
  filter_upwards [lem_new_dist_lower0_v2 μ h hh D D' ξ Q cMid hD par pbar r obj] with ω hω
  intro b K₁ K₂ Z hconfig hE P T hgeod
  obtain ⟨hfin, hmain⟩ := hω b K₁ K₂ Z hconfig hE P T hgeod
  refine hmain.trans (add_le_add le_rfl ?_)
  rw [← Finset.sum_attach Z]
  refine Finset.sum_le_sum fun i _ => ?_
  exact finset_sum_le_tsum_set _ _
    (fun e he => (ovSet_subset _ _ _ _) ((Set.Finite.mem_toFinset _).mp he))
    (fun e => D (h ω) (P e.2.1, P e.2.2.1))

 

theorem lem_new_dist_lower_v2 {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (hD : IsWeakLQGMetric ξ Q D)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1) (r : Set.Ioi (0 : ℝ))
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r) :
    ∀ᵐ ω ∂μ, ∀ (b : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ) (Z : Finset (ℤ × ℤ)),
      EndSaving.Interfaces.Configuration r b K₁ K₂ Z → (∀ i ∈ Z, h ω ∈ (obj i).E) →
      ∀ (P : ℝ → ℂ) (T : ℝ),
        EndSaving.FiniteEvents.SetGeodesic (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z (h ω)))
          K₁ K₂ P T →
          OptimalConstants.Ratios.setDist (D (h ω)) K₁ K₂ ≤
            OptimalConstants.Ratios.setDist (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z (h ω)))
              K₁ K₂ +
            ENNReal.ofReal (par.Caround / par.Cacross) * ∑ i ∈ Z,
              ⨆ e ∈ ovSet P T
                  (ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) (4 * (r : ℝ))) (obj i).V,
                D (h ω) (P e.2.1, P e.2.2.1) := by
  filter_upwards [ae_sampleRegularV2 μ h hh D D' ξ Q cMid hD par pbar r obj] with ω hω
  intro b K₁ K₂ Z hconfig hE P T hgeod
  have hreg := hω.2 Z
  rw [← Finset.empty_union Z] at hreg hgeod
  have hmain := lower_general_max_v2 μ h D D' ξ Q cMid par pbar r b K₁ K₂ obj Z ∅ Z
    hconfig (Finset.empty_subset _) le_rfl (Finset.disjoint_empty_left Z) ω hreg hE P T hgeod
  rw [subtractBumps_empty, Finset.empty_union] at hmain
  exact hmain

 
theorem lem_new_dist_lower_printed_v2 {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (hD : IsWeakLQGMetric ξ Q D)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1) (r : Set.Ioi (0 : ℝ))
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r) :
    ∀ᵐ ω ∂μ, ∀ (b : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ) (Z : Finset (ℤ × ℤ)),
      EndSaving.Interfaces.Configuration r b K₁ K₂ Z → (∀ i ∈ Z, h ω ∈ (obj i).E) →
      ∀ (P : ℝ → ℂ) (T : ℝ),
        EndSaving.FiniteEvents.SetGeodesic (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z (h ω)))
          K₁ K₂ P T →
          OptimalConstants.Ratios.setDist (D (h ω)) K₁ K₂ ≤
            OptimalConstants.Ratios.setDist (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z (h ω)))
              K₁ K₂ +
            ENNReal.ofReal (par.Caround / par.Cacross) * ∑ i ∈ Z,
              ⨆ e ∈ excSet P T
                  (ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) (4 * (r : ℝ))) (obj i).V,
                D (h ω) (P e.2.1, P e.2.2.1) := by
  filter_upwards [lem_new_dist_lower_v2 μ h hh D D' ξ Q cMid hD par pbar r obj] with ω hω
  intro b K₁ K₂ Z hconfig hE P T hgeod
  refine (hω b K₁ K₂ Z hconfig hE P T hgeod).trans
    (add_le_add le_rfl (mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ => ?_)))
  refine iSup₂_le fun e he => ?_
  exact le_iSup₂_of_le (f := fun (e : ℝ × ℝ × ℝ × ℝ) (_ : e ∈ excSet P T
      (ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) (4 * (r : ℝ))) (obj i).V) =>
    D (h ω) (P e.2.1, P e.2.2.1)) e (ovSet_subset _ _ _ _ he) le_rfl

 


theorem lem_new_dist_around_v2 {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (hD : IsWeakLQGMetric ξ Q D)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1) (r : Set.Ioi (0 : ℝ))
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r) :
    ∀ᵐ ω ∂μ, ∀ (b : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ) (Z : Finset (ℤ × ℤ)),
      EndSaving.Interfaces.Configuration r b K₁ K₂ Z → (∀ i ∈ Z, h ω ∈ (obj i).E) →
      ∀ (P : ℝ → ℂ) (T : ℝ),
        EndSaving.FiniteEvents.SetGeodesic (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z (h ω)))
          K₁ K₂ P T →
        ∀ i ∈ Z, ∀ c : ℝ,
          IsCircleAverage (h ω) r (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) c →
          (EndSaving.Spent.closedContactTimes P ((obj i).V : Set ℂ) T).Nonempty →
          ENNReal.ofReal (EndSaving.Spent.lastClosedContact P ((obj i).V : Set ℂ) T -
              EndSaving.Spent.firstClosedContact P ((obj i).V : Set ℂ) T) ≤
            ENNReal.ofReal par.Caround * ENNReal.ofReal (scaleN ξ Q r c) := by
  filter_upwards [ae_sampleRegularV2 μ h hh D D' ξ Q cMid hD par pbar r obj] with ω hω
  intro b K₁ K₂ Z hconfig hE P T hgeod i hi c hc hne
  have hreg := hω.2 Z
  set d1 := D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z (h ω))
  have hWh : ∀ p : ℂ × ℂ, D (h ω) p =
      weylScale ξ (LQGMetric.testCont (EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj Z)) d1 p := by
    intro p
    rw [hreg.weyl, addFun_subtract_self]
  have hG := EndSaving.FiniteEvents.SetGeodesic.isGeodesic d1 K₁ K₂ P T hgeod
  have hout : ∀ x ∈ K₁ ∪ K₂,
      4 * (r : ℝ) ≤ dist x (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) := by
    intro x hx
    have hnot : x ∉ ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) (4 * (r : ℝ)) :=
      fun hb => Set.disjoint_left.mp (hconfig.2 i hi) hb (Or.inl hx)
    simpa only [mem_ball, not_lt] using hnot
  exact EndSaving.FiniteEvents.objectAtV2_around_closed_contacts μ h D D' ξ Q cMid par pbar _ r (obj i) ω
    (hE i hi) c hc d1 _ hreg.barrier hreg.length hWh
    (fun x => bumpSum_nonneg μ h D D' ξ Q cMid par pbar r obj Z x) P hG hgeod.1.2.1
    (hout _ (Or.inl hgeod.2.1)) (hout _ (Or.inr hgeod.2.2.1)) hne

 
def cSpent (ξ : Set.Ioi (0 : ℝ)) (par : EndSaving.Interfaces.Parameters ξ) : ℝ :=
  2 * Real.exp ((ξ : ℝ) * par.Cmax) * par.Caround

theorem cSpent_pos (ξ : Set.Ioi (0 : ℝ)) (par : EndSaving.Interfaces.Parameters ξ) : 0 < cSpent ξ par := by
  unfold cSpent
  have := par.around_pos
  positivity

 


theorem lem_new_dist_spent_v2 {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (hD : IsWeakLQGMetric ξ Q D) (cPlus : ℝ≥0∞)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1) (r : Set.Ioi (0 : ℝ))
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r) :
    ∀ᵐ ω ∂μ, ∀ (b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ) (Z : Finset (ℤ × ℤ)),
      EndSaving.FiniteEvents.FbarV2 μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z (h ω) →
      ∀ hbr : ℝ, IsCircleAverage (h ω) b 0 hbr →
      ∀ (P : ℝ → ℂ) (T : ℝ),
        EndSaving.FiniteEvents.SetGeodesic (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z (h ω)))
          K₁ K₂ P T →
        ∀ i ∈ Z,
          (⨆ u ∈ EndSaving.Spent.closedContactTimes P ((obj i).V : Set ℂ) T,
              ⨆ v ∈ EndSaving.Spent.closedContactTimes P ((obj i).V : Set ℂ) T, D (h ω) (P u, P v)) ⊔
            (D (h ω)).len P (EndSaving.Spent.firstClosedContact P ((obj i).V : Set ℂ) T)
              (EndSaving.Spent.lastClosedContact P ((obj i).V : Set ℂ) T) ≤
          ENNReal.ofReal (cSpent ξ par * scaleB ξ Q b q hbr) := by
  filter_upwards [ae_sampleRegularV2 μ h hh D D' ξ Q cMid hD par pbar r obj] with ω hω
  intro b q K₁ K₂ Z hF hbr hb P T hgeod i hi
  rcases hF with ⟨_, hconfig, hbr₀, havg₀, _, hlocal, _⟩
  have hbreq : hbr₀ = hbr := isCircleAverage_unique havg₀ hb
  subst hbreq
  obtain ⟨hE, c, hc, hbin⟩ := hlocal i hi
  have hreg := hω.2 Z
  set d1 := D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z (h ω))
  have hWh : ∀ p : ℂ × ℂ, D (h ω) p =
      weylScale ξ (LQGMetric.testCont (EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj Z)) d1 p := by
    intro p
    rw [hreg.weyl, addFun_subtract_self]
  have hG := EndSaving.FiniteEvents.SetGeodesic.isGeodesic d1 K₁ K₂ P T hgeod
  have hout : ∀ x ∈ K₁ ∪ K₂,
      4 * (r : ℝ) ≤ dist x (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) := by
    intro x hx
    have hnot : x ∉ ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) (4 * (r : ℝ)) :=
      fun hb => Set.disjoint_left.mp (hconfig.2 i hi) hb (Or.inl hx)
    simpa only [mem_ball, not_lt] using hnot
  have hB := scaleB_pos ξ Q b q hbr₀
  have htarget : (ENNReal.ofReal (Real.exp ((ξ : ℝ) * par.Cmax)) * ENNReal.ofReal par.Caround * 2) *
      ENNReal.ofReal (scaleB ξ Q b q hbr₀) = ENNReal.ofReal (cSpent ξ par * scaleB ξ Q b q hbr₀) := by
    unfold cSpent
    rw [ENNReal.ofReal_mul (by have := par.around_pos; positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [ENNReal.ofReal_ofNat]
    ring
  by_cases hne : (EndSaving.Spent.closedContactTimes P ((obj i).V : Set ℂ) T).Nonempty
  · rw [← htarget]
    exact EndSaving.FiniteEvents.objectAtV2_spent_closed_contacts μ h D D' ξ Q cMid par pbar _ r (obj i) ω hE c hc
      d1 _ hreg.barrier hreg.length hWh
      (fun x => bumpSum_nonneg μ h D D' ξ Q cMid par pbar r obj Z x)
      (fun x => bumpSum_le_Cmax μ h D D' ξ Q cMid par pbar r obj b K₁ K₂ Z Z hconfig le_rfl x)
      P hG hgeod.1.2.1 (hout _ (Or.inl hgeod.2.1)) (hout _ (Or.inr hgeod.2.2.1)) hne _
      (EndSaving.FiniteEvents.localSizeBin_upper_ennreal ξ Q r b q c hbr₀ hbin)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have hfirst : EndSaving.Spent.firstClosedContact P ((obj i).V : Set ℂ) T = 0 := by
      rw [EndSaving.Spent.firstClosedContact, hne, Real.sInf_empty]
    have hlast : EndSaving.Spent.lastClosedContact P ((obj i).V : Set ℂ) T = 0 := by
      rw [EndSaving.Spent.lastClosedContact, hne, Real.sSup_empty]
    rw [hfirst, hlast, hne]
    have hlen : (D (h ω)).len P 0 0 = 0 := by
      unfold LSCMetric.len
      rw [Set.Icc_self]
      exact eVariationOn.subsingleton _ Set.subsingleton_singleton
    simp [hlen]


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices
