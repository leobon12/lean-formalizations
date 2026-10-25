import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteAroundCoupling
import SupercriticalLQGUniqueness.B2.DG20Lim.CircleMinimizers

 

















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

open SupercriticalLQGUniqueness.B2.DG20Lim

 
def CrossesAnn (Q : RatCircle) (A : RatAnnulus) : Prop :=
  (Q.toSet ∩ A.inner.toSet).Nonempty ∧ (Q.toSet ∩ A.outer.toSet).Nonempty

 
theorem exists_mem_of_crossesAnn {Q : RatCircle} {A : RatAnnulus} (hQ : CrossesAnn Q A)
    {X : Set ℂ} (hX : LQGMetric.Disconnects X A.inner.toSet A.outer.toSet) :
    ∃ q ∈ Q.toSet, q ∈ X := by
  obtain ⟨x, hxQ, hxI⟩ := hQ.1
  obtain ⟨y, hyQ, hyO⟩ := hQ.2
  have hpc : IsPathConnected Q.toSet := by
    unfold RatCircle.toSet
    exact isPathConnected_sphere (by simp) Q.center
      (by exact_mod_cast Q.radius_nonneg)
  have hj := hpc.joinedIn x hxQ y hyQ
  obtain ⟨p, ⟨t, rfl⟩, hpX⟩ := hX x y hj.somePath hxI hyO
  exact ⟨hj.somePath t, hj.somePath_mem t, hpX⟩

 
theorem finiteCircleDist_le_across_aroundPath_crossing
    (D : LQGMetric.ContMetric) (hD : D.IsLength)
    (A : RatAnnulus) (O₁ O₁' Q : RatCircle)
    (h₁ : A.OppositeSides O₁ O₁') (hQ : CrossesAnn Q A)
    {G : ℝ → ℂ} {c d : ℝ}
    (hG : LQGMetric.Disconnects (G '' Icc c d) A.inner.toSet A.outer.toSet) :
    LQGMetric.Blueprint.setDist D O₁.toSet Q.toSet ≤
      LQGMetric.Blueprint.setDist D O₁.toSet O₁'.toSet + D.len G c d := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨u₁, hu₁, v₁, hv₁, hmin₁⟩ := exists_circleDist_minimizers D O₁ O₁'
  obtain ⟨γ₁, a₁, b₁, hab₁, hc₁, hga₁, hgb₁, hlen₁⟩ :=
    (LQGMetric.MetricGeometry.isLengthSpace_iff_curves).1 hD
      (D.pt u₁) (D.pt v₁) ε (by exact_mod_cast hε)
  let q₁ : ℝ → ℂ := fun t => D.unpt (γ₁ t)
  have hq₁ : ContinuousOn q₁ (Icc a₁ b₁) := D.continuous_unpt.comp_continuousOn hc₁
  have hqa₁ : q₁ a₁ = u₁ := by simp [q₁, hga₁]
  have hqb₁ : q₁ b₁ = v₁ := by simp [q₁, hgb₁]
  obtain ⟨t₁, ht₁, s₁, hs₁, heq₁⟩ :=
    A.exists_hit_around_of_opposite_sides O₁ O₁' h₁ hab₁ hq₁
      (hqa₁ ▸ hu₁) (hqb₁ ▸ hv₁) hG
  obtain ⟨q, hqQ, s₂, hs₂, heq₂⟩ := exists_mem_of_crossesAnn hQ hG
  have hpt₁ : D.pt (G s₁) = γ₁ t₁ := by
    calc
      D.pt (G s₁) = D.pt (q₁ t₁) := by rw [← heq₁]
      _ = γ₁ t₁ := by simp [q₁]
  have hloop : edist (γ₁ t₁) (D.pt q) ≤ D.len G c d := by
    rw [← hpt₁, ← heq₂, LQGMetric.ContMetric.edist_pt]
    exact LQGMetric.GM.ofReal_dist_le_len D hs₁ hs₂
  have hset : LQGMetric.Blueprint.setDist D O₁.toSet Q.toSet ≤ edist (D.pt u₁) (D.pt q) := by
    unfold LQGMetric.Blueprint.setDist
    exact LQGMetric.MetricGeometry.setEDist_le_edist
      (Set.mem_image_of_mem D.pt hu₁) (Set.mem_image_of_mem D.pt hqQ)
  have hlen₁' : LQGMetric.MetricGeometry.curveLength γ₁ a₁ b₁ ≤
      LQGMetric.Blueprint.setDist D O₁.toSet O₁'.toSet + (ε : ℝ≥0∞) := by
    simpa only [LQGMetric.ContMetric.edist_pt, ENNReal.ofReal_coe_nnreal, ← hmin₁] using hlen₁
  calc
    _ ≤ edist (D.pt u₁) (D.pt q) := hset
    _ = edist (γ₁ a₁) (D.pt q) := by rw [hga₁]
    _ ≤ edist (γ₁ a₁) (γ₁ t₁) + edist (γ₁ t₁) (D.pt q) := edist_triangle _ _ _
    _ ≤ LQGMetric.MetricGeometry.curveLength γ₁ a₁ b₁ + D.len G c d :=
        add_le_add ((LQGMetric.MetricGeometry.edist_le_curveLength γ₁ ht₁.1).trans
          (LQGMetric.MetricGeometry.curveLength_mono γ₁ le_rfl ht₁.2)) hloop
    _ ≤ (LQGMetric.Blueprint.setDist D O₁.toSet O₁'.toSet + (ε : ℝ≥0∞)) + D.len G c d :=
        add_le_add hlen₁' le_rfl
    _ = LQGMetric.Blueprint.setDist D O₁.toSet O₁'.toSet + D.len G c d + ε := by ac_rfl

 
theorem finiteCircleDist_le_across_around_crossing
    (D : LQGMetric.ContMetric) (hD : D.IsLength)
    (A : RatAnnulus) (O₁ O₁' Q : RatCircle)
    (h₁ : A.OppositeSides O₁ O₁') (hQ : CrossesAnn Q A) :
    LQGMetric.Blueprint.setDist D O₁.toSet Q.toSet ≤
      LQGMetric.Blueprint.setDist D O₁.toSet O₁'.toSet +
        D.aroundDist A.toSet A.inner.toSet A.outer.toSet := by
  simp only [LQGMetric.ContMetric.aroundDist, ENNReal.add_iInf]
  refine le_iInf fun a => le_iInf fun b => le_iInf fun G =>
    le_iInf fun hab => le_iInf fun hcont => le_iInf fun hsub =>
      le_iInf fun hdisc => ?_
  exact finiteCircleDist_le_across_aroundPath_crossing D hD A O₁ O₁' Q h₁ hQ hdisc

 
theorem finiteCircleDist_eq_zero_of_inter (D : LQGMetric.ContMetric) (O Q : RatCircle)
    (h : (O.toSet ∩ Q.toSet).Nonempty) :
    LQGMetric.Blueprint.setDist D O.toSet Q.toSet = 0 := by
  obtain ⟨x, hxO, hxQ⟩ := h
  refine le_antisymm ?_ zero_le
  unfold LQGMetric.Blueprint.setDist
  calc LQGMetric.MetricGeometry.setEDist (D.pt '' O.toSet) (D.pt '' Q.toSet)
      ≤ edist (D.pt x) (D.pt x) := LQGMetric.MetricGeometry.setEDist_le_edist
        (Set.mem_image_of_mem D.pt hxO) (Set.mem_image_of_mem D.pt hxQ)
    _ = 0 := edist_self _

 
theorem ae_crossing_bound_of_coord_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsFiniteMeasure P] {P' : Measure Ω'}
    (D : Ω → LQGMetric.ContMetric) (hD : AEMeasurable D P)
    (hLen : ∀ᵐ ω ∂P, (D ω).IsLength)
    (Y : Ω' → RatCoords) (hY : Measurable Y)
    (hLaw : P'.map Y = P.map (measurableRatCoordsVersion D hD))
    (A : RatAnnulus) (O₁ O₁' Q : RatCircle)
    (h₁ : A.OppositeSides O₁ O₁') (hQ : CrossesAnn Q A) :
    ∀ᵐ ω ∂P', (Y ω).1 (O₁, Q) ≤ (Y ω).1 (O₁, O₁') + (Y ω).2 A := by
  let E : Set RatCoords := {q | q.1 (O₁, Q) ≤ q.1 (O₁, O₁') + q.2 A}
  have hC (O P : RatCircle) : Measurable (fun q : RatCoords => q.1 (O, P)) :=
    (measurable_pi_apply (O, P)).comp measurable_fst
  have hB : Measurable (fun q : RatCoords => q.2 A) :=
    (measurable_pi_apply A).comp measurable_snd
  have hE : MeasurableSet E := measurableSet_le (hC O₁ Q) ((hC O₁ O₁').add hB)
  have hSm : Measurable (measurableRatCoordsVersion D hD) :=
    measurable_measurableRatCoordsVersion D hD
  have hSource : ∀ᵐ ω ∂P, measurableRatCoordsVersion D hD ω ∈ E := by
    filter_upwards [ae_eq_measurableRatCoordsVersion D hD, hLen] with ω hEq hωLen
    change (measurableRatCoordsVersion D hD ω).1 (O₁, Q) ≤ _
    rw [← hEq]
    exact finiteCircleDist_le_across_around_crossing (D ω) hωLen A O₁ O₁' Q h₁ hQ
  have hSourceMap : ∀ᵐ q ∂P.map (measurableRatCoordsVersion D hD), q ∈ E :=
    (ae_map_iff hSm.aemeasurable hE).2 hSource
  exact (ae_map_iff hY.aemeasurable hE).1 (hLaw ▸ hSourceMap)

 
theorem ae_inter_zero_of_coord_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsFiniteMeasure P] {P' : Measure Ω'}
    (D : Ω → LQGMetric.ContMetric) (hD : AEMeasurable D P)
    (Y : Ω' → RatCoords) (hY : Measurable Y)
    (hLaw : P'.map Y = P.map (measurableRatCoordsVersion D hD))
    (O Q : RatCircle) (h : (O.toSet ∩ Q.toSet).Nonempty) :
    ∀ᵐ ω ∂P', (Y ω).1 (O, Q) = 0 := by
  let E : Set RatCoords := {q | q.1 (O, Q) = 0}
  have hE : MeasurableSet E :=
    measurableSet_eq_fun ((measurable_pi_apply (O, Q)).comp measurable_fst) measurable_const
  have hSm : Measurable (measurableRatCoordsVersion D hD) :=
    measurable_measurableRatCoordsVersion D hD
  have hSource : ∀ᵐ ω ∂P, measurableRatCoordsVersion D hD ω ∈ E := by
    filter_upwards [ae_eq_measurableRatCoordsVersion D hD] with ω hEq
    change (measurableRatCoordsVersion D hD ω).1 (O, Q) = 0
    rw [← hEq]
    exact finiteCircleDist_eq_zero_of_inter (D ω) O Q h
  have hSourceMap : ∀ᵐ q ∂P.map (measurableRatCoordsVersion D hD), q ∈ E :=
    (ae_map_iff hSm.aemeasurable hE).2 hSource
  exact (ae_map_iff hY.aemeasurable hE).1 (hLaw ▸ hSourceMap)

 
theorem coupled_ratLaw
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω')
    (h : Ω → LQGMetric.DistC) (hh : Measurable h)
    (D : ℕ → Ω → LQGMetric.ContMetric) (hD : ∀ n, AEMeasurable (D n) P)
    (Y : ℕ → Ω' → (LQGMetric.CoordJ → ℝ) × RatCoords) (hY : ∀ n, Measurable (Y n))
    (hLaw : ∀ n, P'.map (Y n) = P.map (fun ω =>
      (LQGMetric.pairJ ⊤ (h ω), measurableRatCoordsVersion (D n) (hD n) ω))) (n : ℕ) :
    P'.map (fun ω => (Y n ω).2) = P.map (measurableRatCoordsVersion (D n) (hD n)) := by
  have hSource : Measurable (fun ω =>
      (LQGMetric.pairJ ⊤ (h ω), measurableRatCoordsVersion (D n) (hD n) ω)) :=
    ((LQGMetric.measurable_pairJ ⊤).comp hh).prodMk
      (measurable_measurableRatCoordsVersion (D n) (hD n))
  calc
    P'.map (fun ω => (Y n ω).2) = (P'.map (Y n)).map Prod.snd :=
      (Measure.map_map measurable_snd (hY n)).symm
    _ = (P.map (fun ω =>
        (LQGMetric.pairJ ⊤ (h ω), measurableRatCoordsVersion (D n) (hD n) ω))).map Prod.snd := by
      rw [hLaw n]
    _ = P.map (measurableRatCoordsVersion (D n) (hD n)) := Measure.map_map measurable_snd hSource

 
theorem ae_all_coupled_crossing_bounds
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω')
    (h : Ω → LQGMetric.DistC) (hh : Measurable h)
    (D : ℕ → Ω → LQGMetric.ContMetric) (hD : ∀ n, AEMeasurable (D n) P)
    (hLen : ∀ n, ∀ᵐ ω ∂P, (D n ω).IsLength)
    (Y : ℕ → Ω' → (LQGMetric.CoordJ → ℝ) × RatCoords) (hY : ∀ n, Measurable (Y n))
    (hLaw : ∀ n, P'.map (Y n) = P.map (fun ω =>
      (LQGMetric.pairJ ⊤ (h ω), measurableRatCoordsVersion (D n) (hD n) ω))) :
    ∀ᵐ ω ∂P', ∀ n (A : RatAnnulus) (O₁ O₁' Q : RatCircle),
      A.OppositeSides O₁ O₁' → CrossesAnn Q A →
      (Y n ω).2.1 (O₁, Q) ≤ (Y n ω).2.1 (O₁, O₁') + (Y n ω).2.2 A := by
  refine ae_all_iff.2 fun n => ae_all_iff.2 fun A => ae_all_iff.2 fun O₁ =>
    ae_all_iff.2 fun O₁' => ae_all_iff.2 fun Q => ?_
  by_cases h₁ : A.OppositeSides O₁ O₁'
  · by_cases hQ : CrossesAnn Q A
    · filter_upwards [ae_crossing_bound_of_coord_law (D n) (hD n) (hLen n)
        (fun ω => (Y n ω).2) (measurable_snd.comp (hY n))
        (coupled_ratLaw P P' h hh D hD Y hY hLaw n) A O₁ O₁' Q h₁ hQ] with ω hω
      exact fun _ _ => hω
    · exact Eventually.of_forall fun _ _ h => False.elim (hQ h)
  · exact Eventually.of_forall fun _ h _ => False.elim (h₁ h)

 
theorem ae_all_coupled_inter_zero
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω')
    (h : Ω → LQGMetric.DistC) (hh : Measurable h)
    (D : ℕ → Ω → LQGMetric.ContMetric) (hD : ∀ n, AEMeasurable (D n) P)
    (Y : ℕ → Ω' → (LQGMetric.CoordJ → ℝ) × RatCoords) (hY : ∀ n, Measurable (Y n))
    (hLaw : ∀ n, P'.map (Y n) = P.map (fun ω =>
      (LQGMetric.pairJ ⊤ (h ω), measurableRatCoordsVersion (D n) (hD n) ω))) :
    ∀ᵐ ω ∂P', ∀ n (O Q : RatCircle), (O.toSet ∩ Q.toSet).Nonempty → (Y n ω).2.1 (O, Q) = 0 := by
  refine ae_all_iff.2 fun n => ae_all_iff.2 fun O => ae_all_iff.2 fun Q => ?_
  by_cases hOQ : (O.toSet ∩ Q.toSet).Nonempty
  · filter_upwards [ae_inter_zero_of_coord_law (D n) (hD n) (fun ω => (Y n ω).2)
      (measurable_snd.comp (hY n)) (coupled_ratLaw P P' h hh D hD Y hY hLaw n) O Q hOQ] with ω hω
    exact fun _ => hω
  · exact Eventually.of_forall fun _ h => False.elim (hOQ h)

theorem tendsto_circleCoord {Y : ℕ → (LQGMetric.CoordJ → ℝ) × RatCoords}
    {y : (LQGMetric.CoordJ → ℝ) × RatCoords} (hY : Tendsto Y atTop (𝓝 y)) (O Q : RatCircle) :
    Tendsto (fun n => (Y n).2.1 (O, Q)) atTop (𝓝 (y.2.1 (O, Q))) :=
  ((continuous_apply (O, Q)).comp (continuous_fst.comp continuous_snd)).tendsto y |>.comp hY

theorem tendsto_aroundCoord {Y : ℕ → (LQGMetric.CoordJ → ℝ) × RatCoords}
    {y : (LQGMetric.CoordJ → ℝ) × RatCoords} (hY : Tendsto Y atTop (𝓝 y)) (A : RatAnnulus) :
    Tendsto (fun n => (Y n).2.2 A) atTop (𝓝 (y.2.2 A)) :=
  ((continuous_apply A).comp (continuous_snd.comp continuous_snd)).tendsto y |>.comp hY

 
theorem limit_crossing_bound {Y : ℕ → (LQGMetric.CoordJ → ℝ) × RatCoords}
    {y : (LQGMetric.CoordJ → ℝ) × RatCoords} (hY : Tendsto Y atTop (𝓝 y))
    (hfin : ∀ n (A : RatAnnulus) (O₁ O₁' Q : RatCircle),
      A.OppositeSides O₁ O₁' → CrossesAnn Q A →
      (Y n).2.1 (O₁, Q) ≤ (Y n).2.1 (O₁, O₁') + (Y n).2.2 A)
    (A : RatAnnulus) (O₁ O₁' Q : RatCircle) (h₁ : A.OppositeSides O₁ O₁')
    (hQ : CrossesAnn Q A) :
    y.2.1 (O₁, Q) ≤ y.2.1 (O₁, O₁') + y.2.2 A :=
  le_of_tendsto_of_tendsto' (tendsto_circleCoord hY O₁ Q)
    ((tendsto_circleCoord hY O₁ O₁').add (tendsto_aroundCoord hY A))
    (fun n => hfin n A O₁ O₁' Q h₁ hQ)

 
theorem limit_inter_zero {Y : ℕ → (LQGMetric.CoordJ → ℝ) × RatCoords}
    {y : (LQGMetric.CoordJ → ℝ) × RatCoords} (hY : Tendsto Y atTop (𝓝 y))
    (hfin : ∀ n (O Q : RatCircle), (O.toSet ∩ Q.toSet).Nonempty → (Y n).2.1 (O, Q) = 0)
    (O Q : RatCircle) (h : (O.toSet ∩ Q.toSet).Nonempty) : y.2.1 (O, Q) = 0 :=
  tendsto_nhds_unique (tendsto_circleCoord hY O Q)
    (tendsto_const_nhds.congr fun n => (hfin n O Q h).symm)

end SupercriticalLQGUniqueness.B2.PfeAxioms
