import SupercriticalLQGUniqueness.B2.PfeLocal.L5Indep
import SupercriticalLQGUniqueness.B2.LscTop.Compact
import SupercriticalLQGUniqueness.B2.LscTop.Limits
import LQGMetric.Prob.CondIndepAEDet

 





















set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal
open LQGMetric (CondIndepEv DistC)

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open Uniqueness.Toolkit.CompactPathInfimum

section Disint

variable {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]

 
theorem l5_kernel_ae (P : Measure Ω) [IsFiniteMeasure P] {h : Ω → DistC} (hh : Measurable h)
    {G : Set Ω} (hG : ∀ᵐ ω ∂P, ω ∈ G) :
    ∀ᵐ g ∂P.map h, ∀ᵐ ω ∂(condDistrib id h P g), h ω = g ∧ ω ∈ G := by
  set G' := (toMeasurable P Gᶜ)ᶜ
  have hG'm : MeasurableSet G' := (measurableSet_toMeasurable _ _).compl
  have hG'G : G' ⊆ G := fun ω hω => by
    by_contra hc
    exact hω (subset_toMeasurable P Gᶜ hc)
  have hG' : ∀ᵐ ω ∂P, ω ∈ G' := by
    rw [ae_iff]
    show P G'ᶜ = 0
    rw [compl_compl, measure_toMeasurable]
    exact ae_iff.1 hG
  set S := {p : DistC × Ω | h p.2 = p.1 ∧ p.2 ∈ G'}
  have hS : MeasurableSet S :=
    (measurableSet_eq_fun (hh.comp measurable_snd) measurable_fst).inter (measurable_snd hG'm)
  have hae : ∀ᵐ p ∂((P.map h) ⊗ₘ condDistrib id h P), p ∈ S := by
    rw [compProd_map_condDistrib hh.aemeasurable aemeasurable_id,
      ae_map_iff (p := fun q => q ∈ S) (hh.prodMk measurable_id).aemeasurable hS]
    filter_upwards [hG'] with ω hω
    exact ⟨rfl, hω⟩
  filter_upwards [(Measure.ae_compProd_iff hS).1 hae] with g hg
  filter_upwards [hg] with ω hω
  exact ⟨hω.1, hG'G hω.2⟩

theorem l5_copy_ae_iff (P : Measure Ω) [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : Measurable h) {S : Set (Ω × Ω)} (hS : MeasurableSet S) :
    (∀ᵐ p ∂(l4Copy P h hh), p ∈ S) ↔
      ∀ᵐ ω ∂P, ∀ᵐ ω₂ ∂(condDistrib id h P (h ω)), (ω, ω₂) ∈ S := by
  unfold l4Copy LQGMetric.condCopyMeasure
  rw [Measure.ae_compProd_iff (p := fun x => x ∈ S) hS]
  rfl

theorem l5_kernel_pair_of_copy (P : Measure Ω) [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : Measurable h) {S : Set (Ω × Ω)} (hS : MeasurableSet S)
    (hc : ∀ᵐ p ∂(l4Copy P h hh), p ∈ S) :
    ∀ᵐ g ∂P.map h, ∀ᵐ ω ∂(condDistrib id h P g), ∀ᵐ ω₂ ∂(condDistrib id h P g), (ω, ω₂) ∈ S := by
  have h1 := (l5_copy_ae_iff P hh hS).1 hc
  filter_upwards [l5_kernel_ae P hh
    (G := {ω | ∀ᵐ ω₂ ∂(condDistrib id h P (h ω)), (ω, ω₂) ∈ S}) h1] with g hg
  filter_upwards [hg] with ω hω
  have h2 : ∀ᵐ ω₂ ∂(condDistrib id h P (h ω)), (ω, ω₂) ∈ S := hω.2
  rw [hω.1] at h2
  exact h2

theorem l5_copy_of_kernel_pair (P : Measure Ω) [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : Measurable h) {S : Set (Ω × Ω)} (hS : MeasurableSet S)
    (hk : ∀ᵐ g ∂P.map h, ∀ᵐ ω ∂(condDistrib id h P g),
      ∀ᵐ ω₂ ∂(condDistrib id h P g), (ω, ω₂) ∈ S) :
    ∀ᵐ p ∂(l4Copy P h hh), p ∈ S := by
  rw [l5_copy_ae_iff P hh hS]
  set κ := LQGMetric.condCopyKernel id h P hh
  set S₁ := {ω | κ ω (Prod.mk ω ⁻¹' Sᶜ) = 0}
  have hS₁ : MeasurableSet S₁ :=
    Kernel.measurable_kernel_prodMk_left (κ := κ) hS.compl (measurableSet_singleton 0)
  have hS₁' : ∀ ω, ω ∈ S₁ ↔ ∀ᵐ ω₂ ∂(condDistrib id h P (h ω)), (ω, ω₂) ∈ S := fun ω => by
    simp only [S₁, mem_setOf_eq, ae_iff]
    rfl
  have hmap : ∀ᵐ p ∂(P.map fun ω => (h ω, id ω)), p.2 ∈ S₁ := by
    rw [← compProd_map_condDistrib hh.aemeasurable aemeasurable_id,
      Measure.ae_compProd_iff (p := fun q => q.2 ∈ S₁) (measurable_snd hS₁)]
    filter_upwards [hk, l5_kernel_ae P hh (G := univ) (ae_of_all _ fun _ => mem_univ _)] with
      g hg hsupp
    filter_upwards [hg, hsupp] with ω hω hω'
    rw [hS₁', hω'.1]
    exact hω
  have := (ae_map_iff (p := fun q => q.2 ∈ S₁) (hh.prodMk measurable_id).aemeasurable
    (measurable_snd hS₁)).1 hmap
  filter_upwards [this] with ω hω
  exact (hS₁' ω).1 hω

end Disint

 
theorem l5_circDist_eq_iInf (D : LSCMetric) (hgeo : L5Geo D) (q q' : ℚ × ℚ × ℚ) :
    l5CircDist D q q' =
      ⨅ R : ℕ, compactPathInf D (closedBall 0 (R : ℝ)) (l5Circ q) (l5Circ q') := by
  apply le_antisymm
  · refine le_iInf fun R => ?_
    unfold compactPathInf
    refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
      le_iInf fun _ => le_iInf fun ha => le_iInf fun hb => ?_
    calc l5CircDist D q q' ≤ D.1 (P a, P b) :=
          iInf_le_of_le (P a) (iInf_le_of_le ha (iInf_le_of_le (P b) (iInf_le _ hb)))
      _ ≤ D.len P a b := LQGMetric.MetricGeometry.edist_le_curveLength (D.pt ∘ P) hP.1
  · by_cases hfin : l5CircDist D q q' = ∞
    · rw [hfin]; exact le_top
    rcases (l5Circ q).eq_empty_or_nonempty with h0 | hne
    · exfalso; apply hfin; simp [l5CircDist, Iface.setDistance, h0]
    rcases (l5Circ q').eq_empty_or_nonempty with h0' | hne'
    · exfalso; apply hfin; simp [l5CircDist, Iface.setDistance, h0']
    obtain ⟨u, hu, v, hv, huv⟩ := setDistance_eq_at_min D (isCompact_sphere _ _)
      (isCompact_sphere _ _) hne hne'
    have hlt : D.1 (u, v) < ∞ := by
      rw [← huv]; exact lt_top_iff_ne_top.2 hfin
    obtain ⟨P, a, b, hP, hPa, hPb, hlen⟩ := hgeo.2 u v hlt
    have hcont := continuousOn_euclidean_of_small_metric D hgeo.1 P hP
    have hcpt : IsCompact (P '' Icc a b) := isCompact_Icc.image_of_continuousOn hcont
    obtain ⟨r, hr⟩ := hcpt.isBounded.subset_closedBall 0
    obtain ⟨R, hR⟩ := exists_nat_ge r
    refine iInf_le_of_le R ?_
    calc compactPathInf D (closedBall 0 (R : ℝ)) (l5Circ q) (l5Circ q') ≤ D.len P a b :=
          l5_compactPathInf_le D P a b hP
            (fun t ht => closedBall_subset_closedBall hR (hr ⟨t, ht, rfl⟩))
            (hPa ▸ hu) (hPb ▸ hv)
      _ = l5CircDist D q q' := by rw [hlen, ← huv]; rfl

 
theorem l5_eq_of_circDist (D D' : LSCMetric) (hgeo : L5Geo D) (hgeo' : L5Geo D')
    (heq : ∀ q q' : ℚ × ℚ × ℚ, l5CircDist D q q' = l5CircDist D' q q') : D = D' := by
  apply Subtype.ext
  funext p
  rcases p with ⟨x, y⟩
  refine le_antisymm ?_ ?_
  · have := l5_edist_le_of_circles D' D hgeo' 1 one_ne_zero
      (fun q q' => by rw [one_mul]; exact (heq q q').le) x y
    rwa [one_mul] at this
  · have := l5_edist_le_of_circles D D' hgeo 1 one_ne_zero
      (fun q q' => by rw [one_mul]; exact (heq q q').symm.le) x y
    rwa [one_mul] at this

theorem measurable_l5CircDist (q q' : ℚ × ℚ × ℚ) :
    Measurable fun D : LSCMetric => l5CircDist D q q' :=
  l4_measurable_setDistance (isCompact_sphere _ _) (isCompact_sphere _ _)

 


theorem l5_exists_measurable_of_copy {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [Nonempty Ω] (P : Measure Ω) [IsProbabilityMeasure P] {h : Ω → DistC} (hh : Measurable h)
    {L : Ω → LSCMetric} (hL : Measurable L)
    (hcopy : ∀ᵐ p ∂(l4Copy P h hh), L p.1 = L p.2) :
    ∃ Φ : DistC → LSCMetric, Measurable Φ ∧ ∀ᵐ ω ∂P, L ω = Φ (h ω) := by
  classical
  letI : MeasurableSpace LSCFun := borel LSCFun
  haveI : BorelSpace LSCFun := ⟨rfl⟩
  set Lh : Ω → LSCFun := fun ω => (L ω).toLSCFun
  have hLh : Measurable Lh := LscTop.measurable_toLSCFun.comp hL
  have hdiagF : MeasurableSet {p : LSCFun × LSCFun | p.1 = p.2} :=
    isClosed_diagonal.measurableSet
  have hci : CondIndepEv (MeasurableSpace.comap (fun p : Ω × Ω => h p.1) inferInstance)
      (MeasurableSpace.comap (fun p : Ω × Ω => Lh p.1) inferInstance)
      (MeasurableSpace.comap (fun p : Ω × Ω => Lh p.2) inferInstance) (l4Copy P h hh) := by
    have := LQGMetric.condIndepEv_condCopy_fst (Y := id) (X := h) (μ := P) hh
    refine this.mono ?_ ?_
    · rw [show (fun p : Ω × Ω => Lh p.1) = Lh ∘ Prod.fst from rfl, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono hLh.comap_le
    · rw [show (fun p : Ω × Ω => Lh p.2) = Lh ∘ Prod.snd from rfl, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono hLh.comap_le
  have heq : (fun p : Ω × Ω => Lh p.1) =ᵐ[l4Copy P h hh] fun p => Lh p.2 :=
    hcopy.mono fun p hp => by simp only [Lh, hp]
  obtain ⟨Φ₀, hΦ₀, hΦ₀e⟩ := LQGMetric.aeDeterminedBy_of_condIndepEv_of_ae_eq
    (hh.comp measurable_fst) (hLh.comp measurable_fst) hci heq
  set A := {ω | Lh ω = Φ₀ (h ω)}
  have hAm : MeasurableSet A := hdiagF.preimage (hLh.prodMk (hΦ₀.comp hh))
  have hA : ∀ᵐ ω ∂P, ω ∈ A := by
    rw [← l4Copy_fst P h hh, ae_map_iff (p := fun ω => ω ∈ A) measurable_fst.aemeasurable hAm]
    exact hΦ₀e
  set κ := condDistrib id h P
  set S : Set (DistC × Ω) := {p | h p.2 = p.1 ∧ p.2 ∈ A}
  have hS : MeasurableSet S :=
    (measurableSet_eq_fun (hh.comp measurable_snd) measurable_fst).inter (measurable_snd hAm)
  set T : Set DistC := {g | 0 < κ g (Prod.mk g ⁻¹' S)}
  have hT : MeasurableSet T :=
    measurableSet_lt measurable_const (Kernel.measurable_kernel_prodMk_left (κ := κ) hS)
  have hTae : ∀ᵐ g ∂P.map h, g ∈ T := by
    filter_upwards [l5_kernel_ae P hh hA] with g hg
    have hfull : ∀ᵐ ω ∂κ g, ω ∈ Prod.mk g ⁻¹' S := hg.mono fun ω hω => ⟨hω.1, hω.2⟩
    have h1 : κ g (Prod.mk g ⁻¹' S) = 1 := by
      rw [← prob_compl_eq_zero_iff (measurable_prodMk_left hS)]
      exact ae_iff.1 hfull
    show 0 < κ g (Prod.mk g ⁻¹' S)
    rw [h1]
    exact one_pos
  have hTrange : ∀ g ∈ T, ∃ D : LSCMetric, D.toLSCFun = Φ₀ g := by
    intro g hg
    obtain ⟨ω, hω1, hω2⟩ := nonempty_of_measure_ne_zero hg.ne'
    have e1 : h ω = g := hω1
    have e2 : Lh ω = Φ₀ (h ω) := hω2
    exact ⟨L ω, by rw [← e1]; exact e2⟩
  set d : LSCMetric := Classical.arbitrary LSCMetric
  set Φ : DistC → LSCMetric := fun g => if hg : g ∈ T then Classical.choose (hTrange g hg) else d
  have hΦ' : ∀ g, (Φ g).toLSCFun = T.piecewise Φ₀ (fun _ => d.toLSCFun) g := by
    intro g
    by_cases hg : g ∈ T
    · simp only [Φ, dif_pos hg, Set.piecewise_eq_of_mem _ _ _ hg]
      exact Classical.choose_spec (hTrange g hg)
    · simp only [Φ, dif_neg hg, Set.piecewise_eq_of_notMem _ _ _ hg]
  have hΦm : Measurable Φ := by
    rw [LscTop.measurable_iff_toLSCFun]
    have : (fun g => (Φ g).toLSCFun) = T.piecewise Φ₀ (fun _ => d.toLSCFun) := funext hΦ'
    rw [this]
    exact hΦ₀.piecewise hT measurable_const
  refine ⟨Φ, hΦm, ?_⟩
  filter_upwards [hA, ae_of_ae_map hh.aemeasurable hTae] with ω hω hωT
  apply LscTop.toLSCFun_injective
  rw [hΦ' (h ω), Set.piecewise_eq_of_mem _ _ _ hωT]
  exact hω

end SupercriticalLQGUniqueness.B2.PfeLocal
