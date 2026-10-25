import SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents.HCodeBorel




 


set_option autoImplicit false
noncomputable section

open Set Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents

private theorem endpoints_ne (r : Set.Ioi (0 : ℝ))
    (a : Set.Ioo (3 / 4 : ℝ) 1) (u v : ℂ)
    (hu : u ∈ Metric.sphere (0 : ℂ) ((a : ℝ) * r))
    (hv : v ∈ Metric.sphere (0 : ℂ) (r : ℝ)) : u ≠ v := by
  intro h
  have hu' := Metric.mem_sphere.mp hu
  have hv' := Metric.mem_sphere.mp hv
  rw [h] at hu'
  have heq : (a : ℝ) * r = r := hu'.symm.trans hv'
  have hr : 0 < (r : ℝ) := r.property
  have ha : (a : ℝ) < 1 := a.property.2
  nlinarith

private theorem nonsingular_of_finite (D : LSCMetric) (u v : ℂ)
    (huv : u ≠ v) (hfin : D (u, v) < ⊤) :
    ¬ OptimalConstants.Ratios.Singular D u ∧ ¬ OptimalConstants.Ratios.Singular D v := by
  constructor
  · intro hs
    exact hfin.ne (hs v huv.symm)
  · intro hs
    have htop := hs u huv
    rw [D.isExtMetric.2.2.1] at htop
    exact hfin.ne htop

private theorem compact_annulus (r : Set.Ioi (0 : ℝ))
    (a : Set.Ioo (3 / 4 : ℝ) 1) :
    IsCompact (Metric.closedBall (0 : ℂ) (r : ℝ) \
      Metric.ball 0 ((a : ℝ) * r)) := by
  apply (isCompact_closedBall (0 : ℂ) (r : ℝ)).of_isClosed_subset
  · exact Metric.isClosed_closedBall.inter Metric.isOpen_ball.isClosed_compl
  · exact sdiff_subset

theorem H_iff_exists_HCode (D D' : LSCMetric) (ξ Qpar : ℝ)
    (r : Set.Ioi (0 : ℝ)) (a : Set.Ioo (3 / 4 : ℝ) 1)
    (C θ : Set.Ioi (0 : ℝ)) (c : ℝ) :
    OptimalConstants.Ratios.H D D' ξ Qpar r a C θ c ↔
      ∃ P : Measurability.GeodesicCodes.Path, ∃ u v : ℂ,
        HCode ξ Qpar r a C θ false ((D, D'), ((P, (u, v)), c)) := by
  constructor
  · rintro ⟨u, v, hu, hv, _, _, hcomp, P, s, t, hGeo,
      htrace, hdiam, hbound, hloopu, hloopv⟩
    let K : Set ℂ := Metric.closedBall (0 : ℂ) (r : ℝ) \
      Metric.ball 0 ((a : ℝ) * r)
    have htraceK : P '' Icc s t ⊆ K := by
      rintro y ⟨q, hq, rfl⟩
      exact htrace q hq
    have hEuc : ContinuousOn P (Icc s t) :=
      Toolkit.PathInfimum.continuousOn_euclidean_of_compact_trace D P hGeo.1
        (compact_annulus r a) htraceK
    have hsrcCompact : IsCompact (P '' Icc s t) :=
      isCompact_Icc.image_of_continuousOn hEuc
    obtain ⟨P', hcode, htrace'⟩ :=
      exists_geoCode_of_compact_geodesic D (P '' Icc s t)
        hsrcCompact P s t u v hGeo Subset.rfl
    have htrK : MapsTo P' Set.univ K := by
      intro q _
      exact htraceK (htrace' q)
    have hdiam' : Metric.diam (Set.range P') ≤ (r : ℝ) / 100 := by
      have hsub : Set.range P' ⊆ P '' Icc s t := by
        rintro y ⟨q, rfl⟩
        exact htrace' q
      exact (Metric.diam_mono hsub hsrcCompact.isBounded).trans hdiam
    refine ⟨P', u, v, ?_⟩
    change Measurability.GeodesicCodes.GeoCode (D, (P', (u, v))) ∧ MapsTo P' Set.univ K ∧
      u ∈ Metric.sphere (0 : ℂ) ((a : ℝ) * r) ∧
      v ∈ Metric.sphere (0 : ℂ) (r : ℝ) ∧
      Metric.diam (Set.range P') ≤ (r : ℝ) / 100 ∧
      ENNReal.ofReal (C : ℝ) * D (u, v) ≤ D' (u, v) ∧
      D (u, v) ≤ ENNReal.ofReal ((1 - (a : ℝ))⁻¹ *
        (r : ℝ) ^ (ξ * Qpar) * Real.exp (ξ * c)) ∧
      D (u, v) ≠ ⊤ ∧ OptimalConstants.Ratios.EndpointLoop D r a θ u v u ∧
        OptimalConstants.Ratios.EndpointLoop D r a θ u v v
    exact ⟨hcode, htrK, hu, hv, hdiam', hcomp, hbound,
      hcode.2.2.1.ne, hloopu, hloopv⟩
  · rintro ⟨P, u, v, hcode⟩
    change Measurability.GeodesicCodes.GeoCode (D, (P, (u, v))) ∧
      MapsTo P Set.univ
        (Metric.closedBall (0 : ℂ) (r : ℝ) \
          Metric.ball 0 ((a : ℝ) * r)) ∧
      u ∈ Metric.sphere (0 : ℂ) ((a : ℝ) * r) ∧
      v ∈ Metric.sphere (0 : ℂ) (r : ℝ) ∧
      Metric.diam (Set.range P) ≤ (r : ℝ) / 100 ∧
      ENNReal.ofReal (C : ℝ) * D (u, v) ≤ D' (u, v) ∧
      D (u, v) ≤ ENNReal.ofReal ((1 - (a : ℝ))⁻¹ *
        (r : ℝ) ^ (ξ * Qpar) * Real.exp (ξ * c)) ∧
      D (u, v) ≠ ⊤ ∧ OptimalConstants.Ratios.EndpointLoop D r a θ u v u ∧
        OptimalConstants.Ratios.EndpointLoop D r a θ u v v at hcode
    rcases hcode with ⟨hgeo, htrace, hu, hv, hdiam, hcomp,
      hbound, hfin, hloopu, hloopv⟩
    have hne : u ≠ v := endpoints_ne r a u v hu hv
    obtain ⟨hnsu, hnsv⟩ := nonsingular_of_finite D u v hne hgeo.2.2.1
    let P' : ℝ → ℂ := Measurability.GeodesicCodes.pathReal P
    have htr : ∀ q ∈ Icc (0 : ℝ) 1,
        q ∈ P' ⁻¹' (Metric.closedBall (0 : ℂ) (r : ℝ) \
          Metric.ball 0 ((a : ℝ) * r)) := by
      intro q hq
      change Measurability.GeodesicCodes.pathReal P q ∈
        Metric.closedBall (0 : ℂ) (r : ℝ) \
          Metric.ball 0 ((a : ℝ) * r)
      unfold Measurability.GeodesicCodes.pathReal
      rw [projIcc_of_mem zero_le_one hq]
      exact htrace (x := ⟨q, hq⟩) trivial
    have hsub : P' '' Icc (0 : ℝ) 1 ⊆ Set.range P := by
      rintro y ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, by
        unfold P' Measurability.GeodesicCodes.pathReal
        rw [projIcc_of_mem zero_le_one hq]⟩
    have hPrange : Bornology.IsBounded (Set.range P) := by
      have hc : IsCompact (Set.range P) := by
        simpa only [Set.image_univ] using (isCompact_univ.image P.continuous)
      exact hc.isBounded
    have hdiam' : Metric.diam (P' '' Icc (0 : ℝ) 1) ≤ (r : ℝ) / 100 :=
      (Metric.diam_mono hsub hPrange).trans hdiam
    exact ⟨u, v, hu, hv, hnsu, hnsv, hcomp, P', 0, 1,
      geoCode_isGeodesic D P u v hgeo, htr, hdiam', hbound,
      hloopu, hloopv⟩


theorem Htilde_iff_exists_HCode (D D' : LSCMetric) (ξ Qpar : ℝ)
    (r : Set.Ioi (0 : ℝ)) (a : Set.Ioo (3 / 4 : ℝ) 1)
    (C θ : Set.Ioi (0 : ℝ)) (c : ℝ) :
    OptimalConstants.Ratios.Htilde D D' ξ Qpar r a C θ c ↔
      ∃ P : Measurability.GeodesicCodes.Path, ∃ u v : ℂ,
        HCode ξ Qpar r a C θ true ((D, D'), ((P, (u, v)), c)) := by
  constructor
  · rintro ⟨u, v, hu, hv, _, _, hcomp, P, s, t, hGeo,
      htrace, hdiam, hbound, hloopu, hloopv⟩
    let K : Set ℂ := Metric.closedBall (0 : ℂ) (r : ℝ) \
      Metric.ball 0 ((a : ℝ) * r)
    have htraceK : P '' Icc s t ⊆ K := by
      rintro y ⟨q, hq, rfl⟩
      exact htrace q hq
    have hEuc : ContinuousOn P (Icc s t) :=
      Toolkit.PathInfimum.continuousOn_euclidean_of_compact_trace D' P hGeo.1
        (compact_annulus r a) htraceK
    have hsrcCompact : IsCompact (P '' Icc s t) :=
      isCompact_Icc.image_of_continuousOn hEuc
    obtain ⟨P', hcode, htrace'⟩ :=
      exists_geoCode_of_compact_geodesic D' (P '' Icc s t)
        hsrcCompact P s t u v hGeo Subset.rfl
    have htrK : MapsTo P' Set.univ K := by
      intro q _
      exact htraceK (htrace' q)
    have hdiam' : Metric.diam (Set.range P') ≤ (r : ℝ) / 100 := by
      have hsub : Set.range P' ⊆ P '' Icc s t := by
        rintro y ⟨q, rfl⟩
        exact htrace' q
      exact (Metric.diam_mono hsub hsrcCompact.isBounded).trans hdiam
    refine ⟨P', u, v, ?_⟩
    change Measurability.GeodesicCodes.GeoCode (D', (P', (u, v))) ∧ MapsTo P' Set.univ K ∧
      u ∈ Metric.sphere (0 : ℂ) ((a : ℝ) * r) ∧
      v ∈ Metric.sphere (0 : ℂ) (r : ℝ) ∧
      Metric.diam (Set.range P') ≤ (r : ℝ) / 100 ∧
      D' (u, v) ≤ ENNReal.ofReal (C : ℝ) * D (u, v) ∧
      D' (u, v) ≤ ENNReal.ofReal ((1 - (a : ℝ))⁻¹ *
        (r : ℝ) ^ (ξ * Qpar) * Real.exp (ξ * c)) ∧
      D' (u, v) ≠ ⊤ ∧ OptimalConstants.Ratios.EndpointLoop D' r a θ u v u ∧
        OptimalConstants.Ratios.EndpointLoop D' r a θ u v v
    exact ⟨hcode, htrK, hu, hv, hdiam', hcomp, hbound,
      hcode.2.2.1.ne, hloopu, hloopv⟩
  · rintro ⟨P, u, v, hcode⟩
    change Measurability.GeodesicCodes.GeoCode (D', (P, (u, v))) ∧
      MapsTo P Set.univ
        (Metric.closedBall (0 : ℂ) (r : ℝ) \
          Metric.ball 0 ((a : ℝ) * r)) ∧
      u ∈ Metric.sphere (0 : ℂ) ((a : ℝ) * r) ∧
      v ∈ Metric.sphere (0 : ℂ) (r : ℝ) ∧
      Metric.diam (Set.range P) ≤ (r : ℝ) / 100 ∧
      D' (u, v) ≤ ENNReal.ofReal (C : ℝ) * D (u, v) ∧
      D' (u, v) ≤ ENNReal.ofReal ((1 - (a : ℝ))⁻¹ *
        (r : ℝ) ^ (ξ * Qpar) * Real.exp (ξ * c)) ∧
      D' (u, v) ≠ ⊤ ∧ OptimalConstants.Ratios.EndpointLoop D' r a θ u v u ∧
        OptimalConstants.Ratios.EndpointLoop D' r a θ u v v at hcode
    rcases hcode with ⟨hgeo, htrace, hu, hv, hdiam, hcomp,
      hbound, hfin, hloopu, hloopv⟩
    have hne : u ≠ v := endpoints_ne r a u v hu hv
    obtain ⟨hnsu, hnsv⟩ := nonsingular_of_finite D' u v hne hgeo.2.2.1
    let P' : ℝ → ℂ := Measurability.GeodesicCodes.pathReal P
    have htr : ∀ q ∈ Icc (0 : ℝ) 1,
        q ∈ P' ⁻¹' (Metric.closedBall (0 : ℂ) (r : ℝ) \
          Metric.ball 0 ((a : ℝ) * r)) := by
      intro q hq
      change Measurability.GeodesicCodes.pathReal P q ∈
        Metric.closedBall (0 : ℂ) (r : ℝ) \
          Metric.ball 0 ((a : ℝ) * r)
      unfold Measurability.GeodesicCodes.pathReal
      rw [projIcc_of_mem zero_le_one hq]
      exact htrace (x := ⟨q, hq⟩) trivial
    have hsub : P' '' Icc (0 : ℝ) 1 ⊆ Set.range P := by
      rintro y ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, by
        unfold P' Measurability.GeodesicCodes.pathReal
        rw [projIcc_of_mem zero_le_one hq]⟩
    have hPrange : Bornology.IsBounded (Set.range P) := by
      have hc : IsCompact (Set.range P) := by
        simpa only [Set.image_univ] using (isCompact_univ.image P.continuous)
      exact hc.isBounded
    have hdiam' : Metric.diam (P' '' Icc (0 : ℝ) 1) ≤ (r : ℝ) / 100 :=
      (Metric.diam_mono hsub hPrange).trans hdiam
    exact ⟨u, v, hu, hv, hnsu, hnsv, hcomp, P', 0, 1,
      geoCode_isGeodesic D' P u v hgeo, htr, hdiam', hbound,
      hloopu, hloopv⟩

end SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents
