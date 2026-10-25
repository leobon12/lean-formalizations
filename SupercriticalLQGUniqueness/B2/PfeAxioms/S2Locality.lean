import SupercriticalLQGUniqueness.B2.PfeAxioms.S2LocalityGeom
import SupercriticalLQGUniqueness.B2.PfeAxioms.S2LocalData
import SupercriticalLQGUniqueness.B2.PfeAxioms.S2GFFPlusCont
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLowerLocalized

 

























set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric LQGMetric.DFGPS.L217
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

def locObsU (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (U : Set ℂ) (g : DistC) (p : U × U) : ℝ≥0∞ :=
  ⨅ (j : ℕ) (hx : (p.1 : ℂ) ∈ exhW U j) (hy : (p.2 : ℂ) ∈ exhW U j),
    lowerLocalizedNeighborhoodObservable ξ ε (fun n => m (ε n)) (V := exhV U j)
      ⟨(p.1 : ℂ), exhW_subset_exhV U j hx⟩ ⟨(p.2 : ℂ), exhW_subset_exhV U j hy⟩ g

 
theorem internal_mono' (D : LSCMetric) {S S' : Set ℂ} (hSS : S ⊆ S') (x y : S')
    (hx : (x : ℂ) ∈ S) (hy : (y : ℂ) ∈ S) :
    D.internal S' (x, y) ≤ D.internal S (⟨x, hx⟩, ⟨y, hy⟩) :=
  internal_mono D hSS ⟨x, hx⟩ ⟨y, hy⟩

 

theorem layer_sandwich_of_local_data
    (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (Φ : LSCMetric) (hlen : Φ.IsLengthSpace)
    (hforget : Continuous (PfeWeyl.euclidForget Φ))
    (g : DistC) (F : C(ℂ, ℝ))
    (Fk : ℕ → C(ℂ, ℝ)) (Mk : ℕ → ℝ) (ψ : ℕ → ℕ → C(ℂ, ℝ)) (E : ℕ → LSCMetric)
    (hFkM : ∀ k z, |Fk k z| ≤ Mk k)
    (hFk : ∀ k, EqOn F (Fk k) (Metric.closedBall 0 ((k : ℝ) + 3)))
    (hE : ∀ k p, E k p = weylScale (ξ : ℝ) (Fk k) Φ p)
    (hconv : ∀ k, Tendsto (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ψ k n))
      atTop (𝓝 (E k)))
    (hsmall : ∀ k, PfeWeyl.SmallAnnulusCosts
      (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ψ k n)) (E k)
      (Metric.closedBall 0 ((k : ℝ) + 1 / 2)) (patchBall k))
    (hclose : ∀ k, ∀ θ : ℝ, 0 < θ → ∀ᶠ n in atTop, ∀ z ∈ patchBall k,
      |locMollifyC (ε n : ℝ) (ε n).property g z - ψ k n z| ≤ θ)
    (D : LSCMetric) (hD : ∀ p, D p = weylScale (ξ : ℝ) F Φ p)
    (U : Set ℂ) (j : ℕ) (u v : exhW U j) :
    D.internal (exhU U j)
        (⟨u, exhKout_subset_exhU U j (exhV_subset_exhKout U j (exhW_subset_exhV U j u.2))⟩,
         ⟨v, exhKout_subset_exhU U j (exhV_subset_exhKout U j (exhW_subset_exhV U j v.2))⟩) ≤
      lowerLocalizedNeighborhoodObservable ξ ε (fun n => m (ε n)) (V := exhV U j)
        ⟨u, exhW_subset_exhV U j u.2⟩ ⟨v, exhW_subset_exhV U j v.2⟩ g ∧
    lowerLocalizedNeighborhoodObservable ξ ε (fun n => m (ε n)) (V := exhV U j)
        ⟨u, exhW_subset_exhV U j u.2⟩ ⟨v, exhW_subset_exhV U j v.2⟩ g ≤
      D.internal (exhW U j) (u, v) := by
  have hξ0 : (0 : ℝ) ≤ ξ := ξ.property.le
  set u' : exhV U j := ⟨u, exhW_subset_exhV U j u.2⟩ with hu'
  set v' : exhV U j := ⟨v, exhW_subset_exhV U j v.2⟩ with hv'
  set u'' : exhU U j :=
    ⟨u, exhKout_subset_exhU U j (exhV_subset_exhKout U j (exhW_subset_exhV U j u.2))⟩ with hu''
  set v'' : exhU U j :=
    ⟨v, exhKout_subset_exhU U j (exhV_subset_exhKout U j (exhW_subset_exhV U j v.2))⟩ with hv''
  have hne : (exhV U j).Nonempty := ⟨u, exhW_subset_exhV U j u.2⟩
  have hb : ∀ z, -Mk j ≤ Fk j z ∧ Fk j z ≤ Mk j := fun z => abs_le.1 (hFkM j z)
  have hN : EqOn F (Fk j) (Metric.ball 0 ((j : ℝ) + 3)) := fun z hz =>
    hFk j (Metric.ball_subset_closedBall hz)
  have hsm : PfeWeyl.SmallAnnulusCosts
      (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ψ j n)) (E j)
      (exhK U j) (exhV U j) :=
    smallAnnulusCosts_restrict (hsmall j) (exhK_subset_closedBall U j)
      (lt_min (by norm_num) (half_pos (exhA_pos j)))
      (fun z hz => ball_subset_exhV_of_mem_exhK U j hz)
  have hs : (E j).internal (exhU U j) (u'', v'') ≤
        lowerNeighborhoodObservable
          (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ψ j n)) (exhV U j) u' v' ∧
      lowerNeighborhoodObservable
          (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ψ j n)) (exhV U j) u' v' ≤
        (E j).internal (exhW U j) (u, v) :=
    buffered_neighborhood_observable_sandwich (hconv j)
      (fun n => PfeWeyl.isLengthSpace_normalizedLFPPMetric _ _ _)
      (fun n => finitePathsEuclideanContinuous_normalizedLFPPMetric _ _ _)
      (fun n => continuous_euclidForget_normalizedLFPPMetric _ _ _)
      (W := exhW U j) (V := exhV U j) (K := exhK U j) (Kout := exhKout U j) (U := exhU U j)
      (exhW_subset_exhV U j) (exhW_subset_interior_exhK U j) (exhV_subset_exhKout U j)
      (isCompact_exhKout U j) (exhKout_subset_exhU U j) (isOpen_exhV U j) (isCompact_exhK U j)
      (isCompact_frontier_exhV U j) (frontier_exhV_nonempty U j hne)
      (disjoint_exhK_frontier_exhV U j) hsm u v
  have hobs : lowerLocalizedNeighborhoodObservable ξ ε (fun n => m (ε n)) u' v' g =
      lowerNeighborhoodObservable
        (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ψ j n)) (exhV U j) u' v' := by
    unfold lowerLocalizedNeighborhoodObservable
    exact lowerNbhdObs_eq_of_weight_close ξ (fun n => m (ε n))
      (fun n => locMollifyC (ε n : ℝ) (ε n).property g) (ψ j) (isOpen_exhV U j)
      (fun θ hθ => (hclose j θ hθ).mono fun n hn z hz => hn z (exhV_subset_ball U j hz)) u' v'
  have hcU : D.internal (exhU U j) (u'', v'') = (E j).internal (exhU U j) (u'', v'') :=
    internal_weylScale_congr Φ D (E j) ξ hξ0 F (Fk j) hforget hlen hD (hE j)
      (-Mk j) (Mk j) hb Metric.isOpen_ball hN
      ((exhU_subset_ball U j).trans (Metric.ball_subset_ball (by linarith))) (u'', v'')
  have hcW : D.internal (exhW U j) (u, v) = (E j).internal (exhW U j) (u, v) :=
    internal_weylScale_congr Φ D (E j) ξ hξ0 F (Fk j) hforget hlen hD (hE j)
      (-Mk j) (Mk j) hb Metric.isOpen_ball hN
      ((exhW_subset_ball U j).trans (Metric.ball_subset_ball (by linarith))) (u, v)
  rw [hobs, hcU, hcW]
  exact hs

 

theorem internal_eq_locObsU_of_local_data
    (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (Φ : LSCMetric) (hlen : Φ.IsLengthSpace)
    (hforget : Continuous (PfeWeyl.euclidForget Φ))
    (g : DistC) (F : C(ℂ, ℝ))
    (Fk : ℕ → C(ℂ, ℝ)) (Mk : ℕ → ℝ) (ψ : ℕ → ℕ → C(ℂ, ℝ)) (E : ℕ → LSCMetric)
    (hFkM : ∀ k z, |Fk k z| ≤ Mk k)
    (hFk : ∀ k, EqOn F (Fk k) (Metric.closedBall 0 ((k : ℝ) + 3)))
    (hE : ∀ k p, E k p = weylScale (ξ : ℝ) (Fk k) Φ p)
    (hconv : ∀ k, Tendsto (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ψ k n))
      atTop (𝓝 (E k)))
    (hsmall : ∀ k, PfeWeyl.SmallAnnulusCosts
      (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ψ k n)) (E k)
      (Metric.closedBall 0 ((k : ℝ) + 1 / 2)) (patchBall k))
    (hclose : ∀ k, ∀ θ : ℝ, 0 < θ → ∀ᶠ n in atTop, ∀ z ∈ patchBall k,
      |locMollifyC (ε n : ℝ) (ε n).property g z - ψ k n z| ≤ θ)
    (D : LSCMetric) (hD : ∀ p, D p = weylScale (ξ : ℝ) F Φ p)
    {U : Set ℂ} (hU : IsOpen U) (x y : U) :
    D.internal U (x, y) = locObsU ξ m ε U g (x, y) := by
  have hξ0 : (0 : ℝ) ≤ ξ := ξ.property.le
  have hDforget : Continuous (PfeWeyl.euclidForget D) :=
    Uniqueness.Toolkit.WeylShift.continuous_forget_of_weyl Φ D ξ hξ0 F hforget hD
  have key := layer_sandwich_of_local_data ξ m ε Φ hlen hforget g F Fk Mk ψ E hFkM hFk hE
    hconv hsmall hclose D hD U
  apply le_antisymm
  · refine le_iInf fun j => le_iInf fun hx => le_iInf fun hy => ?_
    exact (internal_mono' D (exhU_subset U j) x y
      (exhKout_subset_exhU U j (exhV_subset_exhKout U j (exhW_subset_exhV U j hx)))
      (exhKout_subset_exhU U j (exhV_subset_exhKout U j (exhW_subset_exhV U j hy)))).trans
      (key j ⟨x, hx⟩ ⟨y, hy⟩).1
  · rw [internal_eq_iInf_of_exhaustion D hDforget (exhW U) (isOpen_exhW U) (monotone_exhW U)
      (exhW_subset U) (subset_iUnion_exhW hU) x y]
    exact iInf_mono fun j => iInf_mono fun hx => iInf_mono fun hy => (key j ⟨x, hx⟩ ⟨y, hy⟩).2

theorem measurable_locObsU (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (U : Set ℂ) (p : U × U) :
    Measurable fun g => locObsU ξ m ε U g p := by
  unfold locObsU
  refine Measurable.iInf fun j => Measurable.iInf fun hx => Measurable.iInf fun hy => ?_
  exact measurable_lowerLocalizedNeighborhoodObservable ξ ε (fun n => m (ε n))
    (isOpen_exhV U j) (Metric.isBounded_ball.subset (exhV_subset_ball U j)) _ _

theorem locObsU_congr (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (U : TopologicalSpace.Opens ℂ) {g g' : DistC} (he : restrictTo U g = restrictTo U g') :
    locObsU ξ m ε (U : Set ℂ) g = locObsU ξ m ε (U : Set ℂ) g' := by
  funext p
  unfold locObsU
  refine iInf_congr fun j => iInf_congr fun hx => iInf_congr fun hy => ?_
  exact lowerLocalizedNeighborhoodObservable_congr ξ ε (fun n => m (ε n)) (isOpen_exhV _ j)
    _ _ U (eventually_closedBall_sqrt_subset_of_compact ε hε (isCompact_closure_exhV _ j) U
      (closure_exhV_subset _ j)) he

 

theorem exists_locObsU_factor (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (U : TopologicalSpace.Opens ℂ) :
    ∃ F : DistOn U → (↥(U : Set ℂ) × ↥(U : Set ℂ) → ℝ≥0∞), Measurable F ∧
      ∀ g, locObsU ξ m ε (U : Set ℂ) g = F (restrictTo U g) := by
  have H : ∀ p : ↥(U : Set ℂ) × ↥(U : Set ℂ), ∃ k : DistOn U → ℝ≥0∞, Measurable k ∧
      (fun g => locObsU ξ m ε (U : Set ℂ) g p) = k ∘ restrictTo U := fun p => by
    have hc := comap_le_fieldSigma_of_local (Ω := DistC)
      (measurable_locObsU ξ m ε (U : Set ℂ) p) U
      (fun g g' he => by rw [locObsU_congr ξ m ε hε U he]) id
    exact Measurable.exists_eq_measurable_comp (measurable_iff_comap_le.2 hc)
  choose k hk hkeq using H
  refine ⟨fun x p => k p x, Measurable.of_eval fun p => hk p, fun g => ?_⟩
  funext p
  exact congrFun (hkeq p) g

variable (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
  (ε : ℕ → Set.Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
  (Φ : DistC → LSCMetric)
  (hlsc : PfeWeyl.NormalizedLscLimit ξ m ε Φ)
  (hgeo : PfeWeyl.NormalizedLimitGeometry Φ)
  (htail : PfeWeyl.NormalizedAcrossTails Φ)
  (hsmall : PfeWeyl.NormalizedSmallAnnuli ξ m ε Φ)

include hε hlsc hgeo htail hsmall in
 


theorem patchWitness_locality_of_gffPlusCont
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsGFFPlusCont h P) (U : TopologicalSpace.Opens ℂ) :
    ∃ F : DistOn U → (↥(U : Set ℂ) × ↥(U : Set ℂ) → ℝ≥0∞), Measurable F ∧
      ∀ᵐ ω ∂P, (patchWitness ξ m ε (h ω)).internal (U : Set ℂ) = F (restrictTo U (h ω)) := by
  obtain ⟨F, hFm, hF⟩ := exists_locObsU_factor ξ m ε hε U
  refine ⟨F, hFm, ?_⟩
  obtain ⟨h₀, g, hh₀, -, hdec⟩ := LQGMetric.DFGPS.T12.isGFFPlusCont_decomp hh
  have hh₀' : IsNormalizedWholePlaneGFF h₀ P := isNormalizedWholePlaneGFF_iff_old.mpr hh₀
  filter_upwards [ae_patch_local_data_of_normalized ξ m ε hε Φ hlsc hgeo htail hsmall P h₀ hh₀',
    ae_patchWitness_weyl_of_normalized ξ m ε hε Φ hlsc hgeo htail hsmall P h₀ hh₀']
    with ω hdat hW
  obtain ⟨hlen, hforget, -, -, hdata⟩ := hdat
  obtain ⟨Fk, Mk, ψ, E, hFkM, hFk, hE, hconv, hsm, hclose⟩ := hdata (g ω)
  rw [← hF, hdec ω]
  funext p
  obtain ⟨x, y⟩ := p
  exact internal_eq_locObsU_of_local_data ξ m ε (Φ (h₀ ω)) hlen hforget
    (addFun (h₀ ω) (g ω)) (g ω) Fk Mk ψ E hFkM hFk hE hconv hsm hclose _ (hW (g ω)).2
    U.isOpen x y

end SupercriticalLQGUniqueness.B2.PfeAxioms
