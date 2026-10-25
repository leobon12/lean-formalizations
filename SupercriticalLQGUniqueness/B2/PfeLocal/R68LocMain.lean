import SupercriticalLQGUniqueness.B2.PfeLocal.R68LocData

 






















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric LQGMetric.DFGPS.L217
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open PfeAxioms

 
theorem r68_layer_sandwich_of_local_data
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
    (U : Set ℂ)
    (hupper : ∀ (k j l : ℕ) (b₁ b₂ : ℚ × ℚ × ℚ) (η : ℚ), 0 < η →
      liminf (fun n => r68Y (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ψ k n))
        (r68Q U j l) b₁ b₂ η) atTop ≤ r68Z (E k) (r68Q U j l) b₁ b₂)
    (hclose : ∀ k, ∀ θ : ℝ, 0 < θ → ∀ᶠ n in atTop, ∀ z ∈ patchBall k,
      |locMollifyC (ε n : ℝ) (ε n).property g z - ψ k n z| ≤ θ)
    (D : LSCMetric) (hD : ∀ p, D p = weylScale (ξ : ℝ) F Φ p)
    (j : ℕ) (u v : exhW U j) :
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
  have hb : ∀ z, -Mk j ≤ Fk j z ∧ Fk j z ≤ Mk j := fun z => abs_le.1 (hFkM j z)
  have hN : EqOn F (Fk j) (Metric.ball 0 ((j : ℝ) + 3)) := fun z hz =>
    hFk j (Metric.ball_subset_closedBall hz)
  have hEforget : Continuous (PfeWeyl.euclidForget (E j)) :=
    Uniqueness.Toolkit.WeylShift.continuous_forget_of_weyl Φ (E j) ξ hξ0 (Fk j) hforget (hE j)
  have hs : (E j).internal (exhU U j) (u'', v'') ≤
        lowerNeighborhoodObservable
          (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ψ j n)) (exhV U j) u' v' ∧
      lowerNeighborhoodObservable
          (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ψ j n)) (exhV U j) u' v' ≤
        (E j).internal (exhW U j) (u, v) :=
    ⟨compact_buffer_le_lowerNeighborhoodObservable (hconv j) (exhV_subset_exhKout U j)
        (isCompact_exhKout U j) (exhKout_subset_exhU U j) u' v',
      r68_lowerNbhdObs_le_internal hEforget (isOpen_exhW U j) (exhW_subset_exhV U j)
        (fun l b₁ b₂ η hη => hupper j j l b₁ b₂ η hη) u v⟩
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

 

theorem r68_internal_eq_locObsU_of_local_data
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
    {U : Set ℂ}
    (hupper : ∀ (k j l : ℕ) (b₁ b₂ : ℚ × ℚ × ℚ) (η : ℚ), 0 < η →
      liminf (fun n => r68Y (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (ψ k n))
        (r68Q U j l) b₁ b₂ η) atTop ≤ r68Z (E k) (r68Q U j l) b₁ b₂)
    (hclose : ∀ k, ∀ θ : ℝ, 0 < θ → ∀ᶠ n in atTop, ∀ z ∈ patchBall k,
      |locMollifyC (ε n : ℝ) (ε n).property g z - ψ k n z| ≤ θ)
    (D : LSCMetric) (hD : ∀ p, D p = weylScale (ξ : ℝ) F Φ p)
    (hU : IsOpen U) (x y : U) :
    D.internal U (x, y) = locObsU ξ m ε U g (x, y) := by
  have hξ0 : (0 : ℝ) ≤ ξ := ξ.property.le
  have hDforget : Continuous (PfeWeyl.euclidForget D) :=
    Uniqueness.Toolkit.WeylShift.continuous_forget_of_weyl Φ D ξ hξ0 F hforget hD
  have key := r68_layer_sandwich_of_local_data ξ m ε Φ hlen hforget g F Fk Mk ψ E hFkM hFk hE
    hconv U hupper hclose D hD
  apply le_antisymm
  · refine le_iInf fun j => le_iInf fun hx => le_iInf fun hy => ?_
    exact (internal_mono' D (exhU_subset U j) x y
      (exhKout_subset_exhU U j (exhV_subset_exhKout U j (exhW_subset_exhV U j hx)))
      (exhKout_subset_exhU U j (exhV_subset_exhKout U j (exhW_subset_exhV U j hy)))).trans
      (key j ⟨x, hx⟩ ⟨y, hy⟩).1
  · rw [internal_eq_iInf_of_exhaustion D hDforget (exhW U) (isOpen_exhW U) (monotone_exhW U)
      (exhW_subset U) (subset_iUnion_exhW hU) x y]
    exact iInf_mono fun j => iInf_mono fun hx => iInf_mono fun hy => (key j ⟨x, hx⟩ ⟨y, hy⟩).2

 

theorem r68_patchWitness_locality_of_gffPlusCont
    (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (ε : ℕ → Set.Ioi (0 : ℝ))
    {Q : ℝ} {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)} {V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {h' : Ω' → DistC} {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}
    (hB : Final.DG20CouplingData ξ Q m ε c V P' h' hN L)
    (hSA : Final.CoupledSmallAnnuli ξ m ε V P' hN L) (hAT : Final.CoupledAcrossTails P' L)
    (Φ : DistC → LSCMetric) (hII : ∀ᵐ ω ∂P', L ω = Φ (h' ω))
    (hpatch : R68PatchWeyl ξ m ε Φ) (hFFW : Iface.FixedFieldWeylAllBounded ξ m ε Φ)
    (hgeo : PfeWeyl.NormalizedLimitGeometry Φ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsGFFPlusCont h P) (U : TopologicalSpace.Opens ℂ) :
    ∃ F : DistOn U → (↥(U : Set ℂ) × ↥(U : Set ℂ) → ℝ≥0∞), Measurable F ∧
      ∀ᵐ ω ∂P, (patchWitness ξ m ε (h ω)).internal (U : Set ℂ) = F (restrictTo U (h ω)) := by
  obtain ⟨F, hFm, hF⟩ := exists_locObsU_factor ξ m ε hB.scale_tendsto U
  refine ⟨F, hFm, ?_⟩
  obtain ⟨h₀, g, hh₀, -, hdec⟩ := LQGMetric.DFGPS.T12.isGFFPlusCont_decomp hh
  have hh₀' : IsNormalizedWholePlaneGFF h₀ P := isNormalizedWholePlaneGFF_iff_old.mpr hh₀
  filter_upwards [r68_ae_patch_local_data hB hSA hAT hII hpatch hFFW hgeo (U : Set ℂ) P h₀ hh₀',
    hpatch P h₀ hh₀'] with ω hdat hW
  obtain ⟨hlen, hforget, hdata⟩ := hdat
  obtain ⟨Fk, Mk, ψ, E, hFkM, hFk, hE, hconv, hup, hclose⟩ := hdata (g ω)
  rw [← hF, hdec ω]
  funext p
  obtain ⟨x, y⟩ := p
  exact r68_internal_eq_locObsU_of_local_data ξ m ε (Φ (h₀ ω)) hlen hforget
    (addFun (h₀ ω) (g ω)) (g ω) Fk Mk ψ E hFkM hFk hE hconv hup hclose _ (hW (g ω)).2
    U.isOpen x y

end SupercriticalLQGUniqueness.B2.PfeLocal
