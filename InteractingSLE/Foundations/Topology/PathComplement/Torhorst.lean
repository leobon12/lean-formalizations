import InteractingSLE.Foundations.Topology.PathComplement.Basic
import InteractingSLE.Foundations.Complex.RiemannMap
import InteractingSLE.Foundations.PrimeEnd.Jordan

/-!
# Torhorst's theorem

Packet GEO-CARA of `planning/INFRA-GEO.md` §4: `isLocallyConnected_frontier_of_peano`, the first
assertion of [LT06] Proposition 3.3 (J. Luo and J. M. Thuswaldner, *On the fundamental group of
self-affine plane tiles*, Ann. Inst. Fourier 56 (2006), `source/external/LT06/LT06.md`, citing
Kuratowski, *Topology* II, §61 II Thm 4): the frontier of a complementary component of a locally
connected continuum is a locally connected continuum.

## Statement

The specification works in the Riemann sphere. A component `R` of `𝕊² \ C` for a locally
connected continuum `C ≠ 𝕊²` becomes, after a rotation of the sphere sending a point of `R` to `∞`,
the unbounded component of `ℂ \ C'` for a compact `C' ⊆ ℂ`; the frontier of `R` in the sphere is
the planar frontier. We state the planar version, for every component (bounded or not).

## Proof (conformal, after Pommerenke)

A bounded simply connected domain `D` whose frontier lies in a closed uniformly locally connected
set `E ⊆ ℂ \ D` has frontier `{f(ζ) : ζ ∈ 𝕋}` for the continuous extension `f` of its Riemann map
([Pom] C. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Thm 2.1, (iv) ⇒ (i) ⇒ (ii) ⇒
(iii), printed pp. 20–22, with QuantumZipper's C3 and C7), hence is a locally connected continuum
(the continuous image of a circle, [Pom] p. 19). For a bounded component `R` take `D = R`, `E = C`.
An unbounded component is moved to a bounded one by an inversion `w ↦ 1/(w - a)` about a point
`a ∉ closure R` (if there is none, `∂R = C`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open QuantumZipper.CA.Topo (ULC)

namespace InteractingSLE

/-! ### Continuous images of the circle -/

theorem locallyConnectedSpace_sphere_one : LocallyConnectedSpace (sphere (0 : ℂ) 1) :=
  locallyConnectedSpace_of_ulc isBounded_sphere (QuantumZipper.CA.Topo.ULC.sphere 0 1)

theorem locallyConnectedSpace_onePoint_real : LocallyConnectedSpace (OnePoint ℝ) :=
  have := locallyConnectedSpace_sphere_one
  cayleyBdryHomeomorph.locallyConnectedSpace

/-- The range of a continuous map of a compact locally connected space into `ℂ` is locally
connected ([Pom] p. 19; Newman, p. 89). -/
theorem locallyConnectedSpace_range {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [LocallyConnectedSpace X] {f : X → ℂ} (hf : Continuous f) :
    LocallyConnectedSpace (range f) := by
  have hc : Continuous (rangeFactorization f) := hf.rangeFactorization
  have hq : Topology.IsQuotientMap (rangeFactorization f) :=
    hc.isClosedMap.isQuotientMap hc rangeFactorization_surjective
  exact hq.isCoinducing.locallyConnectedSpace

/-! ### The Riemann map from `ℍ` -/

/-- **Riemann mapping theorem from `ℍ`**: a proper simply connected planar domain is the conformal
image of the upper half-plane. -/
theorem exists_isConformalBijection_H {D : Set ℂ} (hDo : IsOpen D) (hDc : IsConnected D)
    (hsc : IsSimplyConnected D) (hne : D ≠ univ) : ∃ ψ : ℂ → ℂ, IsConformalBijection ψ H D := by
  obtain ⟨z₀, hz₀⟩ := hDc.nonempty
  obtain ⟨φ, hφ, -⟩ := exists_isConformalBijection_ball hDo hDc hsc hne hz₀
  set e := QuantumZipper.CA.univalentOPH hDo hφ.1 hφ.2.injOn
  have htarget : e.target = ball (0 : ℂ) 1 := hφ.2.image_eq
  refine ⟨e.symm ∘ cayley, ?_, ?_⟩
  · refine (QuantumZipper.CA.differentiableOn_univalentOPH_symm hDo hφ.1 hφ.2.injOn).comp
      (QuantumZipper.CA.differentiableOn_cayley_Hbar.mono QuantumZipper.H_subset_Hbar) ?_
    rw [hφ.2.image_eq]
    exact QuantumZipper.CA.bijOn_cayley_H.mapsTo
  · have h2 : BijOn e.symm e.target e.source := e.symm.bijOn
    rw [htarget] at h2
    exact h2.comp QuantumZipper.CA.bijOn_cayley_H

/-! ### Bounded domains enclosed by a uniformly locally connected set -/

/-- **The frontier of a bounded simply connected domain enclosed by a ULC set is a locally
connected continuum** ([Pom] Thm 2.1, (iv) ⇒ (i) ⇒ (ii) ⇒ (iii), pp. 20–22): if `∂D ⊆ E` for a
closed bounded uniformly locally connected `E` disjoint from `D`, then `∂D` is the continuous image
of `ℝ ∪ {∞}` under the boundary extension of a Riemann map `ℍ → D`. -/
theorem frontier_isLocallyConnectedContinuum_of_ulc {D E : Set ℂ} (hDo : IsOpen D)
    (hDc : IsConnected D) (hDb : Bornology.IsBounded D) (hsc : IsSimplyConnected D)
    (hEc : IsClosed E) (hEb : Bornology.IsBounded E) (hEu : ULC E) (hfr : frontier D ⊆ E)
    (hED : Disjoint E D) :
    IsCompact (frontier D) ∧ IsConnected (frontier D) ∧ LocallyConnectedSpace (frontier D) := by
  have hne : D ≠ univ := fun h => NormedSpace.unbounded_univ ℝ ℂ (h ▸ hDb)
  obtain ⟨ψ, hψ⟩ := exists_isConformalBijection_H hDo hDc hsc hne
  obtain ⟨R₁, hR₁⟩ := hDb.subset_ball 0
  obtain ⟨R₂, hR₂⟩ := hEb.subset_closedBall 0
  have hcar : QuantumZipper.CA.Car.CarHyp ψ D E (max R₁ R₂) :=
    ⟨hψ.1, hψ.2, hDo, hR₁.trans (ball_subset_ball (le_max_left _ _)), hEc, hfr,
      fun x hx hxD => Set.disjoint_left.1 hED hx hxD,
      hR₂.trans (closedBall_subset_closedBall (le_max_right _ _))⟩
  obtain ⟨F, hEq, hF, -, wInf, -, hInf⟩ := QuantumZipper.CA.Car.continuousOn_extension hcar hEu
  have hcont := QuantumZipper.CA.Car.continuous_bdryMap hEq hF hInf
  have hrange : frontier D = range (QuantumZipper.CA.Car.bdryMap F wInf) := by
    rw [QuantumZipper.CA.Car.range_bdryMap,
      QuantumZipper.CA.Car.frontier_eq_insert_range hcar hEq hF hInf]
  rw [hrange]
  have := locallyConnectedSpace_onePoint_real
  exact ⟨isCompact_range hcont, isConnected_range hcont, locallyConnectedSpace_range hcont⟩

/-! ### Complementary components -/

section Components

variable {C : Set ℂ}

/-- The frontier of a component of an open set `F` lies outside `F`. -/
theorem frontier_connectedComponentIn_subset_compl {F : Set ℂ} (hF : IsOpen F) (z : ℂ) :
    frontier (connectedComponentIn F z) ⊆ Fᶜ := by
  intro x hx hxF
  have hRo : IsOpen (connectedComponentIn F z) := hF.connectedComponentIn
  rw [hRo.frontier_eq] at hx
  obtain ⟨u, hux, huR⟩ := mem_closure_iff.1 hx.1 _ hF.connectedComponentIn
    (mem_connectedComponentIn hxF)
  have h1 := connectedComponentIn_eq hux
  have h2 := connectedComponentIn_eq huR
  exact hx.2 (by rw [h2, ← h1]; exact mem_connectedComponentIn hxF)

/-- Two components of an open set are equal or disjoint. -/
theorem connectedComponentIn_eq_or_disjoint {F : Set ℂ} (z w : ℂ) :
    connectedComponentIn F z = connectedComponentIn F w ∨
      Disjoint (connectedComponentIn F z) (connectedComponentIn F w) := by
  by_cases h : (connectedComponentIn F z ∩ connectedComponentIn F w).Nonempty
  · obtain ⟨u, hz, hw⟩ := h
    exact Or.inl ((connectedComponentIn_eq hz).trans (connectedComponentIn_eq hw).symm)
  · exact Or.inr (disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 h))

/-- **The complement of a complementary component of a continuum is connected**: it is `C`
together with the closures of the other components, each of which meets `C`. -/
theorem isPreconnected_compl_connectedComponentIn (hCc : IsClosed C) (hC : IsConnected C)
    (z : ℂ) : IsPreconnected (connectedComponentIn Cᶜ z)ᶜ := by
  obtain ⟨x, hx⟩ := hC.nonempty
  have hCR : C ⊆ (connectedComponentIn Cᶜ z)ᶜ := fun c hc hcR =>
    connectedComponentIn_subset _ _ hcR hc
  refine isPreconnected_of_forall x fun y hy => ?_
  by_cases hyC : y ∈ C
  · exact ⟨C, hCR, hx, hyC, hC.isPreconnected⟩
  set R' := connectedComponentIn Cᶜ y
  have hR'o : IsOpen R' := hCc.isOpen_compl.connectedComponentIn
  have hdisj : Disjoint R' (connectedComponentIn Cᶜ z) := by
    rcases connectedComponentIn_eq_or_disjoint (F := Cᶜ) y z with h | h
    · exact absurd (h ▸ mem_connectedComponentIn (show y ∈ Cᶜ from hyC)) hy
    · exact h
  have hcl : closure R' ⊆ (connectedComponentIn Cᶜ z)ᶜ := fun w hw hwR =>
    Set.disjoint_left.1 (hdisj.closure_left hCc.isOpen_compl.connectedComponentIn) hw hwR
  -- `closure R'` meets `C`: `R'` is a nonempty proper open subset of `ℂ`
  have hfr : (frontier R').Nonempty := by
    refine nonempty_frontier_iff.2 ⟨⟨y, mem_connectedComponentIn (show y ∈ Cᶜ from hyC)⟩, ?_⟩
    intro h
    have := connectedComponentIn_subset Cᶜ y (h ▸ mem_univ x)
    exact this hx
  obtain ⟨c, hc⟩ := hfr
  have hcC : c ∈ C := by
    have := frontier_connectedComponentIn_subset_compl hCc.isOpen_compl y hc
    simpa using this
  refine ⟨C ∪ closure R', union_subset hCR hcl, Or.inl hx,
    Or.inr (subset_closure (mem_connectedComponentIn (show y ∈ Cᶜ from hyC))), ?_⟩
  exact hC.isPreconnected.union c hcC (frontier_subset_closure hc)
    isPreconnected_connectedComponentIn.closure

end Components

/-! ### Removing an interior point -/

/-- A punctured disc is connected (polar coordinates). -/
theorem isPreconnected_ball_diff_singleton (a : ℂ) (r : ℝ) : IsPreconnected (ball a r \ {a}) := by
  have h : ball a r \ {a} =
      (fun p : ℝ × ℝ => a + (p.1 : ℂ) * exp (p.2 * I)) '' (Ioo 0 r ×ˢ univ) := by
    ext w
    constructor
    · rintro ⟨hw, hwa⟩
      refine ⟨(‖w - a‖, arg (w - a)), ⟨⟨norm_pos_iff.2 (sub_ne_zero.2 hwa), ?_⟩, mem_univ _⟩, ?_⟩
      · rw [mem_ball, dist_eq_norm] at hw; exact hw
      · show a + (‖w - a‖ : ℂ) * exp (arg (w - a) * I) = w
        rw [norm_mul_exp_arg_mul_I]; ring
    · rintro ⟨⟨s, θ⟩, ⟨hs, -⟩, rfl⟩
      have hn : ‖(s : ℂ) * exp (θ * I)‖ = s := by
        rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, Real.norm_eq_abs,
          abs_of_pos hs.1]
      refine ⟨?_, fun h => ?_⟩
      · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hn]; exact hs.2
      · have h0 : (s : ℂ) * exp (θ * I) = 0 := by
          have := mem_singleton_iff.1 h
          simpa using this
        have := congrArg norm h0
        rw [hn, norm_zero] at this
        exact hs.1.ne' this
  rw [h]
  exact (isPreconnected_Ioo.prod isPreconnected_univ).image _
    (Continuous.continuousOn (by fun_prop))

/-- Removing an interior point from a connected planar set keeps it connected. -/
theorem isPreconnected_diff_singleton_of_ball_subset {S : Set ℂ} (hS : IsPreconnected S) {a : ℂ}
    {r : ℝ} (hr : 0 < r) (hball : ball a r ⊆ S) : IsPreconnected (S \ {a}) := by
  set P := ball a r \ {a} with hPdef
  have hP := isPreconnected_ball_diff_singleton a r
  have hPS : P ⊆ S \ {a} := fun w hw => ⟨hball hw.1, hw.2⟩
  -- points of `P` near `a`
  have hnear : ∀ δ > 0, ∃ p ∈ P, p ∈ ball a δ := fun δ hδ => by
    refine ⟨a + ((min δ r / 2 : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith [min_le_right δ r]
    · rw [mem_singleton_iff, add_eq_left, ofReal_eq_zero]; positivity
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith [min_le_left δ r]
  -- the case `P ⊆ u`
  have key : ∀ u v : Set ℂ, IsOpen u → IsOpen v → S \ {a} ⊆ u ∪ v → ((S \ {a}) ∩ v).Nonempty →
      (S \ {a}) ∩ (u ∩ v) = ∅ → P ⊆ u → False := by
    intro u v hu hv hsuv ⟨y, hyS, hyv⟩ hempty hPu
    obtain ⟨p, hpP, -⟩ := hnear r hr
    have hcov : S ⊆ (u ∪ ball a r) ∪ v := by
      intro w hw
      by_cases hwa : w = a
      · exact Or.inl (Or.inr (hwa ▸ mem_ball_self hr))
      · rcases hsuv ⟨hw, hwa⟩ with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
    obtain ⟨z, hzS, hzu, hzv⟩ := hS _ _ (hu.union isOpen_ball) hv hcov
      ⟨p, (hPS hpP).1, Or.inl (hPu hpP)⟩ ⟨y, hyS.1, hyv⟩
    by_cases hza : z = a
    · subst hza
      obtain ⟨δ, hδ, hδv⟩ := Metric.isOpen_iff.1 hv z hzv
      obtain ⟨q, hqP, hqδ⟩ := hnear δ hδ
      exact (Set.eq_empty_iff_forall_notMem.1 hempty) q ⟨hPS hqP, hPu hqP, hδv hqδ⟩
    · have hzu' : z ∈ u := by
        rcases hzu with h | h
        · exact h
        · exact hPu ⟨h, hza⟩
      exact (Set.eq_empty_iff_forall_notMem.1 hempty) z ⟨⟨hzS, hza⟩, hzu', hzv⟩
  intro u v hu hv hsuv hu' hv'
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hPuv : P ⊆ u ∪ v := hPS.trans hsuv
  by_cases hPu : (P ∩ u).Nonempty
  · by_cases hPv : (P ∩ v).Nonempty
    · obtain ⟨w, hwP, hw⟩ := hP u v hu hv hPuv hPu hPv
      exact (Set.eq_empty_iff_forall_notMem.1 hne) w ⟨hPS hwP, hw⟩
    · refine key u v hu hv hsuv hv' hne fun w hw => ?_
      rcases hPuv hw with h | h
      · exact h
      · exact absurd ⟨w, hw, h⟩ hPv
  · refine key v u hv hu (by rw [union_comm]; exact hsuv) hu' (by rw [inter_comm v u]; exact hne)
      fun w hw => ?_
    rcases hPuv hw with h | h
    · exact absurd ⟨w, hw, h⟩ hPu
    · exact h

/-! ### Uniform local connectedness after cutting out a disc -/

/-- Closed discs are uniformly locally connected (they are convex). -/
theorem ulc_closedBall (c : ℂ) (r : ℝ) : ULC (closedBall c r) := by
  intro ε hε
  refine ⟨ε / 2, half_pos hε, fun a ha b hb hab => ⟨segment ℝ a b,
    (convex_closedBall c r).segment_subset ha hb, (convex_segment a b).isPreconnected,
    left_mem_segment ℝ a b, right_mem_segment ℝ a b, ?_⟩⟩
  have hsub : segment ℝ a b ⊆ closedBall a (dist a b) :=
    (convex_closedBall a (dist a b)).segment_subset (mem_closedBall_self dist_nonneg)
      (by rw [mem_closedBall, dist_comm])
  calc diam (segment ℝ a b) ≤ diam (closedBall a (dist a b)) := diam_mono hsub isBounded_closedBall
    _ ≤ 2 * dist a b := diam_closedBall dist_nonneg
    _ ≤ ε := by linarith

/-- **Cutting out a disc.** If a compact uniformly locally connected `C'` contains the closed disc
`B̄(a, 2ε)`, then `C' \ B(a, ε)` is still uniformly locally connected: small connected sets of `C'`
near `C' \ B(a, ε)` are pushed out of `B(a, ε)` by the radial retraction onto `{‖w - a‖ ≥ ε}`. -/
theorem ulc_diff_ball {C' : Set ℂ} (hC : IsCompact C') (hCu : ULC C') {a : ℂ} {ε : ℝ}
    (hε : 0 < ε) (hball : closedBall a (2 * ε) ⊆ C') : ULC (C' \ ball a ε) := by
  set ρ : ℂ → ℂ := fun w => a + ((max ‖w - a‖ ε / ‖w - a‖ : ℝ) : ℂ) * (w - a) with hρ
  have hρfix : ∀ w, ε ≤ ‖w - a‖ → ρ w = w := by
    intro w hw
    have hpos : 0 < ‖w - a‖ := hε.trans_le hw
    simp only [hρ, max_eq_left hw, div_self hpos.ne', ofReal_one, one_mul]
    ring
  have hρnorm : ∀ w, w ≠ a → ‖ρ w - a‖ = max ‖w - a‖ ε := by
    intro w hw
    have hpos : 0 < ‖w - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hw)
    simp only [hρ, add_sub_cancel_left, norm_mul, norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (div_nonneg (le_max_of_le_right hε.le) hpos.le), div_mul_cancel₀ _ hpos.ne']
  have hρmem : ∀ w ∈ C', w ≠ a → ρ w ∈ C' \ ball a ε := by
    intro w hw hwa
    refine ⟨?_, ?_⟩
    · by_cases h : ε ≤ ‖w - a‖
      · rw [hρfix w h]; exact hw
      · apply hball
        rw [mem_closedBall, dist_eq_norm, hρnorm w hwa, max_eq_right (not_le.1 h).le]
        linarith
    · rw [mem_ball, dist_eq_norm, hρnorm w hwa, not_lt]
      exact le_max_right _ _
  have hcn : Continuous fun w : ℂ => ‖w - a‖ :=
    continuous_norm.comp (continuous_id.sub continuous_const)
  set K₂ := C' ∩ {w : ℂ | ε / 2 ≤ ‖w - a‖} with hK₂def
  have hK₂ : IsCompact K₂ := hC.inter_right (isClosed_le continuous_const hcn)
  have hρc : ContinuousOn ρ K₂ := by
    have hne : ∀ w ∈ K₂, ‖w - a‖ ≠ 0 := fun w hw => (lt_of_lt_of_le (half_pos hε) hw.2).ne'
    refine continuousOn_const.add (ContinuousOn.mul ?_ (continuousOn_id.sub continuousOn_const))
    exact Complex.continuous_ofReal.comp_continuousOn
      (((hcn.max continuous_const).continuousOn).div hcn.continuousOn hne)
  intro ε' hε'
  obtain ⟨η, hη, hηu⟩ := Metric.uniformContinuousOn_iff.1
    (hK₂.uniformContinuousOn_of_continuous hρc) (ε' / 2) (half_pos hε')
  obtain ⟨δ, hδ, hu⟩ := hCu (min (η / 2) (ε / 4)) (by positivity)
  refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
  obtain ⟨β, hβC, hβc, hxβ, hyβ, hβd⟩ := hu x hx.1 y hy.1 hxy
  have hβb : Bornology.IsBounded β := hC.isBounded.subset hβC
  have hout : ∀ w ∈ C' \ ball a ε, ε ≤ ‖w - a‖ := fun w hw => by
    have := hw.2; rwa [mem_ball, dist_eq_norm, not_lt] at this
  have hβK : β ⊆ K₂ := by
    intro b hb
    refine ⟨hβC hb, show ε / 2 ≤ ‖b - a‖ from ?_⟩
    have h1 := dist_le_diam_of_mem hβb hb hxβ
    have h2 : ‖x - a‖ ≤ dist b x + ‖b - a‖ := by
      rw [dist_comm, dist_eq_norm]; exact norm_sub_le_norm_sub_add_norm_sub x b a
    linarith [min_le_right (η / 2) (ε / 4), hout x hx]
  refine ⟨ρ '' β, ?_, hβc.image _ (hρc.mono hβK), ⟨x, hxβ, hρfix x (hout x hx)⟩,
    ⟨y, hyβ, hρfix y (hout y hy)⟩, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    refine hρmem b (hβC hb) fun hba => ?_
    have : ε / 2 ≤ ‖b - a‖ := (hβK hb).2
    rw [hba, sub_self, norm_zero] at this
    linarith
  · refine Metric.diam_le_of_forall_dist_le hε'.le ?_
    rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩
    have h1 := dist_le_diam_of_mem hβb hb hb'
    have h2 := hηu b (hβK hb) b' (hβK hb') (by linarith [min_le_left (η / 2) (ε / 4)])
    linarith

/-! ### Unbounded components: inversion -/

/-- **Inversion step.** Let `R` be an open connected set containing a neighbourhood of `∞`, with
`ℂ \ R` connected, whose frontier lies in a compact uniformly locally connected `C₁` disjoint from
`R`, and let `a ∉ C₁` with `B(a, r) ∩ R = ∅`. Then `∂R` is a locally connected continuum: under
`w ↦ 1/(w - a)`, `R ∪ {∞}` becomes a bounded simply connected domain enclosed by the image of
`C₁`. -/
theorem frontier_isLocallyConnectedContinuum_of_inversion {R C₁ : Set ℂ} (hRo : IsOpen R)
    (hRc : IsConnected R) {ρ₀ : ℝ} (hRout : {w : ℂ | ρ₀ < ‖w‖} ⊆ R) (hRcc : IsPreconnected Rᶜ)
    (hC₁ : IsCompact C₁) (hC₁u : ULC C₁) (hfr : frontier R ⊆ C₁) (hdisj : Disjoint C₁ R)
    {a : ℂ} {r : ℝ} (hr : 0 < r) (hRa : ∀ w ∈ R, r ≤ ‖w - a‖) (haC : a ∉ C₁) :
    IsCompact (frontier R) ∧ IsConnected (frontier R) ∧ LocallyConnectedSpace (frontier R) := by
  set M : ℂ → ℂ := fun w => (w - a)⁻¹ with hM
  set N : ℂ → ℂ := fun u => a + u⁻¹ with hN
  have hMN : ∀ u, M (N u) = u := fun u => by simp [hM, hN]
  have hNM : ∀ w, w ≠ a → N (M w) = w := fun w _ => by simp [hM, hN]
  have hNc : ContinuousOn N {u | u ≠ 0} := fun u hu =>
    (continuousAt_const.add (continuousAt_inv₀ hu)).continuousWithinAt
  have hMc : ContinuousOn M {w | w ≠ a} := fun w hw =>
    ((continuous_id.sub continuous_const).continuousAt.inv₀
      (sub_ne_zero.2 hw)).continuousWithinAt
  have haR : a ∉ R := fun h => by have := hRa a h; rw [sub_self, norm_zero] at this; linarith
  have hN0 : N 0 = a := by simp [hN]
  -- a punctured disc about `0` lies in `N ⁻¹' R`
  set δ₀ : ℝ := 1 / (|ρ₀| + ‖a‖ + 1) with hδ₀
  have hδ₀pos : 0 < δ₀ := by positivity
  have hsmall : ∀ u : ℂ, u ≠ 0 → ‖u‖ ≤ δ₀ → N u ∈ R := by
    intro u hu hud
    apply hRout
    have hupos : 0 < ‖u‖ := norm_pos_iff.2 hu
    have h1 : |ρ₀| + ‖a‖ + 1 ≤ ‖u⁻¹‖ := by
      rw [norm_inv, le_inv_comm₀ (by positivity) hupos]
      rw [hδ₀, one_div] at hud; exact hud
    have h2 : ‖u⁻¹‖ - ‖a‖ ≤ ‖a + u⁻¹‖ := by
      have := norm_sub_norm_le u⁻¹ (-a)
      rw [sub_neg_eq_add, norm_neg, add_comm] at this
      exact this
    show ρ₀ < ‖a + u⁻¹‖
    linarith [le_abs_self ρ₀]
  set D : Set ℂ := ball 0 δ₀ ∪ N ⁻¹' R with hD
  have hND : ∀ u, N u ∈ R → u ≠ 0 := fun u hu h0 => haR (by rw [h0, hN0] at hu; exact hu)
  have hpre : N ⁻¹' R = M '' R := by
    ext u
    constructor
    · intro hu; exact ⟨N u, hu, hMN u⟩
    · rintro ⟨w, hw, rfl⟩
      show N (M w) ∈ R
      rw [hNM w (fun h => haR (h ▸ hw))]; exact hw
  have hmemD : ∀ u, u ≠ 0 → (u ∈ D ↔ N u ∈ R) := by
    intro u hu
    constructor
    · rintro (h | h)
      · exact hsmall u hu (mem_ball_zero_iff.1 h).le
      · exact h
    · exact fun h => Or.inr h
  -- `D` is open, connected, bounded
  have hpreo : IsOpen (N ⁻¹' R) := by
    have := hNc.isOpen_inter_preimage isOpen_ne hRo
    have h' : {u : ℂ | u ≠ 0} ∩ N ⁻¹' R = N ⁻¹' R := inter_eq_right.2 fun u hu => hND u hu
    rwa [h'] at this
  have hDo : IsOpen D := isOpen_ball.union hpreo
  have hDc : IsConnected D := by
    refine ⟨⟨0, Or.inl (mem_ball_self hδ₀pos)⟩, ?_⟩
    set K : ℝ := |ρ₀| + ‖a‖ + 1 / δ₀ + 1 with hK
    obtain ⟨w, hw⟩ : ∃ w : ℂ, K ≤ ‖w‖ :=
      ⟨(K : ℂ), by rw [norm_real, Real.norm_eq_abs]; exact le_abs_self K⟩
    have hwR : w ∈ R := hRout (show ρ₀ < ‖w‖ by
      linarith [le_abs_self ρ₀, norm_nonneg a, one_div_pos.2 hδ₀pos])
    have hwa : w ≠ a := fun h => haR (h ▸ hwR)
    have hMw : M w ∈ ball (0 : ℂ) δ₀ := by
      rw [mem_ball_zero_iff, hM]
      show ‖(w - a)⁻¹‖ < δ₀
      have h1 : ‖w‖ - ‖a‖ ≤ ‖w - a‖ := norm_sub_norm_le w a
      have h2 : 1 / δ₀ < ‖w - a‖ := by linarith [abs_nonneg ρ₀]
      rw [norm_inv]
      calc ‖w - a‖⁻¹ < (1 / δ₀)⁻¹ := inv_strictAnti₀ (by positivity) h2
        _ = δ₀ := by rw [one_div, inv_inv]
    refine (isPreconnected_ball).union (M w) hMw ?_ ?_
    · exact show N (M w) ∈ R by rw [hNM w hwa]; exact hwR
    · rw [hpre]
      exact hRc.isPreconnected.image _ (hMc.mono fun w hw h => haR (h ▸ hw))
  have hDb : Bornology.IsBounded D := by
    refine (isBounded_ball.union (isBounded_closedBall (x := (0 : ℂ)) (r := 1 / r))).subset
      (union_subset_union_right _ fun u hu => ?_)
    have hu0 := hND u hu
    have h1 := hRa _ hu
    rw [mem_closedBall_zero_iff, ← hMN u, hM]
    simp only [hN, add_sub_cancel_left, inv_inv, norm_inv] at h1 ⊢
    rw [le_div_iff₀ hr]
    calc ‖u‖ * r ≤ ‖u‖ * ‖u‖⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ (norm_ne_zero_iff.2 hu0)
  -- the enclosing set `E = M(C₁)`
  have haC' : ∀ c ∈ C₁, c ≠ a := fun c hc h => haC (h ▸ hc)
  have hMC : ContinuousOn M C₁ := hMc.mono fun c hc => haC' c hc
  have hE : IsCompact (M '' C₁) := hC₁.image_of_continuousOn hMC
  have hM0 : ∀ w, w ≠ a → M w ≠ 0 := fun w hw => inv_ne_zero (sub_ne_zero.2 hw)
  have hEu : ULC (M '' C₁) := ulc_image_of_leftInvOn hC₁ hMC
    (hNc.mono (by rintro _ ⟨c, hc, rfl⟩; exact hM0 c (haC' c hc)))
    (fun c hc => hNM c (haC' c hc)) hC₁u
  have hMD : ∀ w, w ≠ a → (M w ∈ D ↔ w ∈ R) := fun w hw => by
    rw [hmemD _ (hM0 w hw), hNM w hw]
  have hED : Disjoint (M '' C₁) D := by
    rw [Set.disjoint_left]
    rintro _ ⟨c, hc, rfl⟩ hcD
    exact Set.disjoint_left.1 hdisj hc ((hMD c (haC' c hc)).1 hcD)
  have h0D : (0 : ℂ) ∈ D := Or.inl (mem_ball_self hδ₀pos)
  -- frontier correspondence
  have hfrD : ∀ v ∈ frontier D, v ≠ 0 ∧ N v ∈ frontier R := by
    intro v hv
    rw [hDo.frontier_eq] at hv
    have hv0 : v ≠ 0 := fun h => hv.2 (h ▸ h0D)
    refine ⟨hv0, ?_⟩
    rw [hRo.frontier_eq]
    refine ⟨?_, fun h => hv.2 ((hmemD v hv0).2 h)⟩
    rw [mem_closure_iff_nhds]
    intro t ht
    have hNt : N ⁻¹' t ∩ {u | u ≠ 0} ∈ 𝓝 v :=
      inter_mem (((hNc v hv0).continuousAt (isOpen_ne.mem_nhds hv0)).preimage_mem_nhds ht)
        (isOpen_ne.mem_nhds hv0)
    obtain ⟨u, ⟨hut, hu0⟩, huD⟩ := mem_closure_iff_nhds.1 hv.1 _ hNt
    exact ⟨N u, hut, (hmemD u hu0).1 huD⟩
  have hfrDE : frontier D ⊆ M '' C₁ := fun v hv => ⟨N v, hfr (hfrD v hv).2, hMN v⟩
  -- `D` is simply connected: its complement `M(Rᶜ \ {a})` is connected and unbounded
  have hDcompl : Dᶜ = M '' (Rᶜ \ {a}) := by
    ext u
    constructor
    · intro hu
      have hu0 : u ≠ 0 := fun h => hu (h ▸ h0D)
      refine ⟨N u, ⟨fun h => hu ((hmemD u hu0).2 h), fun h => hu0 ?_⟩, hMN u⟩
      rw [← hMN u, mem_singleton_iff.1 h]
      simp [hM]
    · rintro ⟨w, ⟨hwR, hwa⟩, rfl⟩ hD
      exact hwR ((hMD w hwa).1 hD)
  have hball_a : ball a r ⊆ Rᶜ := fun w hw hwR => by
    have := hRa w hwR
    rw [mem_ball, dist_eq_norm] at hw
    linarith
  have hDcpc : IsPreconnected Dᶜ := by
    rw [hDcompl]
    exact (isPreconnected_diff_singleton_of_ball_subset hRcc hr hball_a).image _
      (hMc.mono fun w hw => hw.2)
  have hDcub : ¬ Bornology.IsBounded Dᶜ := by
    intro hb
    obtain ⟨K, hK⟩ := hb.subset_closedBall 0
    set t : ℝ := min (r / 2) (1 / (|K| + 1)) with ht_def
    have ht : 0 < t := by positivity
    have hmem : M (a + t) ∈ Dᶜ := by
      rw [hDcompl]
      refine ⟨a + t, ⟨hball_a ?_, ?_⟩, rfl⟩
      · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_real, Real.norm_eq_abs,
          abs_of_pos ht]
        linarith [min_le_left (r / 2) (1 / (|K| + 1))]
      · rw [mem_singleton_iff, add_eq_left, ofReal_eq_zero]; exact ht.ne'
    have h1 := mem_closedBall_zero_iff.1 (hK hmem)
    simp only [hM, add_sub_cancel_left, norm_inv, norm_real, Real.norm_eq_abs,
      abs_of_pos ht] at h1
    have h2 : |K| + 1 ≤ t⁻¹ := by
      rw [le_inv_comm₀ (by positivity) ht, ← one_div]
      exact min_le_right _ _
    linarith [le_abs_self K]
  have hsc : IsSimplyConnected D := isSimplyConnected_of_forall_not_isBounded hDo hDc
    fun b hb => by rw [hDcpc.connectedComponentIn hb]; exact hDcub
  obtain ⟨hfc, hfconn, hflc⟩ := frontier_isLocallyConnectedContinuum_of_ulc hDo hDc hDb hsc
    hE.isClosed hE.isBounded hEu hfrDE hED
  -- transfer back along `N`
  have hfrR : frontier R = N '' frontier D := by
    apply Subset.antisymm
    · intro w hw
      have hwa : w ≠ a := fun h => haC (h ▸ hfr hw)
      refine ⟨M w, ?_, hNM w hwa⟩
      rw [hDo.frontier_eq]
      rw [hRo.frontier_eq] at hw
      refine ⟨?_, fun h => hw.2 ((hMD w hwa).1 h)⟩
      have := mem_closure_image ((hMc w hwa).continuousAt (isOpen_ne.mem_nhds hwa)) hw.1
      exact closure_mono (by rw [← hpre]; exact subset_union_right) this
    · rintro _ ⟨v, hv, rfl⟩
      exact (hfrD v hv).2
  have hNfc : ContinuousOn N (frontier D) := hNc.mono fun v hv => (hfrD v hv).1
  rw [hfrR]
  refine ⟨hfc.image_of_continuousOn hNfc, hfconn.image _ hNfc, ?_⟩
  have : CompactSpace (frontier D) := isCompact_iff_compactSpace.1 hfc
  have hcont : Continuous (fun v : frontier D => N v) := hNfc.domRestrict
  have := locallyConnectedSpace_range hcont
  exact (Homeomorph.setCongr (image_eq_range N (frontier D))).locallyConnectedSpace

/-! ### Torhorst's theorem -/

/-- **Torhorst's theorem** ([LT06] Proposition 3.3, first assertion; Kuratowski, *Topology* II,
§61 II Thm 4): the frontier of a complementary component of a locally connected continuum
`C ⊆ ℂ` is a locally connected continuum. (The sphere version reduces to this one by a rotation of
the sphere; see the module docstring.) -/
theorem isLocallyConnected_frontier_of_peano {C : Set ℂ} (hCc : IsCompact C) (hC : IsConnected C)
    (hClc : LocallyConnectedSpace C) {z : ℂ} (hz : z ∉ C) :
    IsCompact (frontier (connectedComponentIn Cᶜ z)) ∧
      IsConnected (frontier (connectedComponentIn Cᶜ z)) ∧
      LocallyConnectedSpace (frontier (connectedComponentIn Cᶜ z)) := by
  set R := connectedComponentIn Cᶜ z with hRdef
  have hRo : IsOpen R := hCc.isClosed.isOpen_compl.connectedComponentIn
  have hRc : IsConnected R := isConnected_connectedComponentIn_iff.2 hz
  have hfr : frontier R ⊆ C := fun w hw => by
    simpa using frontier_connectedComponentIn_subset_compl hCc.isClosed.isOpen_compl z hw
  have hdisj : Disjoint C R :=
    Set.disjoint_left.2 fun c hc hcR => connectedComponentIn_subset _ _ hcR hc
  have hRcc : IsPreconnected Rᶜ := isPreconnected_compl_connectedComponentIn hCc.isClosed hC z
  have hCu : ULC C := ulc_of_locallyConnectedSpace hCc
  by_cases hRb : Bornology.IsBounded R
  · -- bounded component: `R` itself, enclosed by `C`
    have hRcub : ¬ Bornology.IsBounded Rᶜ := fun h =>
      NormedSpace.unbounded_univ ℝ ℂ (by rw [← union_compl_self R]; exact hRb.union h)
    have hsc : IsSimplyConnected R := isSimplyConnected_of_forall_not_isBounded hRo hRc
      fun b hb => by rw [hRcc.connectedComponentIn hb]; exact hRcub
    exact frontier_isLocallyConnectedContinuum_of_ulc hRo hRc hRb hsc hCc.isClosed hCc.isBounded
      hCu hfr hdisj
  -- unbounded component
  by_cases hall : C ⊆ frontier R
  · rw [subset_antisymm hfr hall]
    exact ⟨hCc, hC, hClc⟩
  obtain ⟨a, haC, haf⟩ := not_subset.1 hall
  have haR : a ∉ closure R := fun h =>
    haf ⟨h, fun hi => Set.disjoint_left.1 hdisj haC (interior_subset hi)⟩
  obtain ⟨r, hr, hrb⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl a haR
  set ε := r / 3 with hε
  have hεpos : 0 < ε := by positivity
  have hcb : closedBall a (2 * ε) ⊆ (closure R)ᶜ :=
    (closedBall_subset_ball (by linarith)).trans hrb
  set C' := C ∪ closedBall a (2 * ε) with hC'
  have hC'c : IsCompact C' := hCc.union (isCompact_closedBall _ _)
  have hC'u : ULC C' := QuantumZipper.CA.Topo.ULC.union_of_isCompact_of_isClosed hCc
    isClosed_closedBall hCu (ulc_closedBall _ _)
  have hC₁u : ULC (C' \ ball a ε) := ulc_diff_ball hC'c hC'u hεpos subset_union_right
  have hfr₁ : frontier R ⊆ C' \ ball a ε := fun w hw =>
    ⟨Or.inl (hfr hw), fun hwb => hrb (ball_subset_ball (by linarith) hwb)
      (frontier_subset_closure hw)⟩
  have hdisj₁ : Disjoint (C' \ ball a ε) R := by
    refine Set.disjoint_left.2 fun w hw hwR => ?_
    rcases hw.1 with h | h
    · exact Set.disjoint_left.1 hdisj h hwR
    · exact hcb h (subset_closure hwR)
  have haC₁ : a ∉ C' \ ball a ε := fun h => h.2 (mem_ball_self hεpos)
  have hRa : ∀ w ∈ R, r ≤ ‖w - a‖ := fun w hw => by
    by_contra h
    exact hrb (by rw [mem_ball, dist_eq_norm]; exact not_le.1 h) (subset_closure hw)
  -- `R` contains a neighbourhood of `∞`
  obtain ⟨ρ₀, hρ₀⟩ := hCc.isBounded.subset_ball 0
  have hRout : {w : ℂ | ρ₀ < ‖w‖} ⊆ R := by
    obtain ⟨w, hwR, hw⟩ : ∃ w ∈ R, ρ₀ < ‖w‖ := by
      by_contra h
      push Not at h
      exact hRb ((isBounded_closedBall (x := (0 : ℂ)) (r := ρ₀)).subset fun w hw =>
        mem_closedBall_zero_iff.2 (h w hw))
    have hsub := QuantumZipper.CA.Topo.subset_connectedComponentIn_compl_of_unbounded hρ₀
      (QuantumZipper.CA.Topo.isPreconnected_setOf_lt_norm ρ₀) ?_ ?_ hw
    · rwa [← connectedComponentIn_eq hwR] at hsub
    · intro hb
      obtain ⟨K, hK⟩ := hb.subset_closedBall 0
      have hmem : ((|K| + |ρ₀| + 1 : ℝ) : ℂ) ∈ {w : ℂ | ρ₀ < ‖w‖} := by
        show ρ₀ < ‖((|K| + |ρ₀| + 1 : ℝ) : ℂ)‖
        rw [norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        linarith [le_abs_self ρ₀, abs_nonneg K]
      have := mem_closedBall_zero_iff.1 (hK hmem)
      rw [norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at this
      linarith [le_abs_self K, abs_nonneg ρ₀]
    · exact Set.disjoint_left.2 fun w hw hwC => by
        have := mem_ball_zero_iff.1 (hρ₀ hwC)
        exact lt_asymm this hw
  exact frontier_isLocallyConnectedContinuum_of_inversion hRo hRc hRout hRcc
    (hC'c.diff isOpen_ball) hC₁u hfr₁ hdisj₁ hr hRa haC₁

end InteractingSLE
