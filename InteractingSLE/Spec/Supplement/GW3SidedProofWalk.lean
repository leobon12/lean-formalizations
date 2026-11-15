/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW3SidedProof
import InteractingSLE.Spec.Supplement.GW4R51
import InteractingSLE.Spec.Supplement.SB4ProofFrontier

/-!
# Lemma GW3's geometry for the boundary walks, R51 form

Packet PROVE-T14-GW8. The R51 form of Lemma GW3's between-region geometry (`GW3Sided.GW3GeometryRegStatement`: every
component between the walks is a two-arc Jordan component or has an oriented uniformizer) from the deterministic
`GW3SidedProof.hasOrientedUniformizer_of_touching`, whose hypotheses are supplied by:

* both walks proper curves from `0` (`WalkCont.RightWalkProperRegStatement`, its mirror `LeftWalkProperRegStatement`;
  Lemma GW1, p. 618: "There is a field-determined continuous injective proper curve `R` from `x` to `y`", "Reflection
  gives the left boundary walk `L`");
* the closed-side order `R ∩ leftSideOf L = ∅`: GW2a's containment of `R` in the completed counterflow range and SB's
  frontier statement (the range misses the left side of `L`; Theorem GW4, proof, p. 637: "GW1 puts both walks in that
  range");
* every negative real point of `R` lies on `L` (`neg_real_mem_of_frontier`): near a negative real point off `L`, the
  half-disc above it lies on the left of `L`, so it misses the counterflow range and hence `R`; then `R` runs along a
  negative real interval, which the walk cover excludes (real connectors of `R` are rightward, and an ordinary piece
  contains no real interval: `WalkCont.WalkPieceContinuumRegStatement`, Theorem GW4, proof, p. 637).

The last section wires the version-2 component-kernel anchor from these inputs, the union law and GW4's traversal core
(`componentKernels_of_walkInputs`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar isOpen_H)

universe u

namespace InteractingSLE.Theorem14.GW3SidedProof

/-! ### The negative real points of the right wall -/

/-- **A negative real point of `R` lies on `L`**, if `R` is a proper curve from `0` inside a set `K` that misses the
left side of the closed set `L`, and `R` contains no nondegenerate preconnected set of negative reals. -/
theorem neg_real_mem_of_frontier {γ : ℝ≥0 → ℂ} (hγ : Supp9B.IsProperCurve γ) {K L : Set ℂ}
    (hLc : IsClosed L) (hRK : range γ ⊆ K) (hKL : K ∩ leftSideOf L = ∅)
    (hN : ∀ S ⊆ range γ ∩ ((↑) : ℝ → ℂ) '' Iio 0, IsPreconnected S → S.Subsingleton) :
    ∀ x : ℝ, x < 0 → (x : ℂ) ∈ range γ → (x : ℂ) ∈ L := by
  intro x hx ⟨t₀, ht₀⟩
  by_contra hxL
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hLc.isOpen_compl (x : ℂ) hxL
  set r' := min r (-x) with hr'
  have hr'0 : 0 < r' := lt_min hr (neg_pos.2 hx)
  -- the half-disc above `x` lies on the left of `L`
  set B := ball (x : ℂ) r' ∩ H with hB
  have hBc : IsPreconnected B :=
    ((convex_ball (x : ℂ) r').inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hBL : ∀ b ∈ B, b ∉ L := fun b hb hbL => hball (ball_subset_ball (min_le_left _ _) hb.1) hbL
  have hxB : (x : ℂ) ∈ closure B := by
    have ht : Tendsto (fun s : ℝ => (x : ℂ) + (s : ℂ) * Complex.I) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
      have : Continuous (fun s : ℝ => (x : ℂ) + (s : ℂ) * Complex.I) := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT hr'0] with s hs
    refine ⟨?_, show (0 : ℝ) < ((x : ℂ) + (s : ℂ) * Complex.I).im by simpa using hs.1⟩
    rw [mem_ball, dist_eq_norm]
    simpa [abs_of_pos hs.1] using hs.2
  have hBleft : B ⊆ leftSideOf L := by
    intro b hb
    have hsub : B ⊆ connectedComponentIn (H \ L) b :=
      hBc.subset_connectedComponentIn hb fun v hv => ⟨hv.2, hBL v hv⟩
    exact ⟨⟨hb.2, hBL b hb⟩, x, hx, hxL, closure_mono hsub hxB⟩
  have hBK : ∀ z ∈ K, z ∉ B := fun z hz hzB => (Set.eq_empty_iff_forall_notMem.1 hKL) z ⟨hz, hBleft hzB⟩
  -- near `t₀` the curve stays on the negative real axis
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuous_iff.1 hγ.1 t₀ r' hr'0
  have hreal : ∀ t, dist t t₀ < δ → γ t ∈ ((↑) : ℝ → ℂ) '' Iio 0 := by
    intro t ht
    have hd : dist (γ t) (x : ℂ) < r' := ht₀ ▸ hcont t ht
    have hnotB : γ t ∉ B := hBK _ (hRK ⟨t, rfl⟩)
    have him : (γ t).im = 0 := by
      have h1 : 0 ≤ (γ t).im := hγ.2.2.1 t
      rcases h1.lt_or_eq with h2 | h2
      · exact absurd ⟨hd, h2⟩ hnotB
      · exact h2.symm
    have hre : (γ t).re < 0 := by
      have h3 : |(γ t).re - x| < r' := by
        have := Complex.abs_re_le_norm (γ t - x)
        rw [dist_eq_norm] at hd
        simp only [Complex.sub_re, Complex.ofReal_re] at this
        linarith
      have h4 : r' ≤ -x := min_le_right _ _
      have := (abs_lt.1 h3).2
      linarith
    exact ⟨(γ t).re, hre, Complex.ext (by simp) (by simp [him])⟩
  have hδ' : (0 : ℝ) ≤ δ / 2 := by positivity
  set t₁ : ℝ≥0 := t₀ + ⟨δ / 2, hδ'⟩ with ht₁
  have hsub : γ '' Icc t₀ t₁ ⊆ range γ ∩ ((↑) : ℝ → ℂ) '' Iio 0 := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨⟨t, rfl⟩, hreal t ?_⟩
    rw [NNReal.dist_eq]
    have h1 : (t₀ : ℝ) ≤ t := ht.1
    have h2 : (t : ℝ) ≤ t₁ := ht.2
    have h3 : (t₁ : ℝ) = t₀ + δ / 2 := rfl
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hS := hN _ hsub (isPreconnected_Icc.image _ hγ.1.continuousOn)
  have hlt : t₀ < t₁ := by
    rw [ht₁]
    exact lt_add_of_pos_right _ (show (0 : ℝ≥0) < ⟨δ / 2, hδ'⟩ from by
      change (0 : ℝ) < δ / 2
      positivity)
  have := hS (mem_image_of_mem γ ⟨le_rfl, hlt.le⟩) (mem_image_of_mem γ ⟨hlt.le, le_rfl⟩)
  exact hlt.ne (hγ.2.1 this)


/-- **The right walk contains no nondegenerate preconnected set of negative reals**, pointwise: its cover by the root,
its pieces and its real connectors (`WalkCont.walkCover`), the connectors in `[0, ∞)`, no piece containing a
nondegenerate real continuum. -/
theorem neg_real_subsingleton {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {spec : ExplSpec}
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {γ : ℝ≥0 → ℂ} (hγ : Supp9B.IsProperCurve γ)
    (hγr : range γ = ExplState.physSet κ b jumps spec D)
    (hS : ∀ a ∈ (ExplState.run κ b jumps spec D spec.2.2.length).2.1, a ⊆ Ici 0)
    (hP : ∀ p ∈ (ExplState.run κ b jumps spec D spec.2.2.length).1,
      ∀ S ⊆ closure (p.1.tipSet p.2.1 p.2.2) ∩ range ((↑) : ℝ → ℂ), IsPreconnected S → S.Subsingleton) :
    ∀ S ⊆ range γ ∩ ((↑) : ℝ → ℂ) '' Iio 0, IsPreconnected S → S.Subsingleton := by
  have hIic : IsClosed (((↑) : ℝ → ℂ) '' Iic 0) :=
    Complex.isometry_ofReal.isClosedEmbedding.isClosedMap _ isClosed_Iic
  have hreal : ∀ a : Set ℝ, closure (((↑) : ℝ → ℂ) '' a) ⊆ range ((↑) : ℝ → ℂ) := fun a =>
    (WalkCont.closure_ofReal_image_subset (subset_univ a) isClosed_univ).trans (image_univ ▸ subset_rfl)
  refine WalkCont.subsingleton_of_finite_covers hγ (WalkCont.walkCover_finite _ _) (finite_singleton _)
    (fun F hF => WalkCont.isClosed_of_mem_walkCover hF) (fun G hG => (mem_singleton_iff.1 hG) ▸ hIic)
    (hγr ▸ WalkCont.physSet_subset_sUnion_walkCover _ _ _ _ _)
    (fun z hz => mem_sUnion_of_mem (image_mono Iio_subset_Iic_self hz) (mem_singleton _)) ?_
  intro F hF G hG S hSFG hSc
  rw [mem_singleton_iff] at hG
  subst hG
  rcases hF with rfl | ⟨p, hp, rfl⟩ | ⟨a, ha, rfl⟩
  · exact subsingleton_singleton.anti fun z hz => (hSFG hz).1
  · exact hP p hp S (fun z hz => ⟨(hSFG hz).1, image_subset_range _ _ (hSFG hz).2⟩) hSc
  · exact WalkCont.subsingleton_of_subset_ofReal_Ici_Iic fun z hz =>
      ⟨WalkCont.closure_ofReal_image_subset (hS a ha) isClosed_Ici (hSFG hz).1, (hSFG hz).2⟩


/-! ### The geometry of the boundary walks, R51 form -/

/-- **Named input: the left walk is a proper curve from `0`, R51 form** (mirror of
`WalkCont.RightWalkProperRegStatement`; Lemma GW1, p. 618: "There is a field-determined continuous injective proper
curve `R` from `x` to `y` … Reflection gives the left boundary walk `L` at angle `+π/2`"). -/
def LeftWalkProperRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, Supp9B.IsProperCurve γ ∧ γ 0 = 0 ∧
        range γ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
          (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)

/-- **Named input: the right walk contains no nondegenerate continuum of negative reals, R51 form**. Source: the
right walk's real connectors are rightward (Lemma GW1, p. 618: "Every nontrivial real connector is rightward") and an
ordinary piece contains no real subarc (Theorem GW4, proof, p. 637: "An ordinary piece contains no real interval";
follow-up note Part D.2: "the continuous inverse would put a nontrivial real subarc in the ordinary flow, contrary to
Lemma 2.5"). Bridge from the piece statement: `rightWalkNegRealRegStatement_of_pieces`. -/
def RightWalkNegRealRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      ∀ᵐ ω ∂P, ∀ S ⊆ ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) ∩ ((↑) : ℝ → ℂ) '' Iio 0,
        IsPreconnected S → S.Subsingleton

/-- The right walk's negative-real statement from its proper parametrization, the sides of the real connectors and
the piece statement (`neg_real_subsingleton`). -/
theorem rightWalkNegRealRegStatement_of_pieces (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hS : WalkCont.WalkConnectorSideRegStatement.{u}) (hNP : WalkCont.WalkPieceContinuumRegStatement.{u}) :
    RightWalkNegRealRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
  filter_upwards [hPR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hNP κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hPRω hSω hNPω
  obtain ⟨γR, hγR, -, hγRr⟩ := hPRω
  rw [← hγRr]
  exact neg_real_subsingleton hγR hγRr hSω.1 hNPω.2.1

/-- **Lemma GW3's between-region geometry, R51 form** (`GW3Sided.GW3GeometryRegStatement`; every component has an
oriented uniformizer), from the proper parametrizations of the two walks, GW2a's containment of the right walk in the
completed counterflow range, SB's frontier statement and the right walk's negative-real statement
(`hasOrientedUniformizer_of_touching`, `neg_real_mem_of_frontier`). -/
theorem gw3GeometryRegStatement_of_walks (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : LeftWalkProperRegStatement.{u}) (hA : GW2aContainmentStatement.{u}) (hF : SB.SBFrontierRegStatement.{u})
    (hNR : RightWalkNegRealRegStatement.{u}) : GW3Sided.GW3GeometryRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
  have hpi := Real.pi_pos
  have hRA := hA κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE _
    (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith⟩ true)
  filter_upwards [hPR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hPL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg, hRA,
    hF κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hNR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hPRω hPLω hRAω hFω hNRω
  obtain ⟨γR, hγR, hγR0, hγRr⟩ := hPRω
  obtain ⟨γL, hγL, hγL0, hγLr⟩ := hPLω
  intro C hC
  right
  rw [← hγRr, ← hγLr] at hC ⊢
  have hRK : range γR ⊆ counterflowCompletedRange (fun t => W' t ω₀) := hγRr ▸ hRAω
  have hKL := hFω.2
  rw [← hγLr] at hKL
  refine hasOrientedUniformizer_of_touching hγR hγR0 hγL hγL0 ?_ ?_ hC
  · rw [Set.disjoint_left]
    intro z hzR hzL
    exact (Set.eq_empty_iff_forall_notMem.1 hKL) z ⟨hRK hzR, hzL⟩
  · exact neg_real_mem_of_frontier hγR (isClosed_range_of_isProperCurve hγL hγL0) hRK hKL (hγRr ▸ hNRω)

end InteractingSLE.Theorem14.GW3SidedProof
