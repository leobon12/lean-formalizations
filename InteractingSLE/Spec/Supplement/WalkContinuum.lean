/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW3LawEvery
import InteractingSLE.Spec.Supplement.SB3Top
import InteractingSLE.Spec.Supplement.GW1ConnectorFirst
import InteractingSLE.Spec.Exist.StagedLaw4GW1

/-!
# The boundary walks share no nondegenerate continuum: reduction to the pieces

Packet PROVE-T14-GW7. Theorem GW4, proof (`source/spec/p625-671.md` L235, p. 637): "An interior common open subarc is
impossible […]. A common original-real interval is also impossible. Every nontrivial real interval in `R` is on the
original right boundary, and every such interval in `L` is on the original left boundary; these arcs are disjoint away
from their two common endpoints. An ordinary piece contains no real interval."

## The R51 form

The frozen Theorem 1.4 anchors (version 2, ruling R51) assume that every staged family is `StagedPiecesRegular`
(every launched piece is almost surely a continuous curve). Without it, a staged family may carry irregular later
pieces on a set of positive outer measure (PROVE-T14-GW1P), so pathwise statements about the walks' physical sets need
it. `WalkNoCommonContinuumRegStatement` is `GW3Law.WalkNoCommonContinuumStatement` with that hypothesis added
(`walkNoCommonContinuumRegStatement_of_unreg`: the old form implies it); likewise for the inputs below.

## The reduction (`walkNoCommonContinuumRegStatement_of_pieces`), deterministic

The physical set of a walk is its root, its ordinary pieces and its real connectors (`ExplState.physSet`). Suppose
`S ⊆ R ∩ L` is preconnected with two points. The right walk `R` is the range of a proper curve `γ` from `0` (GW1's
construction, `RightWalkProperRegStatement`; `SB.GW1ParamStatement` implies it). A proper injective curve is a closed
embedding, so `γ⁻¹(S)` is an interval and `S` contains an arc `γ([s, t])`, `s < t`
(`exists_Icc_image_subset_of_isPreconnected`). Cover `R` by the finitely many closed sets `{0}`, `closure` of each
piece, `closure` of each connector, and likewise `L` (`walkCover`). A nondegenerate interval covered by finitely many
closed sets has a nondegenerate subinterval inside one of them (`exists_Icc_subset_of_finite`, the finite Baire step);
applying this twice gives an arc `γ([s₂, t₂])` (two distinct points, `γ` injective) inside `F ∩ G` with `F` a set of
`R`'s cover and `G` one of `L`'s (`subsingleton_of_finite_covers`). The cases:

* `F` or `G` the root `{0}`: a singleton;
* two connectors: `R`'s connectors lie in `[0, ∞)` and `L`'s in `(−∞, 0]` (`WalkConnectorSideRegStatement`, the R51 form
  of `GW3Word.WalkConnectorSideStatement`), so `F ∩ G ⊆ {0}`;
* a piece and a connector: an ordinary piece contains no real continuum (`WalkPieceContinuumRegStatement`, parts 2–3);
* two pieces: an ordinary piece of `R` and one of `L` share no continuum (`WalkPieceContinuumRegStatement`, part 1;
  the interior common subarc of the source).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace WalkCont

/-! ### Deterministic topology: arcs in a proper curve, finite closed covers of an interval -/

section Topology

/-- **A proper curve is a closed embedding**: a continuous injective `γ : ℝ≥0 → ℂ` with `‖γ t‖ → ∞` is a proper map,
hence closed. -/
theorem isClosedEmbedding_of_isProperCurve {γ : ℝ≥0 → ℂ} (hγ : Supp9B.IsProperCurve γ) : IsClosedEmbedding γ := by
  have hp : IsProperMap γ := by
    rw [isProperMap_iff_tendsto_cocompact]
    refine ⟨hγ.1, ?_⟩
    rw [cocompact_eq_atTop]
    exact tendsto_cocompact_of_tendsto_dist_comp_atTop 0 (by simpa using hγ.2.2.2)
  exact .of_continuous_injective_isClosedMap hγ.1 hγ.2.1 hp.isClosedMap

/-- **A preconnected subset of the range of an embedded curve with two points contains a nondegenerate arc.** -/
theorem exists_Icc_image_subset_of_isPreconnected {γ : ℝ≥0 → ℂ} (he : IsEmbedding γ) {S : Set ℂ}
    (hS : S ⊆ range γ) (hSc : IsPreconnected S) {x y : ℂ} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    ∃ s t : ℝ≥0, s < t ∧ γ '' Icc s t ⊆ S := by
  have hT : IsPreconnected (γ ⁻¹' S) := by
    rw [← he.isInducing.isPreconnected_image, image_preimage_eq_of_subset hS]
    exact hSc
  obtain ⟨s, rfl⟩ := hS hx
  obtain ⟨t, rfl⟩ := hS hy
  rcases lt_or_gt_of_ne (fun h : s = t => hxy (by rw [h])) with hst | hts
  · exact ⟨s, t, hst, image_subset_iff.2 (hT.Icc_subset hx hy)⟩
  · exact ⟨t, s, hts, image_subset_iff.2 (hT.Icc_subset hy hx)⟩

/-- **Finite Baire step on an interval**: if a nondegenerate interval `[s, t]` is covered by finitely many closed
sets, one of them contains a nondegenerate subinterval. -/
theorem exists_Icc_subset_of_finite {𝒮 : Set (Set ℝ≥0)} (h𝒮 : 𝒮.Finite) (hc : ∀ F ∈ 𝒮, IsClosed F)
    {s t : ℝ≥0} (hst : s < t) (hcov : Icc s t ⊆ ⋃₀ 𝒮) :
    ∃ F ∈ 𝒮, ∃ s' t' : ℝ≥0, s' < t' ∧ Icc s' t' ⊆ Icc s t ∧ Icc s' t' ⊆ F := by
  induction 𝒮, h𝒮 using Set.Finite.induction_on generalizing s t with
  | empty =>
    have := hcov (left_mem_Icc.2 hst.le)
    simp at this
  | @insert F 𝒮 _ _ ih =>
    by_cases hF : Ioo s t ⊆ F
    · obtain ⟨m₁, hm₁, hm₁'⟩ := exists_between hst
      obtain ⟨m₂, hm₂, hm₂'⟩ := exists_between hm₁'
      exact ⟨F, mem_insert _ _, m₁, m₂, hm₂, Icc_subset_Icc hm₁.le hm₂'.le, (Icc_subset_Ioo hm₁ hm₂').trans hF⟩
    · obtain ⟨u, hu, huF⟩ := not_subset.1 hF
      have hopen : IsOpen (Ioo s t ∩ Fᶜ) := isOpen_Ioo.inter (hc F (mem_insert _ _)).isOpen_compl
      obtain ⟨l, r, hlr, hsub⟩ := (mem_nhds_iff_exists_Ioo_subset' ⟨s, hu.1⟩ ⟨t, hu.2⟩).1
        (hopen.mem_nhds ⟨hu, huF⟩)
      obtain ⟨a, ha, ha'⟩ := exists_between hlr.1
      obtain ⟨c, hc', hc''⟩ := exists_between hlr.2
      have hac : Icc a c ⊆ Ioo l r := Icc_subset_Ioo ha hc''
      have hcov' : Icc a c ⊆ ⋃₀ 𝒮 := by
        intro z hz
        have hz' := hsub (hac hz)
        obtain ⟨G, hG, hzG⟩ := hcov (Ioo_subset_Icc_self hz'.1)
        rcases mem_insert_iff.1 hG with rfl | hG
        · exact absurd hzG hz'.2
        · exact ⟨G, hG, hzG⟩
      obtain ⟨G, hG, s', t', hst', hsub', hG'⟩ :=
        ih (fun G hG => hc G (mem_insert_of_mem _ hG)) (ha'.trans hc') hcov'
      exact ⟨G, mem_insert_of_mem _ hG, s', t', hst',
        fun z hz => Ioo_subset_Icc_self (inter_subset_left (hsub (hac (hsub' hz)))), hG'⟩

/-- **No common continuum from finite closed covers.** Let `γ` be a proper curve and `L` a set. Cover `range γ` and
`L` by finite families of closed sets such that any set of the first family and any set of the second share no
nondegenerate preconnected subset. Then every preconnected subset of `range γ ∩ L` is at most a point. -/
theorem subsingleton_of_finite_covers {γ : ℝ≥0 → ℂ} (hγ : Supp9B.IsProperCurve γ) {L : Set ℂ}
    {𝒮R 𝒮L : Set (Set ℂ)} (hRf : 𝒮R.Finite) (hLf : 𝒮L.Finite) (hRc : ∀ F ∈ 𝒮R, IsClosed F)
    (hLc : ∀ G ∈ 𝒮L, IsClosed G) (hRcov : range γ ⊆ ⋃₀ 𝒮R) (hLcov : L ⊆ ⋃₀ 𝒮L)
    (hpair : ∀ F ∈ 𝒮R, ∀ G ∈ 𝒮L, ∀ S ⊆ F ∩ G, IsPreconnected S → S.Subsingleton) :
    ∀ S ⊆ range γ ∩ L, IsPreconnected S → S.Subsingleton := by
  intro S hS hSc x hx y hy
  by_contra hxy
  have he := (isClosedEmbedding_of_isProperCurve hγ).isEmbedding
  obtain ⟨s, t, hst, hsub⟩ :=
    exists_Icc_image_subset_of_isPreconnected he (fun z hz => (hS hz).1) hSc hx hy hxy
  have hcov₁ : Icc s t ⊆ ⋃₀ ((preimage γ) '' 𝒮R) := by
    intro r _
    obtain ⟨F, hF, hrF⟩ := hRcov (mem_range_self r)
    exact ⟨γ ⁻¹' F, mem_image_of_mem _ hF, hrF⟩
  obtain ⟨F', hF', s₁, t₁, hst₁, hsub₁, hF₁⟩ := exists_Icc_subset_of_finite (hRf.image _)
    (by rintro _ ⟨F, hF, rfl⟩; exact (hRc F hF).preimage hγ.1) hst hcov₁
  obtain ⟨F, hF, rfl⟩ := hF'
  have hcov₂ : Icc s₁ t₁ ⊆ ⋃₀ ((preimage γ) '' 𝒮L) := by
    intro r hr
    obtain ⟨G, hG, hrG⟩ := hLcov (hS (hsub (mem_image_of_mem γ (hsub₁ hr)))).2
    exact ⟨γ ⁻¹' G, mem_image_of_mem _ hG, hrG⟩
  obtain ⟨G', hG', s₂, t₂, hst₂, hsub₂, hG₂⟩ := exists_Icc_subset_of_finite (hLf.image _)
    (by rintro _ ⟨G, hG, rfl⟩; exact (hLc G hG).preimage hγ.1) hst₁ hcov₂
  obtain ⟨G, hG, rfl⟩ := hG'
  have hA : γ '' Icc s₂ t₂ ⊆ F ∩ G := by
    rintro _ ⟨r, hr, rfl⟩
    exact ⟨hF₁ (hsub₂ hr), hG₂ hr⟩
  have hAc : IsPreconnected (γ '' Icc s₂ t₂) := isPreconnected_Icc.image _ hγ.1.continuousOn
  exact hst₂.ne (hγ.2.1 (hpair F hF G hG _ hA hAc (mem_image_of_mem _ (left_mem_Icc.2 hst₂.le))
    (mem_image_of_mem _ (right_mem_Icc.2 hst₂.le))))

end Topology

/-! ### The closed cover of a walk's physical set -/

section Cover

/-- The closed cover of the physical set of a final state `s` with root `x` (`ExplState.physSet`): the root, the
closures of the ordinary pieces (`s.1`) and the closures of the real connectors (`s.2.1`). -/
def walkCover (s : ExplState) (x : ℝ) : Set (Set ℂ) :=
  insert {(x : ℂ)} ((fun p : Chart × (ℝ≥0 → ℝ) × ℝ≥0∞ => closure (p.1.tipSet p.2.1 p.2.2)) '' {p | p ∈ s.1} ∪
    (fun a : Set ℝ => closure (((↑) : ℝ → ℂ) '' a)) '' {a | a ∈ s.2.1})

theorem walkCover_finite (s : ExplState) (x : ℝ) : (walkCover s x).Finite :=
  ((s.1.finite_toSet.image _).union (s.2.1.finite_toSet.image _)).insert _

theorem isClosed_of_mem_walkCover {s : ExplState} {x : ℝ} {F : Set ℂ} (hF : F ∈ walkCover s x) :
    IsClosed F := by
  rcases hF with rfl | ⟨p, -, rfl⟩ | ⟨a, -, rfl⟩
  · exact isClosed_singleton
  · exact isClosed_closure
  · exact isClosed_closure

/-- The physical set of a history is covered by the closed cover of its final state. -/
theorem physSet_subset_sUnion_walkCover (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ExplState.physSet κ b jumps spec D ⊆
      ⋃₀ walkCover (ExplState.run κ b jumps spec D spec.2.2.length) spec.1 := by
  intro z hz
  rcases hz with (hz | hz) | hz
  · exact ⟨_, mem_insert _ _, hz⟩
  · obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.1 hz
    exact ⟨_, mem_insert_of_mem _ (Or.inl ⟨p, hp, rfl⟩), subset_closure hzp⟩
  · obtain ⟨a, ha, hza⟩ := mem_iUnion₂.1 hz
    exact ⟨_, mem_insert_of_mem _ (Or.inr ⟨a, ha, rfl⟩), subset_closure hza⟩

/-- The closure of the image of a set of reals lies in the image of any closed set of reals containing it. -/
theorem closure_ofReal_image_subset {a A : Set ℝ} (ha : a ⊆ A) (hA : IsClosed A) :
    closure (((↑) : ℝ → ℂ) '' a) ⊆ ((↑) : ℝ → ℂ) '' A :=
  closure_minimal (image_mono ha) (Complex.isometry_ofReal.isClosedEmbedding.isClosedMap _ hA)

/-- A set of complex numbers that are images of both a nonnegative and a nonpositive real is at most `{0}`. -/
theorem subsingleton_of_subset_ofReal_Ici_Iic {S : Set ℂ}
    (h : S ⊆ ((↑) : ℝ → ℂ) '' Ici 0 ∩ ((↑) : ℝ → ℂ) '' Iic 0) : S.Subsingleton := by
  refine (subsingleton_singleton (a := (0 : ℂ))).anti fun z hz => ?_
  obtain ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩ := h hz
  have hyx : y = x := Complex.ofReal_injective hxy
  have hx0 : x = 0 := le_antisymm (hyx ▸ hy) hx
  simp [hx0]

end Cover

/-! ### The statements in the R51 form -/

/-- **The walks share no nondegenerate connected set, R51 form**: `GW3Law.WalkNoCommonContinuumStatement` for staged
families that are also `StagedPiecesRegular` (the hypothesis of the frozen Theorem 1.4 anchors, version 2). -/
def WalkNoCommonContinuumRegStatement : Prop :=
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
      ∀ᵐ ω₀ ∂P,
        ∀ S ⊆ ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω₀) ∩
            ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
              (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω₀),
          IsPreconnected S → S.Subsingleton

/-- **Named input: the right walk is a proper curve from `0`, R51 form** (Lemma GW1, p. 618: "There is a
field-determined continuous injective proper curve `R` from `x` to `y`"): `SB.GW1ParamStatement` for staged families
that are also `StagedPiecesRegular` (`rightWalkProperRegStatement_of_gw1Param`). -/
def RightWalkProperRegStatement : Prop :=
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
        range γ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)

/-- **Named input: the sides of the walks' real connectors, R51 form** (Lemma GW1: "Every nontrivial real connector
is rightward"; reflection for `L`): `GW3Word.WalkConnectorSideStatement` for staged families that are also
`StagedPiecesRegular` (`walkConnectorSideRegStatement_of_unreg`, `walkConnectorSideRegStatement_of_later`). -/
def WalkConnectorSideRegStatement : Prop :=
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
      ∀ᵐ ω₀ ∂P,
        (∀ a ∈ (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω₀)
            (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length).2.1, a ⊆ Ici 0) ∧
        ∀ a ∈ (ExplState.run κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω₀)
            (boundaryWalkSpec b jumps (Real.pi / 2) false).2.2.length).2.1, a ⊆ Iic 0

/-- **Named input: the ordinary pieces of the walks, pairwise and against the real line, R51 form** (Theorem GW4,
proof, p. 637: "An interior common open subarc is impossible: on the same incident side the two exact flow germs
differ by `πχ`, whereas an inherited branch change is an integer multiple of `2πχ`. […] An ordinary piece contains no
real interval."). Almost surely: (1) the closure of an ordinary piece of `R` and the closure of an ordinary piece of
`L` share no nondegenerate preconnected set; (2)–(3) the closure of an ordinary piece of either walk contains no
nondegenerate preconnected set of real points. -/
def WalkPieceContinuumRegStatement : Prop :=
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
      ∀ᵐ ω₀ ∂P,
        (∀ p ∈ (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω₀)
              (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length).1,
          ∀ q ∈ (ExplState.run κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
              (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω₀)
              (boundaryWalkSpec b jumps (Real.pi / 2) false).2.2.length).1,
          ∀ S ⊆ closure (p.1.tipSet p.2.1 p.2.2) ∩ closure (q.1.tipSet q.2.1 q.2.2),
            IsPreconnected S → S.Subsingleton) ∧
        (∀ p ∈ (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω₀)
              (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length).1,
          ∀ S ⊆ closure (p.1.tipSet p.2.1 p.2.2) ∩ range ((↑) : ℝ → ℂ), IsPreconnected S → S.Subsingleton) ∧
        ∀ q ∈ (ExplState.run κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
              (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω₀)
              (boundaryWalkSpec b jumps (Real.pi / 2) false).2.2.length).1,
          ∀ S ⊆ closure (q.1.tipSet q.2.1 q.2.2) ∩ range ((↑) : ℝ → ℂ), IsPreconnected S → S.Subsingleton

/-! ### The reduction -/

/-- **The walks share no nondegenerate continuum (R51 form)** from the proper parametrization of the right walk, the
sides of the real connectors and the piece statements. -/
theorem walkNoCommonContinuumRegStatement_of_pieces (hP : RightWalkProperRegStatement.{u})
    (hS : WalkConnectorSideRegStatement.{u}) (hN : WalkPieceContinuumRegStatement.{u}) :
    WalkNoCommonContinuumRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
  filter_upwards [hP κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hN κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hPω hSω hNω
  obtain ⟨γ, hγ, -, hγR⟩ := hPω
  obtain ⟨hSR, hSL⟩ := hSω
  obtain ⟨hpp, hpR, hpL⟩ := hNω
  rw [← hγR]
  refine subsingleton_of_finite_covers hγ (walkCover_finite _ _) (walkCover_finite _ _)
    (fun F hF => isClosed_of_mem_walkCover hF) (fun G hG => isClosed_of_mem_walkCover hG)
    (hγR ▸ physSet_subset_sUnion_walkCover _ _ _ _ _) (physSet_subset_sUnion_walkCover _ _ _ _ _) ?_
  have hreal : ∀ a : Set ℝ, closure (((↑) : ℝ → ℂ) '' a) ⊆ range ((↑) : ℝ → ℂ) := fun a =>
    (closure_ofReal_image_subset (subset_univ a) isClosed_univ).trans (image_univ ▸ subset_rfl)
  intro F hF G hG S hSFG hSc
  rcases hF with rfl | ⟨p, hp, rfl⟩ | ⟨a, ha, rfl⟩
  · exact subsingleton_singleton.anti fun z hz => (hSFG hz).1
  · rcases hG with rfl | ⟨q, hq, rfl⟩ | ⟨a', -, rfl⟩
    · exact subsingleton_singleton.anti fun z hz => (hSFG hz).2
    · exact hpp p hp q hq S hSFG hSc
    · exact hpR p hp S (fun z hz => ⟨(hSFG hz).1, hreal a' (hSFG hz).2⟩) hSc
  · rcases hG with rfl | ⟨q, hq, rfl⟩ | ⟨a', ha', rfl⟩
    · exact subsingleton_singleton.anti fun z hz => (hSFG hz).2
    · exact hpL q hq S (fun z hz => ⟨(hSFG hz).2, hreal a (hSFG hz).1⟩) hSc
    · exact subsingleton_of_subset_ofReal_Ici_Iic fun z hz =>
        ⟨closure_ofReal_image_subset (hSR a ha) isClosed_Ici (hSFG hz).1,
          closure_ofReal_image_subset (hSL a' ha') isClosed_Iic (hSFG hz).2⟩

/-! ### Bridges from the unregularized forms -/

/-- The unregularized `GW3Law.WalkNoCommonContinuumStatement` implies its R51 form. -/
theorem walkNoCommonContinuumRegStatement_of_unreg (hN : GW3Law.WalkNoCommonContinuumStatement.{u}) :
    WalkNoCommonContinuumRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE _
  exact hN κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE

/-- GW1's construction (`SB.GW1ParamStatement`) implies the R51 form of the right walk's proper parametrization. -/
theorem rightWalkProperRegStatement_of_gw1Param (hG : SB.GW1ParamStatement.{u}) :
    RightWalkProperRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE _
  exact hG κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE

/-- The unregularized `GW3Word.WalkConnectorSideStatement` implies its R51 form. -/
theorem walkConnectorSideRegStatement_of_unreg (hS : GW3Word.WalkConnectorSideStatement.{u}) :
    WalkConnectorSideRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE _
  exact hS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE

/-- The R51 form of the connector sides from GW0's forward implication and the later walk pieces
(`GW1Conn.walkConnectorSideStatement_of_later`, PROVE-T14-GW6). -/
theorem walkConnectorSideRegStatement_of_later (hGW0 : GW0.GW0ForwardStatement.{u})
    (hlater : GW1Conn.WalkLaterRecordStatement.{u}) : WalkConnectorSideRegStatement.{u} :=
  walkConnectorSideRegStatement_of_unreg (GW1Conn.walkConnectorSideStatement_of_later hGW0 hlater)

end WalkCont

end Theorem14

end InteractingSLE
