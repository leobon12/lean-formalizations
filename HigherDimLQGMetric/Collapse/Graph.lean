import HigherDimLQGMetric.Metric.Lemma21
import LQGMetric.Metric.Geodesic
import Mathlib.Topology.Connected.Clopen

/-!
# Finite rectifiable graphs and their intrinsic metric

The ambient metric is arbitrary. A finite rectifiable graph is a connected finite union of
injective continuous arcs of finite length. Its intrinsic distance is `internalEDist`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

variable {X : Type*} [MetricSpace X]

/-- A finite union of injective rectifiable arcs whose union is connected. -/
def IsFiniteRectGraph (K : Set X) : Prop :=
  ∃ (m : ℕ) (γ : Fin m → ℝ → X),
    (∀ i, ContinuousOn (γ i) (Icc 0 1)) ∧
    (∀ i, Set.InjOn (γ i) (Icc 0 1)) ∧
    (∀ i, curveLength (γ i) 0 1 ≠ ⊤) ∧
    K = (⋃ i, (γ i) '' Icc 0 1) ∧
    IsConnected K

/-- Each finite rectifiable graph is compact in the ambient metric. -/
theorem IsFiniteRectGraph.isCompact {K : Set X} (hK : IsFiniteRectGraph K) : IsCompact K := by
  obtain ⟨m, γ, hcont, _, _, rfl, _⟩ := hK
  refine isCompact_iUnion fun i => ?_
  exact isCompact_Icc.image_of_continuousOn (hcont i)

/-- The ambient metric is bounded by the intrinsic metric, for every set. -/
theorem edist_le_graphDist (K : Set X) (x y : X) :
    edist x y ≤ internalEDist K x y :=
  edist_le_internalEDist K x y

/-- Ordered points on a rectifiable arc have finite intrinsic distance. -/
theorem internalEDist_ne_top_of_mem_arc_ordered {K : Set X} {γ : ℝ → X}
    (hcont : ContinuousOn γ (Icc 0 1)) (hlen : curveLength γ 0 1 ≠ ⊤)
    (hγK : γ '' Icc 0 1 ⊆ K) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t) :
    internalEDist K (γ s) (γ t) ≠ ⊤ := by
  have hsub : Icc s t ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hs.1 ht.2
  have hcurve := internalEDist_le_curveLength hst (hcont.mono hsub)
    (fun u hu => hγK ⟨u, hsub hu, rfl⟩)
  exact ne_top_of_le_ne_top
    (ne_top_of_le_ne_top hlen (curveLength_mono γ hs.1 ht.2)) hcurve

/-- Points on the same rectifiable arc have finite intrinsic distance in any set containing it. -/
theorem internalEDist_ne_top_of_mem_arc {K : Set X} {γ : ℝ → X}
    (hcont : ContinuousOn γ (Icc 0 1)) (hlen : curveLength γ 0 1 ≠ ⊤)
    (hγK : γ '' Icc 0 1 ⊆ K) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    internalEDist K (γ s) (γ t) ≠ ⊤ := by
  rcases le_total s t with hst | hts
  · exact internalEDist_ne_top_of_mem_arc_ordered hcont hlen hγK hs ht hst
  · rw [internalEDist_comm]
    exact internalEDist_ne_top_of_mem_arc_ordered hcont hlen hγK ht hs hts

/-- Connectedness of the finite arc union turns finite within-arc distances into finite
intrinsic distance between any two graph points. -/
theorem IsFiniteRectGraph.internal_finite {K : Set X} (hK : IsFiniteRectGraph K)
    {x y : X} (hx : x ∈ K) (hy : y ∈ K) : internalEDist K x y ≠ ⊤ := by
  classical
  obtain ⟨m, γ, hcont, _, hlen, hEq, hconn⟩ := hK
  let A : Fin m → Set X := fun i => (γ i) '' Icc 0 1
  have hAK (i : Fin m) : A i ⊆ K := by
    intro z hz
    rw [hEq]
    exact Set.mem_iUnion_of_mem i hz
  have hAclosed (i : Fin m) : IsClosed (A i) :=
    ((isCompact_Icc.image_of_continuousOn (hcont i))).isClosed
  have hAfin (i : Fin m) {p q : X} (hp : p ∈ A i) (hq : q ∈ A i) :
      internalEDist K p q ≠ ⊤ := by
    obtain ⟨s, hs, rfl⟩ := hp
    obtain ⟨t, ht, rfl⟩ := hq
    exact internalEDist_ne_top_of_mem_arc (hcont i) (hlen i) (hAK i) hs ht
  let R : Set X := {z | z ∈ K ∧ internalEDist K x z ≠ ⊤}
  let I : Set (Fin m) := {i | ∃ z ∈ A i, z ∈ R}
  let U : Set X := ⋃ i, if i ∈ I then A i else ∅
  let V : Set X := ⋃ i, if i ∉ I then A i else ∅
  have hR_arc (i : Fin m) {p q : X} (hp : p ∈ R) (hpA : p ∈ A i)
      (hqA : q ∈ A i) : q ∈ R := by
    refine ⟨hAK i hqA, ?_⟩
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hp.2, hAfin i hpA hqA⟩)
      (internalEDist_triangle K x p q)
  have hRU : R = U := by
    ext z
    constructor
    · intro hz
      have hzK : z ∈ K := hz.1
      rw [hEq] at hzK
      obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hzK
      have hi : i ∈ I := ⟨z, hzi, hz⟩
      exact Set.mem_iUnion.mpr ⟨i, by simpa only [ite_eq_left hi] using hzi⟩
    · intro hz
      obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hz
      have hi : i ∈ I := by
        by_contra hn
        simp [hn] at hzi
      have hzA : z ∈ A i := by simpa only [ite_eq_left hi] using hzi
      obtain ⟨p, hpA, hpR⟩ := hi
      exact hR_arc i hpR hpA hzA
  have hVnotR {z : X} (hz : z ∈ V) : z ∉ R := by
    obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hz
    have hi : i ∉ I := by
      by_contra h
      simp [h] at hzi
    have hzA : z ∈ A i := by simpa only [ite_eq_left hi] using hzi
    intro hzR
    exact hi ⟨z, hzA, hzR⟩
  have hUclosed : IsClosed U := by
    apply isClosed_iUnion_of_finite
    intro i
    by_cases hi : i ∈ I
    · simpa only [ite_eq_left hi] using hAclosed i
    · simpa only [ite_eq_right hi] using (isClosed_empty : IsClosed (∅ : Set X))
  have hVclosed : IsClosed V := by
    apply isClosed_iUnion_of_finite
    intro i
    by_cases hi : i ∈ I
    · simpa only [ite_eq_right (not_not_intro hi)] using (isClosed_empty : IsClosed (∅ : Set X))
    · simpa only [ite_eq_left hi] using hAclosed i
  have hcover : K ⊆ U ∪ V := by
    intro z hz
    rw [hEq] at hz
    obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hz
    by_cases hi : i ∈ I
    · exact Or.inl (Set.mem_iUnion.mpr ⟨i, by simpa only [ite_eq_left hi] using hzi⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨i, by simpa only [ite_eq_left hi] using hzi⟩)
  have hdisj : K ∩ (U ∩ V) = ∅ := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    intro hz
    exact hVnotR hz.2.2 (hRU.symm ▸ hz.2.1)
  have hxR : x ∈ R := ⟨hx, by rw [internalEDist_self hx]; exact ENNReal.zero_ne_top⟩
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hconn.isPreconnected)
    U V hUclosed hVclosed hcover hdisj with hKU | hKV
  · exact (hRU.symm ▸ hKU hy).2
  · exact False.elim (hVnotR (hKV hx) hxR)

/-- The lift of a rectifiable arc into the intrinsic extended metric of a containing set is
continuous. Its intrinsic distance is controlled by the difference of arc-length parameters. -/
theorem continuous_internalLift_of_arc {K : Set X} {γ : ℝ → X}
    (hcont : ContinuousOn γ (Icc 0 1)) (hlen : curveLength γ 0 1 ≠ ⊤)
    (hγK : γ '' Icc 0 1 ⊆ K) :
    Continuous (fun s : Icc (0 : ℝ) 1 =>
      (InternalSpace.mk ⟨γ s, hγK ⟨s, s.property, rfl⟩⟩ : InternalSpace K)) := by
  let σ : ℝ → ℝ := variationOnFromTo γ (Icc 0 1) 0
  let L : ℝ := (curveLength γ 0 1).toReal
  let Q : ℝ → X := lengthParam γ 0 1
  have hbv : BoundedVariationOn γ (Icc 0 1) :=
    boundedVariationOn_of_curveLength_ne_top hlen
  have h0 : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hσcont : ContinuousOn σ (Icc 0 1) := by
    intro s hs
    exact (hbv.continuousWithinAt_variationOnFromTo_iff h0 hs).2 (hcont s hs)
  have hσimage : σ '' Icc (0 : ℝ) 1 = Icc 0 L :=
    variationOnFromTo_image_Icc (by norm_num) hcont hlen
  have hσmem {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : σ s ∈ Icc 0 L := by
    rw [← hσimage]
    exact ⟨s, hs, rfl⟩
  have hQK {r : ℝ} (hr : r ∈ Icc 0 L) : Q r ∈ K := by
    rw [← hσimage] at hr
    obtain ⟨s, hs, rfl⟩ := hr
    change lengthParam γ 0 1 (variationOnFromTo γ (Icc 0 1) 0 s) ∈ K
    rw [lengthParam_variationOnFromTo hlen hs]
    exact hγK ⟨s, hs, rfl⟩
  have hunit : HasUnitSpeedOn Q (Icc 0 L) :=
    hasUnitSpeedOn_lengthParam (by norm_num) hcont hlen
  have hbound {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
      internalEDist K (γ s) (γ t) ≤ edist (σ s) (σ t) := by
    rcases le_total s t with hst | hts
    · have hσst : σ s ≤ σ t :=
        variationOnFromTo.monotoneOn hbv.locallyBoundedVariationOn h0 hs ht hst
      have hsub : Icc (σ s) (σ t) ⊆ Icc 0 L :=
        Icc_subset_Icc (hσmem hs).1 (hσmem ht).2
      have hcurve := internalEDist_le_curveLength hσst
        ((continuousOn_of_hasUnitSpeedOn hunit).mono hsub)
        (fun r hr => hQK (hsub hr))
      have hQs : Q (σ s) = γ s := lengthParam_variationOnFromTo hlen hs
      have hQt : Q (σ t) = γ t := lengthParam_variationOnFromTo hlen ht
      rw [hQs, hQt] at hcurve
      calc internalEDist K (γ s) (γ t)
          ≤ curveLength Q (σ s) (σ t) := hcurve
        _ = ENNReal.ofReal (σ t - σ s) :=
          curveLength_of_hasUnitSpeedOn hunit (hσmem hs) (hσmem ht)
        _ = edist (σ s) (σ t) := by
          rw [edist_dist, Real.dist_eq, abs_sub_comm (σ s) (σ t),
            abs_of_nonneg (sub_nonneg.mpr hσst)]
    · rw [internalEDist_comm, edist_comm]
      have hσts : σ t ≤ σ s :=
        variationOnFromTo.monotoneOn hbv.locallyBoundedVariationOn h0 ht hs hts
      have hsub : Icc (σ t) (σ s) ⊆ Icc 0 L :=
        Icc_subset_Icc (hσmem ht).1 (hσmem hs).2
      have hcurve := internalEDist_le_curveLength hσts
        ((continuousOn_of_hasUnitSpeedOn hunit).mono hsub)
        (fun r hr => hQK (hsub hr))
      have hQs : Q (σ s) = γ s := lengthParam_variationOnFromTo hlen hs
      have hQt : Q (σ t) = γ t := lengthParam_variationOnFromTo hlen ht
      rw [hQt, hQs] at hcurve
      calc internalEDist K (γ t) (γ s)
          ≤ curveLength Q (σ t) (σ s) := hcurve
        _ = ENNReal.ofReal (σ s - σ t) :=
          curveLength_of_hasUnitSpeedOn hunit (hσmem ht) (hσmem hs)
        _ = edist (σ t) (σ s) := by
          rw [edist_dist, Real.dist_eq, abs_sub_comm (σ t) (σ s),
            abs_of_nonneg (sub_nonneg.mpr hσts)]
  have hσsub : Continuous (fun s : Icc (0 : ℝ) 1 => σ s) := hσcont.domRestrict
  apply EMetric.continuous_iff.mpr
  intro b ε hε
  obtain ⟨δ, hδ, hσδ⟩ := EMetric.continuous_iff.mp hσsub b ε hε
  refine ⟨δ, hδ, fun a ha => ?_⟩
  exact lt_of_le_of_lt (hbound a.property b.property) (hσδ a ha)

/-- The ambient-to-intrinsic identity of a finite rectifiable graph is continuous. The finite
union is handled as a quotient of the disjoint union of its compact arc parameter spaces. -/
theorem IsFiniteRectGraph.continuous_internalLift {K : Set X} (hK : IsFiniteRectGraph K) :
    Continuous (fun z : K => (InternalSpace.mk z : InternalSpace K)) := by
  obtain ⟨m, γ, hcont, _, hlen, hEq, _⟩ := hK
  let f : (Σ _i : Fin m, Icc (0 : ℝ) 1) → K := fun z =>
    ⟨γ z.1 z.2, by
      rw [hEq]
      exact Set.mem_iUnion_of_mem z.1 ⟨z.2, z.2.property, rfl⟩⟩
  have hfcont : Continuous f := by
    apply continuous_sigma_iff.mpr
    intro i
    exact Continuous.subtype_mk (hcont i).domRestrict (fun _ => by
      change γ i _ ∈ K
      rw [hEq]
      exact Set.mem_iUnion_of_mem i ⟨_, Subtype.property _, rfl⟩)
  have hfsurj : Function.Surjective f := by
    intro z
    have hz : (z : X) ∈ ⋃ i, (γ i) '' Icc 0 1 := by
      simpa only [← hEq] using z.property
    obtain ⟨i, t, ht, htz⟩ := Set.mem_iUnion.mp hz
    refine ⟨⟨i, ⟨t, ht⟩⟩, ?_⟩
    exact Subtype.ext htz
  have hfquot : Topology.IsQuotientMap f :=
    Topology.IsQuotientMap.of_surjective_continuous hfsurj hfcont
  apply hfquot.continuous_iff.mpr
  apply continuous_sigma_iff.mpr
  intro i
  simpa only [Function.comp_def] using
    (continuous_internalLift_of_arc (hcont i) (hlen i) (by
      intro z hz
      rw [hEq]
      exact Set.mem_iUnion_of_mem i hz))

/-- The intrinsic distance is jointly continuous on the graph in the ambient topology. -/
theorem IsFiniteRectGraph.continuousOn_internal {K : Set X} (hK : IsFiniteRectGraph K) :
    ContinuousOn (fun p : X × X => internalEDist K p.1 p.2) (K ×ˢ K) := by
  let g : K → InternalSpace K := fun z => InternalSpace.mk z
  have hg : Continuous g := hK.continuous_internalLift
  have H : Continuous (fun p : K × K => edist (g p.1) (g p.2)) :=
    continuous_edist.comp (hg.prodMap hg)
  apply continuousOn_iff_continuous_domRestrict.mpr
  have H' := H.comp (Homeomorph.Set.prod K K).continuous
  convert H' using 1
  funext p
  rfl

/-- The inclusion of an intrinsic subspace into the ambient metric space is 1-Lipschitz. -/
theorem internalSpace_val_lipschitz (K : Set X) :
    LipschitzWith 1 (InternalSpace.val : InternalSpace K → X) := by
  intro p q
  simpa only [ENNReal.coe_one, one_mul] using (InternalSpace.edist_val_le p q)

/-- Ambient and intrinsic lengths agree for a curve in a subset. -/
theorem curveLength_internalSpace {K : Set X} {P : ℝ → InternalSpace K} {a b : ℝ}
    (hP : ContinuousOn P (Icc a b)) :
    curveLength P a b = curveLength (InternalSpace.val ∘ P) a b := by
  have hval : ContinuousOn (InternalSpace.val ∘ P) (Icc a b) :=
    (internalSpace_val_lipschitz K).continuous.continuousOn.comp hP
      (fun _ _ => Set.mem_univ _)
  have hmaps : MapsTo (InternalSpace.val ∘ P) (Icc a b) K := fun t _ => (P t).val_mem
  rw [curveLength_eq_iSup_internalEDist hval hmaps]
  rfl

/-- The intrinsic graph space is compact. -/
theorem IsFiniteRectGraph.compactSpace_internal {K : Set X} (hK : IsFiniteRectGraph K) :
    CompactSpace (InternalSpace K) := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  have hg : Continuous (fun z : K => (InternalSpace.mk z : InternalSpace K)) :=
    hK.continuous_internalLift
  have hrange : Set.range (fun z : K => (InternalSpace.mk z : InternalSpace K)) = Set.univ := by
    ext z
    simp only [Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨z, rfl⟩
  exact isCompact_univ_iff.mp (by simpa only [Set.image_univ, hrange] using
    (isCompact_univ.image hg))

/-- The intrinsic metric of a finite rectifiable graph is a length metric. -/
theorem IsFiniteRectGraph.isLengthSpace_internal {K : Set X} (hK : IsFiniteRectGraph K) :
    IsLengthSpace (InternalSpace K) := by
  intro x y ε hε
  have hfin : edist x y ≠ ⊤ := hK.internal_finite x.val_mem y.val_mem
  have hε0 : ENNReal.ofReal ε ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hε)
  have hlt : internalEDist K x.val y.val <
      internalEDist K x.val y.val + ENNReal.ofReal ε := ENNReal.lt_add_right hfin hε0
  change (⨅ γ : {γ : Path x.val y.val // ∀ t, γ t ∈ K}, pathLength γ.1) <
    internalEDist K x.val y.val + ENNReal.ofReal ε at hlt
  obtain ⟨γ, hγlt⟩ := iInf_lt_iff.mp hlt
  let δ : Path x y :=
    { toFun := fun t => (InternalSpace.mk ⟨γ.1 t, γ.2 t⟩ : InternalSpace K)
      continuous_toFun := hK.continuous_internalLift.comp
        (Continuous.subtype_mk γ.1.continuous (fun t => γ.2 t))
      source' := by
        apply InternalSpace.val_injective
        exact γ.1.source
      target' := by
        apply InternalSpace.val_injective
        exact γ.1.target }
  have hlen : pathLength δ = pathLength γ.1 := by
    unfold pathLength
    rw [curveLength_internalSpace δ.continuous_extend.continuousOn]
    apply curveLength_congr
    intro t ht
    change (δ.extend t).val = γ.1.extend t
    rw [Path.extend_apply δ ht, Path.extend_apply γ.1 ht]
    rfl
  exact ⟨δ, hlen ▸ hγlt.le⟩

/-- Any two graph points are joined inside the graph by a path whose ambient length is exactly
their intrinsic distance. -/
theorem IsFiniteRectGraph.exists_shortest_path {K : Set X} (hK : IsFiniteRectGraph K)
    {x y : X} (hx : x ∈ K) (hy : y ∈ K) :
    ∃ γ : Path x y, (∀ t, γ t ∈ K) ∧ pathLength γ = internalEDist K x y := by
  letI : MetricSpace (InternalSpace K) := EMetricSpace.toMetricSpace (by
    intro p q
    exact hK.internal_finite p.val_mem q.val_mem)
  haveI : CompactSpace (InternalSpace K) := hK.compactSpace_internal
  obtain ⟨γ, hγ⟩ := exists_pathLength_eq_edist hK.isLengthSpace_internal
    (InternalSpace.mk ⟨x, hx⟩) (InternalSpace.mk ⟨y, hy⟩)
  let δ : Path x y := γ.map (internalSpace_val_lipschitz K).continuous
  refine ⟨δ, (fun t => (γ t).val_mem), ?_⟩
  have hlen := curveLength_internalSpace (a := 0) (b := 1)
    γ.continuous_extend.continuousOn
  change pathLength γ = internalEDist K x y at hγ
  unfold pathLength at hγ ⊢
  rw [hlen] at hγ
  convert hγ using 1
  apply curveLength_congr
  intro t ht
  change δ.extend t = InternalSpace.val (γ.extend t)
  rw [Path.extend_apply δ ht, Path.extend_apply γ ht]
  rfl

/-- An intrinsic unit-speed geodesic is injective on its parameter interval. -/
theorem intrinsic_geodesic_injOn {K : Set X} {P : ℝ → X} {a b : ℝ}
    (hP : MapsTo P (Icc a b) K)
    (hunit : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      internalEDist K (P s) (P t) = ENNReal.ofReal |t - s|) :
    InjOn P (Icc a b) := by
  intro s hs t ht heq
  have hzero : ENNReal.ofReal |t - s| = 0 := by
    rw [← hunit s hs t ht, heq, internalEDist_self (hP ht)]
  have habs : |t - s| = 0 := le_antisymm ((ENNReal.ofReal_eq_zero).1 hzero) (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp habs) |>.symm

/-- A finite rectifiable graph has a unit-speed intrinsic geodesic between any two points.
The ambient curve is injective when the endpoints differ. -/
theorem IsFiniteRectGraph.exists_intrinsic_geodesic {K : Set X} (hK : IsFiniteRectGraph K)
    {x y : X} (hx : x ∈ K) (hy : y ∈ K) :
    ∃ P : ℝ → X,
      let ℓ := (internalEDist K x y).toReal
      ContinuousOn P (Icc 0 ℓ) ∧ MapsTo P (Icc 0 ℓ) K ∧
      P 0 = x ∧ P ℓ = y ∧
      (∀ s ∈ Icc 0 ℓ, ∀ t ∈ Icc 0 ℓ,
        internalEDist K (P s) (P t) = ENNReal.ofReal |t - s|) ∧
      InjOn P (Icc 0 ℓ) := by
  letI : MetricSpace (InternalSpace K) := EMetricSpace.toMetricSpace (by
    intro p q
    exact hK.internal_finite p.val_mem q.val_mem)
  haveI : CompactSpace (InternalSpace K) := hK.compactSpace_internal
  let xK : InternalSpace K := InternalSpace.mk ⟨x, hx⟩
  let yK : InternalSpace K := InternalSpace.mk ⟨y, hy⟩
  let ℓ : ℝ := (internalEDist K x y).toReal
  have hd : dist xK yK = ℓ := rfl
  obtain ⟨P, hP0, hP1, hPg, _hunit, hPdist⟩ :=
    exists_isGeodesicCurve_unitSpeed hK.isLengthSpace_internal xK yK
  let Q : ℝ → X := InternalSpace.val ∘ P
  have hQcont : ContinuousOn Q (Icc 0 ℓ) := by
    rw [← hd]
    exact (internalSpace_val_lipschitz K).continuous.continuousOn.comp hPg.2.1
      (fun _ _ => Set.mem_univ _)
  have hQK : MapsTo Q (Icc 0 ℓ) K := fun t _ => (P t).val_mem
  have hQdist : ∀ s ∈ Icc 0 ℓ, ∀ t ∈ Icc 0 ℓ,
      internalEDist K (Q s) (Q t) = ENNReal.ofReal |t - s| := by
    intro s hs t ht
    change edist (P s) (P t) = ENNReal.ofReal |t - s|
    rw [edist_dist, hPdist s (hd ▸ hs) t (hd ▸ ht)]
  refine ⟨Q, hQcont, hQK, ?_, ?_, hQdist, ?_⟩
  · exact congrArg InternalSpace.val hP0
  · change Q ℓ = y
    rw [← hd]
    exact congrArg InternalSpace.val hP1
  · exact intrinsic_geodesic_injOn hQK hQdist

end HigherDimLQGMetric
