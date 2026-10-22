import HigherDimLQGMetric.Routing.Lemma41Connectivity
import HigherDimLQGMetric.Collapse.Graph
import LQGMetric.Metric.LengthGeodesic

/-!
# Simple rectifiable subarcs of rectifiable path images

A finite length path has compact image also for its intrinsic path metric. Therefore its image
contains an injective intrinsic geodesic between any two of its points. This is the connector
shortening step of Lemma 4.1′.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open Set LQGMetric.MetricGeometry
open scoped ENNReal

namespace HigherDimLQGMetric

variable {X : Type*} [MetricSpace X] {x y : X} (P : Path x y)

/-- Every two points of a finite length path image have finite intrinsic distance. -/
theorem lemma41_pathImage_internal_finite (hP : pathLength P ≠ ∞)
    {a b : X} (ha : a ∈ range P) (hb : b ∈ range P) :
    internalEDist (range P) a b ≠ ∞ := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨t, rfl⟩ := hb
  simpa only [Path.extend_apply P s.property, Path.extend_apply P t.property] using
    (internalEDist_ne_top_of_mem_arc P.continuous_extend.continuousOn hP
      (by rw [P.image_extend_of_subset (by rfl)]) s.property t.property)

/-- The inclusion of a rectifiable path image into its intrinsic space is continuous. -/
theorem lemma41_pathImage_continuousLift (hP : pathLength P ≠ ∞) :
    Continuous (fun z : range P =>
      (InternalSpace.mk z : InternalSpace (range P))) := by
  let f : Icc (0 : ℝ) 1 → range P := fun t => ⟨P.extend t, by
    rw [Path.extend_apply P t.property]
    exact mem_range_self t⟩
  have hfcont : Continuous f := by
    exact Continuous.subtype_mk (P.continuous_extend.comp continuous_subtype_val)
      (fun t => by
        change P.extend t ∈ range P
        rw [Path.extend_apply P t.property]
        exact mem_range_self t)
  have hfsurj : Function.Surjective f := by
    intro z
    obtain ⟨t, ht⟩ := z.property
    refine ⟨t, ?_⟩
    exact Subtype.ext (by simpa only [f, Path.extend_apply P t.property] using ht)
  have hfquot : Topology.IsQuotientMap f :=
    Topology.IsQuotientMap.of_surjective_continuous hfsurj hfcont
  apply hfquot.continuous_iff.mpr
  simpa only [Function.comp_def] using
    (continuous_internalLift_of_arc P.continuous_extend.continuousOn hP
      (by rw [P.image_extend_of_subset (by rfl)]))

/-- The intrinsic space of a finite length path image is compact. -/
theorem lemma41_pathImage_compactSpace (hP : pathLength P ≠ ∞) :
    CompactSpace (InternalSpace (range P)) := by
  let F : Icc (0 : ℝ) 1 → InternalSpace (range P) := fun t =>
    InternalSpace.mk ⟨P.extend t, by
      rw [Path.extend_apply P t.property]
      exact mem_range_self t⟩
  have hF : Continuous F :=
    continuous_internalLift_of_arc P.continuous_extend.continuousOn hP
      (by rw [P.image_extend_of_subset (by rfl)])
  have hsurj : Function.Surjective F := by
    intro z
    obtain ⟨t, ht⟩ := z.val_mem
    refine ⟨t, ?_⟩
    apply InternalSpace.val_injective
    change P.extend t = z.val
    rwa [Path.extend_apply P t.property]
  have hcompact : IsCompact (Set.univ : Set (InternalSpace (range P))) := by
    have hrange : range F = Set.univ := hsurj.range_eq
    simpa only [Set.image_univ, hrange] using (isCompact_univ.image hF)
  exact isCompact_univ_iff.mp hcompact

/-- The intrinsic metric on a finite length path image is a length metric. -/
theorem lemma41_pathImage_isLengthSpace (hP : pathLength P ≠ ∞) :
    IsLengthSpace (InternalSpace (range P)) := by
  intro a b ε hε
  have hfin : edist a b ≠ ∞ :=
    lemma41_pathImage_internal_finite P hP a.val_mem b.val_mem
  have hε0 : ENNReal.ofReal ε ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hε)
  have hlt : internalEDist (range P) a.val b.val <
      internalEDist (range P) a.val b.val + ENNReal.ofReal ε :=
    ENNReal.lt_add_right hfin hε0
  change (⨅ γ : {γ : Path a.val b.val // ∀ t, γ t ∈ range P}, pathLength γ.1) <
    internalEDist (range P) a.val b.val + ENNReal.ofReal ε at hlt
  obtain ⟨γ, hγlt⟩ := iInf_lt_iff.mp hlt
  let F : Path a b :=
    { toFun := fun t => (InternalSpace.mk ⟨γ.1 t, γ.2 t⟩ : InternalSpace (range P))
      continuous_toFun := by
        have hlift : Continuous (fun z : range P =>
            (InternalSpace.mk z : InternalSpace (range P))) :=
          lemma41_pathImage_continuousLift P hP
        exact hlift.comp (Continuous.subtype_mk γ.1.continuous (fun t => γ.2 t))
      source' := by apply InternalSpace.val_injective; exact γ.1.source
      target' := by apply InternalSpace.val_injective; exact γ.1.target }
  have hlen : pathLength F = pathLength γ.1 := by
    unfold pathLength
    rw [curveLength_internalSpace F.continuous_extend.continuousOn]
    apply curveLength_congr
    intro t ht
    change (F.extend t).val = γ.1.extend t
    rw [Path.extend_apply F ht, Path.extend_apply γ.1 ht]
    rfl
  exact ⟨F, hlen ▸ hγlt.le⟩

/-- A finite length path image contains an injective intrinsic geodesic between any two points. -/
theorem lemma41_exists_simple_in_pathImage (hP : pathLength P ≠ ∞)
    {a b : X} (ha : a ∈ range P) (hb : b ∈ range P) :
    ∃ Q : ℝ → X,
      let ℓ := (internalEDist (range P) a b).toReal
      ContinuousOn Q (Icc 0 ℓ) ∧ MapsTo Q (Icc 0 ℓ) (range P) ∧
      Q 0 = a ∧ Q ℓ = b ∧
      (∀ s ∈ Icc 0 ℓ, ∀ t ∈ Icc 0 ℓ,
        internalEDist (range P) (Q s) (Q t) = ENNReal.ofReal |t - s|) ∧
      InjOn Q (Icc 0 ℓ) := by
  let K := range P
  letI : MetricSpace (InternalSpace K) := EMetricSpace.toMetricSpace (by
    intro a b
    exact lemma41_pathImage_internal_finite P hP a.val_mem b.val_mem)
  haveI : CompactSpace (InternalSpace K) := lemma41_pathImage_compactSpace P hP
  let aa : InternalSpace K := InternalSpace.mk ⟨a, ha⟩
  let bb : InternalSpace K := InternalSpace.mk ⟨b, hb⟩
  let ℓ : ℝ := (internalEDist K a b).toReal
  have hd : dist aa bb = ℓ := rfl
  obtain ⟨Q, hQ0, hQ1, hQg, _, hQdist⟩ :=
    exists_isGeodesicCurve_unitSpeed (lemma41_pathImage_isLengthSpace P hP) aa bb
  let R : ℝ → X := InternalSpace.val ∘ Q
  have hRcont : ContinuousOn R (Icc 0 ℓ) := by
    rw [← hd]
    exact (internalSpace_val_lipschitz K).continuous.continuousOn.comp hQg.2.1
      (fun _ _ => mem_univ _)
  have hRK : MapsTo R (Icc 0 ℓ) K := fun t _ => (Q t).val_mem
  have hRdist : ∀ s ∈ Icc 0 ℓ, ∀ t ∈ Icc 0 ℓ,
      internalEDist K (R s) (R t) = ENNReal.ofReal |t - s| := by
    intro s hs t ht
    change edist (Q s) (Q t) = ENNReal.ofReal |t - s|
    rw [edist_dist, hQdist s (hd ▸ hs) t (hd ▸ ht)]
  refine ⟨R, hRcont, hRK, ?_, ?_, hRdist, intrinsic_geodesic_injOn hRK hRdist⟩
  · exact congrArg InternalSpace.val hQ0
  · change R ℓ = b
    rw [← hd]
    exact congrArg InternalSpace.val hQ1

/-- A finite length path contains an injective shortest subarc joining its endpoints. -/
theorem lemma41_exists_simple_connector (hP : pathLength P ≠ ∞) :
    ∃ Q : ℝ → X,
      let ℓ := (internalEDist (range P) x y).toReal
      ContinuousOn Q (Icc 0 ℓ) ∧ MapsTo Q (Icc 0 ℓ) (range P) ∧
      Q 0 = x ∧ Q ℓ = y ∧
      (∀ s ∈ Icc 0 ℓ, ∀ t ∈ Icc 0 ℓ,
        internalEDist (range P) (Q s) (Q t) = ENNReal.ofReal |t - s|) ∧
      InjOn Q (Icc 0 ℓ) :=
  lemma41_exists_simple_in_pathImage P hP ⟨0, P.source⟩ ⟨1, P.target⟩

/-- A shortest route to a closed target first meets it at its terminal point. The route stays
inside the image of the original finite-length path. -/
theorem lemma41_first_contact_closed (hP : pathLength P ≠ ∞)
    {C : Set X} (hC : IsClosed C) (hxC : x ∉ C) (hyC : y ∈ C) :
    ∃ z : X, z ∈ C ∩ range P ∧
      ∃ Q : ℝ → X,
        let ℓ := (internalEDist (range P) x z).toReal
        0 < ℓ ∧ ContinuousOn Q (Icc 0 ℓ) ∧
        MapsTo Q (Icc 0 ℓ) (range P) ∧ Q 0 = x ∧ Q ℓ = z ∧
        InjOn Q (Icc 0 ℓ) ∧
        (∀ r ∈ Icc 0 ℓ, r < ℓ → Q r ∉ C) ∧
        (∀ s ∈ Icc 0 ℓ, ∀ t ∈ Icc 0 ℓ,
          internalEDist (range P) (Q s) (Q t) = ENNReal.ofReal |t - s|) := by
  let K := range P
  letI : MetricSpace (InternalSpace K) := EMetricSpace.toMetricSpace (by
    intro a b
    exact lemma41_pathImage_internal_finite P hP a.val_mem b.val_mem)
  haveI : CompactSpace (InternalSpace K) := lemma41_pathImage_compactSpace P hP
  let a : InternalSpace K := InternalSpace.mk ⟨x, ⟨0, P.source⟩⟩
  let b : InternalSpace K := InternalSpace.mk ⟨y, ⟨1, P.target⟩⟩
  let T : Set (InternalSpace K) := {q | q.val ∈ C}
  have hTclosed : IsClosed T := hC.preimage (internalSpace_val_lipschitz K).continuous
  have hTcompact : IsCompact T := isCompact_univ.of_isClosed_subset hTclosed (subset_univ T)
  have hTnonempty : T.Nonempty := ⟨b, hyC⟩
  obtain ⟨z, hzT, hmin⟩ := hTcompact.exists_isMinOn hTnonempty
    ((continuous_const.dist continuous_id).continuousOn :
      ContinuousOn (fun q => dist a q) T)
  have hzx : z.val ∈ K := z.val_mem
  obtain ⟨Q, hQc, hQK, hQ0, hQ1, hQdist, hQinj⟩ :=
    lemma41_exists_simple_in_pathImage P hP (⟨0, P.source⟩ : x ∈ K) hzx
  let ℓ := (internalEDist K x z.val).toReal
  have hdist : dist a z = ℓ := rfl
  have hℓ : 0 < ℓ := by
    have hne : a ≠ z := by
      intro heq
      have hxz : x = z.val := congrArg InternalSpace.val heq
      exact hxC (hxz ▸ hzT)
    simpa only [← hdist] using dist_pos.mpr hne
  refine ⟨z.val, ⟨hzT, hzx⟩, Q, hℓ, hQc, hQK, hQ0, hQ1, hQinj, ?_, hQdist⟩
  intro r hr hrℓ hQrC
  let q : InternalSpace K := InternalSpace.mk ⟨Q r, hQK hr⟩
  have hqT : q ∈ T := hQrC
  have hminq : dist a z ≤ dist a q := hmin hqT
  have hdistq : dist a q = r := by
    change (internalEDist K x (Q r)).toReal = r
    rw [← hQ0, hQdist 0 (by exact ⟨le_rfl, hℓ.le⟩) r hr]
    simp only [sub_zero, abs_of_nonneg hr.1, ENNReal.toReal_ofReal hr.1]
  rw [hdist, hdistq] at hminq
  exact (not_lt_of_ge hminq) hrℓ

/-- An intrinsic unit-speed arc has finite ambient length. -/
theorem lemma41_intrinsic_arc_length {K : Set X} {Q : ℝ → X} {ℓ : ℝ}
    (hQdist : ∀ s ∈ Icc 0 ℓ, ∀ t ∈ Icc 0 ℓ,
      internalEDist K (Q s) (Q t) = ENNReal.ofReal |t - s|) :
    curveLength Q 0 ℓ ≤ ENNReal.ofReal ℓ := by
  have hLip : LipschitzOnWith 1 Q (Icc 0 ℓ) := by
    intro s hs t ht
    calc
      edist (Q s) (Q t) ≤ internalEDist K (Q s) (Q t) :=
        edist_le_internalEDist K (Q s) (Q t)
      _ = ENNReal.ofReal |t - s| := hQdist s hs t ht
      _ = (1 : ℝ≥0∞) * edist s t := by
        simp only [one_mul, edist_dist, Real.dist_eq, abs_sub_comm]
  have hvar := hLip.comp_eVariationOn_le
    (g := id) (s := Icc (0 : ℝ) ℓ) (t := Icc (0 : ℝ) ℓ)
    (fun _ h => h)
  simpa [curveLength, eVariationOn_id_Icc] using hvar

/-- Rescale an intrinsic geodesic to the unit interval for finite graph witnesses. -/
theorem lemma41_rescale_intrinsic_arc {K : Set X} {Q : ℝ → X} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hQc : ContinuousOn Q (Icc 0 ℓ))
    (hQK : MapsTo Q (Icc 0 ℓ) K) (hQinj : InjOn Q (Icc 0 ℓ))
    (hQdist : ∀ s ∈ Icc 0 ℓ, ∀ t ∈ Icc 0 ℓ,
      internalEDist K (Q s) (Q t) = ENNReal.ofReal |t - s|) :
    ∃ γ : ℝ → X, ContinuousOn γ (Icc 0 1) ∧ InjOn γ (Icc 0 1) ∧
      MapsTo γ (Icc 0 1) K ∧ γ 0 = Q 0 ∧ γ 1 = Q ℓ ∧
      curveLength γ 0 1 ≠ ∞ ∧ ∀ t, γ t = Q (ℓ * t) := by
  let φ : ℝ → ℝ := fun t => ℓ * t
  have hφc : Continuous φ := continuous_const.mul continuous_id
  have hφmem : MapsTo φ (Icc (0 : ℝ) 1) (Icc 0 ℓ) := by
    intro t ht
    exact ⟨mul_nonneg hℓ.le ht.1, mul_le_of_le_one_right hℓ.le ht.2⟩
  have hφmono : MonotoneOn φ (Icc (0 : ℝ) 1) := by
    intro a _ b _ hab
    exact mul_le_mul_of_nonneg_left hab hℓ.le
  let γ : ℝ → X := Q ∘ φ
  have hγc : ContinuousOn γ (Icc 0 1) :=
    hQc.comp hφc.continuousOn hφmem
  have hγinj : InjOn γ (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    have hφeq : φ s = φ t := hQinj (hφmem hs) (hφmem ht) hst
    exact mul_left_cancel₀ hℓ.ne' hφeq
  have hγlen : curveLength γ 0 1 ≠ ∞ := by
    have hEq : curveLength γ 0 1 = curveLength Q 0 ℓ := by
      simpa only [γ, φ, mul_zero, mul_one] using
        (curveLength_comp_of_continuousOn_monotoneOn Q
          (by norm_num : (0 : ℝ) ≤ 1) hφc.continuousOn hφmono)
    rw [hEq]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lemma41_intrinsic_arc_length hQdist)
  refine ⟨γ, hγc, hγinj, ?_, ?_, ?_, hγlen, ?_⟩
  · intro t ht
    exact hQK (hφmem ht)
  · simp only [γ, φ, Function.comp_apply, mul_zero]
  · simp only [γ, φ, Function.comp_apply, mul_one]
  · intro t; rfl

/-- A finite rectifiable path to a closed set contains a simple rectifiable first-contact arc. -/
theorem lemma41_first_contact_arc (hP : pathLength P ≠ ∞)
    {C : Set X} (hC : IsClosed C) (hxC : x ∉ C) (hyC : y ∈ C) :
    ∃ z ∈ C ∩ range P, ∃ γ : ℝ → X,
      ContinuousOn γ (Icc 0 1) ∧ InjOn γ (Icc 0 1) ∧
      MapsTo γ (Icc 0 1) (range P) ∧
      γ 0 = x ∧ γ 1 = z ∧ curveLength γ 0 1 ≠ ∞ ∧
      ∀ t ∈ Icc (0 : ℝ) 1, t < 1 → γ t ∉ C := by
  obtain ⟨z, hz, Q, hℓ, hQc, hQK, hQ0, hQ1, hQinj, hQavoid, hQdist⟩ :=
    lemma41_first_contact_closed P hP hC hxC hyC
  let ℓ := (internalEDist (range P) x z).toReal
  obtain ⟨γ, hγc, hγinj, hγK, hγ0, hγ1, hγlen, hγeq⟩ :=
    lemma41_rescale_intrinsic_arc hℓ hQc hQK hQinj hQdist
  refine ⟨z, hz, γ, hγc, hγinj, hγK, hγ0.trans hQ0,
    hγ1.trans hQ1, hγlen, ?_⟩
  intro t ht ht1
  have htℓ : ℓ * t ∈ Icc (0 : ℝ) ℓ :=
    ⟨mul_nonneg hℓ.le ht.1, mul_le_of_le_one_right hℓ.le ht.2⟩
  have htlt : ℓ * t < ℓ := by nlinarith
  rw [hγeq]
  exact hQavoid (ℓ * t) htℓ htlt

end HigherDimLQGMetric
