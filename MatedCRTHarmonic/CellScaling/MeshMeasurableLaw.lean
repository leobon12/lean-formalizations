import MatedCRTHarmonic.CellScaling.MeshMeasurablePrefix

/-!
# Candidate-state prefix masses

Every finite candidate-state string is a valid graph-state prefix precisely when its dart codes
are active. Valid strings decode to actual graph states; their cylinder masses are the measurable
products of `MeshMeasurableWalk`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRTHarmonic.CellScaling

def meshGridCodeValid (ε : ℝ) (ω : MatedCRT.Path2) : MeshGridStateCode → Prop
  | Sum.inl _ => True
  | Sum.inr d => MatedCRT.edgePredicate ε ω d.1 = true

def meshGridCodePrefixValid (ε : ℝ) (ω : MatedCRT.Path2)
    (n : ℕ) (s : ℕ → MeshGridStateCode) : Prop :=
  ∀ i ≤ n, meshGridCodeValid ε ω (s i)

theorem measurableSet_meshGridCodePrefixValid (ε : ℝ)
    (n : ℕ) (s : ℕ → MeshGridStateCode) :
    MeasurableSet {ω : MatedCRT.Path2 | meshGridCodePrefixValid ε ω n s} := by
  classical
  rw [show {ω : MatedCRT.Path2 | meshGridCodePrefixValid ε ω n s} =
      ⋂ i : ℕ, {ω | i ≤ n → meshGridCodeValid ε ω (s i)} by
        ext ω
        simp [meshGridCodePrefixValid]]
  apply MeasurableSet.iInter
  intro i
  by_cases hi : i ≤ n
  · cases hcode : s i with
    | inl x => simp [meshGridCodeValid, hi, hcode]
    | inr d =>
      have hm := (MatedCRT.matedCRT_edgePredicate_measurable_holds ε).eval (a := d.1)
      have hEq : {ω : MatedCRT.Path2 | i ≤ n → meshGridCodeValid ε ω (Sum.inr d)} =
          {ω | MatedCRT.edgePredicate ε ω d.1 = true} := by
        ext ω
        simp [meshGridCodeValid, hi]
      rw [hEq]
      exact (measurableSet_singleton true).preimage hm
  · simp [hi]

noncomputable def meshGridDecodeCode (ε : ℝ) (ω : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite ε ω) : MeshGridStateCode →
      (MatedCRT.graph ε ω hlf).State
  | Sum.inl x => Sum.inl x
  | Sum.inr d => by
      classical
      exact if h : MatedCRT.IsEdge ε ω d.1 then Sum.inr (⟨d.1, h⟩, d.2) else Sum.inl 0

theorem meshGridDecodeCode_encode (ε : ℝ) (ω : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite ε ω)
    (u : (MatedCRT.graph ε ω hlf).State) :
    meshGridDecodeCode ε ω hlf (meshGridEncodeMatedState u) = u := by
  cases u with
  | inl x => rfl
  | inr d =>
    rcases d with ⟨⟨e, he⟩, b⟩
    simp [meshGridDecodeCode, meshGridEncodeMatedState, he, Subtype.mk.injEq]
    rfl

theorem meshGridEncode_decodeCode (ε : ℝ) (ω : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite ε ω) (u : MeshGridStateCode)
    (hu : meshGridCodeValid ε ω u) :
    meshGridEncodeMatedState (meshGridDecodeCode ε ω hlf u) = u := by
  cases u with
  | inl x => rfl
  | inr d =>
    have he : MatedCRT.IsEdge ε ω d.1 := by
      simpa [meshGridCodeValid, MatedCRT.edgePredicate] using hu
    simp [meshGridDecodeCode, meshGridEncodeMatedState, he]

theorem meshGridCodeValid_encode (ε : ℝ) (ω : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite ε ω)
    (u : (MatedCRT.graph ε ω hlf).State) :
    meshGridCodeValid ε ω (meshGridEncodeMatedState u) := by
  cases u with
  | inl x => trivial
  | inr d =>
    rcases d with ⟨⟨e, he⟩, b⟩
    simpa [meshGridCodeValid, meshGridEncodeMatedState, MatedCRT.edgePredicate] using he

/-- A valid fixed code prefix has the cylinder mass computed by its measurable prefix product. -/
theorem meshGridWalkLaw_codeCylinder (ε : ℝ) (ω : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite ε ω) (x : ℤ)
    (n : ℕ) (s : ℕ → MeshGridStateCode)
    (hvalid : meshGridCodePrefixValid ε ω n s) :
    (MatedCRT.graph ε ω hlf).walkLaw x
      {path | ∀ i ≤ n, meshGridEncodeMatedState (path i) = s i} =
      meshGridCodePrefixWeight ε x s n ω := by
  let t : ℕ → (MatedCRT.graph ε ω hlf).State :=
    fun i => meshGridDecodeCode ε ω hlf (s i)
  have hset : {path : ℕ → (MatedCRT.graph ε ω hlf).State |
      ∀ i ≤ n, meshGridEncodeMatedState (path i) = s i} =
      {path | ∀ i ≤ n, path i = t i} := by
    ext path
    constructor
    · intro hp i hi
      have h := congrArg (meshGridDecodeCode ε ω hlf) (hp i hi)
      simpa [t, meshGridDecodeCode_encode] using h
    · intro hp i hi
      rw [hp i hi]
      exact meshGridEncode_decodeCode ε ω hlf (s i) (hvalid i hi)
  rw [hset, meshGridWalkLaw_stateCylinder]
  have hs (i : ℕ) (hi : i ≤ n) : meshGridEncodeMatedState (t i) = s i :=
    meshGridEncode_decodeCode ε ω hlf (s i) (hvalid i hi)
  unfold meshGridCodePrefixWeight
  change (if meshGridEncodeMatedState (t 0) = Sum.inl x then
      ∏ i ∈ Finset.range n,
        meshGridCodeTransitionWeight ε (meshGridEncodeMatedState (t i))
          (meshGridEncodeMatedState (t (i + 1))) ω else 0) =
    if s 0 = Sum.inl x then
      ∏ i ∈ Finset.range n, meshGridCodeTransitionWeight ε (s i) (s (i + 1)) ω else 0
  rw [hs 0 (Nat.zero_le n)]
  by_cases hstart : s 0 = Sum.inl x
  · simp only [if_pos hstart]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hs i (Nat.le_of_lt (Finset.mem_range.mp hi)),
      hs (i + 1) (Nat.succ_le_iff.mpr (Finset.mem_range.mp hi))]
  · simp [hstart]

theorem meshGridWalkLaw_codeCylinder_invalid (ε : ℝ) (ω : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite ε ω) (x : ℤ)
    (n : ℕ) (s : ℕ → MeshGridStateCode)
    (hv : ¬meshGridCodePrefixValid ε ω n s) :
    (MatedCRT.graph ε ω hlf).walkLaw x
      {path | ∀ i ≤ n, meshGridEncodeMatedState (path i) = s i} = 0 := by
  have hset : {path : ℕ → (MatedCRT.graph ε ω hlf).State |
      ∀ i ≤ n, meshGridEncodeMatedState (path i) = s i} = ∅ := by
    ext path
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hp
    apply hv
    intro i hi
    rw [← hp i hi]
    exact meshGridCodeValid_encode ε ω hlf (path i)
  rw [hset, measure_empty]

noncomputable def meshGridCodePrefixTerm (ε : ℝ) (x : ℤ) (z : ℂ) (r : ℝ)
    (n : ℕ) (s : ℕ → MeshGridStateCode)
    (d : MatedCRT.Path2 × C(ℝ, ℂ)) : ℝ≥0∞ := by
  classical
  exact if meshGridCodePrefixValid ε d.1 n s ∧ meshGridCodePrefixGeometry ε z r n s d then
    meshGridCodePrefixWeight ε x s n d.1 else 0

theorem measurable_meshGridCodePrefixTerm (ε : ℝ) (hε : 0 ≤ ε)
    (x : ℤ) (z : ℂ) (r : ℝ) (n : ℕ) (s : ℕ → MeshGridStateCode) :
    Measurable (meshGridCodePrefixTerm ε x z r n s) := by
  classical
  have hv : MeasurableSet {d : MatedCRT.Path2 × C(ℝ, ℂ) |
      meshGridCodePrefixValid ε d.1 n s} :=
    (measurableSet_meshGridCodePrefixValid ε n s).preimage measurable_fst
  have hg := measurableSet_meshGridCodePrefixGeometry ε hε z r n s
  have hw : Measurable (fun d : MatedCRT.Path2 × C(ℝ, ℂ) =>
      meshGridCodePrefixWeight ε x s n d.1) :=
    (measurable_meshGridCodePrefixWeight ε x s n).comp measurable_fst
  unfold meshGridCodePrefixTerm
  exact Measurable.ite (hv.inter hg) hw measurable_const

abbrev MeshGridPrefixIndex := Σ n : ℕ, Fin (n + 1) → MeshGridStateCode

def meshGridPrefixIndexSeq (j : MeshGridPrefixIndex) (i : ℕ) : MeshGridStateCode :=
  j.2 ⟨min i j.1, by omega⟩

theorem meshGridPrefixIndexSeq_get (j : MeshGridPrefixIndex) (i : ℕ) (hi : i ≤ j.1) :
    meshGridPrefixIndexSeq j i = j.2 ⟨i, by omega⟩ := by
  simp [meshGridPrefixIndexSeq, Nat.min_eq_left hi]

noncomputable def meshGridCodeAnnularProbability (ε : ℝ) (x : ℤ)
    (z : ℂ) (r : ℝ) (d : MatedCRT.Path2 × C(ℝ, ℂ)) : ℝ≥0∞ :=
  ∑' j : MeshGridPrefixIndex,
    meshGridCodePrefixTerm ε x z r j.1 (meshGridPrefixIndexSeq j) d

theorem measurable_meshGridCodeAnnularProbability (ε : ℝ) (hε : 0 ≤ ε)
    (x : ℤ) (z : ℂ) (r : ℝ) :
    Measurable (meshGridCodeAnnularProbability ε x z r) := by
  unfold meshGridCodeAnnularProbability
  apply Measurable.ennreal_tsum
  intro j
  exact measurable_meshGridCodePrefixTerm ε hε x z r j.1 (meshGridPrefixIndexSeq j)

def meshGridCodePrefixEvent (ε : ℝ) (ω : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite ε ω) (η : C(ℝ, ℂ))
    (z : ℂ) (r : ℝ) (j : MeshGridPrefixIndex) :
    Set (ℕ → (MatedCRT.graph ε ω hlf).State) :=
  {path | meshGridCodePrefixGeometry ε z r j.1 (meshGridPrefixIndexSeq j) (ω, η) ∧
    ∀ i ≤ j.1, meshGridEncodeMatedState (path i) = meshGridPrefixIndexSeq j i}

theorem measurableSet_meshGridCodePrefixEvent (ε : ℝ) (ω : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite ε ω) (η : C(ℝ, ℂ))
    (z : ℂ) (r : ℝ) (j : MeshGridPrefixIndex) :
    MeasurableSet (meshGridCodePrefixEvent ε ω hlf η z r j) := by
  classical
  letI : MeasurableSpace MeshGridStateCode := ⊤
  by_cases hg : meshGridCodePrefixGeometry ε z r j.1 (meshGridPrefixIndexSeq j) (ω, η)
  · have hcyl : MeasurableSet
        {path : ℕ → (MatedCRT.graph ε ω hlf).State |
          ∀ i ≤ j.1, meshGridEncodeMatedState (path i) = meshGridPrefixIndexSeq j i} := by
      rw [show {path : ℕ → (MatedCRT.graph ε ω hlf).State |
          ∀ i ≤ j.1, meshGridEncodeMatedState (path i) = meshGridPrefixIndexSeq j i} =
        ⋂ i : ℕ, {path | i ≤ j.1 →
          meshGridEncodeMatedState (path i) = meshGridPrefixIndexSeq j i} by ext path; simp]
      apply MeasurableSet.iInter
      intro i
      by_cases hi : i ≤ j.1
      · have hm : Measurable (fun path : ℕ → (MatedCRT.graph ε ω hlf).State =>
            meshGridEncodeMatedState (path i)) :=
          Measurable.of_discrete.comp (measurable_pi_apply i)
        have hEq : {path : ℕ → (MatedCRT.graph ε ω hlf).State |
            i ≤ j.1 → meshGridEncodeMatedState (path i) = meshGridPrefixIndexSeq j i} =
            (fun path => meshGridEncodeMatedState (path i)) ⁻¹'
              {meshGridPrefixIndexSeq j i} := by
          ext path
          simp [hi]
        rw [hEq]
        exact (measurableSet_singleton (meshGridPrefixIndexSeq j i)).preimage hm
      · simp [hi]
    simpa [meshGridCodePrefixEvent, hg] using hcyl
  · simp [meshGridCodePrefixEvent, hg]

theorem meshGridCodePrefixEvent_mass (ε : ℝ) (ω : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite ε ω) (η : C(ℝ, ℂ))
    (x : ℤ) (z : ℂ) (r : ℝ) (j : MeshGridPrefixIndex) :
    (MatedCRT.graph ε ω hlf).walkLaw x
      (meshGridCodePrefixEvent ε ω hlf η z r j) =
      meshGridCodePrefixTerm ε x z r j.1 (meshGridPrefixIndexSeq j) (ω, η) := by
  classical
  by_cases hg : meshGridCodePrefixGeometry ε z r j.1 (meshGridPrefixIndexSeq j) (ω, η)
  · have hset : meshGridCodePrefixEvent ε ω hlf η z r j =
        {path | ∀ i ≤ j.1, meshGridEncodeMatedState (path i) = meshGridPrefixIndexSeq j i} := by
      ext path
      simp [meshGridCodePrefixEvent, hg]
    rw [hset]
    by_cases hv : meshGridCodePrefixValid ε ω j.1 (meshGridPrefixIndexSeq j)
    · rw [meshGridWalkLaw_codeCylinder ε ω hlf x j.1 (meshGridPrefixIndexSeq j) hv]
      simp [meshGridCodePrefixTerm, hv, hg]
    · rw [meshGridWalkLaw_codeCylinder_invalid ε ω hlf x j.1 (meshGridPrefixIndexSeq j) hv]
      simp [meshGridCodePrefixTerm, hv]
  · have hset : meshGridCodePrefixEvent ε ω hlf η z r j = ∅ := by
      ext path
      simp [meshGridCodePrefixEvent, hg]
    rw [hset, measure_empty]
    simp [meshGridCodePrefixTerm, hg]

theorem meshGridAnnularEvent_eq_iUnion_prefixEvent (ε : ℝ) (ω : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite ε ω) (η : C(ℝ, ℂ))
    (z : ℂ) (r : ℝ) :
    {path : ℕ → (MatedCRT.graph ε ω hlf).State |
      (MatedCRT.graph ε ω hlf).AnnularEvent (meshCells ε η) z r
        ((MatedCRT.graph ε ω hlf).vertexPath path)} =
      ⋃ j : MeshGridPrefixIndex, meshGridCodePrefixEvent ε ω hlf η z r j := by
  ext path
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, meshGridCodePrefixEvent]
  constructor
  · intro h
    obtain ⟨n, hg⟩ := (meshGridAnnularEvent_iff_exists_codePrefixGeometry
      ε ω hlf η z r path).mp h
    let j : MeshGridPrefixIndex := ⟨n, fun i => meshGridEncodeMatedState (path i.1)⟩
    have hp (i : ℕ) (hi : i ≤ n) :
        meshGridEncodeMatedState (path i) = meshGridPrefixIndexSeq j i := by
      simp [j, meshGridPrefixIndexSeq_get, hi]
    refine ⟨j, ?_, fun i hi => hp i hi⟩
    exact (meshGridCodePrefixGeometry_congr ε z r n
      (fun i => meshGridEncodeMatedState (path i)) (meshGridPrefixIndexSeq j)
      hp (ω, η)).mp hg
  · rintro ⟨j, hg, hp⟩
    have hg' : meshGridCodePrefixGeometry ε z r j.1
        (fun i => meshGridEncodeMatedState (path i)) (ω, η) :=
      (meshGridCodePrefixGeometry_congr ε z r j.1
        (meshGridPrefixIndexSeq j) (fun i => meshGridEncodeMatedState (path i))
        (fun i hi => (hp i hi).symm) (ω, η)).mp hg
    exact (meshGridAnnularEvent_iff_exists_codePrefixGeometry
      ε ω hlf η z r path).mpr ⟨j.1, hg'⟩

theorem meshGridCodePrefixEvent_pairwiseDisjoint (ε : ℝ) (ω : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite ε ω) (η : C(ℝ, ℂ))
    (z : ℂ) (r : ℝ) :
    Pairwise (fun j k : MeshGridPrefixIndex =>
      Disjoint (meshGridCodePrefixEvent ε ω hlf η z r j)
        (meshGridCodePrefixEvent ε ω hlf η z r k)) := by
  intro j k hne
  apply Set.disjoint_left.mpr
  intro path hj hk
  change meshGridCodePrefixGeometry ε z r j.1 (meshGridPrefixIndexSeq j) (ω, η) ∧
    (∀ i ≤ j.1, meshGridEncodeMatedState (path i) = meshGridPrefixIndexSeq j i) at hj
  change meshGridCodePrefixGeometry ε z r k.1 (meshGridPrefixIndexSeq k) (ω, η) ∧
    (∀ i ≤ k.1, meshGridEncodeMatedState (path i) = meshGridPrefixIndexSeq k i) at hk
  have hgj : meshGridCodePrefixGeometry ε z r j.1
      (fun i => meshGridEncodeMatedState (path i)) (ω, η) :=
    (meshGridCodePrefixGeometry_congr ε z r j.1 (meshGridPrefixIndexSeq j)
      (fun i => meshGridEncodeMatedState (path i))
      (fun i hi => (hj.2 i hi).symm) (ω, η)).mp hj.1
  have hgk : meshGridCodePrefixGeometry ε z r k.1
      (fun i => meshGridEncodeMatedState (path i)) (ω, η) :=
    (meshGridCodePrefixGeometry_congr ε z r k.1 (meshGridPrefixIndexSeq k)
      (fun i => meshGridEncodeMatedState (path i))
      (fun i hi => (hk.2 i hi).symm) (ω, η)).mp hk.1
  have hnm : j.1 = k.1 := meshGridCodePrefixGeometry_unique ε z r
    (fun i => meshGridEncodeMatedState (path i)) (ω, η) hgj hgk
  cases j with
  | mk n f =>
    cases k with
    | mk m g =>
      dsimp at hnm
      subst m
      have hfg : f = g := by
        funext i
        calc
          f i = meshGridPrefixIndexSeq ⟨n, f⟩ i.1 :=
            (meshGridPrefixIndexSeq_get ⟨n, f⟩ i.1 (Nat.lt_succ_iff.mp i.2)).symm
          _ = meshGridEncodeMatedState (path i.1) := (hj.2 i.1 (Nat.lt_succ_iff.mp i.2)).symm
          _ = meshGridPrefixIndexSeq ⟨n, g⟩ i.1 := hk.2 i.1 (Nat.lt_succ_iff.mp i.2)
          _ = g i := meshGridPrefixIndexSeq_get ⟨n, g⟩ i.1 (Nat.lt_succ_iff.mp i.2)
      exact hne (congrArg (Sigma.mk n) hfg)

/-- The annular-event walk probability is the countable sum of its selected measurable
first-exit prefix weights. -/
theorem meshGridCodeAnnularProbability_eq_walkLaw (ε : ℝ) (ω : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite ε ω) (η : C(ℝ, ℂ))
    (x : ℤ) (z : ℂ) (r : ℝ) :
    meshGridCodeAnnularProbability ε x z r (ω, η) =
      (MatedCRT.graph ε ω hlf).walkLaw x
        {path | (MatedCRT.graph ε ω hlf).AnnularEvent (meshCells ε η) z r
          ((MatedCRT.graph ε ω hlf).vertexPath path)} := by
  rw [meshGridAnnularEvent_eq_iUnion_prefixEvent ε ω hlf η z r,
    measure_iUnion (meshGridCodePrefixEvent_pairwiseDisjoint ε ω hlf η z r)
      (measurableSet_meshGridCodePrefixEvent ε ω hlf η z r)]
  simp_rw [meshGridCodePrefixEvent_mass ε ω hlf η x z r]
  rfl

end MatedCRTHarmonic.CellScaling
