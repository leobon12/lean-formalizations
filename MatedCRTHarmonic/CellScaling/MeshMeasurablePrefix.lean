import MatedCRTHarmonic.CellScaling.MeshMeasurableDisconnect

/-!
# Borel first-exit prefix conditions

The conditions on a fixed state-code prefix combine cell hits, cell containment, and graph
separation. Only finitely many prefix positions occur; the separation condition is a countable
intersection over all finite graph walks.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric

namespace MatedCRTHarmonic.CellScaling

def meshGridCodePrefixGeometry (ε : ℝ) (z : ℂ) (r : ℝ)
    (n : ℕ) (s : ℕ → MeshGridStateCode)
    (d : MatedCRT.Path2 × C(ℝ, ℂ)) : Prop :=
  (∀ i < n, (meshCells ε d.2 (meshGridStateVertexCode (s i)) ∩
    annulus z (r / 2) (3 * r / 2)).Nonempty) ∧
  ¬(meshCells ε d.2 (meshGridStateVertexCode (s n)) ∩
    annulus z (r / 2) (3 * r / 2)).Nonempty ∧
  meshGridCodeDisconnects ε d.1
    {y | ∃ i < n, meshGridStateVertexCode (s i) = y}
    (verticesMeeting (meshCells ε d.2) (sphere z (3 * r / 4)))
    (verticesMeeting (meshCells ε d.2) (sphere z (5 * r / 4))) ∧
  (∀ i ≤ n, meshCells ε d.2 (meshGridStateVertexCode (s i)) ⊆
    annulus z (r / 3) (5 * r / 3))

/-- For every fixed state-code prefix, all first-exit geometric and graph-separation
conditions are Borel in the path/curve data. -/
theorem measurableSet_meshGridCodePrefixGeometry (ε : ℝ) (hε : 0 ≤ ε)
    (z : ℂ) (r : ℝ) (n : ℕ) (s : ℕ → MeshGridStateCode) :
    MeasurableSet {d : MatedCRT.Path2 × C(ℝ, ℂ) |
      meshGridCodePrefixGeometry ε z r n s d} := by
  classical
  let hit (i : ℕ) : Set (MatedCRT.Path2 × C(ℝ, ℂ)) :=
    {d | (meshCells ε d.2 (meshGridStateVertexCode (s i)) ∩
      annulus z (r / 2) (3 * r / 2)).Nonempty}
  have hhit (i : ℕ) : MeasurableSet (hit i) :=
    measurable_meshCell_meets_annulus Prod.snd measurable_snd hε
      (meshGridStateVertexCode (s i)) z (r / 2) (3 * r / 2)
  have hpre : MeasurableSet {d | ∀ i < n, d ∈ hit i} := by
    rw [show {d : MatedCRT.Path2 × C(ℝ, ℂ) | ∀ i < n, d ∈ hit i} =
      ⋂ i : ℕ, {d | i < n → d ∈ hit i} by ext d; simp]
    apply MeasurableSet.iInter
    intro i
    by_cases hi : i < n
    · simpa [hi] using hhit i
    · simp [hi]
  have hdisc : MeasurableSet {d : MatedCRT.Path2 × C(ℝ, ℂ) |
      meshGridCodeDisconnects ε d.1
        {y | ∃ i < n, meshGridStateVertexCode (s i) = y}
        (verticesMeeting (meshCells ε d.2) (sphere z (3 * r / 4)))
        (verticesMeeting (meshCells ε d.2) (sphere z (5 * r / 4)))} := by
    apply measurableSet_meshGridCodeDisconnects ε Prod.fst measurable_fst
    · intro a
      exact measurable_meshCell_meets_sphere Prod.snd measurable_snd hε a z (3 * r / 4)
    · intro b
      exact measurable_meshCell_meets_sphere Prod.snd measurable_snd hε b z (5 * r / 4)
  have hcontain : MeasurableSet {d : MatedCRT.Path2 × C(ℝ, ℂ) |
      ∀ i ≤ n, meshCells ε d.2 (meshGridStateVertexCode (s i)) ⊆
        annulus z (r / 3) (5 * r / 3)} := by
    rw [show {d : MatedCRT.Path2 × C(ℝ, ℂ) |
      ∀ i ≤ n, meshCells ε d.2 (meshGridStateVertexCode (s i)) ⊆
        annulus z (r / 3) (5 * r / 3)} =
      ⋂ i : ℕ, {d | i ≤ n → meshCells ε d.2 (meshGridStateVertexCode (s i)) ⊆
        annulus z (r / 3) (5 * r / 3)} by ext d; simp]
    apply MeasurableSet.iInter
    intro i
    by_cases hi : i ≤ n
    · simpa [hi] using measurable_meshCell_subset_annulus Prod.snd measurable_snd hε
        (meshGridStateVertexCode (s i)) z (r / 3) (5 * r / 3)
    · simp [hi]
  change MeasurableSet ({d | (∀ i < n, d ∈ hit i) ∧ d ∉ hit n ∧
    meshGridCodeDisconnects ε d.1
      {y | ∃ i < n, meshGridStateVertexCode (s i) = y}
      (verticesMeeting (meshCells ε d.2) (sphere z (3 * r / 4)))
      (verticesMeeting (meshCells ε d.2) (sphere z (5 * r / 4))) ∧
    (∀ i ≤ n, meshCells ε d.2 (meshGridStateVertexCode (s i)) ⊆
      annulus z (r / 3) (5 * r / 3))})
  have hnot : MeasurableSet {d : MatedCRT.Path2 × C(ℝ, ℂ) | d ∉ hit n} := by
    change MeasurableSet (hit n)ᶜ
    exact (hhit n).compl
  simpa only [Set.setOf_and] using hpre.inter (hnot.inter (hdisc.inter hcontain))

/-- The frozen annular event is exactly the union over its finite first-exit prefixes. -/
theorem meshGridAnnularEvent_iff_exists_codePrefixGeometry (ε : ℝ)
    (ω : MatedCRT.Path2) (hlf : MatedCRT.IsLocallyFinite ε ω)
    (η : C(ℝ, ℂ)) (z : ℂ) (r : ℝ)
    (path : ℕ → (MatedCRT.graph ε ω hlf).State) :
    (MatedCRT.graph ε ω hlf).AnnularEvent (meshCells ε η) z r
      ((MatedCRT.graph ε ω hlf).vertexPath path) ↔
    ∃ n : ℕ, meshGridCodePrefixGeometry ε z r n
      (fun i => meshGridEncodeMatedState (path i)) (ω, η) := by
  let G := MatedCRT.graph ε ω hlf
  let J := meshCells ε η
  let X := G.vertexPath path
  have hv (i : ℕ) : meshGridStateVertexCode (meshGridEncodeMatedState (path i)) = X i := by
    exact meshGridStateVertexCode_encode (path i)
  have hdisc (n : ℕ) :
      meshGridCodeDisconnects ε ω
        {y | ∃ i < n, X i = y}
        (verticesMeeting J (sphere z (3 * r / 4)))
        (verticesMeeting J (sphere z (5 * r / 4))) ↔
      G.Disconnects {y | ∃ i < n, X i = y}
        (verticesMeeting J (sphere z (3 * r / 4)))
        (verticesMeeting J (sphere z (5 * r / 4))) := by
    exact meshGridCodeDisconnects_iff_graphDisconnects ε ω hlf
      {y | ∃ i < n, X i = y}
      (verticesMeeting J (sphere z (3 * r / 4)))
      (verticesMeeting J (sphere z (5 * r / 4)))
  have hprefix (n : ℕ) :
      meshGridCodePrefixGeometry ε z r n
          (fun i => meshGridEncodeMatedState (path i)) (ω, η) ↔
        Markov.hitTime (verticesMeeting J (annulus z (r / 2) (3 * r / 2)))ᶜ X = n ∧
          G.Disconnects {y | ∃ i < n, X i = y}
            (verticesMeeting J (sphere z (3 * r / 4)))
            (verticesMeeting J (sphere z (5 * r / 4))) ∧
          ∀ i ≤ n, J (X i) ⊆ annulus z (r / 3) (5 * r / 3) := by
    rw [meshGridCodePrefixGeometry, Markov.hitTime_eq_coe_iff]
    simp only [hv, J, X, Set.mem_compl_iff, verticesMeeting, Set.mem_setOf_eq, not_not]
    constructor
    · rintro ⟨hbefore, hexit, hsep, hstay⟩
      exact ⟨⟨hexit, hbefore⟩, (hdisc n).mp hsep, hstay⟩
    · rintro ⟨⟨hexit, hbefore⟩, hsep, hstay⟩
      exact ⟨hbefore, hexit, (hdisc n).mpr hsep, hstay⟩
  simp only [LFMultigraph.AnnularEvent]
  constructor
  · rintro ⟨n, hn, hd, hs⟩
    exact ⟨n, (hprefix n).mpr ⟨hn, hd, hs⟩⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, (hprefix n).mp hn⟩

theorem meshGridCodePrefixGeometry_congr (ε : ℝ) (z : ℂ) (r : ℝ)
    (n : ℕ) (s t : ℕ → MeshGridStateCode)
    (h : ∀ i ≤ n, s i = t i) (d : MatedCRT.Path2 × C(ℝ, ℂ)) :
    meshGridCodePrefixGeometry ε z r n s d ↔
      meshGridCodePrefixGeometry ε z r n t d := by
  have hU : {y | ∃ i < n, meshGridStateVertexCode (s i) = y} =
      {y | ∃ i < n, meshGridStateVertexCode (t i) = y} := by
    ext y
    constructor
    · rintro ⟨i, hi, hy⟩
      exact ⟨i, hi, by rw [← h i (Nat.le_of_lt hi)]; exact hy⟩
    · rintro ⟨i, hi, hy⟩
      exact ⟨i, hi, by rw [h i (Nat.le_of_lt hi)]; exact hy⟩
  unfold meshGridCodePrefixGeometry
  constructor
  · rintro ⟨hb, he, hd, hs⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [← h i (Nat.le_of_lt hi)]
      exact hb i hi
    · rw [← h n le_rfl]
      exact he
    · rw [← hU]
      exact hd
    · intro i hi
      rw [← h i hi]
      exact hs i hi
  · rintro ⟨hb, he, hd, hs⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [h i (Nat.le_of_lt hi)]
      exact hb i hi
    · rw [h n le_rfl]
      exact he
    · rw [hU]
      exact hd
    · intro i hi
      rw [h i hi]
      exact hs i hi

theorem meshGridCodePrefixGeometry_unique (ε : ℝ) (z : ℂ) (r : ℝ)
    (s : ℕ → MeshGridStateCode) (d : MatedCRT.Path2 × C(ℝ, ℂ))
    {n m : ℕ} (hn : meshGridCodePrefixGeometry ε z r n s d)
    (hm : meshGridCodePrefixGeometry ε z r m s d) : n = m := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hn.2.1 (hm.1 n hlt)
  · exact hm.2.1 (hn.1 m hgt)

end MatedCRTHarmonic.CellScaling
