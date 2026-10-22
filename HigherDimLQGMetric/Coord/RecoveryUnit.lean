import HigherDimLQGMetric.Coord.RecoveryChain

/-! # Quantitative recovery of an arc-length parametrized curve -/

set_option autoImplicit false

noncomputable section

open Set Filter Topology LQGMetric.MetricGeometry BoundedContinuousFunction unitInterval
open scoped ENNReal

namespace HigherDimLQGMetric

/-- Lemma 2.4 for a source curve already parametrized by its old coordinate
length.  The old output path is the synchronized parametrization of `P`. -/
theorem lemma24_unitSpeed
    {X : Type*} [MetricSpace X]
    (ρ ρ' : X × X → ℝ) (hρ : IsCoordinate ρ) (hρ' : IsCoordinate ρ')
    (w : X → ℝ) {K O : Set X} (hKO : K ⊆ closure O)
    {L δ e δloc χ Ω M : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (he : 0 ≤ e) (heδ : e ≤ δ) (hδloc : 2 * δ < δloc)
    (hχ : 0 ≤ χ) (hΩ : 0 ≤ Ω) (hΩM : Ω ≤ M)
    (P : ℝ → X) (hP : ContinuousOn P (Icc 0 L))
    (hPK : ∀ t ∈ Icc 0 L, P t ∈ K)
    (hunit : ∀ a ∈ Icc 0 L, ∀ b ∈ Icc 0 L, a ≤ b →
      curveLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) P a b =
        ENNReal.ofReal (b - a))
    (hclose : ∀ u ∈ closure O, ∀ v ∈ closure O,
      |ρ (u, v) - ρ' (u, v)| ≤ e)
    (hmod : ∀ u ∈ closure O, ∀ v ∈ closure O,
      ρ (u, v) ≤ 2 * δ → dist u v ≤ χ)
    (hmod' : ∀ u ∈ closure O, ∀ v ∈ closure O,
      ρ' (u, v) ≤ 2 * δ → dist u v ≤ χ)
    (hw : ∀ z ∈ closure O, 0 ≤ w z ∧ w z ≤ M)
    (hwosc : ∀ u ∈ closure O, ∀ v ∈ closure O,
      dist u v ≤ χ → |w u - w v| ≤ Ω)
    (hlocal : ∀ x ∈ K, ∀ y ∈ K, ρ' (x, y) < δloc →
      ∃ Q : I →ᵇ X, (∀ t, Q t ∈ closure O) ∧ Q 0 = x ∧ Q 1 = y ∧
        curveLengthWith (fun u v => ENNReal.ofReal (ρ' (u, v)))
          (Set.IccExtend zero_le_one Q) 0 1 = ENNReal.ofReal (ρ' (x, y))) :
    ∃ oldPath newPath : Path (P 0) (P L),
      (∀ t, oldPath t ∈ K) ∧ (∀ t, newPath t ∈ closure O) ∧
      coordinatePathLength (fun u v => ENNReal.ofReal (ρ' (u, v))) newPath ≤
        ENNReal.ofReal (L + (L / δ + 1) * e) ∧
      coordinatePathWeightedLength (fun u v => ENNReal.ofReal (ρ' (u, v))) w
          newPath ≤
        weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w P 0 L +
          ENNReal.ofReal (2 * Ω * L + 2 * M * (L / δ + 1) * e) ∧
      (∀ t : I, dist (oldPath t) (newPath t) ≤ 2 * χ) := by
  let E : X → X → ℝ≥0∞ := fun u v => ENNReal.ofReal (ρ (u, v))
  let E' : X → X → ℝ≥0∞ := fun u v => ENNReal.ofReal (ρ' (u, v))
  obtain ⟨N, hN, hcount, hgrid, hsum⟩ := exists_uniform_recovery_grid hL hδ
  let p := IccPartition.uniform (a := 0) (b := L) hL N hN
  let z : ℕ → X := fun i => P (p.t i)
  let ℓ : ℕ → ℝ := fun i => p.t (i + 1) - p.t i
  have hstep (i : ℕ) (hi : i < N) := p.step hi
  have hℓnonneg (i : ℕ) (hi : i < N) : 0 ≤ ℓ i := sub_nonneg.mpr (hstep i hi).2.1
  have hℓδ (i : ℕ) (hi : i < N) : ℓ i ≤ δ := hgrid i hi
  have hzK (i : ℕ) (hi : i ≤ N) : z i ∈ K := hPK _ (p.mem_Icc hi)
  have hzO (i : ℕ) (hi : i ≤ N) : z i ∈ closure O := hKO (hzK i hi)
  have hρstep (i : ℕ) (hi : i < N) : ρ (z i, z (i + 1)) ≤ ℓ i := by
    have h := le_curveLengthWith (δ := E) (P := P) (hstep i hi).2.1
    rw [hunit _ (p.mem_Icc hi.le) _ (p.mem_Icc hi) (hstep i hi).2.1] at h
    exact (ENNReal.ofReal_le_ofReal_iff (hℓnonneg i hi)).1 h
  have hρ'step (i : ℕ) (hi : i < N) : ρ' (z i, z (i + 1)) ≤ ℓ i + e := by
    have h := hclose (z i) (hzO i hi.le) (z (i + 1)) (hzO (i + 1) hi)
    linarith [(abs_le.mp h).1, hρstep i hi]
  have hshort (i : ℕ) (hi : i < N) : ρ' (z i, z (i + 1)) < δloc := by
    linarith [hρ'step i hi, hℓδ i hi]
  have hRexists : ∀ i : ℕ, ∀ hi : i < N,
      ∃ Q : I →ᵇ X, (∀ t, Q t ∈ closure O) ∧ Q 0 = z i ∧
        Q 1 = z (i + 1) ∧
        curveLengthWith E' (Set.IccExtend zero_le_one Q) 0 1 =
          ENNReal.ofReal (ρ' (z i, z (i + 1))) := by
    intro i hi
    exact hlocal (z i) (hzK i hi.le) (z (i + 1)) (hzK (i + 1) hi) (hshort i hi)
  choose R hRmem hR0 hR1 hRlen using hRexists
  let oldStep : ∀ i : ℕ, i < N → Path (z i) (z (i + 1)) := fun i hi =>
    arcSegment P (hstep i hi).2.1
      (hP.mono (Icc_subset_Icc (hstep i hi).1 (hstep i hi).2.2))
  let newStep : ∀ i : ℕ, i < N → Path (z i) (z (i + 1)) := fun i hi =>
    pathOfBounded (R i hi) (hR0 i hi) (hR1 i hi)
  let oldCost : ℕ → ℝ≥0∞ := fun i =>
    if hi : i < N then coordinatePathWeightedLength E w (oldStep i hi) else 0
  have hOldMem (i : ℕ) (hi : i < N) (t : I) : oldStep i hi t ∈ K := by
    exact arcSegment_mem P (hstep i hi).2.1
      (hP.mono (Icc_subset_Icc (hstep i hi).1 (hstep i hi).2.2))
      (fun s hs => hPK s ⟨(hstep i hi).1.trans hs.1, hs.2.trans (hstep i hi).2.2⟩) t
  have hNewMem (i : ℕ) (hi : i < N) (t : I) : newStep i hi t ∈ closure O :=
    hRmem i hi t
  have hOldLen (i : ℕ) (hi : i < N) :
      coordinatePathLength E (oldStep i hi) = ENNReal.ofReal (ℓ i) := by
    rw [coordinatePathLength_arcSegment]
    exact hunit _ (p.mem_Icc hi.le) _ (p.mem_Icc hi) (hstep i hi).2.1
  have hNewLen (i : ℕ) (hi : i < N) :
      coordinatePathLength E' (newStep i hi) ≤ ENNReal.ofReal (ℓ i + e) := by
    change curveLengthWith E' (Set.IccExtend zero_le_one (R i hi)) 0 1 ≤ _
    rw [hRlen i hi]
    exact ENNReal.ofReal_le_ofReal (hρ'step i hi)
  have hpiece (i : ℕ) (hi : i < N) :
      coordinatePathWeightedLength E' w (newStep i hi) ≤
        oldCost i + ENNReal.ofReal (2 * Ω * ℓ i + 2 * M * e) := by
    let Qi : I →ᵇ X := mkOfCompact (oldStep i hi).toContinuousMap
    have hQmem : ∀ t, Qi t ∈ closure O := fun t => hKO (hOldMem i hi t)
    have hQ0 : Qi 0 = z i := (oldStep i hi).source
    have hQlen : curveLengthWith E (Set.IccExtend zero_le_one Qi) 0 1 =
        ENNReal.ofReal (ℓ i) := hOldLen i hi
    have hRlen' : curveLengthWith E' (Set.IccExtend zero_le_one (R i hi)) 0 1 ≤
        ENNReal.ofReal (ℓ i + e) := hNewLen i hi
    have h := recovery_piece_weighted_bound ρ ρ' w (hzO i hi.le)
      Qi (R i hi) hQmem (hRmem i hi) hQ0 (hR0 i hi)
      (hℓnonneg i hi) he heδ (hℓδ i hi) hδ.le hχ hΩ hΩM
      (hw _ (hzO i hi.le)).1 (hw _ (hzO i hi.le)).2
      hmod hmod' hwosc hQlen hRlen'
    simp only [oldCost, dite_eq_left hi]
    change weightedLengthWith E' w (Set.IccExtend zero_le_one (R i hi)) 0 1 ≤
      weightedLengthWith E w (Set.IccExtend zero_le_one Qi) 0 1 +
        ENNReal.ofReal (2 * Ω * ℓ i + 2 * M * e)
    exact h
  have hstepClose (i : ℕ) (hi : i < N) (t : I) :
      dist (oldStep i hi t) (newStep i hi t) ≤ 2 * χ := by
    let Qi : I →ᵇ X := mkOfCompact (oldStep i hi).toContinuousMap
    have hQ0 : Qi 0 = z i := (oldStep i hi).source
    have hQlen : curveLengthWith E (Set.IccExtend zero_le_one Qi) 0 1 =
        ENNReal.ofReal (ℓ i) := hOldLen i hi
    have hQnear : dist (z i) (Qi t) ≤ χ := by
      apply hmod (z i) (hzO i hi.le) (Qi t) (hKO (hOldMem i hi t))
      rw [← hQ0]
      exact (coordinate_distance_le_length_bound ρ Qi (by linarith : 0 ≤ 2 * δ)
        (by rw [hQlen]; exact ENNReal.ofReal_le_ofReal (by linarith [hℓδ i hi])) t)
    have hRnear : dist (z i) (R i hi t) ≤ χ := by
      apply hmod' (z i) (hzO i hi.le) (R i hi t) (hRmem i hi t)
      rw [← hR0 i hi]
      exact coordinate_distance_le_length_bound ρ' (R i hi)
        (by linarith : 0 ≤ 2 * δ)
        ((hNewLen i hi).trans (ENNReal.ofReal_le_ofReal (by linarith [hℓδ i hi]))) t
    calc
      dist (oldStep i hi t) (newStep i hi t) ≤
          dist (oldStep i hi t) (z i) + dist (z i) (newStep i hi t) :=
        dist_triangle _ _ _
      _ ≤ 2 * χ := by
        change dist (oldStep i hi t) (z i) + dist (z i) (R i hi t) ≤ 2 * χ
        calc
          _ = dist (z i) (Qi t) + dist (z i) (R i hi t) := by rw [dist_comm]; rfl
          _ ≤ χ + χ := add_le_add hQnear hRnear
          _ = 2 * χ := by ring
  have hcostsum : (∑ i ∈ Finset.range N, oldCost i) ≤
      weightedLengthWith E w P 0 L := by
    let t : ℕ → ℝ := fun i => p.t (min i N)
    have ht : Monotone t := fun i j hij =>
      p.le_t (min_le_min_right N hij) (min_le_right _ _)
    have hs := sum_weightedLengthWith_eq
      (fun x => by rw [hρ.metric.self_eq_zero]; simp)
      (ofReal_metric_triangle hρ.metric) w P t ht N
    have hterm : (∑ i ∈ Finset.range N, oldCost i) =
        ∑ i ∈ Finset.range N, weightedLengthWith E w P (p.t i) (p.t (i + 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < N := Finset.mem_range.1 hi
      simp only [oldCost, dite_eq_left hi']
      exact coordinatePathWeightedLength_arcSegment E w P (hstep i hi').2.1
        (hP.mono (Icc_subset_Icc (hstep i hi').1 (hstep i hi').2.2))
    have hterm' : (∑ i ∈ Finset.range N,
        weightedLengthWith E w P (p.t i) (p.t (i + 1))) =
        ∑ i ∈ Finset.range N,
          weightedLengthWith E w P (t i) (t (i + 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < N := Finset.mem_range.1 hi
      have hmin0 : min i N = i := min_eq_left hi'.le
      have hmin1 : min (i + 1) N = i + 1 := min_eq_left hi'
      simp only [t, hmin0, hmin1]
    rw [hterm, hterm', hs]
    have ht0 : t 0 = 0 := by simp [t, p.zero]
    have htN : t N = L := by simpa only [t, min_self] using (show p.t N = L from p.last)
    rw [ht0, htN]
  let oldPath := pathJoinFinite z N oldStep N le_rfl
  let newPath := pathJoinFinite z N newStep N le_rfl
  have hchain := recovery_chain_estimate E E' w
    (fun x => by change ENNReal.ofReal (ρ' (x, x)) = 0; rw [hρ'.metric.self_eq_zero]; simp)
    (ofReal_metric_triangle hρ'.metric) z N oldStep newStep ℓ oldCost
    hℓnonneg (by exact le_of_eq (by simpa [ℓ, p] using hsum)) hΩ
    (by have := hw (z 0) (hzO 0 (by omega)); linarith) he hχ
    hNewLen hpiece hcostsum hstepClose
  have hOldMem : ∀ t, oldPath t ∈ K :=
    pathJoinFinite_mem z N oldStep (hzK 0 (by omega)) hOldMem N le_rfl
  have hNewMem : ∀ t, newPath t ∈ closure O :=
    pathJoinFinite_mem z N newStep (hzO 0 (by omega)) hNewMem N le_rfl
  have hsource : z 0 = P 0 := by simp [z, p.zero]
  have htarget : z N = P L := by change P (p.t N) = P L; rw [show p.t N = L from p.last]
  have hM : 0 ≤ M := by have := hw (z 0) (hzO 0 (by omega)); linarith
  let oldPath' : Path (P 0) (P L) := oldPath.cast hsource.symm htarget.symm
  let newPath' : Path (P 0) (P L) := newPath.cast hsource.symm htarget.symm
  refine ⟨oldPath', newPath', ?_, ?_, ?_, ?_, ?_⟩
  · simpa [oldPath', Path.cast_coe] using hOldMem
  · simpa [newPath', Path.cast_coe] using hNewMem
  · have hc := mul_le_mul_of_nonneg_right hcount he
    have hreal : L + N * e ≤ L + (L / δ + 1) * e := by nlinarith
    simpa [newPath', coordinatePathLength, Path.extend_cast] using
      hchain.1.trans (ENNReal.ofReal_le_ofReal hreal)
  · have hc := mul_le_mul_of_nonneg_left hcount (by positivity : 0 ≤ 2 * M * e)
    have hreal : 2 * Ω * L + 2 * M * N * e ≤
        2 * Ω * L + 2 * M * (L / δ + 1) * e := by nlinarith
    simpa [newPath', coordinatePathWeightedLength, Path.extend_cast] using
      hchain.2.1.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hreal))
  · simpa [oldPath', newPath', Path.cast_coe] using hchain.2.2

end HigherDimLQGMetric
