import SupercriticalLQGUniqueness.Uniqueness.EndSaving.PathSurgery.Section4Paths
import LQGMetric.Metric.Geodesic




 





set_option autoImplicit false
noncomputable section

open Set LQGMetric.MetricGeometry Finset
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.PathSurgery

 

def spliceN (P : ℝ → ℂ) (Q : ℕ → ℝ → ℂ) (τ σ : ℕ → ℝ) : ℕ → ℝ → ℂ
  | 0 => P
  | n + 1 => fun t =>
      if t ≤ τ n then spliceN P Q τ σ n t
      else if t ≤ σ n then Q n t
      else spliceN P Q τ σ n t

 
theorem spliceN_tail (P : ℝ → ℂ) (Q : ℕ → ℝ → ℂ) (τ σ : ℕ → ℝ)
    (n : ℕ) {u t : ℝ} (hu : ∀ i < n, σ i < u) (hut : u ≤ t) :
    spliceN P Q τ σ n t = P t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprev : ∀ i < n, σ i < u := by
      intro i hi
      exact hu i (by omega)
    have hσ : σ n < u := hu n (by omega)
    simp only [spliceN]
    by_cases htτ : t ≤ τ n
    · simpa [spliceN, htτ] using ih hprev
    ·
      have htσ' : ¬ t ≤ σ n := not_le.mpr (lt_of_lt_of_le hσ hut)
      simpa [spliceN, htτ, htσ'] using ih hprev

 
theorem one_splice (D : LSCMetric) {P Q : ℝ → ℂ}
    {T τ σ : ℝ} (h0τ : 0 ≤ τ) (hτσ : τ ≤ σ) (hσT : σ ≤ T)
    (hP : D.IsCurve P 0 T) (hQ : D.IsCurve Q τ σ)
    (hτ : P τ = Q τ) (hσ : Q σ = P σ) :
    let R : ℝ → ℂ := fun t => if t ≤ τ then P t else if t ≤ σ then Q t else P t
    D.IsCurve R 0 T ∧ R 0 = P 0 ∧ R T = P T ∧
      D.len R 0 T = D.len P 0 τ + D.len Q τ σ + D.len P σ T := by
  let S : ℝ → ℂ := fun t => if t ≤ σ then Q t else P t
  let R : ℝ → ℂ := fun t => if t ≤ τ then P t else S t
  have hSτ : S τ = P τ := by simp [S, hτσ, ← hτ]
  have hS : D.IsCurve S τ T := by
    refine ⟨hτσ.trans hσT, ?_⟩
    change ContinuousOn (fun t => if t ≤ σ then D.pt (Q t) else D.pt (P t)) (Icc τ T)
    exact continuousOn_concat hτσ hσT (congrArg D.pt hσ) hQ.2
      (hP.2.mono (Icc_subset_Icc (h0τ.trans hτσ) le_rfl))
  have hR : D.IsCurve R 0 T := by
    refine ⟨h0τ.trans (hτσ.trans hσT), ?_⟩
    change ContinuousOn (fun t => if t ≤ τ then D.pt (P t) else D.pt (S t)) (Icc 0 T)
    exact continuousOn_concat h0τ (hτσ.trans hσT) (congrArg D.pt hSτ.symm)
      (hP.2.mono (Icc_subset_Icc le_rfl (hτσ.trans hσT))) hS.2
  have hlenS : D.len S τ T = D.len Q τ σ + D.len P σ T := by
    change curveLength (fun t => if t ≤ σ then D.pt (Q t) else D.pt (P t)) τ T = _
    exact curveLength_concat hτσ hσT (congrArg D.pt hσ)
  have hlenR : D.len R 0 T = D.len P 0 τ + D.len S τ T := by
    change curveLength (fun t => if t ≤ τ then D.pt (P t) else D.pt (S t)) 0 T = _
    exact curveLength_concat h0τ (hτσ.trans hσT) (congrArg D.pt hSτ.symm)
  dsimp only
  have hdef : (fun t => if t ≤ τ then P t else if t ≤ σ then Q t else P t) = R := rfl
  rw [hdef]
  refine ⟨hR, ?_, ?_, ?_⟩
  · simp [h0τ]
  · by_cases hTτ : T ≤ τ
    · simp [hTτ]
    · by_cases hTσ : T ≤ σ
      · have hTeq : T = σ := le_antisymm hTσ hσT
        subst T
        simp [hTτ, hσ]
      · simp [hTτ, hTσ]
  · rw [hlenR, hlenS, add_assoc]

 
theorem one_splice_cost (D : LSCMetric) {P Q : ℝ → ℂ}
    {T τ σ : ℝ} (h0τ : 0 ≤ τ) (hτσ : τ ≤ σ) (hσT : σ ≤ T)
    (hP : D.IsCurve P 0 T) (hQ : D.IsCurve Q τ σ)
    (hτ : P τ = Q τ) (hσ : Q σ = P σ) :
    let R : ℝ → ℂ := fun t => if t ≤ τ then P t else if t ≤ σ then Q t else P t
    D.len R 0 T + D.len P τ σ = D.len P 0 T + D.len Q τ σ := by
  have hsplice := one_splice D h0τ hτσ hσT hP hQ hτ hσ
  dsimp only at hsplice ⊢
  have hlenP : D.len P 0 T = D.len P 0 τ + D.len P τ σ + D.len P σ T := by
    change curveLength (D.pt ∘ P) 0 T = _
    rw [← curveLength_add _ h0τ (hτσ.trans hσT)]
    rw [← curveLength_add _ hτσ hσT]
    ac_rfl
  rw [hsplice.2.2.2, hlenP]
  ac_rfl

 


theorem finite_splice_cost (D : LSCMetric) (P : ℝ → ℂ)
    (Q : ℕ → ℝ → ℂ) (τ σ : ℕ → ℝ) {T : ℝ}
    (hP : D.IsCurve P 0 T) (n : ℕ) :
    (∀ i < n, 0 ≤ τ i ∧ τ i ≤ σ i ∧ σ i ≤ T) →
    (∀ i j, i < j → j < n → σ i < τ j) →
    (∀ i < n, D.IsCurve (Q i) (τ i) (σ i)) →
    (∀ i < n, P (τ i) = Q i (τ i)) →
    (∀ i < n, Q i (σ i) = P (σ i)) →
    D.IsCurve (spliceN P Q τ σ n) 0 T ∧
      spliceN P Q τ σ n 0 = P 0 ∧
      spliceN P Q τ σ n T = P T ∧
      D.len (spliceN P Q τ σ n) 0 T +
        ∑ i ∈ range n, D.len P (τ i) (σ i) =
      D.len P 0 T + ∑ i ∈ range n, D.len (Q i) (τ i) (σ i) := by
  induction n with
  | zero =>
      intro _ _ _ _ _
      exact ⟨hP, rfl, rfl, by simp only [sum_range_zero, add_zero]; rfl⟩
  | succ n ih =>
      intro hbound horder hQ hτ hσ
      have hbound' : ∀ i < n, 0 ≤ τ i ∧ τ i ≤ σ i ∧ σ i ≤ T := by
        intro i hi
        exact hbound i (by omega)
      have horder' : ∀ i j, i < j → j < n → σ i < τ j := by
        intro i j hij hj
        exact horder i j hij (by omega)
      have hQ' : ∀ i < n, D.IsCurve (Q i) (τ i) (σ i) := by
        intro i hi
        exact hQ i (by omega)
      have hτ' : ∀ i < n, P (τ i) = Q i (τ i) := by
        intro i hi
        exact hτ i (by omega)
      have hσ' : ∀ i < n, Q i (σ i) = P (σ i) := by
        intro i hi
        exact hσ i (by omega)
      obtain ⟨hOld, hOld0, hOldT, hOldCost⟩ :=
        ih hbound' horder' hQ' hτ' hσ'
      have hbn := hbound n (by omega)
      have htail : ∀ t, τ n ≤ t → spliceN P Q τ σ n t = P t := by
        intro t ht
        exact spliceN_tail P Q τ σ n (fun i hi => horder i n hi (by omega)) ht
      have hlinkτ : spliceN P Q τ σ n (τ n) = Q n (τ n) :=
        (htail _ le_rfl).trans (hτ n (by omega))
      have hlinkσ : Q n (σ n) = spliceN P Q τ σ n (σ n) :=
        (hσ n (by omega)).trans (htail _ hbn.2.1).symm
      have hOne := one_splice D hbn.1 hbn.2.1 hbn.2.2 hOld
        (hQ n (by omega)) hlinkτ hlinkσ
      dsimp only at hOne
      have hCurve : D.IsCurve (spliceN P Q τ σ (n + 1)) 0 T := hOne.1
      have h0 : spliceN P Q τ σ (n + 1) 0 = P 0 :=
        hOne.2.1.trans hOld0
      have hT : spliceN P Q τ σ (n + 1) T = P T :=
        hOne.2.2.1.trans hOldT
      have hlenEq : D.len (spliceN P Q τ σ n) (τ n) (σ n) =
          D.len P (τ n) (σ n) := by
        change curveLength (D.pt ∘ spliceN P Q τ σ n) (τ n) (σ n) =
          curveLength (D.pt ∘ P) (τ n) (σ n)
        exact curveLength_congr (fun t ht => congrArg D.pt (htail t ht.1))
      have hStep := one_splice_cost D hbn.1 hbn.2.1 hbn.2.2 hOld
        (hQ n (by omega)) hlinkτ hlinkσ
      dsimp only at hStep
      rw [hlenEq] at hStep
      change D.len (spliceN P Q τ σ (n + 1)) 0 T +
          D.len P (τ n) (σ n) =
        D.len (spliceN P Q τ σ n) 0 T + D.len (Q n) (τ n) (σ n) at hStep
      refine ⟨hCurve, h0, hT, ?_⟩
      rw [sum_range_succ, sum_range_succ]
      calc
        D.len (spliceN P Q τ σ (n + 1)) 0 T +
            ((∑ i ∈ range n, D.len P (τ i) (σ i)) + D.len P (τ n) (σ n)) =
          (D.len (spliceN P Q τ σ (n + 1)) 0 T +
            D.len P (τ n) (σ n)) +
              ∑ i ∈ range n, D.len P (τ i) (σ i) := by ac_rfl
        _ = (D.len (spliceN P Q τ σ n) 0 T +
            D.len (Q n) (τ n) (σ n)) +
              ∑ i ∈ range n, D.len P (τ i) (σ i) := by rw [hStep]
        _ = (D.len (spliceN P Q τ σ n) 0 T +
              ∑ i ∈ range n, D.len P (τ i) (σ i)) +
                D.len (Q n) (τ n) (σ n) := by ac_rfl
        _ = (D.len P 0 T +
              ∑ i ∈ range n, D.len (Q i) (τ i) (σ i)) +
                D.len (Q n) (τ n) (σ n) := by rw [hOldCost]
        _ = D.len P 0 T +
              ((∑ i ∈ range n, D.len (Q i) (τ i) (σ i)) +
                D.len (Q n) (τ n) (σ n)) := by ac_rfl

 
def gapStart (σ : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => σ n

 
theorem finite_splice_length (D : LSCMetric) (P : ℝ → ℂ)
    (Q : ℕ → ℝ → ℂ) (τ σ : ℕ → ℝ) (n : ℕ) :
    ∀ T : ℝ,
    D.IsCurve P 0 T →
    (∀ i < n, 0 ≤ τ i ∧ τ i ≤ σ i ∧ σ i ≤ T) →
    (∀ i j, i < j → j < n → σ i < τ j) →
    (∀ i < n, D.IsCurve (Q i) (τ i) (σ i)) →
    (∀ i < n, P (τ i) = Q i (τ i)) →
    (∀ i < n, Q i (σ i) = P (σ i)) →
    D.len (spliceN P Q τ σ n) 0 T =
      (∑ i ∈ range n,
        (D.len P (gapStart σ i) (τ i) + D.len (Q i) (τ i) (σ i))) +
      D.len P (gapStart σ n) T := by
  induction n with
  | zero =>
      intro T _ _ _ _ _ _
      simp only [sum_range_zero, zero_add, gapStart, spliceN]
  | succ n ih =>
      intro T hP hbound horder hQ hτ hσ
      have hbn := hbound n (by omega)
      have hbound' : ∀ i < n, 0 ≤ τ i ∧ τ i ≤ σ i ∧ σ i ≤ τ n := by
        intro i hi
        obtain ⟨h0, hts, _⟩ := hbound i (by omega)
        exact ⟨h0, hts, (horder i n hi (by omega)).le⟩
      have horder' : ∀ i j, i < j → j < n → σ i < τ j := by
        intro i j hij hj
        exact horder i j hij (by omega)
      have hQ' : ∀ i < n, D.IsCurve (Q i) (τ i) (σ i) := by
        intro i hi
        exact hQ i (by omega)
      have hτ' : ∀ i < n, P (τ i) = Q i (τ i) := by
        intro i hi
        exact hτ i (by omega)
      have hσ' : ∀ i < n, Q i (σ i) = P (σ i) := by
        intro i hi
        exact hσ i (by omega)
      have hPprefix : D.IsCurve P 0 (τ n) := by
        refine ⟨hbn.1, ?_⟩
        exact hP.2.mono (Icc_subset_Icc le_rfl (hbn.2.1.trans hbn.2.2))
      have hPrefix := ih (τ n) hPprefix hbound' horder' hQ' hτ' hσ'
      have hOld : D.IsCurve (spliceN P Q τ σ n) 0 T :=
        (finite_splice_cost D P Q τ σ hP n
          (fun i hi => hbound i (by omega))
          (fun i j hij hj => horder i j hij (by omega))
          (fun i hi => hQ i (by omega))
          (fun i hi => hτ i (by omega))
          (fun i hi => hσ i (by omega))).1
      have htail : ∀ t, τ n ≤ t → spliceN P Q τ σ n t = P t := by
        intro t ht
        exact spliceN_tail P Q τ σ n
          (fun i hi => horder i n hi (by omega)) ht
      have hlinkτ : spliceN P Q τ σ n (τ n) = Q n (τ n) :=
        (htail _ le_rfl).trans (hτ n (by omega))
      have hlinkσ : Q n (σ n) = spliceN P Q τ σ n (σ n) :=
        (hσ n (by omega)).trans (htail _ hbn.2.1).symm
      have hOne := one_splice D hbn.1 hbn.2.1 hbn.2.2 hOld
        (hQ n (by omega)) hlinkτ hlinkσ
      have hTailLen : D.len (spliceN P Q τ σ n) (σ n) T =
          D.len P (σ n) T := by
        change curveLength (D.pt ∘ spliceN P Q τ σ n) (σ n) T =
          curveLength (D.pt ∘ P) (σ n) T
        exact curveLength_congr (fun t ht => congrArg D.pt
          (htail t (hbn.2.1.trans ht.1)))
      have hOneLen := hOne.2.2.2
      change D.len (spliceN P Q τ σ (n + 1)) 0 T =
        D.len (spliceN P Q τ σ n) 0 (τ n) +
          D.len (Q n) (τ n) (σ n) +
          D.len (spliceN P Q τ σ n) (σ n) T at hOneLen
      rw [hOneLen, hPrefix, hTailLen, sum_range_succ]
      simp only [gapStart]
      ac_rfl


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.PathSurgery
