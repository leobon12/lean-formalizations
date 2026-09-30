import QuantumZipper.Proofs.Thm14.WeldReadBasic

/-!
# Corollary 1.5(a), `t > 0`: the welding map from its rational values

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5
(pp. 17–18; no proof in the paper). Task COR15-WR, deterministic input of the driver reading.

For a locally finite measure `ν` on `ℝ` with `ν[0,∞) = ∞` and no atoms on `(-∞,0]`, the welding
map `R_ν(s) = inf {r ≥ 0 : ν[s,0] ≤ ν[0,r]}` (`Thm14WDG.wRm`) agrees on `[a,0]` with any
continuous nonnegative `φ` which it agrees with at the rationals of `[a,0]`
(`wRm_eqOn_of_rat`). This handles the irrational endpoint `a = 0₋` too.

Own elementary argument (cost rule of `AGENT_GUIDE.md`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace QuantumZipper
namespace Cor15Group

open Thm14WDG

variable {ν : Measure ℝ}

theorem iInter_Icc_zero_add (r : ℝ) :
    (⋂ n : ℕ, Icc (0 : ℝ) (r + 1 / ((n : ℝ) + 1))) = Icc 0 r := by
  ext x
  simp only [mem_iInter, mem_Icc]
  constructor
  · intro h
    refine ⟨(h 0).1, le_of_forall_pos_lt_add fun ε hε => ?_⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    linarith [(h n).2]
  · rintro ⟨h1, h2⟩ n
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
    exact ⟨h1, by linarith⟩

/-- Right continuity of `r ↦ ν[0,r]`, as a lower bound. -/
theorem le_measure_Icc_zero_of_forall [IsLocallyFiniteMeasure ν] {r : ℝ} {c : ℝ≥0∞}
    (h : ∀ n : ℕ, c ≤ ν (Icc 0 (r + 1 / ((n : ℝ) + 1)))) : c ≤ ν (Icc 0 r) := by
  rw [← iInter_Icc_zero_add, Antitone.measure_iInter (fun n m hnm => ?_)
    (fun n => measurableSet_Icc.nullMeasurableSet) ⟨0, measure_Icc_lt_top.ne⟩]
  · exact le_iInf h
  · have : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := Nat.one_div_le_one_div hnm
    exact Icc_subset_Icc_right (by linarith)

/-- The welding set is nonempty when `ν[0,∞) = ∞`. -/
theorem wRm_set_nonempty [IsLocallyFiniteMeasure ν] (hinf : ν (Ici 0) = ⊤) (s : ℝ) :
    {r : ℝ | 0 ≤ r ∧ ν (Icc s 0) ≤ ν (Icc 0 r)}.Nonempty := by
  have hU : (⋃ n : ℕ, Icc (0 : ℝ) n) = Ici 0 := by
    ext x
    simp only [mem_iUnion, mem_Icc, mem_Ici]
    exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨⌈x⌉₊, h, Nat.le_ceil x⟩⟩
  have ht : Tendsto (fun n : ℕ => ν (Icc (0 : ℝ) n)) atTop (𝓝 ⊤) := by
    rw [← hinf, ← hU]
    exact tendsto_measure_iUnion_atTop fun n m hnm =>
      Icc_subset_Icc_right (by exact_mod_cast hnm)
  have hlt : ν (Icc s 0) < ⊤ := measure_Icc_lt_top
  obtain ⟨n, hn⟩ := (ht.eventually (lt_mem_nhds hlt)).exists
  exact ⟨n, n.cast_nonneg, hn.le⟩

/-- The infimum is attained. -/
theorem wRm_mem [IsLocallyFiniteMeasure ν] (hinf : ν (Ici 0) = ⊤) (s : ℝ) :
    0 ≤ wRm ν s ∧ ν (Icc s 0) ≤ ν (Icc 0 (wRm ν s)) := by
  set S := {r : ℝ | 0 ≤ r ∧ ν (Icc s 0) ≤ ν (Icc 0 r)}
  have hne : S.Nonempty := wRm_set_nonempty hinf s
  have hbdd : BddBelow S := ⟨0, fun r hr => hr.1⟩
  refine ⟨le_csInf hne fun r hr => hr.1, le_measure_Icc_zero_of_forall fun n => ?_⟩
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
  obtain ⟨r, hrS, hr⟩ := exists_lt_of_csInf_lt hne (lt_add_of_pos_right (sInf S) hpos)
  exact hrS.2.trans (measure_mono (Icc_subset_Icc_right hr.le))

theorem wRm_le_of_mem {s r : ℝ} (hr0 : 0 ≤ r) (h : ν (Icc s 0) ≤ ν (Icc 0 r)) :
    wRm ν s ≤ r :=
  csInf_le ⟨0, fun _ h => h.1⟩ ⟨hr0, h⟩

/-- **The welding map is determined by its rational values** (own elementary argument). -/
theorem wRm_eqOn_of_rat [IsLocallyFiniteMeasure ν] (hinf : ν (Ici 0) = ⊤)
    (hatom : ∀ s : ℝ, s ≤ 0 → ν {s} = 0) {a : ℝ} {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc a 0)) (hφ0 : ∀ s ∈ Icc a 0, 0 ≤ φ s)
    (hq : ∀ q : ℚ, a ≤ (q : ℝ) → (q : ℝ) ≤ 0 → wRm ν q = φ q) :
    ∀ s ∈ Icc a 0, wRm ν s = φ s := by
  intro s hs
  rcases eq_or_lt_of_le hs.2 with h0 | hneg
  · have := hq 0 (by simpa [h0] using hs.1) (by simp)
    simpa [h0] using this
  have hcont := hφ s hs
  rw [Metric.continuousWithinAt_iff] at hcont
  refine le_antisymm ?_ ?_
  · -- upper bound: `φ s` lies in the welding set
    refine wRm_le_of_mem (hφ0 s hs) ?_
    refine le_measure_Icc_zero_of_forall fun N => ?_
    have hεpos : (0 : ℝ) < 1 / ((N : ℝ) + 1) := Nat.one_div_pos_of_nat
    obtain ⟨δ, hδ, hδφ⟩ := hcont _ hεpos
    set η := min δ (-s) / 2 with hη
    have hηpos : 0 < η := by
      have : 0 < min δ (-s) := lt_min hδ (by linarith)
      linarith
    have hηδ : η < δ := by
      have := min_le_left δ (-s); linarith
    have hηs : s + η < 0 := by
      have := min_le_right δ (-s); linarith
    -- `ν[s,0] = ν(s,0]`
    have hsplit : ν (Icc s 0) ≤ ν (Ioc s 0) := by
      calc ν (Icc s 0) ≤ ν ({s} ∪ Ioc s 0) := measure_mono fun x hx => by
            rcases eq_or_lt_of_le hx.1 with h | h
            · exact Or.inl h.symm
            · exact Or.inr ⟨h, hx.2⟩
        _ ≤ ν {s} + ν (Ioc s 0) := measure_union_le _ _
        _ = ν (Ioc s 0) := by rw [hatom s hs.2, zero_add]
    have hU : Ioc s 0 = ⋃ n : ℕ, Icc (s + η / ((n : ℝ) + 1)) 0 := by
      ext x
      simp only [mem_Ioc, mem_iUnion, mem_Icc]
      constructor
      · rintro ⟨h1, h2⟩
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < (x - s) / η by
          exact div_pos (by linarith) hηpos)
        refine ⟨n, ?_, h2⟩
        have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have : η / ((n : ℝ) + 1) < x - s := by
          rw [div_lt_iff₀ hn1]
          rw [lt_div_iff₀ hηpos, div_mul_eq_mul_div, one_mul, div_lt_iff₀ hn1] at hn
          linarith
        linarith
      · rintro ⟨n, h1, h2⟩
        have : 0 < η / ((n : ℝ) + 1) := by positivity
        exact ⟨by linarith, h2⟩
    refine hsplit.trans ?_
    rw [hU, Monotone.measure_iUnion fun n m hnm => Icc_subset_Icc_left ?_]
    · refine iSup_le fun n => ?_
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hun : 0 < η / ((n : ℝ) + 1) := div_pos hηpos hn1
      have hle : η / ((n : ℝ) + 1) ≤ η := div_le_self hηpos.le (by linarith)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show s < s + η / ((n : ℝ) + 1) by linarith)
      have hqI : (q : ℝ) ∈ Icc a 0 := ⟨by linarith [hs.1], by linarith⟩
      have hqd : dist (q : ℝ) s < δ := by
        rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith
      have hφq := hδφ hqI hqd
      rw [Real.dist_eq] at hφq
      have hmem := (wRm_mem hinf (q : ℝ)).2
      rw [hq q hqI.1 hqI.2] at hmem
      calc ν (Icc (s + η / ((n : ℝ) + 1)) 0) ≤ ν (Icc (q : ℝ) 0) :=
            measure_mono (Icc_subset_Icc_left hq2.le)
        _ ≤ ν (Icc 0 (φ q)) := hmem
        _ ≤ _ := measure_mono (Icc_subset_Icc_right (by linarith [le_abs_self (φ q - φ s)]))
    · have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h2 : ((n : ℝ) + 1) ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hnm
      have : η / ((m : ℝ) + 1) ≤ η / ((n : ℝ) + 1) :=
        div_le_div_of_nonneg_left hηpos.le h1 h2
      linarith
  · -- lower bound
    have hne := wRm_set_nonempty hinf s
    refine le_csInf hne fun r hr => ?_
    by_contra hlt
    push Not at hlt
    obtain ⟨δ, hδ, hδφ⟩ := hcont _ (show 0 < φ s - r by linarith)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show s < min (s + δ) 0 by
      exact lt_min (by linarith) hneg)
    have hqI : (q : ℝ) ∈ Icc a 0 := ⟨by linarith [hs.1], (hq2.trans_le (min_le_right _ _)).le⟩
    have hqd : dist (q : ℝ) s < δ := by
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      linarith [hq2.trans_le (min_le_left _ _)]
    have hφq := hδφ hqI hqd
    rw [Real.dist_eq] at hφq
    have hrq : r < wRm ν q := by
      rw [hq q hqI.1 hqI.2]; linarith [neg_abs_le (φ q - φ s)]
    have : wRm ν q ≤ r :=
      wRm_le_of_mem hr.1 ((measure_mono (Icc_subset_Icc_left hq1.le)).trans hr.2)
    linarith

end Cor15Group
end QuantumZipper
