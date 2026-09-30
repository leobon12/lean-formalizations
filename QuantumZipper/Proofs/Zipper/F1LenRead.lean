import QuantumZipper.Proofs.Zipper.F1ABJensen

/-!
# Theorem 1.3, node F1: `LenReadStmt` from fixed-time reading and regularity in time

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.4, proof of Theorem 1.3
(pp. 70–72); blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §F1 (F1a–F1b, the law transfer through
the data). `F_c(s) = L⁺(tᴸ_c(s))` (`F1.lenF`) evaluates the right length at the first-passage
time `tᴸ_c(s) = inf {t ≥ 0 : s ≤ L⁻_t}`. Its reading from the data is a.e.-measurable as soon as

* (`LenReadTimeStmt`) the lengths at each fixed time `t ≥ 0` are read a.e.-measurably from the
  data (the fixed-time form of `F1.ReadLenAEMeasStmt`, which is time `1`), and
* (`LenReadRegStmt`) for a.e. datum the left length is nondecreasing and the right length is
  continuous in time on `[0,∞)`.

Deterministic core (`tendsto_dyadic_firstPassage`): for a nondecreasing `L⁻` the first dyadic time
`k/2ᵐ` with `s ≤ L⁻` decreases to `tᴸ(s)` within `2⁻ᵐ` (and is the junk `0` exactly when the
passage set is empty, as is `tᴸ(s) = sInf ∅ = 0`), so by continuity `L⁺` at these times tends
to `L⁺(tᴸ(s))`. The dyadic approximants are measurable (`Measurable.find`), and the limit is
a.e.-measurable (`aemeasurable_of_tendsto_metrizable_ae'`). Own elementary argument (the paper
does not discuss measurability).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F1

/-- The dyadic time `k / 2ᵐ`. -/
def lenDy (m k : ℕ) : ℝ := (k : ℝ) / (2 : ℝ) ^ m

theorem lenDy_nonneg (m k : ℕ) : 0 ≤ lenDy m k := by unfold lenDy; positivity

/-- **Dyadic first-passage approximation, deterministic.** If `n m` is the first index `j` such
that `ℓ ≤ L1 (j/2ᵐ)` (or `0` if there is none), `L1` is nondecreasing and `L2` continuous on
`[0,∞)`, then `L2 (n m / 2ᵐ) → L2 (inf {t ≥ 0 : ℓ ≤ L1 t})`. -/
theorem tendsto_dyadic_firstPassage {L1 : ℝ → ℝ≥0∞} {L2 : ℝ → ℝ} {ℓ : ℝ≥0∞}
    (hmono : MonotoneOn L1 (Ici 0)) (hcont : ContinuousOn L2 (Ici 0)) (n : ℕ → ℕ)
    (hn : ∀ m, ℓ ≤ L1 (lenDy m (n m)) ∨ ∀ j, ¬ ℓ ≤ L1 (lenDy m j))
    (hmin : ∀ m j, j < n m → ¬ (ℓ ≤ L1 (lenDy m j) ∨ ∀ j', ¬ ℓ ≤ L1 (lenDy m j'))) :
    Tendsto (fun m => L2 (lenDy m (n m))) atTop (𝓝 (L2 (sInf {t | 0 ≤ t ∧ ℓ ≤ L1 t}))) := by
  set S := {t : ℝ | 0 ≤ t ∧ ℓ ≤ L1 t} with hSdef
  have hbdd : BddBelow S := ⟨0, fun t ht => ht.1⟩
  by_cases hS : S.Nonempty
  · obtain ⟨t0, ht0⟩ := hS
    have hT0 : 0 ≤ sInf S := Real.sInf_nonneg fun t ht => ht.1
    have hp : ∀ m : ℕ, (0 : ℝ) < (2 : ℝ) ^ m := fun m => by positivity
    have hdy : ∀ m, ∃ j, ℓ ≤ L1 (lenDy m j) := by
      intro m
      refine ⟨⌈(2 : ℝ) ^ m * t0⌉₊, ht0.2.trans (hmono (mem_Ici.2 ht0.1)
        (mem_Ici.2 (lenDy_nonneg _ _)) ?_)⟩
      rw [lenDy, le_div_iff₀ (hp m), mul_comm]
      exact Nat.le_ceil _
    have hin : ∀ m, ℓ ≤ L1 (lenDy m (n m)) := fun m =>
      (hn m).resolve_right fun h => by obtain ⟨j, hj⟩ := hdy m; exact h j hj
    have hlo : ∀ m, sInf S ≤ lenDy m (n m) := fun m =>
      csInf_le hbdd ⟨lenDy_nonneg _ _, hin m⟩
    have hhi : ∀ m, lenDy m (n m) ≤ sInf S + (1 / 2 : ℝ) ^ m := by
      intro m
      set j0 := ⌊(2 : ℝ) ^ m * sInf S⌋₊ + 1 with hj0def
      have hj0 : sInf S < lenDy m j0 := by
        rw [lenDy, lt_div_iff₀ (hp m), mul_comm, hj0def]
        push_cast
        exact Nat.lt_floor_add_one _
      obtain ⟨t, htS, htlt⟩ := exists_lt_of_csInf_lt ⟨t0, ht0⟩ hj0
      have hP : ℓ ≤ L1 (lenDy m j0) :=
        htS.2.trans (hmono (mem_Ici.2 htS.1) (mem_Ici.2 (lenDy_nonneg _ _)) htlt.le)
      have hle : n m ≤ j0 := by
        by_contra h
        exact hmin m j0 (not_le.1 h) (Or.inl hP)
      calc lenDy m (n m) ≤ lenDy m j0 := by
            unfold lenDy
            exact div_le_div_of_nonneg_right (by exact_mod_cast hle) (hp m).le
        _ ≤ sInf S + (1 / 2 : ℝ) ^ m := by
            rw [lenDy, div_le_iff₀ (hp m), add_mul, one_div_pow,
              one_div_mul_cancel (hp m).ne', hj0def]
            push_cast
            have := Nat.floor_le (mul_nonneg (hp m).le hT0)
            linarith
    have htend : Tendsto (fun m => lenDy m (n m)) atTop (𝓝 (sInf S)) := by
      have hz : Tendsto (fun m : ℕ => sInf S + (1 / 2 : ℝ) ^ m) atTop (𝓝 (sInf S)) := by
        simpa using tendsto_const_nhds.add
          (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
            (by norm_num : (1 / 2 : ℝ) < 1))
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz hlo hhi
    exact ((hcont _ (mem_Ici.2 hT0)).tendsto).comp
      (tendsto_nhdsWithin_iff.2 ⟨htend, Eventually.of_forall fun m => mem_Ici.2 (lenDy_nonneg _ _)⟩)
  · have hT : sInf S = 0 := by rw [Set.not_nonempty_iff_eq_empty.1 hS, Real.sInf_empty]
    have hnone : ∀ m j, ¬ ℓ ≤ L1 (lenDy m j) := fun m j h => hS ⟨_, lenDy_nonneg _ _, h⟩
    have h0 : ∀ m, n m = 0 := fun m => by
      by_contra h
      exact hmin m 0 (Nat.pos_of_ne_zero h) (Or.inr (hnone m))
    rw [hT]
    refine tendsto_const_nhds.congr fun m => ?_
    rw [h0 m, lenDy, Nat.cast_zero, zero_div]

/-- **A.e.-measurability of the right length at the left first-passage time.** For random
length processes `L1`, `L2` on `[0,∞)` that are a.e.-measurable at each fixed time, with `L1`
a.e. nondecreasing and `L2` a.e. continuous (as real numbers) on `[0,∞)`, the value
`L2(inf {t ≥ 0 : ℓ ≤ L1 t})` is a.e.-measurable. -/
theorem aemeasurable_firstPassage_eval {D : Type*} [MeasurableSpace D] {μ : Measure D}
    (L1 L2 : D → ℝ → ℝ≥0∞) (ℓ : ℝ≥0∞)
    (h1 : ∀ t, 0 ≤ t → AEMeasurable (fun d => L1 d t) μ)
    (h2 : ∀ t, 0 ≤ t → AEMeasurable (fun d => L2 d t) μ)
    (hreg : ∀ᵐ d ∂μ, MonotoneOn (L1 d) (Ici 0) ∧
      ContinuousOn (fun t => (L2 d t).toReal) (Ici 0)) :
    AEMeasurable (fun d => (L2 d (sInf {t | 0 ≤ t ∧ ℓ ≤ L1 d t})).toReal) μ := by
  classical
  set M1 : ℕ × ℕ → D → ℝ≥0∞ := fun p => (h1 (lenDy p.1 p.2) (lenDy_nonneg _ _)).mk _
  set M2 : ℕ × ℕ → D → ℝ≥0∞ := fun p => (h2 (lenDy p.1 p.2) (lenDy_nonneg _ _)).mk _
  have hM1m : ∀ p, Measurable (M1 p) := fun p => (h1 _ (lenDy_nonneg p.1 p.2)).measurable_mk
  have hM2m : ∀ p, Measurable (M2 p) := fun p => (h2 _ (lenDy_nonneg p.1 p.2)).measurable_mk
  have hgood : ∀ᵐ d ∂μ, ∀ p : ℕ × ℕ,
      L1 d (lenDy p.1 p.2) = M1 p d ∧ L2 d (lenDy p.1 p.2) = M2 p d := by
    rw [ae_all_iff]
    intro p
    filter_upwards [(h1 _ (lenDy_nonneg p.1 p.2)).ae_eq_mk,
      (h2 _ (lenDy_nonneg p.1 p.2)).ae_eq_mk] with d e1 e2
    exact ⟨e1, e2⟩
  let P : ℕ → ℕ → D → Prop := fun m j d => ℓ ≤ M1 (m, j) d ∨ ∀ j', ¬ ℓ ≤ M1 (m, j') d
  have hex : ∀ m d, ∃ j, P m j d := by
    intro m d
    by_cases h : ∃ j, ℓ ≤ M1 (m, j) d
    · obtain ⟨j, hj⟩ := h
      exact ⟨j, Or.inl hj⟩
    · exact ⟨0, Or.inr fun j hj => h ⟨j, hj⟩⟩
  have hPm : ∀ m j, MeasurableSet {d | P m j d} := by
    intro m j
    have e : {d | P m j d} =
        {d | ℓ ≤ M1 (m, j) d} ∪ ⋂ j' : ℕ, {d | ℓ ≤ M1 (m, j') d}ᶜ := by
      ext d
      simp [P]
    rw [e]
    exact (measurableSet_le measurable_const (hM1m _)).union
      (MeasurableSet.iInter fun j' => (measurableSet_le measurable_const (hM1m _)).compl)
  have hf : ∀ m, Measurable fun d => (M2 (m, Nat.find (hex m d)) d).toReal := fun m =>
    Measurable.find (f := fun j d => (M2 (m, j) d).toReal) (p := fun j d => P m j d)
      (fun j => (hM2m _).ennreal_toReal) (hPm m) (hex m)
  refine aemeasurable_of_tendsto_metrizable_ae' (fun m => (hf m).aemeasurable) ?_
  filter_upwards [hgood, hreg] with d hg hr
  have eP : ∀ m j, P m j d ↔ (ℓ ≤ L1 d (lenDy m j) ∨ ∀ j', ¬ ℓ ≤ L1 d (lenDy m j')) := by
    intro m j
    have e : ∀ j, M1 (m, j) d = L1 d (lenDy m j) := fun j => (hg (m, j)).1.symm
    simp only [P, e]
  have ht := tendsto_dyadic_firstPassage hr.1 hr.2 (fun m => Nat.find (hex m d))
    (fun m => (eP m _).1 (Nat.find_spec (hex m d)))
    (fun m j hj h => Nat.find_min (hex m d) hj ((eP m j).2 h))
  refine ht.congr fun m => ?_
  show (L2 d (lenDy m _)).toReal = (M2 (m, _) d).toReal
  rw [(hg (m, _)).2]

/-! ## `LenReadStmt` -/

end F1
end QuantumZipper
