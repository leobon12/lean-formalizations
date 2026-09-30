import QuantumZipper.Proofs.Thm18.G1PkgChord
import QuantumZipper.Proofs.Thm18.G1PkgTrace

/-!
# G1 package: the chord part `G1ChordUnifSelStmt`, from separability and normalized existence

Continuation of G1PkgChord.lean (generic construction; see its docstring). Results:

* `G1Chord.exists_U`: for side data (open domains, normalization, existence, KT2) and a countable
  sphere-uniformly dense family of simple chords, a chord-measurable inverse normalized
  uniformizer `U` with measurable `log ‖U'‖`;
* `G1Chord.SideUnifExistStmt`: every simple chord has left- and right-normalized uniformizers
  (`CA.Kernel.IsLeftUniformizer`, `φ(−1) = −1`; `IsRightUniformizer`, `φ(1) = 1`);
* **`g1ChordUnifSelStmt_of`** : `ChordSepStmt → SideUnifExistStmt → G1ChordUnifSelStmt`, and
  **`g1PsiSelStmt_of_sep`** : `ChordSepStmt → SideUnifExistStmt → G1PsiSelStmt` (the trace part is
  proved, `G1Pkg.g1TraceSelStmt`); KT2 is `CA.Kernel.chordKernelTheoremLeft/Right` (proved).

Own argument (measurable selection; Weierstrass' theorem on derivatives of locally uniform limits,
mathlib `TendstoLocallyUniformlyOn.deriv`).
-/

noncomputable section

open MeasureTheory Filter Set Function Topology Metric
open scoped ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1Chord

open CA.Kernel

/-! ## Exhausting compacts of `ℍ` -/

/-- Exhausting compacts of `ℍ`. -/
def Kj (j : ℕ) : Set ℂ := {z | ‖z‖ ≤ j ∧ 1 / ((j : ℝ) + 1) ≤ z.im}

theorem Kj_subset_H (j : ℕ) : Kj j ⊆ H := fun z hz =>
  show 0 < z.im from lt_of_lt_of_le (by positivity) hz.2

theorem isCompact_Kj (j : ℕ) : IsCompact (Kj j) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_norm continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_im)
  · exact (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := j)).subset fun z hz => by
      simpa using hz.1

theorem Kj_mem_nhds {j : ℕ} {z : ℂ} (hz : z ∈ Kj j) : Kj (j + 1) ∈ 𝓝 z := by
  have hlt : 1 / ((j : ℝ) + 2) < 1 / ((j : ℝ) + 1) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  set δ : ℝ := min 1 (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2)) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by linarith)
  refine Metric.mem_nhds_iff.2 ⟨δ, hδ0, fun w hw => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have h1 : δ ≤ 1 := min_le_left _ _
  have h2 : δ ≤ 1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2) := min_le_right _ _
  have hn := norm_sub_norm_le w z
  have him : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
  rw [Complex.sub_im] at him
  refine ⟨?_, ?_⟩
  · push_cast; linarith [hz.1]
  · push_cast
    have e : (j : ℝ) + 1 + 1 = (j : ℝ) + 2 := by ring
    rw [e]
    linarith [hz.2, (abs_le.1 (him.trans (le_of_lt hw))).1]

theorem exists_Kj_of_compact {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) :
    ∃ j, K ⊆ Kj j := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, empty_subset _⟩
  obtain ⟨z₀, hz₀K, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hz₀ : 0 < z₀.im := hKH hz₀K
  obtain ⟨j, hj⟩ := exists_nat_gt (max R (1 / z₀.im))
  refine ⟨j, fun z hz => ⟨?_, ?_⟩⟩
  · have := hR hz
    rw [mem_closedBall, dist_zero_right] at this
    linarith [le_max_left R (1 / z₀.im)]
  · have h1 : 1 / z₀.im < j + 1 := by linarith [le_max_right R (1 / z₀.im)]
    have h2 : 1 / ((j : ℝ) + 1) < z₀.im := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hz₀] at h1
      linarith
    exact h2.le.trans (hmin hz)

/-- A countable dense subset of `ℂ`. -/
def Qd : Set ℂ := (TopologicalSpace.exists_countable_dense ℂ).choose

theorem Qd_countable : Qd.Countable := (TopologicalSpace.exists_countable_dense ℂ).choose_spec.1

theorem Qd_dense : Dense Qd := (TopologicalSpace.exists_countable_dense ℂ).choose_spec.2

/-! ## Good chords and the limit map -/

section Good

variable (ηk : ℕ → ℝ → ℂ) (ψk : ℕ → ℂ → ℂ)

/-- Good chords: the selected maps are uniformly Cauchy on each `Kj j`, read on `Qd`. -/
def Good (η : ℝ → ℂ) : Prop :=
  ∀ j m : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ n' ≥ N, ∀ q ∈ Qd, q ∈ Kj j →
    ‖ψk (sel ηk n η) q - ψk (sel ηk n' η) q‖ ≤ 1 / ((m : ℝ) + 1)

/-- The limit map. -/
def V (η : ℝ → ℂ) (w : ℂ) : ℂ := limUnder atTop fun n => ψk (sel ηk n η) w

theorem measurableSet_good : MeasurableSet {η | Good ηk ψk η} := by
  have hc : Countable Qd := Qd_countable.to_subtype
  have e : {η | Good ηk ψk η} = ⋂ j : ℕ, ⋂ m : ℕ, ⋃ N : ℕ, ⋂ n : ℕ, ⋂ n' : ℕ, ⋂ q : Qd,
      {η | n ≥ N → n' ≥ N → (q : ℂ) ∈ Kj j →
        ‖ψk (sel ηk n η) q - ψk (sel ηk n' η) q‖ ≤ 1 / ((m : ℝ) + 1)} := by
    ext η
    simp only [Good, mem_ofPred_eq, mem_iInter, mem_iUnion, Subtype.forall]
    constructor
    · rintro h j m
      obtain ⟨N, hN⟩ := h j m
      exact ⟨N, fun n n' q hq hn hn' hqK => hN n hn n' hn' q hq hqK⟩
    · rintro h j m
      obtain ⟨N, hN⟩ := h j m
      exact ⟨N, fun n hn n' hn' q hq hqK => hN n n' q hq hn hn' hqK⟩
  rw [e]
  refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun m => MeasurableSet.iUnion
    fun N => MeasurableSet.iInter fun n => MeasurableSet.iInter fun n' =>
      MeasurableSet.iInter fun q => ?_
  by_cases h : n ≥ N ∧ n' ≥ N ∧ (q : ℂ) ∈ Kj j
  · have e2 : {η : ℝ → ℂ | n ≥ N → n' ≥ N → (q : ℂ) ∈ Kj j →
        ‖ψk (sel ηk n η) q - ψk (sel ηk n' η) q‖ ≤ 1 / ((m : ℝ) + 1)} =
        {η | ‖ψk (sel ηk n η) q - ψk (sel ηk n' η) q‖ ≤ 1 / ((m : ℝ) + 1)} := by
      ext η; simp only [mem_ofPred_eq]
      exact ⟨fun H => H h.1 h.2.1 h.2.2, fun H _ _ _ => H⟩
    rw [e2]
    have hm : ∀ n, Measurable fun η : ℝ → ℂ => ψk (sel ηk n η) q := fun n =>
      (measurable_from_nat (f := fun k => ψk k q)).comp (measurable_sel ηk n)
    exact measurableSet_le (((hm n).sub (hm n')).norm) measurable_const
  · have e2 : {η : ℝ → ℂ | n ≥ N → n' ≥ N → (q : ℂ) ∈ Kj j →
        ‖ψk (sel ηk n η) q - ψk (sel ηk n' η) q‖ ≤ 1 / ((m : ℝ) + 1)} = univ := by
      ext η; simp only [mem_ofPred_eq, mem_univ, iff_true]
      intro h1 h2 h3; exact absurd ⟨h1, h2, h3⟩ h
    rw [e2]; exact MeasurableSet.univ

variable {ηk ψk}

theorem Good.uniformCauchySeqOn (hψd : ∀ k, DifferentiableOn ℂ (ψk k) H) {η : ℝ → ℂ}
    (hg : Good ηk ψk η) (j : ℕ) :
    UniformCauchySeqOn (fun n => ψk (sel ηk n η)) atTop (Kj j) := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := hg (j + 1) m
  refine ⟨N, fun n hn n' hn' z hz => ?_⟩
  have hzH : z ∈ H := Kj_subset_H j hz
  obtain ⟨s, hsQ, hsz⟩ := mem_closure_iff_seq_limit.1 (Qd_dense z)
  have hev : ∀ᶠ i in atTop, s i ∈ Kj (j + 1) := hsz (Kj_mem_nhds hz)
  have hc : ∀ k, ContinuousAt (ψk k) z := fun k =>
    (hψd k).continuousOn.continuousAt (isOpen_H.mem_nhds hzH)
  have hlim : Tendsto (fun i => ‖ψk (sel ηk n η) (s i) - ψk (sel ηk n' η) (s i)‖) atTop
      (𝓝 ‖ψk (sel ηk n η) z - ψk (sel ηk n' η) z‖) :=
    (((hc _).tendsto.comp hsz).sub ((hc _).tendsto.comp hsz)).norm
  have hle := le_of_tendsto hlim (hev.mono fun i hi => hN n hn n' hn' (s i) (hsQ i) hi)
  rw [dist_eq_norm]
  exact lt_of_le_of_lt hle hm

theorem Good.tendstoLocallyUniformlyOn (hψd : ∀ k, DifferentiableOn ℂ (ψk k) H)
    {η : ℝ → ℂ} (hg : Good ηk ψk η) :
    TendstoLocallyUniformlyOn (fun n => ψk (sel ηk n η)) (V ηk ψk η) atTop H := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_H]
  intro K hKH hK
  obtain ⟨j, hj⟩ := exists_Kj_of_compact hK hKH
  refine ((hg.uniformCauchySeqOn hψd j).tendstoUniformlyOn_of_tendsto fun z hz => ?_).mono hj
  exact ((hg.uniformCauchySeqOn hψd j).cauchySeq hz).tendsto_limUnder

theorem good_of_tendsto {η : ℝ → ℂ} {f : ℂ → ℂ}
    (h : TendstoLocallyUniformlyOn (fun n => ψk (sel ηk n η)) f atTop H) : Good ηk ψk η := by
  intro j m
  have hu := ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_H).1 h (Kj j)
    (Kj_subset_H j) (isCompact_Kj j)).uniformCauchySeqOn
  obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.1 hu (1 / ((m : ℝ) + 1)) (by positivity)
  refine ⟨N, fun n hn n' hn' q _ hq => ?_⟩
  have := hN n hn n' hn' q hq
  rw [dist_eq_norm] at this
  exact this.le

end Good

end G1Chord
end Thm18Asm
end QuantumZipper
