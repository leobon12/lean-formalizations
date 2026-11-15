/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField8Trace

/-!
# The first entrance of a capped path, and the stops that announce it

Packet PROVE-WHOLEFIELD8, deterministic part of the reduction of Aux. lemma 56 at first entrance times.

For a continuous path `γ` (the capped flow line `η(· ∧ ζ ∧ m)`), constant after `c = ζ ∧ m`, started outside the open
set `U`, whose values before `c` are the trace values `Γ`:

* `firstEntrance_eq_ratEntrance`: its first entrance time into `U` is the rational entrance time `R` of `Γ` before `ζ`
  when `R < m`, and `∞` otherwise.

For `R`, `m` and a nondecreasing sequence `σₙ < ζ` reaching every time before `ζ` (an announcing sequence of the
lifetime), with `τₙ = R ∧ m ∧ σₙ` (`seqStop`) and `c̃ = sup τₙ` (`supStop`):

* `isEntered_iff`: the event `{c̃ < m and c̃ is attained}` (`IsEntered`, readable from the `τₙ`) is `{R < m}`;
* `supStop_eq_of_isEntered`, `supStop_eq_of_not_isEntered`: `c̃ = R` on it, `c̃ = ζ ∧ m` off it;
* `exists_m_le_seqStop_iff`: off it, `{∃ n, m ≤ τₙ} = {m < ζ}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

open Sec6

/-! ### The first entrance of a capped path -/

section Capped

variable {U : Set ℂ} {γ : ℝ≥0 → ℂ}

/-- A continuous path started outside the open set `U` that is in `U` at time `s` is in `U` at a rational time
before `s`. -/
theorem exists_rat_lt_mem (hU : IsOpen U) (hγ : Continuous γ) (h0 : γ 0 ∉ U) {s : ℝ≥0} (hs : γ s ∈ U) :
    ∃ q : ℚ≥0, (q : ℝ≥0) < s ∧ γ q ∈ U := by
  have h1 : firstEntrance U (pathCoord γ) < s := by
    by_contra hle
    exact notMem_of_le_firstEntrance hU hγ h0 (not_lt.1 hle) hs
  unfold firstEntrance at h1
  simp only [iInf_lt_iff, exists_prop] at h1
  obtain ⟨q, hqU, hqs⟩ := h1
  exact ⟨q, ENNReal.coe_lt_coe.1 hqs, hqU⟩

/-- **The first entrance of a capped path** is the rational entrance time of its trace values before the lifetime,
if that is before the cap, and `∞` otherwise. -/
theorem firstEntrance_eq_ratEntrance (hU : IsOpen U) (hγ : Continuous γ) (h0 : γ 0 ∉ U) {c m : ℝ≥0}
    {ζ : ℝ≥0∞} {Γ : ℝ≥0 → ℂ} (hconst : ∀ t, γ t = γ (min t c)) (hc : (c : ℝ≥0∞) = min ζ m)
    (hΓ : ∀ s : ℝ≥0, s < c → Γ s = γ s) :
    firstEntrance U (pathCoord γ) = if ratEntrance U Γ ζ < m then ratEntrance U Γ ζ else ⊤ := by
  have hpc : ∀ p : ℝ≥0, p < c → (p : ℝ≥0∞) < ζ ∧ p < m := fun p hp => by
    have : (p : ℝ≥0∞) < min ζ m := hc ▸ ENNReal.coe_lt_coe.2 hp
    exact ⟨lt_of_lt_of_le this (min_le_left _ _), ENNReal.coe_lt_coe.1 (lt_of_lt_of_le this (min_le_right _ _))⟩
  -- every entrance of `γ` gives an earlier entrance of `Γ` before `c`
  have F1 : ∀ q : ℚ≥0, γ q ∈ U → ∃ p : ℚ≥0, (p : ℝ≥0) ≤ q ∧ (p : ℝ≥0) < c ∧ Γ p ∈ U := by
    intro q hq
    by_cases hqc : (q : ℝ≥0) < c
    · exact ⟨q, le_rfl, hqc, by rw [hΓ _ hqc]; exact hq⟩
    · have hγc : γ c ∈ U := by
        have := hconst q
        rw [min_eq_right (not_lt.1 hqc)] at this
        rwa [← this]
      obtain ⟨p, hp, hpU⟩ := exists_rat_lt_mem hU hγ h0 hγc
      exact ⟨p, (hp.trans_le (not_lt.1 hqc)).le, hp, by rw [hΓ _ hp]; exact hpU⟩
  -- every entrance of `Γ` before `ζ ∧ m` is one of `γ`
  have F2 : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < ζ → Γ q ∈ U → (q : ℝ≥0) < m → γ q ∈ U := by
    intro q hqζ hqU hqm
    have hqc : (q : ℝ≥0) < c := by
      have : ((q : ℝ≥0) : ℝ≥0∞) < min ζ m := lt_min hqζ (ENNReal.coe_lt_coe.2 hqm)
      exact ENNReal.coe_lt_coe.1 (hc ▸ this)
    rw [← hΓ _ hqc]; exact hqU
  split_ifs with hR
  · refine le_antisymm ?_ ?_
    · refine le_of_forall_gt_imp_ge_of_dense fun b hb => ?_
      obtain ⟨q, hqζ, hqU, hqb⟩ := ratEntrance_lt_iff.1 (lt_min hb hR)
      have hqm : (q : ℝ≥0) < m := ENNReal.coe_lt_coe.1 (lt_of_lt_of_le hqb (min_le_right _ _))
      exact (firstEntrance_le (c := pathCoord γ) (F2 q hqζ hqU hqm)).trans
        (lt_of_lt_of_le hqb (min_le_left _ _)).le
    · refine le_iInf₂ fun q hq => ?_
      obtain ⟨p, hpq, hpc', hpU⟩ := F1 q hq
      exact (ratEntrance_le (hpc _ hpc').1 hpU).trans (ENNReal.coe_le_coe.2 hpq)
  · refine iInf₂_eq_top.2 fun q hq => ?_
    exfalso
    obtain ⟨p, -, hpc', hpU⟩ := F1 q hq
    exact hR (lt_of_le_of_lt (ratEntrance_le (hpc _ hpc').1 hpU) (ENNReal.coe_lt_coe.2 (hpc _ hpc').2))

end Capped

/-! ### The stops `τₙ = R ∧ m ∧ σₙ` -/

section Seq

/-- The capped entrance `R ∧ m` as a real time. -/
def capStop (R : ℝ≥0∞) (m : ℝ≥0) : ℝ≥0 := (min R m).toNNReal

/-- The stops `τₙ = R ∧ m ∧ σₙ`. -/
def seqStop (R : ℝ≥0∞) (m : ℝ≥0) (σ : ℕ → ℝ≥0) (n : ℕ) : ℝ≥0 := min (capStop R m) (σ n)

/-- Their supremum `c̃ = sup τₙ`. -/
def supStop (R : ℝ≥0∞) (m : ℝ≥0) (σ : ℕ → ℝ≥0) : ℝ≥0 := ⨆ n, seqStop R m σ n

/-- The event `{c̃ < m and c̃ is attained}`, read from the stops `τₙ`. -/
def IsEntered (R : ℝ≥0∞) (m : ℝ≥0) (σ : ℕ → ℝ≥0) : Prop :=
  supStop R m σ < m ∧ ∃ n, supStop R m σ ≤ seqStop R m σ n

variable {R : ℝ≥0∞} {m : ℝ≥0} {σ : ℕ → ℝ≥0} {ζ : ℝ≥0∞}

theorem coe_capStop (R : ℝ≥0∞) (m : ℝ≥0) : ((capStop R m : ℝ≥0) : ℝ≥0∞) = min R m :=
  ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))

theorem capStop_le (R : ℝ≥0∞) (m : ℝ≥0) : capStop R m ≤ m := by
  rw [← ENNReal.coe_le_coe, coe_capStop]; exact min_le_right _ _

theorem seqStop_le_m (n : ℕ) : seqStop R m σ n ≤ m := (min_le_left _ _).trans (capStop_le R m)

theorem seqStop_le_σ (n : ℕ) : seqStop R m σ n ≤ σ n := min_le_right _ _

theorem coe_seqStop_le_R (n : ℕ) : (seqStop R m σ n : ℝ≥0∞) ≤ R := by
  have : (seqStop R m σ n : ℝ≥0∞) ≤ (capStop R m : ℝ≥0∞) := ENNReal.coe_le_coe.2 (min_le_left _ _)
  rw [coe_capStop] at this
  exact this.trans (min_le_left _ _)

theorem monotone_seqStop (hσm : Monotone σ) : Monotone (seqStop R m σ) := fun _ _ h =>
  min_le_min_left _ (hσm h)

theorem bddAbove_seqStop : BddAbove (range (seqStop R m σ)) :=
  ⟨m, by rintro _ ⟨n, rfl⟩; exact seqStop_le_m n⟩

theorem seqStop_le_supStop (n : ℕ) : seqStop R m σ n ≤ supStop R m σ := le_ciSup bddAbove_seqStop n

theorem supStop_le_m : supStop R m σ ≤ m := ciSup_le fun n => seqStop_le_m n

theorem exists_le_seqStop_of_lt {s : ℝ≥0} (hs : s < supStop R m σ) : ∃ n, s ≤ seqStop R m σ n := by
  obtain ⟨n, hn⟩ := (lt_ciSup_iff bddAbove_seqStop).1 hs
  exact ⟨n, hn.le⟩

variable (hσm : Monotone σ) (hσζ : ∀ n, (σ n : ℝ≥0∞) < ζ) (hσex : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∃ n, t ≤ σ n)
  (hRζ : R < ⊤ → R < ζ)

include hσex hRζ in
/-- Before the cap, the entrance is attained by the stops. -/
theorem supStop_eq_of_lt (hR : R < m) :
    supStop R m σ = R.toNNReal ∧ ∃ n, seqStop R m σ n = R.toNNReal := by
  have hRtop : R ≠ ⊤ := ne_top_of_lt hR
  have hcap : capStop R m = R.toNNReal := by rw [capStop, min_eq_left hR.le]
  obtain ⟨n, hn⟩ := hσex R.toNNReal (by rw [ENNReal.coe_toNNReal hRtop]; exact hRζ (lt_top_iff_ne_top.2 hRtop))
  have hseq : seqStop R m σ n = R.toNNReal := by rw [seqStop, hcap, min_eq_left hn]
  refine ⟨le_antisymm (ciSup_le fun k => ?_) (hseq ▸ seqStop_le_supStop n), n, hseq⟩
  rw [seqStop, hcap]; exact min_le_left _ _

include hσζ hσex hRζ in
/-- **The entrance event read from the stops is `{R < m}`.** -/
theorem isEntered_iff : IsEntered R m σ ↔ R < m := by
  constructor
  · rintro ⟨hlt, n, hn⟩
    by_contra hR
    have hcap : capStop R m = m := by
      rw [capStop, min_eq_right (not_lt.1 hR), ENNReal.toNNReal_coe]
    have hseq : ∀ k, seqStop R m σ k = min m (σ k) := fun k => by rw [seqStop, hcap]
    have hn' : seqStop R m σ n = supStop R m σ := le_antisymm (seqStop_le_supStop n) hn
    have hσn : σ n = supStop R m σ := by
      rw [hseq] at hn'
      rcases le_total m (σ n) with h | h
      · rw [min_eq_left h] at hn'; exact absurd hn' (ne_of_gt hlt)
      · rwa [min_eq_right h] at hn'
    have hall : ∀ k, σ k ≤ σ n := fun k => by
      have h1 := seqStop_le_supStop (R := R) (m := m) (σ := σ) k
      rw [hseq] at h1
      rcases le_total m (σ k) with h | h
      · rw [min_eq_left h] at h1; exact absurd (lt_of_le_of_lt h1 hlt) (lt_irrefl _)
      · rw [min_eq_right h] at h1; exact h1.trans hσn.symm.le
    obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (hσζ n)
    obtain ⟨k, hk⟩ := hσex r hr2
    exact absurd ((hk.trans (hall k))) (not_le.2 (ENNReal.coe_lt_coe.1 hr1))
  · intro hR
    obtain ⟨hsup, n, hn⟩ := supStop_eq_of_lt hσex hRζ hR
    refine ⟨?_, n, hsup ▸ hn.symm ▸ le_rfl⟩
    rw [hsup, ← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal (ne_top_of_lt hR)]
    exact hR

include hσζ hσex hRζ in
theorem supStop_eq_of_isEntered (h : IsEntered R m σ) : (supStop R m σ : ℝ≥0∞) = R := by
  have hR := (isEntered_iff hσζ hσex hRζ).1 h
  rw [(supStop_eq_of_lt hσex hRζ hR).1, ENNReal.coe_toNNReal (ne_top_of_lt hR)]

include hσζ hσex hRζ in
/-- Off the entrance event, `c̃ = ζ ∧ m`. -/
theorem supStop_eq_of_not_isEntered (h : ¬ IsEntered R m σ) : (supStop R m σ : ℝ≥0∞) = min ζ m := by
  have hR : ¬ R < m := fun hR => h ((isEntered_iff hσζ hσex hRζ).2 hR)
  have hcap : capStop R m = m := by
    rw [capStop, min_eq_right (not_lt.1 hR), ENNReal.toNNReal_coe]
  have hseq : ∀ k, seqStop R m σ k = min m (σ k) := fun k => by rw [seqStop, hcap]
  refine le_antisymm (le_min ?_ (ENNReal.coe_le_coe.2 supStop_le_m)) ?_
  · rw [supStop, ENNReal.coe_iSup bddAbove_seqStop]
    exact iSup_le fun k => (ENNReal.coe_le_coe.2 (seqStop_le_σ k)).trans (hσζ k).le
  · rcases lt_or_ge (m : ℝ≥0∞) ζ with hmζ | hζm
    · obtain ⟨n, hn⟩ := hσex m hmζ
      refine (min_le_right _ _).trans (ENNReal.coe_le_coe.2 ?_)
      refine le_trans ?_ (seqStop_le_supStop n)
      rw [hseq, min_eq_left hn]
    · rw [min_eq_left hζm]
      refine le_of_forall_lt fun b hb => ?_
      obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hb
      obtain ⟨n, hn⟩ := hσex r hr2
      have hrm : r ≤ m := ENNReal.coe_le_coe.1 (hr2.le.trans hζm)
      refine lt_of_lt_of_le hr1 (ENNReal.coe_le_coe.2 ((le_min hrm hn).trans ?_))
      rw [← hseq]; exact seqStop_le_supStop n

include hσζ hσex hRζ in
/-- Off the entrance event, the stops reach the cap exactly when the cap is before the lifetime. -/
theorem exists_m_le_seqStop_iff (h : ¬ IsEntered R m σ) :
    (∃ n, m ≤ seqStop R m σ n) ↔ (m : ℝ≥0∞) < ζ := by
  have hR : ¬ R < m := fun hR => h ((isEntered_iff hσζ hσex hRζ).2 hR)
  have hcap : capStop R m = m := by
    rw [capStop, min_eq_right (not_lt.1 hR), ENNReal.toNNReal_coe]
  constructor
  · rintro ⟨n, hn⟩
    exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (hn.trans (seqStop_le_σ n))) (hσζ n)
  · intro hmζ
    obtain ⟨n, hn⟩ := hσex m hmζ
    exact ⟨n, by rw [seqStop, hcap, min_eq_left hn]⟩

end Seq

end WholeField

end InteractingSLE
