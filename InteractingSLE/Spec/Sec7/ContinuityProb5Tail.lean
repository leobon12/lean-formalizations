/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb5Band
import InteractingSLE.Spec.Sec7.ContinuityProb4Restart
import InteractingSLE.Spec.Sec7.ContinuityProbGaps

/-!
# §7.3: infinite bands with a discrete angular-clock cutoff

Packet PROVE-SEC7-C5. Specification §7.3, Aux. lemma 106 (`source/spec/p337-384.md` L392, p. 354): "If `a ≤ 0` or
`b ≤ 0`, Aux. lemma 102 gives finite total angular clock. The alternating bands `U ≤ 2/3` and `U ≥ 1/3` have only
finitely many switches on that clock […]. On the final infinite band, deleting the opposite mark has finite energy,
bounded by a constant times `∫ D^{-2} dt`. Apply the bounded-energy comparison from each adapted band starting time with
an additional integer angular-clock cutoff, and take the countable union"; the same step for `N` groups in Aux. lemma
113 (pp. 370–371, the alternatives `s_L ≤ −2` or `s_R ≤ −2` of (TI13.1)).

The angular clock `∫ D^{-2}` (`D = V^{R,j₀} − V^{L,i₀}` the nearest-group cross-gap, nondecreasing) is replaced in the
stopping rule by its **discrete upper bound** `discClock t = Σ_{k ≤ ⌊t⌋} D(k)^{-2}` (integer sampling times), which is
adapted, Borel on codes, and finite exactly when the angular clock is (`D` is monotone). The band deleting the right
group runs while the driver stays at distance more than `D/4` from the nearest right mark (`U < 3/4`) and the discrete
clock stays below `m`; on it every right gap is at least `D_0/4` and the energy of the deletion is at most
`16 (Σ |ρ^R|)² m / κ`, so the whole-tail band transfer `ae_traceEvent_of_changeWeights_tail` applies.

## Main results

* `crossGap`, `discClock`, `ExitR`, `ExitL`, `tailHorizonR`, `tailHorizonL` and their path lemmas;
* `integral_inv_sq_crossGap_le`: `∫₀ᵗ D^{-2} ≤ Σ_{k < ⌈t⌉} D(k)^{-2}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace Band

variable {nL nR : ℕ}

/-! ### The cross-gap and the discrete angular clock -/

/-- The nearest-group cross-gap `D = V^{R,j₀} − V^{L,i₀}`. -/
def crossGap (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (i₀ : Fin nL) (j₀ : Fin nR) (s : ℝ≥0) : ℝ :=
  vR j₀ s - vL i₀ s

/-- **The discrete angular clock** `Σ_{k ≤ ⌊t⌋} D(k)^{-2}`. -/
def discClock (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (i₀ : Fin nL) (j₀ : Fin nR) (t : ℝ≥0) : ℝ :=
  ∑ k ∈ Finset.range (⌊(t : ℝ)⌋₊ + 1), (crossGap vL vR i₀ j₀ k)⁻¹ ^ 2

/-- Exit from the band deleting the right group: the driver is within `D/4` of the nearest right mark, or the
discrete clock has reached `m`. -/
def ExitR (m : ℕ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (i₀ : Fin nL) (j₀ : Fin nR)
    (s : ℝ≥0) : Prop :=
  4 * (vR j₀ s - w s) ≤ crossGap vL vR i₀ j₀ s ∨ (m : ℝ) ≤ discClock vL vR i₀ j₀ s

/-- Exit from the band deleting the left group. -/
def ExitL (m : ℕ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (i₀ : Fin nL) (j₀ : Fin nR)
    (s : ℝ≥0) : Prop :=
  4 * (w s - vL i₀ s) ≤ crossGap vL vR i₀ j₀ s ∨ (m : ℝ) ≤ discClock vL vR i₀ j₀ s

/-- **The horizon of the infinite band deleting the right group.** -/
def tailHorizonR (m : ℕ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (i₀ : Fin nL)
    (j₀ : Fin nR) (ζ : ℝ≥0∞) : ℝ≥0∞ :=
  min (hitTime (ExitR m w vL vR i₀ j₀) ζ) ζ

/-- **The horizon of the infinite band deleting the left group.** -/
def tailHorizonL (m : ℕ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (i₀ : Fin nL)
    (j₀ : Fin nR) (ζ : ℝ≥0∞) : ℝ≥0∞ :=
  min (hitTime (ExitL m w vL vR i₀ j₀) ζ) ζ

section Path

variable {m : ℕ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {i₀ : Fin nL} {j₀ : Fin nR}
  {ζ : ℝ≥0∞}

theorem tailHorizonR_le_lifetime : tailHorizonR m w vL vR i₀ j₀ ζ ≤ ζ := min_le_right _ _

theorem tailHorizonL_le_lifetime : tailHorizonL m w vL vR i₀ j₀ ζ ≤ ζ := min_le_right _ _

theorem discClock_mono {s t : ℝ≥0} (hst : s ≤ t) :
    discClock vL vR i₀ j₀ s ≤ discClock vL vR i₀ j₀ t := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => sq_nonneg _
  refine Finset.range_subset_range.2 (Nat.add_le_add_right (Nat.floor_le_floor ?_) 1)
  exact_mod_cast hst

/-- Before an exit hitting time, the discrete clock is below `m`. -/
theorem discClock_lt_of_lt_hitTime {p : ℝ≥0 → Prop} (hp : ∀ s, (m : ℝ) ≤ discClock vL vR i₀ j₀ s → p s)
    {t : ℝ≥0} (htζ : (t : ℝ≥0∞) < ζ) (ht : (t : ℝ≥0∞) < hitTime p ζ) :
    discClock vL vR i₀ j₀ t < m := by
  by_contra hge
  rw [not_lt] at hge
  obtain ⟨q, -, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 (lt_min ht htζ)
  have hq1' : t ≤ Real.toNNReal q := by exact_mod_cast hq1.le
  have hp' : p (Real.toNNReal q) := hp _ (hge.trans (discClock_mono hq1'))
  have hle := hitTime_le (lt_of_lt_of_le hq2 (min_le_right _ _)) hp'
  exact absurd (lt_of_lt_of_le hq2 (min_le_left _ _)) (not_lt.2 hle)

/-- Before the right-band horizon the discrete clock is below `m`. -/
theorem discClock_lt_of_lt_tailHorizonR {t : ℝ≥0} (ht : (t : ℝ≥0∞) < tailHorizonR m w vL vR i₀ j₀ ζ) :
    discClock vL vR i₀ j₀ t < m :=
  discClock_lt_of_lt_hitTime (fun _ hs => Or.inr hs) (ht.trans_le tailHorizonR_le_lifetime)
    (ht.trans_le (min_le_left _ _))

/-- Before the left-band horizon the discrete clock is below `m`. -/
theorem discClock_lt_of_lt_tailHorizonL {t : ℝ≥0} (ht : (t : ℝ≥0∞) < tailHorizonL m w vL vR i₀ j₀ ζ) :
    discClock vL vR i₀ j₀ t < m :=
  discClock_lt_of_lt_hitTime (fun _ hs => Or.inr hs) (ht.trans_le tailHorizonL_le_lifetime)
    (ht.trans_le (min_le_left _ _))

/-- Before the right-band horizon the driver is at distance at least `D/4` from the nearest right mark. -/
theorem crossGap_le_of_lt_tailHorizonR (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hvL : ∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < ζ}) (hvR : ∀ j, ContinuousOn (vR j) {t | (t : ℝ≥0∞) < ζ})
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < tailHorizonR m w vL vR i₀ j₀ ζ) :
    crossGap vL vR i₀ j₀ t ≤ 4 * (vR j₀ t - w t) := by
  have htζ : (t : ℝ≥0∞) < ζ := ht.trans_le tailHorizonR_le_lifetime
  have hth : (t : ℝ≥0∞) < hitTime (fun s => 4 * (vR j₀ s - w s) - crossGap vL vR i₀ j₀ s ≤ 0) ζ :=
    (ht.trans_le (min_le_left _ _)).trans_le (hitTime_mono fun s hs => Or.inl (by linarith))
  have h := le_of_lt_hitTime (((hvR j₀).sub hw).const_smul (4 : ℝ) |>.sub ((hvR j₀).sub (hvL i₀)))
    htζ hth
  simp only [crossGap, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
  linarith

/-- Before the left-band horizon the driver is at distance at least `D/4` from the nearest left mark. -/
theorem crossGap_le_of_lt_tailHorizonL (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hvL : ∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < ζ}) (hvR : ∀ j, ContinuousOn (vR j) {t | (t : ℝ≥0∞) < ζ})
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < tailHorizonL m w vL vR i₀ j₀ ζ) :
    crossGap vL vR i₀ j₀ t ≤ 4 * (w t - vL i₀ t) := by
  have htζ : (t : ℝ≥0∞) < ζ := ht.trans_le tailHorizonL_le_lifetime
  have hth : (t : ℝ≥0∞) < hitTime (fun s => 4 * (w s - vL i₀ s) - crossGap vL vR i₀ j₀ s ≤ 0) ζ :=
    (ht.trans_le (min_le_left _ _)).trans_le (hitTime_mono fun s hs => Or.inl (by linarith))
  have h := le_of_lt_hitTime ((hw.sub (hvL i₀)).const_smul (4 : ℝ) |>.sub ((hvR j₀).sub (hvL i₀)))
    htζ hth
  simp only [crossGap, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
  linarith

end Path

/-! ### Integrals against the integer step function -/

theorem integral_floor_step (c : ℕ → ℝ) (k : ℕ) : ∫ s in (k : ℝ)..(k + 1 : ℝ), c ⌊s⌋₊ = c k := by
  have e : ∫ s in (k : ℝ)..(k + 1 : ℝ), c ⌊s⌋₊ = ∫ _ in (k : ℝ)..(k + 1 : ℝ), c k := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Girsanov.ae_ne_real ((k : ℝ) + 1)] with s hs hmem
    rw [uIoc_of_le (by linarith)] at hmem
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    congr 1
    rw [Nat.floor_eq_iff (show (0 : ℝ) ≤ s by linarith [hmem.1])]
    exact ⟨hmem.1.le, lt_of_le_of_ne hmem.2 hs⟩
  rw [e, intervalIntegral.integral_const]
  simp

theorem intervalIntegrable_floor_step {c : ℕ → ℝ} (hc : ∀ k, 0 ≤ c k) (n : ℕ) :
    IntervalIntegrable (fun s : ℝ => c ⌊s⌋₊) volume 0 n := by
  refine (intervalIntegrable_const (c := ∑ k ∈ Finset.range (n + 1), c k)).mono_fun'
    ((measurable_from_nat (f := c)).comp Nat.measurable_floor).aestronglyMeasurable ?_
  rw [EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
  refine Eventually.of_forall fun s hs => ?_
  rw [uIoc_of_le (Nat.cast_nonneg n)] at hs
  rw [Real.norm_eq_abs, abs_of_nonneg (hc _)]
  refine Finset.single_le_sum (fun k _ => hc k) (Finset.mem_range.2 (Nat.lt_succ_of_le ?_))
  exact Nat.floor_le_of_le hs.2

theorem integral_floor_step_nat {c : ℕ → ℝ} (hc : ∀ k, 0 ≤ c k) (n : ℕ) :
    ∫ s in (0 : ℝ)..(n : ℝ), c ⌊s⌋₊ = ∑ k ∈ Finset.range n, c k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := intervalIntegrable_floor_step hc n
    have h2 : IntervalIntegrable (fun s : ℝ => c ⌊s⌋₊) volume n (n + 1) := by
      have := intervalIntegrable_floor_step hc (n + 1)
      push_cast at this
      exact this.mono_set (by
        rw [uIcc_of_le (by linarith : (n : ℝ) ≤ n + 1),
          uIcc_of_le (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
        exact Icc_subset_Icc (Nat.cast_nonneg n) le_rfl)
    rw [Finset.sum_range_succ, ← ih, Nat.cast_succ, ← intervalIntegral.integral_add_adjacent_intervals h1 h2,
      integral_floor_step]

/-- **`∫₀ᵗ f ≤ Σ_{k < ⌈t⌉} c(k)`** when `0 ≤ f(s) ≤ c(⌊s⌋)` on `[0, t)` and `c ≥ 0`. -/
theorem integral_le_sum_ceil {f : ℝ → ℝ} {c : ℕ → ℝ} (hc : ∀ k, 0 ≤ c k) {t : ℝ} (ht : 0 ≤ t)
    (hf : IntervalIntegrable f volume 0 t) (hfc : ∀ s ∈ Ico 0 t, f s ≤ c ⌊s⌋₊) :
    ∫ s in (0 : ℝ)..t, f s ≤ ∑ k ∈ Finset.range ⌈t⌉₊, c k := by
  have hceil : t ≤ ⌈t⌉₊ := Nat.le_ceil t
  have hg : IntervalIntegrable (fun s : ℝ => c ⌊s⌋₊) volume 0 ⌈t⌉₊ := intervalIntegrable_floor_step hc _
  have hg' : IntervalIntegrable (fun s : ℝ => c ⌊s⌋₊) volume 0 t :=
    hg.mono_set (by rw [uIcc_of_le ht, uIcc_of_le (Nat.cast_nonneg _)]; exact Icc_subset_Icc le_rfl hceil)
  have hg'' : IntervalIntegrable (fun s : ℝ => c ⌊s⌋₊) volume t ⌈t⌉₊ :=
    hg.mono_set (by
      rw [uIcc_of_le hceil, uIcc_of_le (Nat.cast_nonneg _)]
      exact Icc_subset_Icc ht le_rfl)
  calc ∫ s in (0 : ℝ)..t, f s ≤ ∫ s in (0 : ℝ)..t, c ⌊s⌋₊ :=
        intervalIntegral.integral_mono_on_of_le_Ioo ht hf hg' fun s hs => hfc s ⟨hs.1.le, hs.2⟩
    _ ≤ ∫ s in (0 : ℝ)..(⌈t⌉₊ : ℝ), c ⌊s⌋₊ := by
        rw [← intervalIntegral.integral_add_adjacent_intervals hg' hg'']
        have : 0 ≤ ∫ s in t..(⌈t⌉₊ : ℝ), c ⌊s⌋₊ :=
          intervalIntegral.integral_nonneg hceil fun s _ => hc _
        linarith
    _ = ∑ k ∈ Finset.range ⌈t⌉₊, c k := integral_floor_step_nat hc _

/-! ### The energy of the band deletion -/

/-- The cut integrand of deleting the right group is at most `Σ|ρ^R| / (√κ g)` when every right gap is at least
`g ≥ δ`. -/
theorem abs_shiftIntegrand_delR_le {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {w : ℝ} {u : Fin (nL + nR) → ℝ} {g : ℝ} (hg : δ ≤ g)
    (hgap : ∀ j, g ≤ u (Fin.natAdd nL j) - w) :
    |Girsanov.shiftIntegrand κ 1 δ (Sec2.weightDiff ρL ρL ρR 0) w u| ≤ (∑ j, |ρR j|) / (Real.sqrt κ * g) := by
  have hg0 : 0 < g := hδ.trans_le hg
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hsum : Girsanov.addedDriftCut (Sec2.weightDiff ρL ρL ρR 0) δ w u =
      ∑ j, (-ρR j) * Girsanov.recipCut δ (w - u (Fin.natAdd nL j)) := by
    simp only [Girsanov.addedDriftCut, Fin.sum_univ_add, Sec2.weightDiff, Fin.addCases_left,
      Fin.addCases_right, sub_self, zero_mul, Finset.sum_const_zero, zero_add, Pi.zero_apply, zero_sub]
  have hterm : ∀ j, |(-ρR j) * Girsanov.recipCut δ (w - u (Fin.natAdd nL j))| ≤ |ρR j| / g := by
    intro j
    have hj := hgap j
    have hx : δ ≤ |w - u (Fin.natAdd nL j)| := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    rw [Girsanov.recipCut_of_le hδ hx, abs_mul, abs_neg, abs_inv, abs_sub_comm,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ u (Fin.natAdd nL j) - w), div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hg0 hj) (abs_nonneg _)
  rw [Girsanov.shiftIntegrand, hsum, abs_mul, abs_neg, abs_div, abs_one, abs_of_pos hsk]
  calc 1 / Real.sqrt κ * |∑ j, (-ρR j) * Girsanov.recipCut δ (w - u (Fin.natAdd nL j))|
      ≤ 1 / Real.sqrt κ * ∑ j, |ρR j| / g :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun j _ => hterm j)) (by positivity)
    _ = (∑ j, |ρR j|) / (Real.sqrt κ * g) := by
        rw [← Finset.sum_div]; field_simp

/-- The cut integrand of deleting the left group is at most `Σ|ρ^L| / (√κ g)` when every left gap is at least
`g ≥ δ`. -/
theorem abs_shiftIntegrand_delL_le {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {w : ℝ} {u : Fin (nL + nR) → ℝ} {g : ℝ} (hg : δ ≤ g)
    (hgap : ∀ i, g ≤ w - u (Fin.castAdd nR i)) :
    |Girsanov.shiftIntegrand κ 1 δ (Sec2.weightDiff ρL 0 ρR ρR) w u| ≤ (∑ i, |ρL i|) / (Real.sqrt κ * g) := by
  have hg0 : 0 < g := hδ.trans_le hg
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hsum : Girsanov.addedDriftCut (Sec2.weightDiff ρL 0 ρR ρR) δ w u =
      ∑ i, (-ρL i) * Girsanov.recipCut δ (w - u (Fin.castAdd nR i)) := by
    simp only [Girsanov.addedDriftCut, Fin.sum_univ_add, Sec2.weightDiff, Fin.addCases_left,
      Fin.addCases_right, sub_self, zero_mul, Finset.sum_const_zero, add_zero, Pi.zero_apply, zero_sub]
  have hterm : ∀ i, |(-ρL i) * Girsanov.recipCut δ (w - u (Fin.castAdd nR i))| ≤ |ρL i| / g := by
    intro i
    have hi := hgap i
    have hx : δ ≤ |w - u (Fin.castAdd nR i)| := by
      rw [abs_of_nonneg (by linarith)]; linarith
    rw [Girsanov.recipCut_of_le hδ hx, abs_mul, abs_neg, abs_inv,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ w - u (Fin.castAdd nR i)), div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hg0 hi) (abs_nonneg _)
  rw [Girsanov.shiftIntegrand, hsum, abs_mul, abs_neg, abs_div, abs_one, abs_of_pos hsk]
  calc 1 / Real.sqrt κ * |∑ i, (-ρL i) * Girsanov.recipCut δ (w - u (Fin.castAdd nR i))|
      ≤ 1 / Real.sqrt κ * ∑ i, |ρL i| / g :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => hterm i)) (by positivity)
    _ = (∑ i, |ρL i|) / (Real.sqrt κ * g) := by
        rw [← Finset.sum_div]; field_simp


/-! ### The energy bound along a path -/

section Energy

variable {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
  {i₀ : Fin nL} {j₀ : Fin nR} {m : ℕ}

/-- `Σ_{k < ⌈t⌉} D(k)^{-2} < m` before the horizon `t ≤ τ` of a band with clock cutoff `m`. -/
theorem sum_ceil_lt_of_le {τ : ℝ≥0∞} (hτ : ∀ s : ℝ≥0, (s : ℝ≥0∞) < τ → discClock vL vR i₀ j₀ s < m)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ τ) :
    ∑ k ∈ Finset.range ⌈(t : ℝ)⌉₊, (crossGap vL vR i₀ j₀ k)⁻¹ ^ 2 ≤ m := by
  rcases Nat.eq_zero_or_pos ⌈(t : ℝ)⌉₊ with h0 | hpos
  · rw [h0, Finset.sum_range_zero]; exact Nat.cast_nonneg m
  · set n := ⌈(t : ℝ)⌉₊ - 1 with hn
    have hnt : (n : ℝ) < t := by
      have := Nat.ceil_lt_add_one (NNReal.coe_nonneg t)
      rw [hn, Nat.cast_sub hpos, Nat.cast_one]
      linarith
    have hlt : ((n : ℝ≥0) : ℝ≥0∞) < τ := by
      refine lt_of_lt_of_le ?_ ht
      rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]
      exact_mod_cast hnt
    have h := hτ n hlt
    have e : ⌊((n : ℝ≥0) : ℝ)⌋₊ + 1 = ⌈(t : ℝ)⌉₊ := by
      rw [NNReal.coe_natCast, Nat.floor_natCast, hn]; omega
    simp only [discClock, e] at h
    exact h.le

/-- **The energy of deleting the right group on the right band** is at most `16 (Σ |ρ^R|)² m / κ`. -/
theorem energy_delR_le {κ : ℝ} (hκ : 0 < κ) (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    (hj₀ : ∀ j, j₀ ≤ j) (hD0 : 0 < xR j₀ - xL i₀) {u : ℝ → Fin (nL + nR) → ℝ}
    (hu : ∀ s j, u s (Fin.natAdd nL j) = vR j s.toNNReal) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) ≤ tailHorizonR m w vL vR i₀ j₀ ζ) :
    ∫ s in (0 : ℝ)..t, Girsanov.shiftIntegrand κ 1 ((xR j₀ - xL i₀) / 4) (Sec2.weightDiff ρL ρL ρR 0)
        (w s.toNNReal) (u s) ^ 2 ≤ 16 * (∑ j, |ρR j|) ^ 2 / κ * m := by
  have hF := hp.isForcePath
  set S := ∑ j, |ρR j| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => abs_nonneg _
  set c : ℕ → ℝ := fun k => 16 * S ^ 2 / κ * (crossGap vL vR i₀ j₀ k)⁻¹ ^ 2 with hc
  have hc0 : ∀ k, 0 ≤ c k := fun k => by positivity
  have hD0' : crossGap vL vR i₀ j₀ 0 = xR j₀ - xL i₀ := by simp only [crossGap, hF.vL_zero, hF.vR_zero]
  have hbound : ∀ s ∈ Ico (0 : ℝ) t, Girsanov.shiftIntegrand κ 1 ((xR j₀ - xL i₀) / 4)
      (Sec2.weightDiff ρL ρL ρR 0) (w s.toNNReal) (u s) ^ 2 ≤ c ⌊s⌋₊ := by
    intro s hs
    have hst : (s.toNNReal : ℝ≥0∞) < tailHorizonR m w vL vR i₀ j₀ ζ := by
      refine lt_of_lt_of_le ?_ ht
      rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs.1]
      exact hs.2
    have hsζ : (s.toNNReal : ℝ≥0∞) < ζ := hst.trans_le tailHorizonR_le_lifetime
    have hq := crossGap_le_of_lt_tailHorizonR hF.continuousOn_w hF.continuousOn_vL hF.continuousOn_vR hst
    have hfl : ((⌊s⌋₊ : ℕ) : ℝ≥0) ≤ s.toNNReal := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1, NNReal.coe_natCast]
      exact Nat.floor_le hs.1
    have hDk : xR j₀ - xL i₀ ≤ crossGap vL vR i₀ j₀ (⌊s⌋₊ : ℝ≥0) := by
      rw [← hD0']; exact hF.crossGap_le i₀ j₀ zero_le (lt_of_le_of_lt (by exact_mod_cast hfl) hsζ)
    have hDs : crossGap vL vR i₀ j₀ (⌊s⌋₊ : ℝ≥0) ≤ crossGap vL vR i₀ j₀ s.toNNReal :=
      hF.crossGap_le i₀ j₀ hfl hsζ
    have hDk0 : 0 < crossGap vL vR i₀ j₀ (⌊s⌋₊ : ℝ≥0) := hD0.trans_le hDk
    have hgap : ∀ j, crossGap vL vR i₀ j₀ s.toNNReal / 4 ≤ u s (Fin.natAdd nL j) - w s.toNNReal := by
      intro j
      rw [hu]
      have := hF.monotone_vR hsζ (hj₀ j)
      linarith
    have hδg : (xR j₀ - xL i₀) / 4 ≤ crossGap vL vR i₀ j₀ s.toNNReal / 4 := by linarith
    have habs := abs_shiftIntegrand_delR_le hκ (by linarith) ρL ρR hδg hgap
    have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
    rw [← sq_abs]
    calc |Girsanov.shiftIntegrand κ 1 ((xR j₀ - xL i₀) / 4) (Sec2.weightDiff ρL ρL ρR 0) (w s.toNNReal)
            (u s)| ^ 2
        ≤ (S / (Real.sqrt κ * (crossGap vL vR i₀ j₀ s.toNNReal / 4))) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ ≤ (S / (Real.sqrt κ * (crossGap vL vR i₀ j₀ (⌊s⌋₊ : ℝ≥0) / 4))) ^ 2 := by
          refine pow_le_pow_left₀ (div_nonneg hS0 (mul_pos hsk (by linarith)).le) ?_ 2
          exact div_le_div_of_nonneg_left hS0 (mul_pos hsk (by linarith))
            (mul_le_mul_of_nonneg_left (by linarith) hsk.le)
      _ = c ⌊s⌋₊ := by
          rw [hc]
          simp only
          rw [div_pow, mul_pow, div_pow, Real.sq_sqrt hκ.le, inv_pow]
          field_simp
          ring
  have hsum := sum_ceil_lt_of_le (τ := tailHorizonR m w vL vR i₀ j₀ ζ)
    (fun s hs => discClock_lt_of_lt_tailHorizonR hs) ht
  by_cases hint : IntervalIntegrable (fun s : ℝ => Girsanov.shiftIntegrand κ 1 ((xR j₀ - xL i₀) / 4)
      (Sec2.weightDiff ρL ρL ρR 0) (w s.toNNReal) (u s) ^ 2) volume 0 t
  · refine (integral_le_sum_ceil hc0 t.coe_nonneg hint hbound).trans ?_
    rw [hc]
    simp only
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  · rw [intervalIntegral.integral_undef hint]
    positivity

/-- **The energy of deleting the left group on the left band** is at most `16 (Σ |ρ^L|)² m / κ`. -/
theorem energy_delL_le {κ : ℝ} (hκ : 0 < κ) (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    (hi₀ : ∀ i, i₀ ≤ i) (hD0 : 0 < xR j₀ - xL i₀) {u : ℝ → Fin (nL + nR) → ℝ}
    (hu : ∀ s i, u s (Fin.castAdd nR i) = vL i s.toNNReal) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) ≤ tailHorizonL m w vL vR i₀ j₀ ζ) :
    ∫ s in (0 : ℝ)..t, Girsanov.shiftIntegrand κ 1 ((xR j₀ - xL i₀) / 4) (Sec2.weightDiff ρL 0 ρR ρR)
        (w s.toNNReal) (u s) ^ 2 ≤ 16 * (∑ i, |ρL i|) ^ 2 / κ * m := by
  have hF := hp.isForcePath
  set S := ∑ i, |ρL i| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => abs_nonneg _
  set c : ℕ → ℝ := fun k => 16 * S ^ 2 / κ * (crossGap vL vR i₀ j₀ k)⁻¹ ^ 2 with hc
  have hc0 : ∀ k, 0 ≤ c k := fun k => by positivity
  have hD0' : crossGap vL vR i₀ j₀ 0 = xR j₀ - xL i₀ := by simp only [crossGap, hF.vL_zero, hF.vR_zero]
  have hbound : ∀ s ∈ Ico (0 : ℝ) t, Girsanov.shiftIntegrand κ 1 ((xR j₀ - xL i₀) / 4)
      (Sec2.weightDiff ρL 0 ρR ρR) (w s.toNNReal) (u s) ^ 2 ≤ c ⌊s⌋₊ := by
    intro s hs
    have hst : (s.toNNReal : ℝ≥0∞) < tailHorizonL m w vL vR i₀ j₀ ζ := by
      refine lt_of_lt_of_le ?_ ht
      rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs.1]
      exact hs.2
    have hsζ : (s.toNNReal : ℝ≥0∞) < ζ := hst.trans_le tailHorizonL_le_lifetime
    have hq := crossGap_le_of_lt_tailHorizonL hF.continuousOn_w hF.continuousOn_vL hF.continuousOn_vR hst
    have hfl : ((⌊s⌋₊ : ℕ) : ℝ≥0) ≤ s.toNNReal := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1, NNReal.coe_natCast]
      exact Nat.floor_le hs.1
    have hDk : xR j₀ - xL i₀ ≤ crossGap vL vR i₀ j₀ (⌊s⌋₊ : ℝ≥0) := by
      rw [← hD0']; exact hF.crossGap_le i₀ j₀ zero_le (lt_of_le_of_lt (by exact_mod_cast hfl) hsζ)
    have hDs : crossGap vL vR i₀ j₀ (⌊s⌋₊ : ℝ≥0) ≤ crossGap vL vR i₀ j₀ s.toNNReal :=
      hF.crossGap_le i₀ j₀ hfl hsζ
    have hDk0 : 0 < crossGap vL vR i₀ j₀ (⌊s⌋₊ : ℝ≥0) := hD0.trans_le hDk
    have hgap : ∀ i, crossGap vL vR i₀ j₀ s.toNNReal / 4 ≤ w s.toNNReal - u s (Fin.castAdd nR i) := by
      intro i
      rw [hu]
      have := hF.antitone_vL hsζ (hi₀ i)
      linarith
    have hδg : (xR j₀ - xL i₀) / 4 ≤ crossGap vL vR i₀ j₀ s.toNNReal / 4 := by linarith
    have habs := abs_shiftIntegrand_delL_le hκ (by linarith) ρL ρR hδg hgap
    have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
    rw [← sq_abs]
    calc |Girsanov.shiftIntegrand κ 1 ((xR j₀ - xL i₀) / 4) (Sec2.weightDiff ρL 0 ρR ρR) (w s.toNNReal)
            (u s)| ^ 2
        ≤ (S / (Real.sqrt κ * (crossGap vL vR i₀ j₀ s.toNNReal / 4))) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ ≤ (S / (Real.sqrt κ * (crossGap vL vR i₀ j₀ (⌊s⌋₊ : ℝ≥0) / 4))) ^ 2 := by
          refine pow_le_pow_left₀ (div_nonneg hS0 (mul_pos hsk (by linarith)).le) ?_ 2
          exact div_le_div_of_nonneg_left hS0 (mul_pos hsk (by linarith))
            (mul_le_mul_of_nonneg_left (by linarith) hsk.le)
      _ = c ⌊s⌋₊ := by
          rw [hc]
          simp only
          rw [div_pow, mul_pow, div_pow, Real.sq_sqrt hκ.le, inv_pow]
          field_simp
          ring
  have hsum := sum_ceil_lt_of_le (τ := tailHorizonL m w vL vR i₀ j₀ ζ)
    (fun s hs => discClock_lt_of_lt_tailHorizonL hs) ht
  by_cases hint : IntervalIntegrable (fun s : ℝ => Girsanov.shiftIntegrand κ 1 ((xR j₀ - xL i₀) / 4)
      (Sec2.weightDiff ρL 0 ρR ρR) (w s.toNNReal) (u s) ^ 2) volume 0 t
  · refine (integral_le_sum_ceil hc0 t.coe_nonneg hint hbound).trans ?_
    rw [hc]
    simp only
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  · rw [intervalIntegral.integral_undef hint]
    positivity

end Energy

/-! ### The tail horizons of an evolution are stopping times -/

section Process

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {i₀ : Fin nL} {j₀ : Fin nR}

/-- The killed value of an adapted-before process. -/
def killedAt (ζ : Ω → ℝ≥0∞) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : ℝ≥0∞) < ζ ω then X t ω else 0

theorem killedAt_of_lt {X : ℝ≥0 → Ω → ℝ} {t : ℝ≥0} {ω : Ω} (h : (t : ℝ≥0∞) < ζ ω) :
    killedAt ζ X t ω = X t ω := by simp only [killedAt, h, ite_true]

/-- On `{s < ζ}`, the discrete clock at `s` is a measurable function of the killed marks at the integer times
`k ≤ s`. -/
theorem measurableSet_lt_and_discClock (hVL : ∀ i, AdaptedBefore 𝓕 ζ (VL i))
    (hVR : ∀ j, AdaptedBefore 𝓕 ζ (VR j)) (s : ℝ≥0) (c : ℝ) :
    MeasurableSet[𝓕 s] {ω | (s : ℝ≥0∞) < ζ ω ∧
      c ≤ discClock (fun i t => VL i t ω) (fun j t => VR j t ω) i₀ j₀ s} := by
  have hζs : MeasurableSet[𝓕 s] {ω | (s : ℝ≥0∞) < ζ ω} := by
    have := hVL i₀ s univ MeasurableSet.univ
    simpa only [mem_univ, and_true] using this
  have hk : ∀ k ∈ Finset.range (⌊(s : ℝ)⌋₊ + 1), ((k : ℝ≥0)) ≤ s := fun k hk => by
    rw [← NNReal.coe_le_coe, NNReal.coe_natCast]
    exact (Nat.cast_le.2 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))).trans (Nat.floor_le s.coe_nonneg)
  have hm : Measurable[𝓕 s] fun ω => ∑ k ∈ Finset.range (⌊(s : ℝ)⌋₊ + 1),
      (killedAt ζ (VR j₀) k ω - killedAt ζ (VL i₀) k ω)⁻¹ ^ 2 := by
    refine Finset.measurable_sum _ fun k hk' => ?_
    have h1 := (Band.measurable_killed_of_adaptedBefore (hVR j₀) (k : ℝ≥0)).mono (𝓕.mono (hk k hk')) le_rfl
    have h2 := (Band.measurable_killed_of_adaptedBefore (hVL i₀) (k : ℝ≥0)).mono (𝓕.mono (hk k hk')) le_rfl
    exact ((h1.sub h2).inv).pow_const 2
  have e : {ω | (s : ℝ≥0∞) < ζ ω ∧ c ≤ discClock (fun i t => VL i t ω) (fun j t => VR j t ω) i₀ j₀ s} =
      {ω | (s : ℝ≥0∞) < ζ ω} ∩ {ω | c ≤ ∑ k ∈ Finset.range (⌊(s : ℝ)⌋₊ + 1),
        (killedAt ζ (VR j₀) k ω - killedAt ζ (VL i₀) k ω)⁻¹ ^ 2} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, and_congr_right_iff]
    intro hsζ
    have hsum : discClock (fun i t => VL i t ω) (fun j t => VR j t ω) i₀ j₀ s =
        ∑ k ∈ Finset.range (⌊(s : ℝ)⌋₊ + 1), (killedAt ζ (VR j₀) k ω - killedAt ζ (VL i₀) k ω)⁻¹ ^ 2 := by
      refine Finset.sum_congr rfl fun k hk' => ?_
      have hkζ : ((k : ℝ≥0) : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hk k hk') hsζ
      simp only [crossGap, killedAt_of_lt hkζ]
    rw [hsum]
  rw [e]
  exact hζs.inter (measurableSet_le measurable_const hm)

theorem isStoppingTime_tailHorizonR [𝓕.IsRightContinuous] (hW : AdaptedBefore 𝓕 ζ W)
    (hVL : ∀ i, AdaptedBefore 𝓕 ζ (VL i)) (hVR : ∀ j, AdaptedBefore 𝓕 ζ (VR j)) (m : ℕ) :
    IsStoppingTime 𝓕 fun ω =>
      (tailHorizonR m (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) i₀ j₀ (ζ ω) : WithTop ℝ≥0) := by
  have h1 : IsStoppingTime 𝓕 fun ω => (hitTime (ExitR m (fun t => W t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) i₀ j₀) (ζ ω) : WithTop ℝ≥0) := by
    refine isStoppingTime_hitTime fun s => ?_
    have e : {ω | (s : ℝ≥0∞) < ζ ω ∧ ExitR m (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
        i₀ j₀ s} = {ω | (s : ℝ≥0∞) < ζ ω ∧ (4 * (VR j₀ s ω - W s ω) - (VR j₀ s ω - VL i₀ s ω) ≤ 0)} ∪
        {ω | (s : ℝ≥0∞) < ζ ω ∧ (m : ℝ) ≤ discClock (fun i t => VL i t ω) (fun j t => VR j t ω) i₀ j₀ s} := by
      ext ω
      simp only [ExitR, crossGap, mem_ofPred_eq, mem_union]
      constructor
      · rintro ⟨h, h' | h'⟩
        · exact Or.inl ⟨h, by linarith⟩
        · exact Or.inr ⟨h, h'⟩
      · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
        · exact ⟨h, Or.inl (by linarith)⟩
        · exact ⟨h, Or.inr h'⟩
    rw [e]
    refine MeasurableSet.union ?_ (measurableSet_lt_and_discClock hVL hVR s _)
    have hζs : MeasurableSet[𝓕 s] {ω | (s : ℝ≥0∞) < ζ ω} := by
      have := hW s univ MeasurableSet.univ
      simpa only [mem_univ, and_true] using this
    have hm : Measurable[𝓕 s] fun ω => 4 * (killedAt ζ (VR j₀) s ω - killedAt ζ W s ω) -
        (killedAt ζ (VR j₀) s ω - killedAt ζ (VL i₀) s ω) :=
      (((Band.measurable_killed_of_adaptedBefore (hVR j₀) s).sub
        (Band.measurable_killed_of_adaptedBefore hW s)).const_mul 4).sub
        ((Band.measurable_killed_of_adaptedBefore (hVR j₀) s).sub
          (Band.measurable_killed_of_adaptedBefore (hVL i₀) s))
    have e2 : {ω | (s : ℝ≥0∞) < ζ ω ∧ (4 * (VR j₀ s ω - W s ω) - (VR j₀ s ω - VL i₀ s ω) ≤ 0)} =
        {ω | (s : ℝ≥0∞) < ζ ω} ∩ {ω | 4 * (killedAt ζ (VR j₀) s ω - killedAt ζ W s ω) -
          (killedAt ζ (VR j₀) s ω - killedAt ζ (VL i₀) s ω) ≤ 0} := by
      ext ω
      simp only [mem_ofPred_eq, mem_inter_iff, and_congr_right_iff]
      intro h
      simp only [killedAt_of_lt h]
    rw [e2]
    exact hζs.inter (measurableSet_le hm measurable_const)
  exact h1.min (Ito.isStoppingTime_lifetime hW)

theorem isStoppingTime_tailHorizonL [𝓕.IsRightContinuous] (hW : AdaptedBefore 𝓕 ζ W)
    (hVL : ∀ i, AdaptedBefore 𝓕 ζ (VL i)) (hVR : ∀ j, AdaptedBefore 𝓕 ζ (VR j)) (m : ℕ) :
    IsStoppingTime 𝓕 fun ω =>
      (tailHorizonL m (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) i₀ j₀ (ζ ω) : WithTop ℝ≥0) := by
  have h1 : IsStoppingTime 𝓕 fun ω => (hitTime (ExitL m (fun t => W t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) i₀ j₀) (ζ ω) : WithTop ℝ≥0) := by
    refine isStoppingTime_hitTime fun s => ?_
    have e : {ω | (s : ℝ≥0∞) < ζ ω ∧ ExitL m (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
        i₀ j₀ s} = {ω | (s : ℝ≥0∞) < ζ ω ∧ (4 * (W s ω - VL i₀ s ω) - (VR j₀ s ω - VL i₀ s ω) ≤ 0)} ∪
        {ω | (s : ℝ≥0∞) < ζ ω ∧ (m : ℝ) ≤ discClock (fun i t => VL i t ω) (fun j t => VR j t ω) i₀ j₀ s} := by
      ext ω
      simp only [ExitL, crossGap, mem_ofPred_eq, mem_union]
      constructor
      · rintro ⟨h, h' | h'⟩
        · exact Or.inl ⟨h, by linarith⟩
        · exact Or.inr ⟨h, h'⟩
      · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
        · exact ⟨h, Or.inl (by linarith)⟩
        · exact ⟨h, Or.inr h'⟩
    rw [e]
    refine MeasurableSet.union ?_ (measurableSet_lt_and_discClock hVL hVR s _)
    have hζs : MeasurableSet[𝓕 s] {ω | (s : ℝ≥0∞) < ζ ω} := by
      have := hW s univ MeasurableSet.univ
      simpa only [mem_univ, and_true] using this
    have hm : Measurable[𝓕 s] fun ω => 4 * (killedAt ζ W s ω - killedAt ζ (VL i₀) s ω) -
        (killedAt ζ (VR j₀) s ω - killedAt ζ (VL i₀) s ω) :=
      (((Band.measurable_killed_of_adaptedBefore hW s).sub
        (Band.measurable_killed_of_adaptedBefore (hVL i₀) s)).const_mul 4).sub
        ((Band.measurable_killed_of_adaptedBefore (hVR j₀) s).sub
          (Band.measurable_killed_of_adaptedBefore (hVL i₀) s))
    have e2 : {ω | (s : ℝ≥0∞) < ζ ω ∧ (4 * (W s ω - VL i₀ s ω) - (VR j₀ s ω - VL i₀ s ω) ≤ 0)} =
        {ω | (s : ℝ≥0∞) < ζ ω} ∩ {ω | 4 * (killedAt ζ W s ω - killedAt ζ (VL i₀) s ω) -
          (killedAt ζ (VR j₀) s ω - killedAt ζ (VL i₀) s ω) ≤ 0} := by
      ext ω
      simp only [mem_ofPred_eq, mem_inter_iff, and_congr_right_iff]
      intro h
      simp only [killedAt_of_lt h]
    rw [e2]
    exact hζs.inter (measurableSet_le hm measurable_const)
  exact h1.min (Ito.isStoppingTime_lifetime hW)

end Process

/-! ### The infinite-band traces of an evolution -/

section BandTrace

open Sec2 Sec2.Assembly Sec2.Restart RandRestart Girsanov

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {i₀ : Fin nL} {j₀ : Fin nR}

/-- **The trace through the infinite band deleting the right group** (Aux. lemma 106, the final band; Aux. lemma
113). For an evolution of a separated word, if Wiener-almost every path drives a solution of the word with all right
weights `0` with the full trace event, then almost surely the driver has the trace event up to the tail horizon of the
right band: a continuous trace, tending to infinity when the band never ends. -/
theorem ae_traceEvent_tailHorizonR [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hsep : ∀ i j, xL i < xR j)
    (hj₀ : ∀ j, j₀ ≤ j) (m : ℕ)
    (hfull : ∀ᵐ f ∂wienerPath,
      ((xL, xR), enc f) ∈ lawSetS κ ρL (0 : Fin nR → ℝ) (fullTraceSet (nL := nL) (nR := nR))) :
    ∀ᵐ ω ∂P, TraceEvent (fun t => W t ω)
      (tailHorizonR m (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) i₀ j₀ (ζ ω)) := by
  have hE𝓖 := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hT := isStoppingTime_tailHorizonR (i₀ := i₀) (j₀ := j₀) hE𝓖.2.1 hE𝓖.2.2.1 hE𝓖.2.2.2.1 m
  have hD0 : 0 < xR j₀ - xL i₀ := sub_pos.2 (hsep i₀ j₀)
  have hδ : 0 < (xR j₀ - xL i₀) / 4 := by linarith
  have hgap : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) <
      tailHorizonR m (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) i₀ j₀ (ζ ω) →
      (∀ i, ρL i ≠ ρL i → (xR j₀ - xL i₀) / 4 ≤ |W t ω - VL i t ω|) ∧
        ∀ j, (0 : Fin nR → ℝ) j ≠ ρR j → (xR j₀ - xL i₀) / 4 ≤ |W t ω - VR j t ω| := by
    filter_upwards [hE.2.2.2.2] with ω hp t ht
    have hF := hp.isForcePath
    refine ⟨fun i h => absurd rfl h, fun j _ => ?_⟩
    have htζ : (t : ℝ≥0∞) < ζ ω := ht.trans_le tailHorizonR_le_lifetime
    have h1 := crossGap_le_of_lt_tailHorizonR hF.continuousOn_w hF.continuousOn_vL hF.continuousOn_vR ht
    have h2 := hF.crossGap_le i₀ j₀ zero_le htζ
    have h3 := hF.monotone_vR htζ (hj₀ j)
    rw [hF.vL_zero, hF.vR_zero] at h2
    simp only [crossGap] at h1
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  have hK : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤
      tailHorizonR m (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) i₀ j₀ (ζ ω) →
      ∫ s in (0 : ℝ)..(t : ℝ), shiftIntegrand κ 1 ((xR j₀ - xL i₀) / 4) (weightDiff ρL ρL ρR 0)
        (W s.toNNReal ω) (fun k => allMarks VL VR k s.toNNReal ω) ^ 2 ≤ 16 * (∑ j, |ρR j|) ^ 2 / κ * m := by
    filter_upwards [hE.2.2.2.2] with ω hp t ht
    exact energy_delR_le hκ hp hj₀ hD0 (u := fun s k => allMarks VL VR k s.toNNReal ω)
      (fun s j => by simp [allMarks]) ht
  exact ae_traceEvent_of_changeWeights_tail hκ hE𝓖 hsep ρL 0 (fun s => hT s)
    (fun ω => tailHorizonR_le_lifetime) hδ hgap hK hfull

/-- **The trace through the infinite band deleting the left group.** -/
theorem ae_traceEvent_tailHorizonL [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hsep : ∀ i j, xL i < xR j)
    (hi₀ : ∀ i, i₀ ≤ i) (m : ℕ)
    (hfull : ∀ᵐ f ∂wienerPath,
      ((xL, xR), enc f) ∈ lawSetS κ (0 : Fin nL → ℝ) ρR (fullTraceSet (nL := nL) (nR := nR))) :
    ∀ᵐ ω ∂P, TraceEvent (fun t => W t ω)
      (tailHorizonL m (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) i₀ j₀ (ζ ω)) := by
  have hE𝓖 := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hT := isStoppingTime_tailHorizonL (i₀ := i₀) (j₀ := j₀) hE𝓖.2.1 hE𝓖.2.2.1 hE𝓖.2.2.2.1 m
  have hD0 : 0 < xR j₀ - xL i₀ := sub_pos.2 (hsep i₀ j₀)
  have hδ : 0 < (xR j₀ - xL i₀) / 4 := by linarith
  have hgap : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) <
      tailHorizonL m (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) i₀ j₀ (ζ ω) →
      (∀ i, (0 : Fin nL → ℝ) i ≠ ρL i → (xR j₀ - xL i₀) / 4 ≤ |W t ω - VL i t ω|) ∧
        ∀ j, ρR j ≠ ρR j → (xR j₀ - xL i₀) / 4 ≤ |W t ω - VR j t ω| := by
    filter_upwards [hE.2.2.2.2] with ω hp t ht
    have hF := hp.isForcePath
    refine ⟨fun i _ => ?_, fun j h => absurd rfl h⟩
    have htζ : (t : ℝ≥0∞) < ζ ω := ht.trans_le tailHorizonL_le_lifetime
    have h1 := crossGap_le_of_lt_tailHorizonL hF.continuousOn_w hF.continuousOn_vL hF.continuousOn_vR ht
    have h2 := hF.crossGap_le i₀ j₀ zero_le htζ
    have h3 := hF.antitone_vL htζ (hi₀ i)
    rw [hF.vL_zero, hF.vR_zero] at h2
    simp only [crossGap] at h1
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hK : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤
      tailHorizonL m (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) i₀ j₀ (ζ ω) →
      ∫ s in (0 : ℝ)..(t : ℝ), shiftIntegrand κ 1 ((xR j₀ - xL i₀) / 4) (weightDiff ρL 0 ρR ρR)
        (W s.toNNReal ω) (fun k => allMarks VL VR k s.toNNReal ω) ^ 2 ≤ 16 * (∑ i, |ρL i|) ^ 2 / κ * m := by
    filter_upwards [hE.2.2.2.2] with ω hp t ht
    exact energy_delL_le hκ hp hi₀ hD0 (u := fun s k => allMarks VL VR k s.toNNReal ω)
      (fun s i => by simp [allMarks]) ht
  exact ae_traceEvent_of_changeWeights_tail hκ hE𝓖 hsep 0 ρR (fun s => hT s)
    (fun ω => tailHorizonL_le_lifetime) hδ hgap hK hfull

end BandTrace

end Band

end Sec7

end InteractingSLE
