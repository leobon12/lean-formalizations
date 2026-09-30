import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.Order.LeftRightNhds

/-!
# THM11-AD3: left limits at swallowed points — the deterministic core

Sheffield, *Conformal weldings of random surfaces* (arXiv:1012.4797), Theorem 1.1 addendum
(§1, p. 12 of the paper): for `κ ∈ (4,8)`, a point `z` swallowed at time `τ(z)` receives the
value `𝔥_{τ(z)}(z) := lim_{s ↑ τ(z)} 𝔥_s(z)`. The paper states this limit as a definition and
gives no proof; the blueprint (`THM11_BLUEPRINT.md` §9 AD-3) asks for it a.s.

The probabilistic input (that `s ↦ 𝔥_s(a)` is an `L²`-bounded martingale up to the swallowing
time, i.e. that the accumulated quadratic variation `∫₀^{τ} 4 (Im f_s(a))²/|f_s(a)|⁴ ds` has
finite expectation, from FD-8 with `κ < 8`) is **not** proved here; see the report.

What is proved here is the analytic half, in the exact form in which the probabilistic half is
consumed: if the oscillation of the field on the successive "plates"
`[σ k, σ (k+1)]` is summable along a cofinal sequence `σ k ↑ τ`, then the left limit at `τ`
exists (`exists_tendsto_nhdsWithin_Iio_of_summable`). This is the "plus continuity of the path
to pass to the left limit" step of the route in `TASKS.md` R19: it converts a statement about a
countable family of stopping times (which is what martingale convergence theorems provide) into
the left limit as written in the target statement.

Own elementary proof (no source needed: the telescoping/Cauchy argument is standard).
-/

noncomputable section

open Filter Set
open scoped Topology

namespace QuantumZipper.Thm11Add

/-- **Covering by plates.** If `σ k ↑ τ` strictly from below, then every `s ∈ [σ K, τ)` lies in
the plate `[σ k, σ (k+1)]` for some `k ≥ K`. -/
theorem exists_le_sigma_lt_succ {σ : ℕ → ℝ} {τ : ℝ} (hmono : StrictMono σ)
    (htend : Tendsto σ atTop (𝓝[<] τ)) {K : ℕ} {s : ℝ} (hKs : σ K ≤ s)
    (hsτ : s < τ) : ∃ k ≥ K, σ k ≤ s ∧ s < σ (k + 1) := by
  have hex : ∃ k, s < σ (k + 1) := by
    have hmem : Ioi s ∈ 𝓝[<] τ :=
      mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hsτ)
    obtain ⟨k, hk⟩ := (htend.eventually hmem).exists
    exact ⟨k, lt_trans hk (hmono (Nat.lt_succ_self k))⟩
  have hkK : K ≤ Nat.find hex := by
    by_contra hcon
    have hk1 : Nat.find hex + 1 ≤ K := Nat.succ_le_of_lt (not_le.mp hcon)
    have : σ (Nat.find hex + 1) ≤ σ K := hmono.monotone hk1
    linarith [Nat.find_spec hex]
  refine ⟨Nat.find hex, hkK, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · obtain rfl : K = 0 := Nat.eq_zero_of_le_zero (h0 ▸ hkK)
    rw [h0]; exact hKs
  · have hmin : ¬ (s < σ (Nat.find hex)) := by
      intro hlt'
      have hstep : Nat.find hex - 1 + 1 = Nat.find hex := Nat.sub_add_cancel hpos
      have := Nat.find_min' hex (m := Nat.find hex - 1) (by rw [hstep]; exact hlt')
      omega
    exact not_lt.mp hmin

/-- **Telescoping bound.** If the oscillation of `f` on each plate `[σ k, σ (k+1)]` is at most
`b k`, the oscillation over `[σ k, σ j]` is at most the sum of `b` over `[k, j)`. -/
theorem abs_sub_le_sum_Ico {f : ℝ → ℝ} {σ : ℕ → ℝ} {b : ℕ → ℝ} (hmono : StrictMono σ)
    (hbound : ∀ k, ∀ s ∈ Icc (σ k) (σ (k + 1)), |f s - f (σ k)| ≤ b k) {k j : ℕ} (hkj : k ≤ j) :
    |f (σ j) - f (σ k)| ≤ ∑ i ∈ Finset.Ico k j, b i := by
  have hten : (∑ i ∈ Finset.Ico k j, (f (σ (i + 1)) - f (σ i))) = f (σ j) - f (σ k) := by
    induction j, hkj using Nat.le_induction with
    | base => simp
    | succ j hkj ih =>
        rw [Finset.sum_Ico_succ_top hkj, ih]; ring

  rw [← hten]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact hbound i (σ (i + 1)) ⟨hmono.monotone (Nat.le_succ i), le_rfl⟩

/-- **AD-3, deterministic core.** If `σ k ↑ τ` strictly from below and the oscillations of `f` on
the plates `[σ k, σ (k+1)]` are bounded by a summable `b`, then `f` has a left limit at `τ`.

This is the form in which martingale convergence is consumed: a countable family of stopping
times `σ k ↑ τ` with pathwise summable increments gives `lim_{s ↑ τ} f s`. -/
theorem exists_tendsto_nhdsWithin_Iio_of_summable {f : ℝ → ℝ} {τ : ℝ} {σ : ℕ → ℝ} {b : ℕ → ℝ}
    (hmono : StrictMono σ) (hlt : ∀ k, σ k < τ) (htend : Tendsto σ atTop (𝓝[<] τ))
    (hb0 : ∀ k, 0 ≤ b k) (hb : Summable b)
    (hbound : ∀ k, ∀ s ∈ Icc (σ k) (σ (k + 1)), |f s - f (σ k)| ≤ b k) :
    ∃ ℓ, Tendsto f (𝓝[<] τ) (𝓝 ℓ) := by
  set T : ℝ := ∑' i, b i with hT
  have hle : ∀ n, (∑ i ∈ Finset.range n, b i) ≤ T := by
    intro n
    rw [hT]
    exact Summable.sum_le_tsum (Finset.range n) (fun i _ => hb0 i) hb
  have htail : Tendsto (fun k => T - ∑ i ∈ Finset.range k, b i) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => T) atTop (𝓝 T) := tendsto_const_nhds
    have h := hc.sub hb.hasSum.tendsto_sum_nat
    have h0 : T - ∑' i, b i = 0 := by rw [← hT, sub_self]
    rw [h0] at h
    exact h
  have htail_anti : Antitone fun k => T - ∑ i ∈ Finset.range k, b i := by
    intro m n hmn
    have hle' : (∑ i ∈ Finset.range m, b i) ≤ ∑ i ∈ Finset.range n, b i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hmn)
        (fun i _ _ => hb0 i)
    linarith
  -- oscillation over a plate is bounded by the tail at the left endpoint
  have hplate : ∀ k j, k ≤ j →
      |f (σ j) - f (σ k)| ≤ T - ∑ i ∈ Finset.range k, b i := by
    intro k j hkj
    refine (abs_sub_le_sum_Ico hmono hbound hkj).trans ?_
    rw [Finset.sum_Ico_eq_sub _ hkj]
    linarith [hle j]
  -- the grid sequence is Cauchy
  have hcau : CauchySeq fun k => f (σ k) := by
    refine cauchySeq_iff_le_tendsto_0.2 ⟨fun N => T - ∑ i ∈ Finset.range N, b i,
      fun N => sub_nonneg.mpr (hle N), ?_, htail⟩
    intro n m N hn hm
    rw [Real.dist_eq]
    have hmain : ∀ k j, N ≤ k → N ≤ j →
        |f (σ k) - f (σ j)| ≤ T - ∑ i ∈ Finset.range N, b i := by
      intro k j hk hj
      rcases le_total k j with hkj | hjk
      · rw [abs_sub_comm]
        exact (hplate k j hkj).trans (by linarith [hle N, hle k, htail_anti hk])
      · exact (hplate j k hjk).trans (by linarith [hle N, hle j, htail_anti hj])
    exact hmain n m hn hm
  obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨ℓ, Metric.tendsto_nhdsWithin_nhds.mpr fun ε hε => ?_⟩
  have h1 : ∀ᶠ k in atTop, T - ∑ i ∈ Finset.range k, b i < ε / 2 :=
    htail.eventually (eventually_lt_nhds (by linarith))
  rw [eventually_atTop] at h1
  obtain ⟨K₁, hK1⟩ := h1
  have h2 : ∀ᶠ k in atTop, |f (σ k) - ℓ| < ε / 2 := by
    have hd : ∀ᶠ k in atTop, dist (f (σ k)) ℓ < ε / 2 :=
      hℓ.eventually (Metric.ball_mem_nhds ℓ (by linarith))
    filter_upwards [hd] with k hk
    rwa [Real.dist_eq] at hk
  rw [eventually_atTop] at h2
  obtain ⟨K₂, hK2⟩ := h2
  refine ⟨τ - σ (max K₁ K₂), by linarith [hlt (max K₁ K₂)], fun s hs hdist => ?_⟩
  have hσK : σ (max K₁ K₂) < s := by
    rw [Real.dist_eq] at hdist
    have := abs_lt.mp hdist
    linarith [this.1, this.2, hs]
  obtain ⟨k, hkK, hk1, hk2⟩ :=
    exists_le_sigma_lt_succ hmono htend hσK.le hs
  have hbk : |f s - f (σ k)| ≤ b k := hbound k s ⟨hk1, hk2.le⟩
  have htailk : b k ≤ T - ∑ i ∈ Finset.range k, b i := by
    have hsub : (∑ i ∈ Finset.Ico k (k + 1), b i) =
        (∑ i ∈ Finset.range (k + 1), b i) - ∑ i ∈ Finset.range k, b i :=
      Finset.sum_Ico_eq_sub _ (Nat.le_succ k)
    have hbk : (∑ i ∈ Finset.Ico k (k + 1), b i) = b k := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp
    rw [hbk] at hsub
    linarith [hle (k + 1), hsub]
  rw [Real.dist_eq]
  calc |f s - ℓ| ≤ |f s - f (σ k)| + |f (σ k) - ℓ| := abs_sub_le _ _ _
    _ ≤ b k + ε / 2 := add_le_add hbk (hK2 k (le_trans (le_max_right _ _) hkK)).le
    _ ≤ (T - ∑ i ∈ Finset.range k, b i) + ε / 2 := by linarith
    _ < ε := by
        have := hK1 k (le_trans (le_max_left _ _) hkK)
        linarith

end QuantumZipper.Thm11Add
