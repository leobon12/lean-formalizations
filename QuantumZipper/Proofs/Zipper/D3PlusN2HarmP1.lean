import QuantumZipper.Proofs.Zipper.D3PlusN2Harm
import QuantumZipper.Proofs.Zipper.D3PlusN1Model
import QuantumZipper.Proofs.GFF.K3.HarmonicPart

/-!
# D3⁺(i), node N2: the continuous harmonic part on the whole half-disc

Task N2-HARMPART. Proves `D3Plus.D3PlusN2HarmPartStmt` (`Proofs/Zipper/D3PlusN2Harm.lean`): almost
surely there is `H_ω`, continuous on `ball 0 r ∩ Hbar`, with `H_ω ∘ foldH` harmonic near `0` and
`X ω (bal 0 r μ) = ∫ H_ω dμ` for every dyadic folded circle `μ ∈ circSet r`.

Route (own elementary argument, assembling `K3.markov_decomposition`):
with the radii `rSeq r n = r (1 − 1/(n+2)) ↑ r`,

* **Consistency** (`ae_harmH_rSeq_consistent`): a.s. the continuous versions
  `harmH X 0 r (rSeq r n)` and `harmH X 0 r (rSeq r m)` (`n ≤ m`) agree on `closedBall 0 (rSeq r n)`.
  Proof: both are a.s. equal to `X (halfDiscPoisson 0 r (retr 0 _ w)) − X (P_0)` at every point `w`
  of the countable dense set `ℚ + iℚ ∩ ball`, where the retraction is the identity (Sheffield,
  *Gaussian free fields for mathematicians*, PTRF 139 (2007), §2.4; `K3.kolY_harmIncr_spec`); two
  continuous functions agreeing on a dense set agree on its closure
  (`Set.EqOn.of_subset_closure`).
* **Decomposition** (`ae_n2_decomp_rSeq`): a.s., for every dyadic folded circle carried by
  `closedBall 0 (rSeq r N)`, `X ω (bal 0 r μ) = ∫ harmH X 0 r (rSeq r N) dμ + X ω (P_0)`
  (`K3.markov_decomposition` with `markovZ X 0 r ω μ = X ω μ − X ω (bal μ)`).
* **Gluing** (`d3PlusN2HarmPart_holds`): on the a.s. event,
  `H_ω z = lim_n harmH X 0 r (rSeq r n) ω z + X ω (P_0)` is locally (on `‖z‖ < rSeq r N`) the
  continuous function `harmH X 0 r (rSeq r N) + X ω (P_0)`, hence continuous on `ball 0 r`;
  `H_ω ∘ foldH = H_ω`, so `K3.ae_harmonicOnNhd_harmH` applied to `rSeq r 0` gives harmonicity near
  `0`. The circle identity then follows from the decomposition at the first `N` with
  `‖d‖ + ρ ≤ rSeq r N`, the eventual constancy of the limit outside the support of the circle and
  `D3Plus.integrable_circ`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-! ## The radius sequence `r (1 − 1/(n+2)) ↑ r` -/

/-- Radii increasing to `r`: `rSeq r n = r * (1 - 1/(n+2))`. -/
def rSeq (r : ℝ) (n : ℕ) : ℝ := r * (1 - 1 / ((n : ℝ) + 2))

theorem rSeq_pos {r : ℝ} (hr : 0 < r) (n : ℕ) : 0 < rSeq r n := by
  have h1 : 1 / ((n : ℝ) + 2) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have h3 : 0 < 1 - 1 / ((n : ℝ) + 2) := by linarith
  exact mul_pos hr h3

theorem rSeq_lt {r : ℝ} (hr : 0 < r) (n : ℕ) : rSeq r n < r := by
  have h1 : 0 < 1 / ((n : ℝ) + 2) := by positivity
  have h2 : (1 : ℝ) - 1 / ((n : ℝ) + 2) < 1 := by linarith
  calc rSeq r n = r * (1 - 1 / ((n : ℝ) + 2)) := rfl
    _ < r * 1 := mul_lt_mul_of_pos_left h2 hr
    _ = r := mul_one r

theorem rSeq_mono {r : ℝ} (hr : 0 ≤ r) : Monotone (rSeq r) := by
  intro n m hnm
  have hnm' : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.2 hnm
  have h1 : 1 / ((m : ℝ) + 2) ≤ 1 / ((n : ℝ) + 2) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have h2 : 1 - 1 / ((n : ℝ) + 2) ≤ 1 - 1 / ((m : ℝ) + 2) := by linarith
  exact mul_le_mul_of_nonneg_left h2 hr

theorem tendsto_rSeq (r : ℝ) : Tendsto (rSeq r) atTop (𝓝 r) := by
  have h : Tendsto (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  have h1 : (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) + 1)) =
      fun n : ℕ => 1 / ((n : ℝ) + 2) := by
    funext n; push_cast; ring
  rw [h1] at h
  rw [show rSeq r = fun n : ℕ => r * (1 - 1 / ((n : ℝ) + 2)) from rfl]
  simpa using (tendsto_const_nhds.mul (tendsto_const_nhds.sub h) :
    Tendsto (fun n : ℕ => r * (1 - 1 / ((n : ℝ) + 2))) atTop (𝓝 (r * (1 - 0))))

theorem exists_rSeq_gt {r : ℝ} (_hr : 0 < r) {x : ℝ} (hx : x < r) : ∃ N, x < rSeq r N :=
  ((tendsto_rSeq r).eventually (isOpen_Ioi.mem_nhds hx)).exists

/-- The dyadic rounding takes countably many values. -/
theorem countable_range_dyadicRoundC (n : ℕ) : (Set.range (dyadicRoundC n)).Countable := by
  have hsub : Set.range (dyadicRoundC n) ⊆
      Set.range (fun p : ℤ × ℤ =>
        (⟨(p.1 : ℝ) / (2 : ℝ) ^ n, (p.2 : ℝ) / (2 : ℝ) ^ n⟩ : ℂ)) := by
    rintro _ ⟨z, rfl⟩
    exact ⟨(⌊(2 : ℝ) ^ n * z.re⌋, ⌊(2 : ℝ) ^ n * z.im⌋), rfl⟩
  exact (Set.countable_range _).mono hsub

/-! ## Two elementary facts about `foldH` and `harmH` -/

theorem foldH_norm_eq (z : ℂ) : ‖foldH z‖ = ‖z‖ := by
  unfold foldH
  split_ifs <;> simp

/-- `harmH` is `foldH`-invariant: it is the Kolmogorov modification of `w ↦ harmIncr (foldH w)`. -/
theorem harmH_foldH (X : Ω → FieldSample) (t r r' : ℝ) (ω : Ω) (z : ℂ) :
    K3.harmH X t r r' ω (foldH z) = K3.harmH X t r r' ω z := by
  simp only [K3.harmH, CircleFubini.foldH_of_mem' (CircleFubini.foldH_mem_Hbar' z)]

/-! ## Consistency of `harmH` at the radii `rSeq r n` -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- Almost surely, the continuous versions `harmH X 0 r (rSeq r n)` and `harmH X 0 r (rSeq r m)`
(`n ≤ m`) agree on `closedBall 0 (rSeq r n)`: at every point of a countable dense set both are
`X (halfDiscPoisson 0 r ·) − X (P_0)`, because the half-disc retraction is the identity there. -/
theorem ae_harmH_rSeq_consistent [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {r : ℝ} (hr : 0 < r) {n m : ℕ} (hnm : n ≤ m) :
    ∀ᵐ ω ∂P, Set.EqOn (K3.harmH X 0 r (rSeq r n) ω) (K3.harmH X 0 r (rSeq r m) ω)
      (Metric.closedBall (0 : ℂ) (rSeq r n)) := by
  have hn_pos : 0 < rSeq r n := rSeq_pos hr n
  have hm_pos : 0 < rSeq r m := rSeq_pos hr m
  have hn_lt : rSeq r n < r := rSeq_lt hr n
  have hm_lt : rSeq r m < r := rSeq_lt hr m
  have hle : rSeq r n ≤ rSeq r m := rSeq_mono hr.le hnm
  set QQ : ℚ × ℚ → ℂ :=
    Complex.equivRealProdCLM.symm ∘ Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ) with hQQ
  have hdense : DenseRange QQ :=
    (Complex.equivRealProdCLM.symm.surjective.denseRange).comp
      (Rat.denseRange_cast.prodMap Rat.denseRange_cast) Complex.equivRealProdCLM.symm.continuous
  have hall : ∀ᵐ ω ∂P, ∀ q : ℚ × ℚ, QQ q ∈ Metric.ball (0 : ℂ) (rSeq r n) →
      K3.harmH X 0 r (rSeq r n) ω (QQ q) = K3.harmH X 0 r (rSeq r m) ω (QQ q) := by
    rw [ae_all_iff]
    rintro q
    by_cases hq : QQ q ∈ Metric.ball (0 : ℂ) (rSeq r n)
    · have hq' : ‖QQ q‖ < rSeq r n := by
        simpa [Metric.mem_ball, dist_eq_norm] using hq
      filter_upwards [(K3.kolY_harmIncr_spec (P := P) hX hr hn_pos hn_lt).2
          (foldH (QQ q)) (CircleFubini.foldH_mem_Hbar' _),
        (K3.kolY_harmIncr_spec (P := P) hX hr hm_pos hm_lt).2
          (foldH (QQ q)) (CircleFubini.foldH_mem_Hbar' _)] with ω h1 h2
      intro _
      simp only [K3.harmH] at h1 h2 ⊢
      rw [h1, h2]
      have hretr : ∀ j : ℕ, ‖QQ q‖ ≤ rSeq r j →
          K3.retr 0 (rSeq r j) (foldH (QQ q)) = foldH (QQ q) := fun j hj =>
        K3.retr_eq_self (CircleFubini.foldH_mem_Hbar' _)
          (by simpa [Complex.ofReal_zero, foldH_norm_eq] using hj)
      simp only [K3.harmIncr]
      rw [hretr n hq'.le, hretr m (hq'.le.trans hle)]
    · filter_upwards with ω h
      exact absurd h hq
  filter_upwards [hall] with ω hω
  have hu := K3.continuous_harmH (P := P) (t := 0) hX hr hn_pos hn_lt ω
  have hv := K3.continuous_harmH (P := P) (t := 0) hX hr hm_pos hm_lt ω
  refine Set.EqOn.of_subset_closure
    (s := Metric.ball (0 : ℂ) (rSeq r n) ∩ Set.range QQ)
    (t := Metric.closedBall (0 : ℂ) (rSeq r n))
    (by rintro z ⟨hzE, q, rfl⟩; exact hω q hzE) hu.continuousOn hv.continuousOn
    (Set.inter_subset_left.trans Metric.ball_subset_closedBall) ?_
  rw [show Metric.closedBall (0 : ℂ) (rSeq r n) =
      closure (Metric.ball (0 : ℂ) (rSeq r n)) from
    (closure_ball (0 : ℂ) (ne_of_gt hn_pos)).symm]
  exact (closure_mono (hdense.open_subset_closure_inter Metric.isOpen_ball)).trans
    (le_of_eq closure_closure)

/-! ## The Markov decomposition at the radii `rSeq r n` -/

/-- Almost surely, for every dyadic folded circle `foldedCircle d (radius k)` carried by
`closedBall 0 (rSeq r N)`: `X ω (bal 0 r μ) = ∫ harmH X 0 r (rSeq r N) dμ + X ω (P_0)`. -/
theorem ae_n2_decomp_rSeq [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ (n k N : ℕ) (d : Set.range (dyadicRoundC n)),
      ‖(d : ℂ)‖ + radius k ≤ rSeq r N →
      X ω (K3.bal 0 r (foldedCircle (d : ℂ) (radius k))) =
        (∫ z, K3.harmH X 0 r (rSeq r N) ω z ∂foldedCircle (d : ℂ) (radius k)) +
          X ω (K3.halfDiscPoisson 0 r ((0 : ℝ) : ℂ)) := by
  rw [ae_all_iff]
  intro n
  rw [ae_all_iff]
  intro k
  rw [ae_all_iff]
  intro N
  have hcount : Countable (Set.range (dyadicRoundC n)) := countable_range_dyadicRoundC n
  rw [ae_all_iff]
  intro d
  by_cases hd : ‖(d : ℂ)‖ + radius k ≤ rSeq r N
  · have hμadm : IsAdmissibleH (foldedCircle (d : ℂ) (radius k)) :=
      isAdmissibleH_foldedCircle' _ (radius_pos k)
    have hsupp : foldedCircle (d : ℂ) (radius k)
        (Metric.closedBall ((0 : ℝ) : ℂ) (rSeq r N))ᶜ = 0 :=
      measure_mono_null (Set.compl_subset_compl.2 (Metric.closedBall_subset_closedBall hd))
        (foldedCircle_compl_closedBall (d := (d : ℂ)) (radius_pos k))
    filter_upwards [K3.markov_decomposition (P := P) hX hr (rSeq_pos hr N) (rSeq_lt hr N)
      hμadm hsupp] with ω hω
    intro _
    have hzu : K3.markovZ X 0 r ω (foldedCircle (d : ℂ) (radius k)) =
        X ω (foldedCircle (d : ℂ) (radius k)) -
          X ω (K3.bal 0 r (foldedCircle (d : ℂ) (radius k))) := rfl
    rw [hzu, measure_univ, ENNReal.toReal_one, one_mul] at hω
    linarith only [hω]
  · filter_upwards with ω h
    exact absurd h hd

/-! ## The harmonic part on the whole half-disc -/

/-- **Node N2, harmonic part**: almost surely there is `H_ω : ℂ → ℝ`, continuous on
`ball 0 r ∩ Hbar`, with `H_ω ∘ foldH` harmonic on a neighbourhood of `0`, and
`X ω (bal 0 r μ) = ∫ H_ω dμ` for every dyadic folded circle `μ ∈ circSet r`. -/
theorem d3PlusN2HarmPart_holds : D3PlusN2HarmPartStmt := by
  intro r Ω _ P _ X hr hX
  have hcons : ∀ᵐ ω ∂P, ∀ n m : ℕ, n ≤ m → ∀ z ∈ Metric.closedBall (0 : ℂ) (rSeq r n),
      K3.harmH X 0 r (rSeq r n) ω z = K3.harmH X 0 r (rSeq r m) ω z := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro m
    by_cases hnm : n ≤ m
    · filter_upwards [ae_harmH_rSeq_consistent (P := P) hX hr hnm] with ω h
      exact fun _ z hz => h (x := z) hz
    · filter_upwards with ω h
      exact absurd h hnm
  filter_upwards [hcons, ae_n2_decomp_rSeq (P := P) hX hr,
    K3.ae_harmonicOnNhd_harmH (P := P) (t := 0) hX hr (rSeq_pos hr 0) (rSeq_lt hr 0)]
    with ω hconsω hdecω hharmω
  set cω : ℝ := X ω (K3.halfDiscPoisson 0 r ((0 : ℝ) : ℂ)) with hcω
  -- eventual constancy of the limit at every point of a `closedBall 0 (rSeq r N)`
  have hlim : ∀ (N : ℕ) (z : ℂ), ‖z‖ ≤ rSeq r N →
      limUnder atTop (fun m => K3.harmH X 0 r (rSeq r m) ω z) =
        K3.harmH X 0 r (rSeq r N) ω z := by
    intro N z hz
    have hev : (fun _ : ℕ => K3.harmH X 0 r (rSeq r N) ω z) =ᶠ[atTop]
        (fun m => K3.harmH X 0 r (rSeq r m) ω z) := by
      filter_upwards [eventually_ge_atTop N] with m hm
      exact hconsω N m hm z (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)
    exact (tendsto_const_nhds.congr' hev).limUnder_eq
  refine ⟨fun z => limUnder atTop (fun m => K3.harmH X 0 r (rSeq r m) ω z) + cω, ?_, ?_, ?_⟩
  · -- continuity on `ball 0 r ∩ Hbar`
    intro z₀ hz₀
    have hz₀' : ‖z₀‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hz₀.1
    obtain ⟨N, hN⟩ := exists_rSeq_gt hr hz₀'
    have hball : z₀ ∈ Metric.ball (0 : ℂ) (rSeq r N) := by
      simpa [Metric.mem_ball, dist_eq_norm] using hN
    have hev : (fun z => limUnder atTop (fun m => K3.harmH X 0 r (rSeq r m) ω z) + cω)
        =ᶠ[𝓝 z₀] (fun z => K3.harmH X 0 r (rSeq r N) ω z + cω) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hball] with z hz
      rw [hlim N z (le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hz))]
    exact ((K3.continuous_harmH (P := P) (t := 0) hX hr (rSeq_pos hr N) (rSeq_lt hr N)
      ω).add continuous_const).continuousAt.congr_of_eventuallyEq hev |>.continuousWithinAt
  · -- `H_ω ∘ foldH` is harmonic near `0`
    refine ⟨rSeq r 0, rSeq_pos hr 0, ?_⟩
    intro x hx
    have hev : (fun z => limUnder atTop (fun m => K3.harmH X 0 r (rSeq r m) ω (foldH z)) + cω)
        =ᶠ[𝓝 x] (fun z => K3.harmH X 0 r (rSeq r 0) ω z + cω) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
      have hz' : ‖z‖ ≤ rSeq r 0 :=
        le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
      rw [congrArg (limUnder atTop) (funext fun m => harmH_foldH X 0 r (rSeq r m) ω z), hlim 0 z hz']
    rw [InnerProductSpace.harmonicAt_congr_nhds hev]
    exact (hharmω x hx).add (InnerProductSpace.harmonicAt_const cω)
  · -- the circle identity
    intro μ hμ
    obtain ⟨n, k, z, hz, rfl⟩ := hμ
    obtain ⟨N, hN⟩ := exists_rSeq_gt hr hz
    have hkey := hdecω n k N ⟨dyadicRoundC n z, z, rfl⟩ hN.le
    have hsupp : foldedCircle (dyadicRoundC n z) (radius k)
        (Metric.closedBall (0 : ℂ) (‖dyadicRoundC n z‖ + radius k))ᶜ = 0 := by
      simpa using foldedCircle_compl_closedBall (d := dyadicRoundC n z) (radius_pos k)
    have hae : (fun z' => limUnder atTop (fun m => K3.harmH X 0 r (rSeq r m) ω z') + cω)
        =ᵐ[foldedCircle (dyadicRoundC n z) (radius k)]
        fun z' => K3.harmH X 0 r (rSeq r N) ω z' + cω := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hsupp] with z' hz'
      have hz'' : ‖z'‖ ≤ rSeq r N :=
        le_trans (by simpa [Metric.mem_closedBall, dist_eq_norm] using (not_not.1 hz')) hN.le
      rw [hlim N z' hz'']
    have hint : Integrable (fun z' => K3.harmH X 0 r (rSeq r N) ω z')
        (foldedCircle (dyadicRoundC n z) (radius k)) := by
      have h := integrable_circ (α := 0) (ψ := K3.harmH X 0 r (rSeq r N) ω)
        (((K3.continuous_harmH (P := P) (t := 0) hX hr (rSeq_pos hr N) (rSeq_lt hr N)
          ω).continuousOn).mono (Set.subset_univ _))
        (μ := foldedCircle (dyadicRoundC n z) (radius k)) ⟨n, k, z, hz, rfl⟩
      simpa using h
    have hmain : ∫ z', (limUnder atTop (fun m => K3.harmH X 0 r (rSeq r m) ω z') + cω)
        ∂foldedCircle (dyadicRoundC n z) (radius k)
        = X ω (K3.bal 0 r (foldedCircle (dyadicRoundC n z) (radius k))) := by
      rw [integral_congr_ae hae, integral_add hint (integrable_const cω), integral_const,
        Measure.real, measure_univ, ENNReal.toReal_one, one_smul, ← hkey]
    exact hmain.symm

end D3Plus
end QuantumZipper
