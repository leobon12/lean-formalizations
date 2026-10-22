import HigherDimLQGMetric.DGZ.AcrossLower
import HigherDimLQGMetric.DGZ.Discretize

/-!
# DGZ Lemma 4.10, across half (packet L3c3; MA7 D-4.10)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), Lemma 4.10 (TeX l. 1910–1976, pp. 37–38);
planning audit `planning/audits/MA7-ref2-sections-4-6.md`, §5 row L3c3, gap G5 and Details (a)
D-4.10; the target shape `SuperExpAcrossShape` is copied **verbatim** from MA7 Details (c) §E
(durable copy `planning/audits/statements/MA7Statements.lean.txt`).

Main results:
* `SuperExpAcrossShape` (definition, verbatim) and
  `superExpAcrossShape : SuperExpAcrossShape d κ ξ Q` (for all `d, κ, ξ, Q`): under
  `DGZHyp d κ ξ Q`, for `δ > 0` and `0 < r₂ < r₁` there is `C` with
  `P*[D_n(across B_{r₁}(0) \ B_{r₂}(0)) ≤ 2^{-(1-ξQ+δ)n}] ≤ C e^{-n log n}`;
* the deterministic crossing lemma `le_acrossDist_of_smallDiam` (no duality, G5): if the closed
  sites of a site configuration on `s ℤ^d` form clusters of diameter `≤ D` with
  `D s + 8 s ≤ r₁ - r₂`, and every open site `x` with `|s x|_∞ ≤ r₁` has
  `D(across B_{2s}(s x) \ B_s(s x)) ≥ t`, then `D(across B_{r₁}(0) \ B_{r₂}(0)) ≥ t`.

Proof (MA7 D-4.10). Scale `m = m(n) = 2 ⌊log₂ n⌋ + 2` (`AcrossAroundTools.superScale`),
`s = 2^{-m}`, `T' = 2^{-(1-ξQ)n - δn/3}`. A site `x` with `|s x|_∞ ≤ r₁` is closed iff
`D[h_n - h_m](across B_{2s}(s x) \ B_s(s x)) < T'`; all other sites are open. `h_n - h_m` is a
version of `h_{m,n}` (`isBandVersion_sub_of_realization`); by scaling and D-4.8 (with `δ/4`),
`P[x closed] ≤ C e^{-(n-m)/C}`; closedness is local (the field on `B̄_{2s}(s x)`), so the product
bound and `Perc.diameterBound` give
`P[some closed cluster has diameter > ⌊(r₁-r₂)/(4s)⌋] ≤ e^{-n log n}` for large `n`. On
`{sup_{B̄_{r₁+1}(0)} |h_m| ≤ δ n log 2/(3ξ)}` (probability `≥ 1 - e^{-n log n}`,
`exists_field_superExp`), every open site has `D_n(across) ≥ 2^{-δn/3} T'`, and the crossing lemma
gives `D_n(across B_{r₁} \ B_{r₂}) ≥ 2^{-(1-ξQ)n - 2δn/3} > 2^{-(1-ξQ+δ)n}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox obox_subset_cbox)

variable {d : ℕ}

/-! ### The target shape (MA7 Details (c) §E, verbatim) -/

/-- **DGZ Lemma 4.10, across half** (MA7 D-4.10): super-exponential lower tail for every shell -/
def SuperExpAcrossShape (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ) : Prop :=
  DGZHyp d κ ξ Q → ∀ δ > 0, ∀ r₁ r₂ : ℝ, 0 < r₂ → r₂ < r₁ → ∃ C > 0,
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
      IsDyadicRealization κ P W H → ∀ n : ℕ,
        P {ω | acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ ≤ (2 : ℝ) ^ (-(1 - ξ * Q + δ) * n)} ≤
          ENNReal.ofReal (C * Real.exp (-(n : ℝ) * Real.log n))

/-! ### The deterministic crossing lemma -/

/-- **The crossing lemma** (MA7 D-4.10, deterministic part; no duality, G5): let `O` be a site
configuration on `s ℤ^d` whose closed clusters have `ℓ^∞`-diameter `≤ D`, with
`D s + 8 s ≤ r₁ - r₂`, and suppose every open site `x` with `|s x|_∞ ≤ r₁` satisfies
`t ≤ D(across B_{2s}(s x) \ B_s(s x))`. Then `t ≤ D(across B_{r₁}(0) \ B_{r₂}(0))`.

Proof: a path crossing the shell contains a sub-crossing of `B̄_{r₁-3s} \ B_{r₂+3s}`; its
discretization (D-DISC) is an L-path of sites of `ℓ^∞`-diameter `> D`, so one of its sites `x` is
open (otherwise the path would lie in one closed cluster). The path meets `B̄_s(s x)` and starts
outside `B_{2s}(s x)`, so it crosses `B̄_{2s}(s x) \ B_s(s x)`. -/
theorem le_acrossDist_of_smallDiam (hd : 1 ≤ d) {ξ : ℝ} {φ : Rd d → ℝ} (hφ : Continuous φ)
    {r₁ r₂ s : ℝ} (hs : 0 < s) (hr₂ : 0 ≤ r₂) {O : Set (Zd d)} {D : ℕ}
    (hdiam : ∀ C, IsClosedCluster O C → ∀ y ∈ C, ∀ y' ∈ C, WithinInf (D : ℤ) y y')
    (hD : (D : ℝ) * s + 8 * s ≤ r₁ - r₂) {t : ℝ}
    (hopen : ∀ x ∈ O, (∀ i, s * |(x i : ℝ)| ≤ r₁) → t ≤ acrossDist ξ φ (latPt s x) (2 * s) s) :
    t ≤ acrossDist ξ φ 0 r₁ r₂ := by
  have hD0 : (0 : ℝ) ≤ D * s := by positivity
  have hr₁ : 0 ≤ r₁ := by linarith
  have hshell : r₂ + 3 * s < r₁ - 3 * s := by linarith
  unfold acrossDist
  refine le_lfppSetDist (lsph_nonempty hd 0 hr₂) (lsph_nonempty hd 0 hr₁) fun x hx y hy =>
    le_lfppDistOn (pcwJoined_univ x y) fun γ hγ _ => ?_
  -- the middle sub-crossing of `B̄_{r₁-3s} \ B_{r₂+3s}`
  have hx0 : γ 0 ∈ cbox (0 : Rd d) (r₂ + 3 * s) := by
    rw [hγ.source]
    exact cbox_mono (by linarith) (mem_lsph.1 hx).1
  have hy1 : γ 1 ∉ obox (0 : Rd d) (r₁ - 3 * s) := by
    rw [hγ.target]
    exact fun h => (mem_lsph.1 hy).2 (obox_mono (by linarith) h)
  obtain ⟨t₀, t₁, h0, h01, h1, ht₀, ht₁, hin, -⟩ :=
    (isShellPair_box (0 : Rd d) hshell).exists_crossing_of_le zero_le_one hγ.continuousOn hx0 hy1
  -- the discretization of the sub-crossing
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, ⌈r₁ / s⌉₊ + 1 = N := ⟨_, rfl⟩
  have hN1 : 1 ≤ N := by omega
  have hsN : r₁ < s * N := by
    have h1 : r₁ / s ≤ ⌈r₁ / s⌉₊ := Nat.le_ceil _
    have h2 : (N : ℝ) = ⌈r₁ / s⌉₊ + 1 := by rw [← hNdef]; push_cast; ring
    rw [div_le_iff₀ hs] at h1
    rw [h2]
    nlinarith
  have hmaps : MapsTo γ (Icc t₀ t₁) (obox (latPt s (0 : Zd d)) (s * N)) := by
    intro τ hτ i
    have h1 := ((hin τ hτ).1 i)
    rw [HigherDimLFPP.DGZ.latPt_zero]
    simp only [PiLp.zero_apply, sub_zero] at h1 ⊢
    linarith
  obtain ⟨l, x₀, x₁, -, hl, hhead, hlast, hx₀, hx₁, hsites⟩ :=
    exists_discretization hs 0 hN1 h01.le
      (hγ.continuousOn.mono (Icc_subset_Icc h0 h1)) hmaps
  -- the discretized path is long
  have hfar : ¬ WithinInf (D : ℤ) x₀ x₁ := by
    obtain ⟨j, hj⟩ : ∃ j, r₁ - 3 * s ≤ |γ t₁ j| := by
      have h := ht₁.2
      rw [mem_obox] at h
      push Not at h
      obtain ⟨j, hj⟩ := h
      exact ⟨j, by simpa using hj⟩
    have h0j : |γ t₀ j| ≤ r₂ + 3 * s := by
      have := ht₀.1 j
      simpa using this
    have hx₀j : |γ t₀ j - s * (x₀ j : ℝ)| < s := hx₀ j
    have hx₁j : |γ t₁ j - s * (x₁ j : ℝ)| < s := hx₁ j
    intro hW
    have hWj : |((x₁ j : ℤ) : ℝ) - (x₀ j : ℝ)| ≤ D := by
      have := hW j
      rw [abs_sub_comm] at this
      exact_mod_cast this
    have h3 : s * |((x₁ j : ℤ) : ℝ) - (x₀ j : ℝ)| ≤ s * D := mul_le_mul_of_nonneg_left hWj hs.le
    have h4 : |s * (x₁ j : ℝ) - s * (x₀ j : ℝ)| = s * |((x₁ j : ℤ) : ℝ) - (x₀ j : ℝ)| := by
      rw [← mul_sub, abs_mul, abs_of_pos hs]
    have h5 := abs_sub_abs_le_abs_sub (γ t₁ j) (γ t₀ j)
    have key : |γ t₁ j - γ t₀ j| ≤ |γ t₁ j - s * (x₁ j : ℝ)| +
        |s * (x₁ j : ℝ) - s * (x₀ j : ℝ)| + |γ t₀ j - s * (x₀ j : ℝ)| := by
      rw [abs_sub_comm (γ t₀ j)]
      calc |γ t₁ j - γ t₀ j| = |(γ t₁ j - s * (x₁ j : ℝ)) + (s * (x₁ j : ℝ) - s * (x₀ j : ℝ)) +
            (s * (x₀ j : ℝ) - γ t₀ j)| := by ring_nf
        _ ≤ _ := abs_add_three _ _ _
    linarith
  -- an open site on the discretized path
  obtain ⟨u, hul, huO⟩ := exists_mem_open_of_connIn hdiam (connIn_of_isChain hl)
    ⟨x₀, List.mem_of_mem_head? hhead, x₁, List.mem_of_mem_getLast? hlast, hfar⟩
  obtain ⟨-, -, τ, hτ, hγτ⟩ := hsites u hul
  have hτ01 : τ ∈ Icc (0 : ℝ) 1 := ⟨h0.trans hτ.1, hτ.2.trans h1⟩
  have hτsh := hin τ hτ
  have hreg : ∀ i, s * |(u i : ℝ)| ≤ r₁ := by
    intro i
    have h1 : |γ τ i - s * (u i : ℝ)| < s := hγτ i
    have h2 : |γ τ i| ≤ r₁ - 3 * s := by
      have := hτsh.1 i
      simpa using this
    have h3 := abs_sub_abs_le_abs_sub (s * (u i : ℝ)) (γ τ i)
    rw [abs_sub_comm] at h1
    rw [abs_mul, abs_of_pos hs] at h3
    linarith
  -- the crossing of `B̄_{2s}(s u) \ B_s(s u)`
  have hout : γ 0 ∉ obox (latPt s u) (2 * s) := by
    rw [hγ.source]
    intro hxo
    obtain ⟨j, hj⟩ : ∃ j, r₂ + 3 * s ≤ |γ τ j| := by
      have h := hτsh.2
      rw [mem_obox] at h
      push Not at h
      obtain ⟨j, hj⟩ := h
      exact ⟨j, by simpa using hj⟩
    have h1 : |γ τ j - s * (u j : ℝ)| < s := hγτ j
    have h2 : |x j - s * (u j : ℝ)| < 2 * s := hxo j
    have h3 : |x j| ≤ r₂ := by
      have := (mem_lsph.1 hx).1 j
      simpa using this
    have h4 := abs_sub_abs_le_abs_sub (γ τ j) (x j)
    have h5 := abs_sub_le (γ τ j) (s * (u j : ℝ)) (x j)
    rw [abs_sub_comm (s * (u j : ℝ)) (x j)] at h5
    linarith
  have hcross := acrossDist_le_lfppLength_of_crossing hφ (by linarith : s < 2 * s) hγ hτ01
    (⟨le_rfl, zero_le_one⟩ : (0 : ℝ) ∈ Icc (0 : ℝ) 1) (c := latPt s u) (ξ := ξ)
    (obox_subset_cbox _ _ hγτ) hout
  exact (hopen u huO hreg).trans hcross

/-! ### Local events and per-site bounds -/

/-- The closed-site event of D-4.10 is measurable for the field on `B̄_{2s}(s x)`. -/
lemma measurableSet_acrossClosed_comap {Ω : Type*} {G : Rd d → Ω → ℝ}
    (hc : ∀ ω, Continuous fun z => G z ω) {s : ℝ} (hs : 0 < s) (ξ : ℝ) (p : Prop) (T : ℝ)
    (x : Zd d) :
    MeasurableSet[MeasurableSpace.comap (fun ω (z : cbox (latPt s x) (2 * s)) => G z ω)
      MeasurableSpace.pi]
      {ω | p ∧ acrossDist ξ (fun z => G z ω) (latPt s x) (2 * s) s < T} := by
  let mΩ : MeasurableSpace Ω :=
    MeasurableSpace.comap (fun ω (z : cbox (latPt s x) (2 * s)) => G z ω) MeasurableSpace.pi
  have hf : Measurable fun ω => acrossDist ξ (fun z => G z ω) (latPt s x) (2 * s) s :=
    measurable_acrossDist_comap hc ξ _ (by positivity) (by linarith)
  rw [Set.ofPred_and]
  exact (MeasurableSet.const p).inter (measurableSet_lt hf measurable_const)

/-- **Per-site bound** (MA7 D-4.10): for `G = h_n - h_m`, by scaling and D-4.8 (at `δ/4`),
`P[D(G)(across B_{2s}(w) \ B_s(w)) < T'] ≤ C e^{-(n-m)/C}` when `ξ Q m ≤ δ n/12`
(`s = 2^{-m}`, `T' = 2^{-(1-ξQ)n - δn/3}`). -/
lemma measure_acrossBand_lt_le {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {ξ Q δ Cal : ℝ}
    (hal : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ n : ℕ,
        P {ω | acrossDist ξ (fun z => H n z ω) 0 2 1 < (2 : ℝ) ^ (-(1 - ξ * Q + δ / 4) * n)} ≤
          ENNReal.ofReal (Cal * Real.exp (-(n : ℝ) / Cal)))
    (hδ : 0 < δ) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
    {H : ℕ → Rd d → Ω → ℝ} (hH : IsDyadicRealization κ P W H) {m n : ℕ} (hmn : m ≤ n)
    (hmQ : ξ * Q * m ≤ δ * n / 12) (w : Rd d) :
    P {ω | acrossDist ξ (fun z => H n z ω - H m z ω) w (2 * (2 : ℝ)⁻¹ ^ m) ((2 : ℝ)⁻¹ ^ m) <
        (2 : ℝ) ^ (-(1 - ξ * Q) * n - δ * n / 3)} ≤
      ENNReal.ofReal (Cal * Real.exp (-((n - m : ℕ) : ℝ) / Cal)) := by
  rw [measure_acrossDist_band_lt_eq hκ hH hmn (isBandVersion_sub_of_realization hκ hH hmn) ξ w,
    two_rpow_div_inv_two_pow]
  refine (measure_mono fun ω hω => ?_).trans (hal Ω P W H hH (n - m))
  refine lt_of_lt_of_le hω (Real.rpow_le_rpow_of_exponent_le one_le_two ?_)
  rw [Nat.cast_sub hmn]
  have h1 : 0 ≤ δ * m / 4 := by positivity
  linarith only [hmQ, h1]

/-! ### The tail bound -/

/-- **DGZ Lemma 4.10, across half** (MA7 D-4.10), for the dyadic realizations of `DGZHyp`. -/
theorem superExpAcross_tail {κ : Rd d → ℝ} {ξ Q : ℝ} (h : DGZHyp d κ ξ Q) {δ : ℝ} (hδ : 0 < δ)
    {r₁ r₂ : ℝ} (hr₂ : 0 < r₂) (hr : r₂ < r₁) :
    ∃ C > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ n : ℕ,
        P {ω | acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ ≤ (2 : ℝ) ^ (-(1 - ξ * Q + δ) * n)} ≤
          ENNReal.ofReal (C * Real.exp (-(n : ℝ) * Real.log n)) := by
  have hd := h.dim
  have hd1 : 1 ≤ d := by omega
  have hκ := h.kernel
  have hξ := h.xi_pos
  obtain ⟨hL0, -⟩ := log_two_pos_lt_one
  have hQ : 0 < Q := lt_of_le_of_lt (Real.sqrt_nonneg _) h.subcritical
  obtain ⟨Cal, hCal, hal⟩ := acrossLower_tail h (δ := δ / 4) (by positivity)
  -- the Peierls parameters
  obtain ⟨ρ, -, hρ⟩ := hκ.exists_radius
  obtain ⟨r, hrdef⟩ : ∃ r : ℕ, ⌈2 * (2 + ρ)⌉₊ = r := ⟨_, rfl⟩
  obtain ⟨hθ0, hθ1⟩ := theta_pow_pos_le_one d r
  have hθtop : ENNReal.ofReal (2 * 3 ^ d : ℝ)⁻¹ ^ ((r + 1) ^ d) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hθ1
  obtain ⟨k₀, hk₀⟩ := exists_mul_exp_neg_div_le hCal
    (θ := (ENNReal.ofReal (2 * 3 ^ d : ℝ)⁻¹ ^ ((r + 1) ^ d)).toReal)
    (ENNReal.toReal_pos hθ0.ne' hθtop)
  -- the field at the coarse scale: `c₀ = δ log 2/(3ξ)`
  obtain ⟨n₁, hn₁⟩ := exists_field_superExp hκ (R := r₁ + 1) (by linarith)
    (c := δ * Real.log 2 / (3 * ξ)) (by positivity)
  -- the threshold `n₀`
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (((((eventually_ge_atTop (max 1 (max n₁ (2 * k₀)))).and
    (eventually_superScale_le_mul (c := 1 / 2) (by norm_num))).and
    (eventually_superScale_le_mul (c := δ / (12 * (ξ * Q))) (by positivity))).and
    (eventually_le_two_pow_superScale (max 2 (32 / (3 * (r₁ - r₂)))))).and
    (eventually_peierls_superExp d (a := r₁) (b := (r₁ - r₂) / 4) (by linarith) (by linarith)))
  obtain ⟨C₀, hC₀, hC₀small⟩ := exists_superExp_const n₀
  obtain ⟨C, hC2, hCC₀⟩ : ∃ C : ℝ, 2 ≤ C ∧ C₀ ≤ C := ⟨max 2 C₀, le_max_left _ _, le_max_right _ _⟩
  refine ⟨C, by linarith, fun Ω _ P W H hH n => ?_⟩
  have hW := hH.whiteNoise
  have := hW.isProbabilityMeasure
  rcases lt_or_ge n n₀ with hn | hn
  · -- small `n`
    calc _ ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal ((hC₀small n hn).trans
          (mul_le_mul_of_nonneg_right hCC₀ (Real.exp_pos _).le))
  obtain ⟨⟨⟨⟨hnbig, hm2⟩, hmQ⟩, hs2⟩, hpei⟩ := hn₀ n hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hnbig
  have hnn₁ : n₁ ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hnbig
  have hnk : 2 * k₀ ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hnbig
  -- the scale `m = m(n)` and the mesh `s = 2^{-m}`
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, superScale n = m := ⟨_, rfl⟩
  rw [hmdef] at hm2 hmQ hs2 hpei
  have hmn : m ≤ n := by
    have : (m : ℝ) ≤ n := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    exact_mod_cast this
  have hnm : ((n - m : ℕ) : ℝ) = n - m := Nat.cast_sub hmn
  have hk : k₀ ≤ n - m := by
    have h1 : (2 * k₀ : ℝ) ≤ n := by exact_mod_cast hnk
    have : (k₀ : ℝ) ≤ ((n - m : ℕ) : ℝ) := by rw [hnm]; linarith
    exact_mod_cast this
  have hmQ' : ξ * Q * m ≤ δ * n / 12 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at hmQ
    have : 0 < ξ * Q := by positivity
    nlinarith
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, (2 : ℝ)⁻¹ ^ m = s := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [← hsdef]; positivity
  have hs2m : s * (2 : ℝ) ^ m = 1 := by
    rw [← hsdef, ← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow]
  have hshalf : s ≤ 1 / 2 := by
    have h2 : 2 ≤ (2 : ℝ) ^ m := (le_max_left _ _).trans hs2
    rw [le_div_iff₀ two_pos]
    nlinarith
  have hs8 : 8 * s ≤ 3 * (r₁ - r₂) / 4 := by
    have h2 : 32 / (3 * (r₁ - r₂)) ≤ (2 : ℝ) ^ m := (le_max_right _ _).trans hs2
    rw [div_le_iff₀ (by linarith)] at h2
    nlinarith
  have hG := isBandVersion_sub_of_realization hκ hH hmn
  -- the closed sites
  obtain ⟨T', hT'def⟩ : ∃ T' : ℝ, (2 : ℝ) ^ (-(1 - ξ * Q) * n - δ * n / 3) = T' := ⟨_, rfl⟩
  set closed : Zd d → Set Ω := fun x => {ω | (∀ i, s * |(x i : ℝ)| ≤ r₁) ∧
    acrossDist ξ (fun z => H n z ω - H m z ω) (latPt s x) (2 * s) s < T'} with hclosed
  have hcl : ∀ x, P (closed x) ≤ ENNReal.ofReal (2 * 3 ^ d : ℝ)⁻¹ ^ ((r + 1) ^ d) := by
    intro x
    have h1 := measure_acrossBand_lt_le hκ hal hδ hH hmn hmQ' (latPt s x)
    rw [hsdef, hT'def] at h1
    refine (measure_mono fun ω hω => hω.2).trans (h1.trans ?_)
    rw [← ENNReal.ofReal_toReal hθtop]
    exact ENNReal.ofReal_le_ofReal (hk₀ _ hk)
  have hPB : ProductBound P closed (r : ℤ) := by
    have := productBound_of_local hκ hW hρ (by positivity) hG hs0 hsdef.le (R := 2) closed
      fun x => measurableSet_acrossClosed_comap hG.continuous hs0 ξ _ T' x
    rwa [hrdef] at this
  -- the Peierls event
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, ⌈r₁ / s⌉₊ = N := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : ℕ, ⌊(r₁ - r₂) / (4 * s)⌋₊ = D := ⟨_, rfl⟩
  have hN : ∀ x ω, ω ∈ closed x → WithinInf (N : ℤ) x 0 := by
    intro x ω hω i
    have h1 := hω.1 i
    have h2 : |(x i : ℝ)| ≤ r₁ / s := by
      rw [le_div_iff₀ hs0]
      linarith
    have h3 : |(x i : ℝ)| ≤ N := h2.trans (by rw [← hNdef]; exact Nat.le_ceil _)
    simp only [Pi.zero_apply, sub_zero]
    exact_mod_cast h3
  have hpeierls := measure_not_smallClusters_le P closed r _ _ hcl hPB
    (HigherDimLFPP.L33.theta_le_one d) le_rfl (HigherDimLFPP.L33.three_pow_mul_theta_le d) N D hN
  have hNb : (N : ℝ) ≤ r₁ * (2 : ℝ) ^ m + 1 := by
    have h1 : (N : ℝ) < r₁ / s + 1 := by
      rw [← hNdef]; exact Nat.ceil_lt_add_one (div_nonneg (by linarith) hs0.le)
    have h2 : r₁ / s = r₁ * (2 : ℝ) ^ m := by
      rw [div_eq_iff hs0.ne']
      linear_combination r₁ * hs2m.symm
    linarith
  have hDb : (r₁ - r₂) / 4 * (2 : ℝ) ^ m ≤ D + 1 := by
    have h1 : (r₁ - r₂) / (4 * s) < D + 1 := by rw [← hDdef]; exact Nat.lt_floor_add_one _
    have h2 : (r₁ - r₂) / (4 * s) = (r₁ - r₂) / 4 * (2 : ℝ) ^ m := by
      rw [div_eq_iff (by positivity)]
      linear_combination (r₁ - r₂) * hs2m.symm
    linarith
  have hPei := hpeierls.trans (hpei N D hNb hDb)
  -- the field event
  have hfield := hn₁ hH n hnn₁
  rw [hmdef] at hfield
  -- the inclusion
  have hsub : {ω | acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ ≤ (2 : ℝ) ^ (-(1 - ξ * Q + δ) * n)} ⊆
      {ω | ∃ z ∈ cbox (0 : Rd d) (r₁ + 1), δ * Real.log 2 / (3 * ξ) * n < |H m z ω|} ∪
        {ω | ¬ SmallClusters {x | ω ∉ closed x} D} := by
    intro ω hω
    by_contra hno
    simp only [mem_union, mem_ofPred_eq, not_or, not_not, not_exists, not_and, not_lt] at hno
    obtain ⟨hF, hsmall⟩ := hno
    have hφ := (hH.band n).continuous ω
    have hψ := hG.continuous ω
    -- every open site of the region has a large across distance
    have hopen : ∀ x ∈ {x | ω ∉ closed x}, (∀ i, s * |(x i : ℝ)| ≤ r₁) →
        T' / Real.exp (ξ * (δ * Real.log 2 / (3 * ξ) * n)) ≤
          acrossDist ξ (fun z => H n z ω) (latPt s x) (2 * s) s := by
      intro x hx hreg
      have hT : T' ≤ acrossDist ξ (fun z => H n z ω - H m z ω) (latPt s x) (2 * s) s := by
        by_contra hlt
        exact hx ⟨hreg, not_le.1 hlt⟩
      have hcmp := acrossDist_le_mul_of_exp_le hψ hφ (by linarith : s < 2 * s)
        (C := Real.exp (ξ * (δ * Real.log 2 / (3 * ξ) * n))) (c := latPt s x) (ξ := ξ)
        (Real.exp_pos _).le (by
          intro z hz
          have hz1 : z ∈ cbox (0 : Rd d) (r₁ + 1) := by
            intro i
            have h1 := hz.1 i
            have h2 := hreg i
            simp only [PiLp.zero_apply, sub_zero]
            rw [latPt_apply] at h1
            have h3 := abs_sub_abs_le_abs_sub (z i) (s * (x i : ℝ))
            rw [abs_mul, abs_of_pos hs0] at h3
            linarith
          have h1 := hF z hz1
          have h2 := neg_abs_le (H m z ω)
          rw [← Real.exp_add, Real.exp_le_exp]
          have := mul_le_mul_of_nonneg_left (show -H m z ω ≤ δ * Real.log 2 / (3 * ξ) * n by
            linarith) hξ.le
          nlinarith)
      rw [div_le_iff₀ (Real.exp_pos _)]
      linarith
    have hlow := le_acrossDist_of_smallDiam hd1 hφ hs0 hr₂.le
      (fun C hC => (hsmall C hC).2) (by
        have h1 : (D : ℝ) ≤ (r₁ - r₂) / (4 * s) := by
          rw [← hDdef]; exact Nat.floor_le (by positivity)
        rw [le_div_iff₀ (by positivity)] at h1
        linarith) hopen
    have hlt : (2 : ℝ) ^ (-(1 - ξ * Q + δ) * n) <
        T' / Real.exp (ξ * (δ * Real.log 2 / (3 * ξ) * n)) := by
      rw [lt_div_iff₀ (Real.exp_pos _), ← hT'def, Real.rpow_def_of_pos two_pos,
        Real.rpow_def_of_pos two_pos, ← Real.exp_add, Real.exp_lt_exp]
      have e : ξ * (δ * Real.log 2 / (3 * ξ) * n) = δ * Real.log 2 * n / 3 := by
        field_simp
      rw [e]
      have h1 : (0 : ℝ) < δ * Real.log 2 * n := by
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        positivity
      nlinarith
    have hω' : acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ ≤ (2 : ℝ) ^ (-(1 - ξ * Q + δ) * n) := hω
    linarith
  calc P {ω | acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ ≤ (2 : ℝ) ^ (-(1 - ξ * Q + δ) * n)}
      ≤ P ({ω | ∃ z ∈ cbox (0 : Rd d) (r₁ + 1), δ * Real.log 2 / (3 * ξ) * n < |H m z ω|} ∪
        {ω | ¬ SmallClusters {x | ω ∉ closed x} D}) := measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * Real.log n)) +
          ENNReal.ofReal (Real.exp (-(n : ℝ) * Real.log n)) :=
        (measure_union_le _ _).trans (add_le_add hfield hPei)
    _ = ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * Real.log n)) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, two_mul]
    _ ≤ ENNReal.ofReal (C * Real.exp (-(n : ℝ) * Real.log n)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC2 (Real.exp_pos _).le)

/-- **MA7 Details (c) `SuperExpAcrossShape`** (DGZ Lemma 4.10, across half; MA7 D-4.10), for
every `d, κ, ξ, Q`. -/
theorem superExpAcrossShape (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ) : SuperExpAcrossShape d κ ξ Q :=
  fun h _ hδ _ _ hr₂ hr => superExpAcross_tail h hδ hr₂ hr

end DGZ

end HigherDimLQGMetric
