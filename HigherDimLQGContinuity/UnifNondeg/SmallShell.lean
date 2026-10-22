import HigherDimLQGContinuity.UnifNondeg.SeqTight
import HigherDimLQGMetric.DGZ.NondegLawTransfer

/-!
# Uniform nondegeneracy of small shells (packet U5)

Blueprint Part D, `d:prop-u64`(a), first paragraph (NA3 §2.8, R11; errata ED `d:err-depth`): for a quantile
`q ∈ (0, 1)` at which the uniform inputs hold — Hölder tightness `UHolderTightAt`, distance to infinity
`UDistInfAt`, and positive crossings `UCrossPosAt` (Part D `d:lem-u65`(b)) — the normalized crossings of every small
shell `B_{2r}(0) \ B_r(0)` are bounded below in probability, uniformly in `ξ ∈ S(b, μ)`, over realizations and
**for every depth `n`**.

* `u5_limit_positiveCross_prob`: the witness passes to array limits (closed-set portmanteau).
* `u5_smallShell_nondeg_of_inputs`: the contradiction argument along arrays `(ξ_j, n_j)` for one realization:
  bad arrays have `n_j → ∞`, a convergent subsequence of joint laws (μ0), limit mass `≤ 1 - θ` on positive crossings,
  the witness gives mass `≥ c > 0`, contradicting the sequence zero-one law `u5_zeroOne_limitLaw_of_bounded` (the
  zero sets are bounded by `UDistInfAt`, (μ5)).
* `u5_smallShell_nondeg_eventually`: the same for all realizations (law transfer to the canonical realization).
* `u5_smallShell_nondeg_finite`: the **finite-depth bound** for `n < N`: on `{sup_{B̄₂(0)} |h_n| ≤ L}`,
  `D_n(across) ≥ r e^{-bL}` and `a^ξ_n(q) ≤ e^{bL}` (uniform in `ξ ≤ b`).
* `u5_smallShell_nondeg`: every depth.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLQGMetric.DGZ
open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox)

variable {d : ℕ}

/-- **Uniform positive crossings at the quantile `q`** (Part D `d:lem-u65`(b); the form of packet U4's
`nondeg_cross_pos_unif`, with an eventual depth `N`): for every small radius `r` there is `c > 0` with
`P[c a^ξ_n(q) < D^ξ_n(across B_{2r}(0) \ B_r(0))] ≥ c` for `ξ ∈ S(b, μ)`, every realization and `n ≥ N`. -/
def UCrossPosAt (d : ℕ) (κ : Rd d → ℝ) (b μ : ℝ) (q : ℝ≥0∞) : Prop :=
  ∀ r : ℝ, 0 < r → r * (10 * Real.sqrt d) ≤ 1 → ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ ξ : ℝ, UHyp d κ b μ ξ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : HigherDimLFPP.WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), DGZ.IsDyadicRealization κ P W H → ∀ n : ℕ, N ≤ n →
        ENNReal.ofReal c ≤
          P {ω | c * DGZ.aQ P H ξ n q < DGZ.acrossDist ξ (fun w => H n w ω) 0 (2 * r) r}

section Limit

variable {κ : Rd d → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ} {b μ : ℝ} {ξs : ℕ → ℝ} {q : ℝ≥0∞}

/-- **The witness passes to array limits** (port of `DGZ.nd_limit_positiveCross_prob`, with an eventual witness). -/
theorem u5_limit_positiveCross_prob (hH : IsDyadicRealization κ P W H)
    (hU : ∀ k, UHyp d κ b μ (ξs k)) (hq0 : 0 < q) (hq1 : q < 1)
    (rGrid r c : ℝ) (hc : 0 < c) (ns : ℕ → ℕ) {μ₀ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q rGrid (ns k))
      atTop (𝓝 μ₀))
    (hcross : ∀ᶠ k in atTop, ENNReal.ofReal c ≤
      P {ω | c * aQ P H (ξs k) (ns k) q < acrossDist (ξs k) (fun z => H (ns k) z ω) 0 (2 * r) r}) :
    ENNReal.ofReal c ≤ (μ₀ : Measure (nd_Joint d rGrid)) (nd_positiveCrossEvent rGrid r) := by
  have hd0 : 0 < d := by have := (hU 0).dim; omega
  let F := nd_crossGeCSet (d := d) rGrid r c
  have hF : IsClosed F := nd_isClosed_crossGeCSet rGrid r c
  have hpre : ∀ᶠ k in atTop, ENNReal.ofReal c ≤ P (nd_jointSample P H (ξs k) q rGrid (ns k) ⁻¹' F) := by
    filter_upwards [hcross] with k hk
    refine hk.trans (measure_mono fun ω hω => ?_)
    have ha : 0 < aQ P H (ξs k) (ns k) q := tight_aQ_pos hd0 hH (ξs k) (ns k) hq0 hq1
    change c ≤ nd_crossPhi 0 (2 * r) r
      (normMetricC (ξs k) (fun z => H (ns k) z ω) (aQ P H (ξs k) (ns k) q))
    rw [nd_crossPhi_normMetricC ((hH.band (ns k)).continuous ω) ha]
    change c * aQ P H (ξs k) (ns k) q < acrossDist (ξs k) (fun z => H (ns k) z ω) 0 (2 * r) r at hω
    rw [mul_comm c] at hω
    exact ((lt_inv_mul_iff₀ ha).2 hω).le
  have hlimF := u5_le_measure_of_eventually hH hlim hF hpre
  exact hlimF.trans (measure_mono fun s hs => hc.trans_le hs)

end Limit

section Small

variable {κ : Rd d → ℝ} {b μ β : ℝ} {q : ℝ≥0∞}

/-- **The contradiction argument of `d:prop-u64`(a) for one realization** (port of
`DGZ.nd_smallShell_nondeg_fixed_of_limit_inputs` along arrays): under the three uniform inputs at the quantile `q`,
for every small shell and `θ ∈ (0, 1]` there are `δ > 0` and `N` with
`P[D^ξ_n(across B_{2r}(0) \ B_r(0)) ≤ δ a^ξ_n(q)] ≤ θ` for every `ξ ∈ S(b, μ)` and `n ≥ N`. -/
theorem u5_smallShell_nondeg_of_inputs (hκ : IsLFPPKernel κ) (hq0 : 0 < q) (hq1 : q < 1)
    (hT : UHolderTightAt d κ b μ q β) (hβ : 0 < β) (hI : UDistInfAt d κ b μ q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ)
    (hH : IsDyadicRealization κ P W H) {r : ℝ} (hr : 0 < r) {c : ℝ} (hc : 0 < c) {Nw : ℕ}
    (hW : ∀ ξ : ℝ, UHyp d κ b μ ξ → ∀ n : ℕ, Nw ≤ n →
      ENNReal.ofReal c ≤ P {ω | c * aQ P H ξ n q < acrossDist ξ (fun z => H n z ω) 0 (2 * r) r})
    {θ : ℝ≥0∞} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ ξ : ℝ, UHyp d κ b μ ξ → ∀ n : ℕ, N ≤ n →
      P {ω | acrossDist ξ (fun z => H n z ω) 0 (2 * r) r ≤ δ * aQ P H ξ n q} ≤ θ := by
  by_contra hno
  push Not at hno
  let δs : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hδpos (k : ℕ) : 0 < δs k := by dsimp [δs]; positivity
  have hbadall : ∀ k : ℕ, ∃ ξ : ℝ, UHyp d κ b μ ξ ∧ ∃ n : ℕ, k ≤ n ∧
      θ < P {ω | acrossDist ξ (fun z => H n z ω) 0 (2 * r) r ≤ δs k * aQ P H ξ n q} := by
    intro k
    exact hno (δs k) (hδpos k) k
  choose ξs hU ns hns_ge hbad using hbadall
  have hns : Tendsto ns atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro m
    filter_upwards [eventually_ge_atTop m] with k hk
    exact hk.trans (hns_ge k)
  obtain ⟨μ₀, ψ, hψ, hlim⟩ := u5_exists_joint_limit hκ hT hβ hq0 hq1 r P W H hH ξs hU ns
  let ξs' : ℕ → ℝ := fun k => ξs (ψ k)
  let ns' : ℕ → ℕ := fun k => ns (ψ k)
  have hU' : ∀ k, UHyp d κ b μ (ξs' k) := fun k => hU (ψ k)
  have hns' : Tendsto ns' atTop atTop := hns.comp hψ.tendsto_atTop
  have hlim' : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs' k) q r (ns' k))
      atTop (𝓝 μ₀) := hlim
  have hδlim : Tendsto (δs ∘ ψ) atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hψ.tendsto_atTop
  -- the bad mass
  have hbadlim : (μ₀ : Measure (nd_Joint d r)) (nd_positiveCrossEvent r r) ≤ 1 - θ := by
    apply nd_limit_positiveCross_le_of_bad
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs' k) q r (ns' k)) μ₀ hlim'
      (δs ∘ ψ) hδlim θ hθ1
    intro k
    exact nd_jointLaw_badCross_prob (hU' k).base hH hq0 hq1 r r (δs (ψ k)) (ns' k) (hbad (ψ k)).le
  -- the witness
  have hpos : ENNReal.ofReal c ≤ (μ₀ : Measure (nd_Joint d r)) (nd_positiveCrossEvent r r) := by
    refine u5_limit_positiveCross_prob hH hU' hq0 hq1 r r c hc ns' hlim' ?_
    filter_upwards [hns'.eventually (eventually_ge_atTop Nw)] with k hk
    exact hW (ξs' k) (hU' k) (ns' k) hk
  -- bounded zero sets at `r` and `2r`
  have hbdd : ∀ r' : ℝ, 0 < r' →
      ∀ᵐ s ∂(μ₀ : Measure (nd_Joint d r)), s ∈ nd_boundedZeroEvent r r' := by
    intro r' hr'
    refine u5_ae_boundedZeroEvent hH hU' hq0 hq1 r r' hr' ns' hlim' fun θ' hθ' => ?_
    obtain ⟨R, hR, N', hN'⟩ := hI r' 1 θ' hr' hθ'
    refine ⟨R, hR, ?_⟩
    filter_upwards [hns'.eventually (eventually_ge_atTop N')] with k hk
    simpa only [one_mul] using hN' (ξs' k) (hU' k) Ω P W H hH (ns' k) hk
  rcases u5_zeroOne_limitLaw_of_bounded hH hU' hq0 hq1 r r hr hr ns' hns' hlim' (hbdd r hr)
      (hbdd (2 * r) (by positivity)) with hz | hz
  · have hcpos : (0 : ℝ≥0∞) < ENNReal.ofReal c := ENNReal.ofReal_pos.mpr hc
    rw [hz] at hpos
    exact (not_le_of_gt hcpos) hpos
  · rw [hz] at hbadlim
    exact (not_le_of_gt (ENNReal.sub_lt_self (by simp) (by simp) hθ0.ne')) hbadlim

/-- **Every realization** (port of `DGZ.nd_smallShell_nondeg_uniform`): the contradiction argument on the canonical
realization and the transfer of the law of `(D_n(across), a^ξ_n(q))` (`DGZ.nd_across_bad_prob_eq_of_realizations`). -/
theorem u5_smallShell_nondeg_eventually (hκ : IsLFPPKernel κ) (hq0 : 0 < q) (hq1 : q < 1)
    (hT : UHolderTightAt d κ b μ q β) (hβ : 0 < β) (hI : UDistInfAt d κ b μ q)
    (hW : UCrossPosAt d κ b μ q) {r : ℝ} (hr : 0 < r) (hrd : r * (10 * Real.sqrt d) ≤ 1)
    {θ : ℝ≥0∞} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
        IsDyadicRealization κ P W H → ∀ n : ℕ, N ≤ n →
          P {ω | acrossDist ξ (fun z => H n z ω) 0 (2 * r) r ≤ δ * aQ P H ξ n q} ≤ θ := by
  obtain ⟨W₀, hW₀⟩ := exists_isWhiteNoise d
  obtain ⟨H₀, hH₀⟩ := exists_isDyadicRealization hκ hW₀
  obtain ⟨c, hc, Nw, hcross⟩ := hW r hr hrd
  obtain ⟨δ, hδ, N, hN⟩ := u5_smallShell_nondeg_of_inputs hκ hq0 hq1 hT hβ hI
    LQGDimension.ExistAsm.stdP W₀ H₀ hH₀ hr hc
    (fun ξ hξ n hn => hcross ξ hξ (ℕ → ℝ) LQGDimension.ExistAsm.stdP W₀ H₀ hH₀ n hn) hθ0 hθ1
  refine ⟨δ, hδ, N, fun ξ hξ Ω _ P W H hH n hn => ?_⟩
  rw [nd_across_bad_prob_eq_of_realizations hκ hH hH₀ ξ n q r δ]
  exact hN ξ hξ n hn

/-- Uniform tail levels of `sup_{B̄_R(0)} |h_n|` for the finitely many depths `n < N`. -/
theorem u5_exists_sup_tail_levels (hκ : IsLFPPKernel κ) (N : ℕ) {R : ℝ} (hR : 0 ≤ R) {θ : ℝ}
    (hθ : 0 < θ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ n : ℕ, n < N → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
        P {ω | ∃ z ∈ cbox (0 : Rd d) R, L < |H n z ω|} ≤ ENNReal.ofReal θ := by
  induction N with
  | zero => exact ⟨0, le_rfl, fun n hn => absurd hn (Nat.not_lt_zero n)⟩
  | succ N ih =>
    obtain ⟨L', hL'0, hL'⟩ := ih
    obtain ⟨L₁, hL₁0, hL₁⟩ := exists_sup_tail_level_tight hκ N hR hθ
    refine ⟨max L' L₁, le_max_of_le_left hL'0, fun n hn Ω _ P W H hH => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hlt | heq
    · refine le_trans (measure_mono fun ω hω => ?_) (hL' n hlt Ω P W H hH)
      obtain ⟨z, hz, hzL⟩ := hω
      exact ⟨z, hz, lt_of_le_of_lt (le_max_left _ _) hzL⟩
    · subst heq
      refine le_trans (measure_mono fun ω hω => ?_) (hL₁ hH.whiteNoise (hH.band n) 0)
      obtain ⟨z, hz, hzL⟩ := hω
      exact ⟨z, hz, lt_of_le_of_lt (le_max_right _ _) hzL⟩

/-- **The finite-depth bound** (Part D `d:prop-u64`(a), errata `d:err-depth`): for finitely many depths `n < N`,
uniformly in `ξ ∈ [0, b]`: on `{sup_{B̄₂(0)} |h_n| ≤ L}`, `D^ξ_n(across B_{2r}(0) \ B_r(0)) ≥ r e^{-bL}` and
`D^ξ_n(0, e₁; B₂(0)) ≤ e^{bL}`, so `a^ξ_n(q) ≤ e^{bL}` once `P[sup > L] ≤ 1 - q`; hence
`P[D^ξ_n(across) ≤ δ a^ξ_n(q)] ≤ θ` with `δ = r e^{-2bL}/2`. -/
theorem u5_smallShell_nondeg_finite (hd : 0 < d) (hκ : IsLFPPKernel κ)
    (hq0 : 0 < q) (hq1 : q < 1) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (N : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ξ : ℝ, 0 ≤ ξ → ξ ≤ b →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
        IsDyadicRealization κ P W H → ∀ n : ℕ, n < N →
          P {ω | acrossDist ξ (fun z => H n z ω) 0 (2 * r) r ≤ δ * aQ P H ξ n q} ≤
            ENNReal.ofReal θ := by
  have hq1' : (1 : ℝ≥0∞) - q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  set t : ℝ := ((1 : ℝ≥0∞) - q).toReal with ht
  have ht0 : 0 < t := ENNReal.toReal_pos (tsub_pos_of_lt hq1).ne' hq1'
  have htq : ENNReal.ofReal t = 1 - q := ENNReal.ofReal_toReal hq1'
  obtain ⟨L, hL0, hL⟩ := u5_exists_sup_tail_levels (κ := κ) hκ N (R := 2) zero_le_two
    (θ := min θ t) (lt_min hθ ht0)
  refine ⟨r * Real.exp (-(2 * (b * L))) / 2, by positivity, ?_⟩
  intro ξ hξ0 hξb Ω _ P W H hH n hn
  have : IsProbabilityMeasure P := hH.whiteNoise.isProbabilityMeasure
  set G : Set Ω := {ω | ∃ z ∈ cbox (0 : Rd d) 2, L < |H n z ω|} with hGdef
  have hG : P G ≤ ENNReal.ofReal (min θ t) := hL n hn Ω P W H hH
  have hbL : ξ * L ≤ b * L := mul_le_mul_of_nonneg_right hξb hL0
  -- the upper bound for the quantile
  have hgood : ∀ ω, ω ∉ G → ∀ z ∈ cbox (0 : Rd d) 2, |H n z ω| ≤ L := by
    intro ω hω z hz
    by_contra hlt
    exact hω ⟨z, hz, lt_of_not_ge hlt⟩
  have hXle : ∀ ω, ω ∉ G → lfppDistance d ξ (fun z => H n z ω) ≤ Real.exp (b * L) := by
    intro ω hω
    rw [lfppDistance_eq_lfppDistOn]
    have hM : ∀ z ∈ HigherDimLFPP.cube d, ξ * H n z ω ≤ b * L := by
      intro z hz
      have h1 := hgood ω hω z (cube_subset_cbox_two hz)
      have h2 : H n z ω ≤ L := (le_abs_self _).trans h1
      calc ξ * H n z ω ≤ ξ * L := mul_le_mul_of_nonneg_left h2 hξ0
        _ ≤ b * L := hbL
    have h := lfppDistOn_le_exp_mul_norm_of_convex ((hH.band n).continuous ω)
      (HigherDimLFPP.convex_cube d) (HigherDimLFPP.zero_mem_cube d) (HigherDimLFPP.e₁_mem_cube d) hM
    rwa [sub_zero, HigherDimLFPP.norm_e₁ hd, mul_one] at h
  have haQ : aQ P H ξ n q ≤ Real.exp (b * L) := by
    have hXm := (hH.band n).measurable_lfppDistance ξ
    unfold aQ
    rw [← LQGMetric.le_measure_Iic_iff_lowerQuantile_le hq0 hq1, Measure.map_apply hXm measurableSet_Iic]
    have hcov : (univ : Set Ω) ⊆
        (fun ω => lfppDistance d ξ (fun z => H n z ω)) ⁻¹' Iic (Real.exp (b * L)) ∪ G := by
      intro ω _
      by_cases hω : ω ∈ G
      · exact Or.inr hω
      · exact Or.inl (hXle ω hω)
    have h1 : (1 : ℝ≥0∞) ≤
        P ((fun ω => lfppDistance d ξ (fun z => H n z ω)) ⁻¹' Iic (Real.exp (b * L))) + (1 - q) := by
      calc (1 : ℝ≥0∞) = P univ := measure_univ.symm
        _ ≤ P ((fun ω => lfppDistance d ξ (fun z => H n z ω)) ⁻¹' Iic (Real.exp (b * L)) ∪ G) :=
            measure_mono hcov
        _ ≤ _ := measure_union_le _ _
        _ ≤ _ := add_le_add le_rfl (hG.trans (by rw [← htq]; exact ENNReal.ofReal_le_ofReal (min_le_right _ _)))
    calc q = 1 - (1 - q) := (ENNReal.sub_sub_cancel ENNReal.one_ne_top hq1.le).symm
      _ ≤ _ := tsub_le_iff_right.2 h1
  -- the lower bound for the crossing on the good event
  have hsub : {ω | acrossDist ξ (fun z => H n z ω) 0 (2 * r) r ≤
      r * Real.exp (-(2 * (b * L))) / 2 * aQ P H ξ n q} ⊆ G := by
    intro ω hω
    by_contra hωG
    have hlow : Real.exp (-(b * L)) * (2 * r - r) ≤ acrossDist ξ (fun z => H n z ω) 0 (2 * r) r := by
      refine exp_mul_le_acrossDist hd ((hH.band n).continuous ω) hr.le (by linarith) fun z hz => ?_
      have hz2 : z ∈ cbox (0 : Rd d) 2 := fun i => (hz.1 i).trans (by linarith)
      have h1 := hgood ω hωG z hz2
      have h2 : -L ≤ H n z ω := (abs_le.1 h1).1
      have h3 : ξ * -L ≤ ξ * H n z ω := mul_le_mul_of_nonneg_left h2 hξ0
      linarith
    have hδa : r * Real.exp (-(2 * (b * L))) / 2 * aQ P H ξ n q ≤
        r * Real.exp (-(2 * (b * L))) / 2 * Real.exp (b * L) :=
      mul_le_mul_of_nonneg_left haQ (by positivity)
    have hexp : r * Real.exp (-(2 * (b * L))) / 2 * Real.exp (b * L) = Real.exp (-(b * L)) * r / 2 := by
      rw [show -(2 * (b * L)) = -(b * L) + -(b * L) by ring, Real.exp_add]
      have := Real.exp_pos (b * L)
      field_simp
      rw [← Real.exp_add]
      simp
    have hpos : 0 < Real.exp (-(b * L)) * r := by positivity
    have : acrossDist ξ (fun z => H n z ω) 0 (2 * r) r ≤ Real.exp (-(b * L)) * r / 2 := by
      have := hω
      simp only [mem_ofPred_eq] at this
      linarith
    linarith
  exact (measure_mono hsub).trans (hG.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)))

/-- **Small shells at every depth** (Part D `d:prop-u64`(a), first fixing the shell `B_{2r}(0) \ B_r(0)`): under the
three uniform inputs at the quantile `q`, for every `θ > 0` there is `δ > 0` with
`P[D^ξ_n(across B_{2r}(0) \ B_r(0)) ≤ δ a^ξ_n(q)] ≤ θ` for every `ξ ∈ S(b, μ)`, every realization and **every**
`n`. -/
theorem u5_smallShell_nondeg (hκ : IsLFPPKernel κ) (hq0 : 0 < q) (hq1 : q < 1)
    (hT : UHolderTightAt d κ b μ q β) (hβ : 0 < β) (hI : UDistInfAt d κ b μ q)
    (hW : UCrossPosAt d κ b μ q) {r : ℝ} (hr : 0 < r) (hrd : r * (10 * Real.sqrt d) ≤ 1)
    (hd : 0 < d) {θ : ℝ} (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
        IsDyadicRealization κ P W H → ∀ n : ℕ,
          P {ω | acrossDist ξ (fun z => H n z ω) 0 (2 * r) r ≤ δ * aQ P H ξ n q} ≤
            ENNReal.ofReal θ := by
  have hr1 : r ≤ 1 := by
    have hs : 1 ≤ Real.sqrt d := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hd)
    nlinarith
  obtain ⟨δE, hδE, N, hN⟩ := u5_smallShell_nondeg_eventually hκ hq0 hq1 hT hβ hI hW hr hrd
    (θ := ENNReal.ofReal (min θ 1)) (ENNReal.ofReal_pos.2 (lt_min hθ one_pos))
    (ENNReal.ofReal_le_one.2 (min_le_right _ _))
  obtain ⟨δF, hδF, hF⟩ := u5_smallShell_nondeg_finite (b := b) hd hκ hq0 hq1 hr hr1 N hθ
  refine ⟨min δE δF, lt_min hδE hδF, fun ξ hξ Ω _ P W H hH n => ?_⟩
  have hd0 := hd
  have ha : 0 ≤ aQ P H ξ n q := (tight_aQ_pos hd0 hH ξ n hq0 hq1).le
  by_cases hn : N ≤ n
  · refine le_trans (measure_mono fun ω hω => ?_) ((hN ξ hξ Ω P W H hH n hn).trans
      (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
    simp only [mem_ofPred_eq] at hω ⊢
    exact hω.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) ha)
  · refine le_trans (measure_mono fun ω hω => ?_)
      (hF ξ hξ.xi_pos.le hξ.le_b Ω P W H hH n (lt_of_not_ge hn))
    simp only [mem_ofPred_eq] at hω ⊢
    exact hω.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) ha)

end Small

end HigherDimLQGContinuity
