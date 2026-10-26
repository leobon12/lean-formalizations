import SupercriticalConformalCovariance.Tangent.EpigraphPullback
import SupercriticalConformalCovariance.Tangent.LscLemmas

/-!
# Lemma 3.3, steps 4–6: pullback and passage to expanding confinement

Paper l. 221–230. For each fixed target confinement radius `S`, the target closed-disk metrics
`T^S_n` converge in probability to `T^S` (steps 2–3); `T^S → T^∞` as `S → ∞`; pullback by `ψ_n`
preserves epigraph convergence (step 4, `lscTendsto_pullback_univalent`); and the barrier event of
Lemma 3.2 makes `e_n` agree with the pulled-back fixed-confinement metric on every inner square with
probability close to one (step 6).

The printed text passes from fixed to expanding confinement "uniformly in probability on each inner
disk" but leaves the limit interchange implicit (source gap `lem-3.3#expanding-confinement`).
It is made rigorous here by a diagonal choice `S_n → ∞`
(`tendstoInMeasure_diagonal`), for which the barrier probabilities tend to one by monotonicity in
`S`, followed by the local-agreement criterion `SubseqLSC.of_local_agreement`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal

namespace SupercriticalConformalCovariance.Tangent

open SupercriticalLQGUniqueness (LSCTendsto LSCFun)

/-- **Diagonal choice for convergence in measure.** If `F S n → FL S` in measure for every `S`
and `FL S → F∞` in measure, there is `s n → ∞` (as slowly as needed, `M (s n) ≤ n` eventually)
with `F (s n) n → F∞` in measure. No measurability is needed. -/
theorem tendstoInMeasure_diagonal {Ω L : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [PseudoEMetricSpace L] (F : ℕ → ℕ → Ω → L) (FL : ℕ → Ω → L) (Finf : Ω → L)
    (h1 : ∀ S, TendstoInMeasure P (F S) atTop (FL S)) (h2 : TendstoInMeasure P FL atTop Finf)
    (M : ℕ → ℕ) :
    ∃ s : ℕ → ℕ, Tendsto s atTop atTop ∧ (∀ᶠ n in atTop, M (s n) ≤ n) ∧
      TendstoInMeasure P (fun n => F (s n) n) atTop Finf := by
  -- thresholds for the rate `(S+1)⁻¹`
  have hthr : ∀ S : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      P {ω | ((S : ℝ≥0∞) + 1)⁻¹ ≤ edist (F S n ω) (FL S ω)} ≤ ((S : ℝ≥0∞) + 1)⁻¹ := by
    intro S
    have hpos : (0 : ℝ≥0∞) < ((S : ℝ≥0∞) + 1)⁻¹ := ENNReal.inv_pos.2 (by simp)
    have := (h1 S _ hpos).eventually (ge_mem_nhds hpos)
    exact eventually_atTop.1 this
  choose N₁ hN₁ using hthr
  set N : ℕ → ℕ := fun S => (Finset.range (S + 1)).sum (fun S' => N₁ S' + M S') + S with hN
  have hN₁le : ∀ S, N₁ S ≤ N S ∧ M S ≤ N S ∧ S ≤ N S := by
    intro S
    have : N₁ S + M S ≤ (Finset.range (S + 1)).sum (fun S' => N₁ S' + M S') :=
      Finset.single_le_sum (f := fun S' => N₁ S' + M S') (fun i _ => Nat.zero_le _)
        (Finset.self_mem_range_succ S)
    refine ⟨?_, ?_, ?_⟩ <;> simp only [hN] <;> omega
  set s : ℕ → ℕ := fun n => Nat.findGreatest (fun S => N S ≤ n) n with hs
  have hspec : ∀ n, N 0 ≤ n → N (s n) ≤ n := fun n hn =>
    Nat.findGreatest_spec (P := fun S => N S ≤ n) (Nat.zero_le n) hn
  have hge : ∀ K n, N K ≤ n → K ≤ s n := fun K n hKn =>
    Nat.le_findGreatest ((hN₁le K).2.2.trans hKn) hKn
  have hstend : Tendsto s atTop atTop :=
    tendsto_atTop.2 fun K => (eventually_ge_atTop (N K)).mono fun n hn => hge K n hn
  refine ⟨s, hstend, (eventually_ge_atTop (N 0)).mono fun n hn =>
    (hN₁le (s n)).2.1.trans (hspec n hn), ?_⟩
  intro ε hε
  -- split `ε` in halves
  have hε2 : 0 < ε / 2 := ENNReal.div_pos hε.ne' (by norm_num)
  have hsplit : ∀ x y z : L, ε ≤ edist x z → ε / 2 ≤ edist x y ∨ ε / 2 ≤ edist y z := by
    intro x y z hxz
    by_contra hcon
    simp only [not_or, not_le] at hcon
    have := (edist_triangle x y z).trans_lt (ENNReal.add_lt_add hcon.1 hcon.2)
    rw [ENNReal.add_halves] at this
    exact absurd hxz (not_le.2 this)
  -- the second piece
  have hB := (h2 (ε / 2) hε2).comp hstend
  -- the first piece: eventually `(s n + 1)⁻¹ ≤ ε / 2`
  have hA' : Tendsto (fun n => ((s n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
    have h0 : Tendsto (fun k : ℕ => ((k : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
      have := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
      simpa [Function.comp_def] using this
    exact h0.comp hstend
  have hsmall : ∀ᶠ n in atTop, ((s n : ℝ≥0∞) + 1)⁻¹ ≤ ε / 2 :=
    hA'.eventually (ge_mem_nhds hε2)
  have hA : Tendsto (fun n => P {ω | ε / 2 ≤ edist (F (s n) n ω) (FL (s n) ω)}) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hA'
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [hsmall, eventually_ge_atTop (N 0)] with n hn hn0
    refine (measure_mono fun ω hω => hn.trans hω).trans ?_
    exact hN₁ (s n) n ((hN₁le (s n)).1.trans (hspec n hn0))
  have hsum := hA.add hB
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) fun n => ?_
  refine (measure_mono fun ω hω => hsplit _ (FL (s n) ω) _ hω).trans ?_
  exact measure_union_le _ _

/-- **Expanding confinement, abstract form** (paper l. 221–230). In the setting of Lemma 3.3 for
`ψ_n`, suppose:
* for every `S`, the LSC-valued target metrics `T S n` converge in probability to `TL S`
  (fixed confinement), all a.e.-strongly measurable;
* `TL S → T∞` almost surely as `S → ∞`;
* the barrier estimate: for every inner radius `R` and `δ > 0` there are `S₀`, `N` such that for
  `S ≥ S₀`, `n ≥ N` and `n ≥ M S` (the geometric threshold), `e n` agrees with the pullback of
  `T S n` (extended by `+∞` outside `K_n × K_n`) on the open square of radius `R`, outside an
  event of probability at most `δ`.
Then `e n → (a·)^* T∞` in probability. -/
theorem subseqLSC_expanding {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {U : ℕ → Set ℂ} {ψ : ℕ → ℂ → ℂ} {a : ℂ}
    (hopen : ∀ n, IsOpen (U n)) (hzeroU : ∀ n, (0 : ℂ) ∈ U n)
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, K ⊆ U n)
    (hd : ∀ n, DifferentiableOn ℂ (ψ n) (U n)) (hinj : ∀ n, InjOn (ψ n) (U n))
    (hzero : ∀ n, ψ n 0 = 0) (ha0 : a ≠ 0) (ha : Tendsto (fun n => deriv (ψ n) 0) atTop (𝓝 a))
    {R : ℕ → ℝ} (hR : Tendsto R atTop atTop)
    (T : ℕ → ℕ → Ω → LSCFun) (TL : ℕ → Ω → LSCFun) (Tinf : Ω → LSCFun)
    (hTm : ∀ S n, AEStronglyMeasurable (T S n) P) (hTLm : ∀ S, AEStronglyMeasurable (TL S) P)
    (hfix : ∀ S, SubseqLSC P (fun n ω => (T S n ω).1) (fun ω => (TL S ω).1))
    (hlimS : ∀ᵐ ω ∂P, LSCTendsto (fun S => (TL S ω).1) (Tinf ω).1)
    (e : ℕ → Ω → ℂ × ℂ → EReal) (M : ℕ → ℕ)
    (hbar : ∀ ρ : ℝ, ∀ δ : ℝ, 0 < δ → ∃ S₀ N : ℕ, ∀ S n, S₀ ≤ S → N ≤ n → M S ≤ n →
      P {ω | ¬ ∀ p : ℂ × ℂ, ‖p.1‖ < ρ → ‖p.2‖ < ρ →
        e n ω p = extendTop (closedBall 0 (R n)) (fun q => (T S n ω).1 (ψ n q.1, ψ n q.2)) p} ≤
        ENNReal.ofReal δ) :
    SubseqLSC P e (fun ω q => (Tinf ω).1 (a * q.1, a * q.2)) := by
  obtain ⟨d, hdm⟩ := SupercriticalLQGUniqueness.B2.LscTop.exists_compatible_metric
  letI : MetricSpace LSCFun := d
  -- fixed confinement and the limit `S → ∞`, in measure
  have h1 : ∀ S, @TendstoInMeasure _ _ _ d.toEDist _ P (T S) atTop (TL S) := fun S =>
    (subseqLSC_iff_tendstoInMeasure d.toPseudoEMetricSpace hdm (hTm S)).1 (hfix S)
  have h2 : @TendstoInMeasure _ _ _ d.toEDist _ P TL atTop Tinf := by
    have hf : ∀ S, @AEStronglyMeasurable _ _ d.toUniformSpace.toTopologicalSpace _ _ (TL S) P := by
      intro S
      have h := hTLm S
      rw [← hdm] at h
      exact h
    refine tendstoInMeasure_of_tendsto_ae hf ?_
    filter_upwards [hlimS] with ω hω
    have : Tendsto (fun S => TL S ω) atTop (@nhds _ LSCFun.instTopologicalSpace (Tinf ω)) :=
      SupercriticalLQGUniqueness.LSCFun.tendsto_iff_lscTendsto.2 hω
    rwa [← hdm] at this
  obtain ⟨s, hs, hsM, hdiag⟩ := tendstoInMeasure_diagonal T TL Tinf h1 h2 M
  -- pulled-back diagonal metrics converge in probability
  set G : ℕ → Ω → ℂ × ℂ → EReal := fun n ω =>
    extendTop (closedBall 0 (R n)) (fun q => (T (s n) n ω).1 (ψ n q.1, ψ n q.2)) with hGdef
  have hG : SubseqLSC P G (fun ω q => (Tinf ω).1 (a * q.1, a * q.2)) := by
    intro ns hns
    have hsub : @TendstoInMeasure _ _ _ d.toEDist _ P (fun k => T (s (ns k)) (ns k)) atTop Tinf :=
      fun ε hε => (hdiag ε hε).comp hns.tendsto_atTop
    obtain ⟨ms, hms, hae⟩ := hsub.exists_seq_tendsto_ae
    refine ⟨ms, hms, ?_⟩
    filter_upwards [hae] with ω hω
    have hω' : Tendsto (fun k => T (s (ns (ms k))) (ns (ms k)) ω) atTop
        (@nhds _ LSCFun.instTopologicalSpace (Tinf ω)) := by rw [← hdm]; exact hω
    have hlsc := SupercriticalLQGUniqueness.LSCFun.tendsto_iff_lscTendsto.1 hω'
    have hsub' : StrictMono (fun k => ns (ms k)) := hns.comp hms
    exact lscTendsto_pullback_univalent (U := fun k => U (ns (ms k)))
      (ψ := fun k => ψ (ns (ms k))) (fun k => hopen _) (fun k => hzeroU _)
      (fun K hK => hsub'.tendsto_atTop.eventually (hexhaust K hK)) (fun k => hd _)
      (fun k => hinj _) (fun k => hzero _) ha0 (ha.comp hsub'.tendsto_atTop)
      (hR.comp hsub'.tendsto_atTop) hlsc
  -- local agreement of `e n` with the diagonal metrics
  refine SubseqLSC.of_local_agreement hG fun ρ => ?_
  refine ENNReal.tendsto_nhds_zero.2 fun δ hδ => ?_
  rcases eq_or_ne δ ⊤ with hδt | hδt
  · exact Eventually.of_forall fun _ => hδt ▸ le_top
  obtain ⟨S₀, N, hSN⟩ := hbar ρ δ.toReal (ENNReal.toReal_pos hδ.ne' hδt)
  filter_upwards [hs.eventually_ge_atTop S₀, eventually_ge_atTop N, hsM] with n hn1 hn2 hn3
  have := hSN (s n) n hn1 hn2 hn3
  rwa [ENNReal.ofReal_toReal hδt] at this

end SupercriticalConformalCovariance.Tangent
