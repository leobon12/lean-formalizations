import SLUMetricAPI
import SupercriticalLQGUniqueness.B2.LscTop.InProbability
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Lemma 3.3: deterministic and subsequence tools for epigraph convergence

Paper l. 155–161 (epigraph convergence (i)+(ii) = DG Definition 1.2, frozen `LSCTendsto`) and the
uses in the proof of Lemma 3.3 (l. 206–236):

* `lscTendsto_of_ge_of_tendsto`: functions `≥ F` converging pointwise to a lower semicontinuous
  `F` converge in the epigraph sense (the expanding confinement `d_n = D_h(·,·;K_n) ↓ D_h`);
* `lscTendsto_of_eventually_eq_local`: epigraph convergence is local: agreement on every bounded
  square, eventually, transfers it (the passage from fixed to expanding confinement, l. 224–230);
* `lscTendsto_mul_sandwich`: multiplicative errors tending to a positive finite constant (the
  smooth-average restoration and the Weyl correction, l. 214–217);
* `SubseqLSC`: convergence in probability in subsequence form, `ℕ`-indexed (the frozen
  `LSCTendstoInProbability` along a fixed sequence), with the local-agreement criterion
  `SubseqLSC.of_local_agreement` (Borel–Cantelli) and the metric bridge
  `subseqLSC_iff_tendstoInMeasure`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalConformalCovariance.Tangent

open SupercriticalLQGUniqueness (LSCTendsto LSCFun lowerSemicontinuous_iff_seq)

/-! ## Deterministic lemmas -/

/-- If `G n ≥ F` eventually, `G n → F` pointwise and `F` is lower semicontinuous, then `G n → F` in
the sense of DG Definition 1.2. -/
theorem lscTendsto_of_ge_of_tendsto {α : Type*} [TopologicalSpace α]
    [FirstCountableTopology α] {G : ℕ → α × α → EReal} {F : α × α → EReal}
    (hF : LowerSemicontinuous F) (hge : ∀ᶠ n in atTop, ∀ p, F p ≤ G n p)
    (hpt : ∀ p, Tendsto (fun n => G n p) atTop (𝓝 (F p))) : LSCTendsto G F := by
  refine ⟨fun p q hp => ?_, fun q => ⟨fun _ => q, tendsto_const_nhds, hpt q⟩⟩
  calc F q ≤ liminf (fun n => F (p n)) atTop := (lowerSemicontinuous_iff_seq.1 hF) p q hp
    _ ≤ liminf (fun n => G n (p n)) atTop :=
        liminf_le_liminf (hge.mono fun n hn => hn (p n))

/-- Pairs converging to `q` lie eventually in the open square of any radius exceeding both norms. -/
theorem eventually_norm_lt {p : ℕ → ℂ × ℂ} {q : ℂ × ℂ} (hp : Tendsto p atTop (𝓝 q)) :
    ∀ᶠ n in atTop, ‖(p n).1‖ < max ‖q.1‖ ‖q.2‖ + 1 ∧ ‖(p n).2‖ < max ‖q.1‖ ‖q.2‖ + 1 := by
  have h1 : Tendsto (fun n => ‖(p n).1‖) atTop (𝓝 ‖q.1‖) :=
    ((continuous_fst.tendsto q).comp hp).norm
  have h2 : Tendsto (fun n => ‖(p n).2‖) atTop (𝓝 ‖q.2‖) :=
    ((continuous_snd.tendsto q).comp hp).norm
  filter_upwards [h1.eventually (gt_mem_nhds (show ‖q.1‖ < max ‖q.1‖ ‖q.2‖ + 1 by
      linarith [le_max_left ‖q.1‖ ‖q.2‖])),
    h2.eventually (gt_mem_nhds (show ‖q.2‖ < max ‖q.1‖ ‖q.2‖ + 1 by
      linarith [le_max_right ‖q.1‖ ‖q.2‖]))] with n hn1 hn2
  exact ⟨hn1, hn2⟩

/-- **Locality of epigraph convergence.** If for every radius `R` the functions `F n` and `G n`
eventually agree on the open square `{‖x‖ < R, ‖y‖ < R}`, and `G n → L`, then `F n → L`. -/
theorem lscTendsto_of_eventually_eq_local {F G : ℕ → ℂ × ℂ → EReal} {L : ℂ × ℂ → EReal}
    (hEq : ∀ R : ℝ, ∀ᶠ n in atTop, ∀ p : ℂ × ℂ, ‖p.1‖ < R → ‖p.2‖ < R → F n p = G n p)
    (hG : LSCTendsto G L) : LSCTendsto F L := by
  refine ⟨fun p q hp => ?_, fun q => ?_⟩
  · have heq : (fun n => F n (p n)) =ᶠ[atTop] fun n => G n (p n) := by
      filter_upwards [hEq (max ‖q.1‖ ‖q.2‖ + 1), eventually_norm_lt hp] with n hn hpn
      exact hn _ hpn.1 hpn.2
    rw [liminf_congr heq]
    exact hG.1 p q hp
  · obtain ⟨p, hp, hGp⟩ := hG.2 q
    refine ⟨p, hp, hGp.congr' ?_⟩
    filter_upwards [hEq (max ‖q.1‖ ‖q.2‖ + 1), eventually_norm_lt hp] with n hn hpn
    exact (hn _ hpn.1 hpn.2).symm

/-- The coercion `ℝ≥0∞ → EReal` commutes with `liminf`. -/
theorem coe_liminf_ennreal (w : ℕ → ℝ≥0∞) :
    ((liminf w atTop : ℝ≥0∞) : EReal) = liminf (fun n => (w n : EReal)) atTop :=
  EReal.coe_ennreal_strictMono.monotone.map_liminf_of_continuousAt w
    continuous_coe_ennreal_ereal.continuousAt

/-- **Multiplicative sandwich around a convergent sequence.** If `G n → G` (values in `[0, ∞]`),
`a n, b n → c` with `0 < c < ∞`, and `a n * G n ≤ F n ≤ b n * G n` eventually, then
`F n → c * G`. -/
theorem lscTendsto_mul_sandwich {α : Type*} [TopologicalSpace α]
    {F G : ℕ → α × α → ℝ≥0∞} {G₀ : α × α → ℝ≥0∞}
    (hG : LSCTendsto (fun n p => (G n p : EReal)) (fun p => (G₀ p : EReal)))
    {a b : ℕ → ℝ≥0∞} {c : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    (ha : Tendsto a atTop (𝓝 c)) (hb : Tendsto b atTop (𝓝 c))
    (hbound : ∀ᶠ n in atTop, ∀ p, a n * G n p ≤ F n p ∧ F n p ≤ b n * G n p) :
    LSCTendsto (fun n p => (F n p : EReal)) (fun p => ((c * G₀ p : ℝ≥0∞) : EReal)) := by
  refine ⟨fun p q hp => ?_, fun q => ?_⟩
  · have hGq : (G₀ q : EReal) ≤ liminf (fun n => (G n (p n) : EReal)) atTop := hG.1 p q hp
    rw [← coe_liminf_ennreal] at hGq
    have hGq' : G₀ q ≤ liminf (fun n => G n (p n)) atTop :=
      EReal.coe_ennreal_le_coe_ennreal_iff.mp hGq
    have hmul : c * G₀ q ≤ liminf (fun n => a n * G n (p n)) atTop :=
      calc c * G₀ q ≤ c * liminf (fun n => G n (p n)) atTop := by gcongr
        _ = liminf a atTop * liminf (fun n => G n (p n)) atTop := by rw [ha.liminf_eq]
        _ ≤ liminf (fun n => a n * G n (p n)) atTop := ENNReal.le_liminf_mul
    have hle : c * G₀ q ≤ liminf (fun n => F n (p n)) atTop :=
      hmul.trans (liminf_le_liminf (hbound.mono fun n hn => (hn (p n)).1))
    rw [← coe_liminf_ennreal]
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr hle
  · obtain ⟨p, hp, hGp⟩ := hG.2 q
    refine ⟨p, hp, ?_⟩
    have hGp' : Tendsto (fun n => G n (p n)) atTop (𝓝 (G₀ q)) := by
      have := (EReal.continuous_toENNReal.tendsto _).comp hGp
      simpa [Function.comp_def, EReal.toENNReal_coe] using this
    have hlo : Tendsto (fun n => a n * G n (p n)) atTop (𝓝 (c * G₀ q)) :=
      ENNReal.Tendsto.mul ha (Or.inl hc0) hGp' (Or.inr hctop)
    have hhi : Tendsto (fun n => b n * G n (p n)) atTop (𝓝 (c * G₀ q)) :=
      ENNReal.Tendsto.mul hb (Or.inl hc0) hGp' (Or.inr hctop)
    have hF : Tendsto (fun n => F n (p n)) atTop (𝓝 (c * G₀ q)) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
        (hbound.mono fun n hn => (hn (p n)).1) (hbound.mono fun n hn => (hn (p n)).2)
    exact (continuous_coe_ennreal_ereal.tendsto _).comp hF

/-! ## Convergence in probability, subsequence form -/

/-- Convergence in probability in the topology of DG Definition 1.2, in subsequence form, along
`n → ∞`: every subsequence has a further subsequence along which, almost surely, `F n ω → L ω` in
the sense of `LSCTendsto` (the frozen `LSCTendstoInProbability`, for a fixed sequence). -/
def SubseqLSC {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : ℕ → Ω → ℂ × ℂ → EReal)
    (L : Ω → ℂ × ℂ → EReal) : Prop :=
  ∀ ns : ℕ → ℕ, StrictMono ns → ∃ ms : ℕ → ℕ, StrictMono ms ∧
    ∀ᵐ ω ∂P, LSCTendsto (fun k => F (ns (ms k)) ω) (L ω)

section Subseq

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Almost sure convergence implies convergence in probability. -/
theorem SubseqLSC.of_ae {F : ℕ → Ω → ℂ × ℂ → EReal} {L : Ω → ℂ × ℂ → EReal}
    (h : ∀ᵐ ω ∂P, LSCTendsto (fun n => F n ω) (L ω)) : SubseqLSC P F L := by
  intro ns hns
  refine ⟨id, strictMono_id, ?_⟩
  filter_upwards [h] with ω hω
  exact hω.comp_strictMono hns

/-- Passing to a subsequence. -/
theorem SubseqLSC.comp {F : ℕ → Ω → ℂ × ℂ → EReal} {L : Ω → ℂ × ℂ → EReal}
    (h : SubseqLSC P F L) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    SubseqLSC P (fun n => F (φ n)) L := fun ns hns => h (φ ∘ ns) (hφ.comp hns)

/-- Almost sure congruence of the sequence. -/
theorem SubseqLSC.congr_ae {F F' : ℕ → Ω → ℂ × ℂ → EReal} {L L' : Ω → ℂ × ℂ → EReal}
    (h : SubseqLSC P F L) (hF : ∀ n, F n =ᵐ[P] F' n) (hL : L =ᵐ[P] L') :
    SubseqLSC P F' L' := by
  intro ns hns
  obtain ⟨ms, hms, hae⟩ := h ns hns
  refine ⟨ms, hms, ?_⟩
  have hall : ∀ᵐ ω ∂P, ∀ n, F n ω = F' n ω := ae_all_iff.2 hF
  filter_upwards [hae, hall, hL] with ω hω hω' hωL
  simp only [← hω', ← hωL]
  exact hω

/-- A strictly increasing sequence whose `k`-th term lies in a prescribed tail `[N k, ∞)`. -/
theorem exists_strictMono_ge (N : ℕ → ℕ) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, N k ≤ φ k := by
  refine ⟨fun k => (Finset.range (k + 1)).sum N + k, ?_, fun k => ?_⟩
  · refine strictMono_nat_of_lt_succ fun k => ?_
    simp only [Finset.sum_range_succ]
    omega
  · have : N k ≤ (Finset.range (k + 1)).sum N :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (N i)) (Finset.self_mem_range_succ k)
    show N k ≤ (Finset.range (k + 1)).sum N + k
    omega

/-- **Local agreement criterion** (paper l. 224–230, "fixed-confinement convergence approximates
expanding-confinement convergence uniformly in probability on each inner disk"). If `G n → L` in
probability and, for every radius `R`, the probability that `F n` and `G n` differ somewhere on the
open square of radius `R` tends to zero, then `F n → L` in probability. No measurability is needed
(outer measure; first Borel–Cantelli lemma). -/
theorem SubseqLSC.of_local_agreement {F G : ℕ → Ω → ℂ × ℂ → EReal} {L : Ω → ℂ × ℂ → EReal}
    (hG : SubseqLSC P G L)
    (hloc : ∀ R : ℝ, Tendsto (fun n => P {ω | ¬ ∀ p : ℂ × ℂ, ‖p.1‖ < R → ‖p.2‖ < R →
      F n ω p = G n ω p}) atTop (𝓝 0)) :
    SubseqLSC P F L := by
  intro ns hns
  obtain ⟨ms₁, hms₁, hae⟩ := hG ns hns
  -- the bad events, monotone in the radius
  set bad : ℝ → ℕ → Set Ω := fun R n =>
    {ω | ¬ ∀ p : ℂ × ℂ, ‖p.1‖ < R → ‖p.2‖ < R → F n ω p = G n ω p} with hbad
  have hmono : ∀ {R R' : ℝ}, R ≤ R' → ∀ n, bad R n ⊆ bad R' n := by
    intro R R' hRR' n ω hω hall
    exact hω fun p h1 h2 => hall p (h1.trans_le hRR') (h2.trans_le hRR')
  -- choose indices along `ns ∘ ms₁` with `P (bad k) ≤ 2⁻ᵏ`
  have hev : ∀ k : ℕ, ∀ᶠ j in atTop, P (bad k (ns (ms₁ j))) ≤ (2⁻¹ : ℝ≥0∞) ^ k := by
    intro k
    have ht := (hloc k).comp ((hns.comp hms₁).tendsto_atTop)
    exact ht.eventually (ge_mem_nhds (ENNReal.pow_pos (by norm_num) k))
  choose N hN using fun k => eventually_atTop.1 (hev k)
  obtain ⟨ms₂, hms₂, hms₂N⟩ := exists_strictMono_ge N
  refine ⟨ms₁ ∘ ms₂, hms₁.comp hms₂, ?_⟩
  have hsum : ∑' k : ℕ, P (bad (k : ℝ) (ns (ms₁ (ms₂ k)))) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (tsum_geometric_lt_top.2
      (by norm_num : (2⁻¹ : ℝ≥0∞) < 1)).ne ?_
    exact ENNReal.tsum_le_tsum fun k => hN k (ms₂ k) (hms₂N k)
  have hgood : ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop, ω ∉ bad (k : ℝ) (ns (ms₁ (ms₂ k))) :=
    ae_eventually_notMem hsum
  filter_upwards [hae, hgood] with ω hω hωg
  have hG' : LSCTendsto (fun k => G (ns (ms₁ (ms₂ k))) ω) (L ω) := hω.comp_strictMono hms₂
  refine lscTendsto_of_eventually_eq_local (fun R => ?_) hG'
  obtain ⟨K, hK⟩ := exists_nat_ge R
  filter_upwards [hωg, eventually_ge_atTop K] with k hk hkK
  intro p h1 h2
  by_contra hne
  exact hk (hmono (hK.trans (Nat.cast_le.2 hkK)) _ fun hall => hne (hall p h1 h2))

end Subseq

/-! ## The metric bridge -/

/-- For `LSCFun`-valued a.e.-strongly measurable sequences and a finite measure, `SubseqLSC` is
convergence in measure for any pseudo-emetric inducing the topology of DG Definition 1.2. -/
theorem subseqLSC_iff_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (d : PseudoEMetricSpace LSCFun)
    (hd : d.toUniformSpace.toTopologicalSpace = LSCFun.instTopologicalSpace)
    {G : ℕ → Ω → LSCFun} {L : Ω → LSCFun} (hG : ∀ n, AEStronglyMeasurable (G n) P) :
    SubseqLSC P (fun n ω => (G n ω).1) (fun ω => (L ω).1) ↔
      @TendstoInMeasure _ _ _ d.toEDist _ P G atTop L := by
  have hf : ∀ n, @AEStronglyMeasurable _ _ d.toUniformSpace.toTopologicalSpace _ _ (G n) P := by
    intro n
    have h := hG n
    rw [← hd] at h
    exact h
  refine Iff.trans ?_ (@exists_seq_tendstoInMeasure_atTop_iff _ _ _ P d _ _ hf L).symm
  refine forall₂_congr fun ns _ => exists_congr fun ns' => and_congr_right fun _ => ?_
  refine Filter.eventually_congr (Eventually.of_forall fun ω => ?_)
  rw [hd]
  exact LSCFun.tendsto_iff_lscTendsto.symm

end SupercriticalConformalCovariance.Tangent
