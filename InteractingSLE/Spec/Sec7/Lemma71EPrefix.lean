/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71CMeas
import InteractingSLE.Spec.Restart.ClockMeasCap

/-!
# The mapped prefixes of a random segment curve are measurable; the prefix filtration

Packet PROVE-LEMMA71E, item (3), second half (PROVE-LEMMA71D's "What remains" C: "`IsPrefixAdapted` then follows from
measurability of `ψ` and of the segment clock"). For a random curve `γ ω` with the geometric clause `IsSegCurve` for
every `ω` and measurable positions `ω ↦ γ ω t`:

* the capacity clock `ω ↦ capClock (γ ω) u = hcap(fill γ_ω([0, u]))/2` is measurable (PROVE-RESTART-CPL5's
  `measurable_hcapHit_image`, `hcapHit_image_eq`);
* the **prefix events** `{r < T_ω, Q ∩ γ_ω([0, capInv r]) ≠ ∅}` (`Q` a closed dyadic square, `T` the terminal capacity
  time) are measurable (`measurableSet_prefixEvent`): on `{r < T}` the prefix meets `Q` iff for every `j` some rational
  time `q ≥ 0` has `capClock q < r + 1/(j+1)` and `dist(γ q, Q) < 1/(j+1)` (sequential compactness below a clock value
  exceeding `r`; continuity and strict monotonicity of the clock);
* hence the **prefix filtration** `prefixFiltration 𝓐₀ γ` (`𝓐₀` together with the prefix events up to capacity time
  `r`) is a filtration, the curve is prefix-adapted to it (`isPrefixAdapted_prefixFiltration`), and it extends `𝓐₀`
  at time `0`; `prefixFiltrationOf` is the same filtration written without side conditions (intersected with `mΩ`),
  for use inside statements (`isPrefixAdapted_prefixFiltrationOf`, `le_prefixFiltrationOf`).

This is the filtration of Lemma 7.1's proof, "retaining the complete outer curves" (`𝓐₀`) and the mapped middle prefix.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma71E

open Lemma71C Restart

variable {Ω : Type*}

/-- The prefix event: before the terminal capacity time, the prefix up to capacity time `r` meets the closed dyadic
square `Q_{n,k}`. -/
def prefixEvent (γ : Ω → ℝ → ℂ) (r : ℝ≥0) (n : ℕ) (k : ℤ × ℤ) : Set Ω :=
  {ω | (r : ℝ≥0∞) < capLife (γ ω) ∧ (dyadicSquare n k ∩ γ ω '' Icc 0 (capInv (γ ω) r)).Nonempty}

theorem image_Icc_real_eq {g : ℝ → ℂ} {u : ℝ} (hu : 0 ≤ u) :
    g '' Icc 0 u = (fun s : ℝ≥0 => g s) '' Icc 0 u.toNNReal := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t.toNNReal, ⟨zero_le, Real.toNNReal_le_toNNReal ht.2⟩, ?_⟩
    simp [Real.coe_toNNReal _ ht.1]
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s, ⟨s.2, ?_⟩, rfl⟩
    have := hs.2
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu] at this
    exact this

variable [MeasurableSpace Ω] {γ : Ω → ℝ → ℂ}

/-- **The capacity clock of a random segment curve is measurable.** -/
theorem measurable_capClock (hγ : ∀ ω, IsSegCurve (γ ω)) (hm : ∀ t, 0 ≤ t → Measurable fun ω => γ ω t) {u : ℝ}
    (hu : 0 ≤ u) : Measurable fun ω => capClock (γ ω) u := by
  set Γ : Ω → ℝ≥0 → ℂ := fun ω s => γ ω s with hΓ
  have hc : ∀ ω, Continuous (Γ ω) := fun ω =>
    (hγ ω).1.comp_continuous NNReal.continuous_coe fun s => s.2
  have hmeas := measurable_hcapHit_image hc (fun t => hm t t.2) u.toNNReal
  have heq : (fun ω => capClock (γ ω) u) =
      fun ω => (WholeField.hcapHit (Γ ω '' Icc 0 u.toNNReal)).toReal / 2 := by
    funext ω
    have h0 : (Γ ω 0).im ≤ 0 := by
      show (γ ω ((0 : ℝ≥0) : ℝ)).im ≤ 0
      rw [NNReal.coe_zero, (hγ ω).2.2.2.1, Complex.zero_im]
    rw [hcapHit_image_eq (hc ω).continuousOn h0, capClock, image_Icc_real_eq hu]
    have hnn : 0 ≤ ConformalImage.hcapSet (fillH (Γ ω '' Icc 0 u.toNNReal)) := by
      have := (hγ ω).capClock_nonneg hu
      rw [capClock, image_Icc_real_eq hu] at this
      linarith
    rw [ENNReal.toReal_ofReal hnn]
  rw [heq]
  exact (ENNReal.measurable_toReal.comp hmeas).div_const _

omit [MeasurableSpace Ω] in
/-- `{r < T}` through the clock at integer times. -/
theorem setOf_lt_capLife_eq (hγ : ∀ ω, IsSegCurve (γ ω)) (r : ℝ≥0) :
    {ω | (r : ℝ≥0∞) < capLife (γ ω)} = ⋃ N : ℕ, {ω | (r : ℝ) < capClock (γ ω) N} := by
  ext ω
  simp only [mem_ofPred_eq, mem_iUnion]
  constructor
  · intro h
    exact exists_lt_capClock_of_lt_capLife (by rwa [ENNReal.ofReal_coe_nnreal])
  · rintro ⟨N, hN⟩
    have h1 := (hγ ω).ofReal_capClock_lt (show (0 : ℝ) ≤ N by positivity)
    rw [← ENNReal.ofReal_coe_nnreal]
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hN.le) h1

/-- **The prefix meets a closed set, through rational times** (on `{r < T}`). -/
theorem prefix_nonempty_iff {g : ℝ → ℂ} (hg : IsSegCurve g) {r : ℝ≥0} (hr : (r : ℝ≥0∞) < capLife g)
    {Q : Set ℂ} (hQ : IsClosed Q) (hQne : Q.Nonempty) :
    (Q ∩ g '' Icc 0 (capInv g r)).Nonempty ↔
      ∀ j : ℕ, ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ capClock g q < r + 1 / ((j : ℝ) + 1) ∧
        infDist (g q) Q < 1 / ((j : ℝ) + 1) := by
  have hr' : ENNReal.ofReal (r : ℝ) < capLife g := by rwa [ENNReal.ofReal_coe_nnreal]
  obtain ⟨hu0, hur⟩ := hg.capInv_spec (NNReal.coe_nonneg r) hr'
  have hle_iff : ∀ t, 0 ≤ t → (t ≤ capInv g r ↔ capClock g t ≤ r) := fun t ht => by
    have := (hg.strictMonoOn_capClock.le_iff_le ht hu0).symm
    rwa [hur] at this
  constructor
  · rintro ⟨z, hzQ, t, ht, rfl⟩ j
    have hj : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    -- continuity of the clock and of the curve at `t` within `[0, ∞)`
    have hcc := hg.continuousOn_capClock t ht.1
    have hgc := hg.1 t ht.1
    have h1 : ∀ᶠ s in 𝓝[Ici 0] t, capClock g s < r + 1 / ((j : ℝ) + 1) := by
      have := (hle_iff t ht.1).1 ht.2
      exact hcc.eventually (gt_mem_nhds (by linarith))
    have h2 : ∀ᶠ s in 𝓝[Ici 0] t, dist (g s) (g t) < 1 / ((j : ℝ) + 1) :=
      hgc.eventually (ball_mem_nhds _ hj)
    obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhdsWithin_iff.1 (h1.and h2)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t < t + δ by linarith)
    have hqI : (q : ℝ) ∈ ball t δ ∩ Ici 0 := by
      refine ⟨?_, le_of_lt (lt_of_le_of_lt ht.1 hq1)⟩
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    obtain ⟨hq3, hq4⟩ := hδs hqI
    refine ⟨q, hqI.2, hq3, lt_of_le_of_lt (infDist_le_dist_of_mem hzQ) hq4⟩
  · intro h
    choose q hq0 hqc hqd using h
    obtain ⟨N, hN⟩ := exists_lt_capClock_of_lt_capLife hr'
    obtain ⟨j₀, hj₀⟩ := exists_nat_one_div_lt (show 0 < capClock g N - r by linarith)
    have hN0 : (0 : ℝ) ≤ N := by positivity
    -- late rational times lie in `[0, N]`
    have hqN : ∀ j, j₀ ≤ j → ((q j : ℚ) : ℝ) ∈ Icc (0 : ℝ) N := by
      intro j hj
      refine ⟨hq0 j, ?_⟩
      by_contra hlt
      rw [not_le] at hlt
      have h1 := hg.strictMonoOn_capClock hN0 (hq0 j) hlt
      have h2 : 1 / ((j : ℝ) + 1) ≤ 1 / ((j₀ : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hj 1)
      linarith [hqc j]
    obtain ⟨t, ht, φ, hφ, hlim⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := N)).tendsto_subseq
      (x := fun i => ((q (i + j₀) : ℚ) : ℝ)) fun i => hqN _ (Nat.le_add_left _ _)
    have hφmono : Tendsto (fun i => φ i + j₀) atTop atTop :=
      tendsto_atTop_mono (fun i => Nat.le_add_right _ _) hφ.tendsto_atTop
    have hεlim : Tendsto (fun i => 1 / (((φ i + j₀ : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφmono
    have hlim' : Tendsto (fun i => ((q (φ i + j₀) : ℚ) : ℝ)) atTop (𝓝[Ici 0] t) :=
      tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun i => hq0 _⟩
    -- the clock at `t` is at most `r`
    have hct : capClock g t ≤ r := by
      have hc := (hg.continuousOn_capClock t ht.1).tendsto.comp hlim'
      refine le_of_tendsto_of_tendsto' hc (by simpa using (tendsto_const_nhds (x := (r : ℝ))).add hεlim)
        fun i => (hqc _).le
    -- the curve at `t` lies in `Q`
    have hgt : g t ∈ Q := by
      have hd := ((continuous_infDist_pt Q).tendsto (g t)).comp ((hg.1 t ht.1).tendsto.comp hlim')
      have h0 : infDist (g t) Q = 0 :=
        le_antisymm (le_of_tendsto_of_tendsto' hd hεlim fun i => (hqd _).le) infDist_nonneg
      exact (hQ.mem_iff_infDist_zero hQne).2 h0
    exact ⟨g t, hgt, t, ⟨ht.1, (hle_iff t ht.1).2 hct⟩, rfl⟩

omit [MeasurableSpace Ω] in
theorem nonempty_dyadicSquare (n : ℕ) (k : ℤ × ℤ) : (dyadicSquare n k).Nonempty := by
  refine ⟨((k.1 : ℝ) / 2 ^ n : ℝ) + ((k.2 : ℝ) / 2 ^ n : ℝ) * Complex.I, ?_⟩
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  simp only [dyadicSquare, mem_ofPred_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im, Complex.mul_im,
    zero_add]
  field_simp
  refine ⟨le_refl _, ?_, le_refl _, ?_⟩ <;> linarith

/-- **The prefix events of a random segment curve are measurable.** -/
theorem measurableSet_prefixEvent (hγ : ∀ ω, IsSegCurve (γ ω)) (hm : ∀ t, 0 ≤ t → Measurable fun ω => γ ω t)
    (r : ℝ≥0) (n : ℕ) (k : ℤ × ℤ) : MeasurableSet (prefixEvent γ r n k) := by
  have heq : prefixEvent γ r n k = {ω | (r : ℝ≥0∞) < capLife (γ ω)} ∩
      ⋂ j : ℕ, ⋃ q : ℚ, {ω | 0 ≤ (q : ℝ) ∧ capClock (γ ω) q < r + 1 / ((j : ℝ) + 1) ∧
        infDist (γ ω q) (dyadicSquare n k) < 1 / ((j : ℝ) + 1)} := by
    ext ω
    simp only [prefixEvent, mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_iUnion]
    constructor
    · rintro ⟨hr, hne⟩
      exact ⟨hr, (prefix_nonempty_iff (hγ ω) hr (isClosed_dyadicSquare n k) (nonempty_dyadicSquare n k)).1 hne⟩
    · rintro ⟨hr, h⟩
      exact ⟨hr, (prefix_nonempty_iff (hγ ω) hr (isClosed_dyadicSquare n k) (nonempty_dyadicSquare n k)).2 h⟩
  rw [heq, setOf_lt_capLife_eq hγ]
  refine (MeasurableSet.iUnion fun N => measurableSet_lt measurable_const
    (measurable_capClock hγ hm (by positivity))).inter (MeasurableSet.iInter fun j => MeasurableSet.iUnion fun q => ?_)
  by_cases hq : 0 ≤ (q : ℝ)
  · simp only [hq, true_and]
    exact (measurableSet_lt (measurable_capClock hγ hm hq) measurable_const).inter
      (measurableSet_lt ((continuous_infDist_pt _).measurable.comp (hm q hq)) measurable_const)
  · simp [hq]

end InteractingSLE.Sec7.Lemma71E

/-! ### The prefix filtration -/

namespace InteractingSLE.Sec7.Lemma71E

open Lemma71C Restart

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The prefix filtration**: the σ-algebra `𝓐₀` together with the prefix events up to capacity time `r`. -/
def prefixFiltration (𝓐₀ : MeasurableSpace Ω) (h₀ : 𝓐₀ ≤ mΩ) (γ : Ω → ℝ → ℂ)
    (hpm : ∀ r n k, MeasurableSet[mΩ] (prefixEvent γ r n k)) : Filtration ℝ≥0 mΩ where
  seq r := 𝓐₀ ⊔ MeasurableSpace.generateFrom {s | ∃ r' : ℝ≥0, r' ≤ r ∧ ∃ n k, s = prefixEvent γ r' n k}
  mono' r s hrs := by
    refine sup_le_sup_left (MeasurableSpace.generateFrom_mono ?_) _
    rintro t ⟨r', hr', n, k, ht⟩
    exact ⟨r', hr'.trans hrs, n, k, ht⟩
  le' r := by
    refine sup_le h₀ (MeasurableSpace.generateFrom_le ?_)
    rintro t ⟨r', -, n, k, rfl⟩
    exact hpm r' n k

theorem le_prefixFiltration (𝓐₀ : MeasurableSpace Ω) (h₀ : 𝓐₀ ≤ mΩ) (γ : Ω → ℝ → ℂ)
    (hpm : ∀ r n k, MeasurableSet[mΩ] (prefixEvent γ r n k)) (r : ℝ≥0) :
    𝓐₀ ≤ prefixFiltration 𝓐₀ h₀ γ hpm r :=
  le_sup_left

/-- **The curve is prefix-adapted to its prefix filtration.** -/
theorem isPrefixAdapted_prefixFiltration (𝓐₀ : MeasurableSpace Ω) (h₀ : 𝓐₀ ≤ mΩ) (γ : Ω → ℝ → ℂ)
    (hpm : ∀ r n k, MeasurableSet[mΩ] (prefixEvent γ r n k)) :
    IsPrefixAdapted (prefixFiltration 𝓐₀ h₀ γ hpm) γ := fun r n k => by
  have hs : prefixEvent γ r n k ∈
      {s | ∃ r' : ℝ≥0, r' ≤ r ∧ ∃ n k, s = prefixEvent γ r' n k} := ⟨r, le_rfl, n, k, rfl⟩
  exact le_sup_right (a := 𝓐₀) _ (MeasurableSpace.measurableSet_generateFrom hs)

/-- **The prefix filtration without side conditions**: `(𝓐₀ ⊔ σ(prefix events up to r)) ⊓ mΩ`. When `𝓐₀ ≤ mΩ` and
the prefix events are measurable it has the same sets as `prefixFiltration`. -/
def prefixFiltrationOf (𝓐₀ : MeasurableSpace Ω) (γ : Ω → ℝ → ℂ) : Filtration ℝ≥0 mΩ where
  seq r := (𝓐₀ ⊔ MeasurableSpace.generateFrom {s | ∃ r' : ℝ≥0, r' ≤ r ∧ ∃ n k, s = prefixEvent γ r' n k}) ⊓ mΩ
  mono' r s hrs := by
    refine inf_le_inf_right _ (sup_le_sup_left (MeasurableSpace.generateFrom_mono ?_) _)
    rintro t ⟨r', hr', n, k, ht⟩
    exact ⟨r', hr'.trans hrs, n, k, ht⟩
  le' _ := inf_le_right

theorem le_prefixFiltrationOf {𝓐₀ : MeasurableSpace Ω} (h₀ : 𝓐₀ ≤ mΩ) (γ : Ω → ℝ → ℂ) (r : ℝ≥0) :
    𝓐₀ ≤ prefixFiltrationOf (mΩ := mΩ) 𝓐₀ γ r :=
  le_inf le_sup_left h₀

/-- **A curve with measurable prefix events is prefix-adapted to its prefix filtration.** -/
theorem isPrefixAdapted_prefixFiltrationOf (𝓐₀ : MeasurableSpace Ω) (γ : Ω → ℝ → ℂ)
    (hpm : ∀ r n k, MeasurableSet[mΩ] (prefixEvent γ r n k)) :
    IsPrefixAdapted (prefixFiltrationOf (mΩ := mΩ) 𝓐₀ γ) γ := fun r n k => by
  have hs : prefixEvent γ r n k ∈
      {s | ∃ r' : ℝ≥0, r' ≤ r ∧ ∃ n k, s = prefixEvent γ r' n k} := ⟨r, le_rfl, n, k, rfl⟩
  exact ⟨le_sup_right (a := 𝓐₀) _ (MeasurableSpace.measurableSet_generateFrom hs), hpm r n k⟩

end InteractingSLE.Sec7.Lemma71E
