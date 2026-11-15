/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactMartFormula
import InteractingSLE.Spec.Sec7.Lemma71EPrefix

/-!
# The image word of the contact step, part 5: the prefix events of a family of killed arcs are measurable

Packet PROVE-WW-B17, step B1 of PROVE-WW-B15's plan. PROVE-LEMMA71E's `measurableSet_prefixEvent` (for Lemma 7.1's
global segment curves) adapted to killed arcs: for a family of killed arcs `γ ω` on `P ω` whose rational
pre-killing events `{q ∈ P ω}`, capacity clocks on them and positions are measurable,

* `kprefix_nonempty_iff`: before the terminal capacity, the prefix up to capacity time `r` meets a closed set `Q`
  iff for every `j` some rational time `q ∈ P` has `σ(q) < r + 1/(j+1)` and `dist(γ q, Q) < 1/(j+1)`;
* `setOf_lt_kLife_eq`: `{r < kLife} = ⋃_{q ∈ ℚ} {q ∈ P, r < σ(q)}`;
* **`measurableSet_lt_kLife`**, **`measurableSet_kPrefix`**: the events `{r < kLife}` and
  `{r < kLife, Q_{n,k} ∩ γ([0, σ⁻¹ r]) ≠ ∅}` are measurable;
* **`measurable_indicator_kW_of_base`**: hence the killed driver at a fixed capacity time is measurable on
  `E ∩ {s < kLife}` (`measurable_indicator_kW`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap)
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

open Sec7.Lemma71C Sec7.Lemma71E Restart ImgWord

variable {g : ℝ → ℂ} {P : Set ℝ}

/-- **The prefix meets a closed set, through rational times** (before the terminal capacity). -/
theorem kprefix_nonempty_iff (hg : IsKilledArc g P) {r : ℝ≥0} (hr : (r : WithTop ℝ≥0) < kLife g P)
    {Q : Set ℂ} (hQ : IsClosed Q) (hQne : Q.Nonempty) :
    (Q ∩ g '' Icc 0 (kInv g P r)).Nonempty ↔
      ∀ j : ℕ, ∃ q : ℚ, (q : ℝ) ∈ P ∧ capClock g q < r + 1 / ((j : ℝ) + 1) ∧
        infDist (g q) Q < 1 / ((j : ℝ) + 1) := by
  obtain ⟨hu0, hur⟩ := hg.kInv_spec hr
  have hle_iff : ∀ t ∈ P, (t ≤ kInv g P r ↔ capClock g t ≤ r) := fun t ht => by
    have := (hg.strictMonoOn_capClock.le_iff_le ht hu0).symm
    rwa [hur] at this
  constructor
  · rintro ⟨z, hzQ, t, ht, rfl⟩ j
    have htP : t ∈ P := hg.icc _ hu0 ht
    have hj : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    have hcc := hg.continuousOn_capClock t htP
    have hgc := hg.cont t htP
    have h1 : ∀ᶠ s in 𝓝[P] t, capClock g s < r + 1 / ((j : ℝ) + 1) := by
      have := (hle_iff t htP).1 ht.2
      exact hcc.eventually (gt_mem_nhds (by linarith))
    have h2 : ∀ᶠ s in 𝓝[P] t, dist (g s) (g t) < 1 / ((j : ℝ) + 1) :=
      hgc.eventually (ball_mem_nhds _ hj)
    obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhdsWithin_iff.1 (h1.and h2)
    obtain ⟨S', hS', htS'⟩ := hg.exists_gt t htP
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t < min (t + δ) S' by
      exact lt_min (by linarith) htS')
    have hqP : (q : ℝ) ∈ P := hg.icc S' hS' ⟨(hg.nonneg t htP).trans hq1.le, hq2.le.trans (min_le_right _ _)⟩
    have hqI : (q : ℝ) ∈ ball t δ ∩ P := by
      refine ⟨?_, hqP⟩
      rw [mem_ball, Real.dist_eq, abs_lt]
      have := min_le_left (t + δ) S'
      constructor <;> linarith
    obtain ⟨hq3, hq4⟩ := hδs hqI
    exact ⟨q, hqP, hq3, lt_of_le_of_lt (infDist_le_dist_of_mem hzQ) hq4⟩
  · intro h
    choose q hqP hqc hqd using h
    obtain ⟨S, hS, hrS⟩ := lt_kLife_iff.1 hr
    obtain ⟨j₀, hj₀⟩ := exists_nat_one_div_lt (show 0 < capClock g S - r by linarith)
    have hS0 : (0 : ℝ) ≤ S := hg.nonneg S hS
    have hqS : ∀ j, j₀ ≤ j → ((q j : ℚ) : ℝ) ∈ Icc (0 : ℝ) S := by
      intro j hj
      refine ⟨hg.nonneg _ (hqP j), ?_⟩
      by_contra hlt
      rw [not_le] at hlt
      have h1 := hg.strictMonoOn_capClock hS (hqP j) hlt
      have h2 : 1 / ((j : ℝ) + 1) ≤ 1 / ((j₀ : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hj 1)
      linarith [hqc j]
    obtain ⟨t, ht, φ, hφ, hlim⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := S)).tendsto_subseq
      (x := fun i => ((q (i + j₀) : ℚ) : ℝ)) fun i => hqS _ (Nat.le_add_left _ _)
    have htP : t ∈ P := hg.icc S hS ht
    have hφmono : Tendsto (fun i => φ i + j₀) atTop atTop :=
      tendsto_atTop_mono (fun i => Nat.le_add_right _ _) hφ.tendsto_atTop
    have hεlim : Tendsto (fun i => 1 / (((φ i + j₀ : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφmono
    have hlim' : Tendsto (fun i => ((q (φ i + j₀) : ℚ) : ℝ)) atTop (𝓝[P] t) :=
      tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun i => hqP _⟩
    have hct : capClock g t ≤ r := by
      have hc := (hg.continuousOn_capClock t htP).tendsto.comp hlim'
      refine le_of_tendsto_of_tendsto' hc (by simpa using (tendsto_const_nhds (x := (r : ℝ))).add hεlim)
        fun i => (hqc _).le
    have hgt : g t ∈ Q := by
      have hd := ((continuous_infDist_pt Q).tendsto (g t)).comp ((hg.cont t htP).tendsto.comp hlim')
      have h0 : infDist (g t) Q = 0 :=
        le_antisymm (le_of_tendsto_of_tendsto' hd hεlim fun i => (hqd _).le) infDist_nonneg
      exact (hQ.mem_iff_infDist_zero hQne).2 h0
    exact ⟨g t, hgt, t, ⟨ht.1, (hle_iff t htP).2 hct⟩, rfl⟩

/-- `{r < kLife}` through rational times in `P`. -/
theorem IsKilledArc.lt_kLife_iff_rat (hg : IsKilledArc g P) (r : ℝ≥0) :
    (r : WithTop ℝ≥0) < kLife g P ↔ ∃ q : ℚ, (q : ℝ) ∈ P ∧ (r : ℝ) < capClock g q := by
  constructor
  · intro h
    obtain ⟨S, hS, hrS⟩ := lt_kLife_iff.1 h
    have hS0 : 0 < S := by
      refine lt_of_le_of_ne (hg.nonneg S hS) fun he => ?_
      rw [← he, hg.capClock_zero] at hrS
      exact absurd hrS (not_lt.2 r.coe_nonneg)
    have hcc : ContinuousWithinAt (capClock g) (Icc 0 S) S :=
      (hg.continuousOn_capClock.mono (hg.icc S hS)) S ⟨hS0.le, le_rfl⟩
    have hev : ∀ᶠ u in 𝓝[Icc 0 S] S, (r : ℝ) < capClock g u := hcc.eventually (lt_mem_nhds hrS)
    obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhdsWithin_iff.1 hev
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max 0 (S - δ) < S from max_lt hS0 (by linarith))
    have hqI : (q : ℝ) ∈ Icc 0 S := ⟨(le_max_left _ _).trans hq1.le, hq2.le⟩
    refine ⟨q, hg.icc S hS hqI, hδs ⟨?_, hqI⟩⟩
    rw [mem_ball, Real.dist_eq, abs_lt]
    have := le_max_right 0 (S - δ)
    constructor <;> linarith
  · rintro ⟨q, hq, hrq⟩
    exact lt_kLife_iff.2 ⟨q, hq, hrq⟩

/-! ### Families of killed arcs -/

section Family

variable {Ω : Type*} [MeasurableSpace Ω] {γ : Ω → ℝ → ℂ} {P : Ω → Set ℝ}

/-- **`{r < kLife}` is measurable** for a family of killed arcs with measurable rational pre-killing events and
clocks. -/
theorem measurableSet_lt_kLife (hγ : ∀ ω, IsKilledArc (γ ω) (P ω))
    (hP : ∀ q : ℚ, MeasurableSet {ω | (q : ℝ) ∈ P ω})
    (hc : ∀ q : ℚ, Measurable ({ω | (q : ℝ) ∈ P ω}.indicator fun ω => capClock (γ ω) q)) (r : ℝ≥0) :
    MeasurableSet {ω | (r : WithTop ℝ≥0) < kLife (γ ω) (P ω)} := by
  have heq : {ω | (r : WithTop ℝ≥0) < kLife (γ ω) (P ω)} =
      ⋃ q : ℚ, {ω | (q : ℝ) ∈ P ω} ∩ {ω | (r : ℝ) <
        ({ω | (q : ℝ) ∈ P ω}.indicator fun ω => capClock (γ ω) q) ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    rw [(hγ ω).lt_kLife_iff_rat r]
    refine exists_congr fun q => and_congr_right fun hq => ?_
    rw [indicator_of_mem (show ω ∈ {ω | (q : ℝ) ∈ P ω} from hq)]
  rw [heq]
  exact MeasurableSet.iUnion fun q => (hP q).inter (measurableSet_lt measurable_const (hc q))

/-- **The killed prefix events are measurable.** -/
theorem measurableSet_kPrefix (hγ : ∀ ω, IsKilledArc (γ ω) (P ω))
    (hP : ∀ q : ℚ, MeasurableSet {ω | (q : ℝ) ∈ P ω})
    (hc : ∀ q : ℚ, Measurable ({ω | (q : ℝ) ∈ P ω}.indicator fun ω => capClock (γ ω) q))
    (hm : ∀ q : ℚ, Measurable fun ω => γ ω q) (r : ℝ≥0) (n : ℕ) (k : ℤ × ℤ) :
    MeasurableSet {ω | (r : WithTop ℝ≥0) < kLife (γ ω) (P ω) ∧
      (dyadicSquare n k ∩ kPre (γ ω) (P ω) r).Nonempty} := by
  have heq : {ω | (r : WithTop ℝ≥0) < kLife (γ ω) (P ω) ∧ (dyadicSquare n k ∩ kPre (γ ω) (P ω) r).Nonempty} =
      {ω | (r : WithTop ℝ≥0) < kLife (γ ω) (P ω)} ∩
        ⋂ j : ℕ, ⋃ q : ℚ, {ω | (q : ℝ) ∈ P ω} ∩
          {ω | ({ω | (q : ℝ) ∈ P ω}.indicator fun ω => capClock (γ ω) q) ω < r + 1 / ((j : ℝ) + 1)} ∩
          {ω | infDist (γ ω q) (dyadicSquare n k) < 1 / ((j : ℝ) + 1)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_iUnion]
    refine and_congr_right fun hr => ?_
    have e : kPre (γ ω) (P ω) r = γ ω '' Icc 0 (kInv (γ ω) (P ω) r) := by
      rw [kPre, max_eq_left r.coe_nonneg]
    rw [e, kprefix_nonempty_iff (hγ ω) hr (isClosed_dyadicSquare n k) (nonempty_dyadicSquare n k)]
    refine forall_congr' fun j => exists_congr fun q => ?_
    constructor
    · rintro ⟨hq, h1, h2⟩
      refine ⟨⟨hq, ?_⟩, h2⟩
      rw [indicator_of_mem (show ω ∈ {ω | (q : ℝ) ∈ P ω} from hq)]
      exact h1
    · rintro ⟨⟨hq, h1⟩, h2⟩
      rw [indicator_of_mem (show ω ∈ {ω | (q : ℝ) ∈ P ω} from hq)] at h1
      exact ⟨hq, h1, h2⟩
  rw [heq]
  refine (measurableSet_lt_kLife hγ hP hc r).inter (MeasurableSet.iInter fun j => MeasurableSet.iUnion fun q => ?_)
  exact ((hP q).inter (measurableSet_lt (hc q) measurable_const)).inter
    (measurableSet_lt ((continuous_infDist_pt _).measurable.comp (hm q)) measurable_const)

/-- **The killed driver at a fixed capacity time is measurable** on `E ∩ {s < kLife}` for a family of killed arcs with
measurable rational pre-killing events, clocks and positions. -/
theorem measurable_indicator_kW_of_base (hγ : ∀ ω, IsKilledArc (γ ω) (P ω))
    (hP : ∀ q : ℚ, MeasurableSet {ω | (q : ℝ) ∈ P ω})
    (hc : ∀ q : ℚ, Measurable ({ω | (q : ℝ) ∈ P ω}.indicator fun ω => capClock (γ ω) q))
    (hm : ∀ q : ℚ, Measurable fun ω => γ ω q) (s : ℝ≥0) :
    Measurable ({ω | (s : WithTop ℝ≥0) < kLife (γ ω) (P ω)}.indicator fun ω => kW (γ ω) (P ω) s) := by
  refine measurable_indicator_kW hγ (measurableSet_lt_kLife hγ hP hc s) (fun ω hω => hω) fun r hr0 hrs n k => ?_
  have heq : {ω | (s : WithTop ℝ≥0) < kLife (γ ω) (P ω)} ∩
      {ω | (dyadicSquare n k ∩ kPre (γ ω) (P ω) r).Nonempty} =
      {ω | (s : WithTop ℝ≥0) < kLife (γ ω) (P ω)} ∩ {ω | ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) <
        kLife (γ ω) (P ω) ∧ (dyadicSquare n k ∩ kPre (γ ω) (P ω) (r.toNNReal : ℝ≥0)).Nonempty} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, Real.coe_toNNReal _ hr0]
    have hle : r.toNNReal ≤ s := by rw [Real.toNNReal_le_iff_le_coe]; exact hrs
    exact and_congr_right fun hs => ⟨fun h => ⟨lt_of_le_of_lt (WithTop.coe_le_coe.2 hle) hs, h⟩, fun h => h.2⟩
  rw [heq]
  exact (measurableSet_lt_kLife hγ hP hc s).inter (measurableSet_kPrefix hγ hP hc hm _ n k)

end Family

end InteractingSLE.WangWu
