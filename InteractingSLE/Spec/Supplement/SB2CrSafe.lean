/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.DomainMarkovAux79

/-!
# K2's (S) from deterministic physical lines under a STRICT time change

Packet PROVE-SB2-CONDFIN (round 8, D44: the root indexed by B's own time). At the root, B's piece `ℓ = relOff` enters
the relative domain at the random entrance time `τE`. The capacity clock `Qc` is `0` until `τE`. The relative
driver's filtration `𝓗'` starts at the entrance: its `0`-events contain the root event, which is not an event of
the physical filtration at time `0`. So the time change `D ∈ 𝓗'_q ⇒ D ∩ {q ≤ Qc t} ∈ 𝓖_t` of
`Aux79.hasSafeLaw_of_lineLaw` fails at `q = 0`. It holds in the STRICT form `D ∩ {q < Qc t} ∈ 𝓖_t` (the events of
`𝓗'_q` are cut by the strict first passage `inf {t | q < Qc t}`, which at `q = 0` is `τE`).

This file redoes Aux. lemma 79's discretization with the strict first passage:

* `hitTS`, `lt_Qc_iff`, `Qc_hitTS`: the strict first passage `σ = inf {t | q < Qc t}`; for a continuous
  nondecreasing clock, `q < Qc t ↔ σ < t`, and `Qc σ = q`;
* `labS = ⌊2ⁿσ⌋ + 1` (the first level-`n` dyadic time after `σ`), `tendsto_dyT_labS`;
* `linePieceS` (the pieces `{q < Qc(k/2ⁿ), Qc(j/2ⁿ) ≤ q (j < k)}`), their labels, measurability, pointwise limits;
* **`hasSafeLaw_of_lineLawS`**: (S) for `𝓗'` from the conditional laws on deterministic physical lines, needed only
  where the clock is positive (`0 < Qc t`), with the line safe events measurable only there.

The proofs follow `Aux79` line by line; the change is the strict passage.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Cr

open Restart.DomainMarkov Restart.DomainMarkov.Aux79 Restart.DomainMarkov.K2 Coupling Ito

/-! ### The strict first passage -/

section Clock

variable {Ω : Type*} (Qc : ℝ≥0 → Ω → ℝ≥0) (q : ℝ≥0)

/-- The strict first passage of the clock above `q`. -/
def hitTS (ω : Ω) : ℝ≥0 := sInf {t | q < Qc t ω}

/-- The level-`n` label of the strict passage: the first dyadic index strictly after it. -/
def labS (n : ℕ) (ω : Ω) : ℕ := ⌊(2 : ℝ≥0) ^ n * hitTS Qc q ω⌋₊ + 1

variable {Qc q}

/-- For a continuous nondecreasing clock that exceeds `q`, `q < Qc t` exactly after the strict passage. -/
theorem lt_Qc_iff {ω : Ω} (hc : Continuous fun t => Qc t ω) (hm : Monotone fun t => Qc t ω)
    (h0 : Qc 0 ω = 0) (hr : ∃ t, q < Qc t ω) {t : ℝ≥0} : q < Qc t ω ↔ hitTS Qc q ω < t := by
  have hne : {t | q < Qc t ω}.Nonempty := hr
  constructor
  · intro h
    have hle : hitTS Qc q ω ≤ t := csInf_le (OrderBot.bddBelow _) h
    refine lt_of_le_of_ne hle fun heq => ?_
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [h0] at h
      exact absurd h (not_lt.2 zero_le)
    have hopen : IsOpen {s : ℝ≥0 | q < Qc s ω} := isOpen_lt continuous_const hc
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen t h
    set s : ℝ≥0 := t - (min ε (t : ℝ) / 2).toNNReal with hs
    have hpos : 0 < min ε (t : ℝ) / 2 := by
      have : 0 < (t : ℝ) := by exact_mod_cast pos_iff_ne_zero.2 ht0
      positivity
    have hst : s < t := by
      rw [hs]
      exact tsub_lt_self (pos_iff_ne_zero.2 ht0) (Real.toNNReal_pos.2 hpos)
    have hsd : dist s t < ε := by
      rw [NNReal.dist_eq, hs, NNReal.coe_sub (Real.toNNReal_le_iff_le_coe.2 (by
        linarith [min_le_right ε (t : ℝ)])), Real.coe_toNNReal _ hpos.le]
      rw [show (t : ℝ) - min ε (t : ℝ) / 2 - t = -(min ε (t : ℝ) / 2) by ring, abs_neg, abs_of_pos hpos]
      linarith [min_le_left ε (t : ℝ)]
    have hsm : q < Qc s ω := hball hsd
    have : hitTS Qc q ω ≤ s := csInf_le (OrderBot.bddBelow _) hsm
    rw [heq] at this
    exact absurd hst (not_lt.2 this)
  · intro h
    obtain ⟨s, hs, hst⟩ := (csInf_lt_iff (OrderBot.bddBelow _) hne).1 h
    exact lt_of_lt_of_le hs (hm hst.le)

/-- At the strict passage the clock equals `q`. -/
theorem Qc_hitTS {ω : Ω} (hc : Continuous fun t => Qc t ω) (hm : Monotone fun t => Qc t ω) (h0 : Qc 0 ω = 0)
    (hr : ∃ t, q < Qc t ω) : Qc (hitTS Qc q ω) ω = q := by
  have hle : Qc (hitTS Qc q ω) ω ≤ q := not_lt.1 fun h => lt_irrefl _ ((lt_Qc_iff hc hm h0 hr).1 h)
  refine le_antisymm hle ?_
  have hev : ∀ᶠ t in 𝓝[>] (hitTS Qc q ω), q ≤ Qc t ω := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ((lt_Qc_iff hc hm h0 hr).2 ht).le
  exact ge_of_tendsto ((hc.tendsto _).mono_left nhdsWithin_le_nhds) hev

/-- The first level-`n` dyadic time strictly after `a` tends to `a`. -/
theorem tendsto_dyT_floor_succ (a : ℝ≥0) :
    Tendsto (fun n => dyT n (⌊(2 : ℝ≥0) ^ n * a⌋₊ + 1)) atTop (𝓝 a) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (tendsto_dyT_ceil a) (fun n => ?_)
    (fun n => dyT_mono n (Nat.succ_le_succ (Nat.floor_le_ceil _)))
  rw [le_dyT_iff]
  exact Nat.ceil_le.2 (by push_cast; exact (Nat.lt_floor_add_one _).le)

theorem tendsto_Qc_dyT_labS {ω : Ω} (hc : Continuous fun t => Qc t ω) (hm : Monotone fun t => Qc t ω)
    (h0 : Qc 0 ω = 0) (hr : ∃ t, q < Qc t ω) :
    Tendsto (fun n => Qc (dyT n (labS Qc q n ω)) ω) atTop (𝓝 q) := by
  have h := (hc.tendsto (hitTS Qc q ω)).comp (tendsto_dyT_floor_succ (hitTS Qc q ω))
  rwa [Qc_hitTS hc hm h0 hr] at h

theorem lt_dyT_iff {a : ℝ≥0} {n k : ℕ} : a < dyT n k ↔ ⌊(2 : ℝ≥0) ^ n * a⌋₊ < k := by
  rw [Nat.floor_lt zero_le, dyT, lt_div_iff₀ (pow_pos two_pos n), mul_comm]

theorem eventually_labS_lt_four_pow (a : ℝ≥0) : ∀ᶠ n : ℕ in atTop, ⌊(2 : ℝ≥0) ^ n * a⌋₊ + 1 < 4 ^ n := by
  filter_upwards [eventually_ceil_lt_four_pow (a + 1)] with n hn
  refine lt_of_le_of_lt ?_ hn
  have h1 : (1 : ℝ≥0) ≤ 2 ^ n := one_le_pow₀ one_le_two
  have : ((⌊(2 : ℝ≥0) ^ n * a⌋₊ + 1 : ℕ) : ℝ≥0) ≤ 2 ^ n * (a + 1) := by
    push_cast
    calc ((⌊(2 : ℝ≥0) ^ n * a⌋₊ : ℕ) : ℝ≥0) + 1 ≤ 2 ^ n * a + 1 := by gcongr; exact Nat.floor_le zero_le
      _ ≤ 2 ^ n * a + 2 ^ n := by gcongr
      _ = 2 ^ n * (a + 1) := by ring
  exact_mod_cast this.trans (Nat.le_ceil _)

/-- The `k`-th level-`n` piece of `D` along the strict passage at `q`. -/
def linePieceS (Qc : ℝ≥0 → Ω → ℝ≥0) (q : ℝ≥0) (D : Set Ω) (S : ℝ≥0 → Set Ω) (n k : ℕ) : Set Ω :=
  D ∩ {ω | q < Qc (dyT n k) ω ∧ ∀ j < k, Qc (dyT n j) ω ≤ q} ∩ S (dyT n k)

theorem labS_eq_of_mem {D : Set Ω} {S : ℝ≥0 → Set Ω} {n k : ℕ} {ω : Ω}
    (hc : Continuous fun t => Qc t ω) (hm : Monotone fun t => Qc t ω) (h0 : Qc 0 ω = 0)
    (hω : ω ∈ linePieceS Qc q D S n k) : labS Qc q n ω = k := by
  obtain ⟨⟨-, hlt, hle⟩, -⟩ := hω
  have hr : ∃ t, q < Qc t ω := ⟨_, hlt⟩
  have h1 : ⌊(2 : ℝ≥0) ^ n * hitTS Qc q ω⌋₊ < k := lt_dyT_iff.1 ((lt_Qc_iff hc hm h0 hr).1 hlt)
  unfold labS
  refine le_antisymm h1 (not_lt.1 fun hk => ?_)
  have hk' : ⌊(2 : ℝ≥0) ^ n * hitTS Qc q ω⌋₊ < k - 1 := by omega
  have h2 : q < Qc (dyT n (k - 1)) ω := (lt_Qc_iff hc hm h0 hr).2 (lt_dyT_iff.2 hk')
  exact absurd (hle (k - 1) (by omega)) (not_le.2 h2)

theorem mem_linePieceS_lab {D : Set Ω} {S : ℝ≥0 → Set Ω} {n : ℕ} {ω : Ω}
    (hc : Continuous fun t => Qc t ω) (hm : Monotone fun t => Qc t ω) (h0 : Qc 0 ω = 0)
    (hr : ∃ t, q < Qc t ω) (hD : ω ∈ D) (hS : ω ∈ S (dyT n (labS Qc q n ω))) :
    ω ∈ linePieceS Qc q D S n (labS Qc q n ω) := by
  refine ⟨⟨hD, (lt_Qc_iff hc hm h0 hr).2 (lt_dyT_iff.2 (Nat.lt_succ_self _)), fun j hj => ?_⟩, hS⟩
  refine not_lt.1 fun hlt => ?_
  have h1 := lt_dyT_iff.1 ((lt_Qc_iff hc hm h0 hr).1 hlt)
  unfold labS at hj
  omega

/-- **The pieces are events of the physical filtration at their line**, from the strict cut of `D` and the safe
events where the clock is positive. -/
theorem measurableSet_linePieceS {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ}
    (hQa : ∀ t, Measurable[𝓖 t] (Qc t)) {D : Set Ω} (hD : ∀ t, MeasurableSet[𝓖 t] (D ∩ {ω | q < Qc t ω}))
    {S : ℝ≥0 → Set Ω} (hS : ∀ t, MeasurableSet[𝓖 t] ({ω | 0 < Qc t ω} ∩ S t)) (n k : ℕ) :
    MeasurableSet[𝓖 (dyT n k)] (linePieceS Qc q D S n k) := by
  have hj : MeasurableSet[𝓖 (dyT n k)] {ω | ∀ j < k, Qc (dyT n j) ω ≤ q} := by
    have e : {ω | ∀ j < k, Qc (dyT n j) ω ≤ q} = ⋂ j : Fin k, {ω | Qc (dyT n j) ω ≤ q} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iInter]
      exact ⟨fun h j => h j j.2, fun h j hj => h ⟨j, hj⟩⟩
    rw [e]
    refine MeasurableSet.iInter fun j => ?_
    exact 𝓖.mono (dyT_mono n j.2.le) _ (measurableSet_le (hQa _) measurable_const)
  have e : linePieceS Qc q D S n k = (D ∩ {ω | q < Qc (dyT n k) ω}) ∩ {ω | ∀ j < k, Qc (dyT n j) ω ≤ q} ∩
      ({ω | 0 < Qc (dyT n k) ω} ∩ S (dyT n k)) := by
    ext ω
    simp only [linePieceS, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hD, hlt, hle⟩, hS⟩
      exact ⟨⟨⟨hD, hlt⟩, hle⟩, lt_of_le_of_lt zero_le hlt, hS⟩
    · rintro ⟨⟨⟨hD, hlt⟩, hle⟩, -, hS⟩
      exact ⟨⟨hD, hlt, hle⟩, hS⟩
  rw [e]
  exact ((hD _).inter hj).inter (hS _)

theorem linePieceS_subset (D : Set Ω) (S : ℝ≥0 → Set Ω) (n k : ℕ) : linePieceS Qc q D S n k ⊆ D :=
  fun _ hω => hω.1.1

theorem pos_of_mem_linePieceS {D : Set Ω} {S : ℝ≥0 → Set Ω} {n k : ℕ} {ω : Ω}
    (hω : ω ∈ linePieceS Qc q D S n k) : 0 < Qc (dyT n k) ω :=
  lt_of_le_of_lt zero_le hω.1.2.1

/-- **Pointwise convergence of the discretized integrands** (strict passage). -/
theorem ae_tendsto_sum_linePieceS [MeasurableSpace Ω] {P : Measure Ω} {D : Set Ω} {S : ℝ≥0 → Set Ω}
    (hc : ∀ ω, Continuous fun t => Qc t ω) (hm : ∀ ω, Monotone fun t => Qc t ω) (h0 : ∀ ω, Qc 0 ω = 0)
    (g : ℕ → ℕ → Ω → ℂ) (g' : Ω → ℂ)
    (hgood : ∀ᵐ ω ∂P, ω ∈ D → (∃ t, q < Qc t ω) ∧
      (∀ t : ℕ → ℝ≥0, Tendsto (fun n => Qc (t n) ω) atTop (𝓝 q) → ∀ᶠ n in atTop, ω ∈ S (t n)) ∧
      Tendsto (fun n => g n (labS Qc q n ω) ω) atTop (𝓝 (g' ω))) :
    ∀ᵐ ω ∂P, Tendsto (fun n => ∑ k ∈ Finset.range (4 ^ n), (linePieceS Qc q D S n k).indicator (g n k) ω) atTop
      (𝓝 (D.indicator g' ω)) := by
  filter_upwards [hgood] with ω hω
  have hlab : ∀ n k ω', ω' ∈ linePieceS Qc q D S n k → labS Qc q n ω' = k := fun n k ω' h =>
    labS_eq_of_mem (hc ω') (hm ω') (h0 ω') h
  by_cases hD : ω ∈ D
  · obtain ⟨hr, hS, hg⟩ := hω hD
    have hev : ∀ᶠ n in atTop, labS Qc q n ω ∈ Finset.range (4 ^ n) ∧
        ω ∈ linePieceS Qc q D S n (labS Qc q n ω) := by
      filter_upwards [eventually_labS_lt_four_pow (hitTS Qc q ω),
        hS _ (tendsto_Qc_dyT_labS (hc ω) (hm ω) (h0 ω) hr)] with n hn hSn
      exact ⟨Finset.mem_range.2 hn, mem_linePieceS_lab (hc ω) (hm ω) (h0 ω) hr hD hSn⟩
    rw [indicator_of_mem hD]
    refine hg.congr' (hev.mono fun n hn => ?_)
    beta_reduce
    rw [sum_indicator_eq_of_label (fun k ω' h => hlab n k ω' h) ω]
    split_ifs with hk
    · exact (indicator_of_mem hn.2 _).symm
    · exact absurd hn.1 hk
  · rw [indicator_of_notMem hD]
    refine tendsto_const_nhds.congr fun n => (Finset.sum_eq_zero fun k _ => ?_).symm
    exact indicator_of_notMem (fun h => hD (linePieceS_subset D S n k h)) _

theorem norm_sum_linePieceS_le {D : Set Ω} {S : ℝ≥0 → Set Ω} (hc : ∀ ω, Continuous fun t => Qc t ω)
    (hm : ∀ ω, Monotone fun t => Qc t ω) (h0 : ∀ ω, Qc 0 ω = 0) (g : ℕ → ℕ → Ω → ℂ) (n : ℕ) (s : Finset ℕ)
    {ω : Ω} (hb : ∀ k, ω ∈ linePieceS Qc q D S n k → ‖g n k ω‖ ≤ 1) :
    ‖∑ k ∈ s, (linePieceS Qc q D S n k).indicator (g n k) ω‖ ≤ 1 := by
  rw [sum_indicator_eq_of_label (fun k ω' h => labS_eq_of_mem (hc ω') (hm ω') (h0 ω') h) ω]
  split_ifs with hk
  · by_cases hω : ω ∈ linePieceS Qc q D S n (labS Qc q n ω)
    · rw [indicator_of_mem hω]
      exact hb _ hω
    · rw [indicator_of_notMem hω, norm_zero]
      exact zero_le_one
  · rw [norm_zero]
    exact zero_le_one

end Clock

/-! ### (S) from the line laws, strict passage -/

section Law

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {F : Set Ω} {Qc : ℝ≥0 → Ω → ℝ≥0}

/-- **(S) from the conditional laws on deterministic physical lines, under a strict time change**: as
`Aux79.hasSafeLaw_of_lineLaw`, with the `q`-events of `𝓗'` cut by `{q < Qc t}` and the line facts (the safe events'
measurability and the line laws) needed only where the clock is positive. -/
theorem hasSafeLaw_of_lineLawS [IsProbabilityMeasure P] {𝓖 𝓗' : Filtration ℝ≥0 mΩ}
    {X : Ω → DistOn upperHalfPlaneOpens} (hX : ∀ ψ : TestOn upperHalfPlaneOpens, Measurable fun ω => X ω ψ)
    (hc : ∀ ω, Continuous fun t => Qc t ω) (hm : ∀ ω, Monotone fun t => Qc t ω) (h0 : ∀ ω, Qc 0 ω = 0)
    (hQa : ∀ t, Measurable[𝓖 t] (Qc t))
    (h𝓗' : ∀ q D, MeasurableSet[𝓗' q] D → ∀ t, MeasurableSet[𝓖 t] (D ∩ {ω | q < Qc t ω}))
    (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < ζ ω → ∃ t, q ≤ Qc t ω)
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsForceReg W VL VR ζ ω)
    (hS : ∀ (ψ : TestOn upperHalfPlaneOpens) t,
      MeasurableSet[𝓖 t] ({ω | 0 < Qc t ω} ∩ lineSafe Qc W ζ (tsupport ψ) t))
    (𝒢L : ℝ≥0 → MeasurableSpace Ω) (h𝒢L : ∀ t, 𝓖 t ≤ 𝒢L t) (h𝒢Lm : ∀ t, 𝒢L t ≤ mΩ)
    (hline : ∀ (ψ : TestOn upperHalfPlaneOpens) (t : ℝ≥0), ∀ᵐ ω ∂P, ω ∈ F → 0 < Qc t ω →
      ω ∈ lineSafe Qc W ζ (tsupport ψ) t → P[fun ω => Complex.exp (Complex.I * (X ω ψ : ℂ)) | 𝒢L t] ω =
        cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 (Qc t) ω) :
    HasSafeLaw κ ρL ρR P 𝓗' F ζ W VL VR X := by
  intro ψ q D hD hDs
  set f : Ω → ℂ := fun ω => Complex.exp (Complex.I * (X ω ψ : ℂ)) with hf
  have hfm : Measurable f :=
    (by fun_prop : Measurable fun x : ℝ => Complex.exp (Complex.I * x)).comp (hX ψ)
  have hfn : ∀ ω, ‖f ω‖ ≤ 1 := fun ω => by
    simp only [hf, Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_zero, Real.exp_zero, le_refl]
  have hfi : Integrable f P := Integrable.of_bound hfm.aestronglyMeasurable 1 (Eventually.of_forall hfn)
  set u := bheProc κ ρL ρR W VL VR with hu
  set S : ℝ≥0 → Set Ω := lineSafe Qc W ζ (tsupport ψ) with hSdef
  set E : ℕ → ℕ → Set Ω := linePieceS Qc q D S with hEdef
  set g : ℕ → ℕ → Ω → ℂ := fun n k => cfAt κ W u ψ 1 (Qc (dyT n k)) with hgdef
  have hDm : MeasurableSet D := 𝓗'.le q _ hD
  have hEm : ∀ n k, MeasurableSet[𝓖 (dyT n k)] (E n k) := measurableSet_linePieceS hQa (h𝓗' q D hD) (hS ψ)
  have hEm' : ∀ n k, MeasurableSet (E n k) := fun n k => 𝓖.le _ _ (hEm n k)
  have hDF : ∀ᵐ ω ∂P, ω ∈ D → ω ∈ F ∧ IsForceReg W VL VR ζ ω ∧ ω ∈ avoidSet W ζ ψ q := by
    filter_upwards [hDs, hreg] with ω h1 h2 hωD using ⟨(h1 hωD).1, h2 (h1 hωD).1, (h1 hωD).2⟩
  have hgb : ∀ᵐ ω ∂P, ∀ n k, ω ∈ E n k → ‖g n k ω‖ ≤ 1 := by
    filter_upwards [hDF] with ω hω n k hωE
    exact norm_cfAt_le_one_of_isForceReg u ψ (hω (linePieceS_subset D S n k hωE)).2.1 hωE.2.1 hωE.2.2
  have hpiece : ∀ n k, AEStronglyMeasurable ((E n k).indicator (g n k)) P ∧
      ∫ ω, (E n k).indicator f ω ∂P = ∫ ω, (E n k).indicator (g n k) ω ∂P := by
    intro n k
    have hae : (E n k).indicator (g n k) =ᵐ[P] (E n k).indicator (P[f | 𝒢L (dyT n k)]) := by
      filter_upwards [hline ψ (dyT n k), hDF] with ω hω hω'
      by_cases hωE : ω ∈ E n k
      · rw [indicator_of_mem hωE, indicator_of_mem hωE]
        exact (hω (hω' (linePieceS_subset D S n k hωE)).1 (pos_of_mem_linePieceS hωE) hωE.2).symm
      · rw [indicator_of_notMem hωE, indicator_of_notMem hωE]
    have hm' : AEStronglyMeasurable ((E n k).indicator (P[f | 𝒢L (dyT n k)])) P :=
      ((stronglyMeasurable_condExp.mono (h𝒢Lm _)).indicator (hEm' n k)).aestronglyMeasurable
    refine ⟨hm'.congr hae.symm, ?_⟩
    rw [integral_congr_ae hae, integral_indicator (hEm' n k), integral_indicator (hEm' n k),
      setIntegral_condExp (h𝒢Lm _) hfi (h𝒢L _ _ (hEm n k))]
  have hgi : ∀ n k, Integrable ((E n k).indicator (g n k)) P := fun n k => by
    refine Integrable.of_bound (hpiece n k).1 1 ?_
    filter_upwards [hgb] with ω hω
    by_cases hωE : ω ∈ E n k
    · rw [indicator_of_mem hωE]; exact hω n k hωE
    · rw [indicator_of_notMem hωE, norm_zero]; exact zero_le_one
  have hsum : ∀ n, ∫ ω, ∑ k ∈ Finset.range (4 ^ n), (E n k).indicator f ω ∂P =
      ∫ ω, ∑ k ∈ Finset.range (4 ^ n), (E n k).indicator (g n k) ω ∂P := fun n => by
    rw [integral_finsetSum _ fun k _ => hfi.indicator (hEm' n k),
      integral_finsetSum _ fun k _ => hgi n k]
    exact Finset.sum_congr rfl fun k _ => (hpiece n k).2
  -- the clock exceeds `q` on `D`: reach at a level strictly between `q` and the lifetime
  have hgood : ∀ᵐ ω ∂P, ω ∈ D → (∃ t, q < Qc t ω) ∧
      (∀ t : ℕ → ℝ≥0, Tendsto (fun n => Qc (t n) ω) atTop (𝓝 q) → ∀ᶠ n in atTop, ω ∈ S (t n)) ∧
      IsForceReg W VL VR ζ ω ∧ ω ∈ avoidSet W ζ ψ q := by
    have hreach' : ∀ᵐ ω ∂P, ∀ r : ℚ, 0 ≤ r → ω ∈ F → (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω →
        ∃ t, (r : ℝ).toNNReal ≤ Qc t ω :=
      ae_all_iff.2 fun r => (hreach (r : ℝ).toNNReal).mono fun ω h _ => h
    filter_upwards [hDF, hreach'] with ω hω hr hωD
    obtain ⟨hωF, hp, hav⟩ := hω hωD
    refine ⟨?_, fun t ht => eventually_mem_lineSafe ψ.hasCompactSupport.isCompact
      (tsupport_subset_H ψ) hp hav.1 hav.2 t ht, hp, hav⟩
    obtain ⟨r, hr0, hqr, hrζ⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hav.1
    have hq : (q : ℝ≥0∞) < (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) := hqr
    obtain ⟨t, ht⟩ := hr r hr0 hωF hrζ
    exact ⟨t, lt_of_lt_of_le (ENNReal.coe_lt_coe.1 hq) ht⟩
  have hlimf := ae_tendsto_sum_linePieceS (P := P) (D := D) (S := S) hc hm h0 (fun _ _ => f) f (by
    filter_upwards [hgood] with ω hω hωD
    obtain ⟨hr, hS', -, -⟩ := hω hωD
    exact ⟨hr, hS', tendsto_const_nhds⟩)
  have hlimg := ae_tendsto_sum_linePieceS (P := P) (D := D) (S := S) hc hm h0 g
    (cfAt κ W u ψ 1 fun _ => q) (by
    filter_upwards [hgood] with ω hω hωD
    obtain ⟨hr, hS', hp, hav⟩ := hω hωD
    exact ⟨hr, hS', (tendsto_cfAt_of_isForceReg (isBoundedHarmonicExtension_bheProc) ψ hp hav.1 hav.2
      (tendsto_Qc_dyT_labS (hc ω) (hm ω) (h0 ω) hr)).2⟩)
  have hTf := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun n => (Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
      (hfm.aestronglyMeasurable.indicator (hEm' n k))))
    (integrable_const 1) (fun n => Eventually.of_forall fun ω =>
      norm_sum_linePieceS_le hc hm h0 (fun _ _ => f) n _ fun k _ => hfn ω) hlimf
  have hTg := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun n => Finset.aestronglyMeasurable_fun_sum _ fun k _ => (hpiece n k).1)
    (integrable_const 1) (fun n => by
      filter_upwards [hgb] with ω hω
      exact norm_sum_linePieceS_le hc hm h0 g n _ fun k hk => hω n k hk) hlimg
  rw [integral_indicator hDm] at hTf hTg
  exact tendsto_nhds_unique (hTf.congr fun n => hsum n) hTg

end Law

end InteractingSLE.Theorem14.SB.Cr
