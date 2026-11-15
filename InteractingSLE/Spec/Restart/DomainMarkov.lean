/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.Assembly11Tau
import InteractingSLE.Spec.Sec7.LocalExtGChart

/-!
# The domain Markov step, part 1: the coupling clause at every stopping time from dyadic times

Packet PROVE-DOMAINMARKOV. The domain Markov property of a flow-line coupling is proved by disintegrating the restarted
coupling along the regular conditional law given the stopped history (Aux. lemma 53 in kernel form). Under a kernel
measure only **countably many** identities can be transferred from the original probability space, while the frozen
optional hull specification asks for the conditional-law clause at **every** stopping time of the (kernel-augmented)
driving filtration. This file is the single-measure bridge between the two:

* **`setIntegral_cexp_eq_cfAt_of_dyadic`**: for an integrated evolution and a measurable field, if at every dyadic
  time `q = k/2ⁿ` and for every event `A` of the null augmentation of the killed driving filtration at `q` contained in
  the avoidance event `{q < ζ, supp ψ ∩ K_q = ∅}` the field has the protected-kernel law
  `∫_A e^{i(h,ψ)} = ∫_A exp(i(𝔥_q, ψ) − E_q(ψ)/2)` (`IsDyadicSampled`), then the same identity holds at **every**
  stopping time `τ < ζ` of the frozen driving filtration, on every event of `𝓕_τ` inside `{supp ψ ∩ K_τ = ∅}`;
* **`condExp_cexp_eq_frozenRHS_of_dyadic`**: hence the conditional-law conjunct of the frozen `IsOptionalHullCoupling`;
* **`isOptionalHullCoupling_of_dyadic`**: the frozen predicate from an evolution, the GFF law at time `0`,
  `IsDyadicSampled` and the locality of `K_τ` (conditional helper: locality is an input).

Proof of the first item: discretize `τ` from above, `σₙ = (⌈2ⁿτ⌉ + 1)/2ⁿ ↓ τ`. The piece `A ∩ {⌈2ⁿτ⌉ = k}` is an
event of the frozen `𝓕_{k/2ⁿ}`, hence of the null augmentation at `(k + 1)/2ⁿ` (`measurableSet_piece`,
`usualAugmentation_le_nullAugmented`). Intersected with the measurable safe events (`safeU`: the avoidance event with a
positive margin, through `Coupling.safeSet`) the pieces satisfy the dyadic identity, and the finite sums over
`k < 4ⁿ` give the identity at `σₙ`. As `n → ∞` the summed events increase to `A ∩ {τ < ∞}` (right-continuity of the
hulls on compact sets, `exists_eventually_isSafeAt_tendsto_cfAt`) and `cfAt σₙ → cfAt τ` (continuity in time of the
tested mean and energy up to a safe time); dominated convergence (all integrands have modulus at most one) finishes.

The right-continuity of the hulls is PROVE-LOCEXT-L's argument (`Foundations/Loewner/HullRightCont.lean`, in flight and
not imported here), restated below.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

namespace DomainMarkov

open Coupling Ito

/-! ### Right-continuity of the hulls on compact sets (PROVE-LOCEXT-L's argument) -/

/-- A compact set avoiding the hull of a continuous driver at time `s` avoids it slightly later. -/
theorem exists_pos_disjoint_fwdHull_cont {A : ℝ → ℝ} (hA : Continuous A) {C : Set ℂ} (hC : IsCompact C)
    (hCH : C ⊆ H) {s : ℝ} (hs : Disjoint C (fwdHull A s)) :
    ∃ δ > 0, Disjoint C (fwdHull A (s + δ)) := by
  rcases C.eq_empty_or_nonempty with hC0 | hCne
  · exact ⟨1, one_pos, by rw [hC0]; exact empty_disjoint _⟩
  obtain ⟨z₀, hz₀C, hmin⟩ :=
    (CoreArc.lowerSemicontinuousOn_swallowTime hA hCH).exists_isMinOn hCne hC
  have hz₀ : ENNReal.ofReal s < swallowTime A z₀ := by
    by_contra hle
    exact Set.disjoint_left.1 hs hz₀C ⟨hCH hz₀C, not_lt.1 hle⟩
  obtain ⟨r, -, hsr, hrσ⟩ := ENNReal.lt_iff_exists_real_btwn.1 hz₀
  have hs' : s < r := (ENNReal.ofReal_lt_ofReal_iff'.1 hsr).1
  refine ⟨r - s, sub_pos.2 hs', Set.disjoint_left.2 fun z hzC hzK => ?_⟩
  have h1 : swallowTime A z₀ ≤ swallowTime A z := hmin hzC
  have h2 : swallowTime A z ≤ ENNReal.ofReal (s + (r - s)) := hzK.2
  rw [add_sub_cancel] at h2
  exact absurd (hrσ.trans_le (h1.trans h2)) (lt_irrefl _)

/-- **Right-continuity of the hulls of a driving path continuous before its lifetime**: a compact `C ⊆ ℍ` avoiding
`K_s`, `s < ζ`, avoids every `K_t`, `t ≤ s + δ`, for some `δ > 0` with `s + δ < ζ`. -/
theorem exists_pos_disjoint_fwdHull_rpath' {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) {s : ℝ≥0} (hsζ : (s : ℝ≥0∞) < ζ) {C : Set ℂ} (hC : IsCompact C)
    (hCH : C ⊆ H) (hs : Disjoint C (fwdHull (rpath w) s)) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ((s + δ : ℝ≥0) : ℝ≥0∞) < ζ ∧
      ∀ t : ℝ≥0, t ≤ s + δ → Disjoint C (fwdHull (rpath w) t) := by
  obtain ⟨T, hsT, hTζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hsζ
  have hsT' : s < T := by exact_mod_cast hsT
  have hT0 : (0 : ℝ) ≤ T := T.coe_nonneg
  have hwT : ContinuousOn (rpath w) (Icc 0 (T : ℝ)) := continuousOn_rpath hw hTζ
  set A : ℝ → ℝ := clampDrv (rpath w) T with hAdef
  have hA : Continuous A := continuous_clampDrv hT0 hwT
  have hcongr : ∀ t : ℝ, 0 ≤ t → t < T → fwdHull (rpath w) t = fwdHull A t := fun t ht htT =>
    LocalExt.fwdHull_congr_of_eqOn_of_lt ht htT clampDrv_eqOn.symm
  have hsA : Disjoint C (fwdHull A s) := by
    rw [← hcongr s s.coe_nonneg (by exact_mod_cast hsT')]
    exact hs
  obtain ⟨δ, hδ, hδC⟩ := exists_pos_disjoint_fwdHull_cont hA hC hCH hsA
  set δ' : ℝ≥0 := min (Real.toNNReal δ) ((T - s) / 2) with hδ'def
  have hTs : 0 < T - s := tsub_pos_of_lt hsT'
  have hδ'pos : 0 < δ' := lt_min (Real.toNNReal_pos.2 hδ) (half_pos hTs)
  have hδ'T : s + δ' < T := by
    have h1 : δ' ≤ (T - s) / 2 := min_le_right _ _
    have h2 : (T - s) / 2 < T - s := half_lt_self hTs
    calc s + δ' < s + (T - s) := by gcongr; exact h1.trans_lt h2
      _ = T := add_tsub_cancel_of_le hsT'.le
  have hδ'δ : ((s + δ' : ℝ≥0) : ℝ) ≤ (s : ℝ) + δ := by
    have : (δ' : ℝ) ≤ δ := by
      have := min_le_left (Real.toNNReal δ) ((T - s) / 2)
      calc (δ' : ℝ) ≤ (Real.toNNReal δ : ℝ) := by exact_mod_cast this
        _ = δ := Real.coe_toNNReal δ hδ.le
    push_cast
    linarith
  refine ⟨δ', hδ'pos, lt_of_lt_of_le (by exact_mod_cast hδ'T) hTζ.le, fun t ht => ?_⟩
  have htT : (t : ℝ) < T := by exact_mod_cast ht.trans_lt hδ'T
  rw [hcongr t t.coe_nonneg htT]
  refine hδC.mono_right ((fwdHull_mono (W := A)).1 ?_)
  exact (show (t : ℝ) ≤ ((s + δ' : ℝ≥0) : ℝ) by exact_mod_cast ht).trans hδ'δ

/-! ### Safe times -/

section Safe

variable {K : Set ℂ} {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- A safe time is safe for the parameters `σ₀ = N = t` of `Coupling.safeSet`. -/
theorem isSafeAt_self_of {δ N : ℝ} {σ₀ t : ℝ≥0} (h : IsSafeAt K δ N σ₀ ζ w t) : IsSafeAt K δ t t ζ w t :=
  ⟨h.1, le_rfl, le_rfl, h.2.2.2⟩

/-- **A compact set alive at a time `t < ζ` is safe at `t` at some positive level.** -/
theorem exists_isSafeAt_self (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) (hK : IsCompact K)
    (hKH : K ⊆ H) {t : ℝ≥0} (htζ : (t : ℝ≥0∞) < ζ) (halive : ∀ z ∈ K, ∃ u, IsForwardSol (rpath w) z t u) :
    ∃ δ > 0, IsSafeAt K δ t t ζ w t := by
  obtain ⟨m, hm, hKm⟩ := exists_pos_le_im_of_isCompact hK hKH
  have hev := eventually_le_safeExitTime hw hK hKH m (le_refl t) htζ halive
  obtain ⟨n, hn, htn⟩ := (hev.and (eventually_ge_atTop ⌈(t : ℝ)⌉₊)).exists
  have hδ : 0 < m / ((n : ℝ) + 1) := by positivity
  have hζ0 : 0 < ζ := lt_of_le_of_lt (zero_le (a := (t : ℝ≥0∞))) htζ
  have h0 : IsSafeAt K (m / ((n : ℝ) + 1)) n t ζ w 0 := by
    refine isSafeAt_zero hKH (fun z hz => ?_) hw0 hζ0 (Nat.cast_nonneg n)
    have h1 : m / ((n : ℝ) + 1) ≤ m := div_le_self hm.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    exact h1.trans (hKm z hz)
  have hex := isSafeAt_safeExitTime hw hKH hδ htζ h0
  exact ⟨_, hδ, isSafeAt_self_of (hex.anti hw hKH hn)⟩

/-- A safe set avoids the hull. -/
theorem disjoint_fwdHull_of_isSafeAt {δ N : ℝ} {σ₀ t : ℝ≥0} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hKH : K ⊆ H) (h : IsSafeAt K δ N σ₀ ζ w t) : Disjoint K (fwdHull (rpath w) t) :=
  Set.disjoint_left.2 fun z hz =>
    notMem_fwdHull_of_alive hw h.1 (hKH hz) (h.2.2.2 z hz).1

end Safe

/-! ### Dyadic times and the pieces of a discretized stopping time -/

section Pieces

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The dyadic time `k / 2ⁿ`. -/
def dyT (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / 2 ^ n

theorem le_dyT_iff {a : ℝ≥0} {n k : ℕ} : a ≤ dyT n k ↔ ⌈2 ^ n * a⌉₊ ≤ k := by
  rw [Nat.ceil_le, dyT, le_div_iff₀ (pow_pos two_pos n), mul_comm]

theorem dyT_lt_dyT_succ (n k : ℕ) : dyT n k < dyT n (k + 1) := by
  unfold dyT
  exact div_lt_div_of_pos_right (by exact_mod_cast Nat.lt_succ_self k) (pow_pos two_pos n)

theorem dyT_mono (n : ℕ) {k k' : ℕ} (h : k ≤ k') : dyT n k ≤ dyT n k' := by
  unfold dyT
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (zero_le (a := (2 : ℝ≥0) ^ n))

/-- `a ≤ ⌈2ⁿ a⌉/2ⁿ`. -/
theorem le_dyT_ceil (a : ℝ≥0) (n : ℕ) : a ≤ dyT n ⌈2 ^ n * a⌉₊ := le_dyT_iff.2 le_rfl

/-- `(⌈2ⁿ a⌉ + 1)/2ⁿ ≤ a + 2/2ⁿ`. -/
theorem dyT_ceil_succ_le (a : ℝ≥0) (n : ℕ) : dyT n (⌈2 ^ n * a⌉₊ + 1) ≤ a + 2 / 2 ^ n := by
  have h2 : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
  unfold dyT
  rw [div_le_iff₀ h2, add_mul, div_mul_cancel₀ _ h2.ne']
  have hc : ((⌈2 ^ n * a⌉₊ : ℕ) : ℝ≥0) < 2 ^ n * a + 1 := Nat.ceil_lt_add_one (zero_le (a := 2 ^ n * a))
  push_cast
  calc ((⌈2 ^ n * a⌉₊ : ℕ) : ℝ≥0) + 1 ≤ 2 ^ n * a + 1 + 1 := by gcongr
    _ = a * 2 ^ n + 2 := by ring

/-- `τ ≤ k/2ⁿ` iff `τ` is finite and `⌈2ⁿ τ⌉ ≤ k`. -/
theorem le_coe_dyT_iff {τ : WithTop ℝ≥0} {n k : ℕ} :
    τ ≤ ((dyT n k : ℝ≥0) : WithTop ℝ≥0) ↔ τ ≠ ⊤ ∧ ⌈2 ^ n * τ.untopD 0⌉₊ ≤ k := by
  induction τ using WithTop.recTopCoe with
  | top => simp only [ne_eq, not_true_eq_false, false_and, iff_false]; exact WithTop.not_top_le_coe _
  | coe a =>
    rw [WithTop.coe_le_coe, le_dyT_iff, WithTop.untopD_coe]
    simp only [ne_eq, WithTop.coe_ne_top, not_false_eq_true, true_and]

/-- The pieces `{⌈2ⁿ τ⌉ = k}` of an event of `𝓖_τ` are events of `𝓖_{k/2ⁿ}`. -/
theorem measurableSet_piece {𝓖 : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) (n k : ℕ) :
    MeasurableSet[𝓖 (dyT n k)] (A ∩ {ω | τ ω ≠ ⊤ ∧ ⌈2 ^ n * (τ ω).untopD 0⌉₊ = k}) := by
  have h1 : MeasurableSet[𝓖 (dyT n k)] (A ∩ {ω | τ ω ≤ ((dyT n k : ℝ≥0) : WithTop ℝ≥0)}) := hA.2 _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · convert h1 using 2
    ext ω
    simp only [mem_ofPred_eq, le_coe_dyT_iff, Nat.le_zero]
  · have h2 : MeasurableSet[𝓖 (dyT n k)] {ω | τ ω ≤ ((dyT n (k - 1) : ℝ≥0) : WithTop ℝ≥0)} :=
      𝓖.mono (dyT_mono n (Nat.sub_le k 1)) _ (hτ _)
    convert h1.diff h2 using 1
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, Set.mem_sdiff, le_coe_dyT_iff]
    constructor
    · rintro ⟨hωA, hne, hc⟩
      exact ⟨⟨hωA, hne, hc.le⟩, fun ⟨_, h⟩ => by omega⟩
    · rintro ⟨⟨hωA, hne, hc⟩, h⟩
      exact ⟨hωA, hne, by by_contra hc'; exact h ⟨hne, by omega⟩⟩

/-- The usual augmentation at `t` lies in the null augmentation at every later time. -/
theorem usualAugmentation_le_nullAugmented {P : Measure Ω} (𝓗 : Filtration ℝ≥0 mΩ) {t s : ℝ≥0}
    (hts : t < s) : usualAugmentation 𝓗 P t ≤ nullAugmented 𝓗 P s := by
  rw [usualAugmentation_apply]
  exact iInf₂_le s hts

/-- A finite sum of indicators of sets on which a labelling function takes the summation index reduces to the term
of the label. -/
theorem sum_indicator_eq_of_label {s : Finset ℕ} {D : ℕ → Set Ω} {g : ℕ → Ω → ℂ} {lab : Ω → ℕ}
    (hD : ∀ k ω, ω ∈ D k → lab ω = k) (ω : Ω) :
    ∑ k ∈ s, (D k).indicator (g k) ω = if lab ω ∈ s then (D (lab ω)).indicator (g (lab ω)) ω else 0 := by
  have hz : ∀ k, k ≠ lab ω → (D k).indicator (g k) ω = 0 := fun k hk =>
    indicator_of_notMem (fun hω => hk (hD k ω hω).symm) _
  split_ifs with hl
  · exact Finset.sum_eq_single_of_mem _ hl fun b _ hb => hz b hb
  · exact Finset.sum_eq_zero fun b hb => hz b fun e => hl (e ▸ hb)

/-- `(⌈2ⁿ a⌉ + 1)/2ⁿ → a`. -/
theorem tendsto_dyT_ceil (a : ℝ≥0) : Tendsto (fun n => dyT n (⌈2 ^ n * a⌉₊ + 1)) atTop (𝓝 a) := by
  have h2 : Tendsto (fun n : ℕ => (2 : ℝ≥0) / 2 ^ n) atTop (𝓝 0) := by
    have h := (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := 2⁻¹) (by norm_num)).const_mul 2
    simpa [div_eq_mul_inv, ← inv_pow] using h
  have hup : Tendsto (fun n : ℕ => a + 2 / 2 ^ n) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.add h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun n => (le_dyT_ceil a n).trans (dyT_mono n (Nat.le_succ _))) (fun n => dyT_ceil_succ_le a n)

/-- Eventually `⌈2ⁿ a⌉ < 4ⁿ`. -/
theorem eventually_ceil_lt_four_pow (a : ℝ≥0) : ∀ᶠ n : ℕ in atTop, ⌈2 ^ n * a⌉₊ < 4 ^ n := by
  have hev : ∀ᶠ n : ℕ in atTop, a + 1 ≤ (2 : ℝ≥0) ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two : (1 : ℝ≥0) < 2)).eventually_ge_atTop (a + 1)
  filter_upwards [hev] with n hn
  have h1 : (1 : ℝ≥0) ≤ 2 ^ n := one_le_pow₀ one_le_two
  have hc : ((⌈2 ^ n * a⌉₊ : ℕ) : ℝ≥0) < 2 ^ n * a + 1 := Nat.ceil_lt_add_one (zero_le (a := 2 ^ n * a))
  have h4 : ((4 ^ n : ℕ) : ℝ≥0) = 2 ^ n * 2 ^ n := by
    rw [← mul_pow]; norm_num
  have hle : 2 ^ n * a + 1 ≤ ((4 ^ n : ℕ) : ℝ≥0) := by
    rw [h4]
    calc 2 ^ n * a + 1 ≤ 2 ^ n * a + 2 ^ n := by gcongr
      _ = 2 ^ n * (a + 1) := by ring
      _ ≤ 2 ^ n * 2 ^ n := by gcongr
  exact_mod_cast hc.trans_le hle

end Pieces

/-! ### The protected-kernel law at dyadic times gives it at every stopping time -/

section Main

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
  {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- The avoidance event `{q < ζ, supp ψ ∩ K_q = ∅}` at a fixed time `q`. -/
def avoidSet (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ψ : ℂ → ℝ) (q : ℝ≥0) : Set Ω :=
  {ω | (q : ℝ≥0∞) < ζ ω ∧ Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) q)}

/-- **The protected-kernel law at the dyadic times**: at every dyadic time `q = k/2ⁿ`, on every event of the null
augmentation of the killed driving filtration at `q` inside the avoidance event, `∫_A e^{i(h,ψ)} = ∫_A cfAt q`. -/
def IsDyadicSampled (κ : ℝ) (W : ℝ≥0 → Ω → ℝ) (u : Ω → ℝ≥0 → ℂ → ℝ) (P : Measure Ω)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) : Prop :=
  ∀ (ψ : LQGMetric.TestOn upperHalfPlaneOpens) (n k : ℕ) (A : Set Ω),
    MeasurableSet[nullAugmented (killedDrivingFiltration hX) P (dyT n k)] A →
    A ⊆ avoidSet W ζ ψ (dyT n k) →
    ∫ ω in A, Complex.exp (Complex.I * (h ω ψ : ℂ)) ∂P = ∫ ω in A, cfAt κ W u ψ 1 (fun _ => dyT n k) ω ∂P

/-- **Along one good path, times decreasing to an avoidance time are eventually safe, and `cfAt` converges.** -/
theorem exists_eventually_isSafeAt_tendsto_cfAt {u : Ω → ℝ≥0 → ℂ → ℝ}
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
    (ψ : LQGMetric.TestOn upperHalfPlaneOpens) {ω : Ω}
    (hp : IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω)
      (fun t => B t ω) (ζ ω))
    {a : ℝ≥0} (haζ : (a : ℝ≥0∞) < ζ ω)
    (hdis : Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) a))
    {t : ℕ → ℝ≥0} (ht : Tendsto t atTop (𝓝 a)) :
    ∃ m : ℕ, (∀ᶠ n in atTop, IsSafeAt (tsupport ψ) (1 / ((m : ℝ) + 1)) (t n) (t n) (ζ ω) (W · ω) (t n)) ∧
      Tendsto (fun n => cfAt κ W u ψ 1 (fun _ => t n) ω) atTop (𝓝 (cfAt κ W u ψ 1 (fun _ => a) ω)) := by
  set K : Set ℂ := tsupport (ψ : ℂ → ℝ) with hKdef
  have hKH : K ⊆ H := tsupport_subset_H ψ
  have hK : IsCompact K := ψ.hasCompactSupport.isCompact
  have hw : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω} := hp.2.2.2.1
  obtain ⟨δ', hδ', hrζ, hdisj⟩ := exists_pos_disjoint_fwdHull_rpath' hw haζ hK hKH hdis
  set r : ℝ≥0 := a + δ' with hr
  have halive : ∀ z ∈ K, ∃ v, IsForwardSol (rpath (W · ω)) z r v := fun z hz =>
    exists_isForwardSol_of_mem r.coe_nonneg ⟨hKH hz, fun hzK => Set.disjoint_left.1 (hdisj r le_rfl) hz hzK⟩
  obtain ⟨δ₀, hδ₀, hsafe⟩ := exists_isSafeAt_self hw hp.1 hK hKH hrζ halive
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ₀
  have har : a < r := lt_add_of_pos_right a hδ'
  have hev_le : ∀ᶠ n in atTop, t n ≤ r := ((tendsto_order.1 ht).2 r har).mono fun n h => h.le
  refine ⟨m, hev_le.mono fun n hn => ?_, ?_⟩
  · exact (isSafeAt_self_of (hsafe.anti hw hKH hn)).mono hm.le le_rfl le_rfl
  set g : ℝ≥0 → ℂ := fun s => Complex.exp (Complex.I * 1 *
      ((∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s z * ψ z : ℝ) : ℂ) -
      1 ^ 2 * ((loewnerGreenEnergy (rpath (W · ω)) s ψ : ℝ) : ℂ) / 2) with hg
  have hgc : ContinuousOn g (Iic r) := by
    have h1 := hsafe.continuousOn_meanInt (κ := κ) (ρL := ρL) (ρR := ρR) ψ.continuous ψ.hasCompactSupport hw
      hp.2.2.2.2.1 hp.2.2.2.2.2.1 hKH hδ₀
    have h2 := hsafe.continuousOn_loewnerGreenEnergy ψ.continuous ψ.hasCompactSupport hw hKH hδ₀
    exact ((continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn h1)).sub
      ((continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn h2)).div_const 2)).cexp
  have hcf : ∀ s ≤ r, cfAt κ W u ψ 1 (fun _ => s) ω = g s := fun s hs => by
    have hsζ : (s : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hs) hrζ
    have hmean : (∫ z, couplingMean κ (fun x : ℝ => W x.toNNReal ω) s (u ω s) z * ψ z) =
        ∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s z * ψ z := by
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      by_cases hz : z ∈ K
      · have hvL : ∀ i, VL i s ω ≤ W s ω := hp.2.2.2.2.2.2.2.1 s hsζ
        have hvR : ∀ i, W s ω ≤ VR i s ω := hp.2.2.2.2.2.2.2.2.1 s hsζ
        have e := couplingMean_eq_meanCan (κ := κ) (ρL := ρL) (ρR := ρR) (w := (W · ω))
          (vL := fun i t => VL i t ω) (vR := fun i t => VR i t ω) hw hKH hsafe hδ₀ hs hz hvL hvR (hu ω s)
        exact congrArg (· * ψ z) e
      · simp [image_eq_zero_of_notMem_tsupport hz]
    simp only [cfAt, hg, hmean]
    rfl
  have hlim : Tendsto (fun n => g (t n)) atTop (𝓝 (g a)) :=
    (hgc a (mem_Iic.2 har.le)).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨ht, hev_le⟩)
  rw [hcf a har.le]
  exact hlim.congr' (hev_le.mono fun n hn => (hcf (t n) hn).symm)

/-- On a safe event at a fixed time `q`, `cfAt q` is a measurable function (the explicit mean and energy). -/
theorem measurable_safeSet_indicator_cfAt {𝓖 : Filtration ℝ≥0 mΩ} (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
    (ψ : LQGMetric.TestOn upperHalfPlaneOpens) {G : Set Ω}
    (hGp : ∀ ω ∈ G, IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (fun t => B t ω) (ζ ω))
    (hG0 : MeasurableSet[𝓖 0] G) (hWa : AdaptedBefore 𝓖 ζ W) (hVLa : ∀ i, AdaptedBefore 𝓖 ζ (VL i))
    (hVRa : ∀ i, AdaptedBefore 𝓖 ζ (VR i)) {δ : ℝ} (hδ : 0 < δ) (q : ℝ≥0) :
    Measurable ((safeSet W ζ G ψ δ q).indicator (cfAt κ W u ψ 1 fun _ => q)) := by
  have hKH : tsupport (ψ : ℂ → ℝ) ⊆ H := tsupport_subset_H ψ
  have hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω hω =>
    (hGp ω hω).2.2.2.1
  have e : (safeSet W ζ G ψ δ q).indicator (cfAt κ W u ψ 1 fun _ => q) =
      (safeSet W ζ G ψ δ q).indicator (fun ω =>
        Complex.exp (Complex.I * 1 * ((meanK κ ρL ρR W VL VR ζ G ψ δ q ω : ℝ) : ℂ) -
          1 ^ 2 * ((energyK W ζ G ψ δ q ω : ℝ) : ℂ) / 2)) := by
    refine indicator_congr fun ω hω => ?_
    have hp := hGp ω hω.1
    have hw := hGc ω hω.1
    have hvL : ∀ i, VL i q ω ≤ W q ω := hp.2.2.2.2.2.2.2.1 q hω.2.1
    have hvR : ∀ i, W q ω ≤ VR i q ω := hp.2.2.2.2.2.2.2.2.1 q hω.2.1
    have hmean : (∫ z, couplingMean κ (fun x : ℝ => W x.toNNReal ω) q (u ω q) z * ψ z) =
        ∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) q z * ψ z := by
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      by_cases hz : z ∈ tsupport (ψ : ℂ → ℝ)
      · have e := couplingMean_eq_meanCan (κ := κ) (ρL := ρL) (ρR := ρR) (w := (W · ω))
          (vL := fun i t => VL i t ω) (vR := fun i t => VR i t ω) hw hKH hω.2 hδ le_rfl hz hvL hvR (hu ω q)
        exact congrArg (· * ψ z) e
      · simp [image_eq_zero_of_notMem_tsupport hz]
    have hm : meanK κ ρL ρR W VL VR ζ G ψ δ q ω =
        ∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) q z * ψ z := by
      simp only [meanK, hω, ↓reduceIte]
    have he : energyK W ζ G ψ δ q ω = loewnerGreenEnergy (rpath (W · ω)) q ψ := by
      simp only [energyK, hω, ↓reduceIte]
    rw [hm, he, ← hmean]
    rfl
  rw [e]
  refine Measurable.indicator ?_ ((𝓖.le q) _ (measurableSet_safeSet hWa hGc hG0 hKH hδ q))
  have h1 := (measurable_meanK hWa hGc hG0 hKH hδ κ ρL ρR hVLa hVRa ψ.continuous.measurable q).mono
    (𝓖.le q) le_rfl
  have h2 := (measurable_energyK hWa hGc hG0 hKH hδ ψ.continuous.measurable q).mono (𝓖.le q) le_rfl
  exact Complex.measurable_exp.comp ((measurable_const.mul (Complex.measurable_ofReal.comp h1)).sub
    ((measurable_const.mul (Complex.measurable_ofReal.comp h2)).div_const 2))

/-- The union over the levels `1/(m+1)` of the safe events at a fixed time `q` (the avoidance event with some positive
margin, on the good set `G`). -/
def safeU (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (G : Set Ω) (ψ : ℂ → ℝ) (q : ℝ≥0) : Set Ω :=
  ⋃ m : ℕ, safeSet W ζ G ψ (1 / ((m : ℝ) + 1)) q

theorem mem_safeU_of_isSafeAt {G : Set Ω} {ψ : ℂ → ℝ} {q : ℝ≥0} {ω : Ω} (hωG : ω ∈ G) {m : ℕ}
    (h : IsSafeAt (tsupport ψ) (1 / ((m : ℝ) + 1)) q q (ζ ω) (W · ω) q) : ω ∈ safeU W ζ G ψ q :=
  mem_iUnion.2 ⟨m, hωG, h⟩

section Good

variable {u : Ω → ℝ≥0 → ℂ → ℝ}
  (hu : ∀ ω s, IsBoundedHarmonicExtension
    (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
    (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
  (ψ : LQGMetric.TestOn upperHalfPlaneOpens) {G : Set Ω}
  (hGp : ∀ ω ∈ G, IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
    (fun i t => VR i t ω) (fun t => B t ω) (ζ ω))

include hGp in
theorem safeU_subset_avoidSet (q : ℝ≥0) : safeU W ζ G ψ q ⊆ avoidSet W ζ ψ q := fun ω hω => by
  obtain ⟨m, hm⟩ := mem_iUnion.1 hω
  have hw : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := (hGp ω hm.1).2.2.2.1
  have hs : IsSafeAt (tsupport (ψ : ℂ → ℝ)) (1 / ((m : ℝ) + 1)) q q (ζ ω) (W · ω) q := hm.2
  have hd : Disjoint (tsupport (ψ : ℂ → ℝ)) (fwdHull (rpath (W · ω)) q) :=
    disjoint_fwdHull_of_isSafeAt hw (tsupport_subset_H ψ) hs
  exact ⟨hs.1, hd⟩

include hGp in
theorem norm_cfAt_le_one_of_mem_safeU (u : Ω → ℝ≥0 → ℂ → ℝ) {q : ℝ≥0} {ω : Ω} (hω : ω ∈ safeU W ζ G ψ q) :
    ‖cfAt κ W u ψ 1 (fun _ => q) ω‖ ≤ 1 := by
  obtain ⟨m, hm⟩ := mem_iUnion.1 hω
  exact norm_cfAt_le_one u 1 ψ (r := fun _ => q) (continuousOn_rpath (hGp ω hm.1).2.2.2.1 hm.2.1)
    (hGp ω hm.1).1 (fun z hz => (hm.2.2.2.2 z hz).1)

include hu hGp in
/-- `cfAt q` restricted to the safe union is almost everywhere strongly measurable. -/
theorem aestronglyMeasurable_safeU_indicator_cfAt {𝓖 : Filtration ℝ≥0 mΩ} (hG0 : MeasurableSet[𝓖 0] G)
    (hWa : AdaptedBefore 𝓖 ζ W) (hVLa : ∀ i, AdaptedBefore 𝓖 ζ (VL i)) (hVRa : ∀ i, AdaptedBefore 𝓖 ζ (VR i))
    (q : ℝ≥0) : AEStronglyMeasurable ((safeU W ζ G ψ q).indicator (cfAt κ W u ψ 1 fun _ => q)) P := by
  have hmK : ∀ m : ℕ, Measurable
      ((safeSet W ζ G ψ (1 / ((m : ℝ) + 1)) q).indicator (cfAt κ W u ψ 1 fun _ => q)) := fun m =>
    measurable_safeSet_indicator_cfAt u hu ψ hGp hG0 hWa hVLa hVRa (by positivity) q
  refine aestronglyMeasurable_of_tendsto_ae atTop (fun m => (hmK m).aestronglyMeasurable)
    (ae_of_all _ fun ω => ?_)
  by_cases hω : ω ∈ safeU W ζ G ψ q
  · obtain ⟨m₀, hm₀⟩ := mem_iUnion.1 hω
    rw [indicator_of_mem hω]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop m₀] with m hm
    have hle : 1 / ((m : ℝ) + 1) ≤ 1 / ((m₀ : ℝ) + 1) := by gcongr
    rw [indicator_of_mem (show ω ∈ safeSet W ζ G ψ (1 / ((m : ℝ) + 1)) q from
      ⟨hm₀.1, hm₀.2.mono hle le_rfl le_rfl⟩)]
  · rw [indicator_of_notMem hω]
    exact tendsto_const_nhds.congr fun m =>
      (indicator_of_notMem (fun h' => hω (mem_iUnion.2 ⟨m, h'⟩)) _).symm

/-- The `k`-th piece at level `n` of an event `A` along a stopping time `τ`: `⌈2ⁿ τ⌉ = k` and the support is safe at
`(k + 1)/2ⁿ`. -/
def piece (τ : Ω → WithTop ℝ≥0) (A : Set Ω) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (G : Set Ω) (ψ : ℂ → ℝ)
    (n k : ℕ) : Set Ω :=
  A ∩ {ω | τ ω ≠ ⊤ ∧ ⌈2 ^ n * (τ ω).untopD 0⌉₊ = k} ∩ safeU W ζ G ψ (dyT n (k + 1))

include hu hGp in
/-- **Pointwise convergence of the discretized integrands.** Almost surely (on the good set, with `τ < ζ`), the sums
over the pieces at level `n` of `e^{i(h,ψ)}` and of `cfAt` converge to their values at `τ` on `A ∩ {τ < ∞}`. -/
theorem ae_tendsto_sum_piece {τ : Ω → WithTop ℝ≥0} {A : Set Ω} (f : Ω → ℂ)
    (hAE : A ⊆ {ω | Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))})
    (hGae : ∀ᵐ ω ∂P, ω ∈ G) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) :
    ∀ᵐ ω ∂P, Tendsto (fun n => ∑ k ∈ Finset.range (4 ^ n), (piece τ A W ζ G ψ n k).indicator f ω) atTop
        (𝓝 ((A ∩ {ω | τ ω ≠ ⊤}).indicator f ω)) ∧
      Tendsto (fun n => ∑ k ∈ Finset.range (4 ^ n),
          (piece τ A W ζ G ψ n k).indicator (cfAt κ W u ψ 1 fun _ => dyT n (k + 1)) ω) atTop
        (𝓝 ((A ∩ {ω | τ ω ≠ ⊤}).indicator (cfAt κ W u ψ 1 fun ω => (τ ω).untopD 0) ω)) := by
  have hlab : ∀ n k ω, ω ∈ piece τ A W ζ G ψ n k → ⌈2 ^ n * (τ ω).untopD 0⌉₊ = k := fun n k ω hω => hω.1.2.2
  filter_upwards [hGae, hτζ] with ω hωG hωζ
  by_cases hωA : ω ∈ A ∩ {ω | τ ω ≠ ⊤}
  · have hne : τ ω ≠ ⊤ := hωA.2
    set a : ℝ≥0 := (τ ω).untopD 0 with ha
    have haζ : (a : ℝ≥0∞) < ζ ω := coe_untopD_lt_zeta hωζ
    obtain ⟨m, hevs, htend⟩ := exists_eventually_isSafeAt_tendsto_cfAt hu ψ (hGp ω hωG) haζ (hAE hωA.1)
      (tendsto_dyT_ceil a)
    have hevC : ∀ᶠ n in atTop, ⌈2 ^ n * a⌉₊ ∈ Finset.range (4 ^ n) ∧
        ω ∈ piece τ A W ζ G ψ n ⌈2 ^ n * a⌉₊ := by
      filter_upwards [eventually_ceil_lt_four_pow a, hevs] with n hn hs
      exact ⟨Finset.mem_range.2 hn, ⟨⟨hωA.1, hne, rfl⟩, mem_safeU_of_isSafeAt hωG hs⟩⟩
    rw [indicator_of_mem hωA, indicator_of_mem hωA]
    refine ⟨tendsto_const_nhds.congr' (hevC.mono fun n hn => ?_), htend.congr' (hevC.mono fun n hn => ?_)⟩
    · beta_reduce
      rw [sum_indicator_eq_of_label (hlab n) ω]
      split_ifs with hc
      · exact (indicator_of_mem hn.2 _).symm
      · exact absurd hn.1 hc
    · beta_reduce
      rw [sum_indicator_eq_of_label (hlab n) ω]
      split_ifs with hc
      · exact (indicator_of_mem hn.2 _).symm
      · exact absurd hn.1 hc
  · have h0 : ∀ n k, ω ∉ piece τ A W ζ G ψ n k := fun n k hω => hωA ⟨hω.1.1, hω.1.2.1⟩
    rw [indicator_of_notMem hωA, indicator_of_notMem hωA]
    exact ⟨tendsto_const_nhds.congr fun n => (Finset.sum_eq_zero fun k _ => indicator_of_notMem (h0 n k) _).symm,
      tendsto_const_nhds.congr fun n => (Finset.sum_eq_zero fun k _ => indicator_of_notMem (h0 n k) _).symm⟩

end Good

/-- **The protected-kernel law at every stopping time from the dyadic times.** For an integrated evolution, a measurable
field satisfying `IsDyadicSampled`, every test function `ψ`, every stopping time `τ < ζ` of the frozen driving
filtration and every event `A ∈ 𝓕_τ` inside `{supp ψ ∩ K_τ = ∅}`: `∫_A e^{i(h,ψ)} = ∫_A cfAt τ`. -/
theorem setIntegral_cexp_eq_cfAt_of_dyadic
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (hh : ∀ ψ, Measurable fun ω => h ω ψ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hdy : IsDyadicSampled κ W u P hX h)
    (ψ : LQGMetric.TestOn upperHalfPlaneOpens) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A)
    (hAE : A ⊆ {ω | Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))}) :
    ∫ ω in A, Complex.exp (Complex.I * (h ω ψ : ℂ)) ∂P =
      ∫ ω in A, cfAt κ W u ψ 1 (fun ω => (τ ω).untopD 0) ω ∂P := by
  classical
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  set 𝓗 := killedDrivingFiltration hX with h𝓗
  set 𝓐 := nullAugmented 𝓗 P with h𝓐
  set f : Ω → ℂ := fun ω => Complex.exp (Complex.I * (h ω ψ : ℂ)) with hf
  have hfm : Measurable f :=
    Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp (hh ψ)))
  have hfb : ∀ ω, ‖f ω‖ ≤ 1 := fun ω => (norm_cexp_I_mul_ofReal _).le
  have hfint : Integrable f P := Integrable.of_bound hfm.aestronglyMeasurable 1 (ae_of_all _ hfb)
  -- the good set
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hE.2.2.2.2)
  set G : Set Ω := Nᶜ with hGdef
  have hGp : ∀ ω ∈ G, IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (fun t => B t ω) (ζ ω) := fun ω hω => by
    by_contra hc
    exact hω (hNsub hc)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    simpa [hGdef] using hN0
  have hG0 : MeasurableSet[𝓐 0] G := (measurableSet_nullAugmented_of_null hNm hN0 0).compl
  have hWa : AdaptedBefore 𝓐 ζ W :=
    adaptedBefore_mono (le_nullAugmented 𝓗 P) (adaptedBefore_killedDriving_W hX)
  have hVLa : ∀ i, AdaptedBefore 𝓐 ζ (VL i) := fun i =>
    adaptedBefore_mono (le_nullAugmented 𝓗 P) (adaptedBefore_killedDriving_VL hX i)
  have hVRa : ∀ i, AdaptedBefore 𝓐 ζ (VR i) := fun i =>
    adaptedBefore_mono (le_nullAugmented 𝓗 P) (adaptedBefore_killedDriving_VR hX i)
  have hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω hω =>
    (hGp ω hω).2.2.2.1
  -- the pieces
  set C : ℕ → ℕ → Set Ω := fun n k => piece τ A W ζ G ψ n k with hC
  have hCm𝓐 : ∀ n k, MeasurableSet[𝓐 (dyT n (k + 1))] (C n k) := fun n k => by
    have h1 : MeasurableSet[𝓐 (dyT n (k + 1))]
        (A ∩ {ω | τ ω ≠ ⊤ ∧ ⌈2 ^ n * (τ ω).untopD 0⌉₊ = k}) :=
      usualAugmentation_le_nullAugmented (P := P) 𝓗 (dyT_lt_dyT_succ n k) _ (measurableSet_piece hτ hA n k)
    have h2 : MeasurableSet[𝓐 (dyT n (k + 1))] (safeU W ζ G ψ (dyT n (k + 1))) :=
      MeasurableSet.iUnion fun m => measurableSet_safeSet hWa hGc hG0 (tsupport_subset_H ψ) (by positivity) _
    exact h1.inter h2
  have hCm : ∀ n k, MeasurableSet (C n k) := fun n k => 𝓐.le _ _ (hCm𝓐 n k)
  have hcfint : ∀ n k, Integrable ((C n k).indicator (cfAt κ W u ψ 1 fun _ => dyT n (k + 1))) P := by
    intro n k
    have e : (C n k).indicator (cfAt κ W u ψ 1 fun _ => dyT n (k + 1)) =
        (C n k).indicator ((safeU W ζ G ψ (dyT n (k + 1))).indicator (cfAt κ W u ψ 1 fun _ => dyT n (k + 1))) := by
      rw [indicator_indicator, inter_eq_left.2 (fun ω hω => hω.2)]
    rw [e]
    refine Integrable.of_bound (((aestronglyMeasurable_safeU_indicator_cfAt hu ψ hGp hG0 hWa hVLa hVRa
      _).indicator (hCm n k))) 1 (ae_of_all _ fun ω => ?_)
    by_cases hω : ω ∈ C n k
    · rw [indicator_of_mem hω, indicator_of_mem hω.2]
      exact norm_cfAt_le_one_of_mem_safeU ψ hGp u hω.2
    · rw [indicator_of_notMem hω, norm_zero]; exact zero_le_one
  -- the dyadic identity, summed over the pieces at level `n`
  have hGF : ∀ n, ∫ ω, ∑ k ∈ Finset.range (4 ^ n), (C n k).indicator f ω ∂P =
      ∫ ω, ∑ k ∈ Finset.range (4 ^ n), (C n k).indicator (cfAt κ W u ψ 1 fun _ => dyT n (k + 1)) ω ∂P := by
    intro n
    rw [integral_finsetSum _ (fun k _ => hfint.indicator (hCm n k)),
      integral_finsetSum _ (fun k _ => hcfint n k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_indicator (hCm n k), integral_indicator (hCm n k)]
    exact hdy ψ n (k + 1) _ (hCm𝓐 n k) fun ω hω => safeU_subset_avoidSet ψ hGp _ hω.2
  -- bounds
  have hlab : ∀ n k ω, ω ∈ C n k → ⌈2 ^ n * (τ ω).untopD 0⌉₊ = k := fun n k ω hω => hω.1.2.2
  have hGb : ∀ n ω, ‖∑ k ∈ Finset.range (4 ^ n), (C n k).indicator f ω‖ ≤ 1 := fun n ω => by
    rw [sum_indicator_eq_of_label (hlab n) ω]
    split_ifs
    · by_cases hω : ω ∈ C n ⌈2 ^ n * (τ ω).untopD 0⌉₊
      · rw [indicator_of_mem hω]; exact hfb ω
      · rw [indicator_of_notMem hω, norm_zero]; exact zero_le_one
    · rw [norm_zero]; exact zero_le_one
  have hFb : ∀ n ω, ‖∑ k ∈ Finset.range (4 ^ n),
      (C n k).indicator (cfAt κ W u ψ 1 fun _ => dyT n (k + 1)) ω‖ ≤ 1 := fun n ω => by
    rw [sum_indicator_eq_of_label (hlab n) ω]
    split_ifs
    · by_cases hω : ω ∈ C n ⌈2 ^ n * (τ ω).untopD 0⌉₊
      · rw [indicator_of_mem hω]; exact norm_cfAt_le_one_of_mem_safeU ψ hGp u hω.2
      · rw [indicator_of_notMem hω, norm_zero]; exact zero_le_one
    · rw [norm_zero]; exact zero_le_one
  -- dominated convergence
  have hpt := ae_tendsto_sum_piece hu ψ hGp f hAE hGae hτζ
  have hlimG := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun n => (integrable_finsetSum _ (fun k _ => hfint.indicator (hCm n k))).aestronglyMeasurable)
    (integrable_const 1) (fun n => ae_of_all _ (hGb n)) (hpt.mono fun ω h => h.1)
  have hlimF := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun n => (integrable_finsetSum _ (fun k _ => hcfint n k)).aestronglyMeasurable)
    (integrable_const 1) (fun n => ae_of_all _ (hFb n)) (hpt.mono fun ω h => h.2)
  have heq := tendsto_nhds_unique (hlimG.congr hGF) hlimF
  have hA'm : MeasurableSet (A ∩ {ω | τ ω ≠ ⊤}) :=
    (hτ.measurableSpace_le _ hA).inter (measurableSet_eq_top_of_isStoppingTime hτ).compl
  rw [integral_indicator hA'm, integral_indicator hA'm] at heq
  have hAA' : A =ᵐ[P] (A ∩ {ω | τ ω ≠ ⊤} : Set Ω) := by
    filter_upwards [hτζ] with ω hω
    exact propext ⟨fun h => ⟨h, ne_top_of_lt_zeta hω⟩, fun h => h.1⟩
  rw [setIntegral_congr_set hAA', setIntegral_congr_set hAA']
  exact heq

/-- **The conditional-law clause of the frozen optional hull specification from the dyadic times**: for a field with
`IsDyadicSampled` and every stopping time `τ < ζ` of the frozen driving filtration, for every test function `φ`, almost
surely on `{supp φ ∩ K_τ = ∅}`, `E[exp(i (h, φ)) | 𝓕_τ] = exp(i (𝔥_τ, φ) − ½ E_τ(φ))` (the proof of
`Coupling.condExp_cexp_eq_frozenRHS_of_family` with `setIntegral_cexp_eq_cfAt_of_dyadic` for the family identity). -/
theorem condExp_cexp_eq_frozenRHS_of_dyadic
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (hh : ∀ ψ, Measurable fun ω => h ω ψ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hdy : IsDyadicSampled κ W u P hX h)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (drivingFiltration P hX) τ)
    (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) (uτ : Ω → ℂ → ℝ)
    (huτ : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) (uτ ω))
    (φ : LQGMetric.TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, Disjoint (tsupport φ)
        (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
      condExp hτ.measurableSpace P (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) ω =
        frozenRHS κ W uτ φ (fun ω => (τ ω).untopD 0) ω := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  set τ' : Ω → ℝ≥0 := fun ω => (τ ω).untopD 0 with hτ'def
  obtain ⟨E', hE'm, hE'sub, hE'ae, hE'mean, hE'path, hE'sm⟩ :=
    exists_drivingStopped_measurable hE hX φ hτ hτζ uτ huτ
  set f : Ω → ℂ := fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) with hf
  have hfm : Measurable f :=
    Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp (hh φ)))
  have hfint : Integrable f P :=
    Integrable.of_bound hfm.aestronglyMeasurable 1
      (ae_of_all _ fun ω => (norm_cexp_I_mul_ofReal _).le)
  set g : Ω → ℂ := E'.indicator (frozenRHS κ W uτ φ τ') with hg
  have hcf : ∀ ω ∈ E', frozenRHS κ W uτ φ τ' ω = cfAt κ W u φ 1 τ' ω := fun ω hω => by
    simp only [frozenRHS, cfAt]
    rw [← hE'mean ω hω (u ω (τ' ω)) (hu ω (τ' ω))]
    congr 1
    push_cast
    ring
  have hgb : ∀ ω, ‖g ω‖ ≤ 1 := fun ω => by
    by_cases hω : ω ∈ E'
    · rw [hg, indicator_of_mem hω, hcf ω hω]
      obtain ⟨h1, h2, h3⟩ := hE'path ω hω
      exact norm_cfAt_le_one u 1 φ (r := τ') h1 h2 h3
    · rw [hg, indicator_of_notMem hω, norm_zero]; exact zero_le_one
  have hgm : StronglyMeasurable[hτ.measurableSpace] g := hE'sm
  have hgint : Integrable g P :=
    Integrable.of_bound ((hgm.mono hτ.measurableSpace_le).aestronglyMeasurable) 1 (ae_of_all _ hgb)
  have hE'mΩ : MeasurableSet E' := hτ.measurableSpace_le _ hE'm
  have key : g =ᵐ[P] condExp hτ.measurableSpace P (E'.indicator f) := by
    refine ae_eq_condExp_of_forall_setIntegral_eq hτ.measurableSpace_le
      (hfint.indicator hE'mΩ) (fun A _ _ => hgint.integrableOn) (fun A hA _ => ?_)
      hgm.aestronglyMeasurable
    have hAm : MeasurableSet A := hτ.measurableSpace_le _ hA
    rw [hg, setIntegral_indicator hE'mΩ, setIntegral_indicator hE'mΩ]
    have hAE : MeasurableSet[hτ.measurableSpace] (A ∩ E') :=
      @MeasurableSet.inter Ω hτ.measurableSpace _ _ hA hE'm
    have hdy' := setIntegral_cexp_eq_cfAt_of_dyadic hE u hu h hh hX hdy φ hτ hτζ hAE
      (inter_subset_right.trans hE'sub)
    rw [hdy']
    refine setIntegral_congr_fun (hAm.inter hE'mΩ) fun ω hω => ?_
    exact hcf ω hω.2
  have hind := condExp_indicator (m := hτ.measurableSpace) (μ := P) hfint hE'm
  filter_upwards [key, hind, hE'ae] with ω h1 h2 h3 hdis
  have hω : ω ∈ E' := h3 hdis
  have e1 : condExp hτ.measurableSpace P f ω =
      E'.indicator (condExp hτ.measurableSpace P f) ω := (indicator_of_mem hω _).symm
  rw [e1, ← h2, ← h1, hg, indicator_of_mem hω]

/-- **The frozen optional hull specification from the dyadic times**, given locality of `K_τ` at every frozen stopping
time (conditional helper; the locality input is a separate obligation): an integrated evolution, a measurable field with
the GFF law of the initial data, and the protected-kernel law at the dyadic times form an optional hull coupling. -/
theorem isOptionalHullCoupling_of_dyadic
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (hgff : ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR)
        (forceJumpSet xL xR) u₀ →
      LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => h ω φ - ∫ z, u₀ z * φ z) P)
    (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
    (hdy : ∀ hX : IsMeasurableKilledDriving W VL VR ζ, IsDyadicSampled κ W u P hX h)
    (hloc : ∀ (hX : IsMeasurableKilledDriving W VL VR ζ) (τ : Ω → WithTop ℝ≥0),
      IsStoppingTime (drivingFiltration P hX) τ → (∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) →
        IsLocalSet (fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) h P) :
    IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h := by
  have hX := IsIntegratedSLEEvolution.isMeasurableKilledDriving hE
  have hh' : ∀ ψ, Measurable fun ω => h ω ψ := fun ψ => (LQGMetric.measurable_distOn_apply ψ).comp hh
  exact ⟨hE, hh, hgff, hX, fun τ hτ hτζ => ⟨hloc hX τ hτ hτζ, fun uτ huτ φ =>
    condExp_cexp_eq_frozenRHS_of_dyadic hE u hu h hh' hX (hdy hX) hτ hτζ uτ huτ φ⟩⟩

end Main

end DomainMarkov

end Restart

end InteractingSLE
