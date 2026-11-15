/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TwoForceMain3Prop73
import InteractingSLE.Spec.Sec7.CounterflowProbDilation

/-!
# Proposition LP4, deterministic part: the terminal cluster set and its modulus

Packet PROVE-LP14. Supplement §6.3, proof of Proposition LP4 (`source/spec/p481-528.md` L64–L70, p. 483): "Let
`Q = ⋂_{n ≥ 1} closure(η([n, ∞)))` (closure in the Riemann sphere). The event `0 ∉ Q` is a measurable
dilation-invariant event of the full canonical driving law. […] Set `Z = inf{|z| : z ∈ Q ∩ ℂ}`, `inf ∅ = ∞`. The
absence of `0` and compactness of `Q` give `Z > 0`. Exact dilation invariance of the trace law gives `Z =ᵈ aZ` for
every `a > 0`. […] Thus `Q = {∞}` and `η(t) → ∞`."

This file proves the deterministic statements behind these sentences, for a continuous path `η : [0, ∞) → ℂ`:

* `terminalClusterSet η = ⋂_n closure(η([n, ∞)))`, the finite part `Q ∩ ℂ` of `Q` (a point of `ℂ` lies in the
  spherical closure of a set of `ℂ` iff it lies in its closure in `ℂ`);
* `terminalModulus η = sup_r inf_{t ≥ r} ‖η t‖ = liminf_{t → ∞} ‖η t‖ ∈ [0, ∞]`, which is LP4's `Z`
  (`terminalModulus_le_enorm_of_mem`, `exists_mem_terminalClusterSet_enorm_eq`, `terminalModulus_eq_iInf`): the least
  modulus of a finite cluster point, `∞` if there is none;
* `terminalModulus_pos_of_notMem` ("the absence of `0` […] give[s] `Z > 0`");
* `tendsto_norm_of_terminalModulus_eq_top` (`Z = ∞` means `Q = {∞}`, i.e. `η(t) → ∞`);
* `terminalModulus_dilate`: under the dilation `t ↦ s η(t/s²)` (here `s = (√c)⁻¹`, Mathlib's Brownian scaling
  convention, as in `IsGeneratingTrace.dilate`), `Z` is multiplied by `s`;
* the measurable coding: `ratTerminalModulus` is a measurable function of the rational-time values of the driver
  (through the measurable trace evaluation `traceAt` and the extension `Sec7.extendRat`), and equals `terminalModulus η`
  for the generating trace `η` of every continuous driver vanishing at `0` (`ratTerminalModulus_eq`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal NNRat

namespace InteractingSLE.LP

/-! ### The terminal cluster set and its modulus -/

/-- The finite part `Q ∩ ℂ = ⋂_{n ≥ 1} closure(η([n, ∞)))` of LP4's terminal cluster set (the index `n = 0` adds the
whole range, which contains the others, and does not change the intersection). -/
def terminalClusterSet (η : ℝ≥0 → ℂ) : Set ℂ := ⋂ n : ℕ, closure (η '' Ici (n : ℝ≥0))

/-- The tail infimum `inf_{t ≥ r} ‖η t‖`. -/
def tailInf (η : ℝ≥0 → ℂ) (r : ℝ≥0) : ℝ≥0∞ := ⨅ t : {t : ℝ≥0 // r ≤ t}, ‖η t‖ₑ

/-- **LP4's `Z`**: the terminal modulus `liminf_{t → ∞} ‖η t‖ = sup_r inf_{t ≥ r} ‖η t‖ ∈ [0, ∞]`. -/
def terminalModulus (η : ℝ≥0 → ℂ) : ℝ≥0∞ := ⨆ r : ℝ≥0, tailInf η r

theorem tailInf_mono (η : ℝ≥0 → ℂ) : Monotone (tailInf η) := fun _ _ h =>
  le_iInf fun t => iInf_le (fun s : {s : ℝ≥0 // _ ≤ s} => ‖η s‖ₑ) ⟨t.1, h.trans t.2⟩

theorem tailInf_le_terminalModulus (η : ℝ≥0 → ℂ) (r : ℝ≥0) : tailInf η r ≤ terminalModulus η :=
  le_iSup (tailInf η) r

/-- The terminal modulus is the supremum over integer thresholds. -/
theorem terminalModulus_eq_iSup_nat (η : ℝ≥0 → ℂ) :
    terminalModulus η = ⨆ n : ℕ, tailInf η n := by
  refine le_antisymm (iSup_le fun r => ?_) (iSup_le fun n => le_iSup (tailInf η) (n : ℝ≥0))
  obtain ⟨n, hn⟩ := exists_nat_ge r
  exact (tailInf_mono η hn).trans (le_iSup (fun n : ℕ => tailInf η n) n)

/-- **`Z > 0` from the absence of `0`** (LP4, p. 483: "The absence of `0` and compactness of `Q` give `Z > 0`"). -/
theorem terminalModulus_pos_of_notMem {η : ℝ≥0 → ℂ} (h : (0 : ℂ) ∉ terminalClusterSet η) :
    0 < terminalModulus η := by
  simp only [terminalClusterSet, mem_iInter, not_forall] at h
  obtain ⟨n, hn⟩ := h
  rw [Metric.mem_closure_iff] at hn
  push Not at hn
  obtain ⟨ε, hε, hb⟩ := hn
  have hinf : ENNReal.ofReal ε ≤ tailInf η n := le_iInf fun t => by
    have h1 := hb (η t) (mem_image_of_mem η (show (t : ℝ≥0) ∈ Ici (n : ℝ≥0) from t.2))
    rw [dist_zero_left] at h1
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal h1
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 hε) (hinf.trans (tailInf_le_terminalModulus η n))

/-- **`Z = ∞` means `η(t) → ∞`** (LP4, p. 483: "Thus `Q = {∞}` and `η(t) → ∞`"). -/
theorem tendsto_norm_of_terminalModulus_eq_top {η : ℝ≥0 → ℂ} (h : terminalModulus η = ⊤) :
    Tendsto (fun t => ‖η t‖) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun b => ?_
  have hlt : ENNReal.ofReal b < ⨆ r, tailInf η r := by
    rw [← terminalModulus, h]; exact ENNReal.ofReal_lt_top
  obtain ⟨r, hr⟩ := lt_iSup_iff.1 hlt
  refine ⟨r, fun t ht => ?_⟩
  have h1 : ENNReal.ofReal b < ‖η t‖ₑ := lt_of_lt_of_le hr (iInf_le (fun s : {s : ℝ≥0 // r ≤ s} => ‖η s‖ₑ)
    ⟨t, ht⟩)
  rw [← ofReal_norm] at h1
  rcases le_or_gt b 0 with hb | hb
  · exact hb.trans (norm_nonneg _)
  · exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hb.le).1 h1).le

/-- Every finite cluster point has modulus at least `Z`. -/
theorem terminalModulus_le_enorm_of_mem {η : ℝ≥0 → ℂ} {z : ℂ} (hz : z ∈ terminalClusterSet η) :
    terminalModulus η ≤ ‖z‖ₑ := by
  rw [terminalModulus_eq_iSup_nat]
  refine iSup_le fun n => ?_
  have hz' : z ∈ closure (η '' Ici (n : ℝ≥0)) := mem_iInter.1 hz n
  have hsub : η '' Ici (n : ℝ≥0) ⊆ {y : ℂ | tailInf η n ≤ ‖y‖ₑ} := by
    rintro _ ⟨t, ht, rfl⟩
    exact iInf_le (fun s : {s : ℝ≥0 // (n : ℝ≥0) ≤ s} => ‖η s‖ₑ) ⟨t, ht⟩
  have hcl : IsClosed {y : ℂ | tailInf η n ≤ ‖y‖ₑ} := isClosed_le continuous_const continuous_enorm
  exact (closure_minimal hsub hcl) hz'

/-- If `Z < ∞`, some finite cluster point has modulus exactly `Z` (`Q ∩ ℂ` is closed and the tail values of modulus
close to `Z` are bounded, hence have a convergent subsequence). -/
theorem exists_mem_terminalClusterSet_enorm_eq {η : ℝ≥0 → ℂ} (hL : terminalModulus η ≠ ⊤) :
    ∃ z ∈ terminalClusterSet η, ‖z‖ₑ = terminalModulus η := by
  set L := terminalModulus η with hLdef
  -- a time `t n ≥ n` with `‖η (t n)‖ < L + 1/(n+1)`
  have hex : ∀ n : ℕ, ∃ t : ℝ≥0, (n : ℝ≥0) ≤ t ∧ ‖η t‖ₑ < L + ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    have hlt : tailInf η n < L + ((n : ℝ≥0∞) + 1)⁻¹ :=
      lt_of_le_of_lt (tailInf_le_terminalModulus η n)
        (ENNReal.lt_add_right hL (ENNReal.inv_ne_zero.2 (by simp)))
    obtain ⟨t, ht⟩ := iInf_lt_iff.1 hlt
    exact ⟨t.1, t.2, ht⟩
  choose t ht using hex
  have hbound : ∀ n, ‖η (t n)‖ ≤ L.toReal + 1 := by
    intro n
    have h1 : ‖η (t n)‖ₑ < ENNReal.ofReal (L.toReal + 1) := by
      refine lt_of_lt_of_le (ht n).2 ?_
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one, ENNReal.ofReal_toReal hL, ENNReal.ofReal_one]
      gcongr
      exact ENNReal.inv_le_one.2 le_add_self
    rw [← ofReal_norm] at h1
    exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)).1 h1).le
  obtain ⟨z, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : ℂ) (L.toReal + 1)).tendsto_subseq
    (x := fun n => η (t n)) fun n => mem_closedBall_zero_iff.2 (hbound n)
  refine ⟨z, mem_iInter.2 fun m => ?_, le_antisymm ?_ (terminalModulus_le_enorm_of_mem ?_)⟩
  · refine mem_closure_of_tendsto hlim (Filter.eventually_atTop.2 ⟨m, fun k hk => ?_⟩)
    refine ⟨t (φ k), ?_, rfl⟩
    exact le_trans (Nat.cast_le.2 (hk.trans (hφ.id_le k))) (ht (φ k)).1
  · have hz := (continuous_enorm.tendsto z).comp hlim
    have hR : Tendsto (fun k : ℕ => L + ((k : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 (L + 0)) := by
      refine tendsto_const_nhds.add ?_
      have h := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
      simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using h
    rw [add_zero] at hR
    refine le_of_tendsto_of_tendsto' hz hR fun k => ?_
    refine ((ht (φ k)).2.le).trans (add_le_add_right (ENNReal.inv_le_inv.2 ?_) L)
    exact add_le_add_left (Nat.cast_le.2 (hφ.id_le k)) 1
  · refine mem_iInter.2 fun m => mem_closure_of_tendsto hlim (Filter.eventually_atTop.2 ⟨m, fun k hk => ?_⟩)
    exact ⟨t (φ k), le_trans (Nat.cast_le.2 (hk.trans (hφ.id_le k))) (ht (φ k)).1, rfl⟩

/-- **LP4's `Z = inf{|z| : z ∈ Q ∩ ℂ}`, `inf ∅ = ∞`** (p. 483): the terminal modulus is the least modulus of a finite
terminal cluster point. -/
theorem terminalModulus_eq_iInf (η : ℝ≥0 → ℂ) :
    terminalModulus η = ⨅ z ∈ terminalClusterSet η, ‖z‖ₑ := by
  refine le_antisymm (le_iInf₂ fun z hz => terminalModulus_le_enorm_of_mem hz) ?_
  rcases eq_or_ne (terminalModulus η) ⊤ with h | h
  · rw [h]; exact le_top
  · obtain ⟨z, hz, hzL⟩ := exists_mem_terminalClusterSet_enorm_eq h
    exact (iInf₂_le z hz).trans hzL.le

/-! ### Dilation -/

section Dilation

open Sec7.Dilation

variable {c : ℝ≥0}

/-- Reindexing a tail infimum by `t ↦ c t`. -/
theorem iInf_comp_mul_eq (hc : c ≠ 0) (f : ℝ≥0 → ℝ≥0∞) (r : ℝ≥0) :
    ⨅ t : {t : ℝ≥0 // r ≤ t}, f (c * t) = ⨅ u : {u : ℝ≥0 // c * r ≤ u}, f u := by
  have hc0 : 0 < c := pos_iff_ne_zero.2 hc
  refine le_antisymm (le_iInf fun u => ?_) (le_iInf fun t => ?_)
  · have hu : r ≤ u.1 / c := (le_div_iff₀ hc0).2 (by rw [mul_comm]; exact u.2)
    refine iInf_le_of_le ⟨u.1 / c, hu⟩ ?_
    rw [mul_div_cancel₀ _ hc]
  · exact iInf_le_of_le ⟨c * t.1, mul_le_mul_of_nonneg_left t.2 c.2⟩ le_rfl

/-- **The terminal modulus under dilation**: for `s = (√c)⁻¹`, the dilated path `t ↦ s η(ct)` has terminal modulus
`s Z`. -/
theorem terminalModulus_dilate (hc : c ≠ 0) (η : ℝ≥0 → ℂ) :
    terminalModulus (fun t => (((√(c : ℝ))⁻¹ : ℝ) : ℂ) * η (c * t)) =
      ‖(((√(c : ℝ))⁻¹ : ℝ) : ℂ)‖ₑ * terminalModulus η := by
  set k : ℝ≥0∞ := ‖(((√(c : ℝ))⁻¹ : ℝ) : ℂ)‖ₑ with hk
  have hk0 : k ≠ 0 := by
    rw [hk, enorm_ne_zero]
    exact_mod_cast inv_sqrt_ne_zero hc
  have hktop : k ≠ ⊤ := enorm_ne_top
  have hc0 : 0 < c := pos_iff_ne_zero.2 hc
  have htail : ∀ r, tailInf (fun t => (((√(c : ℝ))⁻¹ : ℝ) : ℂ) * η (c * t)) r = k * tailInf η (c * r) := by
    intro r
    simp only [tailInf, enorm_mul]
    rw [← ENNReal.mul_iInf_of_ne hk0 hktop]
    congr 1
    exact iInf_comp_mul_eq hc (fun u => ‖η u‖ₑ) r
  simp only [terminalModulus, htail]
  rw [← ENNReal.mul_iSup]
  congr 1
  refine le_antisymm (iSup_le fun r => le_iSup (tailInf η) (c * r)) (iSup_le fun r => ?_)
  refine le_iSup_of_le (r / c) ?_
  rw [mul_div_cancel₀ _ hc]

end Dilation

/-! ### The measurable coding of `Z` -/

section Coding

open Sec7

/-- The tail infimum at an integer threshold is the infimum over the rational times above it, for a continuous
path. -/
theorem tailInf_nat_eq_rat {η : ℝ≥0 → ℂ} (hη : Continuous η) (n : ℕ) :
    tailInf η n = ⨅ q : {q : ℚ≥0 // (n : ℚ≥0) ≤ q}, ‖η (q.1 : ℝ≥0)‖ₑ := by
  refine le_antisymm (le_iInf fun q => ?_) (le_iInf fun t => ?_)
  · have hq : (n : ℝ≥0) ≤ ((q.1 : ℚ≥0) : ℝ≥0) := by
      rw [← NNRat.cast_natCast (α := ℝ≥0)]
      exact NNRat.cast_le.2 q.2
    exact iInf_le (fun s : {s : ℝ≥0 // (n : ℝ≥0) ≤ s} => ‖η s‖ₑ) ⟨_, hq⟩
  · have hlim := (continuous_enorm.tendsto (η t)).comp ((hη.tendsto t).comp (tendsto_ratAbove t))
    refine ge_of_tendsto hlim (Eventually.of_forall fun k => ?_)
    have hq : (n : ℚ≥0) ≤ ratAbove t k := by
      rw [← NNRat.cast_le (K := ℝ≥0), NNRat.cast_natCast]
      exact t.2.trans (le_ratAbove t k)
    exact iInf_le (fun q : {q : ℚ≥0 // (n : ℚ≥0) ≤ q} => ‖η (q.1 : ℝ≥0)‖ₑ) ⟨_, hq⟩

/-- **The coded terminal modulus**: `sup_n inf_{q ≥ n rational} ‖traceAt q (extendRat v)‖`, a function of the
rational-time values `v` of a driver. -/
def ratTerminalModulus (v : ℚ≥0 → ℝ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨅ q : {q : ℚ≥0 // (n : ℚ≥0) ≤ q}, ‖traceAt (q.1 : ℝ≥0) (extendRat v)‖ₑ

theorem measurable_ratTerminalModulus : Measurable ratTerminalModulus :=
  Measurable.iSup fun _ => Measurable.iInf fun q =>
    measurable_enorm.comp ((measurable_traceAt (q.1 : ℝ≥0)).comp measurable_extendRat)

/-- **The coding identity**: for a continuous driver vanishing at `0` with a continuous generating trace `η` on
`[0, ∞)`, the coded terminal modulus of its rational-time values is `Z(η)`. -/
theorem ratTerminalModulus_eq {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) : ratTerminalModulus (fun q : ℚ≥0 => w q) = terminalModulus η := by
  have hηc : Continuous η := continuousOn_univ.1 (by simpa using hη.2.1)
  have htr : ∀ s : ℝ≥0, traceAt s w = η s := fun s =>
    traceAt_eq_of_isGeneratingTrace hη hw.continuousOn hw0 ENNReal.coe_lt_top
  rw [terminalModulus_eq_iSup_nat, ratTerminalModulus, extendRat_eq hw]
  refine iSup_congr fun n => ?_
  rw [tailInf_nat_eq_rat hηc n]
  simp only [htr]

end Coding

end InteractingSLE.LP
