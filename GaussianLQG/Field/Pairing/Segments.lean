import GaussianLQG.Core.Setup
import GaussianLQG.Core.Interfaces
import GaussianLQG.Field.Pairing.Linear
import GaussianLQG.Probability.Kolmogorov

/-!
# Regularity of the segment pairings `H(s, t)` (blueprint Lemma `lem:H-continuity`)

For `S : Setup`, `H(s,t) = (h, λ_{is, 1+it})` (`Setup.H`) and `M = inf_{y ∈ 𝔻} H(y,y)`
(`Setup.M`).

* (a) `Setup.integral_sq_H_sub_le`: `E|H(s,t) - H(s',t')|² ≤ 6 a^{1/2}` with
  `a = |s - s'| ∨ |t - t'|`, and `Setup.variance_H_le`: `Var H(s,t) ≤ 3/2 + log 2`
  (`s, t, s', t' ∈ [0, 1]`); both from the Gaussian law of differences of pairings and blueprint
  Lemma `lem:segments`(c),(d).
* (b) `Setup.exists_continuous_modification_H`: `y ↦ H(y, y)` has a modification on `[0, 1]` with
  continuous paths (Kolmogorov–Chentsov, Gaussian increments of variance `≤ 6 |y - y'|^{1/2}`);
  `Setup.exists_continuous_modification_H2`: the two-parameter version on `[0, 1]²`.
* (c) `Setup.measurable_M'`, and `Setup.ae_M_eq_min`: for any such continuous modification `X`,
  almost surely `{H(y,y) : y ∈ 𝔻}` is bounded below and `M = min_{y ∈ [0,1]} X y`;
  `Setup.exists_ae_M_eq_min` packages existence and the identity; `Setup.ae_bddBelow_H_dyadic`.
* `Setup.h00Law`: the interface proposition `Setup.H00Law`, `H(0,0) ∼ N(0, 3/2)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GaussianLQG

/-- The segment measure `λ_{is, 1+it}`. -/
abbrev segST (s t : ℝ) : Measure ℂ := segMeasure ((s : ℂ) * Complex.I) (1 + (t : ℂ) * Complex.I)

theorem isRegular_segST (s t : ℝ) : IsRegular (segST s t) :=
  isRegular_segMeasure (sI_ne_one_add_tI s t)

/-! ## Dyadic rationals -/

theorem dyadicUnit_subset_Icc : Setup.dyadicUnit ⊆ Icc (0 : ℝ) 1 := by
  rintro y ⟨n, k, hk, rfl⟩
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  refine ⟨by positivity, (div_le_one h2).2 ?_⟩
  exact_mod_cast hk

theorem dyadicUnit_countable : Setup.dyadicUnit.Countable := by
  refine (Set.countable_range fun p : ℕ × ℕ => (p.2 : ℝ) / 2 ^ p.1).mono ?_
  rintro y ⟨n, k, -, rfl⟩
  exact ⟨(n, k), rfl⟩

instance countableDyadicUnit : Countable Setup.dyadicUnit := dyadicUnit_countable.to_subtype

theorem zero_mem_dyadicUnit : (0 : ℝ) ∈ Setup.dyadicUnit := ⟨0, 0, by simp, by simp⟩

instance nonemptyDyadicUnit : Nonempty Setup.dyadicUnit := ⟨⟨0, zero_mem_dyadicUnit⟩⟩

/-- The dyadic rationals are dense in `[0, 1]`. -/
theorem Icc_subset_closure_dyadicUnit : Icc (0 : ℝ) 1 ⊆ closure Setup.dyadicUnit := by
  intro y hy
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hy0 : 0 ≤ 2 ^ n * y := mul_nonneg h2.le hy.1
  refine ⟨(⌊2 ^ n * y⌋₊ : ℝ) / 2 ^ n, ⟨n, ⌊2 ^ n * y⌋₊, ?_, rfl⟩, ?_⟩
  · have h3 : (⌊2 ^ n * y⌋₊ : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by
      push_cast
      nlinarith [Nat.floor_le hy0, hy.2]
    exact_mod_cast h3
  · have hfl := Nat.floor_le hy0
    have hlt := Nat.lt_floor_add_one (2 ^ n * y)
    rw [Real.dist_eq, abs_lt]
    have e1 : (1 / 2 : ℝ) ^ n = 1 / 2 ^ n := by rw [one_div_pow]
    rw [e1] at hn
    constructor
    · have : (⌊2 ^ n * y⌋₊ : ℝ) / 2 ^ n ≤ y := by
        rw [div_le_iff₀ h2]; linarith
      linarith
    · have : y - (⌊2 ^ n * y⌋₊ : ℝ) / 2 ^ n < 1 / 2 ^ n := by
        rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ h2]; linarith
      linarith

namespace Setup

variable (S : Setup)

theorem measurable_H (s t : ℝ) : Measurable (S.H s t) := measurable_pairing _ _

/-- `H(s,t) ∼ N(0, ℰ(λ_{is,1+it}, λ_{is,1+it}))`. -/
theorem hasLaw_H (s t : ℝ) :
    HasLaw (S.H s t) (gaussianReal 0 (energy (segST s t) (segST s t)).toNNReal) stdP :=
  hasLaw_pairing S.frame (isRegular_segST s t)

/-- `H(s,t) - H(s',t')` is a centered Gaussian with variance `‖λ_{is,1+it} - λ_{is',1+it'}‖_*²`. -/
theorem hasLaw_H_sub (s t s' t' : ℝ) :
    HasLaw (fun ω => S.H s t ω - S.H s' t' ω)
      (gaussianReal 0 (energy (segST s t) (segST s t) - 2 * energy (segST s t) (segST s' t') +
        energy (segST s' t') (segST s' t')).toNNReal) stdP :=
  hasLaw_pairing_sub S.frame (isRegular_segST s t) (isRegular_segST s' t')

/-! ## (a) Second moments -/

/-- **Lemma `lem:H-continuity`(a)**: `E|H(s,t) - H(s',t')|² ≤ 6 a^{1/2}`,
`a = |s - s'| ∨ |t - t'|`. -/
theorem integral_sq_H_sub_le {s t s' t' : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hs' : s' ∈ Icc (0 : ℝ) 1) (ht' : t' ∈ Icc (0 : ℝ) 1) :
    ∫ ω, (S.H s t ω - S.H s' t' ω) ^ 2 ∂stdP ≤ 6 * (max |s - s'| |t - t'|) ^ (1 / 2 : ℝ) := by
  rw [show (fun ω => (S.H s t ω - S.H s' t' ω) ^ 2) =
      fun ω => (pairing S.e (segST s t) ω - pairing S.e (segST s' t') ω) ^ 2 from rfl,
    integral_sq_pairing_sub S.frame (isRegular_segST s t) (isRegular_segST s' t')]
  exact energy_segMeasure_sub_le hs ht hs' ht'

/-- **Lemma `lem:H-continuity`(a)**: `Var H(s,t) ≤ 3/2 + log 2`. -/
theorem variance_H_le {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    Var[S.H s t; stdP] ≤ 3 / 2 + Real.log 2 := by
  rw [variance_of_hasLaw_gaussianReal (S.hasLaw_H s t),
    Real.coe_toNNReal _ (S.frame.energy_nonneg (isRegular_segST s t))]
  exact energy_segMeasure_sI_le hs ht

/-! ## (b) A continuous modification of the diagonal -/

/-- **Lemma `lem:H-continuity`(b)**: `y ↦ H(y, y)` has a modification on `[0, 1]` with
continuous paths. -/
theorem exists_continuous_modification_H :
    ∃ X : ℝ → Coord → ℝ, (∀ ω, Continuous fun y => X y ω) ∧
      ∀ y ∈ Icc (0 : ℝ) 1, X y =ᵐ[stdP] fun ω => S.H y y ω := by
  refine exists_continuous_modification_Icc_of_hasLaw (C := 6) (α := 1 / 2) (by norm_num)
    (by norm_num) (fun y _ => (S.measurable_H y y).aemeasurable) fun y hy y' hy' => ?_
  refine ⟨_, ?_, S.hasLaw_H_sub y y y' y'⟩
  rw [Real.coe_toNNReal']
  refine max_le ?_ (by positivity)
  have h := energy_segMeasure_sub_le hy hy hy' hy'
  rwa [max_self] at h

/-- **Lemma `lem:H-continuity`(b)**, two-parameter form: `(H(s,t))_{(s,t) ∈ [0,1]²}` has a
modification with jointly continuous paths. -/
theorem exists_continuous_modification_H2 :
    ∃ Y : ℝ → ℝ → Coord → ℝ, (∀ ω, Continuous fun p : ℝ × ℝ => Y p.1 p.2 ω) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, Y s t =ᵐ[stdP] S.H s t := by
  refine exists_continuous_modification_Icc2_of_hasLaw (C := 6) (α := 1 / 2) (by norm_num)
    (by norm_num) (fun s _ t _ => (S.measurable_H s t).aemeasurable)
    fun s hs t ht s' hs' t' ht' => ⟨_, ?_, S.hasLaw_H_sub s t s' t'⟩
  rw [Real.coe_toNNReal']
  exact max_le (energy_segMeasure_sub_le hs ht hs' ht') (by positivity)

/-! ## (c) `M` as a minimum -/

theorem measurable_M' : Measurable S.M :=
  Measurable.iInf fun y => S.measurable_H y y

/-- **Lemma `lem:H-continuity`(c)**: for any modification `X` of `y ↦ H(y,y)` on `[0,1]` with
continuous paths, almost surely `{H(y,y) : y ∈ 𝔻}` is bounded below and
`M = min_{y ∈ [0,1]} X y`. -/
theorem ae_M_eq_min {X : ℝ → Coord → ℝ} (hXc : ∀ ω, Continuous fun y => X y ω)
    (hXH : ∀ y ∈ Icc (0 : ℝ) 1, X y =ᵐ[stdP] fun ω => S.H y y ω) :
    ∀ᵐ ω ∂stdP, BddBelow (range fun y : dyadicUnit => S.H y y ω) ∧
      IsLeast ((fun y => X y ω) '' Icc 0 1) (S.M ω) := by
  have hae : ∀ᵐ ω ∂stdP, ∀ y : dyadicUnit, X y ω = S.H y y ω :=
    ae_all_iff.2 fun y => hXH y (dyadicUnit_subset_Icc y.2)
  filter_upwards [hae] with ω hω
  have hcomp : IsCompact ((fun y => X y ω) '' Icc 0 1) :=
    isCompact_Icc.image (hXc ω)
  have hrange : range (fun y : dyadicUnit => S.H y y ω) ⊆ (fun y => X y ω) '' Icc 0 1 := by
    rintro _ ⟨y, rfl⟩
    exact ⟨y, dyadicUnit_subset_Icc y.2, hω y⟩
  have hbdd : BddBelow (range fun y : dyadicUnit => S.H y y ω) :=
    hcomp.bddBelow.mono hrange
  refine ⟨hbdd, ?_, ?_⟩
  · -- the infimum is attained
    obtain ⟨m, hm, hmin⟩ := hcomp.exists_isLeast
      ((nonempty_Icc.2 zero_le_one).image fun y => X y ω)
    have hle : m ≤ S.M ω := le_ciInf fun y => hmin (hrange ⟨y, rfl⟩)
    have hge : S.M ω ≤ m := by
      obtain ⟨y₀, hy₀, rfl⟩ := hm
      have h1 : X y₀ ω ∈ closure ((fun y => X y ω) '' dyadicUnit) :=
        ((hXc ω).continuousAt.continuousWithinAt).mem_closure_image
          (Icc_subset_closure_dyadicUnit hy₀)
      have h2 : (fun y => X y ω) '' dyadicUnit ⊆ Ici (S.M ω) := by
        rintro _ ⟨y, hy, rfl⟩
        show S.M ω ≤ X y ω
        rw [show X y ω = S.H y y ω from hω ⟨y, hy⟩]
        exact ciInf_le hbdd ⟨y, hy⟩
      exact closure_minimal h2 isClosed_Ici h1
    rw [le_antisymm hge hle]
    exact hm
  · rintro _ ⟨y, hy, rfl⟩
    have hge : S.M ω ≤ X y ω := by
      have h1 : X y ω ∈ closure ((fun y => X y ω) '' dyadicUnit) :=
        ((hXc ω).continuousAt.continuousWithinAt).mem_closure_image
          (Icc_subset_closure_dyadicUnit hy)
      have h2 : (fun y => X y ω) '' dyadicUnit ⊆ Ici (S.M ω) := by
        rintro _ ⟨y', hy', rfl⟩
        show S.M ω ≤ X y' ω
        rw [show X y' ω = S.H y' y' ω from hω ⟨y', hy'⟩]
        exact ciInf_le hbdd ⟨y', hy'⟩
      exact closure_minimal h2 isClosed_Ici h1
    exact hge

/-- **Lemma `lem:H-continuity`(b),(c)**: a continuous modification `X` of `y ↦ H(y,y)` on
`[0,1]` exists, and almost surely `M = min_{y ∈ [0,1]} X y ∈ ℝ`. -/
theorem exists_ae_M_eq_min :
    ∃ X : ℝ → Coord → ℝ, (∀ ω, Continuous fun y => X y ω) ∧
      (∀ y ∈ Icc (0 : ℝ) 1, X y =ᵐ[stdP] fun ω => S.H y y ω) ∧
      ∀ᵐ ω ∂stdP, BddBelow (range fun y : dyadicUnit => S.H y y ω) ∧
        IsLeast ((fun y => X y ω) '' Icc 0 1) (S.M ω) := by
  obtain ⟨X, hXc, hXH⟩ := S.exists_continuous_modification_H
  exact ⟨X, hXc, hXH, S.ae_M_eq_min hXc hXH⟩

/-- Almost surely `{H(y,y) : y ∈ 𝔻}` is bounded below, so `M ≤ H(y,y)` for every dyadic `y`. -/
theorem ae_M_le_H : ∀ᵐ ω ∂stdP, ∀ y ∈ dyadicUnit, S.M ω ≤ S.H y y ω := by
  obtain ⟨X, hXc, hXH, hae⟩ := S.exists_ae_M_eq_min
  filter_upwards [hae] with ω hω y hy
  exact ciInf_le hω.1 ⟨y, hy⟩

/-- **Lemma `lem:H-continuity`(c)**: almost surely `{H(y,y) : y ∈ 𝔻}` is bounded below, so
`M ∈ ℝ` is a genuine infimum. -/
theorem ae_bddBelow_H_dyadic :
    ∀ᵐ ω ∂stdP, BddBelow (range fun y : dyadicUnit => S.H y y ω) := by
  obtain ⟨X, hXc, hXH, hae⟩ := S.exists_ae_M_eq_min
  filter_upwards [hae] with ω hω
  exact hω.1

/-- `H(0,0) = (h, λ_{0,1})`. -/
theorem H_zero_zero : S.H 0 0 = pairing S.e (segMeasure 0 1) := by
  unfold H
  simp only [Complex.ofReal_zero, zero_mul, add_zero]

/-- **Lemma `lem:field`(b) with Lemma `lem:segments`(a)**: `H(0,0) ∼ N(0, 3/2)` (the interface
proposition `Setup.H00Law`). -/
theorem h00Law : S.H00Law := by
  unfold H00Law
  rw [H_zero_zero, (hasLaw_pairing S.frame (isRegular_segMeasure zero_ne_one)).map_eq,
    energy_segMeasure_zero_one]
  congr 1
  apply NNReal.eq
  rw [Real.coe_toNNReal _ (by norm_num)]
  norm_num

end Setup

end GaussianLQG
