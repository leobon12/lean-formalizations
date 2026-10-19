import HigherDimLFPP.Upper.RecordLaw
import LQGDimension.LFPP.RecordVarianceAux3

/-!
# Record variances: HA3 D6 (iii) and the variance bound (4.18)

Source: `source/higher-dimensional-lfpp-limit.pdf`, §4.3, Lemma 4.4 ((4.18), (4.19)), as corrected
by the planning audit HA3 (`planning/audits/HA3-section-4.md`), Details D6 (iii) (with the fix F1:
the record families carry the chord-length constraints); ruling H7.

**Statement** (`exists_chain_variance_bound`, packet P-U3 target T2).  There is `C_V = C_V(d, κ)`
such that for every `n ≥ 3` there is `C'_V = C'_V(n, d, κ)` with: for every band `(a, b)`,
`0 < a ≤ b` (in particular the cutoff `(ε, 1)` for every `ε`), every `δ > 0`, every chain record
`(ρ_0, …, ρ_{l-1})` of valid records and every choice `c_i ∈ Φ(ρ_i)`,
`Var(Σ_i Y_i(c_i)) ≤ C_V Σ_{i good} √(k_i + 1) + C'_V m_b / δ`
(`variance_chain_le`; `m_b` is the number of bad records).  `C_V` does not depend on `n`.

**Proof** (HA3 D6 (iii)).
* Pair data (`pairData_of_mem_family`): for a good record in bin `k`, the chord measure and the
  polygon measure have the growth bound (3.4) with constant `3` at the scale `R = |y - x|` of the
  chord and a displacement coupling of size `R · 2δ√(k+1)` (HA3 D4 (a), (b)); for a bad record the
  two chord measures have the growth bound with constant `4K` at scale `R` (the adverse chord is
  longer than `R/(2K)`) and a coupling of size `R (ρ₀ + 1)`.
* Lemma 3.1 (`transport_cov_bound`) and the Itô isometry `inner_cfgVec` give
  `|Cov(Y_i, Y_ℓ)| ≤ δ⁻¹ C_B √(u_i u_ℓ) / R_i` for the coarse node `i ≤ ℓ`; scale separation along
  chains (`IsChainRec.scale_sep`, `n ≥ 3`) gives `R_ℓ ≤ 2 · 4^{-(ℓ-i)} R_i`, hence
  `|Cov(Y_i, Y_ℓ)| ≤ D A_i A_ℓ 2^{-(ℓ-i)}` with `A_i² = 2√(k_i+1)` (good) and
  `A_i² = M_b² (ρ₀+1)/δ` (bad); all `n`-dependence (the growth constant `4K` of bad pairs) is put
  into `M_b`, so that `D` is universal.
* The geometric Schur test `LQGDimension.RecVar.quad_sum_le` gives `Var ≤ 3D Σ_i A_i²`.

Only (I1) (`HigherDimLFPP.Upper.RecordLaw`) and Lemma 3.1 for the band `(a, b)` are used; the
cutoff domination (3.3) is not.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Upper

variable {d : ℕ} {κ : Rd d → ℝ}

attribute [local instance] isFiniteMeasure_polyMeasure

/-! ## Pair data for Lemma 3.1 -/

section PairData

/-- The data of a pair of measures in Lemma 3.1: probability measures, both with the growth
bound (3.4) with constant `B` at scale `R > 0`, coupled within `u ≥ 0`. -/
structure PairData (μ ν : Measure (Rd d)) (B R u : ℝ) : Prop where
  prob₁ : IsProbabilityMeasure μ
  prob₂ : IsProbabilityMeasure ν
  R_pos : 0 < R
  u_nonneg : 0 ≤ u
  growth₁ : HigherDimLFPP.GrowthBound μ B R
  growth₂ : HigherDimLFPP.GrowthBound ν B R
  coupled : HigherDimLFPP.CoupledWithin μ ν u

theorem growthBound_mono {μ : Measure (Rd d)} {B B' R : ℝ} (h : HigherDimLFPP.GrowthBound μ B R)
    (hB : B ≤ B') (hR : 0 < R) : HigherDimLFPP.GrowthBound μ B' R := fun z t ht =>
  (h z t ht).trans (mul_le_mul_of_nonneg_right hB (le_min zero_le_one (div_nonneg ht.le hR.le)))

theorem coupledWithin_mono {μ ν : Measure (Rd d)} {u u' : ℝ}
    (h : HigherDimLFPP.CoupledWithin μ ν u) (hu : u ≤ u') : HigherDimLFPP.CoupledWithin μ ν u' := by
  obtain ⟨cpl, h1, h2, h3⟩ := h
  exact ⟨cpl, h1, h2, h3.mono fun q hq => hq.trans hu⟩

theorem PairData.mono_B {μ ν : Measure (Rd d)} {B B' R u : ℝ} (h : PairData μ ν B R u)
    (hB : B ≤ B') : PairData μ ν B' R u :=
  ⟨h.prob₁, h.prob₂, h.R_pos, h.u_nonneg, growthBound_mono h.growth₁ hB h.R_pos,
    growthBound_mono h.growth₂ hB h.R_pos, h.coupled⟩

/-- The affine coupling of two segment measures: `ν_{[a,b]}` and `ν_{[a',b']}` are coupled within
`u` if `|a - a'|, |b - b'| ≤ u`. -/
theorem coupledWithin_segMeasure {a b a' b' : Rd d} {u : ℝ} (ha : ‖a - a'‖ ≤ u)
    (hb : ‖b - b'‖ ≤ u) : HigherDimLFPP.CoupledWithin (segMeasure a b) (segMeasure a' b') u := by
  set V : ℕ → Rd d := fun i => if i = 0 then a else b with hV
  set V' : ℕ → Rd d := fun i => if i = 0 then a' else b' with hV'
  have h := coupled_segSum (m := 1) (W := fun _ => 1) (V := V) (V' := V') (u := u) (fun i hi => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with rfl | rfl
    · simpa [hV, hV'] using ha
    · simpa [hV, hV'] using hb)
  have e : ∀ W : ℕ → Rd d, segSum 1 (fun _ => 1) W = segMeasure (W 0) (W 1) := by
    intro W
    simp only [segSum, Finset.range_one, Finset.sum_singleton, ENNReal.ofReal_one, one_smul,
      zero_add]
  rw [e, e] at h
  simp only [hV, hV', ↓reduceIte, one_ne_zero] at h
  exact h

/-- Growth of a chord measure at a coarser scale: if `2R ≤ B |y - x|` and `B ≥ 1`, then
`ν_{[x,y]}` has the growth bound with constant `B` at scale `R`. -/
theorem segMeasure_growthBound_of_le {x y : Rd d} (hxy : x ≠ y) {B R : ℝ} (hR : 0 < R)
    (hB : 1 ≤ B) (h : 2 * R ≤ B * ‖y - x‖) : HigherDimLFPP.GrowthBound (segMeasure x y) B R := by
  intro w t ht
  have hR' : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hxy))
  refine (segMeasure_growth hxy w ht).trans ?_
  rcases le_total (t / R) 1 with h1 | h1
  · rw [min_eq_right h1]
    refine (min_le_right _ _).trans ?_
    rw [mul_div_assoc', div_le_div_iff₀ hR' hR]
    nlinarith
  · rw [min_eq_left h1, mul_one]
    exact (min_le_left _ _).trans hB

end PairData

/-! ## Pair data of record configurations -/

section RecordPairs

/-- The growth constant of the pair data of a record: `3` (good), `4K` (bad), `K = 2ⁿ`. -/
def recGrowth (n : ℕ) : Record d → ℝ
  | .inl _ => 3
  | .inr _ => 4 * 2 ^ n

/-- The relative coupling size of a record: `2δ√(k+1)` (good, bin `k`) and `ρ₀ + 1` (bad). -/
def recBeta (d : ℕ) (δ : ℝ) : Record d → ℝ
  | .inl g => 2 * δ * Real.sqrt ((g.bin : ℝ) + 1)
  | .inr _ => rho0 d + 1

theorem recGrowth_le (n : ℕ) (ρ : Record d) : recGrowth n ρ ≤ 4 * 2 ^ n := by
  rcases ρ with g | b
  · show (3 : ℝ) ≤ 4 * 2 ^ n
    have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    linarith
  · exact le_rfl

theorem recBeta_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (ρ : Record d) : 0 ≤ recBeta d δ ρ := by
  rcases ρ with g | b
  · show 0 ≤ 2 * δ * Real.sqrt ((g.bin : ℝ) + 1)
    positivity
  · show 0 ≤ rho0 d + 1
    have := rho0_pos d
    linarith

/-- **Pair data of a good configuration** (HA3 D4 (a), (b) and the bin condition). -/
theorem pairData_of_mem_goodFam {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {g : GoodRec d} {c : Config d}
    (hc : c ∈ goodFam n δ g) :
    ∃ x y : Rd d, c.1 = [x, y] ∧ HasLoc δ g.loc x y ∧
      PairData (polyMeasure c.1) (polyMeasure c.2) 3 ‖y - x‖
        (‖y - x‖ * (2 * δ * Real.sqrt ((g.bin : ℝ) + 1))) := by
  obtain ⟨x, y, h1, hloc, hQ, -, hk2, -, -⟩ := hc
  have hxy := hloc.ne
  have hR := hloc.norm_pos
  refine ⟨x, y, h1, hloc, ?_⟩
  rw [h1, polyMeasure_pair hxy]
  have hprob := goodFamily_isProbabilityMeasure hQ hxy
  have hcpl := goodFamily_coupled hQ hxy (a0_le_one n)
  refine ⟨inferInstance, hprob, hR, by positivity, ?_, ?_, ?_⟩
  · exact growthBound_mono (segMeasure_growthBound hxy) (by norm_num) hR
  · exact goodFamily_growthBound hQ hxy
  · refine coupledWithin_mono hcpl ?_
    have hsq : Real.sqrt (Real.log (polyLen c.2 / ‖y - x‖)) ≤ δ * Real.sqrt ((g.bin : ℝ) + 1) := by
      calc Real.sqrt (Real.log (polyLen c.2 / ‖y - x‖))
          ≤ Real.sqrt (((g.bin : ℝ) + 1) * δ ^ 2) := Real.sqrt_le_sqrt hk2.le
        _ = δ * Real.sqrt ((g.bin : ℝ) + 1) := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hδ.le, mul_comm]
    nlinarith [norm_nonneg (y - x)]

/-- **Pair data of a bad configuration**: the parent chord and the adverse chord have the growth
bound with constant `4K` at the scale of the parent chord and are coupled within `(ρ₀ + 1) R`. -/
theorem pairData_of_mem_badFam {n : ℕ} {δ : ℝ} {b : BadRec d} {c : Config d}
    (hc : c ∈ badFam n δ b) :
    ∃ x y : Rd d, c.1 = [x, y] ∧ HasLoc δ b.loc x y ∧
      PairData (polyMeasure c.1) (polyMeasure c.2) (4 * 2 ^ n) ‖y - x‖
        (‖y - x‖ * (rho0 d + 1)) := by
  obtain ⟨x, y, x', y', rfl, hloc, -, -, hch⟩ := hc
  obtain ⟨hl1, -, hx', hy'⟩ := hch
  have hxy := hloc.ne
  have hR := hloc.norm_pos
  have hK : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hR' : 0 < ‖y' - x'‖ := lt_of_lt_of_le (by positivity) hl1
  have hxy' : x' ≠ y' := fun h => by rw [h, sub_self, norm_zero] at hR'; exact lt_irrefl _ hR'
  refine ⟨x, y, rfl, hloc, ?_⟩
  simp only
  rw [polyMeasure_pair hxy, polyMeasure_pair hxy']
  have hρ := rho0_pos d
  refine ⟨inferInstance, inferInstance, hR, by positivity, ?_, ?_, ?_⟩
  · exact growthBound_mono (segMeasure_growthBound hxy) (by linarith) hR
  · refine segMeasure_growthBound_of_le hxy' hR (by linarith) ?_
    rw [div_le_iff₀ (by positivity)] at hl1
    linarith
  · refine coupledWithin_segMeasure ?_ ?_
    · rw [← neg_sub, norm_neg]
      nlinarith [norm_nonneg (y - x)]
    · have : ‖y - y'‖ ≤ ‖y - x‖ + ‖y' - x‖ := by
        calc ‖y - y'‖ = ‖(y - x) - (y' - x)‖ := by congr 1; abel
          _ ≤ ‖y - x‖ + ‖y' - x‖ := norm_sub_le _ _
      nlinarith [norm_nonneg (y - x)]

/-- **Pair data of a record configuration** (both types). -/
theorem pairData_of_mem_family {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {ρ : Record d} {c : Config d}
    (hc : c ∈ family n δ ρ) :
    ∃ x y : Rd d, c.1 = [x, y] ∧ HasLoc δ ρ.loc x y ∧
      PairData (polyMeasure c.1) (polyMeasure c.2) (recGrowth n ρ) ‖y - x‖
        (‖y - x‖ * recBeta d δ ρ) := by
  rcases ρ with g | b
  · exact pairData_of_mem_goodFam hδ hc
  · exact pairData_of_mem_badFam hc

end RecordPairs

/-! ## Lemma 3.1 for record variables -/

section Covariance

/-- **Lemma 3.1 for record variables**: for every growth constant `B` there is `C = C(d, κ, B)`
such that `|⟪cfgVec c, cfgVec c'⟫| ≤ δ⁻¹ C √(uv) / R` for pairs with the pair data. -/
theorem exists_abs_inner_cfgVec_le (hκ : IsLFPPKernel κ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a b : ℝ}, 0 < a → a ≤ b → ∀ {δ : ℝ}, 0 < δ →
      ∀ (c c' : Config d) (R r u v : ℝ),
        PairData (polyMeasure c.1) (polyMeasure c.2) B R u →
        PairData (polyMeasure c'.1) (polyMeasure c'.2) B r v →
        |⟪cfgVec κ a b δ c, cfgVec κ a b δ c'⟫| ≤ δ⁻¹ * (C * Real.sqrt (u * v) / R) := by
  obtain ⟨C, hC0, hC⟩ := transport_cov_bound hκ B
  refine ⟨C, hC0, fun {a b} ha hab {δ} hδ c c' R r u v h h' => ?_⟩
  have := h.prob₁
  have := h.prob₂
  have := h'.prob₁
  have := h'.prob₂
  have hS0 : Ioo a b ⊆ Ioi 0 := fun t ht => lt_trans ha ht.1
  obtain ⟨-, -, hb⟩ := hC (Ioo a b) measurableSet_Ioo hS0 _ _ _ _ R r u v h.R_pos h'.R_pos
    h.u_nonneg h'.u_nonneg h.growth₁ h.growth₂ h'.growth₁ h'.growth₂ h.coupled h'.coupled
  rw [inner_cfgVec hκ ha hab hδ, abs_mul, abs_of_pos (inv_pos.2 hδ)]
  exact mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hδ.le)

/-- `r ≤ 2 · 4^{-k} R` from the scale indices: `2^{-j-1} < R`, `r ≤ 2^{-j'}` and `j + 2k ≤ j'`. -/
theorem le_of_scaleIdx {R r : ℝ} {j j' : ℤ} {k : ℕ} (hR : (2 : ℝ) ^ (-j - 1) < R)
    (hr : r ≤ (2 : ℝ) ^ (-j')) (hjj : j + 2 * (k : ℤ) ≤ j') :
    r ≤ 2 * ((1 : ℝ) / 4) ^ k * R := by
  have h1 : (2 : ℝ) ^ (-j') ≤ (2 : ℝ) ^ (-j - 1 + 1 - 2 * (k : ℤ)) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have h2 : (2 : ℝ) ^ (-j - 1 + 1 - 2 * (k : ℤ)) = 2 ^ (-j - 1) * (2 * ((1 : ℝ) / 4) ^ k) := by
    rw [zpow_sub₀ two_ne_zero, zpow_add₀ two_ne_zero, zpow_one, zpow_mul]
    have e4 : ((2 : ℝ) ^ (2 : ℤ)) = 4 := by norm_num
    rw [e4, zpow_natCast, div_pow, one_pow]
    field_simp
  have hpos : 0 < 2 * ((1 : ℝ) / 4) ^ k := by positivity
  calc r ≤ (2 : ℝ) ^ (-j') := hr
    _ ≤ 2 ^ (-j - 1) * (2 * ((1 : ℝ) / 4) ^ k) := h1.trans h2.le
    _ ≤ R * (2 * ((1 : ℝ) / 4) ^ k) := mul_le_mul_of_nonneg_right hR.le hpos.le
    _ = 2 * ((1 : ℝ) / 4) ^ k * R := by ring

/-- `√((Rβ)(rβ'))/R ≤ √2 √β √β' 2^{-k}` when `r ≤ 2 · 4^{-k} R`. -/
theorem sqrt_ratio_le {R r β β' : ℝ} (hR : 0 < R) (hβ : 0 ≤ β) (hβ' : 0 ≤ β') {k : ℕ}
    (hrR : r ≤ 2 * ((1 : ℝ) / 4) ^ k * R) :
    Real.sqrt ((R * β) * (r * β')) / R ≤
      Real.sqrt 2 * Real.sqrt β * Real.sqrt β' * ((1 : ℝ) / 2) ^ k := by
  rw [div_le_iff₀ hR]
  have hrhs : 0 ≤ Real.sqrt 2 * Real.sqrt β * Real.sqrt β' * ((1 : ℝ) / 2) ^ k * R := by
    positivity
  rw [← Real.sqrt_sq hrhs]
  refine Real.sqrt_le_sqrt ?_
  have e : (Real.sqrt 2 * Real.sqrt β * Real.sqrt β' * ((1 : ℝ) / 2) ^ k * R) ^ 2 =
      2 * β * β' * ((1 : ℝ) / 4) ^ k * R ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hβ,
      Real.sq_sqrt hβ', ← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  rw [e]
  have hββ : 0 ≤ β * β' := mul_nonneg hβ hβ'
  calc R * β * (r * β') = (β * β') * R * r := by ring
    _ ≤ (β * β') * R * (2 * ((1 : ℝ) / 4) ^ k * R) :=
        mul_le_mul_of_nonneg_left hrR (mul_nonneg hββ hR.le)
    _ = 2 * β * β' * ((1 : ℝ) / 4) ^ k * R ^ 2 := by ring

end Covariance

/-! ## The variance bound (4.18) -/

section Variance

/-- The variance weight of a record in (4.18): `C_V √(k+1)` (good, bin `k`) and `C'_V/δ` (bad). -/
def recVar (CV CV' δ : ℝ) : Record d → ℝ
  | .inl g => CV * Real.sqrt ((g.bin : ℝ) + 1)
  | .inr _ => CV' / δ

/-- The multiplier `1` (good) or `M_b` (bad) of the Schur weights. -/
def recMult (Mb : ℝ) : Record d → ℝ
  | .inl _ => 1
  | .inr _ => Mb

theorem recMult_one_le {Mb : ℝ} (hMb : 1 ≤ Mb) (ρ : Record d) : 1 ≤ recMult Mb ρ := by
  rcases ρ with g | b
  · exact le_rfl
  · exact hMb

/-- The Schur weights: `A² = 2√(k+1)` (good) and `A² = M_b² (ρ₀+1)/δ` (bad). -/
theorem sq_schurWeight {Mb δ : ℝ} (hδ : 0 < δ) (ρ : Record d) :
    (recMult Mb ρ * Real.sqrt (recBeta d δ ρ / δ)) ^ 2 =
      recVar 2 (Mb ^ 2 * (rho0 d + 1)) δ ρ := by
  rw [mul_pow, Real.sq_sqrt (div_nonneg (recBeta_nonneg hδ.le ρ) hδ.le)]
  rcases ρ with g | b
  · show (1 : ℝ) ^ 2 * (2 * δ * Real.sqrt ((g.bin : ℝ) + 1) / δ) =
      2 * Real.sqrt ((g.bin : ℝ) + 1)
    field_simp
  · show Mb ^ 2 * ((rho0 d + 1) / δ) = Mb ^ 2 * (rho0 d + 1) / δ
    ring

theorem recVar_scale (c CV CV' δ : ℝ) (ρ : Record d) :
    c * recVar CV CV' δ ρ = recVar (c * CV) (c * CV') δ ρ := by
  rcases ρ with g | b
  · show c * (CV * _) = c * CV * _
    ring
  · show c * (CV' / δ) = c * CV' / δ
    ring

/-- `‖Σ_i v_i‖² = Σ_i Σ_j ⟪v_i, v_j⟫`. -/
theorem norm_sum_sq_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {l : ℕ}
    (v : Fin l → E) : ‖∑ i, v i‖ ^ 2 = ∑ i, ∑ j, ⟪v i, v j⟫ := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  exact Finset.sum_congr rfl fun i _ => inner_sum _ _ _

/-- The Schur test along `Fin l`: if `|X_{ij}|, |X_{ji}| ≤ D A_i A_j 2^{-(j-i)}` for `i ≤ j`, then
`Σ_{i,j} X_{ij} ≤ 3 D Σ_i A_i²` (`LQGDimension.RecVar.quad_sum_le` on `Fin l`). -/
theorem quad_sum_le_fin {l : ℕ} (X : Fin l → Fin l → ℝ) (A : Fin l → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hX : ∀ i j : Fin l, i ≤ j →
      |X i j| ≤ D * A i * A j * (1 / 2) ^ ((j : ℕ) - i) ∧
        |X j i| ≤ D * A i * A j * (1 / 2) ^ ((j : ℕ) - i)) :
    ∑ i, ∑ j, X i j ≤ 3 * D * ∑ i, A i ^ 2 := by
  set X' : ℕ → ℕ → ℝ := fun i j => if h : i < l ∧ j < l then X ⟨i, h.1⟩ ⟨j, h.2⟩ else 0
    with hX'
  set A' : ℕ → ℝ := fun i => if h : i < l then A ⟨i, h⟩ else 0 with hA'
  have e1 : ∑ i, ∑ j, X i j = ∑ i ∈ Finset.range l, ∑ j ∈ Finset.range l, X' i j := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ Finset.range l, X' i j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Fin.sum_univ_eq_sum_range (fun j => X' i j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hX', i.2, j.2, and_self, dite_true]
  have e2 : ∑ i, A i ^ 2 = ∑ i ∈ Finset.range l, A' i ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => A' i ^ 2)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hA', i.2, dite_true]
  rw [e1, e2]
  refine LQGDimension.RecVar.quad_sum_le X' A' hD l fun i j hij hjl => ?_
  have hil : i < l := lt_of_le_of_lt hij hjl
  have := hX ⟨i, hil⟩ ⟨j, hjl⟩ hij
  simp only [hX', hA', hil, hjl, and_self, dite_true]
  exact this

/-- **The variance bound (4.18)** (HA3 D6 (iii); packet P-U3 target T2), in white-noise form:
there is `C_V = C_V(d, κ)` such that for every `n ≥ 3` there is `C'_V = C'_V(n, d, κ)` with
`‖Σ_i cfgVec(c_i)‖² ≤ Σ_i recVar C_V C'_V δ (ρ_i)` for every band `0 < a ≤ b`, every `δ > 0`, every
chain record of valid records and every choice `c_i ∈ Φ(ρ_i)`. -/
theorem exists_chain_variance_bound (hκ : IsLFPPKernel κ) :
    ∃ CV : ℝ, 0 ≤ CV ∧ ∀ n : ℕ, 3 ≤ n → ∃ CV' : ℝ, 0 ≤ CV' ∧
      ∀ {a b : ℝ}, 0 < a → a ≤ b → ∀ {δ : ℝ}, 0 < δ → ∀ {l : ℕ} (ρ : Fin l → Record d),
        IsChainRec δ ρ → (∀ i, RecValid n δ (ρ i)) → ∀ c : Fin l → Config d,
        (∀ i, c i ∈ family n δ (ρ i)) →
          ‖∑ i, cfgVec κ a b δ (c i)‖ ^ 2 ≤ ∑ i, recVar CV CV' δ (ρ i) := by
  obtain ⟨C₃, hC₃0, hC₃⟩ := exists_abs_inner_cfgVec_le (d := d) hκ 3
  set D : ℝ := Real.sqrt 2 * max C₃ 1 with hD
  have hD0 : 0 ≤ D := by positivity
  refine ⟨3 * D * 2, by positivity, fun n hn => ?_⟩
  obtain ⟨CK, hCK0, hCK⟩ := exists_abs_inner_cfgVec_le (d := d) hκ (4 * 2 ^ n)
  set Mb : ℝ := max 1 CK with hMb
  have hMb1 : 1 ≤ Mb := le_max_left _ _
  have hρ0 := rho0_pos d
  refine ⟨3 * D * (Mb ^ 2 * (rho0 d + 1)), by positivity,
    fun {a b} ha hab {δ} hδ {l} ρ hch hv c hc => ?_⟩
  -- pair data of every configuration
  have hpd : ∀ i, ∃ x y : Rd d, (c i).1 = [x, y] ∧ HasLoc δ (ρ i).loc x y ∧
      PairData (polyMeasure (c i).1) (polyMeasure (c i).2) (recGrowth n (ρ i)) ‖y - x‖
        (‖y - x‖ * recBeta d δ (ρ i)) := fun i => pairData_of_mem_family hδ (hc i)
  choose x y hcxy hloc hdat using hpd
  set R : Fin l → ℝ := fun i => ‖y i - x i‖ with hR
  set A : Fin l → ℝ := fun i => recMult Mb (ρ i) * Real.sqrt (recBeta d δ (ρ i) / δ) with hA
  set V : Fin l → WN d := fun i => cfgVec κ a b δ (c i) with hVdef
  -- the pair bound
  have hpair : ∀ i j : Fin l, i ≤ j →
      |⟪V i, V j⟫| ≤ D * A i * A j * (1 / 2) ^ ((j : ℕ) - i) := by
    intro i j hij
    -- scale separation
    have hk : (i : ℕ) + ((j : ℕ) - i) < l := by omega
    obtain ⟨hsep, -⟩ := hch.scale_sep hv i ((j : ℕ) - i) hk
    have hj_eq : (⟨(i : ℕ) + ((j : ℕ) - i), hk⟩ : Fin l) = j := Fin.ext (by simp; omega)
    have hi_eq : (⟨(i : ℕ), by omega⟩ : Fin l) = i := Fin.ext rfl
    rw [hj_eq, hi_eq] at hsep
    have hn2 : (2 : ℤ) * (((j : ℕ) - i : ℕ) : ℤ) ≤ ((n : ℤ) - 1) * (((j : ℕ) - i : ℕ) : ℤ) :=
      mul_le_mul_of_nonneg_right (by omega) (by positivity)
    have hratio : R j ≤ 2 * ((1 : ℝ) / 4) ^ ((j : ℕ) - i) * R i :=
      le_of_scaleIdx (hloc i).1 (hloc j).2.1 (by linarith)
    have hβi := recBeta_nonneg hδ.le (ρ i)
    have hβj := recBeta_nonneg hδ.le (ρ j)
    have hsq := sqrt_ratio_le (r := R j) (hdat i).R_pos hβi hβj hratio
    -- the common growth constant and the covariance bound
    have key : ∀ (B C : ℝ), 0 ≤ C → recGrowth n (ρ i) ≤ B → recGrowth n (ρ j) ≤ B →
        (∀ (c c' : Config d) (R r u v : ℝ),
          PairData (polyMeasure c.1) (polyMeasure c.2) B R u →
          PairData (polyMeasure c'.1) (polyMeasure c'.2) B r v →
          |⟪cfgVec κ a b δ c, cfgVec κ a b δ c'⟫| ≤ δ⁻¹ * (C * Real.sqrt (u * v) / R)) →
        |⟪V i, V j⟫| ≤ Real.sqrt 2 * C * Real.sqrt (recBeta d δ (ρ i) / δ) *
          Real.sqrt (recBeta d δ (ρ j) / δ) * (1 / 2) ^ ((j : ℕ) - i) := by
      intro B C hC hBi hBj hcov
      have h1 := hcov (c i) (c j) (R i) (R j) _ _ ((hdat i).mono_B hBi) ((hdat j).mono_B hBj)
      refine h1.trans ?_
      have e : Real.sqrt (recBeta d δ (ρ i) / δ) * Real.sqrt (recBeta d δ (ρ j) / δ) =
          δ⁻¹ * (Real.sqrt (recBeta d δ (ρ i)) * Real.sqrt (recBeta d δ (ρ j))) := by
        rw [Real.sqrt_div' _ hδ.le, Real.sqrt_div' _ hδ.le, div_mul_div_comm,
          Real.mul_self_sqrt hδ.le, div_eq_inv_mul]
      calc δ⁻¹ * (C * Real.sqrt (R i * recBeta d δ (ρ i) * (R j * recBeta d δ (ρ j))) / R i)
          = δ⁻¹ * C * (Real.sqrt (R i * recBeta d δ (ρ i) * (R j * recBeta d δ (ρ j))) / R i) := by
            ring
        _ ≤ δ⁻¹ * C * (Real.sqrt 2 * Real.sqrt (recBeta d δ (ρ i)) *
              Real.sqrt (recBeta d δ (ρ j)) * ((1 : ℝ) / 2) ^ ((j : ℕ) - i)) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = Real.sqrt 2 * C * (Real.sqrt (recBeta d δ (ρ i) / δ) *
              Real.sqrt (recBeta d δ (ρ j) / δ)) * (1 / 2) ^ ((j : ℕ) - i) := by
            rw [e]; ring
        _ = _ := by ring
    have hfin : ∀ C : ℝ, Real.sqrt 2 * C ≤ D * (recMult Mb (ρ i) * recMult Mb (ρ j)) →
        |⟪V i, V j⟫| ≤ Real.sqrt 2 * C * Real.sqrt (recBeta d δ (ρ i) / δ) *
          Real.sqrt (recBeta d δ (ρ j) / δ) * (1 / 2) ^ ((j : ℕ) - i) →
        |⟪V i, V j⟫| ≤ D * A i * A j * (1 / 2) ^ ((j : ℕ) - i) := by
      intro C hC h
      refine h.trans ?_
      have hpos : 0 ≤ Real.sqrt (recBeta d δ (ρ i) / δ) * Real.sqrt (recBeta d δ (ρ j) / δ) *
          ((1 : ℝ) / 2) ^ ((j : ℕ) - i) := by positivity
      calc Real.sqrt 2 * C * Real.sqrt (recBeta d δ (ρ i) / δ) *
            Real.sqrt (recBeta d δ (ρ j) / δ) * (1 / 2) ^ ((j : ℕ) - i)
          = (Real.sqrt 2 * C) * (Real.sqrt (recBeta d δ (ρ i) / δ) *
              Real.sqrt (recBeta d δ (ρ j) / δ) * (1 / 2) ^ ((j : ℕ) - i)) := by ring
        _ ≤ (D * (recMult Mb (ρ i) * recMult Mb (ρ j))) * (Real.sqrt (recBeta d δ (ρ i) / δ) *
              Real.sqrt (recBeta d δ (ρ j) / δ) * (1 / 2) ^ ((j : ℕ) - i)) :=
            mul_le_mul_of_nonneg_right hC hpos
        _ = D * A i * A j * (1 / 2) ^ ((j : ℕ) - i) := by simp only [hA]; ring
    by_cases hgg : (∃ gi, ρ i = Sum.inl gi) ∧ (∃ gj, ρ j = Sum.inl gj)
    · -- good–good: the universal constant
      obtain ⟨⟨gi, hgi⟩, ⟨gj, hgj⟩⟩ := hgg
      refine hfin C₃ ?_ (key 3 C₃ hC₃0 (by rw [hgi]; exact le_rfl) (by rw [hgj]; exact le_rfl)
        (fun c c' R r u v h h' => hC₃ ha hab hδ c c' R r u v h h'))
      rw [hgi, hgj]
      simp only [recMult, mul_one]
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.sqrt_nonneg 2)
    · -- a bad record is involved: the constant `C_K` is absorbed by `M_b`
      refine hfin CK ?_ (key (4 * 2 ^ n) CK hCK0 (recGrowth_le n _) (recGrowth_le n _)
        (fun c c' R r u v h h' => hCK ha hab hδ c c' R r u v h h'))
      have hCKMb : CK ≤ Mb := le_max_right _ _
      have hm : CK ≤ recMult Mb (ρ i) * recMult Mb (ρ j) := by
        rcases hρi : ρ i with gi | bi <;> rcases hρj : ρ j with gj | bj
        · exact absurd ⟨⟨gi, hρi⟩, ⟨gj, hρj⟩⟩ hgg
        · simp only [recMult, one_mul]
          exact hCKMb
        · simp only [recMult, mul_one]
          exact hCKMb
        · simp only [recMult]
          nlinarith
      have hmax : (1 : ℝ) ≤ max C₃ 1 := le_max_right _ _
      have hm0 : 0 ≤ recMult Mb (ρ i) * recMult Mb (ρ j) := by
        have := recMult_one_le hMb1 (ρ i)
        have := recMult_one_le hMb1 (ρ j)
        positivity
      calc Real.sqrt 2 * CK ≤ Real.sqrt 2 * (max C₃ 1 * (recMult Mb (ρ i) * recMult Mb (ρ j))) :=
            mul_le_mul_of_nonneg_left (hm.trans (le_mul_of_one_le_left hm0 hmax))
              (Real.sqrt_nonneg 2)
        _ = D * (recMult Mb (ρ i) * recMult Mb (ρ j)) := by rw [hD]; ring
  -- the Schur test
  have hschur := quad_sum_le_fin (fun i j => ⟪V i, V j⟫) A hD0 fun i j hij =>
    ⟨hpair i j hij, by rw [real_inner_comm]; exact hpair i j hij⟩
  rw [norm_sum_sq_eq]
  refine hschur.trans (le_of_eq ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hA]
  rw [sq_schurWeight hδ, recVar_scale]

/-- **The variance bound (4.18)** for the record variables of the field (packet P-U3 target T2;
HA3 D6 (iii)): with the constants of `exists_chain_variance_bound`,
`Var(Σ_i Y_i(c_i)) ≤ C_V Σ_{good} √(k_i+1) + C'_V m_b / δ` for every continuous version `H` of the
band field `H_{a,b}` (`0 < a ≤ b`; in particular the cutoff `(ε, 1)` for every `ε ∈ (0,1)`). -/
theorem variance_chain_le (hκ : IsLFPPKernel κ) {CV CV' : ℝ} {n : ℕ}
    (hCV : ∀ {a b : ℝ}, 0 < a → a ≤ b → ∀ {δ : ℝ}, 0 < δ → ∀ {l : ℕ} (ρ : Fin l → Record d),
        IsChainRec δ ρ → (∀ i, RecValid n δ (ρ i)) → ∀ c : Fin l → Config d,
        (∀ i, c i ∈ family n δ (ρ i)) →
          ‖∑ i, cfgVec κ a b δ (c i)‖ ^ 2 ≤ ∑ i, recVar CV CV' δ (ρ i))
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ} (hW : IsWhiteNoise P W)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {H : Rd d → Ω → ℝ} (hH : IsBandVersion P W κ a b H)
    {δ : ℝ} (hδ : 0 < δ) {l : ℕ} (ρ : Fin l → Record d) (hch : IsChainRec δ ρ)
    (hv : ∀ i, RecValid n δ (ρ i)) (c : Fin l → Config d) (hc : ∀ i, c i ∈ family n δ (ρ i)) :
    Var[fun ω => ∑ i, cfgVal δ (fun z => H z ω) (c i); P] ≤ ∑ i, recVar CV CV' δ (ρ i) := by
  rw [variance_sum_cfgVal hκ hW ha hab hH δ c]
  exact hCV ha hab hδ ρ hch hv c hc

/-- `√(k+1)` for a good record in bin `k`, `0` for a bad record. -/
def goodSqrt : Record d → ℝ
  | .inl g => Real.sqrt ((g.bin : ℝ) + 1)
  | .inr _ => 0

/-- `1` for a bad record, `0` for a good record (so `Σ_i badInd (ρ_i) = m_b`). -/
def badInd : Record d → ℝ
  | .inl _ => 0
  | .inr _ => 1

/-- `Σ_i recVar C_V C'_V δ (ρ_i) = C_V Σ_{good} √(k_i+1) + C'_V m_b / δ`. -/
theorem sum_recVar_eq (CV CV' δ : ℝ) {l : ℕ} (ρ : Fin l → Record d) :
    ∑ i, recVar CV CV' δ (ρ i) = CV * ∑ i, goodSqrt (ρ i) + CV' * (∑ i, badInd (ρ i)) / δ := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases ρ i with g | b
  · simp only [recVar, goodSqrt, badInd, mul_zero, zero_div, add_zero]
  · simp only [recVar, goodSqrt, badInd, mul_zero, mul_one, zero_add]

/-- **The variance bound (4.18)** in the explicit form of HA3 D6 (iii) (packet P-U3 target T2):
there is `C_V = C_V(d, κ)` such that for every `n ≥ 3` there is `C'_V = C'_V(n, d, κ)` with
`Var(Σ_i Y_i(c_i)) ≤ C_V Σ_{i good} √(k_i+1) + C'_V m_b/δ` for every white-noise model, every
continuous version of `H_{a,b}` (`0 < a ≤ b`; in particular the cutoff `(ε, 1)` for every `ε`),
every `δ > 0`, every chain record of valid records and every choice `c_i ∈ Φ(ρ_i)`. -/
theorem exists_variance_chain_le (hκ : IsLFPPKernel κ) :
    ∃ CV : ℝ, 0 ≤ CV ∧ ∀ n : ℕ, 3 ≤ n → ∃ CV' : ℝ, 0 ≤ CV' ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ},
      IsWhiteNoise P W → ∀ {a b : ℝ}, 0 < a → a ≤ b → ∀ {H : Rd d → Ω → ℝ},
      IsBandVersion P W κ a b H → ∀ {δ : ℝ}, 0 < δ → ∀ {l : ℕ} (ρ : Fin l → Record d),
      IsChainRec δ ρ → (∀ i, RecValid n δ (ρ i)) → ∀ c : Fin l → Config d,
      (∀ i, c i ∈ family n δ (ρ i)) →
        Var[fun ω => ∑ i, cfgVal δ (fun z => H z ω) (c i); P] ≤
          CV * ∑ i, goodSqrt (ρ i) + CV' * (∑ i, badInd (ρ i)) / δ := by
  obtain ⟨CV, hCV0, hCV⟩ := exists_chain_variance_bound (d := d) hκ
  refine ⟨CV, hCV0, fun n hn => ?_⟩
  obtain ⟨CV', hCV'0, hvar⟩ := hCV n hn
  refine ⟨CV', hCV'0, fun {Ω} _ {P} {W} hW {a b} ha hab {H} hH {δ} hδ {l} ρ hch hv c hc => ?_⟩
  rw [← sum_recVar_eq]
  exact variance_chain_le hκ hvar hW ha hab hH hδ ρ hch hv c hc

end Variance

end HigherDimLFPP.Upper
