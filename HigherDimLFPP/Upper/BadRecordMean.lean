import HigherDimLFPP.Upper.RecordVariance
import LQGDimension.Gaussian.ChainingBox
import LQGDimension.Gaussian.SudakovFernique

/-!
# The bad-record mean: HA3 D6 (ii)

Source: `source/higher-dimensional-lfpp-limit.pdf`, §4.3, Lemma 4.4 ("For bad records,
`E sup Y_u ≤ C_{n,d}` by chaining in the rescaled endpoint coordinates"), as corrected by the
planning audit HA3 (`planning/audits/HA3-section-4.md`), Details D6 (ii), with the fix F1 (the bad
families carry the chord-length constraints `|y' - x'| ≥ |y - x|/(2K)`).

**Statement** (`exists_badRecord_mean_bound`, packet P-U3 target T1).  For every `n` there is
`C_bad = C_bad(n, d, κ)` such that for every white-noise model, every band `0 < a ≤ b` (in
particular every cutoff `(ε, 1)`), every `δ > 0`, every bad record `ρ` and every finite
`F ⊆ Φ(ρ)`: `E max_{c ∈ F} Y(c) ≤ C_bad`, where `Y(c) = δ^{-1/2} ⟨H, ν_{[x,y]} - ν_{[x',y']}⟩`.

**Proof** (HA3 D6 (ii)).  The configurations of `Φ(ρ)` are parametrized by their four endpoints,
which lie in four fixed lattice cubes of side `s = δ L`, `L = 2^{-j}`: the parameter
`p(c) ∈ ℝ^{4d}` (sup norm) has diameter `≤ s`.  The chords `[x, y]` (length in `(L/2, L]`) and
`[x', y']` (length `≥ L/(4K)`) have the growth bound (3.4) with constant `8K` at scale `L`, and
moving the endpoints by `≤ √d ‖p - p̃‖` moves the chord measures by at most that much (affine
coupling).  Lemma 3.1 in variance form (`transport_var_bound`) and the Itô isometry give
`E(Y(c) - Y(c̃))² ≤ (4 C √d / (δ L)) ‖p(c) - p(c̃)‖`, and chaining on a box
(`LQGDimension.ChainBox.chainingBox_bound`, dimension `4d`, diameter `δ L`) gives
`E max_F Y ≤ 20 √5 √(4 C √d) √(4d + 1)`, independent of `δ`, `L` and the band.

2D source: `LQGDimension/LFPP/RecordMeanCrude.lean` (`gem_le_chain`: Gram vectors, the
Sudakov–Fernique reduction to increments, chaining on a box).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Upper

variable {d : ℕ} {κ : Rd d → ℝ}

attribute [local instance] isFiniteMeasure_polyMeasure

/-! ## Endpoint parameters of configurations -/

section Params

/-- The four endpoints `x, y, x', y'` of a configuration `([x, y], [x', y'])`. -/
def cfgPts (c : Config d) : Fin 4 → Rd d :=
  ![c.1.getD 0 0, c.1.getD 1 0, c.2.getD 0 0, c.2.getD 1 0]

/-- The endpoint parameter `p(c) ∈ ℝ^{4d}` (coordinates of the four endpoints). -/
def cfgParam (c : Config d) : Fin (4 * d) → ℝ := fun k =>
  (cfgPts c (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2

theorem cfgPts_pair (x y x' y' : Rd d) :
    cfgPts (([x, y], [x', y']) : Config d) = ![x, y, x', y'] := by
  ext q : 1
  fin_cases q <;> rfl

/-- Each endpoint moves by at most `√d ‖p(c) - p(c̃)‖` (Euclidean norm vs sup norm). -/
theorem norm_cfgPts_sub_le (c c' : Config d) (q : Fin 4) :
    ‖cfgPts c q - cfgPts c' q‖ ≤ Real.sqrt d * ‖cfgParam c - cfgParam c'‖ := by
  refine (Osc.norm_sub_le_sqrt_mul _ _).trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  have h := norm_le_pi_norm (cfgParam c - cfgParam c') (finProdFinEquiv (q, i))
  simpa only [Pi.sub_apply, cfgParam, Equiv.symm_apply_apply] using h

/-- Points of a half-open lattice cube of side `s` have coordinates within `s` of each other. -/
theorem abs_sub_le_of_mem_latCube {s : ℝ} {p : Fin d → ℤ} {z w : Rd d} (hz : z ∈ latCube s p)
    (hw : w ∈ latCube s p) (i : Fin d) : |z i - w i| ≤ s := by
  obtain ⟨h1, h2⟩ := hz i
  obtain ⟨h3, h4⟩ := hw i
  rw [abs_le]
  constructor <;> nlinarith

/-- The endpoint parameters of a bad family have sup-diameter at most the side `δ 2^{-j}`. -/
theorem norm_cfgParam_sub_le {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {br : BadRec d} {c c' : Config d}
    (hc : c ∈ badFam n δ br) (hc' : c' ∈ badFam n δ br) :
    ‖cfgParam c - cfgParam c'‖ ≤ side δ br.loc.1 := by
  obtain ⟨x, y, x', y', rfl, ⟨-, -, hx, hy⟩, hx', hy', -⟩ := hc
  obtain ⟨x₁, y₁, x₁', y₁', rfl, ⟨-, -, hx₁, hy₁⟩, hx₁', hy₁', -⟩ := hc'
  refine (pi_norm_le_iff_of_nonneg (side_pos hδ _).le).2 fun k => ?_
  rw [Real.norm_eq_abs]
  simp only [Pi.sub_apply, cfgParam, cfgPts_pair]
  obtain ⟨q, i⟩ := finProdFinEquiv.symm k
  fin_cases q
  · exact abs_sub_le_of_mem_latCube hx hx₁ i
  · exact abs_sub_le_of_mem_latCube hy hy₁ i
  · exact abs_sub_le_of_mem_latCube hx' hx₁' i
  · exact abs_sub_le_of_mem_latCube hy' hy₁' i

end Params

/-! ## The canonical metric of a bad family -/

section Canonical

/-- **Growth of the chords of a bad family at the scale `L = 2^{-j}`**: both chords have the
growth bound (3.4) with constant `8K` at scale `L`. -/
theorem badFam_growth {n : ℕ} {δ : ℝ} {br : BadRec d} {x y x' y' : Rd d}
    (hc : (([x, y], [x', y']) : Config d) ∈ badFam n δ br) :
    x ≠ y ∧ x' ≠ y' ∧
      HigherDimLFPP.GrowthBound (segMeasure x y) (8 * 2 ^ n) ((2 : ℝ) ^ (-br.loc.1)) ∧
      HigherDimLFPP.GrowthBound (segMeasure x' y') (8 * 2 ^ n) ((2 : ℝ) ^ (-br.loc.1)) := by
  obtain ⟨⟨hj1, hj2, -, -⟩, -, -, ⟨hl1, -, -, -⟩⟩ := mem_badFam_pair hc
  have hK : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hL : (0 : ℝ) < 2 ^ (-br.loc.1) := by positivity
  have hR : 0 < ‖y - x‖ := lt_trans (by positivity) hj1
  have hxy : x ≠ y := fun h => by rw [h, sub_self, norm_zero] at hR; exact lt_irrefl _ hR
  have hR' : 0 < ‖y' - x'‖ := lt_of_lt_of_le (by positivity) hl1
  have hxy' : x' ≠ y' := fun h => by rw [h, sub_self, norm_zero] at hR'; exact lt_irrefl _ hR'
  have hhalf : (2 : ℝ) ^ (-br.loc.1) = 2 * (2 : ℝ) ^ (-br.loc.1 - 1) := by
    rw [zpow_sub₀ two_ne_zero, zpow_one]
    ring
  refine ⟨hxy, hxy', ?_, ?_⟩
  · refine segMeasure_growthBound_of_le hxy hL (by linarith) ?_
    nlinarith
  · refine segMeasure_growthBound_of_le hxy' hL (by linarith) ?_
    rw [div_le_iff₀ (by positivity)] at hl1
    nlinarith

/-- **The canonical metric of a bad family** (HA3 D6 (ii)): with `C = C(d, κ, 8K)` the constant of
`transport_var_bound`, `‖cfgVec c - cfgVec c̃‖² ≤ (4 C √d / (δ L)) ‖p(c) - p(c̃)‖` for
configurations of the same bad family, `L = 2^{-j}`. -/
theorem norm_cfgVec_sub_sq_le (hκ : IsLFPPKernel κ) {n : ℕ} {CB : ℝ}
    (hCB : ∀ (S : Set ℝ), MeasurableSet S → S ⊆ Ioi 0 →
      ∀ (μ ν : Measure (Rd d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (R u : ℝ),
        0 < R → 0 ≤ u → HigherDimLFPP.GrowthBound μ (8 * 2 ^ n) R →
        HigherDimLFPP.GrowthBound ν (8 * 2 ^ n) R → HigherDimLFPP.CoupledWithin μ ν u →
        IsPairable κ S μ ν ∧ scaleCov κ S μ ν μ ν ≤ CB * u / R)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {δ : ℝ} (hδ : 0 < δ) {br : BadRec d}
    {c c' : Config d} (hc : c ∈ badFam n δ br) (hc' : c' ∈ badFam n δ br) :
    ‖cfgVec κ a b δ c - cfgVec κ a b δ c'‖ ^ 2 ≤
      (4 * CB * Real.sqrt d / (δ * (2 : ℝ) ^ (-br.loc.1))) * ‖cfgParam c - cfgParam c'‖ := by
  have hcm := hc
  have hcm' := hc'
  obtain ⟨x, y, x', y', rfl, -⟩ := hc
  obtain ⟨x₁, y₁, x₁', y₁', rfl, -⟩ := hc'
  obtain ⟨hxy, hxy', g1, g2⟩ := badFam_growth hcm
  obtain ⟨hxy₁, hxy₁', g3, g4⟩ := badFam_growth hcm'
  set L : ℝ := (2 : ℝ) ^ (-br.loc.1) with hLdef
  have hL : 0 < L := by positivity
  set e : ℝ := ‖cfgParam (([x, y], [x', y']) : Config d) - cfgParam ([x₁, y₁], [x₁', y₁'])‖
    with he
  have hu : 0 ≤ Real.sqrt d * e := by positivity
  have hpts := norm_cfgPts_sub_le (([x, y], [x', y']) : Config d) ([x₁, y₁], [x₁', y₁'])
  simp only [cfgPts_pair] at hpts
  have hS0 : Ioo a b ⊆ Ioi 0 := fun t ht => lt_trans ha ht.1
  -- the two variances
  have v1 : ‖pvec κ a b (segMeasure x y) - pvec κ a b (segMeasure x₁ y₁)‖ ^ 2 ≤
      CB * (Real.sqrt d * e) / L := by
    rw [← real_inner_self_eq_norm_sq, inner_pvec_sub hκ ha hab]
    exact (hCB (Ioo a b) measurableSet_Ioo hS0 _ _ L _ hL hu g1 g3
      (coupledWithin_segMeasure (hpts 0) (hpts 1))).2
  have v2 : ‖pvec κ a b (segMeasure x' y') - pvec κ a b (segMeasure x₁' y₁')‖ ^ 2 ≤
      CB * (Real.sqrt d * e) / L := by
    rw [← real_inner_self_eq_norm_sq, inner_pvec_sub hκ ha hab]
    exact (hCB (Ioo a b) measurableSet_Ioo hS0 _ _ L _ hL hu g2 g4
      (coupledWithin_segMeasure (hpts 2) (hpts 3))).2
  -- the increment of the record vectors
  have hdiff : cfgVec κ a b δ ([x, y], [x', y']) - cfgVec κ a b δ ([x₁, y₁], [x₁', y₁']) =
      δ ^ (-(1 / 2 : ℝ)) • ((pvec κ a b (segMeasure x y) - pvec κ a b (segMeasure x₁ y₁)) -
        (pvec κ a b (segMeasure x' y') - pvec κ a b (segMeasure x₁' y₁'))) := by
    simp only [cfgVec, polyMeasure_pair hxy, polyMeasure_pair hxy', polyMeasure_pair hxy₁,
      polyMeasure_pair hxy₁', ← smul_sub]
    congr 1
    abel
  rw [hdiff, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← Real.rpow_natCast,
    ← Real.rpow_mul hδ.le]
  norm_num
  rw [Real.rpow_neg_one]
  set A := pvec κ a b (segMeasure x y) - pvec κ a b (segMeasure x₁ y₁)
  set B := pvec κ a b (segMeasure x' y') - pvec κ a b (segMeasure x₁' y₁')
  have hpar : ‖A - B‖ ^ 2 ≤ 2 * ‖A‖ ^ 2 + 2 * ‖B‖ ^ 2 := by
    have := norm_sub_le A B
    nlinarith [norm_nonneg A, norm_nonneg B, norm_nonneg (A - B), sq_nonneg (‖A‖ - ‖B‖)]
  have hfin : δ⁻¹ * ‖A - B‖ ^ 2 ≤ δ⁻¹ * (4 * (CB * (Real.sqrt d * e) / L)) :=
    mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hδ.le)
  refine hfin.trans (le_of_eq ?_)
  field_simp

end Canonical

/-! ## The bad-record mean -/

section Mean

/-- **The bad-record mean** (HA3 D6 (ii); packet P-U3 target T1): for every `n` there is
`C_bad = C_bad(n, d, κ) ≥ 0` such that, for every white-noise model, every band `0 < a ≤ b` (every
cutoff), every `δ > 0`, every bad record and every finite `F ⊆ Φ(ρ)`,
`E max_{c ∈ F} Y(c) ≤ C_bad`. -/
theorem exists_badRecord_mean_bound (hκ : IsLFPPKernel κ) (n : ℕ) :
    ∃ Cbad : ℝ, 0 ≤ Cbad ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WN d → Ω → ℝ}, IsWhiteNoise P W → ∀ {a b : ℝ}, 0 < a → a ≤ b →
      ∀ {H : Rd d → Ω → ℝ}, IsBandVersion P W κ a b H → ∀ {δ : ℝ}, 0 < δ →
      ∀ (br : BadRec d) (F : Finset (Config d)), ↑F ⊆ badFam n δ br →
        ∫ ω, (⨆ c : F, cfgVal δ (fun z => H z ω) c) ∂P ≤ Cbad := by
  obtain ⟨CB, hCB0, hCB⟩ := transport_var_bound (d := d) hκ (8 * 2 ^ n)
  refine ⟨20 * Real.sqrt 5 * Real.sqrt (4 * CB * Real.sqrt d) * Real.sqrt (4 * d + 1),
    by positivity, fun {Ω} _ {P} {W} hW {a b} ha hab {H} hH {δ} hδ br F hF => ?_⟩
  rw [integral_iSup_cfgVal hκ hW ha hab hH δ F]
  rcases F.eq_empty_or_nonempty with rfl | hne
  · -- the empty family: the expected maximum is `0`
    unfold LQGDimension.gaussianExpectedMax
    have : IsEmpty (∅ : Finset (Config d)) := Finset.isEmpty_coe_sort.2 rfl
    simp only [Real.iSup_of_isEmpty, integral_zero]
    positivity
  obtain ⟨c₀, hc₀⟩ := hne
  obtain ⟨v, hv, heq⟩ := LQGDimension.exists_vecExpectedMax_eq_gaussianExpectedMax F
    (fun c c' => ⟪cfgVec κ a b δ c, cfgVec κ a b δ c'⟫)
    (LQGDimension.posSemidef_gramOn F (cfgVec κ a b δ))
  rw [heq]
  set L : ℝ := (2 : ℝ) ^ (-br.loc.1) with hLdef
  have hL : 0 < L := by positivity
  set Lc : ℝ := Real.sqrt (4 * CB * Real.sqrt d / (δ * L)) with hLc
  -- the Gram vectors realize the canonical metric
  have hvv : ∀ c ∈ F, ∀ c' ∈ F, ‖v c - v c'‖ ^ 2 ≤ Lc ^ 2 * ‖cfgParam c - cfgParam c'‖ := by
    intro c hc c' hc'
    have e : ‖v c - v c'‖ ^ 2 = ‖cfgVec κ a b δ c - cfgVec κ a b δ c'‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_sub_left,
        inner_sub_right, inner_sub_right, inner_sub_left, inner_sub_right, inner_sub_right,
        hv c hc c hc, hv c hc c' hc', hv c' hc' c hc, hv c' hc' c' hc']
    rw [e, hLc, Real.sq_sqrt (by positivity)]
    exact norm_cfgVec_sub_sq_le hκ hCB ha hab hδ (hF hc) (hF hc')
  have hp : ∀ c ∈ F, ∀ c' ∈ F, ‖cfgParam c - cfgParam c'‖ ≤ side δ br.loc.1 :=
    fun c hc c' hc' => norm_cfgParam_sub_le hδ (hF hc) (hF hc')
  have hSF : LQGDimension.vecExpectedMax F v (fun _ => 0) ≤
      LQGDimension.vecExpectedMax F (fun c => v c - v c₀) (fun _ => 0) :=
    LQGDimension.sudakovFernique (Config d) (EuclideanSpace ℝ F) (EuclideanSpace ℝ F) F v
      (fun c => v c - v c₀) (fun _ => 0) (fun i _ j _ => by rw [sub_sub_sub_cancel_right])
  have hch := LQGDimension.ChainBox.chainingBox_bound F cfgParam v (Real.sqrt_nonneg _) hp hvv hc₀
  refine hSF.trans (hch.trans (le_of_eq ?_))
  -- `Lc √((4d+1) δ L) = √(4 C √d) √(4d+1)`
  have hside : side δ br.loc.1 = δ * L := rfl
  have hcast : ((4 * d : ℕ) : ℝ) = 4 * (d : ℝ) := by push_cast; ring
  have hX : 0 ≤ 4 * CB * Real.sqrt d := by positivity
  rw [hside, hcast, mul_assoc (20 * Real.sqrt 5), mul_assoc (20 * Real.sqrt 5),
    ← Real.sqrt_mul (x := 4 * CB * Real.sqrt d / (δ * L)) (by positivity),
    ← Real.sqrt_mul (x := 4 * CB * Real.sqrt d) hX]
  congr 2
  field_simp

end Mean

end HigherDimLFPP.Upper
