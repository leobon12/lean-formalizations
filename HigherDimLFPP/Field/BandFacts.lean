import HigherDimLFPP.Field.Version

/-!
# Basic facts on band fields and their continuous versions (packet P-F1)

Source: `source/higher-dimensional-lfpp-limit.pdf`, (1.1) and §3.1 ("the fields of disjoint scale
bands are independent"); planning audit HA2, Details D1 (Lemma D1.4 (F3)), D2 (independence of
scale bands) and D9 (R3), (R5).

* `bandVec_add`: band additivity `k_{a,b,z} + k_{b,c,z} = k_{a,c,z}` in `L²` for `0 < a ≤ b ≤ c`
  ((F3); the kernels differ only on the null set `{t = b}`), and its a.s. form
  `IsWhiteNoise.bandVec_add_ae`.
* `IsWhiteNoise.indepFun_bands`: band fields of disjoint scale bands are independent processes.
* `IsBandVersion.measurable_uncurry` (joint measurability), `isGaussianProcess`,
  `integral_eq_zero`, `IsBandVersion.hasLaw`,
  `hasLaw_log` (`H(z) ∼ N(0, log(b/a))`), `hasLaw_sub` (Gaussian increments),
  `integral_iSup_eq_gaussianExpectedMax` (expected maxima over finitely many points),
  `IsBandVersion.ae_eq_forall` (two versions agree everywhere almost surely).

Template: the planar statements `LQGMetric.WhiteNoise.phi_add_ae`, `indepFun_phi`,
`hasLaw_phi_sub` (`LQGMetric/Field/WhiteNoisePhi.lean`, `WhiteNoiseCont.lean`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace

namespace HigherDimLFPP

variable {d : ℕ} {κ : Rd d → ℝ}

/-! ### Band additivity (F3) -/

/-- Off the null set `{t = b}`, `k_{a,b,z} + k_{b,c,z} = k_{a,c,z}` pointwise. -/
theorem bandKernel_add_apply {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (z : Rd d)
    (p : ℝ × Rd d) (hp : p.1 ≠ b) :
    bandKernel κ a b z p + bandKernel κ b c z p = bandKernel κ a c z p := by
  simp only [bandKernel]
  rcases lt_or_gt_of_ne hp with h | h
  · have h2 : p.1 ∉ Ioo b c := fun h' => absurd h'.1 (not_lt.2 h.le)
    rw [indicator_of_notMem h2, add_zero]
    by_cases h1 : p.1 ∈ Ioo a b
    · have h3 : p.1 ∈ Ioo a c := ⟨h1.1, lt_of_lt_of_le h1.2 hbc⟩
      rw [indicator_of_mem h1, indicator_of_mem h3]
    · have h3 : p.1 ∉ Ioo a c := fun h' => h1 ⟨h'.1, h⟩
      rw [indicator_of_notMem h1, indicator_of_notMem h3]
  · have h1 : p.1 ∉ Ioo a b := fun h' => absurd h'.2 (not_lt.2 h.le)
    rw [indicator_of_notMem h1, zero_add]
    by_cases h2 : p.1 ∈ Ioo b c
    · have h3 : p.1 ∈ Ioo a c := ⟨lt_of_le_of_lt hab h2.1, h2.2⟩
      rw [indicator_of_mem h2, indicator_of_mem h3]
    · have h3 : p.1 ∉ Ioo a c := fun h' => h2 ⟨h, h'.2⟩
      rw [indicator_of_notMem h2, indicator_of_notMem h3]

/-- The time slice `{t = b}` is a null set of `ℝ × ℝ^d`. -/
theorem ae_fst_ne (b : ℝ) : ∀ᵐ p : ℝ × Rd d ∂volume, p.1 ≠ b := by
  rw [ae_iff]
  have e : {p : ℝ × Rd d | ¬p.1 ≠ b} = {b} ×ˢ univ := by
    ext p
    exact ⟨fun h => ⟨not_not.1 h, mem_univ _⟩, fun h => not_not.2 h.1⟩
  rw [e, show (volume : Measure (ℝ × Rd d)) = volume.prod volume from rfl, Measure.prod_prod,
    Real.volume_singleton, zero_mul]

/-- **Band additivity** (HA2 (F3)): `k_{a,b,z} + k_{b,c,z} = k_{a,c,z}` for `0 < a ≤ b ≤ c`. -/
theorem bandVec_add (hκ : IsLFPPKernel κ) {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (z : Rd d) : bandVec κ a b z + bandVec κ b c z = bandVec κ a c z := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_add (bandVec κ a b z) (bandVec κ b c z), coeFn_bandVec hκ ha b z,
    coeFn_bandVec hκ (lt_of_lt_of_le ha hab) c z, coeFn_bandVec hκ ha c z, ae_fst_ne (d := d) b]
    with p h1 h2 h3 h4 h5
  rw [h1, Pi.add_apply, h2, h3, h4]
  exact bandKernel_add_apply hab hbc z p h5

/-- `⟪k_{a,b,z}, k_{a,b,w}⟫ = ∫_{(a,b)} C(t⁻¹(z - w)) dt/t` (the Gram kernel of one band). -/
theorem inner_bandVec_self_band (hκ : IsLFPPKernel κ) {a : ℝ} (ha : 0 < a) (b : ℝ)
    (z w : Rd d) :
    ⟪bandVec κ a b z, bandVec κ a b w⟫ = ∫ t in Ioo a b, autoCorr κ (t⁻¹ • (z - w)) / t := by
  rw [inner_bandVec hκ ha ha, max_self, min_self]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}

namespace IsWhiteNoise

/-- a.s. band additivity `H_{a,c}(z) = H_{a,b}(z) + H_{b,c}(z)`. -/
theorem bandVec_add_ae (hW : IsWhiteNoise P W) (hκ : IsLFPPKernel κ) {a b c : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hbc : b ≤ c) (z : Rd d) :
    W (bandVec κ a c z) =ᵐ[P] fun ω => W (bandVec κ a b z) ω + W (bandVec κ b c z) ω := by
  rw [← bandVec_add hκ ha hab hbc z]
  exact hW.add_ae _ _

/-- **Independence of disjoint scale bands** (HA2 D2.1): if `b ≤ a'`, the band fields
`z ↦ H_{a,b}(z)` and `z ↦ H_{a',b'}(z)` are independent processes. -/
theorem indepFun_bands (hW : IsWhiteNoise P W) (hκ : IsLFPPKernel κ) {a b a' b' : ℝ}
    (ha : 0 < a) (ha' : 0 < a') (h : b ≤ a') :
    IndepFun (fun ω (z : Rd d) => W (bandVec κ a b z) ω)
      (fun ω (z : Rd d) => W (bandVec κ a' b' z) ω) P :=
  hW.indepFun_of_inner_eq_zero _ _ fun z w => inner_bandVec_eq_zero_of_le hκ ha ha'
    ((min_le_left b b').trans (h.trans (le_max_right a a'))) z w

end IsWhiteNoise

/-! ### Continuous versions -/

namespace IsBandVersion

variable {a b : ℝ} {H : Rd d → Ω → ℝ}

/-- A version is jointly measurable in `(z, ω)`. -/
theorem measurable_uncurry (hH : IsBandVersion P W κ a b H) : Measurable (Function.uncurry H) :=
  measurable_uncurry_of_continuous_of_measurable hH.continuous hH.measurable

/-- A version is a Gaussian process (centered, with covariance `⟪k_{a,b,z}, k_{a,b,w}⟫`). -/
theorem isGaussianProcess (hH : IsBandVersion P W κ a b H) (hW : IsWhiteNoise P W) :
    IsGaussianProcess H P :=
  (hW.isGaussianProcess_comp fun z => bandVec κ a b z).congr fun z => (hH.ae_eq z).symm

/-- `H(z)` is centered. -/
theorem integral_eq_zero (hH : IsBandVersion P W κ a b H) (hW : IsWhiteNoise P W) (z : Rd d) :
    ∫ ω, H z ω ∂P = 0 := by
  rw [integral_congr_ae (hH.ae_eq z)]
  exact hW.integral_eq_zero _

/-- `H(z) ∼ N(0, ‖k_{a,b,z}‖²)`. -/
theorem hasLaw (hH : IsBandVersion P W κ a b H) (hW : IsWhiteNoise P W) (z : Rd d) :
    HasLaw (H z) (gaussianReal 0 (‖bandVec κ a b z‖ ^ 2).toNNReal) P :=
  (hW.hasLaw_single _).congr (hH.ae_eq z)

/-- `H(z) ∼ N(0, log(b/a))` for `0 < a ≤ b` (the variance normalization of (1.1)). -/
theorem hasLaw_log (hH : IsBandVersion P W κ a b H) (hW : IsWhiteNoise P W)
    (hκ : IsLFPPKernel κ) (ha : 0 < a) (hab : a ≤ b) (z : Rd d) :
    HasLaw (H z) (gaussianReal 0 (Real.log (b / a)).toNNReal) P := by
  have h := hH.hasLaw hW z
  rwa [norm_bandVec_sq hκ ha hab] at h

/-- Increments: `H(z) - H(w) ∼ N(0, ‖k_{a,b,z} - k_{a,b,w}‖²)`. -/
theorem hasLaw_sub (hH : IsBandVersion P W κ a b H) (hW : IsWhiteNoise P W) (z w : Rd d) :
    HasLaw (fun ω => H z ω - H w ω)
      (gaussianReal 0 (‖bandVec κ a b z - bandVec κ a b w‖ ^ 2).toNNReal) P := by
  refine (hW.hasLaw_sub _ _).congr ?_
  filter_upwards [hH.ae_eq z, hH.ae_eq w] with ω h1 h2
  rw [h1, h2]

/-- **Expected maxima over finitely many points** (HA2 D9 (R5)). -/
theorem integral_iSup_eq_gaussianExpectedMax (hH : IsBandVersion P W κ a b H)
    (hW : IsWhiteNoise P W) {ι : Type*} (F : Finset ι) (x : ι → Rd d) (c : ι → ℝ) :
    ∫ ω, (⨆ i : F, H (x i) ω + c i) ∂P =
      LQGDimension.gaussianExpectedMax F
        (fun i j => ⟪bandVec κ a b (x i), bandVec κ a b (x j)⟫) c := by
  rw [← hW.integral_iSup_eq_gaussianExpectedMax F (fun i => bandVec κ a b (x i)) c]
  refine integral_congr_ae ?_
  have h : ∀ᵐ ω ∂P, ∀ i : F, H (x i) ω = W (bandVec κ a b (x i)) ω :=
    ae_all_iff.2 fun i => hH.ae_eq (x i)
  filter_upwards [h] with ω hω
  simp only [hω]

/-- Two continuous versions of the same band field agree at every point almost surely. -/
theorem ae_eq_forall {H' : Rd d → Ω → ℝ} (hH : IsBandVersion P W κ a b H)
    (hH' : IsBandVersion P W κ a b H') : ∀ᵐ ω ∂P, ∀ z, H z ω = H' z ω := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Rd d)
  have : Countable D := hDc.to_subtype
  have h : ∀ᵐ ω ∂P, ∀ z : D, H z ω = H' z ω :=
    ae_all_iff.2 fun z => (hH.ae_eq z).trans (hH'.ae_eq z).symm
  filter_upwards [h] with ω hω
  have heq : (fun z => H z ω) = fun z => H' z ω :=
    Continuous.ext_on hDd (hH.continuous ω) (hH'.continuous ω) fun z hz => hω ⟨z, hz⟩
  exact fun z => congrFun heq z

end IsBandVersion

end HigherDimLFPP
