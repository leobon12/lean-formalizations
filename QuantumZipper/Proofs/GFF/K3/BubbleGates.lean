import QuantumZipper.Proofs.GFF.K3.BubbleTransfer
import QuantumZipper.Proofs.GFF.K3.DualNorm
import QuantumZipper.Proofs.GFF.K3.C5prime
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Algebra.Order.Field

/-!
# K3-BUB4: convergence of dual norms through closing gates

Blueprint: `blueprint/EXT_PP_BLUEPRINT.md` §B, node **BUB-4**. Let `D n ↓` be open subsets of
`ℍ` shrinking to an open `Ω`, with `frontier Ω ∩ D n ⊆ B(p, r n)`, `r n → 0`, and the sphere
condition `hfat` for `D n` at radii in `(2 r n, d)`. Then the dual norms of a fixed bounded
density `g` supported in `Ω` converge:
`dualNormSq (D n) (zeroSpace (D n)) (vol.withDensity g) → dualNormSq Ω (zeroSpace Ω) (vol.withDensity g)`.

Lower bound: monotonicity (`dualNormSq_zeroSpace_mono`, since `Ω ⊆ D n`).
Upper bound: transfer every test function `f ∈ zeroSpace (D n)` to `f' ∈ zeroSpace Ω` by BUB-3
(`exists_zeroSpace_transfer`, `BubbleTransfer.lean`) with `R n := min d (√(r n))`; then
`ε₁ (r n) (R n) → 0` and the pairing error `M √(π R² 2R(|p.im|+R) 2π) → 0` give, for the sup
defining `dualNormSq`,
`(∫ f g)² / E_D f ≤ (√(N_Ω (1 + ε₁)) + C)²`, hence `limsup ≤ N_Ω`.
The squeeze theorem in `ℝ≥0∞` finishes.

Two technical points of the formalization (own elementary proofs):
* the case `E_Ω f' = 0`: then `∇f' = 0` a.e. on `Ω`, hence (continuity of `fderiv`, and
  `Ω` open) everywhere on `Ω`, so `f'` is locally constant on `Ω`; since `tsupport f'` is
  compact inside the preconnected `ℂ`, its level set `Ω ∩ {f' = c}` is clopen, hence all of `ℂ`
  if `c ≠ 0`, contradicting compactness; so `f' = 0` on `Ω` and `∫ f' g = 0`.
* the ENNReal/real bookkeeping of the two nested suprema.

Route: EXT_PP §B (own argument; the gate lemma replacing Dirichlet stability, DECISIONS D8).
-/

set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal

namespace QuantumZipper.K3

/-- The Dirichlet energy on `D` is nonnegative (own elementary proof). -/
lemma dirichletEnergyOn_nonneg (D : Set ℂ) (f : ℂ → ℝ) : 0 ≤ dirichletEnergyOn D f := by
  rw [dirichletEnergyOn]
  exact mul_nonneg (by positivity) (integral_nonneg fun z => sq_nonneg _)

/-- `ℂ` is preconnected, so a nonempty clopen subset of it is everything. -/
private instance bubbleGates_preconnectedSpaceComplex : PreconnectedSpace ℂ :=
  ⟨(pathConnectedSpace_iff_univ.mp (inferInstance : PathConnectedSpace ℂ)).isConnected.isPreconnected⟩

/-! ## Case `E = 0`: a zero-energy test function vanishes on `Ω` -/

/-- **BUB-4, auxiliary lemma.** A smooth compactly supported function whose Dirichlet energy on
the open set `U` vanishes, and whose support lies in `U`, vanishes on `U`. (Own elementary
proof: `∇f = 0` a.e. on `U` and `fderiv f` is continuous, so `∇f = 0` on the open `U`; then `f`
is locally constant on `U`, so for `z ∈ U` the level set `U ∩ f ⁻¹' {f z}` is clopen in `ℂ`, and
if `f z ≠ 0` it would be all of `ℂ`, contradicting that it is contained in the compact
`tsupport f`.) -/
lemma zeroSpace_eq_zero_of_energy_zero {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hcs : HasCompactSupport f)
    (hts : tsupport f ⊆ U) (hE : dirichletEnergyOn U f = 0) : ∀ z ∈ U, f z = 0 := by
  have h2pi : (2 * Real.pi)⁻¹ ≠ 0 := by positivity
  have hint0 : ∫ z in U, ‖fderiv ℝ f z‖ ^ 2 = 0 := by
    have h := hE
    rw [dirichletEnergyOn] at h
    exact (mul_eq_zero.mp h).resolve_left h2pi
  have hint : IntegrableOn (fun z => ‖fderiv ℝ f z‖ ^ 2) U :=
    (isDNSpace_zeroSpace U).energy f ⟨hsm, hcs, hts⟩
  have hae : ∀ᵐ z ∂(volume.restrict U), fderiv ℝ f z = 0 := by
    have h := (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg (‖fderiv ℝ f z‖)) hint).1 hint0
    filter_upwards [h] with z hz
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  -- continuity upgrades the a.e. statement to a pointwise one on the open set `U`
  have hfderiv_cont : Continuous fun w : ℂ => fderiv ℝ f w := hsm.continuous_fderiv smooth_ne_zero
  have hSmeas : MeasurableSet {w : ℂ | fderiv ℝ f w ≠ 0} :=
    (isOpen_compl_singleton.preimage hfderiv_cont).measurableSet
  have hpoint : ∀ z ∈ U, fderiv ℝ f z = 0 := by
    intro z hz
    by_contra hne
    have hSopen : IsOpen ({w : ℂ | fderiv ℝ f w ≠ 0} ∩ U) :=
      (isOpen_compl_singleton.preimage hfderiv_cont).inter hU
    have hSnull : volume ({w : ℂ | fderiv ℝ f w ≠ 0} ∩ U) = 0 := by
      have h1 : (volume.restrict U) {w : ℂ | fderiv ℝ f w ≠ 0} = 0 := ae_iff.mp hae
      rwa [Measure.restrict_apply hSmeas] at h1
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hSopen z ⟨hne, hz⟩
    have hle : volume (Metric.ball z ε) ≤ volume ({w : ℂ | fderiv ℝ f w ≠ 0} ∩ U) :=
      measure_mono hεsub
    rw [hSnull] at hle
    have hvol : volume (Metric.ball z ε) ≠ 0 := by
      rw [Complex.volume_ball]
      exact mul_ne_zero (pow_ne_zero 2 (ENNReal.ofReal_ne_zero_iff.mpr hε))
        (ENNReal.coe_ne_zero.mpr (ne_of_gt NNReal.pi_pos))
    exact hvol (le_antisymm hle bot_le)
  intro z hz
  by_contra hc
  set D : Set ℂ := U ∩ f ⁻¹' {f z} with hDdef
  have hDopen : IsOpen D :=
    hU.isOpen_inter_preimage_of_fderiv_eq_zero (hsm.differentiable smooth_ne_zero).differentiableOn
      (fun w hw => hpoint w hw) {f z}
  have hzD : z ∈ D := ⟨hz, rfl⟩
  have hDsub : D ⊆ tsupport f := by
    intro w hw
    refine subset_tsupport f ?_
    rw [Function.mem_support, hw.2]
    exact hc
  have hcl : closure D ⊆ tsupport f := closure_minimal hDsub (isClosed_tsupport f)
  have hDclosed : IsClosed D := by
    rw [← closure_subset_iff_isClosed]
    intro y hy
    exact ⟨hts (hcl hy), (isClosed_singleton.preimage hsm.continuous).closure_subset
      (closure_mono (fun w hw => hw.2) hy)⟩
  have huniv : D = univ := (isClopen_iff.mp ⟨hDclosed, hDopen⟩).resolve_left
    (fun h => by rw [h] at hzD; exact hzD)
  -- `tsupport f` would then be all of `ℂ`, contradicting that it is bounded
  obtain ⟨R, hR⟩ := hcs.isBounded.subset_closedBall (0 : ℂ)
  have huniv' : (univ : Set ℂ) ⊆ tsupport f := by rw [← huniv]; exact hDsub
  have hmem : ((R + 1 : ℝ) : ℂ) ∈ Metric.closedBall (0 : ℂ) R :=
    hR (by rw [eq_univ_of_univ_subset huniv']; trivial)
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hmem
  have h2 : ‖((R + 1 : ℝ) : ℂ)‖ ^ 2 = (R + 1) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal, ← sq]
  have hnorm : ‖((R + 1 : ℝ) : ℂ)‖ = R + 1 := by
    have h3 : (‖((R + 1 : ℝ) : ℂ)‖ - (R + 1)) * (‖((R + 1 : ℝ) : ℂ)‖ + (R + 1)) = 0 := by
      nlinarith [h2]
    rcases mul_eq_zero.mp h3 with h | h
    · linarith
    · have := norm_nonneg ((R + 1 : ℝ) : ℂ)
      linarith
  rw [hnorm] at hmem
  linarith

/-! ## Pairing bound from the dual norm on `Ω` -/

/-- **BUB-4, auxiliary lemma.** If `a` bounds the squared dual norm of the finite density `g`
(against `volume.withDensity g`) on the open `Ω`, and `g` vanishes off `Ω`, then for every test
function `f` on `Ω` the squared pairing is at most `a.toReal * E_Ω f`. For positive-energy `f`
this is the definition of the supremum; for zero-energy `f` we use that `f` vanishes on `Ω`
(`zeroSpace_eq_zero_of_energy_zero`). -/
lemma sq_pairing_le_of_dualNormSq {Ω : Set ℂ} (hΩ : IsOpen Ω) {g : ℂ → ℝ≥0∞} (hg : Measurable g)
    (hgfin : ∀ z, g z < ⊤) (hg0 : ∀ z ∉ Ω, g z = 0) {a : ℝ≥0∞} (ha : a ≠ ⊤)
    (haeq : dualNormSq Ω (zeroSpace Ω) (volume.withDensity g) ≤ a) {f : ℂ → ℝ}
    (hf : f ∈ zeroSpace Ω) :
    (∫ x, f x ∂(volume.withDensity g)) ^ 2 ≤ a.toReal * dirichletEnergyOn Ω f := by
  by_cases hE : dirichletEnergyOn Ω f = 0
  · have hzero : ∀ z ∈ Ω, f z = 0 :=
      zeroSpace_eq_zero_of_energy_zero hΩ hf.1 hf.2.1 hf.2.2 hE
    have hint : ∫ x, f x ∂(volume.withDensity g) = 0 := by
      rw [integral_withDensity_eq_integral_toReal_smul hg (Eventually.of_forall hgfin) f]
      have h0 : ∀ x, (g x).toReal • f x = 0 := fun x => by
        by_cases hx : x ∈ Ω
        · rw [hzero x hx, smul_zero]
        · rw [hg0 x hx]; simp
      simp only [h0, integral_zero]
    simp [hint, hE]
  · have hEpos : 0 < dirichletEnergyOn Ω f :=
      lt_of_le_of_ne (dirichletEnergyOn_nonneg Ω f) (Ne.symm hE)
    have hterm : ENNReal.ofReal
        ((∫ x, f x ∂(volume.withDensity g)) ^ 2 / dirichletEnergyOn Ω f) ≤
        dualNormSq Ω (zeroSpace Ω) (volume.withDensity g) := by
      rw [dualNormSq]
      refine le_iSup_of_le f (le_iSup_of_le ⟨hf, hEpos⟩ le_rfl)
    have hle := le_trans hterm haeq
    have h1 := ENNReal.toReal_mono ha hle
    rwa [ENNReal.toReal_ofReal (div_nonneg (sq_nonneg _) hEpos.le), div_le_iff₀ hEpos] at h1

/-! ## One-step gate bound -/

/-- **BUB-4, one-step bound.** If `a` bounds the squared dual norm on `Ω`, `D` is an open subset
of `ℍ` containing `Ω` whose gate at `frontier Ω` lies in `B(p, r)`, `hfat` is the sphere
condition of BUB-3 and `g ≤ M < ⊤` is supported in `Ω`, then the squared dual norm on `D` of `g`
is at most `(√(a (1 + ε₁ r R)) + M √(π R² 2R(|Im p| + R) 2π))²`: transfer each test function by
BUB-3 and use the monotonicity/energy bound. -/
lemma dualNormSq_le_of_gates {D Ω : Set ℂ} (hD : IsOpen D) (hDH : D ⊆ H) (hΩ : IsOpen Ω)
    (hΩD : Ω ⊆ D) {p : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : 2 * r < R)
    (hgate : frontier Ω ∩ D ⊆ Metric.closedBall p r)
    (hfat : ∀ s ∈ Set.Ioo (2 * r) R, ∃ z, ‖z - p‖ = s ∧ z ∉ D)
    {g : ℂ → ℝ≥0∞} (hg : Measurable g) {M : ℝ≥0∞} (hM : M < ⊤) (hgM : ∀ z, g z ≤ M)
    (hg0 : ∀ z ∉ Ω, g z = 0)
    {a : ℝ≥0∞} (ha : a ≠ ⊤) (haeq : dualNormSq Ω (zeroSpace Ω) (volume.withDensity g) ≤ a) :
    dualNormSq D (zeroSpace D) (volume.withDensity g) ≤
      ENNReal.ofReal ((Real.sqrt (a.toReal * (1 + eps1 r R)) + M.toReal *
        Real.sqrt (Real.pi * R ^ 2 * 2 * R * (|p.im| + R) * 2 * Real.pi)) ^ 2) := by
  have hgfin : ∀ z, g z < ⊤ := fun z => lt_of_le_of_lt (hgM z) hM
  have hintg (F : ℂ → ℝ) : ∫ x, F x ∂(volume.withDensity g) =
      ∫ x, F x * (g x).toReal ∂volume := by
    rw [integral_withDensity_eq_integral_toReal_smul hg (Eventually.of_forall hgfin) F]
    simp [smul_eq_mul, mul_comm]
  set C : ℝ := Real.sqrt (Real.pi * R ^ 2 * 2 * R * (|p.im| + R) * 2 * Real.pi) with hCdef
  refine iSup_le fun f => iSup_le fun hf => ?_
  have hEpos : 0 < dirichletEnergyOn D f := hf.2
  obtain ⟨f', hf'mem, hpair, hEn⟩ := exists_zeroSpace_transfer hD hDH hΩ hΩD hr hrR hgate hfat
    (g := fun z => (g z).toReal) hg.ennreal_toReal (M := M.toReal)
    (fun z => by
      rw [abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_mono hM.ne (hgM z))
    (fun z hz => by rw [hg0 z hz]; simp) hf.1
  have hsup := sq_pairing_le_of_dualNormSq hΩ hg hgfin hg0 ha haeq hf'mem
  rw [hintg f'] at hsup
  rw [hintg f]
  have h1 : |∫ x, f' x * (g x).toReal| ≤ Real.sqrt (a.toReal * dirichletEnergyOn Ω f') := by
    calc |∫ x, f' x * (g x).toReal| =
          Real.sqrt ((∫ x, f' x * (g x).toReal) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (a.toReal * dirichletEnergyOn Ω f') := Real.sqrt_le_sqrt hsup
  have h2 : Real.sqrt (a.toReal * dirichletEnergyOn Ω f') ≤
      Real.sqrt (dirichletEnergyOn D f) * Real.sqrt (a.toReal * (1 + eps1 r R)) := by
    have hmul : a.toReal * dirichletEnergyOn Ω f' ≤
        a.toReal * ((1 + eps1 r R) * dirichletEnergyOn D f) :=
      mul_le_mul_of_nonneg_left hEn ENNReal.toReal_nonneg
    calc Real.sqrt (a.toReal * dirichletEnergyOn Ω f')
        ≤ Real.sqrt (a.toReal * ((1 + eps1 r R) * dirichletEnergyOn D f)) :=
          Real.sqrt_le_sqrt hmul
      _ = Real.sqrt (dirichletEnergyOn D f * (a.toReal * (1 + eps1 r R))) := by ring_nf
      _ = Real.sqrt (dirichletEnergyOn D f) * Real.sqrt (a.toReal * (1 + eps1 r R)) :=
          Real.sqrt_mul hEpos.le _
  have h3 : |(∫ x, f x * (g x).toReal) - ∫ x, f' x * (g x).toReal| ≤
      M.toReal * C * Real.sqrt (dirichletEnergyOn D f) := hpair
  have h4 : |∫ x, f x * (g x).toReal| ≤
      Real.sqrt (dirichletEnergyOn D f) *
        (Real.sqrt (a.toReal * (1 + eps1 r R)) + M.toReal * C) := by
    have hsplit : |∫ x, f x * (g x).toReal| ≤ |∫ x, f' x * (g x).toReal| +
        |(∫ x, f x * (g x).toReal) - ∫ x, f' x * (g x).toReal| := by
      have h := abs_add_le (∫ x, f' x * (g x).toReal)
        ((∫ x, f x * (g x).toReal) - ∫ x, f' x * (g x).toReal)
      have h3 : (∫ x, f' x * (g x).toReal) + ((∫ x, f x * (g x).toReal) -
          ∫ x, f' x * (g x).toReal) = ∫ x, f x * (g x).toReal := by ring
      rwa [h3] at h
    calc |∫ x, f x * (g x).toReal|
        ≤ |∫ x, f' x * (g x).toReal| +
            |(∫ x, f x * (g x).toReal) - ∫ x, f' x * (g x).toReal| := hsplit
      _ ≤ Real.sqrt (a.toReal * dirichletEnergyOn Ω f') +
            M.toReal * C * Real.sqrt (dirichletEnergyOn D f) := add_le_add h1 h3
      _ ≤ Real.sqrt (dirichletEnergyOn D f) * Real.sqrt (a.toReal * (1 + eps1 r R)) +
            M.toReal * C * Real.sqrt (dirichletEnergyOn D f) := add_le_add h2 le_rfl
      _ = Real.sqrt (dirichletEnergyOn D f) *
            (Real.sqrt (a.toReal * (1 + eps1 r R)) + M.toReal * C) := by ring
  have h5 : (∫ x, f x * (g x).toReal) ^ 2 ≤
      dirichletEnergyOn D f *
        (Real.sqrt (a.toReal * (1 + eps1 r R)) + M.toReal * C) ^ 2 := by
    have h6 := pow_le_pow_left₀ (abs_nonneg (∫ x, f x * (g x).toReal)) h4 2
    rwa [sq_abs, mul_pow, Real.sq_sqrt hEpos.le] at h6
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_iff₀ hEpos]
  exact h5.trans (le_of_eq (by ring))

/-! ## The constants tend to zero -/

/-- The logarithmic window `log (√(r n) / (2 r n))` of BUB-3 along the gates of BUB-4. -/
def gateLog (r : ℕ → ℝ) (n : ℕ) : ℝ := Real.log (Real.sqrt (r n) / (2 * r n))

/-- The constant `4 π² K₀²` of `eps1`. -/
def eps1Const : ℝ := 4 * Real.pi ^ 2 * logCutoffConst ^ 2

/-- **BUB-4, limit of the constants.** For `r n → 0⁺` the energy factor `ε₁ (r n) (R n)` of BUB-3
with `R n = min d (√(r n))` tends to `0`. -/
lemma tendsto_eps1_gates {r : ℕ → ℝ} (hr0 : ∀ n, 0 < r n) (hr : Tendsto r atTop (𝓝 0))
    {d : ℝ} (hd : 0 < d) :
    Tendsto (fun n => eps1 (r n) (min d (Real.sqrt (r n)))) atTop (𝓝 0) := by
  have hsq : Tendsto (fun n => Real.sqrt (r n)) atTop (𝓝 0) := by
    simpa [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hr
  have hevR : ∀ᶠ n in atTop, min d (Real.sqrt (r n)) = Real.sqrt (r n) := by
    filter_upwards [hsq.eventually (Iio_mem_nhds hd)] with n hn
    exact min_eq_right hn.le
  -- `gateLog r n → +∞`
  have h2sr0 : Tendsto (fun n => 2 * Real.sqrt (r n)) atTop (𝓝 0) := by
    simpa using hsq.const_mul 2
  have h2srpos : ∀ᶠ n in atTop, (0 : ℝ) < 2 * Real.sqrt (r n) := by
    filter_upwards with n
    exact mul_pos two_pos (Real.sqrt_pos.mpr (hr0 n))
  have h2sr : Tendsto (fun n => 2 * Real.sqrt (r n)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨h2sr0, h2srpos⟩
  have hlog : Tendsto (fun n => Real.log (2 * Real.sqrt (r n))) atTop atBot :=
    Real.tendsto_log_nhdsGT_zero.comp h2sr
  have hLtop : Tendsto (fun n => gateLog r n) atTop atTop := by
    have heq : (fun n => gateLog r n) =ᶠ[atTop] fun n => -Real.log (2 * Real.sqrt (r n)) := by
      filter_upwards with n
      have hdiv : Real.sqrt (r n) / (2 * r n) = (2 * Real.sqrt (r n))⁻¹ := by
        have h1 : Real.sqrt (r n) ≠ 0 := (Real.sqrt_pos.mpr (hr0 n)).ne'
        have h2 : r n ≠ 0 := (hr0 n).ne'
        field_simp
        nlinarith [Real.sq_sqrt (hr0 n).le]
      rw [gateLog, hdiv, Real.log_inv]
    have hneg : Tendsto (fun n => -Real.log (2 * Real.sqrt (r n))) atTop atTop := by
      simpa [Function.comp_def] using tendsto_neg_atBot_atTop.comp hlog
    exact hneg.congr' heq.symm
  have hLinv : Tendsto (fun n => (gateLog r n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hLtop
  have hLinv2 : Tendsto (fun n => (gateLog r n ^ 2)⁻¹) atTop (𝓝 0) := by
    have h := hLinv.pow 2
    simpa only [inv_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using h
  have hmain : Tendsto (fun n => (gateLog r n)⁻¹ + eps1Const * (gateLog r n)⁻¹ +
      eps1Const * (gateLog r n ^ 2)⁻¹) atTop (𝓝 0) := by
    have h := (hLinv.add (hLinv.const_mul eps1Const)).add (hLinv2.const_mul eps1Const)
    simpa using h
  have heps : ∀ᶠ n in atTop, eps1 (r n) (Real.sqrt (r n)) = (gateLog r n)⁻¹ +
      eps1Const * (gateLog r n)⁻¹ + eps1Const * (gateLog r n ^ 2)⁻¹ := by
    filter_upwards [hLtop.eventually_gt_atTop 0] with n hn
    rw [eps1, ← gateLog, eps1Const, one_div, inv_inv]
    have hne : Real.log (Real.sqrt (r n) / (2 * r n)) ≠ 0 := by
      rw [← gateLog]; exact ne_of_gt hn
    field_simp
    ring
  refine hmain.congr' ?_
  filter_upwards [heps, hevR] with n hn hR
  rw [hR, hn]

/-! ## BUB-4 -/

set_option linter.unusedVariables false in
/-- **K3-BUB4, convergence of dual norms through closing gates.** EXT_PP §B, node BUB-4.
(The bounded support hypothesis `hgb` of the blueprint statement is not needed by this proof, but
is kept verbatim in the statement.) -/
theorem tendsto_dualNormSq_gates {D : ℕ → Set ℂ} {Ω : Set ℂ} (hD : ∀ n, IsOpen (D n))
    (hDH : ∀ n, D n ⊆ H) (hΩ : IsOpen Ω) (hΩD : ∀ n, Ω ⊆ D n) {p : ℂ} {r : ℕ → ℝ}
    (hr0 : ∀ n, 0 < r n) (hr : Tendsto r atTop (𝓝 0))
    (hgate : ∀ n, frontier Ω ∩ D n ⊆ Metric.closedBall p (r n))
    {d : ℝ} (hd : 0 < d) (hfat : ∀ n, ∀ s ∈ Set.Ioo (2 * r n) d, ∃ z, ‖z - p‖ = s ∧ z ∉ D n)
    {g : ℂ → ℝ≥0∞} (hg : Measurable g) (hgM : ∃ M < ⊤, ∀ z, g z ≤ M) (hg0 : ∀ z ∉ Ω, g z = 0)
    (hgb : Bornology.IsBounded (Function.support g)) :
    Tendsto (fun n => dualNormSq (D n) (zeroSpace (D n)) (volume.withDensity g)) atTop
      (𝓝 (dualNormSq Ω (zeroSpace Ω) (volume.withDensity g))) := by
  obtain ⟨M, hM, hgM⟩ := hgM
  set a : ℝ≥0∞ := dualNormSq Ω (zeroSpace Ω) (volume.withDensity g) with hadef
  have hmono : ∀ n, a ≤ dualNormSq (D n) (zeroSpace (D n)) (volume.withDensity g) :=
    fun n => dualNormSq_zeroSpace_mono hΩ (hΩD n)
  by_cases haTop : a = ⊤
  · have hconst : (fun n => dualNormSq (D n) (zeroSpace (D n)) (volume.withDensity g)) =
        fun _ => (⊤ : ℝ≥0∞) := by
      funext n
      have h2 : (⊤ : ℝ≥0∞) ≤ dualNormSq (D n) (zeroSpace (D n)) (volume.withDensity g) := by
        rw [← haTop]
        exact hmono n
      exact le_antisymm le_top h2
    rw [hconst, haTop]
    exact tendsto_const_nhds
  have hsmall : ∀ᶠ n in atTop, r n < min (1 / 4) (d ^ 2) :=
    hr.eventually (Iio_mem_nhds (lt_min (by norm_num) (pow_pos hd 2)))
  have hev : ∀ᶠ n in atTop, 2 * r n < min d (Real.sqrt (r n)) := by
    filter_upwards [hsmall] with n hn
    have hr0n : 0 < r n := hr0 n
    have h1 : r n < 1 / 4 := lt_of_lt_of_le hn (min_le_left _ _)
    have h2 : r n < d ^ 2 := lt_of_lt_of_le hn (min_le_right _ _)
    have h4 : (2 * r n) ^ 2 < r n := by nlinarith
    have h5 : 2 * r n < Real.sqrt (r n) :=
      (Real.lt_sqrt (by linarith : (0 : ℝ) ≤ 2 * r n)).mpr h4
    have h6 : Real.sqrt (r n) < d := (Real.sqrt_lt' hd).mpr h2
    exact lt_min (lt_trans h5 h6) h5
  have hbound : ∀ᶠ n in atTop, dualNormSq (D n) (zeroSpace (D n)) (volume.withDensity g) ≤
      ENNReal.ofReal ((Real.sqrt (a.toReal * (1 + eps1 (r n) (min d (Real.sqrt (r n))))) +
        M.toReal * Real.sqrt (Real.pi * (min d (Real.sqrt (r n))) ^ 2 *
          2 * (min d (Real.sqrt (r n))) * (|p.im| + min d (Real.sqrt (r n))) *
          2 * Real.pi)) ^ 2) := by
    filter_upwards [hev] with n hn
    have hR_le : min d (Real.sqrt (r n)) ≤ d := min_le_left _ _
    refine dualNormSq_le_of_gates (hD n) (hDH n) hΩ (hΩD n) (hr0 n) hn (hgate n) ?_ hg hM hgM
      hg0 haTop (le_of_eq hadef.symm)
    intro s hs
    exact hfat n s ⟨hs.1, lt_of_lt_of_le hs.2 hR_le⟩
  have hsqrt0 : Tendsto (fun n => Real.sqrt (r n)) atTop (𝓝 0) := by
    simpa [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hr
  have hRlim : Tendsto (fun n => min d (Real.sqrt (r n))) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => d) atTop (𝓝 d)).min hsqrt0
    rwa [min_eq_right hd.le] at h
  have heps : Tendsto (fun n => eps1 (r n) (min d (Real.sqrt (r n)))) atTop (𝓝 0) :=
    tendsto_eps1_gates hr0 hr hd
  have hC0 : Tendsto (fun n => Real.sqrt (Real.pi * (min d (Real.sqrt (r n))) ^ 2 *
      2 * (min d (Real.sqrt (r n))) * (|p.im| + min d (Real.sqrt (r n))) * 2 * Real.pi))
      atTop (𝓝 0) := by
    have hinner : Tendsto (fun n => Real.pi * (min d (Real.sqrt (r n))) ^ 2 *
        2 * (min d (Real.sqrt (r n))) * (|p.im| + min d (Real.sqrt (r n))) * 2 * Real.pi)
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => Real.pi * (min d (Real.sqrt (r n))) ^ 2 *
          2 * (min d (Real.sqrt (r n))) * (|p.im| + min d (Real.sqrt (r n))) * 2 * Real.pi)
          atTop (𝓝 (Real.pi * 0 ^ 2 * 2 * 0 * (|p.im| + 0) * 2 * Real.pi)) := by
        exact (((((tendsto_const_nhds.mul (hRlim.pow 2)).mul tendsto_const_nhds).mul hRlim).mul
          (tendsto_const_nhds.add hRlim)).mul tendsto_const_nhds).mul tendsto_const_nhds
      simpa using h1
    simpa [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hinner
  have hB : Tendsto (fun n => (Real.sqrt (a.toReal * (1 + eps1 (r n) (min d (Real.sqrt (r n))))) +
      M.toReal * Real.sqrt (Real.pi * (min d (Real.sqrt (r n))) ^ 2 *
        2 * (min d (Real.sqrt (r n))) * (|p.im| + min d (Real.sqrt (r n))) *
        2 * Real.pi)) ^ 2) atTop (𝓝 a.toReal) := by
    have hC : Tendsto (fun n => M.toReal * Real.sqrt (Real.pi * (min d (Real.sqrt (r n))) ^ 2 *
        2 * (min d (Real.sqrt (r n))) * (|p.im| + min d (Real.sqrt (r n))) * 2 * Real.pi))
        atTop (𝓝 0) := by
      simpa using hC0.const_mul M.toReal
    have hsq1 : Tendsto (fun n =>
        Real.sqrt (a.toReal * (1 + eps1 (r n) (min d (Real.sqrt (r n)))))) atTop
        (𝓝 (Real.sqrt a.toReal)) := by
      have hone : Tendsto (fun n => (1 : ℝ) + eps1 (r n) (min d (Real.sqrt (r n)))) atTop (𝓝 1) := by
        simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add heps
      have h1 : Tendsto (fun n => a.toReal * (1 + eps1 (r n) (min d (Real.sqrt (r n)))))
          atTop (𝓝 (a.toReal * 1)) :=
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => a.toReal) atTop (𝓝 a.toReal)).mul hone
      have h3 := (Real.continuous_sqrt.tendsto (a.toReal * 1)).comp h1
      simpa [Function.comp_def, mul_one] using h3
    have hval : (Real.sqrt a.toReal + 0) ^ 2 = a.toReal := by
      rw [add_zero, Real.sq_sqrt ENNReal.toReal_nonneg]
    simpa [hval] using (hsq1.add hC).pow 2
  have hlim : Tendsto (fun n => ENNReal.ofReal
      ((Real.sqrt (a.toReal * (1 + eps1 (r n) (min d (Real.sqrt (r n))))) +
        M.toReal * Real.sqrt (Real.pi * (min d (Real.sqrt (r n))) ^ 2 *
          2 * (min d (Real.sqrt (r n))) * (|p.im| + min d (Real.sqrt (r n))) *
          2 * Real.pi)) ^ 2)) atTop (𝓝 a) := by
    have h := (ENNReal.continuous_ofReal.tendsto a.toReal).comp hB
    rwa [ENNReal.ofReal_toReal haTop] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall hmono) hbound

/-- **BUB-4** as the blueprint's `Prop` (`QuantumZipper.K3.BUB4Stmt`, `C5prime.lean`). -/
theorem bub4Stmt : BUB4Stmt := by
  intro D Ω hD hDH hΩ hΩD p r hr0 hr hgate d hd hfat g hg hgM hg0 hgb
  exact tendsto_dualNormSq_gates hD hDH hΩ hΩD hr0 hr hgate hd hfat hg hgM hg0 hgb

end QuantumZipper.K3
