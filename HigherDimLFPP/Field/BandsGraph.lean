import HigherDimLFPP.Field.Bands
import HigherDimLFPP.Lower.Frames

/-!
# Lemma 3.4(b), (3.13): graph differences at coarse scales (packet P-F3b)

Source: `source/higher-dimensional-lfpp-limit.pdf`, §3.3, Lemma 3.4(b), (3.13); planning audit
HA2 (`planning/audits/HA2-section-3.md`), finding HA2-13 and Details D8(b); HA4
(`planning/audits/HA4-section-5.md`), D5 step 3 (the consumer, Lemma 5.2).

**Statement** (`bandLemma34b_var`, HA2's `Lemma34b`, first part).  There is `C = C(d, κ)` such
that for all `δ, L > 0`, with `ρ = δ L`, and all measurable `f, g : [0,1] → ℝ^{d-1}` with
`f - g ∈ L²(0,1)` (neither `H¹₀` nor boundedness is needed, HA2-13):
`⟨H_{ρ,∞}, μ_{δf} - μ_{δg}⟩` is defined and
`δ⁻¹ Var⟨H_{ρ,∞}, μ_{δf} - μ_{δg}⟩ ≤ (C / L) ‖f - g‖²_{L²}`.

**Graph measures.**  P-F3a's graph measure is not yet in a committed file, so HA2's definition is
used locally, in the namespace `Bands` (to be unified later): `Bands.lift x y = (x, y) ∈ ℝ^{m+1}`
(`Fin.cons`), and `Bands.graphMeasure δ f = (Leb|_{[0,1]}).map (x ↦ (x, δ f x))`.  Every estimate
is first proved for an **abstract pair of pushforwards** `μ.map p`, `μ.map q` of a finite measure
`μ` on `ℝ` with `μ(B(x, r)) ≤ 2r`, along maps `p, q : ℝ → ℝ^d` that have a common `1`-Lipschitz
"horizontal coordinate" `h` (`h (p x) = h (q x) = x`): `exists_scalePair_map_le`.  This applies
verbatim to P-F3a's `graphMeasure d δ f` with `h = Lower.horiz`.

**Proof** (a variant of HA2 D8(b) that needs no derivative of `κ`).  At a scale `t > 0`, by
P-F2's `mixInt` expansion and the pushforward formula,
`‖(μ_p - μ_q) * K_t‖₂² = ∫∫ G_t(x, x') dμ dμ`, where
`G_t(x, x') = ⟨K_t(p x - ·) - K_t(q x - ·), K_t(p x' - ·) - K_t(q x' - ·)⟩_{L²(ℝ^d)}`
(`scalePair_map_eq_integral`, `scalePair_dirac`).  Then:

* `|G_t(x, x')| ≤ (G_t(x, x) + G_t(x', x'))/2` (`2|uv| ≤ u² + v²`, `abs_scalePair_dirac_le`);
* `G_t(x, x) = 2(1 - C((p x - q x)/t))/t ≤ 2 L_κ |p x - q x|² / t³`, with P-F1's quadratic bound
  `1 - C(v) ≤ L_κ |v|²` (`scalePair_dirac_self_le`) — this replaces the transverse FTC;
* `G_t(x, x') = 0` if `|x - x'| ≥ 2ρ_κ t`, since then all four points are `2ρ_κ t` apart and
  `C = 0` off `B̄(0, 2ρ_κ)` (`scalePair_dirac_eq_zero`);
* Schur: `∫∫ 1{|x - x'| < ε} (a(x) + a(x')) dμ dμ ≤ 4 ε ∫ a dμ` (`integral_indicator_add_le`).

Hence `‖(μ_p - μ_q) * K_t‖₂² ≤ 8 ρ_κ L_κ t⁻² ∫ |p - q|² dμ`, and for graphs
`|p x - q x| = δ |f x - g x|`; integrating `t⁻²` over `t > ρ = δ L` gives (3.13).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal

namespace HigherDimLFPP

/-! ### HA2's graph measures (local copy, to be unified with P-F3a's `graphMeasure`) -/

namespace Bands

variable {m : ℕ}

/-- `(x, y) ∈ ℝ × ℝ^m ↦ ℝ^{m+1}`, horizontal coordinate first (HA2's `lift`). -/
def lift (x : ℝ) (y : Rd m) : Rd (m + 1) :=
  WithLp.toLp 2 (Fin.cons x (WithLp.ofLp y) : Fin (m + 1) → ℝ)

/-- `μ_{δf} = ∫₀¹ δ_{(x, δ f(x))} dx` (HA2's `graphMeasure`; a probability measure for measurable
`f`, and `0` otherwise, since `Measure.map` of a non-measurable map is `0`). -/
def graphMeasure (δ : ℝ) (f : ℝ → Rd m) : Measure (Rd (m + 1)) :=
  (volume.restrict (Icc (0 : ℝ) 1)).map fun x => lift x (δ • f x)

/-- Lebesgue measure on `[0, 1]` is a probability measure. -/
theorem isProbabilityMeasure_volume_Icc :
    IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]⟩

theorem lift_eq (x : ℝ) (y : Rd m) : lift x y = x • e₁ (m + 1) + Lower.embedT (d := m + 1) y :=
  Lower.toLp_cons_eq m x y

theorem continuous_embedT : Continuous (Lower.embedT (d := m + 1)) := by
  refine (LipschitzWith.of_dist_le_mul fun y y' => ?_).continuous (K := 1)
  rw [dist_eq_norm, dist_eq_norm, ← Lower.embedT_sub, Lower.norm_embedT, NNReal.coe_one, one_mul]

theorem measurable_lift_comp {δ : ℝ} {f : ℝ → Rd m} (hf : Measurable f) :
    Measurable fun x => lift x (δ • f x) := by
  simp_rw [lift_eq]
  exact (measurable_id.smul_const _).add (continuous_embedT.measurable.comp (hf.const_smul δ))

theorem horiz_lift (x : ℝ) (y : Rd m) : Lower.horiz (lift x y) = x := by
  rw [lift_eq]
  exact Lower.horiz_smul_e₁_add_embedT (Nat.succ_pos m) x y

theorem lift_sub_lift (x : ℝ) (y y' : Rd m) :
    lift x y - lift x y' = Lower.embedT (d := m + 1) (y - y') := by
  rw [lift_eq, lift_eq, Lower.embedT_sub]
  abel

theorem norm_lift_sub_lift (x : ℝ) (y y' : Rd m) : ‖lift x y - lift x y'‖ = ‖y - y'‖ := by
  rw [lift_sub_lift, Lower.norm_embedT]

/-- The horizontal coordinate is `1`-Lipschitz. -/
theorem abs_horiz_sub_le {d : ℕ} (hd : 0 < d) (z z' : Rd d) :
    |Lower.horiz z - Lower.horiz z'| ≤ ‖z - z'‖ := by
  rw [← Lower.horiz_sub]
  exact Lower.abs_horiz_le _ hd

instance (δ : ℝ) (f : ℝ → Rd m) : IsFiniteMeasure (graphMeasure δ f) := by
  unfold graphMeasure
  infer_instance

/-- Small balls of the restricted Lebesgue measure: `Leb|_{[0,1]}(B(x, r)) ≤ 2r`. -/
theorem measureReal_ball_volume_Icc_le (x r : ℝ) (hr : 0 ≤ r) :
    (volume.restrict (Icc (0 : ℝ) 1)).real (ball x r) ≤ 2 * r := by
  rw [measureReal_def]
  calc ((volume.restrict (Icc (0 : ℝ) 1)) (ball x r)).toReal ≤ (volume (ball x r)).toReal :=
        ENNReal.toReal_mono (by rw [Real.volume_ball]; exact ENNReal.ofReal_ne_top)
          (Measure.restrict_le_self _)
    _ = 2 * r := by rw [Real.volume_ball, ENNReal.toReal_ofReal (by linarith)]

end Bands

variable {d : ℕ} {κ : Rd d → ℝ}

/-! ### The four-point kernel -/

section Dirac

open Measure

/-- `scalePair` of four Dirac masses:
`∫∫ C((z - w)/t)/t (δ_a - δ_b)(dz) (δ_{a'} - δ_{b'})(dw)`. -/
theorem scalePair_dirac (κ : Rd d → ℝ) (t : ℝ) (a b a' b' : Rd d) :
    scalePair κ t (dirac a) (dirac b) (dirac a') (dirac b') =
      autoCorr κ (t⁻¹ • (a - a')) / t - autoCorr κ (t⁻¹ • (a - b')) / t -
        autoCorr κ (t⁻¹ • (b - a')) / t + autoCorr κ (t⁻¹ • (b - b')) / t := by
  simp only [scalePair, mixInt, dirac_prod_dirac, integral_dirac]

/-- **Gram bound**: `|G(a, b; a', b')| ≤ (G(a, b; a, b) + G(a', b'; a', b'))/2` for the
four-point kernel `G = scalePair` of Dirac masses (it is the `L²(ℝ^d)` inner product of
`K_t(a - ·) - K_t(b - ·)` and `K_t(a' - ·) - K_t(b' - ·)`). -/
theorem abs_scalePair_dirac_le (hκ : IsLFPPKernel κ) {t : ℝ} (ht : 0 < t) (a b a' b' : Rd d) :
    |scalePair κ t (dirac a) (dirac b) (dirac a') (dirac b')| ≤
      (scalePair κ t (dirac a) (dirac b) (dirac a) (dirac b) +
        scalePair κ t (dirac a') (dirac b') (dirac a') (dirac b')) / 2 := by
  rw [← integral_scaleConv_sub_mul hκ ht (dirac a) (dirac b) (dirac a') (dirac b'),
    ← integral_scaleConv_sub_mul hκ ht (dirac a) (dirac b) (dirac a) (dirac b),
    ← integral_scaleConv_sub_mul hκ ht (dirac a') (dirac b') (dirac a') (dirac b')]
  have h1 := integrable_scaleConv_sub_mul hκ ht (dirac a) (dirac b) (dirac a') (dirac b')
  have h2 := integrable_scaleConv_sub_mul hκ ht (dirac a) (dirac b) (dirac a) (dirac b)
  have h3 := integrable_scaleConv_sub_mul hκ ht (dirac a') (dirac b') (dirac a') (dirac b')
  have key : ∀ u v : ℝ, |u * v| ≤ (u * u + v * v) / 2 := fun u v => by
    rw [abs_mul]
    nlinarith [sq_nonneg (|u| - |v|), sq_abs u, sq_abs v]
  calc |∫ y, (scaleConv κ t (dirac a) y - scaleConv κ t (dirac b) y) *
          (scaleConv κ t (dirac a') y - scaleConv κ t (dirac b') y)|
      ≤ ∫ y, |(scaleConv κ t (dirac a) y - scaleConv κ t (dirac b) y) *
          (scaleConv κ t (dirac a') y - scaleConv κ t (dirac b') y)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ y, ((scaleConv κ t (dirac a) y - scaleConv κ t (dirac b) y) *
          (scaleConv κ t (dirac a) y - scaleConv κ t (dirac b) y) +
          (scaleConv κ t (dirac a') y - scaleConv κ t (dirac b') y) *
          (scaleConv κ t (dirac a') y - scaleConv κ t (dirac b') y)) / 2 :=
        integral_mono h1.abs ((h2.add h3).div_const 2) fun y => key _ _
    _ = _ := by rw [integral_div, integral_add h2 h3]

/-- **Diagonal bound** (replaces the transverse FTC of HA2 D8(b)): if `1 - C(v) ≤ L |v|²`, then
`G(a, b; a, b) = 2 (1 - C((a - b)/t))/t ≤ 2 L |a - b|² / t³`. -/
theorem scalePair_dirac_self_le (hκ : IsLFPPKernel κ) {L : ℝ}
    (hL : ∀ x : Rd d, 1 - autoCorr κ x ≤ L * ‖x‖ ^ 2) {t : ℝ} (ht : 0 < t) (a b : Rd d) :
    scalePair κ t (dirac a) (dirac b) (dirac a) (dirac b) ≤ 2 * L * ‖a - b‖ ^ 2 / t ^ 3 := by
  rw [scalePair_dirac, sub_self, sub_self, smul_zero, autoCorr_zero hκ,
    show b - a = -(a - b) by abel, smul_neg, autoCorr_neg]
  have h := hL (t⁻¹ • (a - b))
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le)] at h
  calc 1 / t - autoCorr κ (t⁻¹ • (a - b)) / t - autoCorr κ (t⁻¹ • (a - b)) / t + 1 / t
      = 2 * (1 - autoCorr κ (t⁻¹ • (a - b))) / t := by ring
    _ ≤ 2 * (L * (t⁻¹ * ‖a - b‖) ^ 2) / t := by gcongr
    _ = 2 * L * ‖a - b‖ ^ 2 / t ^ 3 := by field_simp

/-- **Finite range**: the four-point kernel vanishes when all four cross distances are at least
`2ρ t`, `ρ` a support radius of `κ`. -/
theorem scalePair_dirac_eq_zero {ρ : ℝ} (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {t : ℝ} (ht : 0 < t)
    {a b a' b' : Rd d} (h1 : 2 * ρ * t ≤ ‖a - a'‖) (h2 : 2 * ρ * t ≤ ‖a - b'‖)
    (h3 : 2 * ρ * t ≤ ‖b - a'‖) (h4 : 2 * ρ * t ≤ ‖b - b'‖) :
    scalePair κ t (dirac a) (dirac b) (dirac a') (dirac b') = 0 := by
  have hz : ∀ v : Rd d, 2 * ρ * t ≤ ‖v‖ → autoCorr κ (t⁻¹ • v) = 0 := fun v hv => by
    refine autoCorr_eq_zero_of_two_mul_le hρ ?_
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le), inv_mul_eq_div, le_div_iff₀ ht]
    exact hv
  rw [scalePair_dirac, hz _ h1, hz _ h2, hz _ h3, hz _ h4]
  simp only [zero_div, sub_self, add_zero]

/-- The integrand `x ↦ C(t⁻¹(p₁ x.1 - p₂ x.2))/t` is bounded and measurable. -/
theorem integrable_autoCorr_comp (hκ : IsLFPPKernel κ) (t : ℝ) {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {p₁ p₂ : α → Rd d} (h₁ : Measurable p₁)
    (h₂ : Measurable p₂) :
    Integrable (fun x : α × α => autoCorr κ (t⁻¹ • (p₁ x.1 - p₂ x.2)) / t) (μ.prod μ) := by
  refine Integrable.of_bound ((((continuous_autoCorr hκ).measurable.comp
    (((h₁.comp measurable_fst).sub (h₂.comp measurable_snd)).const_smul t⁻¹)).div_const
      t)).aestronglyMeasurable |t⁻¹| (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_div, div_eq_mul_inv, abs_inv]
  calc |autoCorr κ (t⁻¹ • (p₁ x.1 - p₂ x.2))| * |t|⁻¹ ≤ 1 * |t|⁻¹ :=
        mul_le_mul_of_nonneg_right (abs_autoCorr_le_one hκ _) (inv_nonneg.2 (abs_nonneg t))
    _ = |t|⁻¹ := one_mul _

/-- **Pushforward formula**: for a finite measure `μ` and measurable `p, q`,
`‖(μ.map p - μ.map q) * K_t‖₂² = ∫∫ G_t(p x, q x; p x', q x') dμ(x) dμ(x')`. -/
theorem scalePair_map_eq_integral (hκ : IsLFPPKernel κ) (t : ℝ) {α : Type*}
    [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] {p q : α → Rd d}
    (hp : Measurable p) (hq : Measurable q) :
    scalePair κ t (μ.map p) (μ.map q) (μ.map p) (μ.map q) =
      ∫ x, scalePair κ t (dirac (p x.1)) (dirac (q x.1)) (dirac (p x.2)) (dirac (q x.2))
        ∂(μ.prod μ) := by
  have key : ∀ {p₁ p₂ : α → Rd d}, Measurable p₁ → Measurable p₂ →
      ∫ z, autoCorr κ (t⁻¹ • (z.1 - z.2)) / t ∂((μ.map p₁).prod (μ.map p₂)) =
        ∫ x, autoCorr κ (t⁻¹ • (p₁ x.1 - p₂ x.2)) / t ∂(μ.prod μ) := by
    intro p₁ p₂ h₁ h₂
    rw [map_prod_map μ μ h₁ h₂, integral_map (h₁.prodMap h₂).aemeasurable]
    · rfl
    · exact (((continuous_autoCorr hκ).comp
        ((continuous_fst.sub continuous_snd).const_smul t⁻¹)).div_const t).aestronglyMeasurable
  simp_rw [scalePair_dirac]
  unfold scalePair mixInt
  rw [key hp hp, key hp hq, key hq hp, key hq hq]
  have i1 := integrable_autoCorr_comp hκ t μ hp hp
  have i2 := integrable_autoCorr_comp hκ t μ hp hq
  have i3 := integrable_autoCorr_comp hκ t μ hq hp
  have i4 := integrable_autoCorr_comp hκ t μ hq hq
  symm
  rw [integral_add ?_ i4, integral_sub ?_ i3, integral_sub i1 i2]
  · exact i1.sub i2
  · exact (i1.sub i2).sub i3

end Dirac

/-! ### The Schur step -/

/-- **Schur bound** (HA2 D8(b)): for a finite measure `μ` on `ℝ` with `μ(B(x, ε)) ≤ 2ε` and
`a ≥ 0` integrable, `∫∫ 1{|x - x'| < ε} (a(x) + a(x')) dμ dμ ≤ 4 ε ∫ a dμ`. -/
theorem integral_indicator_add_le {μ : Measure ℝ} [IsFiniteMeasure μ] {ε : ℝ}
    (hμ : ∀ x : ℝ, μ.real (ball x ε) ≤ 2 * ε) {a : ℝ → ℝ} (ha : Integrable a μ)
    (ha0 : ∀ x, 0 ≤ a x) :
    ∫ z, {z : ℝ × ℝ | |z.1 - z.2| < ε}.indicator (fun z => a z.1 + a z.2) z ∂(μ.prod μ) ≤
      4 * ε * ∫ x, a x ∂μ := by
  set S : Set (ℝ × ℝ) := {z | |z.1 - z.2| < ε} with hSdef
  have hS : MeasurableSet S := measurableSet_lt (by fun_prop) measurable_const
  have hi1 : Integrable (fun z : ℝ × ℝ => a z.1) (μ.prod μ) := ha.comp_fst μ
  have hi2 : Integrable (fun z : ℝ × ℝ => a z.2) (μ.prod μ) := ha.comp_snd μ
  have hj1 : Integrable (S.indicator fun z : ℝ × ℝ => a z.1) (μ.prod μ) := hi1.indicator hS
  have hj2 : Integrable (S.indicator fun z : ℝ × ℝ => a z.2) (μ.prod μ) := hi2.indicator hS
  have hε : ∀ x : ℝ, 0 ≤ μ.real (ball x ε) := fun x => measureReal_nonneg
  -- first half
  have hA : ∫ z, S.indicator (fun z : ℝ × ℝ => a z.1) z ∂(μ.prod μ) ≤ 2 * ε * ∫ x, a x ∂μ := by
    rw [integral_prod _ hj1]
    have hin : ∀ x : ℝ, ∫ y, S.indicator (fun z : ℝ × ℝ => a z.1) (x, y) ∂μ =
        μ.real (ball x ε) * a x := by
      intro x
      have e : (fun y => S.indicator (fun z : ℝ × ℝ => a z.1) (x, y)) =
          (ball x ε).indicator fun _ => a x := by
        funext y
        by_cases hy : y ∈ ball x ε
        · have : (x, y) ∈ S := by
            simp only [hSdef, mem_ofPred_eq]
            rw [mem_ball, Real.dist_eq, abs_sub_comm] at hy
            exact hy
          rw [indicator_of_mem this, indicator_of_mem hy]
        · have : (x, y) ∉ S := by
            simp only [hSdef, mem_ofPred_eq]
            rw [mem_ball, Real.dist_eq, abs_sub_comm] at hy
            exact hy
          rw [indicator_of_notMem this, indicator_of_notMem hy]
      rw [e, integral_indicator_const _ measurableSet_ball, smul_eq_mul]
    simp_rw [hin]
    calc ∫ x, μ.real (ball x ε) * a x ∂μ ≤ ∫ x, 2 * ε * a x ∂μ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x => mul_nonneg (hε x) (ha0 x))
            (ha.const_mul _) (Eventually.of_forall fun x => ?_)
          exact mul_le_mul_of_nonneg_right (hμ x) (ha0 x)
      _ = 2 * ε * ∫ x, a x ∂μ := integral_const_mul _ _
  -- second half
  have hB : ∫ z, S.indicator (fun z : ℝ × ℝ => a z.2) z ∂(μ.prod μ) ≤ 2 * ε * ∫ x, a x ∂μ := by
    rw [integral_prod_symm _ hj2]
    have hin : ∀ y : ℝ, ∫ x, S.indicator (fun z : ℝ × ℝ => a z.2) (x, y) ∂μ =
        μ.real (ball y ε) * a y := by
      intro y
      have e : (fun x => S.indicator (fun z : ℝ × ℝ => a z.2) (x, y)) =
          (ball y ε).indicator fun _ => a y := by
        funext x
        by_cases hx : x ∈ ball y ε
        · have : (x, y) ∈ S := by
            simp only [hSdef, mem_ofPred_eq]
            rw [mem_ball, Real.dist_eq] at hx
            exact hx
          rw [indicator_of_mem this, indicator_of_mem hx]
        · have : (x, y) ∉ S := by
            simp only [hSdef, mem_ofPred_eq]
            rw [mem_ball, Real.dist_eq] at hx
            exact hx
          rw [indicator_of_notMem this, indicator_of_notMem hx]
      rw [e, integral_indicator_const _ measurableSet_ball, smul_eq_mul]
    simp_rw [hin]
    calc ∫ y, μ.real (ball y ε) * a y ∂μ ≤ ∫ y, 2 * ε * a y ∂μ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun y => mul_nonneg (hε y) (ha0 y))
            (ha.const_mul _) (Eventually.of_forall fun y => ?_)
          exact mul_le_mul_of_nonneg_right (hμ y) (ha0 y)
      _ = 2 * ε * ∫ x, a x ∂μ := integral_const_mul _ _
  have e : S.indicator (fun z : ℝ × ℝ => a z.1 + a z.2) =
      fun z => S.indicator (fun z : ℝ × ℝ => a z.1) z + S.indicator (fun z : ℝ × ℝ => a z.2) z :=
    indicator_add S _ _
  rw [e, integral_add hj1 hj2]
  linarith

/-! ### The core estimate for pushforward pairs -/

/-- **Core estimate for (3.13)**: there is `C = C(d, κ)` such that for every `t > 0`, every
finite measure `μ` on `ℝ` with `μ(B(x, r)) ≤ 2r`, every `1`-Lipschitz function `h : ℝ^d → ℝ` and
all measurable `p, q : ℝ → ℝ^d` with `h ∘ p = h ∘ q = id` and `|p - q|² ∈ L¹(μ)`,
`‖(μ.map p - μ.map q) * K_t‖₂² ≤ C (∫ |p - q|² dμ) t⁻²`. -/
theorem exists_scalePair_map_le (hκ : IsLFPPKernel κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ (μ : Measure ℝ) [IsFiniteMeasure μ],
      (∀ x r : ℝ, 0 ≤ r → μ.real (ball x r) ≤ 2 * r) →
      ∀ (h : Rd d → ℝ), (∀ z z', |h z - h z'| ≤ ‖z - z'‖) →
      ∀ (p q : ℝ → Rd d), Measurable p → Measurable q → (∀ x, h (p x) = x) →
        (∀ x, h (q x) = x) → Integrable (fun x => ‖p x - q x‖ ^ 2) μ →
        scalePair κ t (μ.map p) (μ.map q) (μ.map p) (μ.map q) ≤
          C * (∫ x, ‖p x - q x‖ ^ 2 ∂μ) * t ^ (-2 : ℝ) := by
  obtain ⟨ρ, hρ0, hρ⟩ := hκ.exists_radius
  obtain ⟨L, hL0, hL⟩ := exists_one_sub_autoCorr_le hκ
  refine ⟨8 * ρ * L, by positivity, fun t ht μ _ hμ h hh p q hp hq hpx hqx hint => ?_⟩
  set a : ℝ → ℝ := fun x => ‖p x - q x‖ ^ 2 with hadef
  have ha0 : ∀ x, 0 ≤ a x := fun x => sq_nonneg _
  set G : ℝ × ℝ → ℝ := fun x =>
    scalePair κ t (Measure.dirac (p x.1)) (Measure.dirac (q x.1)) (Measure.dirac (p x.2))
      (Measure.dirac (q x.2)) with hGdef
  set S : Set (ℝ × ℝ) := {z | |z.1 - z.2| < 2 * ρ * t} with hSdef
  have hS : MeasurableSet S := measurableSet_lt (by fun_prop) measurable_const
  -- pointwise bound on `G`
  have hdist : ∀ (r s : ℝ → Rd d), (∀ x, h (r x) = x) → (∀ x, h (s x) = x) →
      ∀ x x', |x - x'| ≤ ‖r x - s x'‖ := by
    intro r s hr hs x x'
    have := hh (r x) (s x')
    rwa [hr, hs] at this
  have hGle : ∀ z, |G z| ≤ L / t ^ 3 * S.indicator (fun z => a z.1 + a z.2) z := by
    intro z
    by_cases hz : z ∈ S
    · rw [indicator_of_mem hz]
      have h1 := abs_scalePair_dirac_le hκ ht (p z.1) (q z.1) (p z.2) (q z.2)
      have h2 := scalePair_dirac_self_le hκ (fun x => (hL x).2) ht (p z.1) (q z.1)
      have h3 := scalePair_dirac_self_le hκ (fun x => (hL x).2) ht (p z.2) (q z.2)
      calc |G z| ≤ _ := h1
        _ ≤ (2 * L * ‖p z.1 - q z.1‖ ^ 2 / t ^ 3 + 2 * L * ‖p z.2 - q z.2‖ ^ 2 / t ^ 3) / 2 := by
            gcongr
        _ = L / t ^ 3 * (a z.1 + a z.2) := by simp only [hadef]; ring
    · rw [indicator_of_notMem hz, mul_zero]
      have hz' : 2 * ρ * t ≤ |z.1 - z.2| := by
        simp only [hSdef, mem_ofPred_eq, not_lt] at hz
        exact hz
      have e := scalePair_dirac_eq_zero (κ := κ) hρ ht
        (hz'.trans (hdist p p hpx hpx z.1 z.2)) (hz'.trans (hdist p q hpx hqx z.1 z.2))
        (hz'.trans (hdist q p hqx hpx z.1 z.2)) (hz'.trans (hdist q q hqx hqx z.1 z.2))
      rw [hGdef]
      simp only
      rw [e, abs_zero]
  -- integrability
  have hGm : Measurable G := by
    have e : G = fun x =>
        autoCorr κ (t⁻¹ • (p x.1 - p x.2)) / t - autoCorr κ (t⁻¹ • (p x.1 - q x.2)) / t -
          autoCorr κ (t⁻¹ • (q x.1 - p x.2)) / t + autoCorr κ (t⁻¹ • (q x.1 - q x.2)) / t := by
      funext x
      simp only [hGdef, scalePair_dirac]
    rw [e]
    have hc := (continuous_autoCorr hκ).measurable
    have m1 : ∀ {r s : ℝ → Rd d}, Measurable r → Measurable s →
        Measurable fun x : ℝ × ℝ => autoCorr κ (t⁻¹ • (r x.1 - s x.2)) / t := fun hr hs =>
      (hc.comp (((hr.comp measurable_fst).sub (hs.comp measurable_snd)).const_smul t⁻¹)).div_const t
    exact (((m1 hp hp).sub (m1 hp hq)).sub (m1 hq hp)).add (m1 hq hq)
  have hai : Integrable a μ := hint
  have hbi : Integrable (S.indicator fun z : ℝ × ℝ => a z.1 + a z.2) (μ.prod μ) :=
    ((hai.comp_fst μ).add (hai.comp_snd μ)).indicator hS
  have hbi' : Integrable (fun z => L / t ^ 3 * S.indicator (fun z : ℝ × ℝ => a z.1 + a z.2) z)
      (μ.prod μ) := hbi.const_mul _
  have hGi : Integrable G (μ.prod μ) :=
    hbi'.mono' hGm.aestronglyMeasurable (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hGle z)
  have hschur := integral_indicator_add_le (μ := μ) (ε := 2 * ρ * t)
    (fun x => hμ x (2 * ρ * t) (by positivity)) hai ha0
  have h2t : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht.le, Real.rpow_natCast]
  rw [scalePair_map_eq_integral hκ t μ hp hq]
  calc ∫ x, G x ∂(μ.prod μ) ≤ ∫ x, |G x| ∂(μ.prod μ) :=
        integral_mono hGi hGi.abs fun x => le_abs_self _
    _ ≤ ∫ z, L / t ^ 3 * S.indicator (fun z : ℝ × ℝ => a z.1 + a z.2) z ∂(μ.prod μ) :=
        integral_mono hGi.abs hbi' hGle
    _ = L / t ^ 3 * ∫ z, S.indicator (fun z : ℝ × ℝ => a z.1 + a z.2) z ∂(μ.prod μ) :=
        integral_const_mul _ _
    _ ≤ L / t ^ 3 * (4 * (2 * ρ * t) * ∫ x, a x ∂μ) :=
        mul_le_mul_of_nonneg_left hschur (by positivity)
    _ = 8 * ρ * L * (∫ x, ‖p x - q x‖ ^ 2 ∂μ) * t ^ (-2 : ℝ) := by
        rw [h2t]
        simp only [hadef]
        field_simp
        ring

/-! ### (3.13) -/

/-- **(3.13) for graph measures, every scale set above `ρ = δ L`**: there is `C = C(m, κ)` such
that for all `δ, L > 0`, every measurable `S ⊆ (δ L, ∞)` and all measurable `f, g` with
`f - g ∈ L²(0, 1)`, `⟨H_S, μ_{δf} - μ_{δg}⟩` is defined and
`δ⁻¹ Var⟨H_S, μ_{δf} - μ_{δg}⟩ ≤ (C / L) ∫₀¹ |f - g|²`. -/
theorem bandLemma34b_var_subset {m : ℕ} {κ : Rd (m + 1) → ℝ} (hκ : IsLFPPKernel κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ L : ℝ) (S : Set ℝ), 0 < δ → 0 < L → MeasurableSet S →
      S ⊆ Ioi (δ * L) → ∀ f g : ℝ → Rd m, Measurable f → Measurable g →
      MemLp (f - g) 2 (volume.restrict (Icc (0 : ℝ) 1)) →
      IsPairable κ S (Bands.graphMeasure δ f) (Bands.graphMeasure δ g) ∧
      δ⁻¹ * scaleCov κ S (Bands.graphMeasure δ f) (Bands.graphMeasure δ g)
          (Bands.graphMeasure δ f) (Bands.graphMeasure δ g) ≤
        C / L * ∫ x in (0 : ℝ)..1, ‖f x - g x‖ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_scalePair_map_le hκ
  refine ⟨C, hC0, fun δ L S hδ hL hS hSρ f g hf hg hfg => ?_⟩
  have hρ : 0 < δ * L := mul_pos hδ hL
  have hS0 : S ⊆ Ioi 0 := fun t ht => lt_trans hρ (hSρ ht)
  set μI : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1) with hμI
  set p : ℝ → Rd (m + 1) := fun x => Bands.lift x (δ • f x) with hpdef
  set q : ℝ → Rd (m + 1) := fun x => Bands.lift x (δ • g x) with hqdef
  have hp : Measurable p := Bands.measurable_lift_comp hf
  have hq : Measurable q := Bands.measurable_lift_comp hg
  have hpq : ∀ x, ‖p x - q x‖ ^ 2 = δ ^ 2 * ‖f x - g x‖ ^ 2 := by
    intro x
    simp only [hpdef, hqdef]
    rw [Bands.norm_lift_sub_lift, ← smul_sub, norm_smul, Real.norm_of_nonneg hδ.le, mul_pow]
  have hfgi : Integrable (fun x => ‖f x - g x‖ ^ 2) μI := by
    have := (memLp_two_iff_integrable_sq_norm hfg.1).1 hfg
    simpa only [Pi.sub_apply] using this
  have hint : Integrable (fun x => ‖p x - q x‖ ^ 2) μI := by
    simp_rw [hpq]
    exact hfgi.const_mul _
  set I : ℝ := ∫ x, ‖f x - g x‖ ^ 2 ∂μI with hIdef
  have hI0 : 0 ≤ I := integral_nonneg fun x => sq_nonneg _
  have hIeq : ∫ x, ‖p x - q x‖ ^ 2 ∂μI = δ ^ 2 * I := by
    simp_rw [hpq]
    rw [integral_const_mul]
  have hpt : ∀ t ∈ S, scalePair κ t (μI.map p) (μI.map q) (μI.map p) (μI.map q) ≤
      C * δ ^ 2 * I * t ^ (-2 : ℝ) := by
    intro t ht
    have := hC t (hS0 ht) μI (fun x r hr => Bands.measureReal_ball_volume_Icc_le x r hr)
      Lower.horiz (Bands.abs_horiz_sub_le (Nat.succ_pos m)) p q hp hq
      (fun x => Bands.horiz_lift x _) (fun x => Bands.horiz_lift x _) hint
    rw [hIeq] at this
    linarith
  obtain ⟨hpow, hpowv⟩ := Bands.integral_Ioi_rpow_neg_two hρ
  have hgi : IntegrableOn (fun t : ℝ => C * δ ^ 2 * I * t ^ (-2 : ℝ)) (Ioi (δ * L)) :=
    hpow.const_mul _
  have hpair : IsPairable κ S (μI.map p) (μI.map q) :=
    isPairable_of_le hκ hS hS0 _ _ (hgi.mono_set hSρ) hpt
  have hgm : Bands.graphMeasure δ f = μI.map p := rfl
  have hgm' : Bands.graphMeasure δ g = μI.map q := rfl
  rw [hgm, hgm']
  refine ⟨hpair, ?_⟩
  have hIint : ∫ x in (0 : ℝ)..1, ‖f x - g x‖ ^ 2 = I := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  rw [hIint, scaleCov_eq_integral hκ hS hS0 hpair hpair]
  have hle : ∫ t in S, scalePair κ t (μI.map p) (μI.map q) (μI.map p) (μI.map q) ≤
      C * δ ^ 2 * I * (δ * L)⁻¹ := by
    calc ∫ t in S, scalePair κ t (μI.map p) (μI.map q) (μI.map p) (μI.map q)
        ≤ ∫ t in S, C * δ ^ 2 * I * t ^ (-2 : ℝ) :=
          setIntegral_mono_on (integrableOn_scalePair hκ hS hS0 hpair hpair) (hgi.mono_set hSρ)
            hS hpt
      _ ≤ ∫ t in Ioi (δ * L), C * δ ^ 2 * I * t ^ (-2 : ℝ) := by
          refine setIntegral_mono_set hgi ?_ (Eventually.of_forall hSρ)
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact mul_nonneg (by positivity) (Real.rpow_nonneg (lt_trans hρ ht).le _)
      _ = C * δ ^ 2 * I * (δ * L)⁻¹ := by rw [integral_const_mul, hpowv]
  calc δ⁻¹ * ∫ t in S, scalePair κ t (μI.map p) (μI.map q) (μI.map p) (μI.map q)
      ≤ δ⁻¹ * (C * δ ^ 2 * I * (δ * L)⁻¹) := mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hδ.le)
    _ = C / L * I := by field_simp

/-- **Lemma 3.4(b), (3.13)** (HA2 D8(b); the first part of HA2's `Lemma34b`): there is
`C = C(m, κ)` such that for all `δ, L > 0` and all measurable `f, g : ℝ → ℝ^m` with
`f - g ∈ L²(0, 1)`, `⟨H_{δL,∞}, μ_{δf} - μ_{δg}⟩` is defined and
`δ⁻¹ Var⟨H_{δL,∞}, μ_{δf} - μ_{δg}⟩ ≤ (C / L) ∫₀¹ |f - g|²`. -/
theorem bandLemma34b_var {m : ℕ} {κ : Rd (m + 1) → ℝ} (hκ : IsLFPPKernel κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ L : ℝ), 0 < δ → 0 < L → ∀ f g : ℝ → Rd m, Measurable f →
      Measurable g → MemLp (f - g) 2 (volume.restrict (Icc (0 : ℝ) 1)) →
      IsPairable κ (Ioi (δ * L)) (Bands.graphMeasure δ f) (Bands.graphMeasure δ g) ∧
      δ⁻¹ * scaleCov κ (Ioi (δ * L)) (Bands.graphMeasure δ f) (Bands.graphMeasure δ g)
          (Bands.graphMeasure δ f) (Bands.graphMeasure δ g) ≤
        C / L * ∫ x in (0 : ℝ)..1, ‖f x - g x‖ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := bandLemma34b_var_subset hκ
  exact ⟨C, hC0, fun δ L hδ hL f g hf hg hfg =>
    hC δ L (Ioi (δ * L)) hδ hL measurableSet_Ioi subset_rfl f g hf hg hfg⟩

end HigherDimLFPP
