import HigherDimLFPP.Lower.Occupation

/-!
# The exact recursion (5.26) of the lower comparison

Packet P-L2a, target T3 (ruling H6; audit HA4, "Details for later use" D7, "Recursion
(= (5.26))", and findings HA4-6, HA4-7).

For a finitely supported `μ = Σ_{z ∈ Sμ} μ z δ_z` and the selector `I = sel Y`:

* `tiltMass Sμ μ Y = ∫ e^{ζ Y(ρq,ρ,·)} dν_{I,μ} = K⁻¹ Σ_i Σ_z μ z e^{ζ Y(ρq, ρ, T_i^I z)}`;
* `tiltW Sμ μ Y p`: the weight at `p` of the tilted replacement `e^{ζ Y(ρq,ρ,·)} ν_{I,μ}`;
* `Tmap κ Sμ μ p = E tiltW(p) / E tiltMass`: the deterministic transformation `T μ` of (5.14),
  the expectations being taken under the root-band law `gLawD κ (stepTris Sμ)`.

**The recursion** (`Good.recursion`, = (5.26), with `s = K q`):

`m_{k+1} = s · m_k · E ∫ e^{ζ Y(ρq,ρ,·)} dν_{I,μ_k}`   and   `μ_{k+1} = T μ_k`,

with the unnormalized forms `Good.mm_succ`, `Good.Mw_succ`
(`M_{k+1}(p) = K q · E tiltW(S k, M_k)(p)`).

**Proof** (HA4 D7).  At the child point `T_i^j w` the cost band splits into the root band and
the child's own band: `(ρq^{k+1}, ρ] = (ρq, ρ] ∪ (ρq^{k+1}, ρq]`, the second being
`τ_{T_i^j}(ρq^k, ρ, w)` (`Good.kapD_rel`, `Good.gram_rel`; two bands per child, no unused
bands).  The depth-`(k+1)` occupation decomposes over the root choice `{I = j}`
(`Good.occH_succ_eq`) into the root factor `Aφ` (indicator of the choice, test weight and coarse
weight; it reads only the root triples `stepTris (S k)`) times the child factor `Cφ` (the
child's own occupation, reading `τ_{T_i^j}(Qs k)`).  The two groups of triples lie in disjoint
bands, so the factors are independent (`integral_mul_of_orth`), and by similarity invariance
(`Good.gram_tau`) the child factor has expectation `M_k(w)` (`Good.integral_Cφ`).  Only the
independence of the root band from each child's finer bands is used; different children may
share correlated finer bands (linearity handles them).

2D source: `LQGDimension/LFPP/BlockConstructionAux6.lean` (`exp_split4`, `gram_eq_add4`, `qX`,
`qY1`, `qY2`, `qC`, `qT`, `Good.kap_rel`, `Good.gram_rel`, `Good.field_rel`, `Aφ`, `Bφ`, `Cφ`,
`Good.RC_succ_eq`, `Good.orth_X`, `Good.orth_BC`, `Good.integral_Bφ`, `Good.gram_tau`,
`Good.integral_Cφ`, `Good.integrable_ABC`, `Good.step`), simplified: two bands per child
point instead of four, no unused-band factor `Bφ`, factor `s = Kq` instead of `4^{ξ²/2}`, and
the recursion also produces `μ_{k+1} = T μ_k`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Lower

variable {d : ℕ}

namespace LParams

variable (P : LParams d) (κ : Rd d → ℝ)

/-! ## The tilted replacement -/

/-- `∫ e^{ζ Y(ρq,ρ,·)} dν_{I,μ}` for `μ = Σ_{z ∈ Sμ} μ z δ_z` and `I = sel Y`: the integrand of
(5.15). -/
def tiltMass (Sμ : Finset (Rd d)) (μ : Rd d → ℝ) (Y : TriD d → ℝ) : ℝ :=
  (1 / (P.K : ℝ)) * ∑ i ∈ Finset.range P.K, ∑ z ∈ Sμ,
    μ z * Real.exp (P.ζ * Y (P.ρ * P.q, P.ρ, (P.T (P.sel Y) i).app z))

/-- The weight at `p` of the tilted replacement `e^{ζ Y(ρq,ρ,·)} ν_{I,μ}`. -/
def tiltW (Sμ : Finset (Rd d)) (μ : Rd d → ℝ) (Y : TriD d → ℝ) (p : Rd d) : ℝ :=
  (1 / (P.K : ℝ)) * ∑ i ∈ Finset.range P.K, ∑ z ∈ Sμ,
    if (P.T (P.sel Y) i).app z = p then μ z * Real.exp (P.ζ * Y (P.ρ * P.q, P.ρ, p)) else 0

/-- **The deterministic transformation** (5.14): `T μ(p) = E tiltW(p) / E tiltMass`, the
expectations under the root-band law. -/
def Tmap (Sμ : Finset (Rd d)) (μ : Rd d → ℝ) (p : Rd d) : ℝ :=
  (∫ Y, P.tiltW Sμ μ Y p ∂gLawD κ (P.stepTris Sμ)) /
    ∫ Y, P.tiltMass Sμ μ Y ∂gLawD κ (P.stepTris Sμ)

variable {P}

theorem tiltMass_mul (Sμ : Finset (Rd d)) (μ : Rd d → ℝ) (c : ℝ) (Y : TriD d → ℝ) :
    P.tiltMass Sμ (fun z => c * μ z) Y = c * P.tiltMass Sμ μ Y := by
  unfold tiltMass
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  ring

theorem tiltW_mul (Sμ : Finset (Rd d)) (μ : Rd d → ℝ) (c : ℝ) (Y : TriD d → ℝ) (p : Rd d) :
    P.tiltW Sμ (fun z => c * μ z) Y p = c * P.tiltW Sμ μ Y p := by
  unfold tiltW
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  split_ifs <;> ring

theorem tiltMass_nonneg {Sμ : Finset (Rd d)} {μ : Rd d → ℝ} (hμ : ∀ z ∈ Sμ, 0 ≤ μ z)
    (Y : TriD d → ℝ) : 0 ≤ P.tiltMass Sμ μ Y :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun z hz =>
    mul_nonneg (hμ z hz) (Real.exp_pos _).le)

theorem tiltW_nonneg {Sμ : Finset (Rd d)} {μ : Rd d → ℝ} (hμ : ∀ z ∈ Sμ, 0 ≤ μ z)
    (Y : TriD d → ℝ) (p : Rd d) : 0 ≤ P.tiltW Sμ μ Y p :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun z hz => by
    split_ifs
    · exact mul_nonneg (hμ z hz) (Real.exp_pos _).le
    · exact le_rfl)

/-- The tilted replacement is carried by `stepPts Sμ`. -/
theorem tiltW_eq_zero_of_not_mem {Sμ : Finset (Rd d)} (μ : Rd d → ℝ) (Y : TriD d → ℝ)
    {p : Rd d} (hp : p ∉ P.stepPts Sμ) : P.tiltW Sμ μ Y p = 0 := by
  unfold tiltW
  rw [Finset.sum_eq_zero, mul_zero]
  intro i hi
  refine Finset.sum_eq_zero fun z hz => ?_
  rw [ite_eq_right_iff]
  intro h
  exact absurd (h ▸ mem_stepPts _ (Finset.mem_range.1 hi) hz) hp

/-- The total mass of the tilted replacement is `tiltMass`. -/
theorem sum_tiltW (Sμ : Finset (Rd d)) (μ : Rd d → ℝ) (Y : TriD d → ℝ) :
    ∑ p ∈ P.stepPts Sμ, P.tiltW Sμ μ Y p = P.tiltMass Sμ μ Y := by
  unfold tiltW tiltMass
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [Finset.sum_ite_eq]
  rw [ite_eq_left_iff.2 fun h => absurd (mem_stepPts _ (Finset.mem_range.1 hi) hz) h]

/-! ## Measurability, locality, integrability of the tilt -/

theorem Good.measurable_of_sel (hP : P.Good) {Φ : Fin (P.J + 1) → (TriD d → ℝ) → ℝ}
    (hΦ : ∀ j, Measurable (Φ j)) : Measurable fun Y => Φ (P.sel Y) Y := by
  have h : Measurable fun p : Fin (P.J + 1) × (TriD d → ℝ) => Φ p.1 p.2 :=
    measurable_from_prod_countable_right fun j => hΦ j
  exact h.comp (hP.measurable_sel.prodMk measurable_id)

theorem Good.measurable_tiltMass (hP : P.Good) (Sμ : Finset (Rd d)) (μ : Rd d → ℝ) :
    Measurable (P.tiltMass Sμ μ) :=
  hP.measurable_of_sel (Φ := fun j Y => (1 / (P.K : ℝ)) * ∑ i ∈ Finset.range P.K, ∑ z ∈ Sμ,
    μ z * Real.exp (P.ζ * Y (P.ρ * P.q, P.ρ, (P.T j i).app z))) fun _ =>
    measurable_const.mul (Finset.measurable_sum _ fun _ _ => Finset.measurable_sum _ fun _ _ =>
      measurable_const.mul (measurable_exp_eval _ _))

theorem Good.measurable_tiltW (hP : P.Good) (Sμ : Finset (Rd d)) (μ : Rd d → ℝ) (p : Rd d) :
    Measurable fun Y => P.tiltW Sμ μ Y p :=
  hP.measurable_of_sel (Φ := fun j Y => (1 / (P.K : ℝ)) * ∑ i ∈ Finset.range P.K, ∑ z ∈ Sμ,
    if (P.T j i).app z = p then μ z * Real.exp (P.ζ * Y (P.ρ * P.q, P.ρ, p)) else 0) fun _ =>
    measurable_const.mul (Finset.measurable_sum _ fun _ _ => Finset.measurable_sum _ fun _ _ =>
      Measurable.ite (MeasurableSet.const _) (measurable_const.mul (measurable_exp_eval _ _))
        measurable_const)

/-- The tilt reads only the root triples `stepTris Sμ`. -/
theorem Good.tiltMass_loc (hP : P.Good) (Sμ : Finset (Rd d)) (μ : Rd d → ℝ) :
    IsLoc (P.stepTris Sμ) (P.tiltMass Sμ μ) := by
  intro Y Y' h
  unfold tiltMass
  rw [hP.sel_loc Sμ Y Y' h]
  congr 1
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun z hz => ?_
  rw [h _ (mem_stepTris_of_stepPts (mem_stepPts _ (Finset.mem_range.1 hi) hz))]

theorem Good.tiltW_loc (hP : P.Good) (Sμ : Finset (Rd d)) (μ : Rd d → ℝ) (p : Rd d) :
    IsLoc (P.stepTris Sμ) fun Y => P.tiltW Sμ μ Y p := by
  intro Y Y' h
  show P.tiltW Sμ μ Y p = P.tiltW Sμ μ Y' p
  unfold tiltW
  rw [hP.sel_loc Sμ Y Y' h]
  congr 1
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun z hz => ?_
  split_ifs with hzp
  · rw [← hzp, h _ (mem_stepTris_of_stepPts (mem_stepPts _ (Finset.mem_range.1 hi) hz))]
  · rfl

/-- Domination of the selected coarse weight by the sum over all choices. -/
theorem exp_sel_le (P : LParams d) (i : ℕ) (z : Rd d) (Y : TriD d → ℝ) :
    Real.exp (P.ζ * Y (P.ρ * P.q, P.ρ, (P.T (P.sel Y) i).app z)) ≤
      ∑ j, Real.exp (P.ζ * Y (P.ρ * P.q, P.ρ, (P.T j i).app z)) :=
  Finset.single_le_sum (f := fun j => Real.exp (P.ζ * Y (P.ρ * P.q, P.ρ, (P.T j i).app z)))
    (fun _ _ => (Real.exp_pos _).le) (Finset.mem_univ _)

theorem Good.integrable_exp_sel (hP : P.Good) (hκ : IsLFPPKernel κ) {F : Finset (TriD d)}
    (hF : ∀ t ∈ F, 0 < t.1) {i : ℕ} {z : Rd d}
    (hz : ∀ j, (P.ρ * P.q, P.ρ, (P.T j i).app z) ∈ F) :
    Integrable (fun Y => Real.exp (P.ζ * Y (P.ρ * P.q, P.ρ, (P.T (P.sel Y) i).app z)))
      (gLawD κ F) := by
  have hsum : Integrable (fun Y : TriD d → ℝ =>
      ∑ j, Real.exp (P.ζ * Y (P.ρ * P.q, P.ρ, (P.T j i).app z))) (gLawD κ F) :=
    integrable_finsetSum Finset.univ fun j _ => integrable_exp_gLawD hκ hF (hz j) P.ζ
  refine Integrable.mono' hsum ?_ (ae_of_all _ fun Y => ?_)
  · exact (hP.measurable_of_sel (Φ := fun j Y => Real.exp (P.ζ * Y (P.ρ * P.q, P.ρ,
      (P.T j i).app z))) fun _ => measurable_exp_eval _ _).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact exp_sel_le P i z Y

theorem Good.integrable_tiltMass (hP : P.Good) (hκ : IsLFPPKernel κ) {F : Finset (TriD d)}
    (hF : ∀ t ∈ F, 0 < t.1) (Sμ : Finset (Rd d)) (hSF : P.stepTris Sμ ⊆ F) (μ : Rd d → ℝ) :
    Integrable (P.tiltMass Sμ μ) (gLawD κ F) := by
  have hzF : ∀ i ∈ Finset.range P.K, ∀ z ∈ Sμ, ∀ j,
      (P.ρ * P.q, P.ρ, (P.T j i).app z) ∈ F := fun i hi z hz j =>
    hSF (mem_stepTris_of_stepPts (mem_stepPts j (Finset.mem_range.1 hi) hz))
  exact (integrable_finsetSum _ fun i hi => integrable_finsetSum _ fun z hz =>
    (hP.integrable_exp_sel κ hκ hF (hzF i hi z hz)).const_mul _).const_mul _

theorem Good.integrable_tiltW (hP : P.Good) (hκ : IsLFPPKernel κ) {F : Finset (TriD d)}
    (hF : ∀ t ∈ F, 0 < t.1) (Sμ : Finset (Rd d)) (hSF : P.stepTris Sμ ⊆ F) (μ : Rd d → ℝ)
    (p : Rd d) : Integrable (fun Y => P.tiltW Sμ μ Y p) (gLawD κ F) := by
  have hzF : ∀ i ∈ Finset.range P.K, ∀ z ∈ Sμ, ∀ j,
      (P.ρ * P.q, P.ρ, (P.T j i).app z) ∈ F := fun i hi z hz j =>
    hSF (mem_stepTris_of_stepPts (mem_stepPts j (Finset.mem_range.1 hi) hz))
  refine (integrable_finsetSum _ fun i hi => integrable_finsetSum _ fun z hz => ?_).const_mul _
  refine Integrable.mono' ((hP.integrable_exp_sel κ hκ hF (hzF i hi z hz)).const_mul |μ z|) ?_
    (ae_of_all _ fun Y => ?_)
  · exact (hP.measurable_of_sel (Φ := fun j Y => if (P.T j i).app z = p then
      μ z * Real.exp (P.ζ * Y (P.ρ * P.q, P.ρ, p)) else 0) fun _ =>
      Measurable.ite (MeasurableSet.const _) (measurable_const.mul (measurable_exp_eval _ _))
        measurable_const).aestronglyMeasurable
  · split_ifs with hzp
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), ← hzp]
    · rw [norm_zero]
      exact mul_nonneg (abs_nonneg _) (Real.exp_pos _).le

/-- The expectation of the tilt is the expectation of the same functional of the white-noise
band values `W(k_t)` (any white noise `W`, any probability space). -/
theorem Good.integral_tiltMass_eq_whiteNoise (hP : P.Good) (hκ : IsLFPPKernel κ) {Ω : Type*}
    [MeasurableSpace Ω] {Pr : Measure Ω} {W : WN d → Ω → ℝ} (hW : IsWhiteNoise Pr W)
    (Sμ : Finset (Rd d)) (μ : Rd d → ℝ) :
    ∫ Y, P.tiltMass Sμ μ Y ∂gLawD κ (P.stepTris Sμ) =
      ∫ ω, P.tiltMass Sμ μ (fun t => W (triVec κ t) ω) ∂Pr :=
  integral_gLawD_eq_whiteNoise hκ (hP.stepTris_pos Sμ) hW (hP.measurable_tiltMass Sμ μ)
    (hP.tiltMass_loc Sμ μ)

theorem Good.integral_tiltW_eq_whiteNoise (hP : P.Good) (hκ : IsLFPPKernel κ) {Ω : Type*}
    [MeasurableSpace Ω] {Pr : Measure Ω} {W : WN d → Ω → ℝ} (hW : IsWhiteNoise Pr W)
    (Sμ : Finset (Rd d)) (μ : Rd d → ℝ) (p : Rd d) :
    ∫ Y, P.tiltW Sμ μ Y p ∂gLawD κ (P.stepTris Sμ) =
      ∫ ω, P.tiltW Sμ μ (fun t => W (triVec κ t) ω) p ∂Pr :=
  integral_gLawD_eq_whiteNoise hκ (hP.stepTris_pos Sμ) hW (hP.measurable_tiltW Sμ μ p)
    (hP.tiltW_loc Sμ μ p)

/-! ## The two bands at a child point -/

variable (P) in
/-- The root triple at the child point: `(ρq, ρ, T_i^j w)`. -/
def qX (j : Fin (P.J + 1)) (i : ℕ) (w : Rd d) : TriD d := (P.ρ * P.q, P.ρ, (P.T j i).app w)

variable (P) in
/-- The child's own band at the child point: `τ_{T_i^j}(ρq^k, ρ, w) = (ρq^{k+1}, ρq, T_i^j w)`. -/
def qC (k : ℕ) (j : Fin (P.J + 1)) (i : ℕ) (w : Rd d) : TriD d :=
  tau (P.T j i) (P.ρ * P.q ^ k, P.ρ, w)

variable (P) in
/-- The depth-`(k+1)` cost triple at the child point: `(ρq^{k+1}, ρ, T_i^j w)`. -/
def qT (k : ℕ) (j : Fin (P.J + 1)) (i : ℕ) (w : Rd d) : TriD d :=
  (P.ρ * P.q ^ (k + 1), P.ρ, (P.T j i).app w)

theorem qC_eq (k : ℕ) (j : Fin (P.J + 1)) (i : ℕ) (w : Rd d) :
    P.qC k j i w = (P.ρ * P.q ^ (k + 1), P.ρ * P.q, (P.T j i).app w) := by
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · simp only [qC, tau_mk, T_r]
    ring
  · simp only [qC, tau_mk, T_r]
    ring

/-- **Two bands per child**: `kapD(·, qT) = kapD(·, qX) + kapD(·, qC)`. -/
theorem Good.kapD_rel (hP : P.Good) (hκ : IsLFPPKernel κ) (k : ℕ) (j : Fin (P.J + 1)) (i : ℕ)
    (w : Rd d) {t' : TriD d} (ht' : 0 < t'.1) :
    kapD κ t' (P.qT k j i w) = kapD κ t' (P.qX j i w) + kapD κ t' (P.qC k j i w) := by
  rw [qC_eq, qT, qX, kapD_split_right hκ (hP.rho_q_pow_pos (k + 1)) (hP.rho_q_pow_succ_le k)
    hP.rho_q_le _ ht', add_comm]

theorem mem_qT {k : ℕ} (j : Fin (P.J + 1)) {i : ℕ} (hi : i < P.K) {w : Rd d} (hw : w ∈ P.S k) :
    P.qT k j i w ∈ P.Qs (k + 1) :=
  mem_Qs_cost (mem_S_succ j hi hw)

theorem mem_qX_stepTris {k : ℕ} (j : Fin (P.J + 1)) {i : ℕ} (hi : i < P.K) {w : Rd d}
    (hw : w ∈ P.S k) : P.qX j i w ∈ P.stepTris (P.S k) :=
  mem_stepTris_of_stepPts (mem_stepPts j hi hw)

theorem mem_qX {k : ℕ} (j : Fin (P.J + 1)) {i : ℕ} (hi : i < P.K) {w : Rd d} (hw : w ∈ P.S k) :
    P.qX j i w ∈ P.Qs (k + 1) :=
  stepTris_subset_Qs k (mem_qX_stepTris j hi hw)

theorem mem_qC {k : ℕ} (j : Fin (P.J + 1)) {i : ℕ} (hi : i < P.K) {w : Rd d} (hw : w ∈ P.S k) :
    P.qC k j i w ∈ P.Qs (k + 1) :=
  mem_Qs_tau j hi (mem_Qs_cost hw)

section Gram

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem Good.gram_rel (hP : P.Good) (hκ : IsLFPPKernel κ) (k : ℕ) {β : TriD d → E}
    (hβ : ∀ t ∈ P.Qs (k + 1), ∀ t' ∈ P.Qs (k + 1), ⟪β t, β t'⟫ = kapD κ t t')
    (j : Fin (P.J + 1)) {i : ℕ} (hi : i < P.K) {w : Rd d} (hw : w ∈ P.S k) :
    β (P.qT k j i w) = β (P.qX j i w) + β (P.qC k j i w) :=
  gram_eq_add_of_rel (P.Qs (k + 1)) (kapD κ) β hβ (mem_qT j hi hw) (mem_qX j hi hw)
    (mem_qC j hi hw) fun t' ht' => hP.kapD_rel κ hκ k j i w (hP.Qs_pos (k + 1) t' ht')

theorem Good.field_rel (hP : P.Good) (hκ : IsLFPPKernel κ) (k : ℕ) {β : TriD d → E}
    (hβ : ∀ t ∈ P.Qs (k + 1), ∀ t' ∈ P.Qs (k + 1), ⟪β t, β t'⟫ = kapD κ t t') (x : E)
    (j : Fin (P.J + 1)) {i : ℕ} (hi : i < P.K) {w : Rd d} (hw : w ∈ P.S k) :
    Yf β x (P.qT k j i w) = Yf β x (P.qX j i w) + Yf β x (P.qC k j i w) := by
  simp only [Yf_apply]
  rw [hP.gram_rel κ hκ k hβ j hi hw, inner_add_left]

/-- **Similarity invariance** in the Gram space: `β ∘ τ_{T_i^j}` realizes `kapD` on `Qs k`. -/
theorem Good.gram_tau (hP : P.Good) (hκ : IsLFPPKernel κ) (k : ℕ) {β : TriD d → E}
    (hβ : ∀ t ∈ P.Qs (k + 1), ∀ t' ∈ P.Qs (k + 1), ⟪β t, β t'⟫ = kapD κ t t')
    (j : Fin (P.J + 1)) {i : ℕ} (hi : i < P.K) :
    ∀ t ∈ P.Qs k, ∀ t' ∈ P.Qs k, ⟪β (tau (P.T j i) t), β (tau (P.T j i) t')⟫ = kapD κ t t' := by
  intro t ht t' ht'
  rw [hβ _ (mem_Qs_tau j hi ht) _ (mem_Qs_tau j hi ht')]
  exact kapD_tau hκ (P.T j i) hP.q_pos t t'

end Gram

/-! ## The factors -/

variable (P) in
/-- Root factor: the indicator of the root choice `j`, the test weight and the coarse weight
`e^{ζ Y(ρq, ρ, T_i^j w)}`.  It reads only the root triples. -/
def Aφ (h : Rd d → ℝ) (j : Fin (P.J + 1)) (i : ℕ) (w : Rd d) (Y : TriD d → ℝ) : ℝ :=
  (if P.sel Y = j then 1 else 0) * (h ((P.T j i).app w) * Real.exp (P.ζ * Y (P.qX j i w)))

variable (P) in
/-- Child factor: the child's own weighted occupation of `w`, in the child's coordinates
(the field `Y ∘ τ_{T_i^j}`). -/
def Cφ (k : ℕ) (j : Fin (P.J + 1)) (i : ℕ) (w : Rd d) (Y : TriD d → ℝ) : ℝ :=
  P.occ k w fun t => Y (tau (P.T j i) t)

/-- The child factor in terms of the band `qC`. -/
theorem Cφ_eq (k : ℕ) (j : Fin (P.J + 1)) (i : ℕ) (w : Rd d) (Y : TriD d → ℝ) :
    P.Cφ k j i w Y = Real.exp (P.ζ * Y (P.qC k j i w)) *
      rcW P.N (P.polyOf k (P.dec k fun t => Y (tau (P.T j i) t))) (dlt w fun _ => 1) := by
  rw [Cφ, occ_eq]
  rfl

theorem Cφ_nonneg (k : ℕ) (j : Fin (P.J + 1)) (i : ℕ) (w : Rd d) (Y : TriD d → ℝ) :
    0 ≤ P.Cφ k j i w Y :=
  occ_nonneg k w _

theorem Cφ_le (k : ℕ) (j : Fin (P.J + 1)) (i : ℕ) (w : Rd d) (Y : TriD d → ℝ) :
    P.Cφ k j i w Y ≤ P.Lb k w * Real.exp (P.ζ * Y (P.qC k j i w)) :=
  occ_le k w _

theorem abs_Aφ_le (h : Rd d → ℝ) (j : Fin (P.J + 1)) (i : ℕ) (w : Rd d) (Y : TriD d → ℝ) :
    |P.Aφ h j i w Y| ≤ |h ((P.T j i).app w)| * Real.exp (P.ζ * Y (P.qX j i w)) := by
  unfold Aφ
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  refine mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) ?_
  split_ifs <;> norm_num

/-- **Decomposition over the root choice**: for a field satisfying the band relations, the
depth-`(k+1)` weighted occupation is `Σ_j Σ_i Σ_{w ∈ S k} q Aφ Cφ`. -/
theorem Good.occH_succ_eq (hP : P.Good) (k : ℕ) (h : Rd d → ℝ) (Y : TriD d → ℝ)
    (hrel : ∀ j, ∀ i < P.K, ∀ w ∈ P.S k,
      Y (P.qT k j i w) = Y (P.qX j i w) + Y (P.qC k j i w)) :
    P.occH (k + 1) h Y = ∑ j, ∑ i : Fin P.K, ∑ w ∈ P.S k,
      P.q * (P.Aφ h j i w Y * P.Cφ k j i w Y) := by
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, j₀ = P.sel Y := ⟨_, rfl⟩
  set t := P.dec (k + 1) Y with ht
  have htfst : t.fst = j₀ := by rw [hj₀]; rfl
  have htsnd : ∀ i, t.snd i = P.dec k fun s => Y (tau (P.T j₀ i) s) := by
    intro i
    rw [hj₀]
    rfl
  have hL : P.occH (k + 1) h Y = ∑ i : Fin P.K, ∑ w ∈ P.S k, P.q *
      (h ((P.T j₀ i).app w) * Real.exp (P.ζ * Y (P.qX j₀ i w)) * P.Cφ k j₀ i w Y) := by
    unfold occH
    rw [← ht]
    change rcW P.N (glueFn P.K fun i => (P.polyOf k (t.snd i)).map (P.T t.fst i).app) _ = _
    rw [rcW_glueFn _ _ _ (hP.pieces_ne_nil k t) (hP.junction k t)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [rcW_map_app, rcW_eq_sum_dlt _ _ _ (hP.riemannPts_polyOf_subset k _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [rcW_dlt, htfst, Cφ_eq, htsnd, T_r, abs_of_pos hP.q_pos]
    have hr := hrel j₀ i i.2 w hw
    simp only [qT] at hr
    rw [hr, mul_add, Real.exp_add]
    ring
  rw [hL]
  have hj : ∀ j, ∑ i : Fin P.K, ∑ w ∈ P.S k, P.q * (P.Aφ h j i w Y * P.Cφ k j i w Y) =
      if j₀ = j then ∑ i : Fin P.K, ∑ w ∈ P.S k, P.q *
        (h ((P.T j i).app w) * Real.exp (P.ζ * Y (P.qX j i w)) * P.Cφ k j i w Y) else 0 := by
    intro j
    unfold Aφ
    rw [← hj₀]
    split_ifs with hjj
    · simp only [one_mul]
    · simp only [zero_mul, mul_zero, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_ite_eq]
  simp

/-! ## Measurability and locality of the factors -/

theorem Good.measurable_Aφ (hP : P.Good) (h : Rd d → ℝ) (j : Fin (P.J + 1)) (i : ℕ)
    (w : Rd d) : Measurable (P.Aφ h j i w) := by
  unfold Aφ
  exact (Measurable.ite (hP.measurableSet_sel_eq j) measurable_const measurable_const).mul
    (measurable_const.mul (measurable_exp_eval _ _))

theorem Good.measurable_Cφ (hP : P.Good) (k : ℕ) (j : Fin (P.J + 1)) (i : ℕ) (w : Rd d) :
    Measurable (P.Cφ k j i w) :=
  (hP.measurable_occ k w).comp (measurable_comp_tri _)

theorem Good.Aφ_loc (hP : P.Good) {k : ℕ} (h : Rd d → ℝ) (j : Fin (P.J + 1)) {i : ℕ}
    (hi : i < P.K) {w : Rd d} (hw : w ∈ P.S k) : IsLoc (P.stepTris (P.S k)) (P.Aφ h j i w) := by
  intro Y Y' hY
  unfold Aφ
  rw [hP.sel_loc (P.S k) Y Y' hY, hY _ (mem_qX_stepTris j hi hw)]

theorem Good.Cφ_loc (hP : P.Good) (k : ℕ) (j : Fin (P.J + 1)) (i : ℕ) (w : Rd d) :
    IsLoc ((P.Qs k).image (tau (P.T j i))) (P.Cφ k j i w) := by
  intro Y Y' hY
  unfold Cφ
  exact hP.occ_loc k w _ _ fun t ht => hY _ (Finset.mem_image_of_mem _ ht)

/-! ## Expectations of the factors -/

section GramInt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The root band is independent of the child's finer bands: they lie in disjoint bands. -/
theorem Good.orth_root_child (hP : P.Good) (k : ℕ) {β : TriD d → E}
    (hβ : ∀ t ∈ P.Qs (k + 1), ∀ t' ∈ P.Qs (k + 1), ⟪β t, β t'⟫ = kapD κ t t')
    (j : Fin (P.J + 1)) {i : ℕ} (hi : i < P.K) :
    ∀ t ∈ P.stepTris (P.S k), ∀ t' ∈ (P.Qs k).image (tau (P.T j i)), ⟪β t, β t'⟫ = 0 := by
  intro t ht t' ht'
  obtain ⟨t'', ht'', rfl⟩ := Finset.mem_image.1 ht'
  rw [hβ t (stepTris_subset_Qs k ht) _ (mem_Qs_tau j hi ht'')]
  refine kapD_eq_zero_of_le' κ ?_
  obtain ⟨z, -, rfl⟩ := mem_stepTris_iff.1 ht
  exact hP.tau_Qs_snd_fst_le j i ht''

/-- **The child factor has expectation `M_k(w)`** (similarity invariance in law). -/
theorem Good.integral_Cφ (hP : P.Good) (hκ : IsLFPPKernel κ) (k : ℕ) {β : TriD d → E}
    (hβ : ∀ t ∈ P.Qs (k + 1), ∀ t' ∈ P.Qs (k + 1), ⟪β t, β t'⟫ = kapD κ t t')
    (j : Fin (P.J + 1)) {i : ℕ} (hi : i < P.K) (w : Rd d) :
    ∫ x, P.Cφ k j i w (Yf β x) ∂stdGaussian E = P.Mw κ k w := by
  have h := transfer_integral (kapD κ) (P.Qs k) (fun t => β (tau (P.T j i) t))
    (hP.gram_tau κ hκ k hβ j hi) (hP.measurable_occ k w) (hP.occ_loc k w)
  rw [Mw, gLawD, ← h]
  rfl

theorem Good.integrable_AC (hP : P.Good) (hκ : IsLFPPKernel κ) (k : ℕ) {β : TriD d → E}
    (hβ : ∀ t ∈ P.Qs (k + 1), ∀ t' ∈ P.Qs (k + 1), ⟪β t, β t'⟫ = kapD κ t t')
    (h : Rd d → ℝ) (j : Fin (P.J + 1)) {i : ℕ} (hi : i < P.K) {w : Rd d} (hw : w ∈ P.S k) :
    Integrable (fun x => P.Aφ h j i w (Yf β x) * P.Cφ k j i w (Yf β x)) (stdGaussian E) := by
  refine integrable_of_le_exp ((((hP.measurable_Aφ h j i w).mul
    (hP.measurable_Cφ k j i w)).comp (measurable_Yf β)).aestronglyMeasurable)
    (|h ((P.T j i).app w)| * P.Lb k w) P.ζ (β (P.qT k j i w)) fun x => ?_
  have hrel := hP.field_rel κ hκ k hβ x j hi hw
  have hC0 := Cφ_nonneg k j i w (Yf β x)
  have hA := abs_Aφ_le h j i w (Yf β x)
  have hC := Cφ_le k j i w (Yf β x)
  have hexp : Real.exp (P.ζ * ⟪β (P.qT k j i w), x⟫) =
      Real.exp (P.ζ * Yf β x (P.qX j i w)) * Real.exp (P.ζ * Yf β x (P.qC k j i w)) := by
    rw [← Real.exp_add, ← mul_add, ← hrel]
    rfl
  rw [abs_mul, abs_of_nonneg hC0, hexp]
  calc |P.Aφ h j i w (Yf β x)| * P.Cφ k j i w (Yf β x)
      ≤ (|h ((P.T j i).app w)| * Real.exp (P.ζ * Yf β x (P.qX j i w))) *
          (P.Lb k w * Real.exp (P.ζ * Yf β x (P.qC k j i w))) :=
        mul_le_mul hA hC hC0 (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
    _ = |h ((P.T j i).app w)| * P.Lb k w * (Real.exp (P.ζ * Yf β x (P.qX j i w)) *
          Real.exp (P.ζ * Yf β x (P.qC k j i w))) := by ring

end GramInt

/-- **The exact recursion with a test weight** (HA4 D7): `E occH_{k+1}(h) =`
`Σ_j Σ_i Σ_{w ∈ S k} q · E[1{I = j} h(T_i^j w) e^{ζ Y(ρq,ρ,T_i^j w)}] · M_k(w)`. -/
theorem Good.integral_occH_succ (hP : P.Good) (hκ : IsLFPPKernel κ) (k : ℕ) (h : Rd d → ℝ) :
    ∫ Y, P.occH (k + 1) h Y ∂gLawD κ (P.Qs (k + 1)) =
      ∑ j, ∑ i : Fin P.K, ∑ w ∈ P.S k,
        P.q * ((∫ Y, P.Aφ h j i w Y ∂gLawD κ (P.Qs (k + 1))) * P.Mw κ k w) := by
  obtain ⟨m, β, hβ⟩ := exists_gram_kapD hκ (P.Qs (k + 1)) (hP.Qs_pos (k + 1))
  have hpt : ∀ x, P.occH (k + 1) h (Yf β x) = ∑ j, ∑ i : Fin P.K, ∑ w ∈ P.S k,
      P.q * (P.Aφ h j i w (Yf β x) * P.Cφ k j i w (Yf β x)) := fun x =>
    hP.occH_succ_eq k h _ fun j i hi w hw => hP.field_rel κ hκ k hβ x j hi hw
  have hint : ∀ j (i : Fin P.K) (w : Rd d), w ∈ P.S k → Integrable (fun x => P.q *
      (P.Aφ h j i w (Yf β x) * P.Cφ k j i w (Yf β x))) (stdGaussian _) := fun j i w hw =>
    (hP.integrable_AC κ hκ k hβ h j i.2 hw).const_mul _
  rw [gLawD, ← transfer_integral (kapD κ) (P.Qs (k + 1)) β hβ (hP.measurable_occH (k + 1) h)
    (hP.occH_loc (k + 1) h)]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun w hw => hint j i w hw]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun w hw => hint j i w hw]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun w hw => hint j i w hw]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [integral_const_mul]
  congr 1
  rw [integral_mul_of_orth β (P.stepTris (P.S k)) ((P.Qs k).image (tau (P.T j i)))
    (hP.orth_root_child κ k hβ j i.2) (hP.measurable_Aφ h j i w) (hP.measurable_Cφ k j i w)
    (hP.Aφ_loc h j i.2 hw) (hP.Cφ_loc k j i w), hP.integral_Cφ κ hκ k hβ j i.2 w,
    transfer_integral (kapD κ) (P.Qs (k + 1)) β hβ (hP.measurable_Aφ h j i w)
      ((hP.Aφ_loc h j i.2 hw).mono (stepTris_subset_Qs k))]

/-! ## Summing over the root choice -/

theorem Good.integrable_Aφ (hP : P.Good) (hκ : IsLFPPKernel κ) {k : ℕ} (h : Rd d → ℝ)
    (j : Fin (P.J + 1)) {i : ℕ} (hi : i < P.K) {w : Rd d} (hw : w ∈ P.S k) :
    Integrable (P.Aφ h j i w) (gLawD κ (P.Qs (k + 1))) :=
  Integrable.mono' ((integrable_exp_gLawD hκ (hP.Qs_pos (k + 1)) (mem_qX j hi hw) P.ζ).const_mul
    |h ((P.T j i).app w)|) (hP.measurable_Aφ h j i w).aestronglyMeasurable
    (ae_of_all _ fun Y => by
      rw [Real.norm_eq_abs]
      exact abs_Aφ_le h j i w Y)

/-- `Σ_j E Aφ_j = E[h(T_i^I w) e^{ζ Y(ρq,ρ,T_i^I w)}]`. -/
theorem Good.sum_integral_Aφ (hP : P.Good) (hκ : IsLFPPKernel κ) {k : ℕ} (h : Rd d → ℝ)
    {i : ℕ} (hi : i < P.K) {w : Rd d} (hw : w ∈ P.S k) :
    ∑ j, ∫ Y, P.Aφ h j i w Y ∂gLawD κ (P.Qs (k + 1)) =
      ∫ Y, h ((P.T (P.sel Y) i).app w) *
        Real.exp (P.ζ * Y (P.ρ * P.q, P.ρ, (P.T (P.sel Y) i).app w)) ∂gLawD κ (P.Qs (k + 1)) := by
  rw [← integral_finsetSum _ fun j _ => hP.integrable_Aφ κ hκ h j hi hw]
  congr 1
  funext Y
  unfold Aφ
  have : ∀ j, (if P.sel Y = j then (1 : ℝ) else 0) *
      (h ((P.T j i).app w) * Real.exp (P.ζ * Y (P.qX j i w))) =
      if P.sel Y = j then h ((P.T j i).app w) * Real.exp (P.ζ * Y (P.qX j i w)) else 0 := by
    intro j
    split_ifs <;> ring
  simp_rw [this]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true, qX]

/-! ## The recursion (5.26) -/

/-- Expectations of the tilt do not depend on the ambient set of triples. -/
theorem Good.integral_tiltMass_eq (hP : P.Good) (hκ : IsLFPPKernel κ) {Sμ : Finset (Rd d)}
    {G : Finset (TriD d)} (hSG : P.stepTris Sμ ⊆ G) (hG : ∀ t ∈ G, 0 < t.1)
    (μ : Rd d → ℝ) :
    ∫ Y, P.tiltMass Sμ μ Y ∂gLawD κ (P.stepTris Sμ) = ∫ Y, P.tiltMass Sμ μ Y ∂gLawD κ G :=
  integral_gLawD_eq_of_subset hκ hSG hG (hP.measurable_tiltMass Sμ μ) (hP.tiltMass_loc Sμ μ)

theorem Good.integral_tiltW_eq (hP : P.Good) (hκ : IsLFPPKernel κ) {Sμ : Finset (Rd d)}
    {G : Finset (TriD d)} (hSG : P.stepTris Sμ ⊆ G) (hG : ∀ t ∈ G, 0 < t.1)
    (μ : Rd d → ℝ) (p : Rd d) :
    ∫ Y, P.tiltW Sμ μ Y p ∂gLawD κ (P.stepTris Sμ) = ∫ Y, P.tiltW Sμ μ Y p ∂gLawD κ G :=
  integral_gLawD_eq_of_subset hκ hSG hG (hP.measurable_tiltW Sμ μ p) (hP.tiltW_loc Sμ μ p)

/-- `E occH_{k+1}(h) = q Σ_i Σ_w M_k(w) E[h(T_i^I w) e^{ζ Y(ρq,ρ,T_i^I w)}]`. -/
theorem Good.integral_occH_succ' (hP : P.Good) (hκ : IsLFPPKernel κ) (k : ℕ) (h : Rd d → ℝ) :
    ∫ Y, P.occH (k + 1) h Y ∂gLawD κ (P.Qs (k + 1)) =
      P.q * ∑ i ∈ Finset.range P.K, ∑ w ∈ P.S k, P.Mw κ k w *
        ∫ Y, h ((P.T (P.sel Y) i).app w) *
          Real.exp (P.ζ * Y (P.ρ * P.q, P.ρ, (P.T (P.sel Y) i).app w)) ∂gLawD κ (P.Qs (k + 1)) := by
  rw [hP.integral_occH_succ κ hκ k h, Finset.sum_comm, Finset.mul_sum,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [← hP.sum_integral_Aφ κ hκ h i.2 hw, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `E tiltMass(S k, μ)` as a sum (under the depth-`(k+1)` law). -/
theorem Good.integral_tiltMass_Qs (hP : P.Good) (hκ : IsLFPPKernel κ) (k : ℕ)
    (μ : Rd d → ℝ) :
    ∫ Y, P.tiltMass (P.S k) μ Y ∂gLawD κ (P.Qs (k + 1)) =
      (1 / (P.K : ℝ)) * ∑ i ∈ Finset.range P.K, ∑ w ∈ P.S k, μ w *
        ∫ Y, Real.exp (P.ζ * Y (P.ρ * P.q, P.ρ, (P.T (P.sel Y) i).app w))
          ∂gLawD κ (P.Qs (k + 1)) := by
  have hz : ∀ i ∈ Finset.range P.K, ∀ w ∈ P.S k, ∀ j,
      (P.ρ * P.q, P.ρ, (P.T j i).app w) ∈ P.Qs (k + 1) := fun i hi w hw j =>
    mem_qX j (Finset.mem_range.1 hi) hw
  have hint : ∀ i ∈ Finset.range P.K, ∀ w ∈ P.S k, Integrable (fun Y => μ w *
      Real.exp (P.ζ * Y (P.ρ * P.q, P.ρ, (P.T (P.sel Y) i).app w))) (gLawD κ (P.Qs (k + 1))) :=
    fun i hi w hw => (hP.integrable_exp_sel κ hκ (hP.Qs_pos (k + 1)) (hz i hi w hw)).const_mul _
  unfold tiltMass
  rw [integral_const_mul, integral_finsetSum _ fun i hi => integrable_finsetSum _ fun w hw =>
    hint i hi w hw]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [integral_finsetSum _ fun w hw => hint i hi w hw]
  exact Finset.sum_congr rfl fun w _ => integral_const_mul _ _

/-- `E tiltW(S k, μ)(p)` as a sum (under the depth-`(k+1)` law). -/
theorem Good.integral_tiltW_Qs (hP : P.Good) (hκ : IsLFPPKernel κ) (k : ℕ) (μ : Rd d → ℝ)
    (p : Rd d) :
    ∫ Y, P.tiltW (P.S k) μ Y p ∂gLawD κ (P.Qs (k + 1)) =
      (1 / (P.K : ℝ)) * ∑ i ∈ Finset.range P.K, ∑ w ∈ P.S k, μ w *
        ∫ Y, dlt p (fun _ => (1 : ℝ)) ((P.T (P.sel Y) i).app w) *
          Real.exp (P.ζ * Y (P.ρ * P.q, P.ρ, (P.T (P.sel Y) i).app w))
          ∂gLawD κ (P.Qs (k + 1)) := by
  have hz : ∀ i ∈ Finset.range P.K, ∀ w ∈ P.S k, ∀ j,
      (P.ρ * P.q, P.ρ, (P.T j i).app w) ∈ P.Qs (k + 1) := fun i hi w hw j =>
    mem_qX j (Finset.mem_range.1 hi) hw
  have hpt : ∀ Y : TriD d → ℝ, ∀ i, ∀ w,
      (if (P.T (P.sel Y) i).app w = p then
        μ w * Real.exp (P.ζ * Y (P.ρ * P.q, P.ρ, p)) else 0) =
      μ w * (dlt p (fun _ => (1 : ℝ)) ((P.T (P.sel Y) i).app w) *
        Real.exp (P.ζ * Y (P.ρ * P.q, P.ρ, (P.T (P.sel Y) i).app w))) := by
    intro Y i w
    simp only [dlt]
    split_ifs with h1
    · rw [h1]
      ring
    · ring
  have hmeas : ∀ i w, Measurable fun Y : TriD d → ℝ =>
      dlt p (fun _ => (1 : ℝ)) ((P.T (P.sel Y) i).app w) *
        Real.exp (P.ζ * Y (P.ρ * P.q, P.ρ, (P.T (P.sel Y) i).app w)) := fun i w =>
    hP.measurable_of_sel (Φ := fun j Y => dlt p (fun _ => (1 : ℝ)) ((P.T j i).app w) *
      Real.exp (P.ζ * Y (P.ρ * P.q, P.ρ, (P.T j i).app w))) fun _ =>
      measurable_const.mul (measurable_exp_eval _ _)
  have hint : ∀ i ∈ Finset.range P.K, ∀ w ∈ P.S k, Integrable (fun Y => μ w *
      (dlt p (fun _ => (1 : ℝ)) ((P.T (P.sel Y) i).app w) *
        Real.exp (P.ζ * Y (P.ρ * P.q, P.ρ, (P.T (P.sel Y) i).app w))))
      (gLawD κ (P.Qs (k + 1))) := by
    intro i hi w hw
    refine Integrable.const_mul ?_ _
    refine Integrable.mono' (hP.integrable_exp_sel κ hκ (hP.Qs_pos (k + 1)) (hz i hi w hw))
      (hmeas i w).aestronglyMeasurable (ae_of_all _ fun Y => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_of_le_one_left (Real.exp_pos _).le ?_
    simp only [dlt]
    split_ifs <;> norm_num
  unfold tiltW
  simp_rw [hpt]
  rw [integral_const_mul, integral_finsetSum _ fun i hi => integrable_finsetSum _ fun w hw =>
    hint i hi w hw]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [integral_finsetSum _ fun w hw => hint i hi w hw]
  exact Finset.sum_congr rfl fun w _ => integral_const_mul _ _

/-- **The recursion for the total mass**: `m_{k+1} = K q · E tiltMass(S k, M_k)`. -/
theorem Good.mm_succ (hP : P.Good) (hκ : IsLFPPKernel κ) (k : ℕ) :
    P.mm κ (k + 1) =
      P.K * P.q * ∫ Y, P.tiltMass (P.S k) (P.Mw κ k) Y ∂gLawD κ (P.stepTris (P.S k)) := by
  have hK : (P.K : ℝ) ≠ 0 := by exact_mod_cast hP.K_pos.ne'
  have key : ∀ X : ℝ, P.q * X = P.K * P.q * (1 / P.K * X) := fun X => by
    field_simp
  rw [hP.integral_tiltMass_eq κ hκ (stepTris_subset_Qs k) (hP.Qs_pos (k + 1)),
    hP.integral_tiltMass_Qs κ hκ k, mm, RC_eq_occH, hP.integral_occH_succ' κ hκ k]
  simp only [one_mul]
  exact key _

/-- **The recursion for the occupation weights**: `M_{k+1}(p) = K q · E tiltW(S k, M_k)(p)`. -/
theorem Good.Mw_succ (hP : P.Good) (hκ : IsLFPPKernel κ) (k : ℕ) (p : Rd d) :
    P.Mw κ (k + 1) p =
      P.K * P.q * ∫ Y, P.tiltW (P.S k) (P.Mw κ k) Y p ∂gLawD κ (P.stepTris (P.S k)) := by
  have hK : (P.K : ℝ) ≠ 0 := by exact_mod_cast hP.K_pos.ne'
  have key : ∀ X : ℝ, P.q * X = P.K * P.q * (1 / P.K * X) := fun X => by
    field_simp
  rw [hP.integral_tiltW_eq κ hκ (stepTris_subset_Qs k) (hP.Qs_pos (k + 1)),
    hP.integral_tiltW_Qs κ hκ k, Mw, occ_eq_occH, hP.integral_occH_succ' κ hκ k]
  exact key _

/-- **The exact recursion (5.26)**: with `s = K q`,
`m_{k+1} = s m_k E ∫ e^{ζ Y(ρq,ρ,·)} dν_{I,μ_k}` and `μ_{k+1} = T μ_k`. -/
theorem Good.recursion (hP : P.Good) (hκ : IsLFPPKernel κ) (k : ℕ) :
    P.mm κ (k + 1) = P.K * P.q * P.mm κ k *
        ∫ Y, P.tiltMass (P.S k) (P.mu κ k) Y ∂gLawD κ (P.stepTris (P.S k)) ∧
      ∀ p, P.mu κ (k + 1) p = P.Tmap κ (P.S k) (P.mu κ k) p := by
  have hm := hP.mm_pos κ hκ k
  have hMw : P.Mw κ k = fun w => P.mm κ k * P.mu κ k w :=
    funext fun w => hP.Mw_eq_mm_mul_mu κ hκ k w
  have hmass : ∫ Y, P.tiltMass (P.S k) (P.Mw κ k) Y ∂gLawD κ (P.stepTris (P.S k)) =
      P.mm κ k * ∫ Y, P.tiltMass (P.S k) (P.mu κ k) Y ∂gLawD κ (P.stepTris (P.S k)) := by
    rw [hMw]
    simp_rw [tiltMass_mul]
    rw [integral_const_mul]
  have hW : ∀ p, ∫ Y, P.tiltW (P.S k) (P.Mw κ k) Y p ∂gLawD κ (P.stepTris (P.S k)) =
      P.mm κ k * ∫ Y, P.tiltW (P.S k) (P.mu κ k) Y p ∂gLawD κ (P.stepTris (P.S k)) := by
    intro p
    rw [hMw]
    simp_rw [tiltW_mul]
    rw [integral_const_mul]
  have hrec : P.mm κ (k + 1) = P.K * P.q * P.mm κ k *
      ∫ Y, P.tiltMass (P.S k) (P.mu κ k) Y ∂gLawD κ (P.stepTris (P.S k)) := by
    rw [hP.mm_succ κ hκ k, hmass]
    ring
  refine ⟨hrec, fun p => ?_⟩
  have hKq : (P.K : ℝ) * P.q * P.mm κ k ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by exact_mod_cast hP.K_pos.ne') hP.q_pos.ne') hm.ne'
  rw [mu, hP.Mw_succ κ hκ k, hW, hrec, Tmap, ← mul_assoc, mul_div_mul_left _ _ hKq]

/-- The tilted mass at depth `k` has positive expectation. -/
theorem Good.integral_tiltMass_pos (hP : P.Good) (hκ : IsLFPPKernel κ) (k : ℕ) :
    0 < ∫ Y, P.tiltMass (P.S k) (P.mu κ k) Y ∂gLawD κ (P.stepTris (P.S k)) := by
  have h := (hP.recursion κ hκ k).1
  have hpos := hP.mm_pos κ hκ (k + 1)
  rw [h] at hpos
  have hKqm : 0 < (P.K : ℝ) * P.q * P.mm κ k :=
    mul_pos (mul_pos (by exact_mod_cast hP.K_pos) hP.q_pos) (hP.mm_pos κ hκ k)
  exact pos_of_mul_pos_right hpos hKqm.le

/-- `μ_{k+1}` is carried by `stepPts (S k) = S (k+1)`. -/
theorem Good.Tmap_isFinProb (hP : P.Good) (hκ : IsLFPPKernel κ) (k : ℕ) :
    IsFinProb (P.stepPts (P.S k)) (P.Tmap κ (P.S k) (P.mu κ k)) := by
  have h := hP.mu_isFinProb κ hκ (k + 1)
  refine ⟨fun p hp => ?_, ?_⟩
  · rw [← (hP.recursion κ hκ k).2 p]
    exact h.1 p hp
  · rw [← h.2]
    exact Finset.sum_congr rfl fun p _ => ((hP.recursion κ hκ k).2 p).symm

/-! ## The iteration skeleton (helpers for Lemma 5.4)

The two lemmas below only chain the recursion; their hypotheses are the conclusions (ii) and
(iii) of Lemma 5.3 (proved elsewhere), stated for every finitely supported `μ ∈ C_δ`. -/

/-- If `T` preserves `C_δ` (Lemma 5.3 (ii)) and `μ₀ ∈ C_δ`, then `μ_k ∈ C_δ` for all `k`. -/
theorem Good.mu_inCDelta (hP : P.Good) (hκ : IsLFPPKernel κ) {δ M B : ℝ}
    (h0 : InCDelta δ M B (P.S 0) (P.mu κ 0))
    (hT : ∀ (Sμ : Finset (Rd d)) (μ : Rd d → ℝ), InCDelta δ M B Sμ μ →
      InCDelta δ M B (P.stepPts Sμ) (P.Tmap κ Sμ μ)) :
    ∀ k, InCDelta δ M B (P.S k) (P.mu κ k)
  | 0 => h0
  | k + 1 => by
    have h := hT (P.S k) (P.mu κ k) (Good.mu_inCDelta hP hκ h0 hT k)
    rw [S_succ]
    exact inCDelta_congr (fun p _ => ((hP.recursion κ hκ k).2 p).symm) h

/-- If, in addition, `E tiltMass(μ) ≤ b` for every `μ ∈ C_δ` (Lemma 5.3 (iii)), then
`m_k ≤ (K q b)^k` (the bound (5.27) with `b = 1 - δ²(4e - 5) + θδ²`). -/
theorem Good.mm_le_pow (hP : P.Good) (hκ : IsLFPPKernel κ) {δ M B b : ℝ}
    (h0 : InCDelta δ M B (P.S 0) (P.mu κ 0))
    (hT : ∀ (Sμ : Finset (Rd d)) (μ : Rd d → ℝ), InCDelta δ M B Sμ μ →
      InCDelta δ M B (P.stepPts Sμ) (P.Tmap κ Sμ μ))
    (hb : ∀ (Sμ : Finset (Rd d)) (μ : Rd d → ℝ), InCDelta δ M B Sμ μ →
      ∫ Y, P.tiltMass Sμ μ Y ∂gLawD κ (P.stepTris Sμ) ≤ b) :
    ∀ k, P.mm κ k ≤ (P.K * P.q * b) ^ k
  | 0 => by rw [hP.mm_zero κ hκ, pow_zero]
  | k + 1 => by
    have hμ := hP.mu_inCDelta κ hκ h0 hT k
    have hbk := hb _ _ hμ
    have hpos := hP.integral_tiltMass_pos κ hκ k
    have hKq : 0 ≤ (P.K : ℝ) * P.q :=
      mul_nonneg (by exact_mod_cast hP.K_pos.le) hP.q_pos.le
    have hm := hP.mm_nonneg κ hκ k
    have ih := Good.mm_le_pow hP hκ h0 hT hb k
    rw [(hP.recursion κ hκ k).1, pow_succ]
    calc (P.K : ℝ) * P.q * P.mm κ k *
          ∫ Y, P.tiltMass (P.S k) (P.mu κ k) Y ∂gLawD κ (P.stepTris (P.S k))
        ≤ (P.K : ℝ) * P.q * P.mm κ k * b :=
          mul_le_mul_of_nonneg_left hbk (mul_nonneg hKq hm)
      _ ≤ (P.K : ℝ) * P.q * (P.K * P.q * b) ^ k * b := by
          have hb0 : 0 ≤ b := hpos.le.trans hbk
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ih hKq) hb0
      _ = (P.K * P.q * b) ^ k * (P.K * P.q * b) := by ring

end LParams

end HigherDimLFPP.Lower
