import HigherDimLFPP.Exist.Concentration

/-!
# Concentration for log-Lipschitz functionals of band fields (packet L3b2, MA7 D-4.6)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), Lemma 4.6 ("verbatim" Lemma 2.7) and the uses
of Lemma 2.7 in §§4–6; planning audit `planning/audits/MA7-ref2-sections-4-6.md`, gap G10 and
Details (a) D-4.6.

**Statement (D-4.6).** Let `0 < a ≤ b`, `X` a continuous version of the band field `H_{a,b}`
(`IsBandVersion P W κ a b X`), `K` compact and `Φ` a functional of fields whose logarithm is
`|ξ|`-Lipschitz for the sup norm on `K` among continuous fields. Then `log Φ(X)` is measurable and
integrable, and for `t ≥ 0`
`P[|log Φ(X) - E log Φ(X)| ≥ t] ≤ 2 exp(-t² / (2 ξ² log(b/a)))`
(`measure_abs_log_sub_ge_le_of_logLipschitz`, `integrable_log_of_logLipschitz`).

Nothing in the proof uses the logarithm: everything is proved for an arbitrary functional `F` that
is `L`-Lipschitz for the sup norm on `K` among continuous fields (`IsSupLipschitzOn K L F`), with
the bound `2 exp(-t² / (2 L² log(b/a)))` (`measure_abs_sub_integral_ge_le_of_isSupLipschitzOn`).
Positivity of `Φ` is not needed (`Real.log` is total).

**Proof** (HigherDimLFPP's proof of `IsBandVersion.measure_abs_log_lfppDistOn_sub_ge_le`, with the
log-distance of the interpolated field replaced by `u ↦ F(I_k u)`):
1. `I_k` is an interpolation scheme of mesh `1/(k+1)` on `K` (`HigherDimLFPP.Conc.InterpScheme`, a
   finite partition of unity); `u ↦ F(I_k u)` is `L`-Lipschitz for the sup norm on the node values
   because `I_k u - I_k u'` is a convex combination of `u - u'` on `K`
   (`lipschitzWith_comp_interp`).
2. The node values of `X` form a centered Gaussian vector with variances `log(b/a)`, so Gaussian
   concentration (`Conc.measureReal_abs_sub_integral_ge_le_of_lipschitzWith`) bounds
   `Z_k = F(I_k X)`.
3. `Z_k → F(X)` pointwise (uniform continuity of `X(·, ω)` on `K`, `tendsto_comp_interp`), with
   the integrable domination `|Z_k| ≤ |F 0| + L sup_K |X|`;
   `Conc.measure_abs_sub_integral_ge_le_of_tendsto` passes the bound to the limit. The same
   approximation shows that `F(X)` is measurable (a pointwise limit of measurable functions) and
   integrable.

The hypotheses of D-4.6 are weakened where possible: `ξ` may have any sign (the Lipschitz constant
is `|ξ|`), `a = b` is allowed (the right side is then `2`), and `K` may be empty.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open scoped NNReal ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Conc

variable {d : ℕ}

/-! ### Functionals that are Lipschitz for the sup norm on a set -/

/-- `F` is `L`-Lipschitz for the sup norm on `K`, among continuous fields: for continuous `φ, ψ`
and `M ≥ 0` with `|φ - ψ| ≤ M` on `K`, `|F φ - F ψ| ≤ L M` (the hypothesis of MA7 D-4.6, with
`F = log Φ` and `L = |ξ|`). -/
def IsSupLipschitzOn (K : Set (Rd d)) (L : ℝ) (F : (Rd d → ℝ) → ℝ) : Prop :=
  ∀ φ ψ : Rd d → ℝ, Continuous φ → Continuous ψ → ∀ M : ℝ, 0 ≤ M →
    (∀ z ∈ K, |φ z - ψ z| ≤ M) → |F φ - F ψ| ≤ L * M

namespace IsSupLipschitzOn

variable {K K' : Set (Rd d)} {L L' : ℝ} {F : (Rd d → ℝ) → ℝ}

/-- The Lipschitz constant is nonnegative. -/
theorem nonneg (h : IsSupLipschitzOn K L F) : 0 ≤ L := by
  have h1 := h (fun _ => 0) (fun _ => 0) continuous_const continuous_const 1 zero_le_one
    fun z _ => by rw [sub_self, abs_zero]; exact zero_le_one
  rw [mul_one] at h1
  exact (abs_nonneg _).trans h1

/-- Enlarging the set. -/
theorem mono_set (h : IsSupLipschitzOn K L F) (hKK' : K ⊆ K') : IsSupLipschitzOn K' L F :=
  fun φ ψ hφ hψ M hM0 hM => h φ ψ hφ hψ M hM0 fun z hz => hM z (hKK' hz)

/-- Enlarging the constant. -/
theorem mono_const (h : IsSupLipschitzOn K L F) (hLL' : L ≤ L') : IsSupLipschitzOn K L' F :=
  fun φ ψ hφ hψ M hM0 hM => (h φ ψ hφ hψ M hM0 hM).trans (mul_le_mul_of_nonneg_right hLL' hM0)

/-- Domination: `|F φ| ≤ |F 0| + L M` if `φ` is continuous and `|φ| ≤ M` on `K` (`M ≥ 0`). -/
theorem abs_le (h : IsSupLipschitzOn K L F) {φ : Rd d → ℝ} (hφ : Continuous φ) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ z ∈ K, |φ z| ≤ M) : |F φ| ≤ |F fun _ => 0| + L * M := by
  have h1 := h φ (fun _ => 0) hφ continuous_const M hM0 fun z hz => by
    rw [sub_zero]
    exact hM z hz
  have h2 := abs_sub_abs_le_abs_sub (F φ) (F fun _ => 0)
  linarith

/-- Two continuous fields that agree on `K` have the same value. -/
theorem eq_of_eqOn (h : IsSupLipschitzOn K L F) {φ ψ : Rd d → ℝ} (hφ : Continuous φ)
    (hψ : Continuous ψ) (hφψ : ∀ z ∈ K, φ z = ψ z) : F φ = F ψ := by
  have h1 := h φ ψ hφ hψ 0 le_rfl fun z hz => by rw [hφψ z hz, sub_self, abs_zero]
  rw [mul_zero] at h1
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h1)

end IsSupLipschitzOn

/-! ### Interpolated fields -/

section Interp

variable {K : Set (Rd d)} {δ : ℝ} (S : InterpScheme d K δ) {L : ℝ} {F : (Rd d → ℝ) → ℝ}

/-- **Lipschitz property of the discretized functional** (MA7 D-4.6, HA5 D2 (3)): if `F` is
`L`-Lipschitz for the sup norm on `K`, then `u ↦ F(S.interp u)` is `L`-Lipschitz for the sup
norm on the node values. -/
theorem lipschitzWith_comp_interp (hF : IsSupLipschitzOn K L F) :
    LipschitzWith ⟨L, hF.nonneg⟩ fun u => F (S.interp u) := by
  refine LipschitzWith.of_dist_le_mul fun u u' => ?_
  rw [Real.dist_eq]
  exact hF _ _ (S.continuous_interp u) (S.continuous_interp u') _ dist_nonneg
    fun z hz => S.abs_interp_sub_interp_le hz u u'

/-- **Domination of the discretized functional**: `|F(S.interp u)| ≤ |F 0| + L M` if all
`|u i| ≤ M` (`M ≥ 0`). -/
theorem abs_comp_interp_le (hF : IsSupLipschitzOn K L F) {u : Fin S.n → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i, |u i| ≤ M) : |F (S.interp u)| ≤ |F fun _ => 0| + L * M :=
  hF.abs_le (S.continuous_interp u) hM0 fun _z hz => S.abs_interp_le hz hM

/-- **Approximation by the discretized functional** (HA5 D2 (4)): if `f` is continuous and
oscillates by at most `η` on `δ`-close pairs of `K`, then `|F(S.interp (f ∘ pt)) - F f| ≤ L η`. -/
theorem abs_comp_interp_sub_le (hF : IsSupLipschitzOn K L F) {f : Rd d → ℝ} (hf : Continuous f)
    {η : ℝ} (hη0 : 0 ≤ η) (hη : ∀ i, ∀ z ∈ K, dist z (S.pt i) < δ → |f (S.pt i) - f z| ≤ η) :
    |F (S.interp fun i => f (S.pt i)) - F f| ≤ L * η :=
  hF _ _ (S.continuous_interp _) hf η hη0 fun _z hz => S.abs_interp_comp_sub_le hη hz

end Interp

/-- **Convergence of the discretized functionals** (deterministic): if `φ` is continuous, `K` is
compact and `S k` are interpolation schemes on `K` of mesh `1/(k+1)`, then
`F(S_k.interp (φ ∘ pt)) → F φ`. -/
theorem tendsto_comp_interp {K : Set (Rd d)} (hK : IsCompact K) {L : ℝ}
    {F : (Rd d → ℝ) → ℝ} (hF : IsSupLipschitzOn K L F)
    (S : ∀ k : ℕ, InterpScheme d K (1 / ((k : ℝ) + 1))) {φ : Rd d → ℝ} (hφ : Continuous φ) :
    Tendsto (fun k => F ((S k).interp fun i => φ ((S k).pt i))) atTop (𝓝 (F φ)) := by
  have hL := hF.nonneg
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' : ℝ := ε / (L + 1) with hε'def
  have hε' : 0 < ε' := by positivity
  have huc := hK.uniformContinuousOn_of_continuous hφ.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδpos, hδ'⟩ := huc ε' hε'
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδpos
  refine ⟨N, fun k hk => ?_⟩
  have hkN : 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
    have : (N : ℝ) ≤ k := by exact_mod_cast hk
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hη : ∀ i, ∀ z ∈ K, dist z ((S k).pt i) < 1 / ((k : ℝ) + 1) →
      |φ ((S k).pt i) - φ z| ≤ ε' := by
    intro i z hz hzi
    have h := hδ' ((S k).pt i) ((S k).pt_mem i) z hz (by rw [dist_comm]; linarith)
    rw [Real.dist_eq] at h
    exact h.le
  have h := abs_comp_interp_sub_le (S k) hF hφ hε'.le hη
  have hlt : L * ε' < ε := by
    rw [hε'def, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  rw [Real.dist_eq]
  exact lt_of_le_of_lt h hlt

/-! ### Band fields -/

section Band

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ} {κ : Rd d → ℝ}
  {a b : ℝ} {X : Rd d → Ω → ℝ}

omit [MeasurableSpace Ω] in
/-- **Interpolation approximants** (MA7 D-4.6; HA5 D2 (2)–(4)): for a continuous random field `X`
(every realization continuous), `K` compact and `F` `L`-Lipschitz for the sup norm on `K`, there are
functions `Z_k` of `ω`, each an `L`-Lipschitz function of finitely many values `X(pt_i)` of the
field at points of `K`, dominated by `|F 0| + L sup_K |X|` and converging pointwise to `F(X)`. -/
theorem exists_interp_approx (hXc : ∀ ω, Continuous fun z => X z ω) {K : Set (Rd d)}
    (hK : IsCompact K) {L : ℝ} {F : (Rd d → ℝ) → ℝ} (hF : IsSupLipschitzOn K L F) :
    ∃ Zk : ℕ → Ω → ℝ,
      (∀ k, ∃ (n : ℕ) (pt : Fin n → Rd d) (Ψ : (Fin n → ℝ) → ℝ),
          (∀ i, pt i ∈ K) ∧ LipschitzWith ⟨L, hF.nonneg⟩ Ψ ∧ ∀ ω, Zk k ω = Ψ fun i => X (pt i) ω) ∧
      (∀ k ω, |Zk k ω| ≤ |F fun _ => 0| + L * ⨆ z : K, |X z ω|) ∧
      ∀ ω, Tendsto (fun k => Zk k ω) atTop (𝓝 (F fun z => X z ω)) := by
  have hδ : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  let S : ∀ k : ℕ, InterpScheme d K (1 / ((k : ℝ) + 1)) := fun k =>
    Classical.choice (exists_interpScheme hK (hδ k))
  refine ⟨fun k ω => F ((S k).interp fun i => X ((S k).pt i) ω), fun k =>
    ⟨(S k).n, (S k).pt, fun u => F ((S k).interp u), (S k).pt_mem,
      lipschitzWith_comp_interp (S k) hF, fun ω => rfl⟩, fun k ω => ?_, fun ω => ?_⟩
  · exact abs_comp_interp_le (S k) hF (iSup_abs_nonneg K fun z => X z ω)
      fun i => abs_le_iSup_abs_of_isCompact hK (hXc ω) ((S k).pt_mem i)
  · exact tendsto_comp_interp hK hF S (hXc ω)

/-- **Measurability** (MA7 D-4.6): for a continuous version `X` of a band field, `K` compact and
`F` Lipschitz for the sup norm on `K`, `ω ↦ F(X(·, ω))` is measurable (a pointwise limit of
measurable functions of finitely many field values). -/
theorem measurable_of_isSupLipschitzOn (hX : IsBandVersion P W κ a b X) {K : Set (Rd d)}
    (hK : IsCompact K) {L : ℝ} {F : (Rd d → ℝ) → ℝ} (hF : IsSupLipschitzOn K L F) :
    Measurable fun ω => F fun z => X z ω := by
  obtain ⟨Zk, hrep, -, hlim⟩ := exists_interp_approx hX.continuous hK hF
  have hmeas : ∀ k, Measurable (Zk k) := fun k => by
    obtain ⟨n, pt, Ψ, -, hΨ, hZ⟩ := hrep k
    have e : Zk k = fun ω => Ψ fun i => X (pt i) ω := funext hZ
    rw [e]
    exact hΨ.continuous.measurable.comp (measurable_pi_iff.2 fun i => hX.measurable _)
  exact measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.2 hlim)

/-- **Integrability** (MA7 D-4.6, "`log Φ(X) ∈ L¹`"): for a continuous version `X` of the band
field `H_{a,b}` (`0 < a`), `K` compact and `F` Lipschitz for the sup norm on `K`, `F(X)` is
integrable. -/
theorem integrable_of_isSupLipschitzOn (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) (ha : 0 < a)
    (hX : IsBandVersion P W κ a b X) {K : Set (Rd d)} (hK : IsCompact K) {L : ℝ}
    {F : (Rd d → ℝ) → ℝ} (hF : IsSupLipschitzOn K L F) :
    Integrable (fun ω => F fun z => X z ω) P := by
  have := hW.isProbabilityMeasure
  have hMint := hX.integrable_iSup_abs_of_isCompact hκ hW ha hK
  refine Integrable.mono' ((integrable_const |F fun _ => 0|).add (hMint.const_mul L))
    (measurable_of_isSupLipschitzOn hX hK hF).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact hF.abs_le (hX.continuous ω) (iSup_abs_nonneg K fun z => X z ω)
    fun z hz => abs_le_iSup_abs_of_isCompact hK (hX.continuous ω) hz

/-- **Concentration for sup-Lipschitz functionals** (MA7 D-4.6 with `F` in place of `log Φ`): for a
continuous version `X` of the band field `H_{a,b}` (`0 < a ≤ b`), `K` compact and `F`
`L`-Lipschitz for the sup norm on `K`, for every `t ≥ 0`
`P[|F(X) - E F(X)| ≥ t] ≤ 2 exp(-t² / (2 L² log(b/a)))` (outer measure). -/
theorem measure_abs_sub_integral_ge_le_of_isSupLipschitzOn (hκ : IsLFPPKernel κ)
    (hW : IsWhiteNoise P W) (ha : 0 < a) (hab : a ≤ b) (hX : IsBandVersion P W κ a b X)
    {K : Set (Rd d)} (hK : IsCompact K) {L : ℝ} {F : (Rd d → ℝ) → ℝ}
    (hF : IsSupLipschitzOn K L F) {t : ℝ} (ht : 0 ≤ t) :
    P {ω | t ≤ |(F fun z => X z ω) - ∫ ω', F (fun z => X z ω') ∂P|} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * L ^ 2 * Real.log (b / a)))) := by
  have := hW.isProbabilityMeasure
  obtain ⟨Zk, hrep, hbk, hlim⟩ := exists_interp_approx hX.continuous hK hF
  have hmeas : ∀ k, Measurable (Zk k) := fun k => by
    obtain ⟨n, pt, Ψ, -, hΨ, hZ⟩ := hrep k
    have e : Zk k = fun ω => Ψ fun i => X (pt i) ω := funext hZ
    rw [e]
    exact hΨ.continuous.measurable.comp (measurable_pi_iff.2 fun i => hX.measurable _)
  have hGint : Integrable (fun ω => |F fun _ => 0| + L * ⨆ z : K, |X z ω|) P :=
    (integrable_const _).add ((hX.integrable_iSup_abs_of_isCompact hκ hW ha hK).const_mul L)
  have hv0 : 0 ≤ Real.log (b / a) := Real.log_nonneg ((one_le_div ha).2 hab)
  -- the finite-dimensional bound
  have hfin : ∀ k, ∀ u : ℝ, 0 ≤ u →
      P {ω | u ≤ |Zk k ω - ∫ ω', Zk k ω' ∂P|} ≤
        ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * L ^ 2 * Real.log (b / a)))) := by
    intro k u hu
    obtain ⟨n, pt, Ψ, -, hΨ, hZ⟩ := hrep k
    have e : Zk k = fun ω => Ψ fun i => X (pt i) ω := funext hZ
    rw [e]
    have hY := LQGMetric.SupTail.hasGaussianLaw_finVec (hX.isGaussianProcess hW) pt
    have hvar : ∀ i, Var[fun ω => X (pt i) ω; P] ≤ (√(Real.log (b / a))) ^ 2 := fun i => by
      rw [Real.sq_sqrt hv0, (hX.hasLaw_log hW hκ ha hab _).variance_eq, variance_id_gaussianReal,
        Real.coe_toNNReal _ hv0]
    have h := measureReal_abs_sub_integral_ge_le_of_lipschitzWith hY
      (fun i => hX.integral_eq_zero hW _) (Real.sqrt_nonneg _) hvar hΨ hu
    have key : ∀ c : ℝ≥0, (c : ℝ) = L →
        2 * Real.exp (-u ^ 2 / (2 * ((c : ℝ) * √(Real.log (b / a))) ^ 2)) =
          2 * Real.exp (-u ^ 2 / (2 * L ^ 2 * Real.log (b / a))) := by
      intro c hc
      rw [hc, mul_pow, Real.sq_sqrt hv0, ← mul_assoc]
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (h.trans_eq (key _ rfl))
  have hf : Continuous fun u : ℝ =>
      2 * Real.exp (-u ^ 2 / (2 * L ^ 2 * Real.log (b / a))) := by
    fun_prop
  exact measure_abs_sub_integral_ge_le_of_tendsto (fun k => (hmeas k).aestronglyMeasurable)
    hGint hbk hlim hf hfin ht

/-! ### The logarithmic form (MA7 D-4.6) -/

/-- `log Φ(X)` is measurable when `log Φ` is Lipschitz for the sup norm on a compact set. -/
theorem measurable_log_of_logLipschitz (hX : IsBandVersion P W κ a b X) {K : Set (Rd d)}
    (hK : IsCompact K) (ξ : ℝ) {Φ : (Rd d → ℝ) → ℝ}
    (hΦ : ∀ φ ψ : Rd d → ℝ, Continuous φ → Continuous ψ → ∀ M : ℝ, 0 ≤ M →
      (∀ z ∈ K, |φ z - ψ z| ≤ M) → |Real.log (Φ φ) - Real.log (Φ ψ)| ≤ |ξ| * M) :
    Measurable fun ω => Real.log (Φ fun z => X z ω) :=
  measurable_of_isSupLipschitzOn (F := fun φ => Real.log (Φ φ)) hX hK hΦ

/-- **MA7 D-4.6, integrability**: for a continuous version `X` of the band field `H_{a,b}`
(`0 < a`), `K` compact and `Φ` with `|log Φ(φ) - log Φ(ψ)| ≤ |ξ| sup_K |φ - ψ|` for continuous
`φ, ψ`, `log Φ(X) ∈ L¹`. -/
theorem integrable_log_of_logLipschitz (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) (ha : 0 < a)
    (hX : IsBandVersion P W κ a b X) {K : Set (Rd d)} (hK : IsCompact K) (ξ : ℝ)
    {Φ : (Rd d → ℝ) → ℝ}
    (hΦ : ∀ φ ψ : Rd d → ℝ, Continuous φ → Continuous ψ → ∀ M : ℝ, 0 ≤ M →
      (∀ z ∈ K, |φ z - ψ z| ≤ M) → |Real.log (Φ φ) - Real.log (Φ ψ)| ≤ |ξ| * M) :
    Integrable (fun ω => Real.log (Φ fun z => X z ω)) P :=
  integrable_of_isSupLipschitzOn (F := fun φ => Real.log (Φ φ)) hκ hW ha hX hK hΦ

/-- **MA7 D-4.6 (DGZ Lemma 4.6 and the uses of Lemma 2.7 in §§4–6): concentration for
log-Lipschitz functionals.** Let `0 < a ≤ b`, `X` a continuous version of the band field
`H_{a,b}`, `K` compact, and `Φ` a functional of fields with
`|log Φ(φ) - log Φ(ψ)| ≤ |ξ| sup_K |φ - ψ|` for continuous `φ, ψ` (in the form: for every `M ≥ 0`
with `|φ - ψ| ≤ M` on `K`, the difference of the logarithms is at most `|ξ| M`). Then for `t ≥ 0`
`P[|log Φ(X) - E log Φ(X)| ≥ t] ≤ 2 exp(-t² / (2 ξ² log(b/a)))` (outer measure). -/
theorem measure_abs_log_sub_ge_le_of_logLipschitz (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    (ha : 0 < a) (hab : a ≤ b) (hX : IsBandVersion P W κ a b X) {K : Set (Rd d)}
    (hK : IsCompact K) (ξ : ℝ) {Φ : (Rd d → ℝ) → ℝ}
    (hΦ : ∀ φ ψ : Rd d → ℝ, Continuous φ → Continuous ψ → ∀ M : ℝ, 0 ≤ M →
      (∀ z ∈ K, |φ z - ψ z| ≤ M) → |Real.log (Φ φ) - Real.log (Φ ψ)| ≤ |ξ| * M)
    {t : ℝ} (ht : 0 ≤ t) :
    P {ω | t ≤ |Real.log (Φ fun z => X z ω) - ∫ ω', Real.log (Φ fun z => X z ω') ∂P|} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ξ ^ 2 * Real.log (b / a)))) := by
  have h := measure_abs_sub_integral_ge_le_of_isSupLipschitzOn (F := fun φ => Real.log (Φ φ))
    hκ hW ha hab hX hK hΦ ht
  rwa [sq_abs] at h

end Band

end HigherDimLQGMetric.DGZ
