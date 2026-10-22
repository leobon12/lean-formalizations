import HigherDimLQGMetric.DGZ.Concentration
import HigherDimLFPP.Field.FiniteRange
import LQGMetric.Gaussian.AssociationEvents
import LQGMetric.Papers.DDDF.L13Limit

/-!
# FKG (Harris) inequality for monotone functionals of a band field (packet L3b3, MA7 D-FKG)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), footnote to Lemma 6.5 (TeX l. 2992: "the FKG
inequality for `h_n`, by approximating `h_n` with step functions") and its uses in Lemmas 6.5–6.7;
planning audit `planning/audits/MA7-ref2-sections-4-6.md`, gap G20 and Details (a) D-FKG; ruling M6
(nonnegative kernels).

**Statement (D-FKG).** Let `X` be a continuous version of the band field `H_{a,b}` (`0 < a`) over
a white noise, `K` compact, and `F_i` (`i` in a finite index set) functionals of continuous fields
that are nondecreasing (`φ ≤ ψ ⟹ F φ ≤ F ψ`, `IsMonotoneFunctional`) and continuous for
`sup_K |φ - ψ| → 0` (`IsSupContinuousOn K`). Then for all thresholds `t_i`
* `∏ᵢ P[F_i(X) > t_i] ≤ P[⋂ᵢ {F_i(X) > t_i}]` (`fkg_increasing`),
* `∏ᵢ P[F_i(X) < t_i] ≤ P[⋂ᵢ {F_i(X) < t_i}]` (`fkg_decreasing`),
and the same with non-strict thresholds (`fkg_increasing_le`, `fkg_decreasing_le`). The events
are measurable (`measurable_comp_of_isSupContinuousOn`); MA7's hypothesis "`F_i(X)` measurable" is
proved, not assumed. The real-valued forms over a `Fintype` index are `fkg_increasing_real`, … .

**Proof** (MA7 D-FKG).
1. *Nonnegative covariance.* `Cov(X(x), X(y)) = ⟪k_{a,b,x}, k_{a,b,y}⟫ = ∫_a^b C((x-y)/t) dt/t ≥ 0`
   (`IsWhiteNoise.cov_eq`, `inner_bandVec`, `autoCorr_nonneg`; here `κ ≥ 0` is used, ruling M6).
2. *Monotone interpolation.* For an interpolation scheme `S` on `K` (HigherDimLFPP
   `Conc.InterpScheme`: nodes in `K`, continuous weights `w_j ≥ 0`, a partition of unity on `K`),
   `S.interp u = ∑_j w_j u_j` is nondecreasing in `u` everywhere on `ℝ^d` (weights `≥ 0`), so
   `u ↦ F_i(S.interp u)` is nondecreasing and, by sup-continuity, continuous. The sets
   `{u : t_i < F_i(S.interp u)}` are open upper sets of `ℝ^{nodes}`.
3. *Pitt.* The node vector `(X(pt_j))_j` is Gaussian with nonnegative covariances, so Pitt's
   inequality for increasing events (`LQGMetric.Pitt.prod_prob_le_biInter`) gives the association of
   `Z_{k,i} = F_i(S_k.interp (X ∘ pt))` for every scheme `S_k`.
4. *Limit.* With `S_k` of mesh `1/(k+1)`, `Z_{k,i} → F_i(X)` pointwise (uniform continuity of
   `X(·, ω)` on `K` and sup-continuity of `F_i`), and `LQGMetric.DDDF.assoc_of_tendsto` passes the
   association to the limit (pattern of `LQGMetric.DDDF.lemma13_cross`).
5. *Decreasing events.* `-X` is a band version over the white noise `-W`, and
   `G_i(φ) = -F_i(-φ)` is again monotone and sup-continuous; `{F_i(X) < t_i} = {G_i(-X) > -t_i}`.
6. *Non-strict thresholds.* `{F ≥ t} = ⋂_n {F > t - 1/(n+1)}` (decreasing in `n`); continuity of
   `P` from above passes the strict inequality to the limit (`prod_measureReal_le_of_lt`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Conc

variable {d : ℕ}

/-! ### Monotone and sup-continuous functionals -/

/-- `F` is nondecreasing in the field, among continuous fields: `φ ≤ ψ` everywhere implies
`F φ ≤ F ψ` (MA7 D-FKG). -/
def IsMonotoneFunctional (F : (Rd d → ℝ) → ℝ) : Prop :=
  ∀ φ ψ : Rd d → ℝ, Continuous φ → Continuous ψ → (∀ z, φ z ≤ ψ z) → F φ ≤ F ψ

/-- `F` is continuous for the sup norm on `K`, among continuous fields: for every continuous `φ`
and `ε > 0` there is `δ > 0` with `|F φ - F ψ| ≤ ε` for every continuous `ψ` with `|φ - ψ| ≤ δ`
on `K` (MA7 D-FKG: "continuous for `sup_K |φ - ψ| → 0`"). -/
def IsSupContinuousOn (K : Set (Rd d)) (F : (Rd d → ℝ) → ℝ) : Prop :=
  ∀ φ : Rd d → ℝ, Continuous φ → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ ψ : Rd d → ℝ, Continuous ψ → (∀ z ∈ K, |φ z - ψ z| ≤ δ) → |F φ - F ψ| ≤ ε

namespace IsMonotoneFunctional

variable {F : (Rd d → ℝ) → ℝ}

/-- `φ ↦ -F(-φ)` is monotone when `F` is. -/
theorem neg_comp_neg (h : IsMonotoneFunctional F) :
    IsMonotoneFunctional fun φ => -F fun z => -φ z :=
  fun _ _ hφ hψ hle => neg_le_neg (h _ _ hψ.neg hφ.neg fun z => neg_le_neg (hle z))

end IsMonotoneFunctional

namespace IsSupContinuousOn

variable {K K' : Set (Rd d)} {F : (Rd d → ℝ) → ℝ}

/-- Enlarging the set. -/
theorem mono_set (h : IsSupContinuousOn K F) (hKK' : K ⊆ K') : IsSupContinuousOn K' F :=
  fun φ hφ ε hε => let ⟨δ, hδ, hF⟩ := h φ hφ ε hε
    ⟨δ, hδ, fun ψ hψ hM => hF ψ hψ fun z hz => hM z (hKK' hz)⟩

/-- `φ ↦ -F(-φ)` is sup-continuous when `F` is. -/
theorem neg_comp_neg (h : IsSupContinuousOn K F) :
    IsSupContinuousOn K fun φ => -F fun z => -φ z := by
  intro φ hφ ε hε
  obtain ⟨δ, hδ, hF⟩ := h (fun z => -φ z) hφ.neg ε hε
  refine ⟨δ, hδ, fun ψ hψ hM => ?_⟩
  have h1 := hF (fun z => -ψ z) hψ.neg fun z hz => by
    rw [show -φ z - -ψ z = -(φ z - ψ z) by ring, abs_neg]
    exact hM z hz
  rw [show -F (fun z => -φ z) - -F (fun z => -ψ z) = -(F (fun z => -φ z) - F fun z => -ψ z) by
    ring, abs_neg]
  exact h1

/-- Two continuous fields that agree on `K` have the same value. -/
theorem eq_of_eqOn (h : IsSupContinuousOn K F) {φ ψ : Rd d → ℝ} (hφ : Continuous φ)
    (hψ : Continuous ψ) (hφψ : ∀ z ∈ K, φ z = ψ z) : F φ = F ψ := by
  refine eq_of_abs_sub_le_all fun ε hε => ?_
  obtain ⟨δ, hδ, hF⟩ := h φ hφ ε hε
  exact hF ψ hψ fun z hz => by rw [hφψ z hz, sub_self, abs_zero]; exact hδ.le

end IsSupContinuousOn

/-- A sup-Lipschitz functional (L3b2's `IsSupLipschitzOn`) is sup-continuous. -/
theorem IsSupLipschitzOn.isSupContinuousOn {K : Set (Rd d)} {L : ℝ} {F : (Rd d → ℝ) → ℝ}
    (h : IsSupLipschitzOn K L F) : IsSupContinuousOn K F := by
  intro φ hφ ε hε
  have hL := h.nonneg
  refine ⟨ε / (L + 1), by positivity, fun ψ hψ hM => ?_⟩
  refine (h φ ψ hφ hψ (ε / (L + 1)) (by positivity) hM).trans ?_
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith

/-- `1 - e^{-x} ≤ x ≤ e^x - 1` for every real `x`. -/
theorem one_sub_exp_neg_le_exp_sub_one (x : ℝ) :
    1 - Real.exp (-x) ≤ Real.exp x - 1 := by
  have h1 := Real.add_one_le_exp x
  have h2 := Real.add_one_le_exp (-x)
  linarith

/-- **Multiplicative comparison implies sup-continuity**: if `F ≥ 0` on continuous fields and
`F φ ≤ e^{c M} F ψ` whenever `|φ - ψ| ≤ M` on `K` (`c ≥ 0`), then `F` is sup-continuous on `K`.
All LFPP functionals of MA7 Details (c) satisfy this with `c = |ξ|` (their `*_le_exp_mul`
lemmas). -/
theorem IsSupContinuousOn.of_le_exp_mul {K : Set (Rd d)} {F : (Rd d → ℝ) → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hnn : ∀ φ : Rd d → ℝ, Continuous φ → 0 ≤ F φ)
    (h : ∀ φ ψ : Rd d → ℝ, Continuous φ → Continuous ψ → ∀ M : ℝ, 0 ≤ M →
      (∀ z ∈ K, |φ z - ψ z| ≤ M) → F φ ≤ Real.exp (c * M) * F ψ) :
    IsSupContinuousOn K F := by
  intro φ hφ ε hε
  have hF0 := hnn φ hφ
  set η : ℝ := ε / (F φ + 1) with hη
  have hη0 : 0 < η := by positivity
  set δ : ℝ := Real.log (1 + η) / (c + 1) with hδ
  have hlog : 0 < Real.log (1 + η) := Real.log_pos (by linarith)
  have hδ0 : 0 < δ := by positivity
  refine ⟨δ, hδ0, fun ψ hψ hM => ?_⟩
  have hcδ : c * δ ≤ Real.log (1 + η) := by
    rw [hδ, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have hE : Real.exp (c * δ) - 1 ≤ η := by
    have := Real.exp_le_exp.2 hcδ
    rw [Real.exp_log (by linarith)] at this
    linarith
  have hE0 : 0 ≤ c * δ := by positivity
  have hEη : (Real.exp (c * δ) - 1) * F φ ≤ ε := by
    calc (Real.exp (c * δ) - 1) * F φ ≤ η * F φ := mul_le_mul_of_nonneg_right hE hF0
      _ ≤ ε := by
        rw [hη, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
  -- `F ψ ≤ e^{cδ} F φ` and `F φ ≤ e^{cδ} F ψ`
  have h1 := h ψ φ hψ hφ δ hδ0.le fun z hz => by rw [abs_sub_comm]; exact hM z hz
  have h2 := h φ ψ hφ hψ δ hδ0.le hM
  have hexp : 0 < Real.exp (c * δ) := Real.exp_pos _
  have h3 : Real.exp (-(c * δ)) * F φ ≤ F ψ := by
    rw [Real.exp_neg, inv_mul_le_iff₀ hexp]
    exact h2
  have h4 := one_sub_exp_neg_le_exp_sub_one (c * δ)
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- **Log-Lipschitz positive functionals are sup-continuous**: if `Φ > 0` on continuous fields and
`|log Φ(φ) - log Φ(ψ)| ≤ |ξ| M` whenever `|φ - ψ| ≤ M` on `K` (the hypothesis of MA7 D-4.6), then
`Φ` is sup-continuous on `K`. -/
theorem IsSupContinuousOn.of_logLipschitz {K : Set (Rd d)} {ξ : ℝ} {Φ : (Rd d → ℝ) → ℝ}
    (hpos : ∀ φ : Rd d → ℝ, Continuous φ → 0 < Φ φ)
    (hΦ : ∀ φ ψ : Rd d → ℝ, Continuous φ → Continuous ψ → ∀ M : ℝ, 0 ≤ M →
      (∀ z ∈ K, |φ z - ψ z| ≤ M) → |Real.log (Φ φ) - Real.log (Φ ψ)| ≤ |ξ| * M) :
    IsSupContinuousOn K Φ := by
  refine IsSupContinuousOn.of_le_exp_mul (abs_nonneg ξ) (fun φ hφ => (hpos φ hφ).le)
    fun φ ψ hφ hψ M hM0 hM => ?_
  have h1 := (abs_le.1 (hΦ φ ψ hφ hψ M hM0 hM)).2
  have h2 : Real.log (Φ φ) ≤ Real.log (Real.exp (|ξ| * M) * Φ ψ) := by
    rw [Real.log_mul (Real.exp_pos _).ne' (hpos ψ hψ).ne', Real.log_exp]
    linarith
  exact (Real.log_le_log_iff (hpos φ hφ) (by positivity [hpos ψ hψ])).1 h2

/-! ### Interpolated fields -/

namespace InterpFKG

variable {K : Set (Rd d)} {δ : ℝ} (S : InterpScheme d K δ)

/-- **Monotonicity of the interpolation**: the weights are nonnegative everywhere, so
`u ≤ u'` implies `S.interp u ≤ S.interp u'` on all of `ℝ^d`. -/
theorem interp_mono {u u' : Fin S.n → ℝ} (h : u ≤ u') (z : Rd d) :
    S.interp u z ≤ S.interp u' z :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (S.w_nonneg i z)

/-- The discretized functional `u ↦ F(S.interp u)` is monotone. -/
theorem monotone_comp_interp {F : (Rd d → ℝ) → ℝ} (hF : IsMonotoneFunctional F) :
    Monotone fun u => F (S.interp u) :=
  fun _ _ h => hF _ _ (S.continuous_interp _) (S.continuous_interp _) (interp_mono S h)

/-- The discretized functional `u ↦ F(S.interp u)` is continuous. -/
theorem continuous_comp_interp {F : (Rd d → ℝ) → ℝ} (hF : IsSupContinuousOn K F) :
    Continuous fun u => F (S.interp u) := by
  refine Metric.continuous_iff.2 fun u ε hε => ?_
  obtain ⟨η, hη, hFη⟩ := hF (S.interp u) (S.continuous_interp u) (ε / 2) (half_pos hε)
  refine ⟨η, hη, fun u' hu' => ?_⟩
  rw [Real.dist_eq, abs_sub_comm]
  refine (hFη _ (S.continuous_interp u') fun z hz => ?_).trans_lt (half_lt_self hε)
  exact (S.abs_interp_sub_interp_le hz u u').trans (by rw [dist_comm]; exact hu'.le)

/-- The sets `{u : t < F(S.interp u)}` are open upper sets. -/
theorem isUpperSet_setOf_lt {F : (Rd d → ℝ) → ℝ} (hF : IsMonotoneFunctional F) (t : ℝ) :
    IsUpperSet {u : Fin S.n → ℝ | t < F (S.interp u)} :=
  fun _ _ h hu => lt_of_lt_of_le hu (monotone_comp_interp S hF h)

end InterpFKG

/-- **Convergence of the discretized functionals** (deterministic): if `φ` is continuous, `K` is
compact, `F` is sup-continuous on `K` and `S k` are interpolation schemes on `K` of mesh `1/(k+1)`,
then `F(S_k.interp (φ ∘ pt)) → F φ`. -/
theorem tendsto_comp_interp_of_isSupContinuousOn {K : Set (Rd d)} (hK : IsCompact K)
    {F : (Rd d → ℝ) → ℝ} (hF : IsSupContinuousOn K F)
    (S : ∀ k : ℕ, InterpScheme d K (1 / ((k : ℝ) + 1))) {φ : Rd d → ℝ} (hφ : Continuous φ) :
    Tendsto (fun k => F ((S k).interp fun i => φ ((S k).pt i))) atTop (𝓝 (F φ)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨η, hη, hFη⟩ := hF φ hφ (ε / 2) (half_pos hε)
  have huc := hK.uniformContinuousOn_of_continuous hφ.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδpos, hδ'⟩ := huc η hη
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδpos
  refine ⟨N, fun k hk => ?_⟩
  have hkN : 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
    have : (N : ℝ) ≤ k := by exact_mod_cast hk
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hosc : ∀ i, ∀ z ∈ K, dist z ((S k).pt i) < 1 / ((k : ℝ) + 1) →
      |φ ((S k).pt i) - φ z| ≤ η := by
    intro i z hz hzi
    have h := hδ' ((S k).pt i) ((S k).pt_mem i) z hz (by rw [dist_comm]; linarith)
    rw [Real.dist_eq] at h
    exact h.le
  have h := hFη _ ((S k).continuous_interp _) fun z hz => by
    rw [abs_sub_comm]
    exact (S k).abs_interp_comp_sub_le hosc hz
  rw [Real.dist_eq, abs_sub_comm]
  exact h.trans_lt (half_lt_self hε)

/-! ### Band fields: covariance, approximation, measurability -/

section Band

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ} {κ : Rd d → ℝ}
  {a b : ℝ} {X : Rd d → Ω → ℝ}

/-- **Nonnegative covariance of a band field** (MA7 D-FKG, ruling M6):
`Cov(X(x), X(y)) = ∫_a^b C((x - y)/t) dt/t ≥ 0`, since the autocorrelation `C = κ ⋆ κ` of the
nonnegative kernel `κ` is nonnegative. -/
theorem covariance_nonneg_of_isBandVersion (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    (ha : 0 < a) (hX : IsBandVersion P W κ a b X) (x y : Rd d) :
    0 ≤ cov[X x, X y; P] := by
  rw [covariance_congr_ae (hX.ae_eq x) (hX.ae_eq y), hW.cov_eq, inner_bandVec hκ ha ha]
  refine setIntegral_nonneg measurableSet_Ioo fun t ht => ?_
  have ht0 : 0 < t := lt_of_lt_of_le ha (le_max_left a a) |>.trans ht.1
  exact div_nonneg (autoCorr_nonneg hκ _) ht0.le

/-- **Association of the discretized functionals** (Pitt's inequality, MA7 D-FKG step 3): for an
interpolation scheme `S` on `K` and monotone sup-continuous `F_i`,
`∏ᵢ P[t_i < F_i(S.interp (X ∘ pt))] ≤ P[⋂ᵢ {t_i < F_i(S.interp (X ∘ pt))}]`. -/
theorem prod_measureReal_le_of_interp (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    (ha : 0 < a) (hX : IsBandVersion P W κ a b X) {K : Set (Rd d)} {δ : ℝ}
    (S : InterpScheme d K δ) {ι : Type*} [Fintype ι] {F : ι → (Rd d → ℝ) → ℝ}
    (hF : ∀ i, IsSupContinuousOn K (F i)) (hmono : ∀ i, IsMonotoneFunctional (F i)) (t : ι → ℝ) :
    ∏ i, P.real {ω | t i < F i (S.interp fun j => X (S.pt j) ω)} ≤
      P.real (⋂ i, {ω | t i < F i (S.interp fun j => X (S.pt j) ω)}) := by
  have hG := LQGMetric.SupTail.hasGaussianLaw_finVec (hX.isGaussianProcess hW) S.pt
  have h := LQGMetric.Pitt.prod_prob_le_biInter hG
    (fun i j => covariance_nonneg_of_isBandVersion hκ hW ha hX (S.pt i) (S.pt j))
    (U := fun i => {u : Fin S.n → ℝ | t i < F i (S.interp u)})
    (fun i => (isOpen_lt continuous_const
      (InterpFKG.continuous_comp_interp S (hF i))).measurableSet)
    (fun i => InterpFKG.isUpperSet_setOf_lt S (hmono i) (t i)) Finset.univ
  simp only [Finset.mem_univ, iInter_true] at h
  exact h

/-- A fixed choice of interpolation schemes of mesh `1/(k+1)` on a compact set `K`
(HigherDimLFPP `exists_interpScheme`). -/
def interpSchemes {K : Set (Rd d)} (hK : IsCompact K) (k : ℕ) :
    InterpScheme d K (1 / ((k : ℝ) + 1)) :=
  Classical.choice (exists_interpScheme hK (by positivity))

/-- **Measurability of sup-continuous functionals** of a continuous version of a band field. -/
theorem measurable_comp_of_isSupContinuousOn (hX : IsBandVersion P W κ a b X) {K : Set (Rd d)}
    (hK : IsCompact K) {F : (Rd d → ℝ) → ℝ} (hF : IsSupContinuousOn K F) :
    Measurable fun ω => F fun z => X z ω := by
  set S := interpSchemes hK
  have hm : ∀ k, Measurable fun ω => F ((S k).interp fun j => X ((S k).pt j) ω) := fun k =>
    (InterpFKG.continuous_comp_interp (S k) hF).measurable.comp
      (measurable_pi_iff.2 fun j => hX.measurable _)
  exact measurable_of_tendsto_metrizable hm (tendsto_pi_nhds.2 fun ω =>
    tendsto_comp_interp_of_isSupContinuousOn hK hF S (hX.continuous ω))

/-! ### The FKG inequality, increasing events -/

/-- **FKG inequality for increasing events, real form** (MA7 D-FKG; DGZ footnote to Lemma 6.5):
for a continuous version `X` of the band field `H_{a,b}` (`0 < a`) of a nonnegative admissible
kernel, `K` compact, and finitely many monotone functionals `F_i` that are continuous for the sup
norm on `K`, `∏ᵢ P[F_i(X) > t_i] ≤ P[⋂ᵢ {F_i(X) > t_i}]`. -/
theorem fkg_increasing_real (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) (ha : 0 < a)
    (hX : IsBandVersion P W κ a b X) {K : Set (Rd d)} (hK : IsCompact K) {ι : Type*} [Fintype ι]
    {F : ι → (Rd d → ℝ) → ℝ} (hF : ∀ i, IsSupContinuousOn K (F i))
    (hmono : ∀ i, IsMonotoneFunctional (F i)) (t : ι → ℝ) :
    ∏ i, P.real {ω | t i < F i fun z => X z ω} ≤
      P.real (⋂ i, {ω | t i < F i fun z => X z ω}) := by
  have := hW.isProbabilityMeasure
  set S := interpSchemes hK
  set Z : ℕ → ι → Ω → ℝ := fun k i ω => F i ((S k).interp fun j => X ((S k).pt j) ω) with hZ
  have hZm : ∀ k i, Measurable (Z k i) := fun k i =>
    (InterpFKG.continuous_comp_interp (S k) (hF i)).measurable.comp
      (measurable_pi_iff.2 fun j => hX.measurable _)
  have hlim : ∀ i ω, Tendsto (fun k => Z k i ω) atTop (𝓝 (F i fun z => X z ω)) := fun i ω =>
    tendsto_comp_interp_of_isSupContinuousOn hK (hF i) S (hX.continuous ω)
  have hZlm : ∀ i, Measurable fun ω => F i fun z => X z ω := fun i =>
    measurable_comp_of_isSupContinuousOn hX hK (hF i)
  have hass : ∀ k (c : ι → ℝ), ∏ i, P.real {ω | c i < Z k i ω} ≤
      P.real (⋂ i, {ω | c i < Z k i ω}) := fun k c =>
    prod_measureReal_le_of_interp hκ hW ha hX (S k) hF hmono c
  exact LQGMetric.DDDF.assoc_of_tendsto (Zl := fun i ω => F i fun z => X z ω) hZm hZlm hlim
    hass t

/-! ### The FKG inequality, decreasing events -/

/-- `-W` is a white noise (the law of `∑ cᵢ (-W fᵢ) = ∑ (-cᵢ) W fᵢ` is `N(0, ‖∑ cᵢ fᵢ‖²)`). -/
theorem isWhiteNoise_neg (hW : IsWhiteNoise P W) : IsWhiteNoise P fun f ω => -W f ω where
  measurable f := (hW.measurable f).neg
  hasLaw f c := by
    have h := hW.hasLaw f fun i => -c i
    have e1 : (fun ω => ∑ i, c i * -W (f i) ω) = fun ω => ∑ i, -c i * W (f i) ω := by
      funext ω
      exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ‖∑ i, -c i • f i‖ = ‖∑ i, c i • f i‖ := by
      rw [← norm_neg]
      congr 1
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [neg_smul, neg_neg]
    rw [e1]
    rw [e2] at h
    exact h

/-- `-X` is a continuous version of the band field `H_{a,b}` over the white noise `-W`. -/
theorem isBandVersion_neg (hX : IsBandVersion P W κ a b X) :
    IsBandVersion P (fun f ω => -W f ω) κ a b fun z ω => -X z ω where
  continuous ω := (hX.continuous ω).neg
  measurable z := (hX.measurable z).neg
  ae_eq z := by
    filter_upwards [hX.ae_eq z] with ω h
    rw [h]

/-- **FKG inequality for decreasing events, real form** (MA7 D-FKG): under the hypotheses of
`fkg_increasing_real`, `∏ᵢ P[F_i(X) < t_i] ≤ P[⋂ᵢ {F_i(X) < t_i}]`. Proof: apply the increasing
form to the band version `-X` over the white noise `-W` and to `G_i(φ) = -F_i(-φ)`. -/
theorem fkg_decreasing_real (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) (ha : 0 < a)
    (hX : IsBandVersion P W κ a b X) {K : Set (Rd d)} (hK : IsCompact K) {ι : Type*} [Fintype ι]
    {F : ι → (Rd d → ℝ) → ℝ} (hF : ∀ i, IsSupContinuousOn K (F i))
    (hmono : ∀ i, IsMonotoneFunctional (F i)) (t : ι → ℝ) :
    ∏ i, P.real {ω | (F i fun z => X z ω) < t i} ≤
      P.real (⋂ i, {ω | (F i fun z => X z ω) < t i}) := by
  have h := fkg_increasing_real hκ (isWhiteNoise_neg hW) ha (isBandVersion_neg hX) hK
    (F := fun i φ => -F i fun z => -φ z) (fun i => (hF i).neg_comp_neg)
    (fun i => (hmono i).neg_comp_neg) fun i => -t i
  have e : ∀ i, {ω | -t i < -F i fun z => - -X z ω} = {ω | (F i fun z => X z ω) < t i} :=
    fun i => by
      ext ω
      simp only [neg_neg, mem_ofPred_eq, neg_lt_neg_iff]
  simp only [e] at h
  exact h

/-! ### Non-strict thresholds -/

/-- **From strict to non-strict thresholds** (measure theory): if finitely many measurable
`G_i` are associated for all strict thresholds, they are associated for all non-strict ones
(`{G ≥ t} = ⋂_n {G > t - 1/(n+1)}`, continuity of `P` from above). -/
theorem prod_measureReal_le_of_lt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ι : Type*} [Fintype ι] {G : ι → Ω → ℝ}
    (hG : ∀ i, Measurable (G i))
    (h : ∀ c : ι → ℝ, ∏ i, P.real {ω | c i < G i ω} ≤ P.real (⋂ i, {ω | c i < G i ω}))
    (t : ι → ℝ) :
    ∏ i, P.real {ω | t i ≤ G i ω} ≤ P.real (⋂ i, {ω | t i ≤ G i ω}) := by
  set A : ℕ → ι → Set Ω := fun n i => {ω | t i - 1 / ((n : ℝ) + 1) < G i ω} with hA
  have hAm : ∀ n i, MeasurableSet (A n i) := fun n i => measurableSet_lt measurable_const (hG i)
  have hanti : ∀ i, Antitone fun n => A n i := fun i n n' hnn' ω hω => by
    simp only [hA, mem_ofPred_eq] at hω ⊢
    have : 1 / ((n' : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnn' 1)
    linarith
  have hinter : ∀ i, ⋂ n, A n i = {ω | t i ≤ G i ω} := fun i => by
    ext ω
    simp only [mem_iInter, hA, mem_ofPred_eq]
    constructor
    · intro hω
      by_contra hc
      push Not at hc
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hc)
      have := hω n
      linarith
    · intro hω n
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have ht1 : ∀ i, Tendsto (fun n => P.real (A n i)) atTop (𝓝 (P.real {ω | t i ≤ G i ω})) :=
    fun i => by
      have h1 := tendsto_measure_iInter_atTop (μ := P) (fun n => (hAm n i).nullMeasurableSet)
        (hanti i) ⟨0, measure_ne_top _ _⟩
      rw [hinter i] at h1
      exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h1
  have ht2 : Tendsto (fun n => P.real (⋂ i, A n i)) atTop
      (𝓝 (P.real (⋂ i, {ω | t i ≤ G i ω}))) := by
    have hm : ∀ n, MeasurableSet (⋂ i, A n i) := fun n => MeasurableSet.iInter fun i => hAm n i
    have hanti' : Antitone fun n => ⋂ i, A n i := fun n n' hnn' =>
      iInter_mono fun i => hanti i hnn'
    have h1 := tendsto_measure_iInter_atTop (μ := P) (fun n => (hm n).nullMeasurableSet) hanti'
      ⟨0, measure_ne_top _ _⟩
    rw [iInter_comm] at h1
    simp only [hinter] at h1
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h1
  have hprod := tendsto_finsetProd Finset.univ fun i _ => ht1 i
  exact le_of_tendsto_of_tendsto' hprod ht2 fun n => h fun i => t i - 1 / ((n : ℝ) + 1)

/-- **FKG inequality for increasing events with non-strict thresholds, real form**:
`∏ᵢ P[F_i(X) ≥ t_i] ≤ P[⋂ᵢ {F_i(X) ≥ t_i}]`. -/
theorem fkg_increasing_le_real (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) (ha : 0 < a)
    (hX : IsBandVersion P W κ a b X) {K : Set (Rd d)} (hK : IsCompact K) {ι : Type*} [Fintype ι]
    {F : ι → (Rd d → ℝ) → ℝ} (hF : ∀ i, IsSupContinuousOn K (F i))
    (hmono : ∀ i, IsMonotoneFunctional (F i)) (t : ι → ℝ) :
    ∏ i, P.real {ω | t i ≤ F i fun z => X z ω} ≤
      P.real (⋂ i, {ω | t i ≤ F i fun z => X z ω}) := by
  have := hW.isProbabilityMeasure
  exact prod_measureReal_le_of_lt (fun i => measurable_comp_of_isSupContinuousOn hX hK (hF i))
    (fun c => fkg_increasing_real hκ hW ha hX hK hF hmono c) t

/-- **FKG inequality for decreasing events with non-strict thresholds, real form**:
`∏ᵢ P[F_i(X) ≤ t_i] ≤ P[⋂ᵢ {F_i(X) ≤ t_i}]`. -/
theorem fkg_decreasing_le_real (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) (ha : 0 < a)
    (hX : IsBandVersion P W κ a b X) {K : Set (Rd d)} (hK : IsCompact K) {ι : Type*} [Fintype ι]
    {F : ι → (Rd d → ℝ) → ℝ} (hF : ∀ i, IsSupContinuousOn K (F i))
    (hmono : ∀ i, IsMonotoneFunctional (F i)) (t : ι → ℝ) :
    ∏ i, P.real {ω | (F i fun z => X z ω) ≤ t i} ≤
      P.real (⋂ i, {ω | (F i fun z => X z ω) ≤ t i}) := by
  have := hW.isProbabilityMeasure
  have e1 : ∀ (c : ι → ℝ) i, {ω | c i < -F i fun z => X z ω} =
      {ω | (F i fun z => X z ω) < -c i} := fun c i => by
    ext ω
    simp only [mem_ofPred_eq, lt_neg]
  have e2 : ∀ i, {ω | -t i ≤ -F i fun z => X z ω} = {ω | (F i fun z => X z ω) ≤ t i} :=
    fun i => by
      ext ω
      simp only [mem_ofPred_eq, neg_le_neg_iff]
  have h := prod_measureReal_le_of_lt (P := P) (G := fun i ω => -F i fun z => X z ω)
    (fun i => (measurable_comp_of_isSupContinuousOn hX hK (hF i)).neg)
    (fun c => by
      simp only [e1]
      exact fkg_decreasing_real hκ hW ha hX hK hF hmono fun i => -c i) fun i => -t i
  simp only [e2] at h
  exact h

/-! ### Probability forms over a finite set of indices -/

/-- Conversion of a real-valued association inequality over the subtype of a finset into the
`ℝ≥0∞`-valued form `∏_{i ∈ s} P(A_i) ≤ P(⋂_{i ∈ s} A_i)`. -/
theorem prod_measure_le_biInter_of_real {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ι : Type*} (s : Finset ι) (A : ι → Set Ω)
    (h : ∏ i : s, P.real (A i) ≤ P.real (⋂ i : s, A i)) :
    ∏ i ∈ s, P (A i) ≤ P (⋂ i ∈ s, A i) := by
  rw [← Finset.prod_coe_sort s fun i => P (A i)]
  have e : (⋂ i ∈ s, A i) = ⋂ i : s, A i := by
    ext ω
    simp only [mem_iInter, Subtype.forall]
  rw [e]
  have h1 : ∏ i : s, P (A i) = ENNReal.ofReal (∏ i : s, P.real (A i)) := by
    rw [ENNReal.ofReal_prod_of_nonneg fun i _ => measureReal_nonneg]
    exact Finset.prod_congr rfl fun i _ => (ofReal_measureReal (measure_ne_top _ _)).symm
  rw [h1, ← ofReal_measureReal (measure_ne_top P (⋂ i : s, A i))]
  exact ENNReal.ofReal_le_ofReal h

/-- **MA7 D-FKG, increasing events** (DGZ footnote to Lemma 6.5, Lemmas 6.6–6.7): let `X` be a
continuous version of the band field `H_{a,b}` (`0 < a`) of a (nonnegative) admissible kernel over a
white noise, `K` compact, `s` a finite set of indices and `F_i` (`i ∈ s`) functionals of continuous
fields that are nondecreasing and continuous for the sup norm on `K`. Then for all thresholds
`t_i`: `∏_{i ∈ s} P[F_i(X) > t_i] ≤ P[⋂_{i ∈ s} {F_i(X) > t_i}]`. -/
theorem fkg_increasing (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) (ha : 0 < a)
    (hX : IsBandVersion P W κ a b X) {K : Set (Rd d)} (hK : IsCompact K) {ι : Type*}
    (s : Finset ι) {F : ι → (Rd d → ℝ) → ℝ} (hF : ∀ i ∈ s, IsSupContinuousOn K (F i))
    (hmono : ∀ i ∈ s, IsMonotoneFunctional (F i)) (t : ι → ℝ) :
    ∏ i ∈ s, P {ω | t i < F i fun z => X z ω} ≤
      P (⋂ i ∈ s, {ω | t i < F i fun z => X z ω}) := by
  have := hW.isProbabilityMeasure
  exact prod_measure_le_biInter_of_real s _ (fkg_increasing_real hκ hW ha hX hK (ι := s)
    (F := fun i => F i) (fun i => hF i i.2) (fun i => hmono i i.2) fun i => t i)

/-- **MA7 D-FKG, decreasing events** (DGZ footnote to Lemma 6.5): under the hypotheses of
`fkg_increasing`, `∏_{i ∈ s} P[F_i(X) < t_i] ≤ P[⋂_{i ∈ s} {F_i(X) < t_i}]`. -/
theorem fkg_decreasing (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) (ha : 0 < a)
    (hX : IsBandVersion P W κ a b X) {K : Set (Rd d)} (hK : IsCompact K) {ι : Type*}
    (s : Finset ι) {F : ι → (Rd d → ℝ) → ℝ} (hF : ∀ i ∈ s, IsSupContinuousOn K (F i))
    (hmono : ∀ i ∈ s, IsMonotoneFunctional (F i)) (t : ι → ℝ) :
    ∏ i ∈ s, P {ω | (F i fun z => X z ω) < t i} ≤
      P (⋂ i ∈ s, {ω | (F i fun z => X z ω) < t i}) := by
  have := hW.isProbabilityMeasure
  exact prod_measure_le_biInter_of_real s _ (fkg_decreasing_real hκ hW ha hX hK (ι := s)
    (F := fun i => F i) (fun i => hF i i.2) (fun i => hmono i i.2) fun i => t i)

/-- **D-FKG, increasing events, non-strict thresholds**:
`∏_{i ∈ s} P[F_i(X) ≥ t_i] ≤ P[⋂_{i ∈ s} {F_i(X) ≥ t_i}]`. -/
theorem fkg_increasing_le (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) (ha : 0 < a)
    (hX : IsBandVersion P W κ a b X) {K : Set (Rd d)} (hK : IsCompact K) {ι : Type*}
    (s : Finset ι) {F : ι → (Rd d → ℝ) → ℝ} (hF : ∀ i ∈ s, IsSupContinuousOn K (F i))
    (hmono : ∀ i ∈ s, IsMonotoneFunctional (F i)) (t : ι → ℝ) :
    ∏ i ∈ s, P {ω | t i ≤ F i fun z => X z ω} ≤
      P (⋂ i ∈ s, {ω | t i ≤ F i fun z => X z ω}) := by
  have := hW.isProbabilityMeasure
  exact prod_measure_le_biInter_of_real s _ (fkg_increasing_le_real hκ hW ha hX hK (ι := s)
    (F := fun i => F i) (fun i => hF i i.2) (fun i => hmono i i.2) fun i => t i)

/-- **D-FKG, decreasing events, non-strict thresholds** (the form of DGZ Lemma 6.5):
`∏_{i ∈ s} P[F_i(X) ≤ t_i] ≤ P[⋂_{i ∈ s} {F_i(X) ≤ t_i}]`. -/
theorem fkg_decreasing_le (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) (ha : 0 < a)
    (hX : IsBandVersion P W κ a b X) {K : Set (Rd d)} (hK : IsCompact K) {ι : Type*}
    (s : Finset ι) {F : ι → (Rd d → ℝ) → ℝ} (hF : ∀ i ∈ s, IsSupContinuousOn K (F i))
    (hmono : ∀ i ∈ s, IsMonotoneFunctional (F i)) (t : ι → ℝ) :
    ∏ i ∈ s, P {ω | (F i fun z => X z ω) ≤ t i} ≤
      P (⋂ i ∈ s, {ω | (F i fun z => X z ω) ≤ t i}) := by
  have := hW.isProbabilityMeasure
  exact prod_measure_le_biInter_of_real s _ (fkg_decreasing_le_real hκ hW ha hX hK (ι := s)
    (F := fun i => F i) (fun i => hF i i.2) (fun i => hmono i i.2) fun i => t i)

end Band

end HigherDimLQGMetric.DGZ
