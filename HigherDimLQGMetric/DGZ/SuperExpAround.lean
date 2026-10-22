import HigherDimLQGMetric.DGZ.AroundCert

/-!
# DGZ Lemma 4.9, around half, certificate form (packet L3c3; MA7 D-4.9)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), Lemma 4.9 (TeX l. 1814–1905, pp. 35–37);
planning audit `planning/audits/MA7-ref2-sections-4-6.md`, §5 row L3c3 and risk (2), gap G3 and
Details (a) D-4.9; the target shape `SuperExpAroundShape` is copied **verbatim** from MA7
Details (c) §E (durable copy `planning/audits/statements/MA7Statements.lean.txt`).

Main results:
* `SuperExpAroundShape` (definition, verbatim) and
  `superExpAroundShape : SuperExpAroundShape d κ ξ Q` (for all `d, κ, ξ, Q`): under
  `DGZHyp d κ ξ Q`, for `δ > 0`, `0 < r₂ < r₁` there is `C` such that for every dyadic
  realization, every cube `B = obox (latPt 1 b) ρ` (`b ∈ ℤ^d`, `ρ ∈ ℕ`, `ρ ≥ r₁`, `0 ∈ B`) and every
  `n`, there is a measurable event `E` with `AroundGood(h_n, 0, r₁, r₂, B, 2^{-(1-ξQ-δ)n})` on `E`
  and `P[Eᶜ] ≤ C e^{-n log n}`;
* the named certificate at level `n`, `aroundCertAt ξ Q δ r₁ r₂ n ψ g` (`AroundCert` of
  `AroundCert.lean` with the parameters of D-4.9), for a coarse field `ψ` (a version of
  `H_{2^{-m(n)}, 1}`) and a fine field `g` (a version of `H_{2^{-n}, 2^{-m(n)}}`), which is what the
  nice-box packet L4a1 needs (MA7 D-5.3 `Cert_{j-1}(z)`, Remark 5.4′): it only depends on `ψ, g` on
  the closed shell (`aroundCert_congr`, `measurableSet_aroundCert_comap`);
  `aroundGood_of_aroundCertAt` (deterministic, `n ≥ n₀`, every admissible cube `B`, field `ψ + g`)
  and `prob_not_aroundCertAt_le` (`P[¬ aroundCertAt] ≤ C e^{-n log n}` for any such `ψ, g` over one
  white noise).

Proof (MA7 D-4.9). `m = m(n) = 2⌊log₂ n⌋ + 2`, `s = 2^{-m}`, `ϱ = min(r₂, r₁ - r₂)/16`,
`D = ⌊ϱ/s⌋`, `T = 2^{-(1-ξQ)n + δn/3}`. A site `x` of the shell region
`Σ = {r₂ + ϱ/2 ≤ s|x|_∞ ≤ r₁ - ϱ/2}` is closed iff `selfDiam(g)(B_s(s x)) > T`; other sites are open
(closedness does not depend on `B`). The certificate is `𝒢₁ ∩ 𝒢₂` with
`𝒢₁ = {|ψ| ≤ δ n log 2/(3ξ) on the closed shell}` and `𝒢₂ = {SmallClusters O D}`. By scaling and
D-4.7s, `P[x closed] ≤ C e^{-(n-m)/C}`; the product bound (locality on `B̄_s(s x)`) and
`Perc.diameterBound` give `P[𝒢₂ᶜ] ≤ e^{-n log n}`; `P[𝒢₁ᶜ] ≤ e^{-n log n}`
(`exists_field_superExp'`). On the certificate, `aroundGood_of_aroundCert` (with `c = 2^m b`,
`N = 2^m ρ`) gives the around-good property with threshold
`2 (2⌈r₁/s⌉+1)^d 2^{δn/3} T ≤ 2^{-(1-ξQ-δ)n}`. For a dyadic realization, `ψ = h_m` and
`g = h_n - h_m` (a version of `h_{m,n}`), so `ψ + g = h_n`; for `n < n₀`, `E = ∅`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox obox_subset_cbox)

variable {d : ℕ}

/-! ### The target shape (MA7 Details (c) §E, verbatim) -/

/-- **DGZ Lemma 4.9, around half, certificate form** (MA7 D-4.9): for the shell
`B_{r₁}(0) \ B_{r₂}(0)` and every open cube `B = obox (latPt 1 b) ρ` with integer centre `b`, integer
radius `ρ ≥ r₁` and `0 ∈ B`, the around-good property holds with threshold `2^{-(1-ξQ-δ)n}` outside
a measurable event of super-exponentially small probability, uniformly in `B` -/
def SuperExpAroundShape (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ) : Prop :=
  DGZHyp d κ ξ Q → ∀ δ > 0, ∀ r₁ r₂ : ℝ, 0 < r₂ → r₂ < r₁ → ∃ C > 0,
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
      IsDyadicRealization κ P W H → ∀ (b : Zd d) (ρ : ℕ), r₁ ≤ ρ →
        (0 : Rd d) ∈ obox (latPt 1 b) ρ → ∀ n : ℕ, ∃ E : Set Ω, MeasurableSet E ∧
          (∀ ω ∈ E, AroundGood ξ (fun z => H n z ω) 0 r₁ r₂ (obox (latPt 1 b) ρ)
            ((2 : ℝ) ^ (-(1 - ξ * Q - δ) * n))) ∧
          P Eᶜ ≤ ENNReal.ofReal (C * Real.exp (-(n : ℝ) * Real.log n))

/-! ### The certificate at level `n` -/

/-- **The around certificate at level `n`** (MA7 D-4.9, the event `E` for `n ≥ n₀`): `AroundCert`
with `ϱ = min(r₂, r₁ - r₂)/16`, mesh `s = 2^{-m(n)}`, threshold `T = 2^{-(1-ξQ)n + δn/3}` and
field level `δ n log 2/(3ξ)`, for a coarse field `ψ` and a fine field `g`. -/
def aroundCertAt (ξ Q δ r₁ r₂ : ℝ) (n : ℕ) (ψ g : Rd d → ℝ) : Prop :=
  AroundCert ξ ψ g r₁ r₂ (min r₂ (r₁ - r₂) / 16) ((2 : ℝ)⁻¹ ^ superScale n)
    ((2 : ℝ) ^ (-(1 - ξ * Q) * n + δ * n / 3)) (δ * Real.log 2 / (3 * ξ) * n)

/-- `ϱ = min(r₂, r₁ - r₂)/16` satisfies `0 < ϱ`, `16ϱ ≤ r₂`, `16ϱ ≤ r₁ - r₂`. -/
lemma aroundRho_spec {r₁ r₂ : ℝ} (hr₂ : 0 < r₂) (hr : r₂ < r₁) :
    0 < min r₂ (r₁ - r₂) / 16 ∧ 16 * (min r₂ (r₁ - r₂) / 16) ≤ r₂ ∧
      16 * (min r₂ (r₁ - r₂) / 16) ≤ r₁ - r₂ :=
  ⟨by have := lt_min hr₂ (sub_pos.2 hr); positivity,
    by linarith [min_le_left r₂ (r₁ - r₂)], by linarith [min_le_right r₂ (r₁ - r₂)]⟩

/-- **Measurability of the certificate at level `n`**. -/
theorem measurableSet_aroundCertAt {Ω : Type*} [MeasurableSpace Ω] {ψ g : Rd d → Ω → ℝ}
    (hψc : ∀ ω, Continuous fun z => ψ z ω) (hψm : ∀ z, Measurable (ψ z))
    (hgc : ∀ ω, Continuous fun z => g z ω) (hgm : ∀ z, Measurable (g z)) (ξ Q δ r₁ r₂ : ℝ)
    (n : ℕ) :
    MeasurableSet {ω | aroundCertAt ξ Q δ r₁ r₂ n (fun z => ψ z ω) (fun z => g z ω)} :=
  measurableSet_aroundCert hψc hψm hgc hgm ξ r₁ r₂ _ (by positivity) _ _

/-! ### Local events and per-site bounds -/

/-- The closed-site event of D-4.9 is measurable for the field on `B̄_s(s x)`. -/
lemma measurableSet_selfDiamClosed_comap {Ω : Type*} {G : Rd d → Ω → ℝ}
    (hc : ∀ ω, Continuous fun z => G z ω) {s : ℝ} (hs : 0 < s) (ξ : ℝ) (p : Prop) (T : ℝ)
    (x : Zd d) :
    MeasurableSet[MeasurableSpace.comap (fun ω (z : cbox (latPt s x) (1 * s)) => G z ω)
      MeasurableSpace.pi]
      {ω | p ∧ T < selfDiam ξ (fun z => G z ω) (latPt s x) s} := by
  rw [one_mul]
  let mΩ : MeasurableSpace Ω :=
    MeasurableSpace.comap (fun ω (z : cbox (latPt s x) s) => G z ω) MeasurableSpace.pi
  have hf : Measurable fun ω => selfDiam ξ (fun z => G z ω) (latPt s x) s :=
    measurable_selfDiam_comap hc ξ _ hs.le
  rw [Set.ofPred_and]
  exact (MeasurableSet.const p).inter (measurableSet_lt measurable_const hf)

/-- **Per-site bound** (MA7 D-4.9): for a version `G` of `h_{m,n}` (over the white noise of a dyadic
realization), by scaling and D-4.7s (at `δ/3`), `P[selfDiam(G)(B_s(w)) > T] ≤ C e^{-(n-m)/C}`
(`s = 2^{-m}`, `T = 2^{-(1-ξQ)n + δn/3}`). -/
lemma measure_selfDiamBand_gt_le {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {ξ Q δ Csd : ℝ}
    (hξQ : 0 ≤ ξ * Q) (hδ : 0 < δ)
    (hsd : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ n : ℕ,
        P {ω | (2 : ℝ) ^ (-(1 - ξ * Q - δ / 3) * n) < selfDiam ξ (fun z => H n z ω) 0 1} ≤
          ENNReal.ofReal (Csd * Real.exp (-(n : ℝ) / Csd)))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
    {H : ℕ → Rd d → Ω → ℝ} (hH : IsDyadicRealization κ P W H) {m n : ℕ} (hmn : m ≤ n)
    {G : Rd d → Ω → ℝ} (hG : IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ m) G)
    (w : Rd d) :
    P {ω | (2 : ℝ) ^ (-(1 - ξ * Q) * n + δ * n / 3) <
        selfDiam ξ (fun z => G z ω) w ((2 : ℝ)⁻¹ ^ m)} ≤
      ENNReal.ofReal (Csd * Real.exp (-((n - m : ℕ) : ℝ) / Csd)) := by
  rw [measure_lt_selfDiam_band_eq hκ hH hmn hG ξ w, two_rpow_div_inv_two_pow]
  refine (measure_mono fun ω hω => ?_).trans (hsd Ω P W H hH (n - m))
  refine lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le one_le_two ?_) hω
  rw [Nat.cast_sub hmn]
  have h1 : 0 ≤ ξ * Q * m := mul_nonneg hξQ (Nat.cast_nonneg m)
  have h2 : 0 ≤ δ * m / 3 := by positivity
  linarith only [h1, h2]

/-! ### The box `B = obox (latPt 1 b) ρ` as a box of the fine grid -/

section Box

variable {m : ℕ} {b : Zd d} {ρ : ℕ}

lemma latPt_two_pow_smul (m : ℕ) (b : Zd d) :
    latPt ((2 : ℝ)⁻¹ ^ m) (fun i => 2 ^ m * b i) = latPt 1 b := by
  ext i
  rw [latPt_apply, latPt_apply]
  push_cast
  rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow, one_mul]

lemma obox_fine_eq (m : ℕ) (b : Zd d) (ρ : ℕ) :
    obox (latPt ((2 : ℝ)⁻¹ ^ m) (fun i => 2 ^ m * b i)) ((2 : ℝ)⁻¹ ^ m * ((2 ^ m * ρ : ℕ) : ℝ)) =
      obox (latPt 1 b) ρ := by
  rw [latPt_two_pow_smul]
  congr 1
  push_cast
  rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow, one_mul]

/-- `0 ∈ B` gives `|2^m b|_∞ ≤ 2^m ρ - 1`. -/
lemma withinInf_fine_of_mem (h0 : (0 : Rd d) ∈ obox (latPt 1 b) ρ) :
    WithinInf (((2 ^ m * ρ : ℕ) : ℤ) - 1) 0 (fun i => 2 ^ m * b i) := by
  intro i
  have h1 : |(0 : Rd d) i - latPt 1 b i| < ρ := h0 i
  rw [latPt_apply, one_mul] at h1
  simp only [PiLp.zero_apply, zero_sub, abs_neg] at h1
  have h2 : |b i| < (ρ : ℤ) := by exact_mod_cast h1
  have h3 : |b i| ≤ (ρ : ℤ) - 1 := by omega
  have h4 : (1 : ℤ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  simp only [Pi.zero_apply, zero_sub, abs_neg, abs_mul, abs_pow, abs_two]
  push_cast
  nlinarith

/-- In every coordinate `B` extends at least `r₁` on one side of `0` (`b ∈ ℤ^d`, `ρ ≥ r₁`). -/
lemma side_fine {r₁ : ℝ} (hρ : r₁ ≤ ρ) (i : Fin d) :
    r₁ ≤ (2 : ℝ)⁻¹ ^ m * (((2 ^ m * b i : ℤ) : ℝ) + ((2 ^ m * ρ : ℕ) : ℝ)) ∨
      (2 : ℝ)⁻¹ ^ m * (((2 ^ m * b i : ℤ) : ℝ) - ((2 ^ m * ρ : ℕ) : ℝ)) ≤ -r₁ := by
  have e : ∀ y : ℝ, (2 : ℝ)⁻¹ ^ m * ((2 : ℝ) ^ m * y) = y := fun y => by
    rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow, one_mul]
  push_cast
  rw [← mul_add, ← mul_sub, e, e]
  rcases le_or_gt 0 (b i) with hb | hb
  · left
    have : (0 : ℝ) ≤ (b i : ℝ) := by exact_mod_cast hb
    linarith
  · right
    have : (b i : ℝ) ≤ -1 := by
      have : b i ≤ -1 := by omega
      exact_mod_cast this
    have : (0 : ℝ) ≤ r₁ ∨ r₁ < 0 := le_or_gt 0 r₁
    rcases this with h | h <;> linarith [Nat.cast_nonneg (α := ℝ) ρ]

end Box

/-! ### The deterministic part at level `n` -/

/-- **The certificate gives the around-good property at level `n`** (MA7 D-4.9 "On `E`"): there is
`n₀` such that for `n ≥ n₀`, continuous `ψ, g` with `aroundCertAt ξ Q δ r₁ r₂ n ψ g`, and every cube
`B = obox (latPt 1 b) ρ` (`b ∈ ℤ^d`, `ρ ∈ ℕ`, `ρ ≥ r₁`, `0 ∈ B`):
`AroundGood ξ (ψ + g) 0 r₁ r₂ B 2^{-(1-ξQ-δ)n}`. -/
theorem aroundGood_of_aroundCertAt (hd : 2 ≤ d) {ξ Q δ : ℝ} (hξ : 0 < ξ) (hδ : 0 < δ)
    {r₁ r₂ : ℝ} (hr₂ : 0 < r₂) (hr : r₂ < r₁) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ ψ g : Rd d → ℝ, Continuous ψ → Continuous g →
      aroundCertAt ξ Q δ r₁ r₂ n ψ g → ∀ (b : Zd d) (ρ : ℕ), r₁ ≤ ρ →
        (0 : Rd d) ∈ obox (latPt 1 b) ρ →
          AroundGood ξ (fun z => ψ z + g z) 0 r₁ r₂ (obox (latPt 1 b) ρ)
            ((2 : ℝ) ^ (-(1 - ξ * Q - δ) * n)) := by
  obtain ⟨hL0, -⟩ := log_two_pos_lt_one
  obtain ⟨hϱ0, hϱ₂, hϱ₁⟩ := aroundRho_spec hr₂ hr
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (((eventually_ge_atTop 1).and
    (eventually_le_two_pow_superScale (8 / (min r₂ (r₁ - r₂) / 16)))).and
    (eventually_mul_poly_le_exp 2 (8 * r₁) 3 d (b := δ * Real.log 2 / 3) (by norm_num)
      (by linarith) (by norm_num) (by positivity)))
  refine ⟨n₀, fun n hn ψ g hψ hg hcert b ρ hρ h0 => ?_⟩
  obtain ⟨⟨hn1, hs8⟩, hpath⟩ := hn₀ n hn
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, superScale n = m := ⟨_, rfl⟩
  rw [hmdef] at hs8
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, (2 : ℝ)⁻¹ ^ m = s := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [← hsdef]; positivity
  have hs2m : s * (2 : ℝ) ^ m = 1 := by
    rw [← hsdef, ← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow]
  have hsϱ : 8 * s ≤ min r₂ (r₁ - r₂) / 16 := by
    rw [div_le_iff₀ hϱ0] at hs8
    nlinarith
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, (2 : ℝ) ^ (-(1 - ξ * Q) * n + δ * n / 3) = T := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [← hTdef]; exact Real.rpow_nonneg (by norm_num) _
  unfold aroundCertAt at hcert
  rw [hmdef, hsdef, hTdef] at hcert
  have hcert' := aroundGood_of_aroundCert hd hξ.le hψ hg hs0 hsϱ hϱ₂ hϱ₁ hT0 hcert
    (c := fun i => 2 ^ m * b i) (N := 2 ^ m * ρ) (withinInf_fine_of_mem h0)
    (by rw [← hsdef]; exact side_fine hρ)
  rw [← hsdef, obox_fine_eq, hsdef] at hcert'
  refine hcert'.mono ?_
  -- the threshold: `2 (2K+1)^d 2^{δn/3} T ≤ 2^{-(1-ξQ-δ)n}`
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ, ⌈r₁ / s⌉₊ = K := ⟨_, rfl⟩
  rw [hKdef]
  have hK' : ((2 * K + 1 : ℕ) : ℝ) ≤ 8 * r₁ * (n : ℝ) ^ 2 + 3 := by
    have h4 := two_pow_superScale_le_real (n := n) (by omega)
    rw [hmdef] at h4
    have h1 : (K : ℝ) < r₁ / s + 1 := by
      rw [← hKdef]; exact Nat.ceil_lt_add_one (div_nonneg (by linarith) hs0.le)
    have h2 : r₁ / s = r₁ * (2 : ℝ) ^ m := by
      rw [div_eq_iff hs0.ne']
      linear_combination r₁ * hs2m.symm
    push_cast
    nlinarith
  have hpow : (((2 * K + 1) ^ d : ℕ) : ℝ) ≤ (8 * r₁ * (n : ℝ) ^ 2 + 3) ^ d := by
    push_cast
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hK') d
  have hT2 : Real.exp (ξ * (δ * Real.log 2 / (3 * ξ) * n)) * T =
      (2 : ℝ) ^ (-(1 - ξ * Q - δ) * n) / Real.exp (δ * Real.log 2 / 3 * n) := by
    rw [← hTdef, Real.rpow_def_of_pos two_pos, Real.rpow_def_of_pos two_pos,
      eq_div_iff (Real.exp_pos _).ne', ← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [hT2, ← mul_div_assoc, div_le_iff₀ (Real.exp_pos _)]
  have h2 : 0 ≤ (2 : ℝ) ^ (-(1 - ξ * Q - δ) * n) := Real.rpow_nonneg (by norm_num) _
  have h3 : 2 * (((2 * K + 1) ^ d : ℕ) : ℝ) ≤ Real.exp (δ * Real.log 2 / 3 * n) :=
    (mul_le_mul_of_nonneg_left hpow (by norm_num)).trans hpath
  nlinarith

/-! ### The probability of the certificate -/

/-- **The certificate fails with super-exponentially small probability** (MA7 D-4.9): for any
version `ψ` of `H_{2^{-m(n)}, 1}` and any version `g` of `H_{2^{-n}, 2^{-m(n)}}` over the same white
noise, `P[¬ aroundCertAt ξ Q δ r₁ r₂ n ψ g] ≤ C e^{-n log n}`, with `C` uniform in everything. -/
theorem prob_not_aroundCertAt_le {κ : Rd d → ℝ} {ξ Q : ℝ} (h : DGZHyp d κ ξ Q) {δ : ℝ}
    (hδ : 0 < δ) {r₁ r₂ : ℝ} (hr₂ : 0 < r₂) (hr : r₂ < r₁) :
    ∃ C > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
      (ψ g : Rd d → Ω → ℝ), IsWhiteNoise P W → ∀ n : ℕ,
        IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ superScale n) 1 ψ →
        IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ superScale n) g →
          P {ω | ¬ aroundCertAt ξ Q δ r₁ r₂ n (fun z => ψ z ω) (fun z => g z ω)} ≤
            ENNReal.ofReal (C * Real.exp (-(n : ℝ) * Real.log n)) := by
  have hκ := h.kernel
  have hξ := h.xi_pos
  obtain ⟨hL0, -⟩ := log_two_pos_lt_one
  have hQ : 0 < Q := lt_of_le_of_lt (Real.sqrt_nonneg _) h.subcritical
  obtain ⟨hϱ0, -, -⟩ := aroundRho_spec hr₂ hr
  obtain ⟨Csd, hCsd, hsd⟩ := selfDiamShape d κ ξ Q h (δ / 3) (by positivity)
  -- the Peierls parameters (locality radius `1`)
  obtain ⟨ρk, -, hρk⟩ := hκ.exists_radius
  obtain ⟨r, hrdef⟩ : ∃ r : ℕ, ⌈2 * (1 + ρk)⌉₊ = r := ⟨_, rfl⟩
  obtain ⟨hθ0, hθ1⟩ := theta_pow_pos_le_one d r
  have hθtop : ENNReal.ofReal (2 * 3 ^ d : ℝ)⁻¹ ^ ((r + 1) ^ d) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hθ1
  obtain ⟨k₀, hk₀⟩ := exists_mul_exp_neg_div_le hCsd
    (θ := (ENNReal.ofReal (2 * 3 ^ d : ℝ)⁻¹ ^ ((r + 1) ^ d)).toReal)
    (ENNReal.toReal_pos hθ0.ne' hθtop)
  -- the coarse field
  obtain ⟨n₁, hn₁⟩ := exists_field_superExp' hκ (R := r₁) (by linarith)
    (c := δ * Real.log 2 / (3 * ξ)) (by positivity)
  -- the threshold `n₀`
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 ((((eventually_ge_atTop (max 1 (max n₁ (2 * k₀)))).and
    (eventually_superScale_le_mul (c := 1 / 2) (by norm_num))).and
    (eventually_peierls_superExp d (a := r₁) (b := min r₂ (r₁ - r₂) / 16) (by linarith)
      hϱ0)))
  obtain ⟨C₀, hC₀, hC₀small⟩ := exists_superExp_const n₀
  obtain ⟨C, hC2, hCC₀⟩ : ∃ C : ℝ, 2 ≤ C ∧ C₀ ≤ C := ⟨max 2 C₀, le_max_left _ _, le_max_right _ _⟩
  refine ⟨C, by linarith, fun Ω _ P W ψ g hW n hψ hg => ?_⟩
  have := hW.isProbabilityMeasure
  rcases lt_or_ge n n₀ with hn | hn
  · -- small `n`
    calc _ ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal ((hC₀small n hn).trans
          (mul_le_mul_of_nonneg_right hCC₀ (Real.exp_pos _).le))
  obtain ⟨⟨hnbig, hm2⟩, hpei⟩ := hn₀ n hn
  have hnn₁ : n₁ ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hnbig
  have hnk : 2 * k₀ ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hnbig
  have hfield := hn₁ hW n hnn₁ hψ
  -- the scale `m = m(n)`, the mesh `s = 2^{-m}` and a reference dyadic realization
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, superScale n = m := ⟨_, rfl⟩
  rw [hmdef] at hm2 hpei hg
  have hmn : m ≤ n := by
    have : (m : ℝ) ≤ n := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    exact_mod_cast this
  have hnm : ((n - m : ℕ) : ℝ) = n - m := Nat.cast_sub hmn
  have hk : k₀ ≤ n - m := by
    have h1 : (2 * k₀ : ℝ) ≤ n := by exact_mod_cast hnk
    have : (k₀ : ℝ) ≤ ((n - m : ℕ) : ℝ) := by rw [hnm]; linarith
    exact_mod_cast this
  obtain ⟨H, hH⟩ := exists_isDyadicRealization hκ hW
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, (2 : ℝ)⁻¹ ^ m = s := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [← hsdef]; positivity
  have hs2m : s * (2 : ℝ) ^ m = 1 := by
    rw [← hsdef, ← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow]
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, (2 : ℝ) ^ (-(1 - ξ * Q) * n + δ * n / 3) = T := ⟨_, rfl⟩
  set closed : Zd d → Set Ω := fun x => {ω |
    ((∃ i, r₂ + min r₂ (r₁ - r₂) / 16 / 2 ≤ s * |(x i : ℝ)|) ∧
      ∀ i, s * |(x i : ℝ)| ≤ r₁ - min r₂ (r₁ - r₂) / 16 / 2) ∧
      T < selfDiam ξ (fun z => g z ω) (latPt s x) s} with hclosed
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ, ⌈r₁ / s⌉₊ = K := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : ℕ, ⌊min r₂ (r₁ - r₂) / 16 / s⌋₊ = D := ⟨_, rfl⟩
  have hreg : ∀ x : Zd d, (∀ i, s * |(x i : ℝ)| ≤ r₁ - min r₂ (r₁ - r₂) / 16 / 2) →
      WithinInf (K : ℤ) x 0 := by
    intro x hx i
    have h2 : |(x i : ℝ)| ≤ r₁ / s := by
      rw [le_div_iff₀ hs0]
      linarith [hx i]
    have h3 : |(x i : ℝ)| ≤ K := h2.trans (by rw [← hKdef]; exact Nat.le_ceil _)
    simp only [Pi.zero_apply, sub_zero]
    exact_mod_cast h3
  -- the closed sites: probability, product bound, Peierls
  have hcl : ∀ x, P (closed x) ≤ ENNReal.ofReal (2 * 3 ^ d : ℝ)⁻¹ ^ ((r + 1) ^ d) := by
    intro x
    have h1 := measure_selfDiamBand_gt_le hκ (by positivity) hδ hsd hH hmn hg (latPt s x)
    rw [hsdef, hTdef] at h1
    refine (measure_mono fun ω hω => hω.2).trans (h1.trans ?_)
    rw [← ENNReal.ofReal_toReal hθtop]
    exact ENNReal.ofReal_le_ofReal (hk₀ _ hk)
  have hPB : ProductBound P closed (r : ℤ) := by
    have := productBound_of_local hκ hW hρk (by positivity) hg hs0 hsdef.le (R := 1) closed
      fun x => measurableSet_selfDiamClosed_comap hg.continuous hs0 ξ _ T x
    rwa [hrdef] at this
  have hpeierls := measure_not_smallClusters_le P closed r _ _ hcl hPB
    (HigherDimLFPP.L33.theta_le_one d) le_rfl (HigherDimLFPP.L33.three_pow_mul_theta_le d) K D
    (fun x ω hω => hreg x hω.1.2)
  have hKb : (K : ℝ) ≤ r₁ * (2 : ℝ) ^ m + 1 := by
    have h1 : (K : ℝ) < r₁ / s + 1 := by
      rw [← hKdef]; exact Nat.ceil_lt_add_one (div_nonneg (by linarith) hs0.le)
    have h2 : r₁ / s = r₁ * (2 : ℝ) ^ m := by
      rw [div_eq_iff hs0.ne']
      linear_combination r₁ * hs2m.symm
    linarith
  have hDb : min r₂ (r₁ - r₂) / 16 * (2 : ℝ) ^ m ≤ D + 1 := by
    have h1 : min r₂ (r₁ - r₂) / 16 / s < D + 1 := by
      rw [← hDdef]; exact Nat.lt_floor_add_one _
    have h2 : min r₂ (r₁ - r₂) / 16 / s = min r₂ (r₁ - r₂) / 16 * (2 : ℝ) ^ m := by
      rw [div_eq_iff hs0.ne']
      linear_combination min r₂ (r₁ - r₂) / 16 * hs2m.symm
    linarith
  have hPei := hpeierls.trans (hpei K D hKb hDb)
  -- the inclusion `{¬ cert} ⊆ 𝒢₁ᶜ ∪ 𝒢₂ᶜ`
  have hsub : {ω | ¬ aroundCertAt ξ Q δ r₁ r₂ n (fun z => ψ z ω) (fun z => g z ω)} ⊆
      {ω | ∃ z ∈ cbox (0 : Rd d) r₁, δ * Real.log 2 / (3 * ξ) * n < |ψ z ω|} ∪
        {ω | ¬ SmallClusters {x | ω ∉ closed x} D} := by
    intro ω hω
    by_contra hno
    simp only [mem_union, mem_ofPred_eq, not_or, not_not, not_exists, not_and, not_lt] at hno
    obtain ⟨hF, hsmall⟩ := hno
    apply hω
    unfold aroundCertAt
    rw [hmdef, hsdef, hTdef]
    refine ⟨fun z hz => hF z hz.1, ?_⟩
    rw [hDdef]
    exact hsmall
  calc P {ω | ¬ aroundCertAt ξ Q δ r₁ r₂ n (fun z => ψ z ω) (fun z => g z ω)}
      ≤ P ({ω | ∃ z ∈ cbox (0 : Rd d) r₁, δ * Real.log 2 / (3 * ξ) * n < |ψ z ω|} ∪
        {ω | ¬ SmallClusters {x | ω ∉ closed x} D}) := measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * Real.log n)) +
          ENNReal.ofReal (Real.exp (-(n : ℝ) * Real.log n)) :=
        (measure_union_le _ _).trans (add_le_add hfield hPei)
    _ = ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * Real.log n)) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, two_mul]
    _ ≤ ENNReal.ofReal (C * Real.exp (-(n : ℝ) * Real.log n)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC2 (Real.exp_pos _).le)

/-! ### The tail bound -/

/-- **DGZ Lemma 4.9, around half** (MA7 D-4.9), for the dyadic realizations of `DGZHyp`: the event
`E = {aroundCertAt ξ Q δ r₁ r₂ n h_{m(n)} (h_n - h_{m(n)})}` for `n ≥ n₀` (`E = ∅` for `n < n₀`). -/
theorem superExpAround_tail {κ : Rd d → ℝ} {ξ Q : ℝ} (h : DGZHyp d κ ξ Q) {δ : ℝ} (hδ : 0 < δ)
    {r₁ r₂ : ℝ} (hr₂ : 0 < r₂) (hr : r₂ < r₁) :
    ∃ C > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ (b : Zd d) (ρ : ℕ), r₁ ≤ ρ →
        (0 : Rd d) ∈ obox (latPt 1 b) ρ → ∀ n : ℕ, ∃ E : Set Ω, MeasurableSet E ∧
          (∀ ω ∈ E, AroundGood ξ (fun z => H n z ω) 0 r₁ r₂ (obox (latPt 1 b) ρ)
            ((2 : ℝ) ^ (-(1 - ξ * Q - δ) * n))) ∧
          P Eᶜ ≤ ENNReal.ofReal (C * Real.exp (-(n : ℝ) * Real.log n)) := by
  have hd := h.dim
  have hκ := h.kernel
  have hξ := h.xi_pos
  obtain ⟨C₁, hC₁, hprob⟩ := prob_not_aroundCertAt_le h hδ hr₂ hr
  obtain ⟨n₀, hdet⟩ := aroundGood_of_aroundCertAt hd hξ hδ hr₂ hr (Q := Q)
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.1 (eventually_superScale_le_mul (c := 1) one_pos)
  obtain ⟨C₀, hC₀, hC₀small⟩ := exists_superExp_const (max n₀ n₂)
  obtain ⟨C, hC1, hC0⟩ : ∃ C : ℝ, C₁ ≤ C ∧ C₀ ≤ C := ⟨max C₁ C₀, le_max_left _ _, le_max_right _ _⟩
  refine ⟨C, by linarith, fun Ω _ P W H hH b ρ hρ h0 n => ?_⟩
  have hW := hH.whiteNoise
  have := hW.isProbabilityMeasure
  rcases lt_or_ge n (max n₀ n₂) with hn | hn
  · -- small `n`: `E = ∅`
    refine ⟨∅, MeasurableSet.empty, fun ω hω => absurd hω (Set.notMem_empty ω), ?_⟩
    calc P ∅ᶜ ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal ((hC₀small n hn).trans
          (mul_le_mul_of_nonneg_right hC0 (Real.exp_pos _).le))
  have hmn : superScale n ≤ n := by
    have := hn₂ n ((le_max_right _ _).trans hn)
    rw [one_mul] at this
    exact_mod_cast this
  have hG := isBandVersion_sub_of_realization hκ hH hmn
  refine ⟨{ω | aroundCertAt ξ Q δ r₁ r₂ n (fun z => H (superScale n) z ω)
      (fun z => H n z ω - H (superScale n) z ω)}, ?_, fun ω hω => ?_, ?_⟩
  · exact measurableSet_aroundCertAt (hH.band _).continuous (hH.band _).measurable
      hG.continuous hG.measurable ξ Q δ r₁ r₂ n
  · have hgood := hdet n ((le_max_left _ _).trans hn) _ _ ((hH.band _).continuous ω)
      (hG.continuous ω) hω b ρ hρ h0
    have e : (fun z => H (superScale n) z ω + (H n z ω - H (superScale n) z ω)) =
        fun z => H n z ω := funext fun z => by ring
    rwa [e] at hgood
  · rw [compl_ofPred]
    exact (hprob Ω P W _ _ hW n (hH.band _) hG).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC1 (Real.exp_pos _).le))

/-- **MA7 Details (c) `SuperExpAroundShape`** (DGZ Lemma 4.9, around half, certificate form;
MA7 D-4.9), for every `d, κ, ξ, Q`. -/
theorem superExpAroundShape (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ) : SuperExpAroundShape d κ ξ Q :=
  fun h _ hδ _ _ hr₂ hr => superExpAround_tail h hδ hr₂ hr

end DGZ

end HigherDimLQGMetric
