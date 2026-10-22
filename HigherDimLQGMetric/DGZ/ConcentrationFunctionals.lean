import HigherDimLQGMetric.DGZ.ConcentrationQuantile
import HigherDimLQGMetric.DGZ.FunctionalsBounds

/-!
# Concentration of the DGZ functionals (packet L3b2, MA7 D-4.6 applied)

Source: planning audit `planning/audits/MA7-ref2-sections-4-6.md`, Details (a) D-4.6 ("Applies
to: `lfppDistOn` on a bounded open `V` (`K = V̄`), set distances between compact sets, `acrossDist`
(minimizing paths can be taken inside the closed shell `K`), `lfppDiam`, `selfDiam`"), and the
log-Lipschitz bounds of packet L3b1 (`abs_log_selfDiam_sub_le`, `abs_log_acrossDist_sub_le`,
`abs_log_lfppSetDist_sub_le`, `abs_log_lfppDiam_sub_le`; HigherDimLFPP `abs_log_lfppDistOn_sub_le`).

For each functional `Φ` the logarithm is `|ξ|`-Lipschitz for the sup norm on a compact set `K`
(`isSupLipschitzOn_log_*`), so the results of `Concentration.lean` and `ConcentrationQuantile.lean`
apply. For a continuous version `X` of the band field `H_{a,b}` (`0 < a ≤ b`), this file records
the integrability of `log Φ(X)` and the two-sided bound
`P[|log Φ(X) - E log Φ(X)| ≥ t] ≤ 2 exp(-t² / (2 ξ² log(b/a)))` for
* `selfDiam ξ X c r` (`r > 0`, `K = cbox c r`);
* `acrossDist ξ X c r₁ r₂` (`r₂ < r₁`, `K = cbox c r₁`);
* `lfppSetDist ξ X V A B` (`V ⊆ K` compact);
* `lfppDiam ξ X U V` (`V` open and preconnected, `U` inside a compact subset of `V`, `V ⊆ K`
  compact);
* `lfppDistOn ξ X V x y` (`x ∈ V ⊆ K` compact; HigherDimLFPP's
  `measure_abs_log_lfppDistOn_sub_ge_le` is the case `K = closure V`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP
open HigherDimLFPP.DGZ (cbox obox)

variable {d : ℕ}

/-! ### Log-Lipschitz functionals -/

section Lipschitz

variable (ξ : ℝ)

/-- `log selfDiam(B_r(c))` is `|ξ|`-Lipschitz for the sup norm on `cbox c r` (`r > 0`). -/
theorem isSupLipschitzOn_log_selfDiam (c : Rd d) {r : ℝ} (hr : 0 < r) :
    IsSupLipschitzOn (cbox c r) |ξ| fun φ => Real.log (selfDiam ξ φ c r) :=
  fun _φ _ψ hφ hψ _M _hM0 hM =>
    abs_log_selfDiam_sub_le hφ hψ hr fun z hz => hM z (HigherDimLFPP.DGZ.obox_subset_cbox c r hz)

/-- `log acrossDist(B_{r₁}(c) \ B_{r₂}(c))` is `|ξ|`-Lipschitz for the sup norm on `cbox c r₁`
(`r₂ < r₁`). -/
theorem isSupLipschitzOn_log_acrossDist (c : Rd d) {r₁ r₂ : ℝ} (hr : r₂ < r₁) :
    IsSupLipschitzOn (cbox c r₁) |ξ| fun φ => Real.log (acrossDist ξ φ c r₁ r₂) :=
  fun _φ _ψ hφ hψ _M hM0 hM => abs_log_acrossDist_sub_le hφ hψ hr hM0 fun z hz => hM z hz.1

/-- `log D(A, B; V)` is `|ξ|`-Lipschitz for the sup norm on every `K ⊇ V`. -/
theorem isSupLipschitzOn_log_lfppSetDist {V K : Set (Rd d)} (hVK : V ⊆ K) (A B : Set (Rd d)) :
    IsSupLipschitzOn K |ξ| fun φ => Real.log (lfppSetDist ξ φ V A B) :=
  fun _φ _ψ hφ hψ _M hM0 hM => abs_log_lfppSetDist_sub_le hφ hψ hM0 fun z hz => hM z (hVK hz)

/-- `log Diam(U; V)` is `|ξ|`-Lipschitz for the sup norm on every `K ⊇ V`, for `V` open and
preconnected and `U` inside a compact subset `K₀` of `V` (so that the diameters of continuous fields
are finite). -/
theorem isSupLipschitzOn_log_lfppDiam {U V K₀ K : Set (Rd d)} (hV : IsOpen V)
    (hVc : IsPreconnected V) (hK₀ : IsCompact K₀) (hK₀V : K₀ ⊆ V) (hUK₀ : U ⊆ K₀) (hVK : V ⊆ K) :
    IsSupLipschitzOn K |ξ| fun φ => Real.log (lfppDiam ξ φ U V) :=
  fun _φ _ψ hφ hψ _M hM0 hM => abs_log_lfppDiam_sub_le hφ hψ hM0 (fun z hz => hM z (hVK hz))
    (bddAbove_lfppDiam_of_isCompact hV hVc hφ ξ hK₀ hK₀V hUK₀)
    (bddAbove_lfppDiam_of_isCompact hV hVc hψ ξ hK₀ hK₀V hUK₀)

/-- `log D(x, y; V)` is `|ξ|`-Lipschitz for the sup norm on every `K ⊇ V`, for `x ∈ V`. -/
theorem isSupLipschitzOn_log_lfppDistOn {V K : Set (Rd d)} {x : Rd d} (hx : x ∈ V) (y : Rd d)
    (hVK : V ⊆ K) : IsSupLipschitzOn K |ξ| fun φ => Real.log (lfppDistOn ξ φ V x y) :=
  fun _φ _ψ hφ hψ _M _hM0 hM => abs_log_lfppDistOn_sub_le hφ hψ hx fun z hz => hM z (hVK hz)

end Lipschitz

/-! ### Concentration -/

section Band

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ} {κ : Rd d → ℝ}
  {a b : ℝ} {X : Rd d → Ω → ℝ}

/-- `log selfDiam(B_r(c))(X) ∈ L¹` (`r > 0`). -/
theorem integrable_log_selfDiam (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) (ha : 0 < a)
    (hX : IsBandVersion P W κ a b X) (ξ : ℝ) (c : Rd d) {r : ℝ} (hr : 0 < r) :
    Integrable (fun ω => Real.log (selfDiam ξ (fun z => X z ω) c r)) P :=
  integrable_of_isSupLipschitzOn (F := fun φ => Real.log (selfDiam ξ φ c r)) hκ hW ha hX
    (isCompact_cbox c r) (isSupLipschitzOn_log_selfDiam ξ c hr)

/-- **Concentration of `log selfDiam`** (MA7 D-4.6; used in D-4.7s): for `r > 0` and `t ≥ 0`,
`P[|log selfDiam(B_r(c))(X) - E …| ≥ t] ≤ 2 exp(-t² / (2 ξ² log(b/a)))`. -/
theorem measure_abs_log_selfDiam_sub_ge_le (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    (ha : 0 < a) (hab : a ≤ b) (hX : IsBandVersion P W κ a b X) (ξ : ℝ) (c : Rd d) {r : ℝ}
    (hr : 0 < r) {t : ℝ} (ht : 0 ≤ t) :
    P {ω | t ≤ |Real.log (selfDiam ξ (fun z => X z ω) c r) -
        ∫ ω', Real.log (selfDiam ξ (fun z => X z ω') c r) ∂P|} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ξ ^ 2 * Real.log (b / a)))) :=
  measure_abs_log_sub_ge_le_of_logLipschitz (Φ := fun φ => selfDiam ξ φ c r) hκ hW ha hab hX
    (isCompact_cbox c r) ξ (isSupLipschitzOn_log_selfDiam ξ c hr) ht

/-- `log acrossDist(B_{r₁}(c) \ B_{r₂}(c))(X) ∈ L¹` (`r₂ < r₁`). -/
theorem integrable_log_acrossDist (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) (ha : 0 < a)
    (hX : IsBandVersion P W κ a b X) (ξ : ℝ) (c : Rd d) {r₁ r₂ : ℝ} (hr : r₂ < r₁) :
    Integrable (fun ω => Real.log (acrossDist ξ (fun z => X z ω) c r₁ r₂)) P :=
  integrable_of_isSupLipschitzOn (F := fun φ => Real.log (acrossDist ξ φ c r₁ r₂)) hκ hW ha hX
    (isCompact_cbox c r₁) (isSupLipschitzOn_log_acrossDist ξ c hr)

/-- **Concentration of `log acrossDist`** (MA7 D-4.6; used in D-4.10, D-5.5): for `r₂ < r₁` and
`t ≥ 0`, `P[|log D(across B_{r₁}(c) \ B_{r₂}(c))(X) - E …| ≥ t] ≤ 2 exp(-t² / (2 ξ² log(b/a)))`. -/
theorem measure_abs_log_acrossDist_sub_ge_le (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    (ha : 0 < a) (hab : a ≤ b) (hX : IsBandVersion P W κ a b X) (ξ : ℝ) (c : Rd d)
    {r₁ r₂ : ℝ} (hr : r₂ < r₁) {t : ℝ} (ht : 0 ≤ t) :
    P {ω | t ≤ |Real.log (acrossDist ξ (fun z => X z ω) c r₁ r₂) -
        ∫ ω', Real.log (acrossDist ξ (fun z => X z ω') c r₁ r₂) ∂P|} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ξ ^ 2 * Real.log (b / a)))) :=
  measure_abs_log_sub_ge_le_of_logLipschitz (Φ := fun φ => acrossDist ξ φ c r₁ r₂) hκ hW ha hab
    hX (isCompact_cbox c r₁) ξ (isSupLipschitzOn_log_acrossDist ξ c hr) ht

/-- `log D(A, B; V)(X) ∈ L¹` for `V` inside a compact set. -/
theorem integrable_log_lfppSetDist (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) (ha : 0 < a)
    (hX : IsBandVersion P W κ a b X) (ξ : ℝ) {V K : Set (Rd d)} (hK : IsCompact K) (hVK : V ⊆ K)
    (A B : Set (Rd d)) :
    Integrable (fun ω => Real.log (lfppSetDist ξ (fun z => X z ω) V A B)) P :=
  integrable_of_isSupLipschitzOn (F := fun φ => Real.log (lfppSetDist ξ φ V A B)) hκ hW ha hX hK
    (isSupLipschitzOn_log_lfppSetDist ξ hVK A B)

/-- **Concentration of `log D(A, B; V)`** (MA7 D-4.6; used in D-4.8 (2)): for `V` inside a compact
set `K` and `t ≥ 0`, `P[|log D(A, B; V)(X) - E …| ≥ t] ≤ 2 exp(-t² / (2 ξ² log(b/a)))`. -/
theorem measure_abs_log_lfppSetDist_sub_ge_le (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    (ha : 0 < a) (hab : a ≤ b) (hX : IsBandVersion P W κ a b X) (ξ : ℝ) {V K : Set (Rd d)}
    (hK : IsCompact K) (hVK : V ⊆ K) (A B : Set (Rd d)) {t : ℝ} (ht : 0 ≤ t) :
    P {ω | t ≤ |Real.log (lfppSetDist ξ (fun z => X z ω) V A B) -
        ∫ ω', Real.log (lfppSetDist ξ (fun z => X z ω') V A B) ∂P|} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ξ ^ 2 * Real.log (b / a)))) :=
  measure_abs_log_sub_ge_le_of_logLipschitz (Φ := fun φ => lfppSetDist ξ φ V A B) hκ hW ha hab
    hX hK ξ (isSupLipschitzOn_log_lfppSetDist ξ hVK A B) ht

/-- `log Diam(U; V)(X) ∈ L¹` for `V` open, preconnected and inside a compact set, and `U` inside a
compact subset of `V`. -/
theorem integrable_log_lfppDiam (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) (ha : 0 < a)
    (hX : IsBandVersion P W κ a b X) (ξ : ℝ) {U V K₀ K : Set (Rd d)} (hV : IsOpen V)
    (hVc : IsPreconnected V) (hK₀ : IsCompact K₀) (hK₀V : K₀ ⊆ V) (hUK₀ : U ⊆ K₀)
    (hK : IsCompact K) (hVK : V ⊆ K) :
    Integrable (fun ω => Real.log (lfppDiam ξ (fun z => X z ω) U V)) P :=
  integrable_of_isSupLipschitzOn (F := fun φ => Real.log (lfppDiam ξ φ U V)) hκ hW ha hX hK
    (isSupLipschitzOn_log_lfppDiam ξ hV hVc hK₀ hK₀V hUK₀ hVK)

/-- **Concentration of `log Diam(U; V)`** (MA7 D-4.6; DGZ Lemma 4.6 for bounded `V`): for `V` open,
preconnected and inside a compact set `K`, `U` inside a compact subset of `V`, and `t ≥ 0`,
`P[|log Diam(U; V)(X) - E …| ≥ t] ≤ 2 exp(-t² / (2 ξ² log(b/a)))`. -/
theorem measure_abs_log_lfppDiam_sub_ge_le (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    (ha : 0 < a) (hab : a ≤ b) (hX : IsBandVersion P W κ a b X) (ξ : ℝ)
    {U V K₀ K : Set (Rd d)} (hV : IsOpen V) (hVc : IsPreconnected V) (hK₀ : IsCompact K₀)
    (hK₀V : K₀ ⊆ V) (hUK₀ : U ⊆ K₀) (hK : IsCompact K) (hVK : V ⊆ K) {t : ℝ} (ht : 0 ≤ t) :
    P {ω | t ≤ |Real.log (lfppDiam ξ (fun z => X z ω) U V) -
        ∫ ω', Real.log (lfppDiam ξ (fun z => X z ω') U V) ∂P|} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ξ ^ 2 * Real.log (b / a)))) :=
  measure_abs_log_sub_ge_le_of_logLipschitz (Φ := fun φ => lfppDiam ξ φ U V) hκ hW ha hab hX hK
    ξ (isSupLipschitzOn_log_lfppDiam ξ hV hVc hK₀ hK₀V hUK₀ hVK) ht

/-- **Concentration of `log D(x, y; V)`** with an arbitrary compact `K ⊇ V` (MA7 D-4.6; for
`K = closure V` this is HigherDimLFPP's `IsBandVersion.measure_abs_log_lfppDistOn_sub_ge_le`). -/
theorem measure_abs_log_lfppDistOn_sub_ge_le' (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    (ha : 0 < a) (hab : a ≤ b) (hX : IsBandVersion P W κ a b X) (ξ : ℝ) {V K : Set (Rd d)}
    (hK : IsCompact K) (hVK : V ⊆ K) {x : Rd d} (hx : x ∈ V) (y : Rd d) {t : ℝ} (ht : 0 ≤ t) :
    P {ω | t ≤ |Real.log (lfppDistOn ξ (fun z => X z ω) V x y) -
        ∫ ω', Real.log (lfppDistOn ξ (fun z => X z ω') V x y) ∂P|} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ξ ^ 2 * Real.log (b / a)))) :=
  measure_abs_log_sub_ge_le_of_logLipschitz (Φ := fun φ => lfppDistOn ξ φ V x y) hκ hW ha hab hX
    hK ξ (isSupLipschitzOn_log_lfppDistOn ξ hx y hVK) ht

end Band

end HigherDimLQGMetric.DGZ
