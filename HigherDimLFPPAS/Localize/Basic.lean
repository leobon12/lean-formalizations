import HigherDimLFPPAS.Core.Interfaces
import HigherDimLQGMetric.Limits.WeylLFPP
import HigherDimLQGMetric.Main.LFPPMedian
import HigherDimLQGMetric.Metric.WeylMetric
import HigherDimLQGMetric.Weak.DetLimit
import HigherDimLFPP.Paths.Compare
import HigherDimLFPP.Paths.Measurable

/-!
# The localized metric `M_ε` and the LFPP metric `N_ε`: identifications and measurability

Packet L24 (Lemma 2.4 of `source/higher-dimensional-lfpp-almost-sure.pdf`; planning audit MA1 §2.7 and
Details A6). Deterministic and measure-theoretic preliminaries for the two assertions of Lemma 2.4.

* `meps_eq_smul`, `neps_eq_smul`: for `𝔞_ε > 0`, `M_ε = 𝔞_ε⁻¹ D^{ĥ*_ε}` and `N_ε = 𝔞_ε⁻¹ D^{h*_ε}` (the
  bundled fields `Core.locFieldC`, `Core.convFieldC`); `meps_isLength`, `neps_isLength` (always).
* `meps_eq_weylMetric`: `M_ε = e^{ξ(ĥ*_ε − h*_ε)} · N_ε` as continuous metrics (the Weyl scaling of the
  length metric `N_ε`), the form used by the deterministic observation of Lemma 2.4 (packet D1).
* `smul_fieldLfppMetric_eq`: a constant multiple of an LFPP metric is the LFPP metric of the field shifted
  by a constant (`ξ ≠ 0`).
* `locFieldC_coe`, `convFieldC_coe`: the bundled fields agree with `locField`, `convMollify` where these
  are continuous.
* Measurability: `measurable_smul_fieldLfppMetric` (on `C(ℝ^d, ℝ)`), `measurable_meps` (for
  `0 < locRad ε`), `aemeasurable_neps` (for a.s. continuous `h*_ε`), `measurable_metric_comp`.
* `isProperFn_of_properSpace`: properness of a continuous metric in the sense of `IsProperFn`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Localize

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ## The bundled fields -/

/-- Where `ĥ*_ε` is continuous, the bundled field `Core.locFieldC` is `ĥ*_ε`. -/
theorem locFieldC_coe {κ : Rd d → ℝ} {ε : ℝ} {g : DistRd d} (hc : Continuous (locField κ ε g)) :
    ⇑(Core.locFieldC κ ε g) = locField κ ε g := by
  unfold Core.locFieldC
  rw [dite_eq_left hc]
  rfl

/-- Where `h*_ε` is continuous, the bundled field `Core.convFieldC` is `h*_ε`. -/
theorem convFieldC_coe {κ : Rd d → ℝ} {ε : ℝ} {g : DistRd d}
    (hc : Continuous (convMollify κ ε g)) :
    ⇑(Core.convFieldC κ ε g) = convMollify κ ε g := by
  unfold Core.convFieldC
  rw [dite_eq_left hc]
  rfl

/-! ## `M_ε` and `N_ε` as multiples of LFPP metrics -/

theorem meps_eq_smul {κ : Rd d → ℝ} {ξ ε : ℝ} (g : DistRd d) (ha : 0 < aEps κ ξ ε) :
    Core.Meps κ ξ ε g =
      (fieldLfppMetric ξ (Core.locFieldC κ ε g)).smul (aEps κ ξ ε)⁻¹ (inv_pos.2 ha) := by
  unfold Core.Meps
  rw [dite_eq_left ha]

theorem neps_eq_smul {κ : Rd d → ℝ} {ξ ε : ℝ} (g : DistRd d) (ha : 0 < aEps κ ξ ε) :
    Core.Neps κ ξ ε g =
      (fieldLfppMetric ξ (Core.convFieldC κ ε g)).smul (aEps κ ξ ε)⁻¹ (inv_pos.2 ha) := by
  unfold Core.Neps
  rw [dite_eq_left ha]

/-- `M_ε` is a length metric (both branches of its definition are). -/
theorem meps_isLength (κ : Rd d → ℝ) (ξ ε : ℝ) (g : DistRd d) : (Core.Meps κ ξ ε g).IsLength := by
  unfold Core.Meps
  split_ifs with ha
  · exact ContMetric.isLength_smul _ (fieldLfppMetric_isLength ξ _)
  · exact fieldLfppMetric_isLength ξ _

/-- `N_ε` is a length metric (both branches of its definition are). -/
theorem neps_isLength (κ : Rd d → ℝ) (ξ ε : ℝ) (g : DistRd d) : (Core.Neps κ ξ ε g).IsLength := by
  unfold Core.Neps
  split_ifs with ha
  · exact ContMetric.isLength_smul _ (fieldLfppMetric_isLength ξ _)
  · exact fieldLfppMetric_isLength ξ _

theorem meps_apply {κ : Rd d → ℝ} {ξ ε : ℝ} (g : DistRd d) (ha : 0 < aEps κ ξ ε)
    (p : Rd d × Rd d) :
    (Core.Meps κ ξ ε g).1 p = (aEps κ ξ ε)⁻¹ * fieldLfpp ξ (Core.locFieldC κ ε g) p := by
  rw [meps_eq_smul g ha, ContMetric.smul_apply, fieldLfppMetric_apply]

theorem neps_apply {κ : Rd d → ℝ} {ξ ε : ℝ} (g : DistRd d) (ha : 0 < aEps κ ξ ε)
    (p : Rd d × Rd d) :
    (Core.Neps κ ξ ε g).1 p = (aEps κ ξ ε)⁻¹ * fieldLfpp ξ (Core.convFieldC κ ε g) p := by
  rw [neps_eq_smul g ha, ContMetric.smul_apply, fieldLfppMetric_apply]

/-- Where `h*_ε` is continuous, `N_ε = 𝔞_ε⁻¹ D^ε_g` pointwise (the metric of the frozen conclusion). -/
theorem neps_apply_eq_lfppDist {κ : Rd d → ℝ} {ξ ε : ℝ} {g : DistRd d} (ha : 0 < aEps κ ξ ε)
    (hc : Continuous (convMollify κ ε g)) (p : Rd d × Rd d) :
    (Core.Neps κ ξ ε g).1 p = ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε g) p := by
  rw [neps_apply g ha, convFieldC_coe hc, fieldLfpp_eq_lfppDistOn hc p, Pi.smul_apply,
    smul_eq_mul]
  rfl

/-- **`M_ε` is the Weyl scaling `e^{ξ(ĥ*_ε − h*_ε)} · N_ε`** of the length metric `N_ε` (for `𝔞_ε > 0`). -/
theorem meps_eq_weylMetric {κ : Rd d → ℝ} {ξ ε : ℝ} (g : DistRd d) (ha : 0 < aEps κ ξ ε) :
    (Core.Meps κ ξ ε g).1 =
      (weylMetric ξ (Core.locFieldC κ ε g - Core.convFieldC κ ε g) (Core.Neps κ ξ ε g)
        (neps_isLength κ ξ ε g)).1 := by
  ext p
  rw [weylMetric_apply]
  have hN := neps_eq_smul (κ := κ) (ξ := ξ) g ha
  have hW : (weylScale ξ (Core.locFieldC κ ε g - Core.convFieldC κ ε g) (Core.Neps κ ξ ε g)
      p.1 p.2).toReal = (aEps κ ξ ε)⁻¹ * fieldLfpp ξ
        (⇑(Core.convFieldC κ ε g) + ⇑(Core.locFieldC κ ε g - Core.convFieldC κ ε g))
        (p.1, p.2) := by
    rw [hN]
    exact l6c_scaledLfpp_weyl_field ξ (aEps κ ξ ε) ha _ _ p.1 p.2
  rw [hW, meps_apply g ha]
  congr 2
  funext z
  simp only [Pi.add_apply, ContinuousMap.coe_sub, Pi.sub_apply, add_sub_cancel]

/-- A constant multiple of an LFPP metric is the LFPP metric of the field shifted by a constant. -/
theorem smul_fieldLfppMetric_eq {ξ : ℝ} (hξ : ξ ≠ 0) (φ : C(Rd d, ℝ)) {c : ℝ} (hc : 0 < c) :
    (fieldLfppMetric ξ φ).smul c hc =
      fieldLfppMetric ξ (φ + ContinuousMap.const (Rd d) (ξ⁻¹ * Real.log c)) := by
  apply Subtype.ext
  ext p
  have hcont : Continuous (⇑(φ + ContinuousMap.const (Rd d) (ξ⁻¹ * Real.log c))) :=
    ContinuousMap.continuous _
  change c * fieldLfpp ξ φ p = fieldLfpp ξ (⇑(φ + ContinuousMap.const (Rd d) (ξ⁻¹ * Real.log c))) p
  rw [fieldLfpp_eq_lfppDistOn φ.continuous p, fieldLfpp_eq_lfppDistOn hcont p]
  have hfun : (⇑(φ + ContinuousMap.const (Rd d) (ξ⁻¹ * Real.log c)) : Rd d → ℝ) =
      fun z => φ z + ξ⁻¹ * Real.log c := by
    funext z
    simp
  rw [hfun, HigherDimLFPP.lfppDistOn_add_const]
  congr 1
  rw [← mul_assoc, mul_inv_cancel₀ hξ, one_mul, Real.exp_log hc]

/-! ## Measurability -/

/-- `φ ↦ c · D^φ` is measurable on `C(ℝ^d, ℝ)` (Borel σ-algebras of the compact-open topologies). -/
theorem measurable_smul_fieldLfppMetric (ξ : ℝ) {c : ℝ} (hc : 0 < c) :
    Measurable fun φ : C(Rd d, ℝ) => ((fieldLfppMetric ξ φ).smul c hc).1 := by
  refine ContinuousMap.measurable_iff_eval.2 fun p => ?_
  have heq : (fun φ : C(Rd d, ℝ) => ((fieldLfppMetric ξ φ).smul c hc).1 p) =
      fun φ : C(Rd d, ℝ) => c * HigherDimLFPP.lfppDistOn ξ φ univ p.1 p.2 := by
    funext φ
    rw [ContMetric.smul_apply, fieldLfppMetric_apply, fieldLfpp_eq_lfppDistOn φ.continuous p]
  rw [heq]
  exact (HigherDimLFPP.measurable_lfppDistOn_continuousMap isOpen_univ ξ p.1 p.2).const_mul c

/-- A measurable metric assignment composed with a measurable random distribution gives a measurable
random continuous function. -/
theorem measurable_metric_comp {D : DistRd d → ContMetric d} (hD : Measurable D)
    {Ω : Type*} [MeasurableSpace Ω] {h : Ω → DistRd d} (hh : Measurable h) :
    Measurable fun ω => (D (h ω)).1 :=
  measurable_subtype_coe.comp (hD.comp hh)

/-- For `0 < locRad ε` and a smooth kernel, `ω ↦ M_ε(h ω)` is measurable. -/
theorem measurable_meps {κ : Rd d → ℝ} {ξ ε : ℝ}
    (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ)) (hs : 0 < locRad ε)
    (ha : 0 < aEps κ ξ ε) {Ω : Type*} [MeasurableSpace Ω] {h : Ω → DistRd d} (hh : Measurable h) :
    Measurable fun ω => (Core.Meps κ ξ ε (h ω)).1 := by
  have hloc : Measurable fun ω => Core.locFieldC κ ε (h ω) := by
    refine ContinuousMap.measurable_iff_eval.2 fun z => ?_
    have heq : (fun ω => Core.locFieldC κ ε (h ω) z) = fun ω => locField κ ε (h ω) z := by
      funext ω
      rw [locFieldC_coe (continuous_locField hK hs (h ω))]
    rw [heq]
    exact (measurable_locField_apply κ ε z).comp hh
  have heq : (fun ω => (Core.Meps κ ξ ε (h ω)).1) =
      (fun φ : C(Rd d, ℝ) => ((fieldLfppMetric ξ φ).smul (aEps κ ξ ε)⁻¹ (inv_pos.2 ha)).1) ∘
        fun ω => Core.locFieldC κ ε (h ω) := by
    funext ω
    simp only [Function.comp_apply, meps_eq_smul (h ω) ha]
  rw [heq]
  exact (measurable_smul_fieldLfppMetric ξ (inv_pos.2 ha)).comp hloc

/-- If `h*_ε` is a.s. continuous, `ω ↦ N_ε(h ω)` is a.e.-measurable. -/
theorem aemeasurable_neps {κ : Rd d → ℝ} {ξ ε : ℝ} (ha : 0 < aEps κ ξ ε)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d} (hh : Measurable h)
    (hc : ∀ᵐ ω ∂P, Continuous (convMollify κ ε (h ω))) :
    AEMeasurable (fun ω => (Core.Neps κ ξ ε (h ω)).1) P := by
  let Y : Rd d → Ω → ℝ := fun z ω => Core.convFieldC κ ε (h ω) z
  have hYc : ∀ ω, Continuous fun z => Y z ω := fun ω => (Core.convFieldC κ ε (h ω)).continuous
  have hYm : ∀ z, AEMeasurable (Y z) P := by
    intro z
    have hmeas : Measurable fun ω => convMollify κ ε (h ω) z :=
      (l10a_measurable_convMollify_apply κ ε z).comp hh
    refine (aemeasurable_congr ?_).1 hmeas.aemeasurable
    filter_upwards [hc] with ω hω
    change convMollify κ ε (h ω) z = Core.convFieldC κ ε (h ω) z
    rw [convFieldC_coe hω]
  have hconv : AEMeasurable (fun ω => Core.convFieldC κ ε (h ω)) P :=
    l10a_aemeasurable_toContMap Y hYm hYc
  have heq : (fun ω => (Core.Neps κ ξ ε (h ω)).1) =
      (fun φ : C(Rd d, ℝ) => ((fieldLfppMetric ξ φ).smul (aEps κ ξ ε)⁻¹ (inv_pos.2 ha)).1) ∘
        fun ω => Core.convFieldC κ ε (h ω) := by
    funext ω
    simp only [Function.comp_apply, neps_eq_smul (h ω) ha]
  rw [heq]
  exact (measurable_smul_fieldLfppMetric ξ (inv_pos.2 ha)).comp_aemeasurable hconv

/-! ## Properness -/

/-- A proper continuous metric is proper in the sense of `IsProperFn` (crossing distances diverge). -/
theorem isProperFn_of_properSpace (G : ContMetric d)
    (hG : ∀ K : Set (Rd d), IsCompact K → ∀ M : ℝ, ∃ R : ℝ,
      ∀ x ∈ K, ∀ y : Rd d, R ≤ ‖y‖ → M < G.1 (x, y)) :
    IsProperFn G.1 := by
  intro r hr M
  obtain ⟨R₀, hR₀⟩ := hG (closedBall (0 : Rd d) r) (isCompact_closedBall _ _) M
  refine ⟨max R₀ (r + 1), lt_of_lt_of_le (by linarith) (le_max_right _ _), ?_⟩
  refine le_iInf₂ fun u hu => le_iInf₂ fun v hv => ?_
  have hv' : ‖v‖ = max R₀ (r + 1) := by simpa using hv
  exact ENNReal.ofReal_le_ofReal (hR₀ u hu v (hv'.symm ▸ le_max_left _ _)).le

end HigherDimLFPPAS.Localize
