import HigherDimLFPPAS.Core.Interfaces
import HigherDimLFPPAS.Field.Prelim
import HigherDimLFPPAS.Field.PathwiseRadial
import HigherDimLFPPAS.Scaling.LocFieldScaling
import HigherDimLFPPAS.Signed.Sec4

/-!
# The rescaled localization bound (3.9) (packet RZL, MA1 A10.2, MA3 P2.4′)

For `0 < ε ≤ r ≤ 1` put `δ := ε / r ∈ [ε, 1]` (kernel scale) and `s := locRad ε / r = δ L_ε` (truncation radius,
`L_ε = (log ε⁻¹)^{10}`), so that `Core.locFieldR κ ε r g = (locMass κ δ s)⁻¹ ⟨g, locTest κ δ s ·⟩`. This file proves
(3.9): almost surely, on `B̄_R`,
`|ĝ_{δ,ε} − g ∗ K_δ| ≤ C_R(ω) · l9bErr d κ C_K ε`, with `l9bErr d κ C_K ε → 0` as `ε ↓ 0`
(`rzl_ae_locFieldR_sub_convMollify_le`, one event for **all** `ε < ε₀`, `r ∈ [ε, 1]`), and hence the interface
`Core.RescaledLoc` (`rescaledLoc_holds`).

Proof (MA1 A10.2). The random constant is the measurable growth constant `C_R` of the sphere averages on `B̄_R`
(`HigherDimLQGMetric.l9b_exists_growth_const`). On the event where the polar formulas of `g ∗ K_δ`
(`Field.radial_formula_F1`) and of the localized pairing (`Field.ae_locTest_radial_all_F1b`) hold for all parameters,
and the sphere averages are continuous, the sign-free localization error `Core.SeedFacts.locError` at kernel scale `δ`
and radius `s` applies: its hypotheses are `δ ≤ 1` (from `ε ≤ r`), `s / (2δ) = locRad ε / (2ε) ≥ 1` and
`locMass κ δ s = locMass κ ε (locRad ε) ≥ 1/2` (the mass clause of `Core.LocFieldScaling`,
`Scaling.locFieldScaling_holds`, and `Core.SeedFacts.locHyp`). Its rate is `(1 + log δ⁻¹)(L_ε/2)^{-1/2}` up to
constants, and `log δ⁻¹ ≤ log ε⁻¹` (from `r ≤ 1`) bounds it by the `r`-free rate `l9bErr d κ C_K ε`
(`HigherDimLQGMetric.tendsto_l9bErr`). The sharp rate `(1 + log δ⁻¹)/L_ε` of `Field.locField_error_sharp_F1b` is not used:
its hypothesis `log(L_ε/2) ≤ log δ⁻¹` fails for `δ` near `1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open HigherDimLFPP (Rd e₁)
open HigherDimLQGMetric

namespace HigherDimLFPPAS.Rescale

variable {d : ℕ} {κ : Rd d → ℝ}

/-- **Deterministic rescaled localization error** (MA1 A10.2): for `0 < ε < 1` satisfying the localization hypotheses
of `Core.SeedFacts.locHyp`, `r ∈ [ε, 1]` and a distribution `g` whose polar formulas at kernel scale `δ = ε / r` and
radius `locRad ε / r` hold at `z`, with continuous sphere averages and `|g_t(z)| ≤ C G(t)`,
`|ĝ_{δ,ε}(z) − g ∗ K_δ(z)| ≤ C · l9bErr d κ C_K ε`. -/
theorem rzl_locFieldR_sub_convMollify_le (hd : 2 ≤ d) (hseed : Core.SeedFacts d κ)
    {CK : ℝ} (hCK0 : 0 ≤ CK)
    (hCK : ∀ u : ℝ, 0 ≤ u → |convKernel κ (u • e₁ d)| ≤ CK * (1 + u) ^ (-((d : ℝ) + 1)))
    {ε r : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hrad : 0 < locRad ε) (ha : 1 ≤ locRad ε / (2 * ε))
    (hZ : 1 / 2 ≤ locMass κ ε (locRad ε)) (hεr : ε ≤ r) (hr1 : r ≤ 1)
    {g : DistRd d} {z : Rd d} {C : ℝ} (hC0 : 0 ≤ C)
    (hφ : convMollify κ (ε / r) g z = sphArea d * ∫ t in Ioi (0 : ℝ),
      t ^ (d - 1) * convKernelEps κ (ε / r) (t • e₁ d) * sphereAvg g t z)
    (hψ : g (locTest κ (ε / r) (locRad ε / r) z) = sphArea d * ∫ t in Ioi (0 : ℝ),
      t ^ (d - 1) * locTest κ (ε / r) (locRad ε / r) z (z + t • e₁ d) * sphereAvg g t z)
    (hcont : ContinuousOn (fun t => sphereAvg g t z) (Ioi 0))
    (hgrowth : ∀ t : ℝ, 0 < t → |sphereAvg g t z| ≤ C * l2b_growthWeight t) :
    |Core.locFieldR κ ε r g z - convMollify κ (ε / r) g z| ≤ C * l9bErr d κ CK ε := by
  have hr : 0 < r := hε.trans_le hεr
  have hδ : 0 < ε / r := div_pos hε hr
  have hδ1 : ε / r ≤ 1 := div_le_one_of_le₀ hεr hr.le
  have hs : 0 < locRad ε / r := div_pos hrad hr
  -- the radius-to-scale ratio and the mass are those at `r = 1`
  have hratio : locRad ε / r / (2 * (ε / r)) = locRad ε / (2 * ε) := by
    field_simp
  have hmass : locMass κ (ε / r) (locRad ε / r) = locMass κ ε (locRad ε) :=
    (Scaling.locFieldScaling_holds hd hseed.kernelSmooth ε r hε hε1 hr).1
  have key := hseed.locError hCK0 hCK hδ hδ1 hs (by rw [hratio]; exact ha)
    (by rw [hmass]; exact hZ) hC0 hφ hψ hcont hgrowth
  rw [hratio] at key
  -- `log δ⁻¹ ≤ log ε⁻¹` since `r ≤ 1`
  have hlog : Real.log (ε / r)⁻¹ ≤ Real.log ε⁻¹ := by
    refine Real.log_le_log (inv_pos.2 hδ) ?_
    rw [inv_div]
    calc r / ε ≤ 1 / ε := div_le_div_of_nonneg_right hr1 hε.le
      _ = ε⁻¹ := one_div ε
  have hA0 : 0 ≤ sphArea d := sphArea_nonneg d
  have hM0 : 0 ≤ l9bKernelMoment κ := l9bKernelMoment_nonneg κ
  have hq : 0 ≤ 6 * CK / Real.sqrt (locRad ε / (2 * ε)) := by positivity
  unfold Core.locFieldR
  rw [abs_sub_comm]
  calc |convMollify κ (ε / r) g z -
        (locMass κ (ε / r) (locRad ε / r))⁻¹ * g (locTest κ (ε / r) (locRad ε / r) z)|
      ≤ C * sphArea d * (1 + Real.log (ε / r)⁻¹) * (6 * CK / Real.sqrt (locRad ε / (2 * ε))) *
          (1 + 2 * sphArea d * l9bKernelMoment κ) := key
    _ ≤ C * sphArea d * (1 + Real.log ε⁻¹) * (6 * CK / Real.sqrt (locRad ε / (2 * ε))) *
          (1 + 2 * sphArea d * l9bKernelMoment κ) := by gcongr
    _ = C * l9bErr d κ CK ε := by
        unfold l9bErr
        ring

/-- **(3.9) on one event, uniformly in the parameters** (MA1 A10.2, MA3 P2.4′): under the standing hypotheses there are
a constant `C_K ≥ 0` and `ε₀ ∈ (0, 1)` such that for every `R > 0` there is a measurable random constant `C ≥ 0` with,
almost surely, `|ĝ_{ε/r,ε}(x) − h ∗ K_{ε/r}(x)| ≤ C(ω) · l9bErr d κ C_K ε` for **all** `ε ∈ (0, ε₀)`, `r ∈ [ε, 1]` and
`x ∈ B̄_R`. The rate `l9bErr d κ C_K ε` tends to `0` (`HigherDimLQGMetric.tendsto_l9bErr`). -/
theorem rzl_ae_locFieldR_sub_convMollify_le {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Core.Setting d ξ Q κ D P h) :
    ∃ CK ε₀ : ℝ, 0 ≤ CK ∧ 0 < ε₀ ∧ ε₀ < 1 ∧ ∀ R : ℝ, 0 < R → ∃ C : Ω → ℝ, Measurable C ∧
      (∀ ω, 0 ≤ C ω) ∧ ∀ᵐ ω ∂P, ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ r ∈ Icc ε 1,
        ∀ x ∈ closedBall (0 : Rd d) R,
          |Core.locFieldR κ ε r (h ω) x - convMollify κ (ε / r) (h ω) x| ≤ C ω * l9bErr d κ CK ε := by
  have hd : 2 ≤ d := by have := hS.dim; omega
  obtain ⟨CK, hCK0, hCK⟩ := Signed.l9b_kernel_axis_decay_seed hd hS.admissible
  obtain ⟨ε₁, hε₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hS.seed.locHyp
  have hε₁0 : 0 < ε₁ := hε₁
  refine ⟨CK, min ε₁ (1 / 2), hCK0, lt_min hε₁0 (by norm_num),
    (min_le_right _ _).trans_lt (by norm_num), fun R hR => ?_⟩
  obtain ⟨Ĉ, hĈm, -, hĈ⟩ := l9b_exists_growth_const hd hS.field hR
  refine ⟨fun ω => (Ĉ ω).toReal, ENNReal.measurable_toReal.comp hĈm,
    fun ω => ENNReal.toReal_nonneg, ?_⟩
  filter_upwards [Field.radial_formula_F1 hd hS.admissible hS.field,
    Field.ae_locTest_radial_all_F1b hd hS.seed.kernelSmooth hS.field,
    hS.field.1.ae_continuousOn_sphereAvg hd, hĈ] with ω hφ hψ hcont hgrowth
  intro ε hε r hr x hx
  obtain ⟨hε0, -, hrad, ha, hZ⟩ := hsub ⟨hε.1, lt_of_lt_of_le hε.2 (min_le_left _ _)⟩
  have hε1 : ε < 1 := lt_of_lt_of_le hε.2 ((min_le_right _ _).trans (by norm_num))
  have hr0 : 0 < r := hε0.trans_le hr.1
  have hcx : ContinuousOn (fun t => sphereAvg (h ω) t x) (Ioi 0) := by
    have hpc : Continuous fun t : ℝ => ((t, x) : ℝ × Rd d) :=
      continuous_id.prodMk continuous_const
    exact ContinuousOn.comp (f := fun t : ℝ => ((t, x) : ℝ × Rd d))
      (g := fun p : ℝ × Rd d => sphereAvg (h ω) p.1 p.2) hcont.2 hpc.continuousOn
      (fun t ht => mk_mem_prod ht (mem_univ _))
  exact rzl_locFieldR_sub_convMollify_le hd hS.seed hCK0 hCK hε0 hε1 hrad ha hZ hr.1 hr.2
    ENNReal.toReal_nonneg (hφ (ε / r) (div_pos hε0 hr0) x)
    (hψ (ε / r) (locRad ε / r) (div_pos hε0 hr0) (div_pos hrad hr0) x) hcx (hgrowth x hx)

/-- **(3.9)**, the interface `Core.RescaledLoc` (MA1 A10.2, MA3 P2.4′), from the standing hypotheses: for every
`R > 0`, with the measurable growth constant `C_R` and the rate `ρ = l9bErr d κ C_K → 0`, for each `ε < ε₀` and
`r ∈ [ε, 1]`, a.s. on `B̄_R`, `|ĝ_{ε/r,ε} − h ∗ K_{ε/r}| ≤ C_R ρ(ε)`. -/
theorem rescaledLoc_holds {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Core.Setting d ξ Q κ D P h) : Core.RescaledLoc κ P h := by
  obtain ⟨CK, ε₀, -, hε₀, -, hmain⟩ := rzl_ae_locFieldR_sub_convMollify_le hS
  intro R hR
  obtain ⟨C, -, -, hC⟩ := hmain R hR
  refine ⟨C, l9bErr d κ CK, ε₀, hε₀, tendsto_l9bErr κ CK, fun ε hε r hr => ?_⟩
  filter_upwards [hC] with ω hω
  exact hω ε hε r hr

end HigherDimLFPPAS.Rescale
