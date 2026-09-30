import QuantumZipper.Proofs.Thm18.LWExc2Refl
import QuantumZipper.Proofs.Zipper.FieldLawlerSubExcGeo
import QuantumZipper.Proofs.Zipper.FieldLawler3Polar

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL round 3: boundary regularity of harmonic measures at analytic boundary arcs

If `f` is harmonic in `Ω`, `ψ` is holomorphic near a real point `x`, maps the upper half-disk
about `x` into `Ω`, and `f → 0` at the images of the real points, then `f ∘ ψ` extends
harmonically across `ℝ` near `x` (`fl3reg_ext`), by the reflection principle for harmonic
functions (L. Ahlfors, *Complex Analysis*, 3rd ed., Ch. 4 §6.5, Thm 24, pp. 172–173,
formalized as `harmReflectStmt_holds`). Consequently the vertical limit
`lim_{y↓0} f(ψ(x+iy))/y` exists (`fl3reg_vert_tendsto`), for harmonic measures on the
`0`-side (`fl3reg_harmMeas_zero`) and, applied to `1 − u`, on the `A`-side
(`fl3reg_harmMeas_one`). In the polar chart this gives the circle flux identity
`fl2FluxR R u = excR (u ∘ χ_R) (0, π)` for a harmonic measure vanishing on the upper half of
`C_R` (`fl3reg_fluxR_eq_excR`), without assuming differentiability of `u` on `C_R`.
The reflection step is Ahlfors'; the rest is own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Complex
open scoped Topology Real ENNReal

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

/-- **Local harmonic extension across an analytic boundary arc** (Ahlfors Thm 24 in a chart). -/
theorem fl3reg_ext {Ω : Set ℂ} {f : ℂ → ℝ} (hf : InnerProductSpace.HarmonicOnNhd f Ω)
    {ψ : ℂ → ℂ} {x r : ℝ} (hr : 0 < r) (hψ : AnalyticOnNhd ℂ ψ (ball (x : ℂ) r))
    (hψΩ : ∀ z ∈ ball (x : ℂ) r, 0 < z.im → ψ z ∈ Ω)
    (hψ0 : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → Tendsto f (𝓝[Ω] ψ z) (𝓝 0)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ ∃ V : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd V (ball (x : ℂ) ρ) ∧
      (∀ z ∈ ball (x : ℂ) ρ, 0 < z.im → V z = f (ψ z)) ∧
      (∀ z ∈ ball (x : ℂ) ρ, z.im = 0 → V z = 0) := by
  set v : ℂ → ℝ := fun z => if 0 < z.im then f (ψ z) else 0 with hv
  have hHo : IsOpen (H ∩ ball (x : ℂ) r) :=
    (isOpen_lt continuous_const Complex.continuous_im).inter isOpen_ball
  have hveq : EqOn v (f ∘ ψ) (H ∩ ball (x : ℂ) r) := fun w hw => by
    simp only [hv, if_pos (show 0 < w.im from hw.1), Function.comp]
  have hvharm : InnerProductSpace.HarmonicOnNhd v (H ∩ ball (x : ℂ) r) := by
    intro w hw
    refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp
      (fl_harmonicAt_comp (hψ w hw.2) (hf _ (hψΩ w hw.2 hw.1)))
    filter_upwards [hHo.mem_nhds hw] with u hu
    exact (hveq hu).symm
  have hvcont : ContinuousOn v (Hbar ∩ ball (x : ℂ) r) := by
    intro w ⟨hwH, hwB⟩
    have hwH' : 0 ≤ w.im := hwH
    rcases hwH'.lt_or_eq with hpos | hzero
    · have hwU : w ∈ H ∩ ball (x : ℂ) r := ⟨hpos, hwB⟩
      exact (hvharm w hwU).1.continuousAt.continuousWithinAt
    · have hψt : Tendsto ψ (𝓝[H ∩ ball (x : ℂ) r] w) (𝓝[Ω] ψ w) :=
        tendsto_nhdsWithin_iff.2 ⟨(hψ w hwB).continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
          eventually_nhdsWithin_of_forall fun z hz => hψΩ z hz.2 hz.1⟩
      have ht : Tendsto (f ∘ ψ) (𝓝[H ∩ ball (x : ℂ) r] w) (𝓝 0) :=
        (hψ0 w hwB hzero.symm).comp hψt
      have hvw : v w = 0 := by simp [hv, ← hzero]
      rw [ContinuousWithinAt, hvw]
      rw [Metric.tendsto_nhdsWithin_nhds] at ht ⊢
      intro ε hε
      obtain ⟨δ, hδ, hδs⟩ := ht ε hε
      refine ⟨δ, hδ, fun u hu hdu => ?_⟩
      by_cases hui : 0 < u.im
      · simp only [hv, if_pos hui]
        exact hδs ⟨hui, hu.2⟩ hdu
      · simp [hv, if_neg hui, hε]
  have hvzero : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → v z = 0 := fun z _ hz => by
    simp [hv, hz]
  obtain ⟨ρ, hρ, hρr, V, hVh, hVeq⟩ := harmReflectStmt_holds v x r hr hvharm hvcont hvzero
  refine ⟨ρ, hρ, hρr, V, hVh, fun z hz hzi => ?_, fun z hz hzi => ?_⟩
  · rw [hVeq ⟨show 0 ≤ z.im from hzi.le, hz⟩]; simp [hv, hzi]
  · rw [hVeq ⟨show 0 ≤ z.im from hzi.ge, hz⟩]; simp [hv, hzi]

/-- The vertical difference quotient of `g` at `x` converges when `g` agrees above `ℝ` with a
harmonic `V` vanishing at `x`; its limit is `DV(x)[i]`. -/
theorem fl3reg_vert_of_ext {g V : ℂ → ℝ} {x ρ : ℝ} (hρ : 0 < ρ)
    (hV : InnerProductSpace.HarmonicOnNhd V (ball (x : ℂ) ρ))
    (hVg : ∀ z ∈ ball (x : ℂ) ρ, 0 < z.im → V z = g z) (hV0 : V x = 0) :
    Tendsto (fun y : ℝ => g ((x : ℂ) + (y : ℂ) * I) / y) (𝓝[>] 0) (𝓝 (fderiv ℝ V x I)) := by
  have hxB : (x : ℂ) ∈ ball (x : ℂ) ρ := mem_ball_self hρ
  have hVd : HasFDerivAt V (fderiv ℝ V x) (x : ℂ) :=
    ((hV x hxB).1.differentiableAt (by norm_num)).hasFDerivAt
  have hpath : HasDerivAt (fun y : ℝ => (x : ℂ) + (y : ℂ) * I) I 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const I).const_add (x : ℂ)
    convert h1 using 1 <;> first | rfl | simp
  have hVd' : HasFDerivAt V (fderiv ℝ V x) ((x : ℂ) + ((0 : ℝ) : ℂ) * I) := by
    rw [show (x : ℂ) + ((0 : ℝ) : ℂ) * I = x by simp]; exact hVd
  have hcomp : HasDerivAt (fun y : ℝ => V ((x : ℂ) + (y : ℂ) * I)) (fderiv ℝ V x I) 0 :=
    hVd'.comp_hasDerivAt (0 : ℝ) hpath
  have hslope := hcomp.tendsto_slope.mono_left (nhdsGT_le_nhdsNE (0 : ℝ))
  have hev : (fun y : ℝ => g ((x : ℂ) + (y : ℂ) * I) / y) =ᶠ[𝓝[>] 0]
      slope (fun y : ℝ => V ((x : ℂ) + (y : ℂ) * I)) 0 := by
    filter_upwards [self_mem_nhdsWithin, (Ioo_mem_nhdsGT hρ : Ioo (0 : ℝ) ρ ∈ 𝓝[>] 0)]
      with y (hy : 0 < y) hyr
    have hyB : (x : ℂ) + (y : ℂ) * I ∈ ball (x : ℂ) ρ := by
      rw [mem_ball, dist_eq_norm]; simp [abs_of_pos hy]; exact hyr.2
    rw [slope_def_field, hVg _ hyB (by simp [hy])]
    simp [hV0]
  exact hslope.congr' hev.symm

/-- `yDer g x = DV(x)[i]` in the setting of `fl3reg_vert_of_ext`. -/
theorem fl3reg_yDer_of_ext {g V : ℂ → ℝ} {x ρ : ℝ} (hρ : 0 < ρ)
    (hV : InnerProductSpace.HarmonicOnNhd V (ball (x : ℂ) ρ))
    (hVg : ∀ z ∈ ball (x : ℂ) ρ, 0 < z.im → V z = g z) (hV0 : V x = 0) :
    yDer g x = fderiv ℝ V x I := by
  have hlim := fl3reg_vert_of_ext hρ hV hVg hV0
  unfold yDer
  rw [if_pos ⟨_, hlim⟩, hlim.limUnder_eq]

/-- **Vertical limit at an analytic boundary arc**: `lim_{y↓0} f(ψ(x+iy))/y` exists. -/
theorem fl3reg_vert_tendsto {Ω : Set ℂ} {f : ℂ → ℝ} (hf : InnerProductSpace.HarmonicOnNhd f Ω)
    {ψ : ℂ → ℂ} {x r : ℝ} (hr : 0 < r) (hψ : AnalyticOnNhd ℂ ψ (ball (x : ℂ) r))
    (hψΩ : ∀ z ∈ ball (x : ℂ) r, 0 < z.im → ψ z ∈ Ω)
    (hψ0 : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → Tendsto f (𝓝[Ω] ψ z) (𝓝 0)) :
    ∃ L : ℝ, Tendsto (fun y : ℝ => f (ψ ((x : ℂ) + (y : ℂ) * I)) / y) (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨ρ, hρ, -, V, hVh, hVf, hV0⟩ := fl3reg_ext hf hr hψ hψΩ hψ0
  exact ⟨_, fl3reg_vert_of_ext (g := f ∘ ψ) hρ hVh hVf (hV0 _ (mem_ball_self hρ) (by simp))⟩

/-- **Harmonic measure, `0`-side**: at boundary points away from `closure A`. -/
theorem fl3reg_harmMeas_zero {Ω A : Set ℂ} {u : ℂ → ℝ} (hu : IsHarmMeas Ω A u)
    {ψ : ℂ → ℂ} {x r : ℝ} (hr : 0 < r) (hψ : AnalyticOnNhd ℂ ψ (ball (x : ℂ) r))
    (hψΩ : ∀ z ∈ ball (x : ℂ) r, 0 < z.im → ψ z ∈ Ω)
    (hψfr : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → ψ z ∈ frontier Ω ∧ ψ z ∉ closure A) :
    ∃ L : ℝ, Tendsto (fun y : ℝ => u (ψ ((x : ℂ) + (y : ℂ) * I)) / y) (𝓝[>] 0) (𝓝 L) :=
  fl3reg_vert_tendsto hu.harm hr hψ hψΩ fun z hz hzi =>
    hu.zero _ (hψfr z hz hzi).1 (hψfr z hz hzi).2

/-! ### The polar chart `χ_R(ζ) = R e^{iζ}` -/

theorem fl3reg_chart_analytic (R : ℝ) (s : Set ℂ) : AnalyticOnNhd ℂ (fl3Chart R) s :=
  fun z _ => Differentiable.analyticAt (by unfold fl3Chart; fun_prop) z

/-- The inward radial segment at `R e^{iθ}` is the vertical segment `θ + i(−log(1 − s/R))`
in the chart. -/
theorem fl3reg_chart_radial {R θ s : ℝ} (hR : 0 < R) (hs : s < R) :
    fl3Chart R ((θ : ℂ) + I * ((-Real.log (1 - s / R) : ℝ) : ℂ)) = fl2Pt R θ s := by
  have hpos : 0 < 1 - s / R := by rw [sub_pos, div_lt_one hR]; exact hs
  have h1 : ((θ : ℂ) + I * ((-Real.log (1 - s / R) : ℝ) : ℂ)) * I =
      (θ : ℂ) * I + ((Real.log (1 - s / R) : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  rw [fl3Chart, fl2Pt, h1, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hpos]
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  push_cast
  field_simp

/-- Radial difference quotients at `R e^{iθ}` converge when `u ∘ χ_R` agrees above `ℝ` with a
harmonic `V` vanishing at `θ`. -/
theorem fl3reg_radial_of_ext {R θ ρ : ℝ} (hR : 0 < R) {u V : ℂ → ℝ} (hρ : 0 < ρ)
    (hV : InnerProductSpace.HarmonicOnNhd V (ball (θ : ℂ) ρ))
    (hVu : ∀ z ∈ ball (θ : ℂ) ρ, 0 < z.im → V z = u (fl3Chart R z)) (hV0 : V θ = 0) :
    Tendsto (fun s : ℝ => u (fl2Pt R θ s) / s) (𝓝[>] 0) (𝓝 (fderiv ℝ V θ I / R)) := by
  set p : ℝ → ℂ := fun s => (θ : ℂ) + I * ((-Real.log (1 - s / R) : ℝ) : ℂ) with hpdef
  have hq : HasDerivAt (fun s : ℝ => -Real.log (1 - s / R)) (1 / R) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => 1 - s / R) (-(1 / R)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).div_const R).const_sub 1
    have h2 := (h1.log (by simp)).neg
    rw [show (1 / R) = -(-(1 / R) / (1 - (0 : ℝ) / R)) by
      rw [zero_div, sub_zero, div_one, neg_neg]]
    exact h2
  have hp : HasDerivAt p (I * ((1 / R : ℝ) : ℂ)) 0 :=
    (hq.ofReal_comp.const_mul I).const_add (θ : ℂ)
  have hp0 : p 0 = θ := by simp [hpdef]
  have hθB : (θ : ℂ) ∈ ball (θ : ℂ) ρ := mem_ball_self hρ
  have hVd : HasFDerivAt V (fderiv ℝ V θ) (p 0) := by
    rw [hp0]; exact ((hV θ hθB).1.differentiableAt (by norm_num)).hasFDerivAt
  have hcomp := hVd.comp_hasDerivAt (0 : ℝ) hp
  have hslope := hcomp.tendsto_slope.mono_left (nhdsGT_le_nhdsNE (0 : ℝ))
  have hball : ∀ᶠ s : ℝ in 𝓝[>] 0, p s ∈ ball (θ : ℂ) ρ := by
    have ht := hp.continuousAt.tendsto
    rw [hp0] at ht
    exact nhdsWithin_le_nhds (ht.eventually (isOpen_ball.mem_nhds hθB))
  have hev : (fun s : ℝ => u (fl2Pt R θ s) / s) =ᶠ[𝓝[>] 0] slope (fun s => V (p s)) 0 := by
    filter_upwards [self_mem_nhdsWithin, (Ioo_mem_nhdsGT hR : Ioo (0 : ℝ) R ∈ 𝓝[>] 0), hball]
      with s (hs : 0 < s) hsR hsB
    have hlt : 0 < 1 - s / R := by rw [sub_pos, div_lt_one hR]; exact hsR.2
    have hlt1 : 1 - s / R < 1 := by have := div_pos hs hR; linarith
    have him : 0 < (p s).im := by
      simp only [hpdef, add_im, ofReal_im, mul_im, I_re, ofReal_re, I_im, one_mul,
        zero_add, mul_zero]
      linarith [Real.log_neg hlt hlt1]
    rw [slope_def_field, hVu _ hsB him, fl3reg_chart_radial hR hsR.2, hp0, hV0]
    simp
  have hlim := hslope.congr' hev.symm
  convert hlim using 2
  rw [show I * ((1 / R : ℝ) : ℂ) = (1 / R : ℝ) • I by rw [Complex.real_smul]; ring, map_smul,
    smul_eq_mul]
  ring

/-- `R · ∂ᵣ⁻ u(R e^{iθ}) = ∂_y (u ∘ χ_R)(θ)` given a harmonic extension of `u ∘ χ_R` at `θ`. -/
theorem fl3reg_rDer_eq_yDer_of_ext {R θ ρ : ℝ} (hR : 0 < R) {u V : ℂ → ℝ} (hρ : 0 < ρ)
    (hV : InnerProductSpace.HarmonicOnNhd V (ball (θ : ℂ) ρ))
    (hVu : ∀ z ∈ ball (θ : ℂ) ρ, 0 < z.im → V z = u (fl3Chart R z)) (hV0 : V θ = 0) :
    fl2rDer R u θ * R = yDer (u ∘ fl3Chart R) θ := by
  rw [fl2_rDer_eq (fl3reg_radial_of_ext hR hρ hV hVu hV0),
    fl3reg_yDer_of_ext (g := u ∘ fl3Chart R) hρ hV hVu hV0]
  field_simp

/-- The regularity hypothesis at `θ`: near `θ` the chart maps the upper half-disk into `Ω` and
real points to boundary points of `Ω` away from `closure A`. -/
def Fl3RegAt (R : ℝ) (Ω A : Set ℂ) (θ : ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ (∀ z ∈ ball (θ : ℂ) r, 0 < z.im → fl3Chart R z ∈ Ω) ∧
    (∀ z ∈ ball (θ : ℂ) r, z.im = 0 → fl3Chart R z ∈ frontier Ω ∧ fl3Chart R z ∉ closure A)

theorem fl3reg_polar_ext {R θ : ℝ} {Ω A : Set ℂ} {u : ℂ → ℝ} (hu : IsHarmMeas Ω A u)
    (hreg : Fl3RegAt R Ω A θ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ V : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd V (ball (θ : ℂ) ρ) ∧
      (∀ z ∈ ball (θ : ℂ) ρ, 0 < z.im → V z = u (fl3Chart R z)) ∧ V θ = 0 := by
  obtain ⟨r, hr, hΩ, hfr⟩ := hreg
  obtain ⟨ρ, hρ, -, V, hVh, hVf, hV0⟩ := fl3reg_ext hu.harm hr (fl3reg_chart_analytic R _) hΩ
    fun z hz hzi => hu.zero _ (hfr z hz hzi).1 (hfr z hz hzi).2
  exact ⟨ρ, hρ, V, hVh, hVf, hV0 _ (mem_ball_self hρ) (by simp)⟩

end FieldLawler
end QuantumZipper
