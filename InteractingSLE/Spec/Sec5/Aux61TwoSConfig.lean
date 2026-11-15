/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61TwoSReflect
import InteractingSLE.Spec.Sec5.GlueCondUnionImgBase
import InteractingSLE.Spec.Sec7.Aux57
import InteractingSLE.WangWu.ReverseContactBdry

/-!
# Aux. 61, the two new sides: the transition between the flow chart and the restart chart

Packet PROVE-AUX61-TWOSIDES, item (D1) (Astra's follow-up 4 §1.1, L113–L123). Everything is written in the
coordinates of the physical flow line mapped out at the restart time (`f_r`-coordinates): there the continuation
of the flow line is a slit `β` from `0` with driver `W`, and the restart chart is a conformal map `Ψ` of a domain
`Ω ⊇ ℍ ∩ B(0, δ)` (the collar of the old tip) onto `ℍ`, sending the continuation `β′((0, τ])` onto the chart hull
of the chart driver `w` at time `t`. The **seed** data: `Ψ → 0` at `0`, `Im Ψ → 0` at the real points of the
collar, and a logarithm `LΨ` of `Ψ′` whose imaginary part tends to `0` at `0` (the branch fixed at the initial seed).

* `IsTwoSideConfig` : this configuration (a predicate on the explicit objects);
* `xiMap` `Ξ = g_t ∘ Ψ ∘ F_σ` (time-`σ` flow coordinates → chart coordinates), `thetaMap` `Θ = f_σ ∘ Ψ⁻¹ ∘ F_t`
  (its inverse), and their logarithmic derivatives `xiLog`, `thetaLog` (`thetaLog = −xiLog ∘ Θ`, exactly);
* **`IsTwoSideConfig.exists_isPosReflect_xi`** : at every real point `p` whose boundary image `F̄_σ(p)` is a real
  point of the collar or a point `β(u)`, `0 < u < σ`, of the slit, `Ξ` is holomorphic and injective on a half-ball
  and has a positive real reflection (`Aux61TwoSReflect`); `xiLog` is a continuous logarithm of `Ξ′` there.

Deterministic; no source statement is replaced. R48/R77: nothing here uses Theorem 1.2/1.3 or the post-contact
kernel.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate Real
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd)

namespace InteractingSLE.Sec5.Aux61TwoS

open WangWu (IsProperArc)

/-- **The two-sides configuration** in the flow coordinates at the restart time. `W`, `β`: the driver and a simple
proper trace whose time-`σ` hull is the flow slit up to the comparison time; `β′`: the actual continuation up to the
chart's time (`β′ = β` on `[0, σ]`, simple on `[0, τ]`, inside `Ω`); `Ψ`: the restart chart in these coordinates,
with inverse `Ψi`, seed collar `ℍ ∩ B(0, δ) ⊆ Ω`, seed limits and the seed-normalized logarithm `LΨ` of `Ψ′`;
`w`, `γ`: the chart driver and a simple proper chart trace, whose hull at time `t` is `Ψ(β′((0, τ]))` with tip
`Ψ(β′(τ))`. -/
structure IsTwoSideConfig (W : ℝ → ℝ) (β β' : ℝ → ℂ) (σ τ : ℝ) (Ω : Set ℂ) (Ψ Ψi LΨ : ℂ → ℂ) (δ : ℝ)
    (w : ℝ → ℝ) (γ : ℝ → ℂ) (t : ℝ) : Prop where
  hW : Continuous W
  hW0 : W 0 = 0
  trace : IsLoewnerTrace W β
  arc : IsProperArc β
  σpos : 0 < σ
  σ_lt_τ : σ < τ
  cont_eqOn : EqOn β' β (Icc 0 σ)
  cont_contOn : ContinuousOn β' (Icc 0 τ)
  cont_injOn : InjOn β' (Icc 0 τ)
  cont_mapsTo : MapsTo β' (Ioc 0 τ) Ω
  isOpen_dom : IsOpen Ω
  dom_subset : Ω ⊆ H
  diff : DifferentiableOn ℂ Ψ Ω
  injOn : InjOn Ψ Ω
  mapsTo : MapsTo Ψ Ω H
  inv_contOn : ContinuousOn Ψi H
  inv_mapsTo : MapsTo Ψi H Ω
  apply_inv : ∀ y ∈ H, Ψ (Ψi y) = y
  inv_apply : ∀ z ∈ Ω, Ψi (Ψ z) = z
  δpos : 0 < δ
  collar : H ∩ ball (0 : ℂ) δ ⊆ Ω
  tendsto_zero : Tendsto Ψ (𝓝[H] 0) (𝓝 0)
  tendsto_im : ∀ ξ : ℝ, |ξ| < δ → Tendsto (fun z => (Ψ z).im) (𝓝[H] (ξ : ℂ)) (𝓝 0)
  log : IsDerivLog Ψ LΨ Ω
  log_seed : Tendsto (fun z => (LΨ z).im) (𝓝[H] 0) (𝓝 0)
  hw : Continuous w
  hw0 : w 0 = 0
  ctrace : IsLoewnerTrace w γ
  carc : IsProperArc γ
  tpos : 0 < t
  hull : fwdHull w t = Ψ '' (β' '' Ioc 0 τ)
  tip : γ t = Ψ (β' τ)

/-- `Ξ = g_t ∘ Ψ ∘ F_σ`: from the time-`σ` flow chart to the time-`t` restart chart. -/
def xiMap (w : ℝ → ℝ) (t : ℝ) (Ψ : ℂ → ℂ) (W : ℝ → ℝ) (σ : ℝ) (y : ℂ) : ℂ :=
  fwdMap w t (Ψ (fwdMapInv W σ y))

/-- The logarithmic derivative of `Ξ`, `L_t ∘ Ψ ∘ F_σ + LΨ ∘ F_σ − L_σ ∘ F_σ`. -/
def xiLog (w : ℝ → ℝ) (t : ℝ) (Ψ LΨ : ℂ → ℂ) (W : ℝ → ℝ) (σ : ℝ) (y : ℂ) : ℂ :=
  logDerivFwd w t (Ψ (fwdMapInv W σ y)) + LΨ (fwdMapInv W σ y) - logDerivFwd W σ (fwdMapInv W σ y)

/-- `Θ = f_σ ∘ Ψ⁻¹ ∘ F_t`: from the restart chart to the flow chart. -/
def thetaMap (W : ℝ → ℝ) (σ : ℝ) (Ψi : ℂ → ℂ) (w : ℝ → ℝ) (t : ℝ) (y : ℂ) : ℂ :=
  fwdMap W σ (Ψi (fwdMapInv w t y))

/-- The logarithmic derivative of `Θ`, `L_σ ∘ Ψ⁻¹ ∘ F_t − LΨ ∘ Ψ⁻¹ ∘ F_t − L_t ∘ F_t`. -/
def thetaLog (W : ℝ → ℝ) (σ : ℝ) (Ψi LΨ : ℂ → ℂ) (w : ℝ → ℝ) (t : ℝ) (y : ℂ) : ℂ :=
  logDerivFwd W σ (Ψi (fwdMapInv w t y)) - LΨ (Ψi (fwdMapInv w t y)) - logDerivFwd w t (fwdMapInv w t y)

/-- A **good boundary point** of the time-`σ` flow chart: a real point of the collar `(−δ, δ)` or a non-tip point
`β(u)`, `0 < u < σ`, of the flow slit. -/
def IsGoodPt (δ : ℝ) (β : ℝ → ℂ) (σ : ℝ) (q : ℂ) : Prop :=
  (q.im = 0 ∧ |q.re| < δ) ∨ ∃ u ∈ Ioo 0 σ, q = β u

namespace IsTwoSideConfig

variable {W : ℝ → ℝ} {β β' : ℝ → ℂ} {σ τ : ℝ} {Ω : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {δ : ℝ} {w : ℝ → ℝ}
  {γ : ℝ → ℂ} {t : ℝ}

section Basic

variable (hc : IsTwoSideConfig W β β' σ τ Ω Ψ Ψi LΨ δ w γ t)
include hc

theorem σ_nonneg : 0 ≤ σ := hc.σpos.le

theorem t_nonneg : 0 ≤ t := hc.tpos.le

/-- The time-`σ` flow hull is the slit `β((0, σ])`. -/
theorem hullσ_eq : fwdHull W σ = β '' Ioc 0 σ := WangWu.fwdHull_eq_image_Ioc hc.trace hc.arc hc.σ_nonneg

/-- A point of `Ω` off the flow hull and off the later continuation is mapped off the chart hull. -/
theorem notMem_chartHull {z : ℂ} (hzΩ : z ∈ Ω) (hz : z ∉ fwdHull W σ) (hz' : z ∉ β' '' Icc σ τ) :
    Ψ z ∉ fwdHull w t := by
  rw [hc.hull]
  rintro ⟨_, ⟨u, hu, rfl⟩, he⟩
  have hzu : β' u = z := hc.injOn (hc.cont_mapsTo hu) hzΩ he
  rcases le_or_gt u σ with huσ | huσ
  · apply hz
    rw [hc.hullσ_eq, ← hzu, hc.cont_eqOn ⟨hu.1.le, huσ⟩]
    exact ⟨u, ⟨hu.1, huσ⟩, rfl⟩
  · exact hz' ⟨u, ⟨huσ.le, hu.2⟩, hzu⟩

/-- `Ψ⁻¹ ∘ F_t` lands off the time-`σ` flow hull. -/
theorem inv_fwdMapInv_mem {y : ℂ} (hy : y ∈ H) : Ψi (fwdMapInv w t y) ∈ H \ fwdHull W σ := by
  have hF := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hc.hw hc.hw0 hc.t_nonneg hy
  have hΩ := hc.inv_mapsTo hF.1
  refine ⟨hc.dom_subset hΩ, fun hK => hF.2 ?_⟩
  rw [hc.hullσ_eq] at hK
  obtain ⟨u, hu, he⟩ := hK
  rw [← hc.apply_inv _ hF.1, ← he, ← hc.cont_eqOn ⟨hu.1.le, hu.2⟩, hc.hull]
  exact ⟨β' u, ⟨u, ⟨hu.1, hu.2.trans hc.σ_lt_τ.le⟩, rfl⟩, rfl⟩

/-- `Θ` maps `ℍ` into `ℍ`. -/
theorem thetaMap_mem {y : ℂ} (hy : y ∈ H) : thetaMap W σ Ψi w t y ∈ H :=
  QuantumZipper.FwdHolo.mapsTo_fwdMap hc.hW hc.σ_nonneg (hc.inv_fwdMapInv_mem hy)

/-- `F_σ ∘ Θ = Ψ⁻¹ ∘ F_t`. -/
theorem fwdMapInv_thetaMap {y : ℂ} (hy : y ∈ H) :
    fwdMapInv W σ (thetaMap W σ Ψi w t y) = Ψi (fwdMapInv w t y) :=
  QuantumZipper.RS.fwdMapInv_fwdMap hc.hW hc.hW0 hc.σ_nonneg (hc.inv_fwdMapInv_mem hy)

/-- `Ξ ∘ Θ = id` on `ℍ`. -/
theorem xiMap_thetaMap {y : ℂ} (hy : y ∈ H) : xiMap w t Ψ W σ (thetaMap W σ Ψi w t y) = y := by
  rw [xiMap, hc.fwdMapInv_thetaMap hy, hc.apply_inv _
    (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hc.hw hc.hw0 hc.t_nonneg hy).1]
  exact QuantumZipper.RS.fwdMap_fwdMapInv hc.hw hc.hw0 hc.t_nonneg hy

/-- `Θ ∘ Ξ = id` at points whose image under `F_σ` lies in `Ω` and is mapped off the chart hull. -/
theorem thetaMap_xiMap {y : ℂ} (hy : y ∈ H) (hΩ : fwdMapInv W σ y ∈ Ω)
    (hK : Ψ (fwdMapInv W σ y) ∉ fwdHull w t) : thetaMap W σ Ψi w t (xiMap w t Ψ W σ y) = y := by
  rw [thetaMap, xiMap, QuantumZipper.RS.fwdMapInv_fwdMap hc.hw hc.hw0 hc.t_nonneg ⟨hc.mapsTo hΩ, hK⟩,
    hc.inv_apply _ hΩ]
  exact QuantumZipper.RS.fwdMap_fwdMapInv hc.hW hc.hW0 hc.σ_nonneg hy

/-- **The two logarithms are exactly opposite**: `thetaLog = −xiLog ∘ Θ` on `ℍ` (no branch is reset). -/
theorem thetaLog_eq {y : ℂ} (hy : y ∈ H) :
    thetaLog W σ Ψi LΨ w t y = -xiLog w t Ψ LΨ W σ (thetaMap W σ Ψi w t y) := by
  rw [thetaLog, xiLog, hc.fwdMapInv_thetaMap hy, hc.apply_inv _
    (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hc.hw hc.hw0 hc.t_nonneg hy).1]
  ring

end Basic

section Reg

variable (hc : IsTwoSideConfig W β β' σ τ Ω Ψ Ψi LΨ δ w γ t)
include hc

/-- The later continuation `β′([σ, τ])` lies in `ℍ`. -/
theorem later_subset_H : β' '' Icc σ τ ⊆ H := by
  rintro _ ⟨u, hu, rfl⟩
  exact hc.dom_subset (hc.cont_mapsTo ⟨hc.σpos.trans_le hu.1, hu.2⟩)

/-- A ball about a good point: inside `Ω` (in `ℍ`), off the later continuation, and real only inside the collar. -/
theorem exists_good_ball {q : ℂ} (hq : IsGoodPt δ β σ q) :
    ∃ r₀ > 0, (∀ z ∈ ball q r₀, z ∈ H → z ∈ Ω) ∧ Disjoint (ball q r₀) (β' '' Icc σ τ) ∧
      ∀ z ∈ ball q r₀, z.im = 0 → |z.re| < δ := by
  have hcpt : IsCompact (β' '' Icc σ τ) :=
    isCompact_Icc.image_of_continuousOn (hc.cont_contOn.mono (Icc_subset_Icc_left hc.σ_nonneg))
  have hqK : q ∉ closure (β' '' Icc σ τ) := by
    rw [hcpt.isClosed.closure_eq]
    rcases hq with ⟨h0, -⟩ | ⟨u, hu, rfl⟩
    · intro hm
      have h1 : (0 : ℝ) < q.im := hc.later_subset_H hm
      linarith
    · rintro ⟨v, hv, he⟩
      rw [← hc.cont_eqOn ⟨hu.1.le, hu.2.le⟩] at he
      have := hc.cont_injOn ⟨hc.σ_nonneg.trans hv.1, hv.2⟩ ⟨hu.1.le, hu.2.le.trans hc.σ_lt_τ.le⟩ he
      linarith [hv.1, hu.2]
  obtain ⟨r₁, hr₁, hd₁⟩ := GlueImg.exists_ball_disjoint_of_notMem_closure hqK
  rcases hq with ⟨h0, hδq⟩ | ⟨u, hu, rfl⟩
  · have hqe : q = (q.re : ℂ) := Complex.ext (by simp) (by simp [h0])
    refine ⟨min r₁ (δ - |q.re|), lt_min hr₁ (by linarith), fun z hz hzH => ?_,
      hd₁.mono_left (ball_subset_ball (min_le_left _ _)), fun z hz hz0 => ?_⟩
    · refine hc.collar ⟨hzH, ?_⟩
      have h1 : dist z q < δ - |q.re| := hz.trans_le (min_le_right _ _)
      have h2 : ‖q‖ = |q.re| := by rw [hqe, Complex.norm_real, Real.norm_eq_abs, ofReal_re]
      rw [mem_ball_zero_iff]
      calc ‖z‖ ≤ ‖z - q‖ + ‖q‖ := by simpa using norm_add_le (z - q) q
        _ < δ := by rw [← dist_eq_norm, h2]; linarith
    · have h1 : dist z q < δ - |q.re| := hz.trans_le (min_le_right _ _)
      have h2 : |z.re - q.re| ≤ dist z q := by
        rw [dist_eq_norm]; simpa using abs_re_le_norm (z - q)
      have h3 := abs_sub_abs_le_abs_sub z.re q.re
      linarith
  · have hβu : β u ∈ Ω := by
      rw [← hc.cont_eqOn ⟨hu.1.le, hu.2.le⟩]
      exact hc.cont_mapsTo ⟨hu.1, hu.2.le.trans hc.σ_lt_τ.le⟩
    obtain ⟨r₂, hr₂, hsub⟩ := Metric.isOpen_iff.1 hc.isOpen_dom _ hβu
    have hpos : (0 : ℝ) < (β u).im := hc.dom_subset hβu
    refine ⟨min r₁ (min r₂ (β u).im), lt_min hr₁ (lt_min hr₂ hpos), fun z hz _ => hsub ?_,
      hd₁.mono_left (ball_subset_ball (min_le_left _ _)), fun z hz hz0 => ?_⟩
    · exact ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hz
    · exfalso
      have h1 : dist z (β u) < (β u).im := hz.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      have h2 : |z.im - (β u).im| ≤ dist z (β u) := by
        rw [dist_eq_norm]; simpa using abs_im_le_norm (z - β u)
      rw [hz0, zero_sub, abs_neg, abs_of_pos hpos] at h2
      linarith

/-- **`Ξ` has a positive real reflection at every good real point.** If `F̄_σ(p)` is a good point, then on a half-ball
about `p` the map `F_σ` lands in `Ω` and `Ψ ∘ F_σ` off the chart hull, and `Ξ` has a positive real reflection. -/
theorem exists_isPosReflect_xi {p : ℝ} (hp : IsGoodPt δ β σ (extendFrom H (fwdMapInv W σ) p)) :
    ∃ ε > 0, (∀ y ∈ H ∩ ball (p : ℂ) ε, fwdMapInv W σ y ∈ Ω ∧ Ψ (fwdMapInv W σ y) ∉ fwdHull w t) ∧
      ∃ G, IsPosReflect (xiMap w t Ψ W σ) G p ε := by
  set q := extendFrom H (fwdMapInv W σ) p with hqdef
  obtain ⟨r₀, hr₀, hΩ, hdisj, hreal⟩ := hc.exists_good_ball hp
  have hB := hc.trace.hasBdryLimits hc.hW hc.hW0 hc.σ_nonneg
  have hpH : (p : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  obtain ⟨ε, hε, hεsub⟩ : ∃ ε > 0, ∀ z ∈ Hbar, dist z p < ε →
      dist (extendFrom H (fwdMapInv W σ) z) q < r₀ :=
    Metric.continuousWithinAt_iff.1 (hB.continuousOn p hpH) r₀ hr₀
  have hE_H : ∀ y ∈ H, extendFrom H (fwdMapInv W σ) y = fwdMapInv W σ y := fun y hy =>
    WangWu.extendFrom_fwdMapInv_eq hc.hW hc.hW0 hc.σ_nonneg hy
  have hreg : ∀ y ∈ H ∩ ball (p : ℂ) ε, fwdMapInv W σ y ∈ Ω ∧ Ψ (fwdMapInv W σ y) ∉ fwdHull w t := by
    intro y hy
    have hFy := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hc.hW hc.hW0 hc.σ_nonneg hy.1
    have hb : fwdMapInv W σ y ∈ ball q r₀ := by
      rw [← hE_H y hy.1]; exact hεsub y (show (0 : ℝ) ≤ y.im from le_of_lt hy.1) hy.2
    have hΩy := hΩ _ hb hFy.1
    exact ⟨hΩy, hc.notMem_chartHull hΩy hFy.2 (Set.disjoint_left.1 hdisj hb)⟩
  refine ⟨ε, hε, hreg, ?_⟩
  apply exists_isPosReflect hε
  · intro y hy
    obtain ⟨hΩy, hKy⟩ := hreg y hy
    have h1 : DifferentiableAt ℂ (fwdMapInv W σ) y :=
      (QuantumZipper.RS.differentiableOn_fwdMapInv hc.hW hc.hW0 hc.σ_nonneg).differentiableAt
        (QuantumZipper.isOpen_H.mem_nhds hy.1)
    have h2 : DifferentiableAt ℂ Ψ (fwdMapInv W σ y) := hc.diff.differentiableAt (hc.isOpen_dom.mem_nhds hΩy)
    have h3 : DifferentiableAt ℂ (fwdMap w t) (Ψ (fwdMapInv W σ y)) :=
      (QuantumZipper.FwdHolo.differentiableOn_fwdMap hc.hw hc.t_nonneg).differentiableAt
        ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hc.hw hc.t_nonneg).mem_nhds ⟨hc.mapsTo hΩy, hKy⟩)
    exact (h3.comp y (h2.comp y h1)).differentiableWithinAt
  · intro y hy
    obtain ⟨hΩy, hKy⟩ := hreg y hy
    exact QuantumZipper.FwdHolo.mapsTo_fwdMap hc.hw hc.t_nonneg ⟨hc.mapsTo hΩy, hKy⟩
  · intro y₁ hy₁ y₂ hy₂ he
    rw [← hc.thetaMap_xiMap hy₁.1 (hreg y₁ hy₁).1 (hreg y₁ hy₁).2,
      ← hc.thetaMap_xiMap hy₂.1 (hreg y₂ hy₂).1 (hreg y₂ hy₂).2, he]
  · intro x hx
    have hxH : (x : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
    set qx := extendFrom H (fwdMapInv W σ) x with hqxdef
    have hqx : qx ∈ ball q r₀ := hεsub x hxH hx
    have hFx : Tendsto (fwdMapInv W σ) (𝓝[H] (x : ℂ)) (𝓝[H \ fwdHull W σ] qx) :=
      tendsto_nhdsWithin_iff.2 ⟨hB.tendsto hxH, eventually_nhdsWithin_of_forall fun y hy =>
        QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hc.hW hc.hW0 hc.σ_nonneg hy⟩
    have hev : ∀ᶠ y in 𝓝[H] (x : ℂ), y ∈ H ∩ ball (p : ℂ) ε :=
      inter_mem_nhdsWithin H (isOpen_ball.mem_nhds hx)
    by_cases hqx0 : qx.im = 0
    · have hδx : |qx.re| < δ := hreal qx hqx hqx0
      have hqxeq : ((qx.re : ℝ) : ℂ) = qx := Complex.ext (by simp) (by simp [hqx0])
      have h1 : Tendsto (fun y => (Ψ (fwdMapInv W σ y)).im) (𝓝[H] (x : ℂ)) (𝓝 0) := by
        have := hc.tendsto_im qx.re hδx
        rw [hqxeq] at this
        exact this.comp (hFx.mono_right (nhdsWithin_mono _ fun z hz => hz.1))
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
      · filter_upwards [hev] with y hy
        obtain ⟨hΩy, hKy⟩ := hreg y hy
        exact le_of_lt (QuantumZipper.FwdHolo.mapsTo_fwdMap hc.hw hc.t_nonneg ⟨hc.mapsTo hΩy, hKy⟩)
      · filter_upwards [hev] with y hy
        obtain ⟨hΩy, hKy⟩ := hreg y hy
        exact QuantumZipper.RS.im_fwdMap_le_im hc.hw hc.t_nonneg ⟨hc.mapsTo hΩy, hKy⟩
    · have hNB := GlueImg.nhdsWithin_H_neBot x
      have hqxcl : qx ∈ closure H := mem_closure_of_tendsto (hB.tendsto hxH)
        (eventually_nhdsWithin_of_forall fun y hy =>
          (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hc.hW hc.hW0 hc.σ_nonneg hy).1)
      have hqxH : qx ∈ H := by
        have h0 : (0 : ℝ) ≤ qx.im := by rw [closure_H] at hqxcl; exact hqxcl
        exact lt_of_le_of_ne h0 (Ne.symm hqx0)
      have hqxK : qx ∈ fwdHull W σ := by
        by_contra hn
        have hfc : ContinuousAt (fwdMap W σ) qx :=
          ((QuantumZipper.FwdHolo.differentiableOn_fwdMap hc.hW hc.σ_nonneg).differentiableAt
            ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hc.hW hc.σ_nonneg).mem_nhds ⟨hqxH, hn⟩)).continuousAt
        have h1 : Tendsto (fun y => fwdMap W σ (fwdMapInv W σ y)) (𝓝[H] (x : ℂ)) (𝓝 (fwdMap W σ qx)) :=
          hfc.tendsto.comp (hFx.mono_right nhdsWithin_le_nhds)
        have h2 : Tendsto (fun y => fwdMap W σ (fwdMapInv W σ y)) (𝓝[H] (x : ℂ)) (𝓝 (x : ℂ)) := by
          refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' ?_
          filter_upwards [self_mem_nhdsWithin] with y hy
          exact (QuantumZipper.RS.fwdMap_fwdMapInv hc.hW hc.hW0 hc.σ_nonneg hy).symm
        have h3 := tendsto_nhds_unique h1 h2
        have h4 : (0 : ℝ) < (fwdMap W σ qx).im :=
          QuantumZipper.FwdHolo.mapsTo_fwdMap hc.hW hc.σ_nonneg ⟨hqxH, hn⟩
        rw [h3] at h4
        simp at h4
      have hqxΩ : qx ∈ Ω := hΩ qx hqx hqxH
      have hΨK : Ψ qx ∈ fwdHull w t := by
        rw [hc.hullσ_eq] at hqxK
        obtain ⟨u, hu, hue⟩ := hqxK
        rw [hc.hull, ← hue, ← hc.cont_eqOn ⟨hu.1.le, hu.2⟩]
        exact ⟨_, ⟨u, ⟨hu.1, hu.2.trans hc.σ_lt_τ.le⟩, rfl⟩, rfl⟩
      have hΨc : ContinuousAt Ψ qx := (hc.diff.differentiableAt (hc.isOpen_dom.mem_nhds hqxΩ)).continuousAt
      have h1 : Tendsto (fun y => Ψ (fwdMapInv W σ y)) (𝓝[H] (x : ℂ)) (𝓝[H \ fwdHull w t] (Ψ qx)) :=
        tendsto_nhdsWithin_iff.2 ⟨hΨc.tendsto.comp (hFx.mono_right nhdsWithin_le_nhds),
          hev.mono fun y hy => ⟨hc.mapsTo (hreg y hy).1, (hreg y hy).2⟩⟩
      exact (QuantumZipper.RS.tendsto_im_fwdMap_hull hc.hw hc.t_nonneg (Or.inl hΨK)).comp h1

/-- `xiLog` is continuous where `F_σ` lands in `Ω` and `Ψ ∘ F_σ` off the chart hull. -/
theorem continuousOn_xiLog {S : Set ℂ} (hS : S ⊆ H)
    (hreg : ∀ y ∈ S, fwdMapInv W σ y ∈ Ω ∧ Ψ (fwdMapInv W σ y) ∉ fwdHull w t) :
    ContinuousOn (xiLog w t Ψ LΨ W σ) S := by
  intro y hy
  obtain ⟨hΩy, hKy⟩ := hreg y hy
  have hFK := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hc.hW hc.hW0 hc.σ_nonneg (hS hy)
  have hFc : ContinuousAt (fwdMapInv W σ) y :=
    ((QuantumZipper.RS.differentiableOn_fwdMapInv hc.hW hc.hW0 hc.σ_nonneg).differentiableAt
      (QuantumZipper.isOpen_H.mem_nhds (hS hy))).continuousAt
  have hΨc : ContinuousAt Ψ (fwdMapInv W σ y) :=
    (hc.diff.differentiableAt (hc.isOpen_dom.mem_nhds hΩy)).continuousAt
  have hLc : ContinuousAt LΨ (fwdMapInv W σ y) :=
    (hc.log.1.differentiableAt (hc.isOpen_dom.mem_nhds hΩy)).continuousAt
  have h1 : ContinuousAt (fun y => logDerivFwd w t (Ψ (fwdMapInv W σ y))) y :=
    (continuousAt_logDerivFwd hc.hw hc.t_nonneg ⟨hc.mapsTo hΩy, hKy⟩).comp
      (f := fun y => Ψ (fwdMapInv W σ y)) (hΨc.comp hFc)
  have h2 : ContinuousAt (fun y => LΨ (fwdMapInv W σ y)) y := hLc.comp hFc
  have h3 : ContinuousAt (fun y => logDerivFwd W σ (fwdMapInv W σ y)) y :=
    (continuousAt_logDerivFwd hc.hW hc.σ_nonneg hFK).comp hFc
  exact ((h1.add h2).sub h3).continuousWithinAt

/-- **The chain rule**: `exp ∘ xiLog = Ξ′` where `F_σ` lands in `Ω` and `Ψ ∘ F_σ` off the chart hull. -/
theorem exp_xiLog {y : ℂ} (hy : y ∈ H) (hΩy : fwdMapInv W σ y ∈ Ω) (hKy : Ψ (fwdMapInv W σ y) ∉ fwdHull w t) :
    exp (xiLog w t Ψ LΨ W σ y) = deriv (xiMap w t Ψ W σ) y := by
  set ζ := fwdMapInv W σ y with hζdef
  have hζK := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hc.hW hc.hW0 hc.σ_nonneg hy
  have hΨK : Ψ ζ ∈ H \ fwdHull w t := ⟨hc.mapsTo hΩy, hKy⟩
  have e1 := (isDerivLog_fwdMap hc.hw hc.t_nonneg).2 (Ψ ζ) hΨK
  have e2 := hc.log.2 ζ hΩy
  have e3 := (isDerivLog_fwdMap hc.hW hc.σ_nonneg).2 ζ hζK
  have hfσ : HasDerivAt (fwdMap W σ) (deriv (fwdMap W σ) ζ) ζ :=
    ((QuantumZipper.FwdHolo.differentiableOn_fwdMap hc.hW hc.σ_nonneg _ hζK).differentiableAt
      ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hc.hW hc.σ_nonneg).mem_nhds hζK)).hasDerivAt
  have hF : HasDerivAt (fwdMapInv W σ) (deriv (fwdMap W σ) ζ)⁻¹ y := by
    refine HasDerivAt.of_local_left_inverse ?_ hfσ (by rw [← e3]; exact exp_ne_zero _) ?_
    · exact ((QuantumZipper.RS.differentiableOn_fwdMapInv hc.hW hc.hW0 hc.σ_nonneg).differentiableAt
        (QuantumZipper.isOpen_H.mem_nhds hy)).continuousAt
    · filter_upwards [QuantumZipper.isOpen_H.mem_nhds hy] with y' hy'
      exact QuantumZipper.RS.fwdMap_fwdMapInv hc.hW hc.hW0 hc.σ_nonneg hy'
  have hΨd : HasDerivAt Ψ (deriv Ψ ζ) ζ :=
    (hc.diff.differentiableAt (hc.isOpen_dom.mem_nhds hΩy)).hasDerivAt
  have hgd : HasDerivAt (fwdMap w t) (deriv (fwdMap w t) (Ψ ζ)) (Ψ ζ) :=
    ((QuantumZipper.FwdHolo.differentiableOn_fwdMap hc.hw hc.t_nonneg _ hΨK).differentiableAt
      ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hc.hw hc.t_nonneg).mem_nhds hΨK)).hasDerivAt
  have hΞ : HasDerivAt (xiMap w t Ψ W σ)
      (deriv (fwdMap w t) (Ψ ζ) * (deriv Ψ ζ * (deriv (fwdMap W σ) ζ)⁻¹)) y :=
    HasDerivAt.comp (h₂ := fwdMap w t) (h := Ψ ∘ fwdMapInv W σ) y hgd (HasDerivAt.comp y hΨd hF)
  rw [hΞ.deriv, xiLog, exp_sub, exp_add, e1, e2, e3]
  field_simp

end Reg

end IsTwoSideConfig

end InteractingSLE.Sec5.Aux61TwoS
