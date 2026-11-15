/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5LfOuter
import InteractingSLE.Spec.Supplement.R1RefFreshTip
import InteractingSLE.Spec.ZhanGT4.RealTip
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Lemma R.5's common phase: the side agreement at the current time from a fresh tip

Packet PROVE-R5-LIFT2 (second round). The side clauses of `R5Lift.R7LiftCurGeom` and `R5Lift.R7OuterLiftGeom` ("the
side of a current coordinate is the side of its ambient image at `T = T⁰(q)`") are proved from the reflection of the
current transition `S = f_T ∘ cur⁻¹` along the open seed interval and a fresh current tip:

* **`reflect_orient`**: a reflecting map increases along the real axis at the centre (positive reflected derivative);
* **`side_of_tip`**: if every real point of `(a, b) ∋ 0` lands in `K_T` and `S → 0` at `0`, then at every `u ∈ (a, b)`
  every real limit `y` of `S` satisfies `u < 0 ↔ y < 0` (the boundary map is continuous and injective — two reflected
  half-discs with a common image point contradict the injectivity of `S` — and increasing at `0`; intermediate values);
* **`tendsto_tip_eq_zero`**: at a positive cut time `T` (`YuanSimpleApprox.IsCutTime`), if `cur⁻¹ → η(T)` at `0`, every
  real limit of `S` at `0` is `0` (Lemma 1.1 of the singleton-tip elimination note,
  `IsLoewnerTrace.eq_zero_of_extendFrom_eq_of_isCutTime`);
* `R7LiftCurTip(Inf)`, `R7OuterRefl(Inf)` (defs, **named pathwise inputs**), **`ae_curSide(Inf)_of_tip`**,
  **`r7LiftCurGeom(Inf)_of_tip`**, **`r7OuterLiftGeom(Inf)_of_tip`**: the side clauses of `R7LiftCurGeom(Inf)` and
  `R7OuterLiftGeom(Inf)` are proved from a fresh current tip (`T⁰(q)` a positive cut time, the current inverse landing
  at `η(T⁰(q))` from the driver `0`, and `0` in the open seed interval).

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd chiC isOpen_H)
open scoped ComplexConjugate NNReal ENNReal

namespace InteractingSLE.Sec7.R5Lift

/-- **A reflecting map increases along the real axis at the centre.** -/
theorem reflect_orient {g : ℂ → ℂ} {x r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ g (H ∩ ball (x : ℂ) r)) (hc : ContinuousOn g (Hbar ∩ ball (x : ℂ) r))
    (hreal : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → (g z).im = 0) (hmaps : ∀ z ∈ H ∩ ball (x : ℂ) r, g z ∈ H)
    (hinj : InjOn g (H ∩ ball (x : ℂ) r)) :
    (∀ᶠ v : ℝ in 𝓝[<] x, (g v).re < (g x).re) ∧ ∀ᶠ v : ℝ in 𝓝[>] x, (g x).re < (g v).re := by
  obtain ⟨b, hb, hder⟩ := exists_pos_tendsto_deriv_of_reflect' hr hd hc hreal hmaps hinj
  obtain ⟨G, hG, hGg, -⟩ := QuantumZipper.CA.exists_reflection_extension hd hc hreal
  have hxB : (x : ℂ) ∈ ball (x : ℂ) r := mem_ball_self hr
  have hHB : H ∩ ball (x : ℂ) r ⊆ Hbar ∩ ball (x : ℂ) r :=
    inter_subset_inter_left _ fun z (hz : 0 < z.im) => (le_of_lt hz : 0 ≤ z.im)
  have hGder : deriv G x = (b : ℂ) := by
    have hcontd : ContinuousAt (deriv G) x :=
      ((hG.deriv isOpen_ball).continuousOn).continuousAt (isOpen_ball.mem_nhds hxB)
    have h1 : Tendsto (deriv G) (𝓝[H] (x : ℂ)) (𝓝 (b : ℂ)) := by
      refine hder.congr' ?_
      filter_upwards [inter_mem_nhdsWithin H (isOpen_ball.mem_nhds hxB)] with y hy
      exact (Filter.eventuallyEq_of_mem ((isOpen_H.inter isOpen_ball).mem_nhds hy)
        fun z hz => (hGg (hHB hz)).symm).deriv_eq
    have := nhdsWithin_H_neBot x
    exact tendsto_nhds_unique (hcontd.tendsto.mono_left nhdsWithin_le_nhds) h1
  have hGx : HasDerivAt G (b : ℂ) (x : ℂ) := by
    rw [← hGder]; exact (hG.differentiableAt (isOpen_ball.mem_nhds hxB)).hasDerivAt
  have hφ := hGx.real_of_complex
  rw [ofReal_re] at hφ
  have hslope := hasDerivAt_iff_tendsto_slope.1 hφ
  have hpos : ∀ᶠ v in 𝓝[≠] x, 0 < slope (fun v : ℝ => (G v).re) x v := hslope.eventually (Ioi_mem_nhds hb)
  -- near `x`, `G = g` on the real axis
  have hnear : ∀ᶠ v : ℝ in 𝓝 x, (G v).re = (g v).re := by
    have hc' : Continuous fun v : ℝ => (v : ℂ) := continuous_ofReal
    filter_upwards [hc'.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds hxB)] with v hv
    rw [hGg ⟨show (0 : ℝ) ≤ (v : ℂ).im by rw [ofReal_im], hv⟩]
  have hGxg : (G x).re = (g x).re := by
    rw [hGg ⟨show (0 : ℝ) ≤ (x : ℂ).im by rw [ofReal_im], hxB⟩]
  constructor
  · filter_upwards [hpos.filter_mono (nhdsWithin_mono _ fun v (hv : v < x) => ne_of_lt hv),
      hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with v hv hvG (hvx : v < x)
    rw [slope_def_field] at hv
    rw [← hvG, ← hGxg]
    rcases div_pos_iff.1 hv with ⟨-, h2⟩ | ⟨h1, -⟩
    · linarith
    · linarith
  · filter_upwards [hpos.filter_mono (nhdsWithin_mono _ fun v (hv : x < v) => ne_of_gt hv),
      hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with v hv hvG (hvx : x < v)
    rw [slope_def_field] at hv
    rw [← hvG, ← hGxg]
    rcases div_pos_iff.1 hv with ⟨h1, -⟩ | ⟨-, h2⟩
    · linarith
    · linarith

/-- **The fresh-tip anchor**: at a positive cut time `T`, if the current inverse tends to the tip `η(T)` at the
coordinate `0`, every real limit of `f_T ∘ cur⁻¹` at `0` is `0`. -/
theorem tendsto_tip_eq_zero {cur : Chart} (hcur : cur.IsConformal) {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T)
    (hcut : YuanSimpleApprox.IsCutTime η T) (hK : (cur.dom : Set ℂ) ⊆ H \ fwdHull W T)
    (htip : Tendsto cur.2.1 (𝓝[H] ((0 : ℝ) : ℂ)) (𝓝 (η T))) {y₀ : ℝ}
    (hy : Tendsto (fun z => fwdMap W T (cur.2.1 z)) (𝓝[H] ((0 : ℝ) : ℂ)) (𝓝 (y₀ : ℂ))) : y₀ = 0 := by
  have hB := ZhanGT4.isBoundaryMap_extendFrom hη hW hW0 hT.le
  have hy0bar : (y₀ : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (y₀ : ℂ).im by rw [ofReal_im]
  have hF : Tendsto (extendFrom H (fwdMapInv W T)) (𝓝[H] (y₀ : ℂ))
      (𝓝 (extendFrom H (fwdMapInv W T) (y₀ : ℂ))) :=
    ((hB.1 _ hy0bar).mono QuantumZipper.H_subset_Hbar).tendsto
  have hyH : Tendsto (fun z => fwdMap W T (cur.2.1 z)) (𝓝[H] ((0 : ℝ) : ℂ)) (𝓝[H] (y₀ : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hy, eventually_nhdsWithin_of_forall fun z hz =>
      QuantumZipper.FwdHolo.mapsTo_fwdMap hW hT.le (hK (hcur.inv_mem_dom hz))⟩
  have h2 : Tendsto cur.2.1 (𝓝[H] ((0 : ℝ) : ℂ)) (𝓝 (extendFrom H (fwdMapInv W T) (y₀ : ℂ))) := by
    refine (hF.comp hyH).congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
    have hm := hK (hcur.inv_mem_dom hz)
    simp only [Function.comp_apply]
    rw [ZhanGT4.extendFrom_eq_fwdMapInv hW hW0 hT.le (QuantumZipper.FwdHolo.mapsTo_fwdMap hW hT.le hm),
      QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hT.le hm]
  have := nhdsWithin_H_neBot 0
  exact hη.eq_zero_of_extendFrom_eq_of_isCutTime hW hW0 hT hcut (tendsto_nhds_unique h2 htip)

/-- **The side agreement on an interval of hull landings with an anchored driver.** Let every real point of
`(a, b) ∋ 0` land (under the current chart, `cur.dom ⊆ ℍ ∖ K_T`) in `K_T`, and let every real limit of
`S = f_T ∘ cur⁻¹` at `0` be `0`. Then at every `u ∈ (a, b)`, every real limit `y` of `S` at `u` satisfies
`u < 0 ↔ y < 0`. -/
theorem side_of_tip {cur : Chart} (hcur : cur.IsConformal) {Fc : ℂ → ℂ} (hFc : EqOn Fc cur.2.1 H)
    (hFcc : ContinuousOn Fc Hbar) {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) (hK : (cur.dom : Set ℂ) ⊆ H \ fwdHull W T) {a b : ℝ}
    (hland : ∀ u ∈ Ioo a b, Fc u ∈ fwdHull W T) (h0 : (0 : ℝ) ∈ Ioo a b)
    (htip : ∀ y : ℝ, Tendsto (fun z => fwdMap W T (cur.2.1 z)) (𝓝[H] ((0 : ℝ) : ℂ)) (𝓝 (y : ℂ)) → y = 0) :
    ∀ u ∈ Ioo a b, ∀ y : ℝ, Tendsto (fun z => fwdMap W T (cur.2.1 z)) (𝓝[H] (u : ℂ)) (𝓝 (y : ℂ)) →
      (u < 0 ↔ y < 0) := by
  set S : ℂ → ℂ := fun z => fwdMap W T (cur.2.1 z) with hS
  set g := extendFrom H S with hg
  have hlandB : ∀ u ∈ Ioo a b, ∃ ρ > 0, ∀ v : ℝ, (v : ℂ) ∈ ball (u : ℂ) ρ → Fc v ∈ fwdHull W T := by
    intro u hu
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 isOpen_Ioo u hu
    exact ⟨ρ, hρ, fun v hv => hland v (hball (mem_ball_of_ofReal_mem_ball hv))⟩
  -- boundary limits, real values
  have hdat : ∀ u ∈ Ioo a b, Tendsto S (𝓝[H] (u : ℂ)) (𝓝 (g u)) ∧ (g u).im = 0 := by
    intro u hu
    obtain ⟨ρ, hρ, hl⟩ := hlandB u hu
    obtain ⟨-, -, hgr, -, -, -, hgl⟩ := reflect_data_of_hull_landing (x := u) (ρ := ρ) hcur hFc hFcc hη hW hW0 hT hK hl
    have hubar : (u : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (u : ℂ).im by rw [ofReal_im]
    exact ⟨hgl u ⟨hubar, mem_ball_self hρ⟩, hgr u (mem_ball_self hρ) (ofReal_im u)⟩
  set φ : ℝ → ℝ := fun v => (g v).re with hφ
  have hgu : ∀ u ∈ Ioo a b, g u = (φ u : ℂ) := fun u hu =>
    Complex.ext (by rw [ofReal_re]) (by rw [ofReal_im]; exact (hdat u hu).2)
  have hφc : ContinuousOn φ (Ioo a b) :=
    continuousOn_of_tendsto_nhdsWithin_H (f := fun z => (S z).re) fun u hu =>
      (continuous_re.tendsto _).comp (hdat u hu).1
  -- injectivity of the boundary map
  have hSinj : InjOn S H := fun z₁ hz₁ z₂ hz₂ h => by
    have h' := congrArg (fwdMapInv W T) h
    simp only [hS] at h'
    rw [QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hT (hK (hcur.inv_mem_dom hz₁)),
      QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hT (hK (hcur.inv_mem_dom hz₂))] at h'
    exact hcur.injOn hz₁ hz₂ h'
  have hinjφ : ∀ u₁ ∈ Ioo a b, ∀ u₂ ∈ Ioo a b, φ u₁ = φ u₂ → u₁ = u₂ := by
    intro u₁ hu₁ u₂ hu₂ heq
    by_contra hne
    have hd0 : 0 < |u₁ - u₂| := abs_pos.2 (sub_ne_zero.2 hne)
    set δ := |u₁ - u₂| / 2 with hδ
    have hδ0 : 0 < δ := by positivity
    obtain ⟨ρ₁, hρ₁, hl₁⟩ := hlandB u₁ hu₁
    obtain ⟨ρ₂, hρ₂, hl₂⟩ := hlandB u₂ hu₂
    obtain ⟨hgΦ₁, hgc₁, hgr₁, hm₁, hi₁, hgd₁, -⟩ := reflect_data_of_hull_landing (x := u₁) (ρ := min ρ₁ δ) hcur hFc
      hFcc hη hW hW0 hT hK fun v hv => hl₁ v (ball_subset_ball (min_le_left _ _) hv)
    obtain ⟨hgΦ₂, hgc₂, hgr₂, hm₂, hi₂, hgd₂, -⟩ := reflect_data_of_hull_landing (x := u₂) (ρ := min ρ₂ δ) hcur hFc
      hFcc hη hW hW0 hT hK fun v hv => hl₂ v (ball_subset_ball (min_le_left _ _) hv)
    obtain ⟨ρ'₁, hρ'₁, hs₁⟩ := exists_halfBall_subset_image_of_reflect (lt_min hρ₁ hδ0) hgd₁ hgc₁ hgr₁ hm₁ hi₁
    obtain ⟨ρ'₂, hρ'₂, hs₂⟩ := exists_halfBall_subset_image_of_reflect (lt_min hρ₂ hδ0) hgd₂ hgc₂ hgr₂ hm₂ hi₂
    have hg12 : g u₁ = g u₂ := by rw [hgu u₁ hu₁, hgu u₂ hu₂, heq]
    set ε := min ρ'₁ ρ'₂ / 2 with hε
    have hε0 : 0 < ε := by positivity
    set w : ℂ := g u₁ + (ε : ℂ) * I with hw
    have hwH : w ∈ H := show 0 < w.im by
      simp only [hw, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero, mul_one, zero_add, add_zero,
        (hdat u₁ hu₁).2]
      exact hε0
    have hdist : dist w (g u₁) = ε := by
      rw [hw, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hε0.le]
    obtain ⟨z₁, hz₁, hzw₁⟩ := hs₁ ⟨hwH, by
      rw [mem_ball, hdist]; linarith [min_le_left ρ'₁ ρ'₂]⟩
    obtain ⟨z₂, hz₂, hzw₂⟩ := hs₂ ⟨hwH, by
      show dist w (g u₂) < ρ'₂
      rw [← hg12, hdist]; linarith [min_le_right ρ'₁ ρ'₂]⟩
    have hSz : S z₁ = S z₂ :=
      calc S z₁ = g z₁ := hgΦ₁ hz₁
        _ = w := hzw₁
        _ = g z₂ := hzw₂.symm
        _ = S z₂ := (hgΦ₂ hz₂).symm
    have hz := hSinj hz₁.1 hz₂.1 hSz
    have h1 : dist z₁ (u₁ : ℂ) < δ := lt_of_lt_of_le (mem_ball.1 hz₁.2) (min_le_right _ _)
    have h2 : dist z₂ (u₂ : ℂ) < δ := lt_of_lt_of_le (mem_ball.1 hz₂.2) (min_le_right _ _)
    have h12 : dist (u₁ : ℂ) (u₂ : ℂ) = |u₁ - u₂| := by
      rw [Complex.dist_eq, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have htri := dist_triangle (u₁ : ℂ) z₁ (u₂ : ℂ)
    rw [hz, dist_comm (u₁ : ℂ) z₂] at htri
    rw [hz] at h1
    linarith [dist_comm z₂ (u₁ : ℂ)]
  -- orientation at `0`
  have hφ0 : φ 0 = 0 := htip (φ 0) (by rw [← hgu 0 h0]; exact (hdat 0 h0).1)
  obtain ⟨ρ₀, hρ₀, hl₀⟩ := hlandB 0 h0
  obtain ⟨-, hgc₀, hgr₀, hm₀, hi₀, hgd₀, -⟩ := reflect_data_of_hull_landing (x := 0) (ρ := ρ₀) hcur hFc hFcc hη hW
    hW0 hT hK hl₀
  obtain ⟨hleft, hright⟩ := reflect_orient hρ₀ hgd₀ hgc₀ hgr₀ hm₀ hi₀
  intro u hu y hy
  have hyφ : y = φ u := by
    have := nhdsWithin_H_neBot u
    have h := (tendsto_nhds_unique hy (hdat u hu).1).trans (hgu u hu)
    exact_mod_cast h
  rw [hyφ]
  constructor
  · intro hu0
    by_contra hge
    push Not at hge
    have hne : φ u ≠ 0 := fun h => (ne_of_lt hu0) (hinjφ u hu 0 h0 (h.trans hφ0.symm))
    have hpos : 0 < φ u := lt_of_le_of_ne hge (Ne.symm hne)
    obtain ⟨v, hv, huv⟩ := (hleft.and (Ioo_mem_nhdsLT hu0)).exists
    have hv' : φ v < 0 := by rw [← hφ0]; exact hv
    have hsub : Icc u v ⊆ Ioo a b := fun t ht => ⟨lt_of_lt_of_le hu.1 ht.1, lt_of_le_of_lt ht.2 (huv.2.trans h0.2)⟩
    obtain ⟨t, ht, ht0⟩ := intermediate_value_Icc' huv.1.le (hφc.mono hsub) ⟨hv'.le, hpos.le⟩
    have := hinjφ t (hsub ht) 0 h0 (ht0.trans hφ0.symm)
    linarith [ht.2, huv.2]
  · intro hφu
    by_contra hge
    push Not at hge
    rcases hge.eq_or_lt with h | h
    · rw [← h, hφ0] at hφu
      exact lt_irrefl _ hφu
    · obtain ⟨v, hv, huv⟩ := (hright.and (Ioo_mem_nhdsGT h)).exists
      have hv' : 0 < φ v := by rw [← hφ0]; exact hv
      have hsub : Icc v u ⊆ Ioo a b := fun t ht => ⟨lt_of_lt_of_le (h0.1.trans huv.1) ht.1, lt_of_le_of_lt ht.2 hu.2⟩
      obtain ⟨t, ht, ht0⟩ := intermediate_value_Icc' huv.2.le (hφc.mono hsub) ⟨hφu.le, hv'.le⟩
      have := hinjφ t (hsub ht) 0 h0 (ht0.trans hφ0.symm)
      linarith [ht.1, huv.1]

section Bounded

open LocalSets PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling PocketStopSide PhaseSel
  PocketWordAssembly PocketSeedOpen PocketCoord PocketJordan R5Phase R5Same R5Ref MartChar.RealFlow
open Wire.Current.SideTest (rationalOriginalTime)

variable {Ω : Type*} [MeasurableSpace Ω] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
  {A : Set Ω}

/-- **The current chart with a fresh tip** (bounded change pocket; named pathwise input): almost surely on the live
test, every coordinate of the current open seed interval lands in `ℍ`, the interval contains the driver `0`, the left
stop `T = T⁰(q)` is a positive cut time of the counterflow (`η(T) ∉ η([0, T))`), and the current inverse tends to the
tip `η(T)` at `0`. -/
def R7LiftCurTip {nL nR : ℕ} (P : Measure Ω) (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0)
    (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart)
    (q : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) →
    (∀ u ∈ Ioo (geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL 0 q ω - segDriver (travAll R L r η ψ ω) q)
        (geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR 0 q ω - segDriver (travAll R L r η ψ ω) q),
      extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 u ∈ H) ∧
    (0 : ℝ) ∈ Ioo (geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL 0 q ω - segDriver (travAll R L r η ψ ω) q)
        (geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR 0 q ω - segDriver (travAll R L r η ψ ω) q) ∧
    0 < leftStop R L r η ψ q ω ∧ YuanSimpleApprox.IsCutTime (η ω) (leftStop R L r η ψ q ω) ∧
    Tendsto (relChart c (travAll R L r η ψ) q ω).2.1 (𝓝[H] ((0 : ℝ) : ℂ)) (𝓝 (η ω (leftStop R L r η ψ q ω)))

/-- **The side agreement at the current time from a fresh tip** (bounded change pocket): under `R7LiftCurTip`, almost
surely on the live test, at every coordinate `u` of the current open seed interval every real limit `y` of
`f_T ∘ cur⁻¹` satisfies `u < 0 ↔ y < 0`. -/
theorem ae_curSide_of_tip {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ} {xR : Ω → Fin (0 + 1) → ℝ}
    {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0) (h : R7LiftCurTip P A R L r η ψ xL xR c q) :
    ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) →
      ∀ u ∈ Ioo (geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL 0 q ω - segDriver (travAll R L r η ψ ω) q)
        (geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR 0 q ω - segDriver (travAll R L r η ψ ω) q), ∀ y : ℝ,
        Tendsto (fun z => fwdMap (fun t : ℝ => W' t.toNNReal ω) (leftStop R L r η ψ q ω)
          ((relChart c (travAll R L r η ψ) q ω).2.1 z)) (𝓝[H] (u : ℂ)) (𝓝 (y : ℂ)) → (u < 0 ↔ y < 0) := by
  filter_upwards [h] with ω hω hA hlive
  obtain ⟨hN1, h0, hT0, hcut, htipl⟩ := hω hA hlive
  have hγ := ((hcfg ω hA).isDrivenCurve (hψ ω hA)).1
  have hq0 : 0 < q := by
    rcases (show (0 : ℝ≥0) ≤ q from zero_le).eq_or_lt with h0q | h0q
    · exfalso
      subst h0q
      rw [seed_interval_eq_empty_zero (c := c) (hxL ω) (hxR ω) hγ hlive] at h0
      exact h0
    · exact h0q
  have hT := hT0.le
  have hd : ((relChart c (travAll R L r η ψ) q ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r ∩
      (H \ fwdHull (fun t : ℝ => W' t.toNNReal ω) (leftStop R L r η ψ q ω)) := by
    rw [current_dom_eq (W := fun ω (s : ℝ) => W' s.toNNReal ω) hA (hcfg ω hA) (hψ ω hA) (hc ω hA) (hdom ω hA)
        (heq ω hA) hlive, ← (hcfg ω hA).trace.2.2 _ hT]
  have hK : ((relChart c (travAll R L r η ψ) q ω).dom : Set ℂ) ⊆
      H \ fwdHull (fun t : ℝ => W' t.toNNReal ω) (leftStop R L r η ψ q ω) := by
    rw [hd]; exact inter_subset_right
  obtain ⟨E, hE, hEc, -⟩ := exists_inverse_extension_of_jordan_cases
    (jordan_of_cfg (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA) (hψ ω hA))
    (hc ω hA) (hdom ω hA) (heq ω hA)
  obtain ⟨Fc, hFc, hFcc, -⟩ :=
    exists_relative_inverse_extension (c := c) (γ := travAll R L r η ψ) hγ hlive hE hEc
  have hcur := isConformal_relChart_of_driven (c := c) hγ hlive (hc ω hA)
  refine side_of_tip hcur hFc hFcc (hcfg ω hA).trace (hcfg ω hA).continuous_W (hcfg ω hA).W_zero hT hK
    (fun u hu => ?_) h0 fun y hy => tendsto_tip_eq_zero hcur (hcfg ω hA).trace (hcfg ω hA).continuous_W
      (hcfg ω hA).W_zero hT0 hcut hK htipl hy
  obtain ⟨hlim, hFu⟩ := tendsto_of_ext hFc hFcc u
  refine landing_mem_hull_of_mem_seed_interval (hxL ω) (hxR ω) (hc ω hA) hγ hlive hq0 hE hEc (hdom ω hA)
    (QuantumZipper.FwdHolo.isOpen_compl_fwdHull (hcfg ω hA).continuous_W hT) hd hu hlim ?_
  rw [hFu]; exact hN1 u hu

/-- **`R5Lift.R7LiftCurGeom` from a fresh current tip** (bounded change pocket). -/
theorem r7LiftCurGeom_of_tip {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ} {xR : Ω → Fin (0 + 1) → ℝ}
    {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0) (h : R7LiftCurTip P A R L r η ψ xL xR c q) :
    R7LiftCurGeom P A R L r η ψ xL xR c W' q := by
  filter_upwards [h, ae_curSide_of_tip (W' := W') hcfg hψ hc hdom heq hxL hxR h] with ω hω hs hA hlive u hu
  exact ⟨(hω hA hlive).1 u hu, fun _ => hs hA hlive u hu⟩

/-- **The outer collars' `K_s`-landing** (bounded change pocket; named pathwise input): the second clause of
`R5Lift.R7OuterLiftGeom` alone. -/
def R7OuterRefl {nL nR : ℕ} (P : Measure Ω) (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0)
    (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart)
    (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (X : Ω → Set ℂ) (q : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) → ∀ ξ : ℝ, ξ ∉ forceJumpSet
      (fun i => geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL i q ω - segDriver (travAll R L r η ψ ω) q)
      (fun j => geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR j q ω -
        segDriver (travAll R L r η ψ ω) q) →
    extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∉ X ω →
    R5Wall.exposedOuterSel c (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) xL xR q ω ξ →
    ∀ (i : ℕ) (x ε : ℝ),
      ω ∈ refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i →
      η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r →
      IsRefCollar (refChart c R L r η ψ i ω) (relChart c (travAll R L r η ψ) q ω) ξ
        (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ) x ε →
      extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈ refHull W' ζ' i ω →
      ∃ ρ > 0, ∀ u : ℝ, (u : ℂ) ∈ ball (x : ℂ) ρ →
        extendFrom H (refChart c R L r η ψ i ω).2.1 u ∈
          fwdHull (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)

/-- **`R5Lift.R7OuterLiftGeom` from a fresh current tip and the outer collars' `K_s`-landing** (bounded change
pocket). -/
theorem r7OuterLiftGeom_of_tip {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ} {xR : Ω → Fin (0 + 1) → ℝ}
    {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {X : Ω → Set ℂ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0) (h : R7LiftCurTip P A R L r η ψ xL xR c q)
    (ho : R7OuterRefl P A R L r η ψ xL xR c W' ζ' X q) :
    R7OuterLiftGeom P A R L r η ψ xL xR c W' ζ' X q := by
  filter_upwards [ho, ae_curSide_of_tip (W' := W') hcfg hψ hc hdom heq hxL hxR h] with ω hω hs hA hlive ξ hξ hX hsel
  exact ⟨fun y hy => hs hA hlive ξ (not_not.1 hsel.1) y hy, hω hA hlive ξ hξ hX hsel⟩

end Bounded

section SeedOpen

open LocalSets PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling PocketStopSide PhaseSel
  PocketWordAssembly PocketSeedOpen PocketCoord PocketJordan R5Phase R5Same R5Ref MartChar.RealFlow
open Wire.Current.SideTest (rationalOriginalTime)

variable {Ω : Type*} [MeasurableSpace Ω] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
  {A : Set Ω}

/-- **The current chart with a fresh tip** (pocket opening at the flow seed; named pathwise input): almost surely on the
live test, every coordinate of the current open seed interval lands in `ℍ`, the interval contains the driver `0`, the
left stop `T = T⁰(q)` is a positive cut time of the counterflow (`η(T) ∉ η([0, T))`), and the current inverse tends to
the tip `η(T)` at `0`. -/
def R7LiftCurTipInf {nL nR : ℕ} (P : Measure Ω) (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0)
    (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart)
    (q : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) →
    (∀ u ∈ Ioo (geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL 0 q ω -
        segDriver (travAllInf R L r η ψ ω) q)
        (geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR 0 q ω - segDriver (travAllInf R L r η ψ ω) q),
      extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 u ∈ H) ∧
    (0 : ℝ) ∈ Ioo (geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL 0 q ω -
        segDriver (travAllInf R L r η ψ ω) q)
        (geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR 0 q ω - segDriver (travAllInf R L r η ψ ω) q) ∧
    0 < leftStopInf R L r η ψ q ω ∧ YuanSimpleApprox.IsCutTime (η ω) (leftStopInf R L r η ψ q ω) ∧
    Tendsto (relChart c (travAllInf R L r η ψ) q ω).2.1 (𝓝[H] ((0 : ℝ) : ℂ)) (𝓝 (η ω (leftStopInf R L r η ψ q ω)))

/-- **The side agreement at the current time from a fresh tip** (pocket opening at the flow seed): under
`R7LiftCurTipInf`, almost surely on the live test, at every coordinate `u` of the current open seed interval every real
limit `y` of `f_T ∘ cur⁻¹` satisfies `u < 0 ↔ y < 0`. -/
theorem ae_curSideInf_of_tip {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ} {xR : Ω → Fin (0 + 1) → ℝ}
    {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0) (h : R7LiftCurTipInf P A R L r η ψ xL xR c q) :
    ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) →
      ∀ u ∈ Ioo (geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL 0 q ω -
          segDriver (travAllInf R L r η ψ ω) q)
        (geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR 0 q ω -
            segDriver (travAllInf R L r η ψ ω) q), ∀ y : ℝ,
        Tendsto (fun z => fwdMap (fun t : ℝ => W' t.toNNReal ω) (leftStopInf R L r η ψ q ω)
          ((relChart c (travAllInf R L r η ψ) q ω).2.1 z)) (𝓝[H] (u : ℂ)) (𝓝 (y : ℂ)) → (u < 0 ↔ y < 0) := by
  filter_upwards [h] with ω hω hA hlive
  obtain ⟨hN1, h0, hT0, hcut, htipl⟩ := hω hA hlive
  have hγ := ((hcfg ω hA).isDrivenCurve (hψ ω hA)).1
  have hq0 : 0 < q := by
    rcases (show (0 : ℝ≥0) ≤ q from zero_le).eq_or_lt with h0q | h0q
    · exfalso
      subst h0q
      rw [seed_interval_eq_empty_zero (c := c) (hxL ω) (hxR ω) hγ hlive] at h0
      exact h0
    · exact h0q
  have hT := hT0.le
  have hd : ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r ∩
      (H \ fwdHull (fun t : ℝ => W' t.toNNReal ω) (leftStopInf R L r η ψ q ω)) := by
    rw [current_dom_eqInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hA (hcfg ω hA) (hψ ω hA) (hc ω hA) (hdom ω hA)
        (heq ω hA) hlive, ← (hcfg ω hA).trace.2.2 _ hT]
  have hK : ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) ⊆
      H \ fwdHull (fun t : ℝ => W' t.toNNReal ω) (leftStopInf R L r η ψ q ω) := by
    rw [hd]; exact inter_subset_right
  obtain ⟨E, hE, hEc, -⟩ := exists_inverse_extension_of_jordan_cases
    (Or.inr (hψ ω hA))
    (hc ω hA) (hdom ω hA) (heq ω hA)
  obtain ⟨Fc, hFc, hFcc, -⟩ :=
    exists_relative_inverse_extension (c := c) (γ := travAllInf R L r η ψ) hγ hlive hE hEc
  have hcur := isConformal_relChart_of_driven (c := c) hγ hlive (hc ω hA)
  refine side_of_tip hcur hFc hFcc (hcfg ω hA).trace (hcfg ω hA).continuous_W (hcfg ω hA).W_zero hT hK
    (fun u hu => ?_) h0 fun y hy => tendsto_tip_eq_zero hcur (hcfg ω hA).trace (hcfg ω hA).continuous_W
      (hcfg ω hA).W_zero hT0 hcut hK htipl hy
  obtain ⟨hlim, hFu⟩ := tendsto_of_ext hFc hFcc u
  refine landing_mem_hull_of_mem_seed_interval (hxL ω) (hxR ω) (hc ω hA) hγ hlive hq0 hE hEc (hdom ω hA)
    (QuantumZipper.FwdHolo.isOpen_compl_fwdHull (hcfg ω hA).continuous_W hT) hd hu hlim ?_
  rw [hFu]; exact hN1 u hu

/-- **`R5Lift.R7LiftCurGeomInf` from a fresh current tip** (pocket opening at the flow seed). -/
theorem r7LiftCurGeomInf_of_tip {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ} {xR : Ω → Fin (0 + 1) → ℝ}
    {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0) (h : R7LiftCurTipInf P A R L r η ψ xL xR c q) :
    R7LiftCurGeomInf P A R L r η ψ xL xR c W' q := by
  filter_upwards [h, ae_curSideInf_of_tip (W' := W') hcfg hψ hc hdom heq hxL hxR h] with ω hω hs hA hlive u hu
  exact ⟨(hω hA hlive).1 u hu, fun _ => hs hA hlive u hu⟩

/-- **The outer collars' `K_s`-landing** (pocket opening at the flow seed; named pathwise input): the second clause of
`R5Lift.R7OuterLiftGeomInf` alone. -/
def R7OuterReflInf {nL nR : ℕ} (P : Measure Ω) (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0)
    (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart)
    (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (X : Ω → Set ℂ) (q : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) → ∀ ξ : ℝ, ξ ∉ forceJumpSet
      (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL i q ω -
          segDriver (travAllInf R L r η ψ ω) q)
      (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR j q ω -
        segDriver (travAllInf R L r η ψ ω) q) →
    extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∉ X ω →
    R5Wall.exposedOuterSel c (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) xL xR q ω ξ →
    ∀ (i : ℕ) (x ε : ℝ),
      ω ∈ refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i →
      η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r →
      IsRefCollar (refChartInf c R L r η ψ i ω) (relChart c (travAllInf R L r η ψ) q ω) ξ
        (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ) x ε →
      extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈ refHull W' ζ' i ω →
      ∃ ρ > 0, ∀ u : ℝ, (u : ℂ) ∈ ball (x : ℂ) ρ →
        extendFrom H (refChartInf c R L r η ψ i ω).2.1 u ∈
          fwdHull (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)

/-- **`R5Lift.R7OuterLiftGeomInf` from a fresh current tip and the outer collars' `K_s`-landing** (bounded change
pocket). -/
theorem r7OuterLiftGeomInf_of_tip {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ} {xR : Ω → Fin (0 + 1) → ℝ}
    {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {X : Ω → Set ℂ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0) (h : R7LiftCurTipInf P A R L r η ψ xL xR c q)
    (ho : R7OuterReflInf P A R L r η ψ xL xR c W' ζ' X q) :
    R7OuterLiftGeomInf P A R L r η ψ xL xR c W' ζ' X q := by
  filter_upwards [ho, ae_curSideInf_of_tip (W' := W') hcfg hψ hc hdom heq hxL hxR h] with ω hω hs hA hlive ξ hξ hX hsel
  exact ⟨fun y hy => hs hA hlive ξ (not_not.1 hsel.1) y hy, hω hA hlive ξ hξ hX hsel⟩

end SeedOpen

end InteractingSLE.Sec7.R5Lift
