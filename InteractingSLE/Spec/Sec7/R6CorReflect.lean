/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6FcCore

/-!
# R.6's seed corner: the same-time inverse transition reflected across an inner real interval

Packet PROVE-R6-CORNER (ruling R98, Astra's note `r6_face_geometry` §§2–5). Deterministic and chart-level.

For conformal charts `O` (outer) and `I` (inner) with `I.dom ⊆ O.dom`, the **inverse transition**
`Φ = O.1 ∘ I.2.1 : ℍ → ℍ` is conformal onto `O.1 '' I.dom`. On an inner real interval `(a, b)` where the inner
landings `E_I(t)` are off `O.dom` (they are old trace, or points of the shared wall) and `Φ` is locally bounded, `Φ`
has a real limit `φ(t)` at every `t` (the cluster set lies in a real fibre of the outer landing `E_O`, which contains no
interval; `PocketStopSide.exists_tendsto_of_tendsto_comp_local`), its boundary extension is real-boundary-conformal at
every `t`, so `φ` is continuous and strictly increasing (positive boundary derivative), and small upper half-discs at
`t` are mapped onto neighbourhoods of `φ(t)` in `ℍ` (open mapping of the injective reflected map): **collars of the
transition domain at every point of `φ((a, b))`**. This is Astra's Lemma 2.5 ("every point of `J₀` has a full
upper-half-disc collar"), obtained from the inner side, so it holds also when the shared attachment is physically the
seed corner `y₀ᵁ`.

## Main results

* `hasDerivAt_re_of_isRealBoundaryConformal`, `strictMonoOn_continuousOn_re_of_forall`;
* `IsRealBoundaryConformal.mono` (shrinking the half-disc);
* **`exists_inverse_reflection`**;
* `phi_zero_eq_zero` (the driver identification from the two relative increments at a common later time);
* **`r6FaceR_right_of_reflection`**, **`r6FaceR_left_of_reflection`**: `R6FaceR` for the later inner chart, with the
  interval `J = φ((t₁, t₂))` through an inner test point `t_ξ` landing on the old hull inside the inner pocket and an
  inner test point `t_y` landing on the open shared wall. The collars at the later time come from the inner increment
  being confined near `0` in the same-time inner chart (Astra's (5)); the signs of the later inner coordinates from the
  transition never reaching the inner driver on `J`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)
open QuantumZipper.CA (schwarzReflect)

namespace InteractingSLE.Sec7.R6Cor

open PocketStopSide R6Fc R6Safe

/-! ### Global monotonicity of a real-boundary-conformal map along an interval -/

/-- The real part of a real-boundary-conformal map has derivative `Re φ̂'(x)` at the centre `x`. -/
theorem hasDerivAt_re_of_isRealBoundaryConformal {G : ℂ → ℂ} {x r : ℝ} (h : R16.IsRealBoundaryConformal G x r)
    (hr : 0 < r) :
    HasDerivAt (fun t : ℝ => (G t).re) (deriv (schwarzReflect G) x).re x := by
  have hd := h.differentiableOn_schwarzReflect
  have hx : (x : ℂ) ∈ ball (x : ℂ) r := mem_ball_self hr
  have h1 := ((hd.differentiableAt (isOpen_ball.mem_nhds hx)).hasDerivAt).real_of_complex
  have he : (fun t : ℝ => (schwarzReflect G t).re) = fun t : ℝ => (G t).re := by
    funext t; rw [schwarzReflect_ofReal]
  rw [he] at h1
  exact h1

/-- **A map real-boundary-conformal at every point of an open interval is strictly increasing and continuous along
it** (positive boundary derivative everywhere, `R16.IsRealBoundaryConformal.deriv_schwarzReflect_pos`). -/
theorem strictMonoOn_continuousOn_re_of_forall {G : ℂ → ℂ} {a b : ℝ}
    (h : ∀ x ∈ Ioo a b, ∃ r > 0, R16.IsRealBoundaryConformal G x r) :
    StrictMonoOn (fun t : ℝ => (G t).re) (Ioo a b) ∧ ContinuousOn (fun t : ℝ => (G t).re) (Ioo a b) := by
  have hd : ∀ x ∈ Ioo a b, HasDerivAt (fun t : ℝ => (G t).re) (deriv (schwarzReflect G) x).re x ∧
      0 < (deriv (schwarzReflect G) x).re := by
    intro x hx
    obtain ⟨r, hr, hrb⟩ := h x hx
    exact ⟨hasDerivAt_re_of_isRealBoundaryConformal hrb hr,
      (hrb.deriv_schwarzReflect_pos (mem_ball_self hr)).2⟩
  have hc : ContinuousOn (fun t : ℝ => (G t).re) (Ioo a b) := fun x hx =>
    (hd x hx).1.continuousAt.continuousWithinAt
  refine ⟨strictMonoOn_of_deriv_pos (convex_Ioo a b) hc fun x hx => ?_, hc⟩
  rw [interior_Ioo] at hx
  rw [(hd x hx).1.deriv]
  exact (hd x hx).2

/-- Real-boundary conformality on a half-disc passes to every smaller concentric half-disc. -/
theorem IsRealBoundaryConformal.mono {G : ℂ → ℂ} {x r r' : ℝ} (h : R16.IsRealBoundaryConformal G x r)
    (hr' : r' ≤ r) : R16.IsRealBoundaryConformal G x r' := by
  have hb : ball (x : ℂ) r' ⊆ ball (x : ℂ) r := ball_subset_ball hr'
  exact ⟨h.1.mono (inter_subset_inter_right _ hb), h.2.1.mono (inter_subset_inter_right _ hb),
    fun z hz hz0 => h.2.2.1 z (hb hz) hz0, fun z hz => h.2.2.2.1 ⟨hz.1, hb hz.2⟩,
    h.2.2.2.2.mono (inter_subset_inter_right _ hb)⟩

theorem eq_ofReal_re_of_im_eq_zero {z : ℂ} (hz : z.im = 0) : z = (z.re : ℂ) :=
  Complex.ext (by simp) (by simp [hz])

theorem re_mem_Ioo_of_mem_ball {a b t r : ℝ} (hr : r ≤ min (t - a) (b - t)) {z : ℂ} (hz : z ∈ ball (t : ℂ) r) :
    z.re ∈ Ioo a b := by
  have h1 : |z.re - t| < r := by
    have h2 := Complex.abs_re_le_norm (z - t)
    rw [mem_ball, dist_eq_norm] at hz
    simp only [Complex.sub_re, Complex.ofReal_re] at h2
    linarith
  rw [abs_lt] at h1
  constructor <;> linarith [min_le_left (t - a) (b - t), min_le_right (t - a) (b - t)]

/-! ### The inverse transition on an inner real interval -/

section Reflect

variable {O I : Chart}

/-- **The inverse transition `Φ = O.1 ∘ I.2.1` reflected across an inner real interval** (see the module docstring):
on `(a, b)`, where the inner landings are off the outer domain and `Φ` is locally bounded, `Φ` has real limits `φ(t)`
with `E_O(φ(t)) = E_I(t)`, `φ` is continuous and strictly increasing, and every upper half-disc at `t` covers an upper
half-disc at `φ(t)`. -/
theorem exists_inverse_reflection (hO : O.IsConformal) (hI : I.IsConformal) (hIO : (I.dom : Set ℂ) ⊆ O.dom)
    {EO EI : ℂ → ℂ} (hEO : EqOn EO O.2.1 H) (hEOc : ContinuousOn EO Hbar)
    (hEI : EqOn EI I.2.1 H) (hEIc : ContinuousOn EI Hbar) {a b : ℝ}
    (hnot : ∀ t ∈ Ioo a b, EI t ∉ (O.dom : Set ℂ))
    (hbdd : ∀ t ∈ Ioo a b, ∃ M : ℝ, ∀ᶠ z in 𝓝[H] (t : ℂ), ‖O.1 (I.2.1 z)‖ ≤ M) :
    ∃ φ : ℝ → ℝ, StrictMonoOn φ (Ioo a b) ∧ ContinuousOn φ (Ioo a b) ∧
      (∀ t ∈ Ioo a b, Tendsto (fun z => O.1 (I.2.1 z)) (𝓝[H] (t : ℂ)) (𝓝 (φ t : ℂ))) ∧
      (∀ t ∈ Ioo a b, EO (φ t) = EI t) ∧
      (∀ t ∈ Ioo a b, ∀ ε > 0, ∃ ρ > 0,
        H ∩ ball (φ t : ℂ) ρ ⊆ (fun z => O.1 (I.2.1 z)) '' (H ∩ ball (t : ℂ) ε)) := by
  classical
  set Φ : ℂ → ℂ := fun z => O.1 (I.2.1 z) with hΦ
  have hT := isConformal_pocketTransitionChart hO hI hIO
  have hΦd : DifferentiableOn ℂ Φ H := hT.1
  have hΦH : MapsTo Φ H H := hT.2.1
  have hΦi : InjOn Φ H := hT.injOn
  have hEOd : DifferentiableOn ℂ EO H := hO.1.congr fun z hz => hEO hz
  have hEOi : InjOn EO H := hO.injOn.congr hEO.symm
  have hR := inverse_extension_real_notMem_image hO hEO hEOc
  have hcomp : ∀ z ∈ H, EO (Φ z) = I.2.1 z := fun z hz => by
    have hm : I.2.1 z ∈ (O.dom : Set ℂ) := hIO (hI.inv_mem_dom hz)
    show EO (O.1 (I.2.1 z)) = I.2.1 z
    rw [hEO (hO.fwd_mem hm), hO.inv_fwd hm]
  have key : ∀ t : ℝ, ∃ y : ℝ, t ∈ Ioo a b →
      EO y = EI t ∧ Tendsto Φ (𝓝[H] (t : ℂ)) (𝓝 (y : ℂ)) := by
    intro t
    by_cases ht : t ∈ Ioo a b
    · obtain ⟨M, hM⟩ := hbdd t ht
      have hFG : Tendsto (fun z => EO (Φ z)) (𝓝[H] (t : ℂ)) (𝓝 (EI t)) :=
        (tendsto_of_extension hEI hEIc t).congr'
          (eventually_nhdsWithin_of_forall fun z hz => (hcomp z hz).symm)
      obtain ⟨ξ, hξ, hEξ, hlim⟩ := exists_tendsto_of_tendsto_comp_local hEOd hEOc hEOi hR one_pos
        (hΦd.continuousOn.mono inter_subset_left) (fun z hz => QuantumZipper.H_subset_Hbar (hΦH hz.1)) hM hFG
      have hξ0 : ξ.im = 0 := by
        rcases (show (0 : ℝ) ≤ ξ.im from hξ).lt_or_eq with h | h
        · exfalso
          apply hnot t ht
          rw [← hEξ, hEO h]
          exact hO.inv_mem_dom h
        · exact h.symm
      have hξr := eq_ofReal_re_of_im_eq_zero hξ0
      exact ⟨ξ.re, fun _ => ⟨by rw [← hξr]; exact hEξ, by rw [← hξr]; exact hlim⟩⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose φ hφ using key
  set Ψ : ℂ → ℂ := extendFrom H Φ with hΨ
  have hΨH : ∀ z ∈ H, Ψ z = Φ z := extendFrom_extends hΦd.continuousOn
  have hcl : ∀ x : ℝ, ((x : ℝ) : ℂ) ∈ closure H := fun x => by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact real_mem_Hbar x
  have hΨt : ∀ t ∈ Ioo a b, Ψ t = (φ t : ℂ) := fun t ht => extendFrom_eq (hcl t) (hφ t ht).2
  have hrb : ∀ t ∈ Ioo a b, ∀ r : ℝ, r ≤ min (t - a) (b - t) → R16.IsRealBoundaryConformal Ψ t r := by
    intro t ht r hrle
    refine ⟨(hΦd.mono inter_subset_left).congr fun z hz => hΨH z hz.1, ?_, ?_, ?_, ?_⟩
    · refine continuousOn_extendFrom (fun z hz => ?_) (fun z hz => ?_)
      · rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact hz.1
      · rcases (show (0 : ℝ) ≤ z.im from hz.1).lt_or_eq with h | h
        · exact ⟨Φ z, (hΦd.continuousOn z h).tendsto⟩
        · rw [eq_ofReal_re_of_im_eq_zero h.symm]
          exact ⟨_, (hφ z.re (re_mem_Ioo_of_mem_ball hrle hz.2)).2⟩
    · intro z hz hz0
      rw [eq_ofReal_re_of_im_eq_zero hz0, hΨt z.re (re_mem_Ioo_of_mem_ball hrle hz)]
      simp
    · intro z hz
      rw [hΨH z hz.1]
      exact hΦH hz.1
    · exact (hΦi.mono inter_subset_left).congr fun z hz => (hΨH z hz.1).symm
  have hpos : ∀ t ∈ Ioo a b, 0 < min (t - a) (b - t) := fun t ht =>
    lt_min (by linarith [ht.1]) (by linarith [ht.2])
  obtain ⟨hmono, hcont⟩ := strictMonoOn_continuousOn_re_of_forall (G := Ψ) (a := a) (b := b)
    fun t ht => ⟨_, hpos t ht, hrb t ht _ le_rfl⟩
  have hφΨ : ∀ t ∈ Ioo a b, φ t = (Ψ t).re := fun t ht => by rw [hΨt t ht, Complex.ofReal_re]
  refine ⟨φ, fun s hs t ht hst => ?_, (hcont.congr fun t ht => hφΨ t ht), fun t ht => (hφ t ht).2,
    fun t ht => (hφ t ht).1, fun t ht ε hε => ?_⟩
  · rw [hφΨ s hs, hφΨ t ht]; exact hmono hs ht hst
  · set r := min (min (t - a) (b - t)) ε with hr
    have hr0 : 0 < r := lt_min (hpos t ht) hε
    have hrb' := hrb t ht r (min_le_left _ _)
    have hSd := hrb'.differentiableOn_schwarzReflect
    have hSi := hrb'.injOn_schwarzReflect
    have hopen := QuantumZipper.CA.isOpen_image_of_injOn' isOpen_ball hSd hSi
    have hmem : (φ t : ℂ) ∈ schwarzReflect Ψ '' ball (t : ℂ) r :=
      ⟨t, mem_ball_self hr0, by rw [schwarzReflect_ofReal, hΨt t ht]⟩
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1 hopen _ hmem
    refine ⟨ρ, hρ, fun w hw => ?_⟩
    obtain ⟨z, hz, hzw⟩ := hρsub hw.2
    have hsg := hrb'.im_schwarzReflect hz
    have hzH : z ∈ H := by
      by_contra hzH
      have hz0 : z.im ≤ 0 := not_lt.1 hzH
      have hw0 : 0 < w.im := hw.1
      rcases hz0.lt_or_eq with h | h
      · have := hsg.2.2 h; rw [hzw] at this; linarith
      · have := hsg.2.1 h; rw [hzw] at this; linarith
    refine ⟨z, ⟨hzH, ball_subset_ball (min_le_right _ _) hz⟩, ?_⟩
    rw [← hzw]
    show Φ z = schwarzReflect Ψ z
    simp only [schwarzReflect, le_of_lt (show (0 : ℝ) < z.im from hzH), ↓reduceIte, hΨH z hzH]

end Reflect

/-! ### The data of the later-time transition on the reflected interval -/

section Later

variable {O I₀ I : Chart}

/-- **The driver identification** `φ(0) = 0`: if points of the inner domain have both chart coordinates arbitrarily
small (the two relative increments at a common later time), the reflected inverse transition fixes `0`. -/
theorem phi_zero_eq_zero (hI₀ : I₀.IsConformal) {φ : ℝ → ℝ}
    (hlim : Tendsto (fun z => O.1 (I₀.2.1 z)) (𝓝[H] ((0 : ℝ) : ℂ)) (𝓝 (φ 0 : ℂ)))
    (hdrv : ∀ ε > 0, ∃ z ∈ (I₀.dom : Set ℂ), ‖I₀.1 z‖ < ε ∧ ‖O.1 z‖ < ε) : φ 0 = 0 := by
  by_contra hne
  have hd : 0 < |φ 0| := abs_pos.2 hne
  obtain ⟨δ, hδ, hδlim⟩ := Metric.tendsto_nhdsWithin_nhds.1 hlim (|φ 0| / 2) (half_pos hd)
  obtain ⟨z, hz, hz1, hz2⟩ := hdrv (min δ (|φ 0| / 2)) (lt_min hδ (half_pos hd))
  have hw := hI₀.fwd_mem hz
  have h1 := hδlim hw (by
    rw [Complex.ofReal_zero, dist_zero_right]; exact hz1.trans_le (min_le_left _ _))
  rw [hI₀.inv_fwd hz, dist_eq_norm] at h1
  have h2 : ‖((φ 0 : ℝ) : ℂ)‖ ≤ ‖O.1 z - (φ 0 : ℂ)‖ + ‖O.1 z‖ := by
    have := norm_sub_le (O.1 z) (O.1 z - (φ 0 : ℂ))
    rw [sub_sub_cancel] at this
    linarith [norm_sub_rev (O.1 z) (O.1 z - (φ 0 : ℂ))]
  rw [Complex.norm_real, Real.norm_eq_abs] at h2
  linarith [min_le_right δ (|φ 0| / 2)]

/-- **R.6's face, shared side on the right, from the same-time inverse reflection** (Astra's §§2–5). The inner chart
`I₀` is the contained pocket's chart at the same original time as the outer chart `O`, the inner chart `I` the one at
the later inner time; `ρ` bounds the inner increment between them (`hinc`, `hinc0`). On the inner interval `(a, b)`
(`a < 0`) the inverse transition reflects (`hnot`, `hbdd`); `t_ξ ∈ (2ρ, b)` lands in the inner pocket on the old
hull, `t_y ∈ (t_ξ, b)` on the open shared wall (dead/alive in both charts, local agreement there). -/
theorem r6FaceR_right_of_reflection {ρL ρR σL σR vL vR wL wR : Fin 1 → ℝ}
    (hO : O.IsConformal) (hI₀ : I₀.IsConformal) (hI : I.IsConformal)
    (hI₀O : (I₀.dom : Set ℂ) ⊆ O.dom) (hIO : (I.dom : Set ℂ) ⊆ O.dom)
    {EO EI₀ EI : ℂ → ℂ} (hEO : EqOn EO O.2.1 H) (hEOc : ContinuousOn EO Hbar)
    (hEI₀ : EqOn EI₀ I₀.2.1 H) (hEI₀c : ContinuousOn EI₀ Hbar)
    (hEI : EqOn EI I.2.1 H) (hEIc : ContinuousOn EI Hbar)
    {a b : ℝ} (ha : a < 0)
    (hnot : ∀ t ∈ Ioo a b, EI₀ t ∉ (O.dom : Set ℂ))
    (hbdd : ∀ t ∈ Ioo a b, ∃ M : ℝ, ∀ᶠ z in 𝓝[H] (t : ℂ), ‖O.1 (I₀.2.1 z)‖ ≤ M)
    (hdrv : ∀ ε > 0, ∃ z ∈ (I₀.dom : Set ℂ), ‖I₀.1 z‖ < ε ∧ ‖O.1 z‖ < ε)
    {ρ : ℝ} (hρ : 0 < ρ) (hinc : ∀ z ∈ H, ρ < ‖z‖ → I₀.2.1 z ∈ (I.dom : Set ℂ))
    (hinc0 : ∀ᶠ w in 𝓝[H] (0 : ℂ), ‖I₀.1 (I.2.1 w)‖ ≤ ρ)
    {tξ ty : ℝ} (hξ : 2 * ρ < tξ) (hξy : tξ < ty) (hyb : ty < b)
    (hdeadO : ∀ x : ℝ, EO x = EI₀ tξ → vL 0 ≤ x ∧ x < vR 0)
    (haliveO : ∀ x : ℝ, EO x = EI₀ ty → x < vL 0 ∨ vR 0 < x)
    (hdeadI : ∀ x : ℝ, EI x = EI₀ tξ → wL 0 < x ∧ x < wR 0)
    (haliveI : ∀ x : ℝ, EI x = EI₀ ty → x < wL 0 ∨ wR 0 < x)
    (hwR : 0 < wR 0) (hρRσ : ρR 0 = σR 0)
    (hlocξ : ∃ ε > 0, (O.dom : Set ℂ) ∩ ball (EI₀ tξ) ε ⊆ I.dom)
    (hlocy : ∃ ε > 0, (O.dom : Set ℂ) ∩ ball (EI₀ ty) ε ⊆ I.dom)
    (hbddI : ∀ t ∈ Ioo a b, ∃ ε > 0, ∃ M : ℝ, ∀ w ∈ (I.dom : Set ℂ) ∩ ball (EI₀ t) ε, ‖I.1 w‖ ≤ M) :
    R6FaceR ρL ρR σL σR vL vR wL wR O I (H \ (O.dom : Set ℂ)) (H \ (I.dom : Set ℂ)) := by
  obtain ⟨φ, hφm, hφc, hφlim, hφE, hφcol⟩ := exists_inverse_reflection hO hI₀ hI₀O hEO hEOc hEI₀ hEI₀c hnot hbdd
  have hξ0 : 0 < tξ := by linarith
  have h0 : (0 : ℝ) ∈ Ioo a b := ⟨ha, by linarith⟩
  have hξab : tξ ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hyab : ty ∈ Ioo a b := ⟨by linarith, hyb⟩
  have hφ0 : φ 0 = 0 := phi_zero_eq_zero hI₀ (by simpa using hφlim 0 h0) hdrv
  -- the interval
  set t₁ := (2 * ρ + tξ) / 2 with ht₁
  set t₂ := (ty + b) / 2 with ht₂
  have ht₁ξ : t₁ < tξ := by linarith
  have ht₁ρ : 2 * ρ < t₁ := by linarith
  have hyt₂ : ty < t₂ := by linarith
  have ht₂b : t₂ < b := by linarith
  have hsub : Icc t₁ t₂ ⊆ Ioo a b := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  set J : Set ℝ := Ioo (φ t₁) (φ t₂) with hJ
  have hJpre : ∀ x ∈ J, ∃ t ∈ Ioo t₁ t₂, φ t = x := fun x hx =>
    intermediate_value_Ioo (by linarith) (hφc.mono hsub) hx
  have hIoo : Ioo t₁ t₂ ⊆ Ioo a b := Ioo_subset_Icc_self.trans hsub
  have hT := isConformal_pocketTransitionChart hO hI hIO
  have hTdom := dom_pocketTransitionChart hO hI hIO
  -- collars
  have hcollar : ∀ x ∈ J, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆ ((pocketTransitionChart O I).dom : Set ℂ) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := hJpre x hx
    obtain ⟨r, hr, hrsub⟩ := hφcol t (hIoo ht) ρ hρ
    refine ⟨r, hr, fun w hw => ?_⟩
    obtain ⟨z, hz, rfl⟩ := hrsub hw
    have hzn : ρ < ‖z‖ := by
      have h1 : ‖(t : ℂ)‖ ≤ ‖z‖ + ‖(t : ℂ) - z‖ := by
        calc ‖(t : ℂ)‖ = ‖z + ((t : ℂ) - z)‖ := by congr 1; ring
          _ ≤ _ := norm_add_le _ _
      have h2 : ‖(t : ℂ) - z‖ < ρ := by rw [norm_sub_rev, ← dist_eq_norm]; exact hz.2
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [ht.1])] at h1
      linarith [ht.1]
    rw [hTdom]
    exact ⟨_, hinc z hz.1 hzn, rfl⟩
  have hland : ∀ x ∈ J, Tendsto O.2.1 (𝓝[H] (x : ℂ)) (𝓝 (EO x)) := fun x _ => tendsto_of_extension hEO hEOc x
  -- bounds
  have hbound : ∀ x ∈ J, ∃ M : ℝ, ∀ᶠ z in 𝓝[((pocketTransitionChart O I).dom : Set ℂ)] (x : ℂ),
      ‖(pocketTransitionChart O I).1 z‖ ≤ M := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := hJpre x hx
    obtain ⟨ε, hε, M, hM⟩ := hbddI t (hIoo ht)
    refine ⟨M, ?_⟩
    have hev : ∀ᶠ z in 𝓝[Hbar] ((φ t : ℝ) : ℂ), EO z ∈ ball (EO (φ t)) ε :=
      (hEOc _ (real_mem_Hbar (φ t))).tendsto.eventually (ball_mem_nhds _ hε)
    have hle : 𝓝[((pocketTransitionChart O I).dom : Set ℂ)] ((φ t : ℝ) : ℂ) ≤ 𝓝[Hbar] ((φ t : ℝ) : ℂ) :=
      nhdsWithin_mono _ (hT.dom_subset.trans QuantumZipper.H_subset_Hbar)
    filter_upwards [hle hev, self_mem_nhdsWithin] with z hzb hzT
    have hzm := (mem_dom_pocketTransitionChart hO hI hIO).1 hzT
    rw [hEO hzm.1, hφE t (hIoo ht)] at hzb
    exact hM _ ⟨hzm.2, hzb⟩
  obtain ⟨G, hGeq, hGc, hGrb, hGE⟩ := exists_transition_extension_of_inverse_and_bounds hO hI hIO hEI hEIc
    isOpen_Ioo hcollar hland hbound
  have hGreal : ∀ x ∈ J, (G x).im = 0 := fun x hx => by
    obtain ⟨r, hr, hrb⟩ := hGrb x hx
    exact hrb.2.2.1 x (mem_ball_self hr) (by simp)
  set g : ℝ → ℝ := fun x => (G x).re with hg
  have hGg : ∀ x ∈ J, G x = ((g x : ℝ) : ℂ) := fun x hx => eq_ofReal_re_of_im_eq_zero (hGreal x hx)
  obtain ⟨hgm, hgc⟩ := strictMonoOn_continuousOn_re_of_forall (G := G) hGrb
  have hglim : ∀ x ∈ J, Tendsto (pocketTransitionChart O I).1
      (𝓝[((pocketTransitionChart O I).dom : Set ℂ)] (x : ℂ)) (𝓝 ((g x : ℝ) : ℂ)) := by
    intro x hx
    have h1 : ContinuousWithinAt G (((pocketTransitionChart O I).dom : Set ℂ) ∪ Complex.ofReal '' J) x :=
      hGc _ (Or.inr ⟨x, hx, rfl⟩)
    have h2 := (h1.mono subset_union_left).tendsto
    rw [hGg x hx] at h2
    exact h2.congr' (eventually_nhdsWithin_of_forall fun z hz => hGeq hz)
  have hgE : ∀ x ∈ J, EI (g x) = EO x := fun x hx => by rw [← hGg x hx]; exact hGE x hx
  -- the transition never reaches the inner driver on `J`
  have hgne : ∀ x ∈ J, g x ≠ 0 := by
    intro x hx hgx
    obtain ⟨t, ht, rfl⟩ := hJpre x hx
    obtain ⟨r, hr, hrsub⟩ := hcollar _ hx
    have hDm : ((pocketTransitionChart O I).dom : Set ℂ) ∈ 𝓝[H] ((φ t : ℝ) : ℂ) :=
      mem_of_superset (inter_mem_nhdsWithin H (ball_mem_nhds _ hr)) hrsub
    have hT0 : Tendsto (pocketTransitionChart O I).1 (𝓝[H] ((φ t : ℝ) : ℂ)) (𝓝[H] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have := (hglim _ hx).mono_left (nhdsWithin_le_of_mem hDm)
        rwa [hgx, Complex.ofReal_zero] at this
      · filter_upwards [hDm] with z hz
        exact hT.fwd_mem hz
    have hA : ∀ᶠ z in 𝓝[H] ((φ t : ℝ) : ℂ), ‖I₀.1 (O.2.1 z)‖ ≤ ρ := by
      filter_upwards [hT0.eventually hinc0, hDm] with z hz hzD
      have hzm := (mem_dom_pocketTransitionChart hO hI hIO).1 hzD
      have he : I.2.1 ((pocketTransitionChart O I).1 z) = O.2.1 z := hI.inv_fwd hzm.2
      rwa [he] at hz
    obtain ⟨r', hr', hr'sub⟩ := hφcol t (hIoo ht) (ρ / 2) (half_pos hρ)
    have hB : ∀ᶠ z in 𝓝[H] ((φ t : ℝ) : ℂ), ρ < ‖I₀.1 (O.2.1 z)‖ := by
      filter_upwards [inter_mem_nhdsWithin H (ball_mem_nhds _ hr')] with z hz
      obtain ⟨z', hz', hz'e⟩ := hr'sub hz
      have hm : I₀.2.1 z' ∈ (O.dom : Set ℂ) := hI₀O (hI₀.inv_mem_dom hz'.1)
      have he : I₀.1 (O.2.1 z) = z' := by
        rw [← hz'e]
        show I₀.1 (O.2.1 (O.1 (I₀.2.1 z'))) = z'
        rw [hO.inv_fwd hm, hI₀.2.2 z' hz'.1]
      rw [he]
      have h1 : ‖(t : ℂ)‖ ≤ ‖z'‖ + ‖(t : ℂ) - z'‖ := by
        calc ‖(t : ℂ)‖ = ‖z' + ((t : ℂ) - z')‖ := by congr 1; ring
          _ ≤ _ := norm_add_le _ _
      have h2 : ‖(t : ℂ) - z'‖ < ρ / 2 := by rw [norm_sub_rev, ← dist_eq_norm]; exact hz'.2
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [ht.1])] at h1
      linarith [ht.1]
    have := neBot_nhdsWithin_H_real (φ t)
    obtain ⟨z, hzA, hzB⟩ := (hA.and hB).exists
    linarith
  -- the two test points
  have hξJ : φ tξ ∈ J := ⟨hφm (hsub ⟨le_rfl, by linarith⟩) hξab ht₁ξ, hφm hξab (hsub ⟨by linarith, le_rfl⟩)
    (by linarith)⟩
  have hyJ : φ ty ∈ J := ⟨hφm (hsub ⟨le_rfl, by linarith⟩) hyab (by linarith), hφm hyab
    (hsub ⟨by linarith, le_rfl⟩) hyt₂⟩
  have hξpos : 0 < φ tξ := by rw [← hφ0]; exact hφm h0 hξab hξ0
  obtain ⟨hξvL, hξvR⟩ := hdeadO (φ tξ) (hφE tξ hξab)
  have hξy' : φ tξ < φ ty := hφm hξab hyab hξy
  have hyvR : vR 0 < φ ty := by
    rcases haliveO (φ ty) (hφE ty hyab) with h | h
    · linarith
    · exact h
  obtain ⟨hηL, hηR⟩ := hdeadI (g (φ tξ)) ((hgE _ hξJ).trans (hφE tξ hξab))
  have hgξy : g (φ tξ) < g (φ ty) := hgm hξJ hyJ hξy'
  have hη₀ : wR 0 < g (φ ty) := by
    rcases haliveI (g (φ ty)) ((hgE _ hyJ).trans (hφE ty hyab)) with h | h
    · linarith
    · exact h
  have hηpos : 0 < g (φ tξ) := by
    rcases lt_or_gt_of_ne (hgne _ hξJ) with h | h
    · exfalso
      have hIcc : Icc (φ tξ) (φ ty) ⊆ J := fun x hx =>
        ⟨lt_of_lt_of_le hξJ.1 hx.1, lt_of_le_of_lt hx.2 hyJ.2⟩
      obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc hξy'.le (hgc.mono hIcc) ⟨h.le, by linarith⟩
      exact hgne x (hIcc hx) hx0
    · exact h
  -- local agreement
  have hagree : ∀ t ∈ Ioo a b, (∃ ε > 0, (O.dom : Set ℂ) ∩ ball (EI₀ t) ε ⊆ I.dom) →
      ∀ p : ℂ, Tendsto O.2.1 (𝓝[H] ((φ t : ℝ) : ℂ)) (𝓝 p) →
        ∃ ε > 0, (H \ (I.dom : Set ℂ)) ∩ ball p ε ⊆ H \ (O.dom : Set ℂ) := by
    intro t ht ⟨ε, hε, hloc⟩ p hp
    have := neBot_nhdsWithin_H_real (φ t)
    have hpE : p = EI₀ t := (tendsto_nhds_unique hp (tendsto_of_extension hEO hEOc (φ t))).trans
      (hφE t ht)
    subst hpE
    exact ⟨ε, hε, fun z hz => ⟨hz.1.1, fun hzO => hz.1.2 (hloc ⟨hzO, hz.2⟩)⟩⟩
  exact ⟨J, φ ty, g (φ ty), φ tξ, g (φ tξ), isOpen_Ioo, isPreconnected_Ioo, hcollar, hbound, hyJ, hξJ,
    hglim _ hyJ, hglim _ hξJ, Or.inl ⟨hyvR, hη₀, hρRσ⟩, Or.inl ⟨hξpos, hξvR, hηpos, hηR⟩,
    hagree ty hyab hlocy, hagree tξ hξab hlocξ⟩

/-- **R.6's face, shared side on the left, from the same-time inverse reflection** (mirror of
`r6FaceR_right_of_reflection`: `b > 0`, `t_y < t_ξ < −2ρ`). -/
theorem r6FaceR_left_of_reflection {ρL ρR σL σR vL vR wL wR : Fin 1 → ℝ}
    (hO : O.IsConformal) (hI₀ : I₀.IsConformal) (hI : I.IsConformal)
    (hI₀O : (I₀.dom : Set ℂ) ⊆ O.dom) (hIO : (I.dom : Set ℂ) ⊆ O.dom)
    {EO EI₀ EI : ℂ → ℂ} (hEO : EqOn EO O.2.1 H) (hEOc : ContinuousOn EO Hbar)
    (hEI₀ : EqOn EI₀ I₀.2.1 H) (hEI₀c : ContinuousOn EI₀ Hbar)
    (hEI : EqOn EI I.2.1 H) (hEIc : ContinuousOn EI Hbar)
    {a b : ℝ} (hb : 0 < b)
    (hnot : ∀ t ∈ Ioo a b, EI₀ t ∉ (O.dom : Set ℂ))
    (hbdd : ∀ t ∈ Ioo a b, ∃ M : ℝ, ∀ᶠ z in 𝓝[H] (t : ℂ), ‖O.1 (I₀.2.1 z)‖ ≤ M)
    (hdrv : ∀ ε > 0, ∃ z ∈ (I₀.dom : Set ℂ), ‖I₀.1 z‖ < ε ∧ ‖O.1 z‖ < ε)
    {ρ : ℝ} (hρ : 0 < ρ) (hinc : ∀ z ∈ H, ρ < ‖z‖ → I₀.2.1 z ∈ (I.dom : Set ℂ))
    (hinc0 : ∀ᶠ w in 𝓝[H] (0 : ℂ), ‖I₀.1 (I.2.1 w)‖ ≤ ρ)
    {tξ ty : ℝ} (hξ : tξ < -(2 * ρ)) (hξy : ty < tξ) (hyb : a < ty)
    (hdeadO : ∀ x : ℝ, EO x = EI₀ tξ → vL 0 < x ∧ x ≤ vR 0)
    (haliveO : ∀ x : ℝ, EO x = EI₀ ty → x < vL 0 ∨ vR 0 < x)
    (hdeadI : ∀ x : ℝ, EI x = EI₀ tξ → wL 0 < x ∧ x < wR 0)
    (haliveI : ∀ x : ℝ, EI x = EI₀ ty → x < wL 0 ∨ wR 0 < x)
    (hwL : wL 0 < 0) (hρLσ : ρL 0 = σL 0)
    (hlocξ : ∃ ε > 0, (O.dom : Set ℂ) ∩ ball (EI₀ tξ) ε ⊆ I.dom)
    (hlocy : ∃ ε > 0, (O.dom : Set ℂ) ∩ ball (EI₀ ty) ε ⊆ I.dom)
    (hbddI : ∀ t ∈ Ioo a b, ∃ ε > 0, ∃ M : ℝ, ∀ w ∈ (I.dom : Set ℂ) ∩ ball (EI₀ t) ε, ‖I.1 w‖ ≤ M) :
    R6FaceR ρL ρR σL σR vL vR wL wR O I (H \ (O.dom : Set ℂ)) (H \ (I.dom : Set ℂ)) := by
  obtain ⟨φ, hφm, hφc, hφlim, hφE, hφcol⟩ := exists_inverse_reflection hO hI₀ hI₀O hEO hEOc hEI₀ hEI₀c hnot hbdd
  have hξ0 : tξ < 0 := by linarith
  have h0 : (0 : ℝ) ∈ Ioo a b := ⟨by linarith, hb⟩
  have hξab : tξ ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hyab : ty ∈ Ioo a b := ⟨hyb, by linarith⟩
  have hφ0 : φ 0 = 0 := phi_zero_eq_zero hI₀ (by simpa using hφlim 0 h0) hdrv
  -- the interval
  set t₁ := (a + ty) / 2 with ht₁
  set t₂ := (tξ - 2 * ρ) / 2 with ht₂
  have ht₁y : t₁ < ty := by linarith
  have ht₁a : a < t₁ := by linarith
  have hξt₂ : tξ < t₂ := by linarith
  have ht₂ρ : t₂ < -(2 * ρ) := by linarith
  have hsub : Icc t₁ t₂ ⊆ Ioo a b := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  set J : Set ℝ := Ioo (φ t₁) (φ t₂) with hJ
  have hJpre : ∀ x ∈ J, ∃ t ∈ Ioo t₁ t₂, φ t = x := fun x hx =>
    intermediate_value_Ioo (by linarith) (hφc.mono hsub) hx
  have hIoo : Ioo t₁ t₂ ⊆ Ioo a b := Ioo_subset_Icc_self.trans hsub
  have hT := isConformal_pocketTransitionChart hO hI hIO
  have hTdom := dom_pocketTransitionChart hO hI hIO
  -- collars
  have hcollar : ∀ x ∈ J, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆ ((pocketTransitionChart O I).dom : Set ℂ) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := hJpre x hx
    obtain ⟨r, hr, hrsub⟩ := hφcol t (hIoo ht) ρ hρ
    refine ⟨r, hr, fun w hw => ?_⟩
    obtain ⟨z, hz, rfl⟩ := hrsub hw
    have hzn : ρ < ‖z‖ := by
      have h1 : ‖(t : ℂ)‖ ≤ ‖z‖ + ‖(t : ℂ) - z‖ := by
        calc ‖(t : ℂ)‖ = ‖z + ((t : ℂ) - z)‖ := by congr 1; ring
          _ ≤ _ := norm_add_le _ _
      have h2 : ‖(t : ℂ) - z‖ < ρ := by rw [norm_sub_rev, ← dist_eq_norm]; exact hz.2
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith [ht.2])] at h1
      linarith [ht.2]
    rw [hTdom]
    exact ⟨_, hinc z hz.1 hzn, rfl⟩
  have hland : ∀ x ∈ J, Tendsto O.2.1 (𝓝[H] (x : ℂ)) (𝓝 (EO x)) := fun x _ => tendsto_of_extension hEO hEOc x
  -- bounds
  have hbound : ∀ x ∈ J, ∃ M : ℝ, ∀ᶠ z in 𝓝[((pocketTransitionChart O I).dom : Set ℂ)] (x : ℂ),
      ‖(pocketTransitionChart O I).1 z‖ ≤ M := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := hJpre x hx
    obtain ⟨ε, hε, M, hM⟩ := hbddI t (hIoo ht)
    refine ⟨M, ?_⟩
    have hev : ∀ᶠ z in 𝓝[Hbar] ((φ t : ℝ) : ℂ), EO z ∈ ball (EO (φ t)) ε :=
      (hEOc _ (real_mem_Hbar (φ t))).tendsto.eventually (ball_mem_nhds _ hε)
    have hle : 𝓝[((pocketTransitionChart O I).dom : Set ℂ)] ((φ t : ℝ) : ℂ) ≤ 𝓝[Hbar] ((φ t : ℝ) : ℂ) :=
      nhdsWithin_mono _ (hT.dom_subset.trans QuantumZipper.H_subset_Hbar)
    filter_upwards [hle hev, self_mem_nhdsWithin] with z hzb hzT
    have hzm := (mem_dom_pocketTransitionChart hO hI hIO).1 hzT
    rw [hEO hzm.1, hφE t (hIoo ht)] at hzb
    exact hM _ ⟨hzm.2, hzb⟩
  obtain ⟨G, hGeq, hGc, hGrb, hGE⟩ := exists_transition_extension_of_inverse_and_bounds hO hI hIO hEI hEIc
    isOpen_Ioo hcollar hland hbound
  have hGreal : ∀ x ∈ J, (G x).im = 0 := fun x hx => by
    obtain ⟨r, hr, hrb⟩ := hGrb x hx
    exact hrb.2.2.1 x (mem_ball_self hr) (by simp)
  set g : ℝ → ℝ := fun x => (G x).re with hg
  have hGg : ∀ x ∈ J, G x = ((g x : ℝ) : ℂ) := fun x hx => eq_ofReal_re_of_im_eq_zero (hGreal x hx)
  obtain ⟨hgm, hgc⟩ := strictMonoOn_continuousOn_re_of_forall (G := G) hGrb
  have hglim : ∀ x ∈ J, Tendsto (pocketTransitionChart O I).1
      (𝓝[((pocketTransitionChart O I).dom : Set ℂ)] (x : ℂ)) (𝓝 ((g x : ℝ) : ℂ)) := by
    intro x hx
    have h1 : ContinuousWithinAt G (((pocketTransitionChart O I).dom : Set ℂ) ∪ Complex.ofReal '' J) x :=
      hGc _ (Or.inr ⟨x, hx, rfl⟩)
    have h2 := (h1.mono subset_union_left).tendsto
    rw [hGg x hx] at h2
    exact h2.congr' (eventually_nhdsWithin_of_forall fun z hz => hGeq hz)
  have hgE : ∀ x ∈ J, EI (g x) = EO x := fun x hx => by rw [← hGg x hx]; exact hGE x hx
  -- the transition never reaches the inner driver on `J`
  have hgne : ∀ x ∈ J, g x ≠ 0 := by
    intro x hx hgx
    obtain ⟨t, ht, rfl⟩ := hJpre x hx
    obtain ⟨r, hr, hrsub⟩ := hcollar _ hx
    have hDm : ((pocketTransitionChart O I).dom : Set ℂ) ∈ 𝓝[H] ((φ t : ℝ) : ℂ) :=
      mem_of_superset (inter_mem_nhdsWithin H (ball_mem_nhds _ hr)) hrsub
    have hT0 : Tendsto (pocketTransitionChart O I).1 (𝓝[H] ((φ t : ℝ) : ℂ)) (𝓝[H] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have := (hglim _ hx).mono_left (nhdsWithin_le_of_mem hDm)
        rwa [hgx, Complex.ofReal_zero] at this
      · filter_upwards [hDm] with z hz
        exact hT.fwd_mem hz
    have hA : ∀ᶠ z in 𝓝[H] ((φ t : ℝ) : ℂ), ‖I₀.1 (O.2.1 z)‖ ≤ ρ := by
      filter_upwards [hT0.eventually hinc0, hDm] with z hz hzD
      have hzm := (mem_dom_pocketTransitionChart hO hI hIO).1 hzD
      have he : I.2.1 ((pocketTransitionChart O I).1 z) = O.2.1 z := hI.inv_fwd hzm.2
      rwa [he] at hz
    obtain ⟨r', hr', hr'sub⟩ := hφcol t (hIoo ht) (ρ / 2) (half_pos hρ)
    have hB : ∀ᶠ z in 𝓝[H] ((φ t : ℝ) : ℂ), ρ < ‖I₀.1 (O.2.1 z)‖ := by
      filter_upwards [inter_mem_nhdsWithin H (ball_mem_nhds _ hr')] with z hz
      obtain ⟨z', hz', hz'e⟩ := hr'sub hz
      have hm : I₀.2.1 z' ∈ (O.dom : Set ℂ) := hI₀O (hI₀.inv_mem_dom hz'.1)
      have he : I₀.1 (O.2.1 z) = z' := by
        rw [← hz'e]
        show I₀.1 (O.2.1 (O.1 (I₀.2.1 z'))) = z'
        rw [hO.inv_fwd hm, hI₀.2.2 z' hz'.1]
      rw [he]
      have h1 : ‖(t : ℂ)‖ ≤ ‖z'‖ + ‖(t : ℂ) - z'‖ := by
        calc ‖(t : ℂ)‖ = ‖z' + ((t : ℂ) - z')‖ := by congr 1; ring
          _ ≤ _ := norm_add_le _ _
      have h2 : ‖(t : ℂ) - z'‖ < ρ / 2 := by rw [norm_sub_rev, ← dist_eq_norm]; exact hz'.2
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith [ht.2])] at h1
      linarith [ht.2]
    have := neBot_nhdsWithin_H_real (φ t)
    obtain ⟨z, hzA, hzB⟩ := (hA.and hB).exists
    linarith
  -- the two test points
  have hξJ : φ tξ ∈ J := ⟨hφm (hsub ⟨le_rfl, by linarith⟩) hξab (by linarith), hφm hξab (hsub ⟨by linarith, le_rfl⟩)
    hξt₂⟩
  have hyJ : φ ty ∈ J := ⟨hφm (hsub ⟨le_rfl, by linarith⟩) hyab ht₁y, hφm hyab
    (hsub ⟨by linarith, le_rfl⟩) (by linarith)⟩
  have hξneg : φ tξ < 0 := by rw [← hφ0]; exact hφm hξab h0 hξ0
  obtain ⟨hξvL, hξvR⟩ := hdeadO (φ tξ) (hφE tξ hξab)
  have hξy' : φ ty < φ tξ := hφm hyab hξab hξy
  have hyvL : φ ty < vL 0 := by
    rcases haliveO (φ ty) (hφE ty hyab) with h | h
    · exact h
    · linarith
  obtain ⟨hηL, hηR⟩ := hdeadI (g (φ tξ)) ((hgE _ hξJ).trans (hφE tξ hξab))
  have hgξy : g (φ ty) < g (φ tξ) := hgm hyJ hξJ hξy'
  have hη₀ : g (φ ty) < wL 0 := by
    rcases haliveI (g (φ ty)) ((hgE _ hyJ).trans (hφE ty hyab)) with h | h
    · exact h
    · linarith
  have hηneg : g (φ tξ) < 0 := by
    rcases lt_or_gt_of_ne (hgne _ hξJ) with h | h
    · exact h
    · exfalso
      have hIcc : Icc (φ ty) (φ tξ) ⊆ J := fun x hx =>
        ⟨lt_of_lt_of_le hyJ.1 hx.1, lt_of_le_of_lt hx.2 hξJ.2⟩
      obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc hξy'.le (hgc.mono hIcc) ⟨by linarith, h.le⟩
      exact hgne x (hIcc hx) hx0
  -- local agreement
  have hagree : ∀ t ∈ Ioo a b, (∃ ε > 0, (O.dom : Set ℂ) ∩ ball (EI₀ t) ε ⊆ I.dom) →
      ∀ p : ℂ, Tendsto O.2.1 (𝓝[H] ((φ t : ℝ) : ℂ)) (𝓝 p) →
        ∃ ε > 0, (H \ (I.dom : Set ℂ)) ∩ ball p ε ⊆ H \ (O.dom : Set ℂ) := by
    intro t ht ⟨ε, hε, hloc⟩ p hp
    have := neBot_nhdsWithin_H_real (φ t)
    have hpE : p = EI₀ t := (tendsto_nhds_unique hp (tendsto_of_extension hEO hEOc (φ t))).trans
      (hφE t ht)
    subst hpE
    exact ⟨ε, hε, fun z hz => ⟨hz.1.1, fun hzO => hz.1.2 (hloc ⟨hzO, hz.2⟩)⟩⟩
  exact ⟨J, φ ty, g (φ ty), φ tξ, g (φ tξ), isOpen_Ioo, isPreconnected_Ioo, hcollar, hbound, hyJ, hξJ,
    hglim _ hyJ, hglim _ hξJ, Or.inr ⟨hyvL, hη₀, hρLσ⟩, Or.inr ⟨hξvL, hξneg, hηL, hηneg⟩,
    hagree ty hyab hlocy, hagree tξ hξab hlocξ⟩

end Later

end InteractingSLE.Sec7.R6Cor
