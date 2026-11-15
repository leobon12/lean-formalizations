/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkNormLift
import InteractingSLE.Spec.Sec7.Lemma71OLocal

/-!
# Theorem 1.4's walk leaves: transitions between two charts across a common real interval

Packet PROVE-T14-WALKNORM. Let `c₁`, `c₂` be conformal charts with derivative lifts (`Chart.HasDerivLift`), and suppose
that the inverse of `c₁` maps an upper half-disc `ℍ ∩ B(x, r)` into the domain of `c₂`, and that the transition
`T = c₂.1 ∘ c₁.2.1` has a real limit at every real point of `B(x, r)`. Then (Theorem GW4, proof, p. 637: "an
inherited branch change is an integer multiple of `2π`"; supplement §2.3 "the transition reflects across this
interval and has positive real derivative there"):

* `tendsto_transition`: `T` tends to its limit, eventually lies in `ℍ` and `c₂.2.1 ∘ T = c₁.2.1`;
* **`exists_int_tendsto_lift_sub`**: the lift difference `c₂.2.2 ∘ c₁.2.1 − c₁.2.2 ∘ c₁.2.1` tends to `2πn` at `x`
  for one integer `n` (Schwarz reflection of `T` with positive derivative — the local form of
  `Sec7.Lemma71O.exists_int_tendsto_of_realLimits`, which needs `T` only on the half-disc).

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H Hbar)
open QuantumZipper.CA (schwarzReflect)

namespace InteractingSLE.Theorem14.WalkNorm

variable {c₁ c₂ : Chart}

/-- **The transition at a germ**: if the inverse of `c₁` maps an upper half-disc at `x` into the domain of `c₂` and
`T = c₂.1 ∘ c₁.2.1` tends to `v` at `x`, then eventually `T ∈ ℍ` and `c₂.2.1 ∘ T = c₁.2.1`. -/
theorem eventually_transition (hc₂ : c₂.IsConformal) {x : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : ∀ y ∈ H ∩ ball x r, c₁.2.1 y ∈ c₂.dom) :
    ∀ᶠ y in 𝓝[H] x, c₂.1 (c₁.2.1 y) ∈ H ∧ c₂.2.1 (c₂.1 (c₁.2.1 y)) = c₁.2.1 y := by
  filter_upwards [inter_mem_nhdsWithin H (ball_mem_nhds x hr)] with y hy
  exact ⟨hc₂.fwd_mem (hsub y hy), hc₂.inv_fwd (hsub y hy)⟩

/-- **The local integer of a transition between two charts with derivative lifts.** -/
theorem exists_int_tendsto_lift_sub (hc₁ : c₁.IsConformal) (hc₂ : c₂.IsConformal) (hL₁ : c₁.HasDerivLift)
    (hL₂ : c₂.HasDerivLift) {x r : ℝ} (hr : 0 < r) (hsub : ∀ y ∈ H ∩ ball (x : ℂ) r, c₁.2.1 y ∈ c₂.dom)
    (hlim : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → ∃ v : ℂ, v.im = 0 ∧
      Tendsto (fun y => c₂.1 (c₁.2.1 y)) (𝓝[H] z) (𝓝 v)) :
    ∃ n : ℤ, Tendsto (fun y => c₂.2.2 (c₁.2.1 y) - c₁.2.2 (c₁.2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (2 * π * n)) := by
  obtain ⟨L₁, hL₁d, hL₁i⟩ := hL₁
  obtain ⟨L₂, hL₂d, hL₂i⟩ := hL₂
  set T : ℂ → ℂ := fun y => c₂.1 (c₁.2.1 y) with hTdef
  set S : Set ℂ := H ∩ ball (x : ℂ) r with hSdef
  have hSo : IsOpen S := QuantumZipper.isOpen_H.inter isOpen_ball
  have hinvd : ∀ y ∈ S, DifferentiableAt ℂ c₁.2.1 y := fun y hy =>
    (hc₁.1 y hy.1).differentiableAt (QuantumZipper.isOpen_H.mem_nhds hy.1)
  have hfwdd : ∀ y ∈ S, DifferentiableAt ℂ c₂.1 (c₁.2.1 y) := fun y hy =>
    (hc₂.differentiableOn_fwd _ (hsub y hy)).differentiableAt (c₂.dom.isOpen.mem_nhds (hsub y hy))
  have hTd : DifferentiableOn ℂ T S := fun y hy => ((hfwdd y hy).comp y (hinvd y hy)).differentiableWithinAt
  set R : ℂ → ℂ := extendFrom H T with hRdef
  have hRT : ∀ y ∈ S, R y = T y := fun y hy =>
    extendFrom_eq (subset_closure hy.1) ((hTd.continuousOn y hy).continuousAt (hSo.mem_nhds hy)
      |>.tendsto.mono_left nhdsWithin_le_nhds)
  have hclH : Hbar ∩ ball (x : ℂ) r ⊆ closure H := fun z hz => by
    rw [closure_H]; exact hz.1
  have hrbc : R16.IsRealBoundaryConformal R x r := by
    refine ⟨hTd.congr fun y hy => hRT y hy, ?_, ?_, ?_, ?_⟩
    · refine continuousOn_extendFrom hclH fun z hz => ?_
      rcases (show (0 : ℝ) ≤ z.im from hz.1).lt_or_eq with hpos | hzero
      · exact ⟨T z, ((hTd.continuousOn z ⟨hpos, hz.2⟩).continuousAt
          (hSo.mem_nhds ⟨hpos, hz.2⟩)).tendsto.mono_left nhdsWithin_le_nhds⟩
      · obtain ⟨v, -, hv⟩ := hlim z hz.2 hzero.symm
        exact ⟨v, hv⟩
    · intro z hz hz0
      obtain ⟨v, hv0, hv⟩ := hlim z hz hz0
      rw [hRdef, extendFrom_eq (hclH ⟨show (0 : ℝ) ≤ z.im from hz0.ge, hz⟩) hv]
      exact hv0
    · intro y hy
      rw [hRT y hy]
      exact hc₂.fwd_mem (hsub y hy)
    · intro y₁ hy₁ y₂ hy₂ h
      rw [hRT y₁ hy₁, hRT y₂ hy₂] at h
      have h' : c₁.2.1 y₁ = c₁.2.1 y₂ := by
        rw [← hc₂.inv_fwd (hsub y₁ hy₁), ← hc₂.inv_fwd (hsub y₂ hy₂)]
        exact congrArg c₂.2.1 h
      exact hc₁.injOn hy₁.1 hy₂.1 h'
  have hSd : DifferentiableOn ℂ (schwarzReflect R) (ball (x : ℂ) r) := hrbc.differentiableOn_schwarzReflect
  set Φ : ℂ → ℂ := deriv (schwarzReflect R) with hΦdef
  have hΦc : ContinuousOn Φ (ball (x : ℂ) r) := (hSd.deriv isOpen_ball).continuousOn
  have hxb : (x : ℂ) ∈ ball (x : ℂ) r := mem_ball_self hr
  obtain ⟨hΦxi, hΦx⟩ := hrbc.deriv_schwarzReflect_pos hxb
  have hΦxc : ContinuousAt Φ (x : ℂ) := hΦc.continuousAt (isOpen_ball.mem_nhds hxb)
  obtain ⟨ε₀, hε₀, hε₀sub⟩ := Metric.mem_nhds_iff.1
    (hΦxc.preimage_mem_nhds ((isOpen_lt continuous_const continuous_re).mem_nhds hΦx))
  set ε := min ε₀ r with hεdef
  have hε : 0 < ε := lt_min hε₀ hr
  have hballε : ball (x : ℂ) ε ⊆ ball (x : ℂ) r := ball_subset_ball (min_le_right _ _)
  have hre : ∀ z ∈ ball (x : ℂ) ε, 0 < (Φ z).re := fun z hz =>
    hε₀sub (ball_subset_ball (min_le_left _ _) hz)
  have hdom₁ : ∀ y ∈ H, c₁.2.1 y ∈ c₁.dom := fun y hy => hc₁.inv_mem_dom hy
  -- `exp (L₂ − L₁) ∘ c₁.2.1 = Φ` on the upper half-disc
  have hexp : ∀ y ∈ ball (x : ℂ) ε ∩ H, exp (L₂ (c₁.2.1 y) - L₁ (c₁.2.1 y)) = Φ y := by
    rintro y ⟨hyb, hy⟩
    have hyS : y ∈ S := ⟨hy, hballε hyb⟩
    have hyo : H ∈ 𝓝 y := QuantumZipper.isOpen_H.mem_nhds hy
    have hSe : schwarzReflect R =ᶠ[𝓝 y] T := by
      filter_upwards [hSo.mem_nhds hyS] with w hw
      simp only [schwarzReflect, show (0 : ℝ) ≤ w.im from le_of_lt hw.1, ↓reduceIte]
      exact hRT w hw
    have hΦy : Φ y = deriv c₂.1 (c₁.2.1 y) * deriv c₁.2.1 y := by
      rw [hΦdef, hSe.deriv_eq]
      exact deriv_comp y (hfwdd y hyS) (hinvd y hyS)
    have hmul := Sec7.Lemma71O.deriv_fwd_mul_deriv_inv hc₁ hy
    have hne : deriv c₁.1 (c₁.2.1 y) ≠ 0 := by rw [← hL₁d.2 _ (hdom₁ y hy)]; exact exp_ne_zero _
    rw [Complex.exp_sub, hL₂d.2 _ (hsub y hyS), hL₁d.2 _ (hdom₁ y hy), hΦy, div_eq_iff hne]
    calc deriv c₂.1 (c₁.2.1 y) = deriv c₂.1 (c₁.2.1 y) * (deriv c₁.1 (c₁.2.1 y) * deriv c₁.2.1 y) := by
          rw [hmul, mul_one]
      _ = deriv c₂.1 (c₁.2.1 y) * deriv c₁.2.1 y * deriv c₁.1 (c₁.2.1 y) := by ring
  have hSc : IsPreconnected (ball (x : ℂ) ε ∩ H) :=
    ((convex_ball _ _).inter (convex_halfSpace_gt (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0)).isPreconnected
  have hcont₁ : ContinuousOn (fun y => L₁ (c₁.2.1 y)) (ball (x : ℂ) ε ∩ H) :=
    hL₁d.1.continuousOn.comp (hc₁.1.continuousOn.mono inter_subset_right) fun y hy => hdom₁ y hy.2
  have hcont₂ : ContinuousOn (fun y => L₂ (c₁.2.1 y)) (ball (x : ℂ) ε ∩ H) :=
    hL₂d.1.continuousOn.comp (hc₁.1.continuousOn.mono inter_subset_right) fun y hy =>
      hsub y ⟨hy.2, hballε hy.1⟩
  have hslit : ∀ z ∈ ball (x : ℂ) ε ∩ H, Φ z ∈ slitPlane := fun z hz =>
    mem_slitPlane_iff.2 (Or.inl (hre z hz.1))
  obtain ⟨n, hn⟩ := Sec7.Aux119.exists_int_eqOn_sub hSc hcont₁ hcont₂
    (hΦc.mono (inter_subset_left.trans hballε)) hslit hexp
  refine ⟨n, ?_⟩
  have hargz : arg (Φ x) = 0 := by
    have heq : Φ x = ((Φ x).re : ℂ) := Complex.ext (by simp) (by simp only [ofReal_im]; exact hΦxi)
    rw [heq, arg_ofReal_of_nonneg hΦx.le]
  have harg : Tendsto (fun y => arg (Φ y)) (𝓝[H] (x : ℂ)) (𝓝 0) := by
    rw [← hargz]
    exact ((continuousAt_arg (mem_slitPlane_iff.2 (Or.inl hΦx))).comp hΦxc).tendsto.mono_left
      nhdsWithin_le_nhds
  have hev : ∀ᶠ y in 𝓝[H] (x : ℂ), y ∈ ball (x : ℂ) ε ∩ H := by
    filter_upwards [nhdsWithin_le_nhds (isOpen_ball.mem_nhds (mem_ball_self hε)), self_mem_nhdsWithin]
      with y h1 h2
    exact ⟨h1, h2⟩
  have hlim' := harg.add_const (2 * π * n)
  rw [zero_add] at hlim'
  refine hlim'.congr' ?_
  filter_upwards [hev] with y hy
  have hyS : y ∈ S := ⟨hy.2, hballε hy.1⟩
  rw [hL₂i _ (hsub y hyS), hL₁i _ (hdom₁ y hy.2), ← Complex.sub_im, hn y hy, Complex.add_im, log_im]
  simp only [mul_im, intCast_re, intCast_im, zero_mul, add_zero, mul_re, ofReal_re, ofReal_im, I_re, I_im,
    mul_zero, sub_zero, mul_one, Complex.re_ofNat, Complex.im_ofNat]
  ring

end InteractingSLE.Theorem14.WalkNorm
