/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71NMain
import InteractingSLE.Spec.Sec7.Aux119Reflect
import InteractingSLE.Spec.Supplement.R6RefPhase

/-!
# Lemma 7.1's inherited branch: the local integer of a transition across a real interval

Packet PROVE-LEMMA71O (supplement §2.3, "Deterministic normalization lemma", `source/spec/p433-480.md` L472–L520:
"The transition `r_p = φ ∘ g_p⁻¹ ∘ m_p⁻¹ : U_p → ℍ` reflects across this interval and has positive real derivative
there. Choose its logarithmic derivative to have imaginary part zero on that one connected interval").

Read in the chart coordinate: let `c` be a conformal chart of a domain `C ⊆ ℍ` with a logarithm `L` of `c.1′` on `C`,
and let `g` be holomorphic and injective on an open set `D ⊇ C` with values in `ℍ` and a logarithm `L_g` of `g′`.
If the transition `T = g ∘ c.2.1 : ℍ → ℍ` has a real limit at every real point of a disc `B(x, r)`, then it extends by
Schwarz reflection across `(x − r, x + r)` with positive derivative there (`R16.IsRealBoundaryConformal`), so
`Im (L_g − L) ∘ c.2.1 → 2πn` at every real point near `x`, for **one** integer `n`
(`exists_int_tendsto_of_realLimits`).

This is the analytic core used at every wall point (with `g` a single wall's Loewner map) and at the opening corner
(with `g` the map of the union of two wall prefixes). Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real ComplexConjugate

namespace InteractingSLE.Sec7.Lemma71O

open QuantumZipper (H Hbar)
open QuantumZipper.CA (schwarzReflect)

/-! ### The derivative of the chart inverse -/

section Deriv

variable {c : Chart}

/-- `c.1′(c.2.1 y) · c.2.1′(y) = 1` on `ℍ` (differentiate `c.1 ∘ c.2.1 = id`). -/
theorem deriv_fwd_mul_deriv_inv (hc : c.IsConformal) {y : ℂ} (hy : y ∈ H) :
    deriv c.1 (c.2.1 y) * deriv c.2.1 y = 1 := by
  have hyo : H ∈ 𝓝 y := QuantumZipper.isOpen_H.mem_nhds hy
  have hd₂ : DifferentiableAt ℂ c.2.1 y := (hc.1 y hy).differentiableAt hyo
  have hmem : c.2.1 y ∈ c.dom := hc.inv_mem_dom hy
  have hd₁ : DifferentiableAt ℂ c.1 (c.2.1 y) :=
    (hc.differentiableOn_fwd _ hmem).differentiableAt (c.dom.isOpen.mem_nhds hmem)
  have hid : (fun w => c.1 (c.2.1 w)) =ᶠ[𝓝 y] id :=
    Filter.eventually_of_mem hyo fun w hw => hc.2.2 w hw
  have h1 : deriv (fun w => c.1 (c.2.1 w)) y = 1 := by rw [hid.deriv_eq, deriv_id]
  rw [← h1]
  exact (deriv_comp y hd₁ hd₂).symm

end Deriv

/-! ### The local integer -/

section Local

variable {c : Chart} {C D : Set ℂ} {L g LG : ℂ → ℂ}

/-- **The transition is real-boundary conformal** (`R16.IsRealBoundaryConformal`) on a half-disc at whose real points
it has real limits. -/
theorem isRealBoundaryConformal_extendFrom (hc : c.IsConformal) (hdom : (c.dom : Set ℂ) = C) (hCD : C ⊆ D)
    (hgd : DifferentiableOn ℂ g D) (hgi : InjOn g D) (hgH : MapsTo g D H) {x r : ℝ}
    (hlim : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → ∃ v : ℂ, v.im = 0 ∧
      Tendsto (fun y => g (c.2.1 y)) (𝓝[H] z) (𝓝 v)) :
    R16.IsRealBoundaryConformal (extendFrom H fun y => g (c.2.1 y)) x r := by
  set T : ℂ → ℂ := fun y => g (c.2.1 y) with hTdef
  have hinvC : ∀ y ∈ H, c.2.1 y ∈ C := fun y hy => by rw [← hdom]; exact hc.inv_mem_dom hy
  have hTd : DifferentiableOn ℂ T H := hgd.comp hc.1 fun y hy => hCD (hinvC y hy)
  set R : ℂ → ℂ := extendFrom H T with hRdef
  have hRT : ∀ y ∈ H, R y = T y := extendFrom_extends hTd.continuousOn
  have hclH : Hbar ∩ ball (x : ℂ) r ⊆ closure H := fun z hz => by
    rw [closure_H]; exact hz.1
  refine ⟨(hTd.mono inter_subset_left).congr fun y hy => hRT y hy.1, ?_, ?_, ?_, ?_⟩
  · refine continuousOn_extendFrom hclH fun z hz => ?_
    rcases (show (0 : ℝ) ≤ z.im from hz.1).lt_or_eq with hpos | hzero
    · exact ⟨T z, hTd.continuousOn z hpos⟩
    · obtain ⟨v, -, hv⟩ := hlim z hz.2 hzero.symm
      exact ⟨v, hv⟩
  · intro z hz hz0
    obtain ⟨v, hv0, hv⟩ := hlim z hz hz0
    rw [hRdef, extendFrom_eq (hclH ⟨show (0 : ℝ) ≤ z.im from hz0.ge, hz⟩) hv]
    exact hv0
  · intro y hy
    rw [hRT y hy.1]
    exact hgH (hCD (hinvC y hy.1))
  · intro y₁ hy₁ y₂ hy₂ h
    rw [hRT y₁ hy₁.1, hRT y₂ hy₂.1] at h
    exact hc.injOn hy₁.1 hy₂.1 (hgi (hCD (hinvC y₁ hy₁.1)) (hCD (hinvC y₂ hy₂.1)) h)

/-- **The local integer of a transition across a real interval** (supplement §2.3, proof of the normalization lemma:
the transition "reflects across this interval and has positive real derivative there"). Let `c` be a conformal chart
of `C` with a logarithm `L` of `c.1′`, and `g` holomorphic and injective on an open `D ⊇ C` into `ℍ` with a logarithm
`LG` of `g′`. If `g ∘ c.2.1` has a real limit (within `ℍ`) at every real point of `B(x, r)`, then for one integer `n`
and some `ε ∈ (0, r]`, `Im (LG − L) ∘ c.2.1 → 2πn` at every real point of `B(x, ε)`. -/
theorem exists_int_tendsto_of_realLimits (hc : c.IsConformal) (hdom : (c.dom : Set ℂ) = C)
    (hL : IsDerivLog c.1 L C) (hDo : IsOpen D) (hCD : C ⊆ D) (hgd : DifferentiableOn ℂ g D) (hgi : InjOn g D)
    (hgH : MapsTo g D H) (hLG : IsDerivLog g LG D) {x r : ℝ} (hr : 0 < r)
    (hlim : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → ∃ v : ℂ, v.im = 0 ∧
      Tendsto (fun y => g (c.2.1 y)) (𝓝[H] z) (𝓝 v)) :
    ∃ n : ℤ, ∃ ε > 0, ε ≤ r ∧ ∀ z ∈ ball (x : ℂ) ε, z.im = 0 →
      Tendsto (fun y => (LG (c.2.1 y) - L (c.2.1 y)).im) (𝓝[H] z) (𝓝 (2 * π * n)) := by
  set T : ℂ → ℂ := fun y => g (c.2.1 y) with hTdef
  have hinvC : ∀ y ∈ H, c.2.1 y ∈ C := fun y hy => by rw [← hdom]; exact hc.inv_mem_dom hy
  have hTd : DifferentiableOn ℂ T H := hgd.comp hc.1 fun y hy => hCD (hinvC y hy)
  set R : ℂ → ℂ := extendFrom H T with hRdef
  have hRT : ∀ y ∈ H, R y = T y := extendFrom_extends hTd.continuousOn
  have hrbc : R16.IsRealBoundaryConformal R x r := isRealBoundaryConformal_extendFrom hc hdom hCD hgd hgi hgH hlim
  have hSd : DifferentiableOn ℂ (schwarzReflect R) (ball (x : ℂ) r) := hrbc.differentiableOn_schwarzReflect
  set Φ : ℂ → ℂ := deriv (schwarzReflect R) with hΦdef
  have hΦc : ContinuousOn Φ (ball (x : ℂ) r) := (hSd.deriv isOpen_ball).continuousOn
  have hxb : (x : ℂ) ∈ ball (x : ℂ) r := mem_ball_self hr
  obtain ⟨-, hΦx⟩ := hrbc.deriv_schwarzReflect_pos hxb
  -- a smaller disc on which `Φ` has positive real part
  have hΦxc : ContinuousAt Φ (x : ℂ) := hΦc.continuousAt (isOpen_ball.mem_nhds hxb)
  obtain ⟨ε₀, hε₀, hε₀sub⟩ := Metric.mem_nhds_iff.1
    (hΦxc.preimage_mem_nhds ((isOpen_lt continuous_const continuous_re).mem_nhds hΦx))
  set ε := min ε₀ r with hεdef
  have hε : 0 < ε := lt_min hε₀ hr
  have hεr : ε ≤ r := min_le_right _ _
  have hballε : ball (x : ℂ) ε ⊆ ball (x : ℂ) r := ball_subset_ball hεr
  have hre : ∀ z ∈ ball (x : ℂ) ε, 0 < (Φ z).re := fun z hz =>
    hε₀sub (ball_subset_ball (min_le_left _ _) hz)
  -- `exp (LG − L) ∘ c.2.1 = Φ` on the upper half-disc
  have hexp : ∀ y ∈ ball (x : ℂ) ε ∩ H, exp (LG (c.2.1 y) - L (c.2.1 y)) = Φ y := by
    rintro y ⟨-, hy⟩
    have hyo : H ∈ 𝓝 y := QuantumZipper.isOpen_H.mem_nhds hy
    have hSe : schwarzReflect R =ᶠ[𝓝 y] T := Filter.eventually_of_mem hyo fun w hw => by
      simp only [schwarzReflect, show (0 : ℝ) ≤ w.im from le_of_lt hw, ↓reduceIte]
      exact hRT w hw
    have hCy : c.2.1 y ∈ C := hinvC y hy
    have hdg : DifferentiableAt ℂ g (c.2.1 y) := (hgd _ (hCD hCy)).differentiableAt (hDo.mem_nhds (hCD hCy))
    have hd₂ : DifferentiableAt ℂ c.2.1 y := (hc.1 y hy).differentiableAt hyo
    have hΦy : Φ y = deriv g (c.2.1 y) * deriv c.2.1 y := by
      rw [hΦdef, hSe.deriv_eq]
      exact deriv_comp y hdg hd₂
    have hmul := deriv_fwd_mul_deriv_inv hc hy
    have hne : deriv c.1 (c.2.1 y) ≠ 0 := by rw [← hL.2 _ hCy]; exact exp_ne_zero _
    rw [Complex.exp_sub, hLG.2 _ (hCD hCy), hL.2 _ hCy, hΦy, div_eq_iff hne]
    calc deriv g (c.2.1 y) = deriv g (c.2.1 y) * (deriv c.1 (c.2.1 y) * deriv c.2.1 y) := by
          rw [hmul, mul_one]
      _ = deriv g (c.2.1 y) * deriv c.2.1 y * deriv c.1 (c.2.1 y) := by ring
  -- one integer on the upper half-disc
  have hSc : IsPreconnected (ball (x : ℂ) ε ∩ H) :=
    ((convex_ball _ _).inter (convex_halfSpace_gt (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0)).isPreconnected
  have hL₁ : ContinuousOn (fun y => L (c.2.1 y)) (ball (x : ℂ) ε ∩ H) :=
    hL.1.continuousOn.comp (hc.1.continuousOn.mono inter_subset_right) fun y hy => hinvC y hy.2
  have hL₂ : ContinuousOn (fun y => LG (c.2.1 y)) (ball (x : ℂ) ε ∩ H) :=
    hLG.1.continuousOn.comp (hc.1.continuousOn.mono inter_subset_right) fun y hy => hCD (hinvC y hy.2)
  have hslit : ∀ z ∈ ball (x : ℂ) ε ∩ H, Φ z ∈ slitPlane := fun z hz =>
    mem_slitPlane_iff.2 (Or.inl (hre z hz.1))
  obtain ⟨n, hn⟩ := Aux119.exists_int_eqOn_sub hSc hL₁ hL₂ (hΦc.mono (inter_subset_left.trans hballε)) hslit hexp
  refine ⟨n, ε, hε, hεr, fun z hz hz0 => ?_⟩
  -- the limit at a real point
  have hzr : z ∈ ball (x : ℂ) r := hballε hz
  obtain ⟨hΦzi, hΦzr⟩ := hrbc.deriv_schwarzReflect_pos (y := z.re)
    (by rw [← eq_ofReal_re_of_im_eq_zero hz0]; exact hzr)
  rw [← eq_ofReal_re_of_im_eq_zero hz0] at hΦzi hΦzr
  have hΦzc : ContinuousAt Φ z := hΦc.continuousAt (isOpen_ball.mem_nhds hzr)
  have hargz : arg (Φ z) = 0 := by
    have heq : Φ z = ((Φ z).re : ℂ) := Complex.ext (by simp) (by simp only [ofReal_im]; exact hΦzi)
    rw [heq, arg_ofReal_of_nonneg hΦzr.le]
  have harg : Tendsto (fun y => arg (Φ y)) (𝓝[H] z) (𝓝 0) := by
    rw [← hargz]
    exact ((continuousAt_arg (mem_slitPlane_iff.2 (Or.inl hΦzr))).comp hΦzc).tendsto.mono_left
      nhdsWithin_le_nhds
  have hev : ∀ᶠ y in 𝓝[H] z, y ∈ ball (x : ℂ) ε ∩ H := by
    filter_upwards [nhdsWithin_le_nhds (isOpen_ball.mem_nhds hz), self_mem_nhdsWithin] with y h1 h2
    exact ⟨h1, h2⟩
  have hlim' := harg.add_const (2 * π * n)
  rw [zero_add] at hlim'
  refine hlim'.congr' ?_
  filter_upwards [hev] with y hy
  rw [hn y hy, Complex.add_im, log_im]
  simp only [mul_im, intCast_re, intCast_im, zero_mul, add_zero, mul_re, ofReal_re, ofReal_im, I_re, I_im,
    mul_zero, sub_zero, mul_one, Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- **The removable corner** (supplement §2.3: the two retained sides "share one real interval containing the incident
image of `x₀`"). If the transition `g ∘ c.2.1` is bounded on the upper half-disc `B(0, r) ∩ ℍ` and has a real limit at
every real point `z ≠ 0` of `B(0, r)`, then it also has a real limit at `0`: the Schwarz reflection is holomorphic and
bounded on the punctured disc (Riemann's removable singularity theorem). -/
theorem exists_tendsto_zero_of_realLimits (hc : c.IsConformal) (hdom : (c.dom : Set ℂ) = C) (hCD : C ⊆ D)
    (hgd : DifferentiableOn ℂ g D) (hgi : InjOn g D) (hgH : MapsTo g D H) {r M : ℝ} (hr : 0 < r)
    (hM : ∀ y ∈ ball (0 : ℂ) r ∩ H, ‖g (c.2.1 y)‖ ≤ M)
    (hlim : ∀ z ∈ ball (0 : ℂ) r, z.im = 0 → z ≠ 0 → ∃ v : ℂ, v.im = 0 ∧
      Tendsto (fun y => g (c.2.1 y)) (𝓝[H] z) (𝓝 v)) :
    ∃ v : ℂ, v.im = 0 ∧ Tendsto (fun y => g (c.2.1 y)) (𝓝[H] 0) (𝓝 v) := by
  set T : ℂ → ℂ := fun y => g (c.2.1 y) with hTdef
  have hinvC : ∀ y ∈ H, c.2.1 y ∈ C := fun y hy => by rw [← hdom]; exact hc.inv_mem_dom hy
  have hTd : DifferentiableOn ℂ T H := hgd.comp hc.1 fun y hy => hCD (hinvC y hy)
  set R : ℂ → ℂ := extendFrom H T with hRdef
  have hRT : ∀ y ∈ H, R y = T y := extendFrom_extends hTd.continuousOn
  set S : ℂ → ℂ := schwarzReflect R with hSdef
  have hSH : ∀ w, 0 < w.im → S w = T w := fun w hw => by
    simp only [hSdef, schwarzReflect, show (0 : ℝ) ≤ w.im from hw.le, ↓reduceIte]
    exact hRT w hw
  have hSL : ∀ w, w.im < 0 → S w = conj (T (conj w)) := fun w hw => by
    have hcw : 0 < (conj w).im := by rw [conj_im]; linarith
    simp only [hSdef, schwarzReflect, show ¬ (0 : ℝ) ≤ w.im from not_le.2 hw, ↓reduceIte]
    rw [hRT _ hcw]
  -- the real values
  have hreal : ∀ z ∈ ball (0 : ℂ) r, z.im = 0 → z ≠ 0 → (S z).im = 0 ∧ ‖S z‖ ≤ M := by
    intro z hz hz0 hzne
    obtain ⟨v, hv0, hv⟩ := hlim z hz hz0 hzne
    have hcl : z ∈ closure H := by rw [closure_H]; exact show (0 : ℝ) ≤ z.im from hz0.ge
    have hSz : S z = v := by
      simp only [hSdef, schwarzReflect, show (0 : ℝ) ≤ z.im from hz0.ge, ↓reduceIte]
      exact extendFrom_eq hcl hv
    refine ⟨hSz ▸ hv0, ?_⟩
    rw [hSz]
    have : (𝓝[H] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
    refine le_of_tendsto hv.norm ?_
    filter_upwards [nhdsWithin_le_nhds (isOpen_ball.mem_nhds hz), self_mem_nhdsWithin] with y h1 h2
    exact hM y ⟨h1, h2⟩
  -- holomorphic on the punctured disc
  have hdiff : ∀ z ∈ ball (0 : ℂ) r, z ≠ 0 → DifferentiableAt ℂ S z := by
    intro z hz hzne
    rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
    · have hcz : conj z ∈ H := by show 0 < (conj z).im; rw [conj_im]; linarith
      have hTc : DifferentiableAt ℂ T (conj z) :=
        (hTd _ hcz).differentiableAt (QuantumZipper.isOpen_H.mem_nhds hcz)
      have hev : S =ᶠ[𝓝 z] (conj ∘ T ∘ conj) :=
        Filter.eventually_of_mem ((isOpen_lt continuous_im continuous_const).mem_nhds hneg) fun w hw => hSL w hw
      refine (DifferentiableAt.congr_of_eventuallyEq ?_ hev)
      have := hTc.conj_conj
      rwa [RCLike.conj_conj] at this
    · -- a small disc about the real point `z` inside the punctured disc
      have hzn : 0 < ‖z‖ := norm_pos_iff.2 hzne
      have hzr : ‖z‖ < r := by simpa [mem_ball, dist_zero_right] using hz
      set δ := min ‖z‖ (r - ‖z‖) with hδ
      have hδ0 : 0 < δ := lt_min hzn (by linarith)
      have hzx : z = ((z.re : ℝ) : ℂ) := eq_ofReal_re_of_im_eq_zero hzero
      have hsub : ∀ w ∈ ball ((z.re : ℝ) : ℂ) δ, w ∈ ball (0 : ℂ) r ∧ w ≠ 0 := by
        intro w hw
        rw [← hzx, mem_ball] at hw
        refine ⟨?_, fun h => ?_⟩
        · rw [mem_ball, dist_zero_right]
          have h1 := norm_le_norm_add_norm_sub' w z
          rw [← dist_eq_norm] at h1
          have h2 : δ ≤ r - ‖z‖ := min_le_right _ _
          linarith
        · rw [h, dist_comm, dist_zero_right] at hw
          have : δ ≤ ‖z‖ := min_le_left _ _
          linarith
      have hrbc := isRealBoundaryConformal_extendFrom (x := z.re) (r := δ) hc hdom hCD hgd hgi hgH
        fun w hw hw0 => hlim w (hsub w hw).1 hw0 (hsub w hw).2
      have hzb : z ∈ ball ((z.re : ℝ) : ℂ) δ := by rw [← hzx]; exact mem_ball_self hδ0
      exact (hrbc.differentiableOn_schwarzReflect z hzb).differentiableAt (isOpen_ball.mem_nhds hzb)
    · have hev : S =ᶠ[𝓝 z] T :=
        Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_im).mem_nhds hpos) fun w hw => hSH w hw
      exact ((hTd _ hpos).differentiableAt (QuantumZipper.isOpen_H.mem_nhds hpos)).congr_of_eventuallyEq hev
  -- bounded on the punctured disc
  have hbd : ∀ w ∈ ball (0 : ℂ) r, w ≠ 0 → ‖S w‖ ≤ M := by
    intro w hw hwne
    rcases lt_trichotomy w.im 0 with hneg | hzero | hpos
    · have hcw : conj w ∈ ball (0 : ℂ) r ∩ H := by
        refine ⟨?_, show 0 < (conj w).im by rw [conj_im]; linarith⟩
        rw [mem_ball, dist_zero_right, Complex.norm_conj]; simpa [mem_ball, dist_zero_right] using hw
      rw [hSL w hneg, Complex.norm_conj]
      exact hM _ hcw
    · exact (hreal w hw hzero hwne).2
    · rw [hSH w hpos]; exact hM w ⟨hw, hpos⟩
  have hpunct : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ ball (0 : ℂ) r ∧ z ≠ 0 := by
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) hr), self_mem_nhdsWithin] with z h1 h2
    exact ⟨h1, h2⟩
  have hlimS := Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under
    (hpunct.mono fun z hz => hdiff z hz.1 hz.2)
    ⟨M + ‖S 0‖, eventually_map.2 (hpunct.mono fun z hz => (norm_sub_le _ _).trans (by linarith [hbd z hz.1 hz.2]))⟩
  set v := limUnder (𝓝[≠] (0 : ℂ)) S with hvdef
  -- the limit along the real axis is real
  have hreal' : Tendsto (fun t : ℝ => S (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 v) := by
    refine hlimS.comp ?_
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun t ht => ?_⟩
    · have := (Complex.continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    · exact Complex.ofReal_ne_zero.2 (ne_of_gt ht)
  have hv0 : v.im = 0 := by
    have h1 := (Complex.continuous_im.tendsto v).comp hreal'
    refine tendsto_nhds_unique h1 (tendsto_const_nhds.congr' ?_)
    have hev : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), (t : ℂ) ∈ ball (0 : ℂ) r ∧ (t : ℂ) ≠ 0 := by
      have hc0 : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun t ht => ?_⟩
        · have := (Complex.continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
          simpa using this
        · exact Complex.ofReal_ne_zero.2 (ne_of_gt ht)
      exact hc0.eventually hpunct
    filter_upwards [hev] with t ht
    exact ((hreal (t : ℂ) ht.1 (by simp) ht.2).1).symm
  refine ⟨v, hv0, ?_⟩
  have hle : 𝓝[H] (0 : ℂ) ≤ 𝓝[≠] (0 : ℂ) :=
    nhdsWithin_mono _ fun w hw h => by
      rw [Set.mem_singleton_iff.1 h] at hw
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hw)
  exact (hlimS.mono_left hle).congr' (eventually_nhdsWithin_of_forall fun w hw => hSH w hw)

/-- **The integer at the corner**: under the hypotheses of `exists_tendsto_zero_of_realLimits`, one integer `n` with
`Im (LG − L) ∘ c.2.1 → 2πn` at every real point of a disc `B(0, ε)`, on both sides of `0`. -/
theorem exists_int_corner (hc : c.IsConformal) (hdom : (c.dom : Set ℂ) = C) (hL : IsDerivLog c.1 L C)
    (hDo : IsOpen D) (hCD : C ⊆ D) (hgd : DifferentiableOn ℂ g D) (hgi : InjOn g D) (hgH : MapsTo g D H)
    (hLG : IsDerivLog g LG D) {r M : ℝ} (hr : 0 < r) (hM : ∀ y ∈ ball (0 : ℂ) r ∩ H, ‖g (c.2.1 y)‖ ≤ M)
    (hlim : ∀ z ∈ ball (0 : ℂ) r, z.im = 0 → z ≠ 0 → ∃ v : ℂ, v.im = 0 ∧
      Tendsto (fun y => g (c.2.1 y)) (𝓝[H] z) (𝓝 v)) :
    ∃ n : ℤ, ∃ ε > 0, ε ≤ r ∧ ∀ z ∈ ball (0 : ℂ) ε, z.im = 0 →
      Tendsto (fun y => (LG (c.2.1 y) - L (c.2.1 y)).im) (𝓝[H] z) (𝓝 (2 * π * n)) := by
  obtain ⟨v₀, hv₀, hT₀⟩ := exists_tendsto_zero_of_realLimits hc hdom hCD hgd hgi hgH hr hM hlim
  have h := exists_int_tendsto_of_realLimits (x := 0) hc hdom hL hDo hCD hgd hgi hgH hLG hr fun z hz hz0 => by
    rw [Complex.ofReal_zero] at hz
    by_cases hz' : z = 0
    · exact ⟨v₀, hv₀, hz' ▸ hT₀⟩
    · exact hlim z hz hz0 hz'
  simpa only [Complex.ofReal_zero] using h

end Local

end InteractingSLE.Sec7.Lemma71O
