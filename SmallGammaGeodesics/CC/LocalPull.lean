import SmallGammaGeodesics.CC.Pullback

/-!
# The local conformal pullback is continuous on `𝓓_K` (track CC, packet CC12a, T3)

Source: planning audit `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D17**
item 2 ("the local pullback [is] a continuous linear map `𝓓_K(U) → 𝓓(ℂ)` for each compact `K`: the
`pullK`/`continuous_pullK` pattern with derivative bounds for compositions").

Let `ϕ` be holomorphic and injective on an open set `W`, with left inverse `ψ = invFunOn ϕ W`. The
conformal pullback `τg = 1_W · |ϕ'|² · (g ∘ ϕ)` (`confPullFun`, CC1) of a test function `g`
supported in a compact `K ⊆ ϕ(W)` is supported in the compact `ψ(K) ⊆ W` (`confK`).

* `confPullFun_iteratedFDeriv_bound`: on a compact `A ⊆ W`, `‖Dⁿ(τg)(x)‖ ≤ C_{A,n} · S` whenever
  `‖Dʲg‖ ≤ S` for all `j ≤ n` (Leibniz `norm_iteratedFDerivWithin_mul_le` and Faà di Bruno
  `norm_iteratedFDerivWithin_comp_le`, within the open set `W`, where `ϕ` and `|ϕ'|²` are smooth;
  their derivatives are bounded on `A`);
* **T3** `confPullK : 𝓓_K →L[ℝ] 𝓓_{ψ(K)}` (`ContDiffMapSupportedIn.mkCLM`, continuous by the
  seminorm estimate), and `confPullOnCLM O : 𝓓(O) →L[ℝ] 𝓓(ℂ)` for an open `O ⊆ ϕ(W)`
  (`TestFunction.mkCLM`), both with underlying function `confPullFun ϕ W g`;
* the consequence used by T4: if `g_n → g` in `𝓓_K`, then `h(τ g_n) → h(τ g)` for every
  distribution `h` (`tendsto_apply_confPullK`, `tendsto_apply_confPullOnCLM`).

The pattern is LQGMetric's `pullK`/`continuous_pullK` (affine maps) and the NIC transport
`NIC.NearIdPair.transportCLM` (global diffeomorphisms); here `ϕ` is only holomorphic on `W`, so
the derivatives are taken within `W` and transferred by `iteratedFDerivWithin_of_isOpen`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Function TopologicalSpace
open scoped Distributions

namespace SmallGammaGeodesics.CC

open LQGMetric

private lemma natCast_le_top_cc12a (j : ℕ) : ((j : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  WithTop.coe_le_coe.2 le_top

section Bound

variable {ϕ : ℂ → ℂ} {W : Set ℂ}

/-- A holomorphic map is real-smooth on its (open) domain of holomorphy. -/
theorem contDiffOn_real_of_differentiableOn (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ϕ W :=
  (hd.contDiffOn hW).restrict_scalars ℝ

/-- The Jacobian `|ϕ'|²` is real-smooth on `W`. -/
theorem contDiffOn_normSq_deriv (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ‖deriv ϕ y‖ ^ 2) W :=
  (contDiff_norm_sq ℝ).comp_contDiffOn (((hd.deriv hW).contDiffOn hW).restrict_scalars ℝ)

/-- On `W`, the pullback is locally the smooth function `|ϕ'|² · (g ∘ ϕ)`, so its iterated
derivatives are the iterated derivatives of that function within `W`. -/
theorem iteratedFDeriv_confPullFun_eq (hW : IsOpen W) (g : ℂ → ℝ) (n : ℕ) {x : ℂ} (hx : x ∈ W) :
    iteratedFDeriv ℝ n (confPullFun ϕ W g) x =
      iteratedFDerivWithin ℝ n (fun y => ‖deriv ϕ y‖ ^ 2 * (g ∘ ϕ) y) W x := by
  rw [iteratedFDerivWithin_of_isOpen n hW hx]
  refine Filter.EventuallyEq.eq_of_nhds ?_
  refine Filter.EventuallyEq.iteratedFDeriv ℝ ?_ n
  filter_upwards [hW.mem_nhds hx] with y hy
  rw [confPullFun_of_mem hy]
  rfl

/-- **Seminorm estimate for the conformal pullback.** On a compact `A ⊆ W`,
`‖Dⁿ(τg)(x)‖ ≤ C · S` whenever `‖Dʲ g‖ ≤ S` for all `j ≤ n`. -/
theorem confPullFun_iteratedFDeriv_bound (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W)
    {A : Set ℂ} (hA : IsCompact A) (hAW : A ⊆ W) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : ℂ → ℝ) (S : ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g →
      (∀ j ≤ n, ∀ y, ‖iteratedFDeriv ℝ j g y‖ ≤ S) →
      ∀ x ∈ A, ‖iteratedFDeriv ℝ n (confPullFun ϕ W g) x‖ ≤ C * S := by
  have hWu : UniqueDiffOn ℝ W := hW.uniqueDiffOn
  have hφ := contDiffOn_real_of_differentiableOn hW hd
  have ha := contDiffOn_normSq_deriv hW hd
  choose C₁ hC₁ using fun j : ℕ => hA.exists_bound_of_continuousOn
    ((hφ.continuousOn_iteratedFDerivWithin (natCast_le_top_cc12a j) hWu).mono hAW)
  choose C₂ hC₂ using fun j : ℕ => hA.exists_bound_of_continuousOn
    ((ha.continuousOn_iteratedFDerivWithin (natCast_le_top_cc12a j) hWu).mono hAW)
  set B := ∑ j ∈ Finset.range (n + 1), (|C₁ j| + |C₂ j|) with hBdef
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => by positivity
  have hbound : ∀ j ≤ n, ∀ x ∈ A,
      ‖iteratedFDerivWithin ℝ j ϕ W x‖ ≤ B ∧
        ‖iteratedFDerivWithin ℝ j (fun y => ‖deriv ϕ y‖ ^ 2) W x‖ ≤ B := by
    intro j hj x hx
    have hs : |C₁ j| + |C₂ j| ≤ B := Finset.single_le_sum
      (f := fun j => |C₁ j| + |C₂ j|) (fun _ _ => by positivity)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
    constructor
    · exact (hC₁ j x hx).trans ((le_abs_self _).trans (by linarith [abs_nonneg (C₂ j)]))
    · exact (hC₂ j x hx).trans ((le_abs_self _).trans (by linarith [abs_nonneg (C₁ j)]))
  set E := 1 + B with hEdef
  have hE : 1 ≤ E := by rw [hEdef]; linarith
  refine ⟨∑ k ∈ Finset.range (n + 1),
    (n.choose k : ℝ) * B * ((n - k).factorial * E ^ (n - k)),
    Finset.sum_nonneg fun _ _ => by positivity, ?_⟩
  intro g S hg hS x hx
  have hxW : x ∈ W := hAW hx
  rw [iteratedFDeriv_confPullFun_eq hW g n hxW]
  refine (norm_iteratedFDerivWithin_mul_le ha (hg.comp_contDiffOn hφ) hWu hxW
    (natCast_le_top_cc12a n)).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  have h₁ : ‖iteratedFDerivWithin ℝ k (fun y => ‖deriv ϕ y‖ ^ 2) W x‖ ≤ B :=
    (hbound k hk' x hx).2
  have h₂ : ‖iteratedFDerivWithin ℝ (n - k) (g ∘ ϕ) W x‖ ≤
      (n - k).factorial * S * E ^ (n - k) := by
    refine norm_iteratedFDerivWithin_comp_le (hg.contDiffOn (s := univ)) hφ
      (natCast_le_top_cc12a _) uniqueDiffOn_univ hWu (mapsTo_univ _ _) hxW
      (fun j hj => ?_) (fun j hj₁ hjk => ?_)
    · rw [iteratedFDerivWithin_univ]
      exact hS j (hj.trans (Nat.sub_le n k)) _
    · refine ((hbound j (hjk.trans (Nat.sub_le n k)) x hx).1).trans ?_
      calc B ≤ E := by rw [hEdef]; linarith
        _ = E ^ 1 := (pow_one E).symm
        _ ≤ E ^ j := pow_le_pow_right₀ hE hj₁
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS 0 (Nat.zero_le _) x)
  calc (n.choose k : ℝ) * ‖iteratedFDerivWithin ℝ k (fun y => ‖deriv ϕ y‖ ^ 2) W x‖ *
        ‖iteratedFDerivWithin ℝ (n - k) (g ∘ ϕ) W x‖
      ≤ (n.choose k : ℝ) * B * ((n - k).factorial * S * E ^ (n - k)) := by gcongr
    _ = (n.choose k : ℝ) * B * ((n - k).factorial * E ^ (n - k)) * S := by ring

end Bound

/-! ## Linearity of the function-level pullback -/

section Linear

variable {ϕ : ℂ → ℂ} {W : Set ℂ}

theorem confPullFun_add (g₁ g₂ : ℂ → ℝ) :
    confPullFun ϕ W (g₁ + g₂) = confPullFun ϕ W g₁ + confPullFun ϕ W g₂ := by
  funext x
  by_cases hx : x ∈ W
  · simp only [confPullFun_of_mem hx, Pi.add_apply, mul_add]
  · simp only [confPullFun_of_notMem hx, Pi.add_apply, add_zero]

theorem confPullFun_smul (c : ℝ) (g : ℂ → ℝ) :
    confPullFun ϕ W (c • g) = c • confPullFun ϕ W g := by
  funext x
  by_cases hx : x ∈ W
  · simp only [confPullFun_of_mem hx, Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [confPullFun_of_notMem hx, Pi.smul_apply, smul_zero]

end Linear

/-! ## T3: the pullback `𝓓_K → 𝓓_{ψ(K)}` and `𝓓(O) → 𝓓(ℂ)` -/

section CLM

variable {ϕ : ℂ → ℂ} {W : Set ℂ}

theorem invFunOn_leftInv (hi : InjOn ϕ W) : ∀ z ∈ W, invFunOn ϕ W (ϕ z) = z :=
  fun _ hz => hi.leftInvOn_invFunOn hz

/-- The compact `ψ(K)` (with `ψ = invFunOn ϕ W`) carrying the pullbacks of test functions
supported in a compact `K ⊆ ϕ(W)`. -/
def confK (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W) (K : Compacts ℂ)
    (hK : (K : Set ℂ) ⊆ ϕ '' W) : Compacts ℂ :=
  ⟨invFunOn ϕ W '' K, K.isCompact.image_of_continuousOn
    ((continuousOn_leftInv hW hd hi (invFunOn_leftInv hi)).mono hK)⟩

theorem coe_confK (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W)
    (K : Compacts ℂ) (hK : (K : Set ℂ) ⊆ ϕ '' W) :
    (confK hW hd hi K hK : Set ℂ) = invFunOn ϕ W '' K :=
  rfl

theorem confK_subset (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W)
    (K : Compacts ℂ) (hK : (K : Set ℂ) ⊆ ϕ '' W) : (confK hW hd hi K hK : Set ℂ) ⊆ W := by
  rintro _ ⟨y, hy, rfl⟩
  exact leftInv_mem (invFunOn_leftInv hi) (hK hy)

/-- The pullback of a function supported in `K` vanishes off `ψ(K)`. -/
theorem confPullFun_eq_zero_of_notMem_confK (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W)
    (hi : InjOn ϕ W) (K : Compacts ℂ) (hK : (K : Set ℂ) ⊆ ϕ '' W) {g : ℂ → ℝ}
    (hg : tsupport g ⊆ K) {x : ℂ} (hx : x ∉ (confK hW hd hi K hK : Set ℂ)) :
    confPullFun ϕ W g x = 0 :=
  confPullFun_eq_zero (invFunOn_leftInv hi) fun hx' => hx (image_mono hg hx')

/-- **T3 (CC0 D17.2).** The conformal pullback as a continuous linear map
`𝓓_K(ℂ) → 𝓓_{ψ(K)}(ℂ)`, for a compact `K ⊆ ϕ(W)`. -/
def confPullK (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W) (K : Compacts ℂ)
    (hK : (K : Set ℂ) ⊆ ϕ '' W) :
    𝓓^{⊤}_{K}(ℂ, ℝ) →L[ℝ] 𝓓^{⊤}_{confK hW hd hi K hK}(ℂ, ℝ) :=
  ContDiffMapSupportedIn.mkCLM ℝ (fun f => confPullFun ϕ W f)
    (fun f g x => by
      change confPullFun ϕ W (⇑f + ⇑g) x = _
      rw [confPullFun_add]
      rfl)
    (fun c f x => by
      change confPullFun ϕ W (c • ⇑f) x = _
      rw [confPullFun_smul]
      rfl)
    (fun f => contDiff_confPullFun hW hd hi f.contDiff f.hasCompactSupport
      (f.tsupport_subset.trans hK))
    (fun f x hx => confPullFun_eq_zero_of_notMem_confK hW hd hi K hK f.tsupport_subset hx)
    (fun i _ => by
      obtain ⟨C, hC, hbound⟩ := confPullFun_iteratedFDeriv_bound hW hd
        (confK hW hd hi K hK).isCompact (confK_subset hW hd hi K hK) i
      refine ⟨Finset.Iic i, C, hC, fun f x hx => ?_⟩
      refine hbound f _ f.contDiff (fun j hj y => ?_) x hx
      exact (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ).trans
        (Seminorm.le_def.1 (Finset.le_sup
          (f := ContDiffMapSupportedIn.seminorm ℝ ℂ ℝ ⊤ K) (Finset.mem_Iic.2 hj)) f))

@[simp] theorem coe_confPullK (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W)
    (K : Compacts ℂ) (hK : (K : Set ℂ) ⊆ ϕ '' W) (f : 𝓓^{⊤}_{K}(ℂ, ℝ)) :
    ⇑(confPullK hW hd hi K hK f) = confPullFun ϕ W f :=
  rfl

/-- The pullback of a test function on an open `O ⊆ ϕ(W)`, as a test function on `ℂ`. -/
def confPullOn (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W) (O : Opens ℂ)
    (hO : (O : Set ℂ) ⊆ ϕ '' W) (φ : TestOn O) : TestC where
  toFun := confPullFun ϕ W φ
  contDiff' := contDiff_confPullFun hW hd hi φ.contDiff φ.hasCompactSupport
    (φ.tsupport_subset.trans hO)
  hasCompactSupport' := hasCompactSupport_confPullFun hW hd hi φ.hasCompactSupport
    (φ.tsupport_subset.trans hO)
  tsupport_subset' := subset_univ _

theorem coe_confPullOn (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W)
    (O : Opens ℂ) (hO : (O : Set ℂ) ⊆ ϕ '' W) (φ : TestOn O) :
    ⇑(confPullOn hW hd hi O hO φ) = confPullFun ϕ W φ :=
  rfl

/-- **T3, on `𝓓(O)`.** The conformal pullback as a continuous linear map `𝓓(O) → 𝓓(ℂ)`, for an
open `O ⊆ ϕ(W)`: on each `𝓓_K` (`K ⊆ O` compact) it factors through the continuous `confPullK`. -/
def confPullOnCLM (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W) (O : Opens ℂ)
    (hO : (O : Set ℂ) ⊆ ϕ '' W) : TestOn O →L[ℝ] TestC :=
  TestFunction.mkCLM ℝ (confPullOn hW hd hi O hO)
    (fun φ ψ => by
      ext x
      change confPullFun ϕ W (⇑φ + ⇑ψ) x = _
      rw [confPullFun_add]
      rfl)
    (fun c φ => by
      ext x
      change confPullFun ϕ W (c • ⇑φ) x = _
      rw [confPullFun_smul]
      rfl)
    (fun K hK => by
      have hKW : (K : Set ℂ) ⊆ ϕ '' W := hK.trans hO
      have hK' : (confK hW hd hi K hKW : Set ℂ) ⊆ ((⊤ : Opens ℂ) : Set ℂ) := subset_univ _
      have he : confPullOn hW hd hi O hO ∘ TestFunction.ofSupportedIn hK =
          TestFunction.ofSupportedInCLM ℝ hK' ∘ confPullK hW hd hi K hKW := by
        funext f
        ext x
        rfl
      rw [he]
      exact (TestFunction.ofSupportedInCLM ℝ hK').continuous.comp
        (confPullK hW hd hi K hKW).continuous)

@[simp] theorem confPullOnCLM_apply (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W)
    (hi : InjOn ϕ W) (O : Opens ℂ) (hO : (O : Set ℂ) ⊆ ϕ '' W) (φ : TestOn O) :
    confPullOnCLM hW hd hi O hO φ = confPullOn hW hd hi O hO φ :=
  rfl

theorem coe_confPullOnCLM (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W)
    (O : Opens ℂ) (hO : (O : Set ℂ) ⊆ ϕ '' W) (φ : TestOn O) :
    ⇑(confPullOnCLM hW hd hi O hO φ) = confPullFun ϕ W φ :=
  rfl

/-- **T3, consequence.** If `g_i → g` in `𝓓_K`, then `h(τ g_i) → h(τ g)` for every distribution `h`
(the pullbacks taken as test functions on `ℂ`). -/
theorem tendsto_apply_confPullK (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W)
    (K : Compacts ℂ) (hK : (K : Set ℂ) ⊆ ϕ '' W) {ι : Type*} {l : Filter ι}
    {g : ι → 𝓓^{⊤}_{K}(ℂ, ℝ)} {g₀ : 𝓓^{⊤}_{K}(ℂ, ℝ)} (hg : Tendsto g l (𝓝 g₀)) (h : DistC) :
    Tendsto (fun i => h (TestFunction.ofSupportedIn
        (subset_univ _ : (confK hW hd hi K hK : Set ℂ) ⊆ ((⊤ : Opens ℂ) : Set ℂ))
        (confPullK hW hd hi K hK (g i)))) l
      (𝓝 (h (TestFunction.ofSupportedIn
        (subset_univ _ : (confK hW hd hi K hK : Set ℂ) ⊆ ((⊤ : Opens ℂ) : Set ℂ))
        (confPullK hW hd hi K hK g₀)))) := by
  have hc : Continuous fun f : 𝓓^{⊤}_{K}(ℂ, ℝ) => h (TestFunction.ofSupportedIn
      (subset_univ _ : (confK hW hd hi K hK : Set ℂ) ⊆ ((⊤ : Opens ℂ) : Set ℂ))
      (confPullK hW hd hi K hK f)) :=
    (map_continuous h).comp ((TestFunction.continuous_ofSupportedIn _).comp
      (confPullK hW hd hi K hK).continuous)
  exact (hc.tendsto g₀).comp hg

/-- **T3, consequence, on `𝓓(O)`.** If `g_i → g` in `𝓓_K` with `K ⊆ O`, then
`h(τ g_i) → h(τ g)` for every distribution `h`. -/
theorem tendsto_apply_confPullOnCLM (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W)
    (hi : InjOn ϕ W) (O : Opens ℂ) (hO : (O : Set ℂ) ⊆ ϕ '' W) {K : Compacts ℂ}
    (hK : (K : Set ℂ) ⊆ O) {ι : Type*} {l : Filter ι} {g : ι → 𝓓^{⊤}_{K}(ℂ, ℝ)}
    {g₀ : 𝓓^{⊤}_{K}(ℂ, ℝ)} (hg : Tendsto g l (𝓝 g₀)) (h : DistC) :
    Tendsto (fun i => h (confPullOnCLM hW hd hi O hO (TestFunction.ofSupportedIn hK (g i)))) l
      (𝓝 (h (confPullOnCLM hW hd hi O hO (TestFunction.ofSupportedIn hK g₀)))) := by
  have hc : Continuous fun f : 𝓓^{⊤}_{K}(ℂ, ℝ) =>
      h (confPullOnCLM hW hd hi O hO (TestFunction.ofSupportedIn hK f)) :=
    (map_continuous h).comp ((confPullOnCLM hW hd hi O hO).continuous.comp
      (TestFunction.continuous_ofSupportedIn hK))
  exact (hc.tendsto g₀).comp hg

end CLM

/-! ## T3 for the chosen pullback `confPull` (packet form: `IsConfNbhd ϕ W V`, `K ⊆ ϕ(V)`) -/

section Chosen

variable {ϕ : ℂ → ℂ} {W V : Set ℂ}

/-- The chosen pullback `confPull` (`Core/Interfaces.lean`) of a test function supported in a
compact `K ⊆ ϕ(V)` is `confPullK`, viewed in `𝓓(ℂ)`. -/
theorem confPull_ofSupportedIn_eq (hϕ : IsConfNbhd ϕ W V) (K : Compacts ℂ)
    (hK : (K : Set ℂ) ⊆ ϕ '' V) (f : 𝓓^{⊤}_{K}(ℂ, ℝ)) :
    confPull ϕ W (TestFunction.ofSupportedIn
        (subset_univ _ : (K : Set ℂ) ⊆ ((⊤ : Opens ℂ) : Set ℂ)) f) =
      TestFunction.ofSupportedIn
        (subset_univ _ : (confK hϕ.isOpen_W hϕ.differentiableOn hϕ.injOn K
          (hK.trans hϕ.image_subset) : Set ℂ) ⊆ ((⊤ : Opens ℂ) : Set ℂ))
        (confPullK hϕ.isOpen_W hϕ.differentiableOn hϕ.injOn K (hK.trans hϕ.image_subset) f) :=
  confPull_eq hϕ (f.tsupport_subset.trans hK) fun _ => rfl

/-- **T3 (packet form).** For `IsConfNbhd ϕ W V` and a compact `K ⊆ ϕ(V)`, the chosen conformal
pullback `g ↦ confPull ϕ W g` restricted to test functions supported in `K` is continuous from
`𝓓_K` into `𝓓(ℂ)`. -/
theorem continuous_confPull_ofSupportedIn (hϕ : IsConfNbhd ϕ W V) (K : Compacts ℂ)
    (hK : (K : Set ℂ) ⊆ ϕ '' V) :
    Continuous fun f : 𝓓^{⊤}_{K}(ℂ, ℝ) => confPull ϕ W (TestFunction.ofSupportedIn
      (subset_univ _ : (K : Set ℂ) ⊆ ((⊤ : Opens ℂ) : Set ℂ)) f) := by
  have he : (fun f : 𝓓^{⊤}_{K}(ℂ, ℝ) => confPull ϕ W (TestFunction.ofSupportedIn
      (subset_univ _ : (K : Set ℂ) ⊆ ((⊤ : Opens ℂ) : Set ℂ)) f)) =
      fun f => TestFunction.ofSupportedIn
        (subset_univ _ : (confK hϕ.isOpen_W hϕ.differentiableOn hϕ.injOn K
          (hK.trans hϕ.image_subset) : Set ℂ) ⊆ ((⊤ : Opens ℂ) : Set ℂ))
        (confPullK hϕ.isOpen_W hϕ.differentiableOn hϕ.injOn K (hK.trans hϕ.image_subset) f) :=
    funext (confPull_ofSupportedIn_eq hϕ K hK)
  rw [he]
  exact (TestFunction.continuous_ofSupportedIn _).comp (confPullK _ _ _ K _).continuous

/-- **T3, consequence (packet form).** If `g_i → g` in `𝓓_K` with `K ⊆ ϕ(V)` compact, then
`h(τ g_i) → h(τ g)` for every distribution `h`, with `τ = confPull ϕ W`. -/
theorem tendsto_apply_confPull (hϕ : IsConfNbhd ϕ W V) (K : Compacts ℂ)
    (hK : (K : Set ℂ) ⊆ ϕ '' V) {ι : Type*} {l : Filter ι} {g : ι → 𝓓^{⊤}_{K}(ℂ, ℝ)}
    {g₀ : 𝓓^{⊤}_{K}(ℂ, ℝ)} (hg : Tendsto g l (𝓝 g₀)) (h : DistC) :
    Tendsto (fun i => h (confPull ϕ W (TestFunction.ofSupportedIn
        (subset_univ _ : (K : Set ℂ) ⊆ ((⊤ : Opens ℂ) : Set ℂ)) (g i)))) l
      (𝓝 (h (confPull ϕ W (TestFunction.ofSupportedIn
        (subset_univ _ : (K : Set ℂ) ⊆ ((⊤ : Opens ℂ) : Set ℂ)) g₀)))) :=
  (((map_continuous h).comp (continuous_confPull_ofSupportedIn hϕ K hK)).tendsto g₀).comp hg

end Chosen

end SmallGammaGeodesics.CC
