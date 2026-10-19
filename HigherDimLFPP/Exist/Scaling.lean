import HigherDimLFPP.Field.SymmetryLaw
import HigherDimLFPP.Paths.Measurable

/-!
# Scaling in law of band fields and internal LFPP distances (packet P-X5b, target T1)

Source: DGZ arXiv:2310.03996, Lemma 2.2(2),(4) and Lemma 2.5; planning audit HA5, Details D14
(used in D4, proof of Lemma 3.4′, and in D9, the site model of Lemma 3.3).

Notation (HA5): `h_{m,n} = H_{2^{-n},2^{-m}}` is the band field with scales between `2^{-n}` and
`2^{-m}`, and `h_n = h_{0,n} = H_{2^{-n},1}`. Band fields are continuous versions
(`IsBandVersion`) over a white noise; all identities in law below compare versions over **two
arbitrary white noises**, possibly on different probability spaces, so they do not depend on the
realization (law transfer, `HigherDimLFPP/Field/LawTransfer.lean`).

* Fields (DGZ Lemma 2.2(4)):
  - `IsBandVersion.map_dyadic_eq`: `(h_{j,j+k}(z))_z =ᵈ (h_k(2^j z))_z`;
  - `IsBandVersion.map_band_scaling_eq` (the packet's form):
    `(h_{n-m,n}(x))_x =ᵈ (h_m(2^{n-m} x))_x` for `m ≤ n`.
* Internal distances under a similarity `T z = x₀ + r • O z` (`r > 0`, `O` a linear isometry,
  DGZ Lemma 2.5; HA5 D14): for an open set `V`, a version `H` of `H_{a,b}` and a version `H'` of
  `H_{a/r,b/r}` (`0 < a`),
  - `IsBandVersion.map_lfppDistOn_sim_eq`: jointly in the pair of points,
    `(D_{T V}(T x, T y)(H))_{x,y} =ᵈ (r · D_V(x, y)(H'))_{x,y}`;
  - `IsBandVersion.map_lfppDistOn_sim_cube_eq`: `D_{T U}(x₀, T e₁)(H) =ᵈ r · D^ξ(H')` with the
    frozen distance `D^ξ = lfppDistance d ξ` (`U = (-2,2)^d`), the form used for the open sites
    of DGZ Lemma 3.3 (HA5 D9: translation, scaling by `2^{-j}`, a signed permutation).
* Dyadic forms:
  - `IsBandVersion.map_lfppDistOn_dyadic_eq` (DGZ Lemma 2.5(2)):
    `(D_V(x, y)(h_{j,j+k}))_{x,y} =ᵈ (2^{-j} D_{2^j V}(2^j x, 2^j y)(h_k))_{x,y}`, and the same in
    the packet's indexing `IsBandVersion.map_lfppDistOn_band_scaling_eq` (`h_{n-m,n}` and `h_m`);
  - `IsBandVersion.map_lfppDistOn_dyadic_cube_eq`: for `T z = x₀ + 2^{-j} • O z`,
    `D_{T U}(x₀, T e₁)(h_{j,j+k}) =ᵈ 2^{-j} D^ξ(h_k)`.

The deterministic input is the path transport `lfppDistOn_sim_image` (packet P-X1); the
probabilistic input is `IsBandVersion.map_comp_sim_eq_of_measurable` (packet P-X2) together with
the Borel measurability of `φ ↦ D_V(x, y)(φ)` on `C(ℝ^d, ℝ)` for open `V`
(`measurable_lfppDistOn_continuousMap`, packet P-X1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace HigherDimLFPP

variable {d : ℕ} {κ : Rd d → ℝ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} {W : WN d → Ω → ℝ} {W' : WN d → Ω' → ℝ}

/-! ### Dyadic arithmetic -/

/-- `2^{-(j+k)} / 2^{-j} = 2^{-k}`. -/
theorem dyadic_div_dyadic (j k : ℕ) :
    ((2 : ℝ) ^ (j + k))⁻¹ / ((2 : ℝ) ^ j)⁻¹ = ((2 : ℝ) ^ k)⁻¹ := by
  rw [pow_add]
  field_simp

/-- `2^{-k} / 2^j = 2^{-(j+k)}`. -/
theorem dyadic_div_pow (j k : ℕ) :
    ((2 : ℝ) ^ k)⁻¹ / (2 : ℝ) ^ j = ((2 : ℝ) ^ (j + k))⁻¹ := by
  rw [pow_add]
  field_simp

/-- `1 / 2^j = 2^{-j}`. -/
theorem one_div_dyadic (j : ℕ) : (1 : ℝ) / (2 : ℝ) ^ j = ((2 : ℝ) ^ j)⁻¹ := one_div _

/-- `2^{-j} / 2^{-j} = 1`. -/
theorem dyadic_div_self (j : ℕ) : ((2 : ℝ) ^ j)⁻¹ / ((2 : ℝ) ^ j)⁻¹ = 1 :=
  div_self (inv_ne_zero (pow_ne_zero j two_ne_zero))

/-- `0 < 2^{-n}`. -/
theorem dyadic_pos (n : ℕ) : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := by positivity

/-! ### Measurability of distance functionals -/

/-- The family of internal distances `(x, y) ↦ c · D_V(x, y)(φ)` is a Borel measurable function
of `φ ∈ C(ℝ^d, ℝ)` (product σ-algebra on `Rd d × Rd d → ℝ`), for open `V`. -/
theorem measurable_lfppDistOn_family {V : Set (Rd d)} (hV : IsOpen V) (ξ c : ℝ) :
    Measurable fun f : C(Rd d, ℝ) => fun q : Rd d × Rd d => c * lfppDistOn ξ f V q.1 q.2 :=
  measurable_pi_iff.2 fun q => (measurable_lfppDistOn_continuousMap hV ξ q.1 q.2).const_mul c

/-- The frozen LFPP distance `φ ↦ D^ξ(φ)` is Borel measurable on `C(ℝ^d, ℝ)` (packet P-X1). -/
theorem measurable_lfppDistance_continuousMap (ξ : ℝ) :
    Measurable fun f : C(Rd d, ℝ) => lfppDistance d ξ f := by
  simp_rw [lfppDistance_eq_lfppDistOn]
  exact measurable_lfppDistOn_continuousMap (isOpen_cube d) ξ 0 (e₁ d)

namespace IsBandVersion

/-- Rewriting the band endpoints of a version along equalities. -/
theorem congr_band {a b a' b' : ℝ} {H : Rd d → Ω → ℝ} (hH : IsBandVersion P W κ a b H)
    (ha : a = a') (hb : b = b') : IsBandVersion P W κ a' b' H := by
  subst ha
  subst hb
  exact hH

/-! ### Fields -/

/-- **Dyadic scaling in law of band fields** (DGZ Lemma 2.2(4); HA5 D14): a version `H` of
`h_{j,j+k} = H_{2^{-(j+k)},2^{-j}}` over `W` and a version `H'` of `h_k = H_{2^{-k},1}` over any
white noise `W'` satisfy `(H(z))_z =ᵈ (H'(2^j z))_z` (law on `Rd d → ℝ`). -/
theorem map_dyadic_eq {j k : ℕ} {H : Rd d → Ω → ℝ} {H' : Rd d → Ω' → ℝ}
    (hH : IsBandVersion P W κ ((2 : ℝ) ^ (j + k))⁻¹ ((2 : ℝ) ^ j)⁻¹ H)
    (hH' : IsBandVersion P' W' κ ((2 : ℝ) ^ k)⁻¹ 1 H') (hW : IsWhiteNoise P W)
    (hW' : IsWhiteNoise P' W') (hκ : IsLFPPKernel κ) :
    P.map (fun ω z => H z ω) = P'.map (fun ω z => H' ((2 : ℝ) ^ j • z) ω) :=
  (hH'.map_smul_eq (hH.congr_band (dyadic_div_pow j k).symm (one_div_dyadic j).symm) hW' hW hκ
    (by positivity) (dyadic_pos k)).symm

/-- **Scaling in law, the packet's form** (DGZ Lemma 2.2(4), as used in Lemma 3.4): for `m ≤ n`,
`(h_{n-m,n}(x))_x =ᵈ (h_m(2^{n-m} x))_x`, where `h_{n-m,n} = H_{2^{-n},2^{-(n-m)}}` and
`h_m = H_{2^{-m},1}`, for versions over any two white noises. -/
theorem map_band_scaling_eq {m n : ℕ} (hmn : m ≤ n) {H : Rd d → Ω → ℝ} {H' : Rd d → Ω' → ℝ}
    (hH : IsBandVersion P W κ ((2 : ℝ) ^ n)⁻¹ ((2 : ℝ) ^ (n - m))⁻¹ H)
    (hH' : IsBandVersion P' W' κ ((2 : ℝ) ^ m)⁻¹ 1 H') (hW : IsWhiteNoise P W)
    (hW' : IsWhiteNoise P' W') (hκ : IsLFPPKernel κ) :
    P.map (fun ω z => H z ω) = P'.map (fun ω z => H' ((2 : ℝ) ^ (n - m) • z) ω) := by
  have e : n = (n - m) + m := (Nat.sub_add_cancel hmn).symm
  exact map_dyadic_eq (hH.congr_band (by rw [← e]) rfl) hH' hW hW' hκ

/-! ### Internal distances -/

/-- **Similarity invariance in law of internal distances** (DGZ Lemma 2.5; HA5 D14). Let
`T z = x₀ + r • O z` (`r > 0`, `O` a linear isometry), `V` open, `H` a version of `H_{a,b}` over
`W` and `H'` a version of `H_{a/r,b/r}` over any white noise `W'` (`0 < a`). Then, jointly in the
pair of points, `(D_{T V}(T x, T y)(H))_{x,y} =ᵈ (r · D_V(x, y)(H'))_{x,y}`. -/
theorem map_lfppDistOn_sim_eq {a b r : ℝ} {H : Rd d → Ω → ℝ} {H' : Rd d → Ω' → ℝ}
    (hH : IsBandVersion P W κ a b H) (hH' : IsBandVersion P' W' κ (a / r) (b / r) H')
    (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') (hκ : IsLFPPKernel κ)
    (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) (hr : 0 < r) (ha : 0 < a) (ξ : ℝ) {V : Set (Rd d)}
    (hV : IsOpen V) :
    P.map (fun ω (q : Rd d × Rd d) => lfppDistOn ξ (fun z => H z ω)
        ((fun z => x₀ + r • O z) '' V) (x₀ + r • O q.1) (x₀ + r • O q.2)) =
      P'.map (fun ω (q : Rd d × Rd d) => r * lfppDistOn ξ (fun z => H' z ω) V q.1 q.2) := by
  have h := hH.map_comp_sim_eq_of_measurable hH' hW hW' hκ O x₀ hr ha
    (G := fun f (q : Rd d × Rd d) => r * lfppDistOn ξ f V q.1 q.2)
    (measurable_lfppDistOn_family hV ξ r)
  refine Eq.trans ?_ h
  congr 1
  funext ω q
  exact lfppDistOn_sim_image O x₀ hr ξ (fun z => H z ω) V q.1 q.2

/-- **Similarity invariance in law, frozen form** (HA5 D9, site model; D14): for
`T z = x₀ + r • O z`, the internal distance from `x₀ = T 0` to `T e₁` in `T U` (`U = (-2,2)^d`)
of a version of `H_{a,b}` has the law of `r · D^ξ(H')` for a version `H'` of `H_{a/r,b/r}` over
any white noise. -/
theorem map_lfppDistOn_sim_cube_eq {a b r : ℝ} {H : Rd d → Ω → ℝ} {H' : Rd d → Ω' → ℝ}
    (hH : IsBandVersion P W κ a b H) (hH' : IsBandVersion P' W' κ (a / r) (b / r) H')
    (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') (hκ : IsLFPPKernel κ)
    (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) (hr : 0 < r) (ha : 0 < a) (ξ : ℝ) :
    P.map (fun ω => lfppDistOn ξ (fun z => H z ω) ((fun z => x₀ + r • O z) '' cube d) x₀
        (x₀ + r • O (e₁ d))) =
      P'.map (fun ω => r * lfppDistance d ξ (fun z => H' z ω)) := by
  have hG : Measurable fun f : C(Rd d, ℝ) => r * lfppDistance d ξ f :=
    (measurable_lfppDistance_continuousMap ξ).const_mul r
  have h := hH.map_comp_sim_eq_of_measurable hH' hW hW' hκ O x₀ hr ha
    (G := fun f => r * lfppDistance d ξ f) hG
  refine Eq.trans ?_ h
  congr 1
  funext ω
  have e := lfppDistOn_sim_image O x₀ hr ξ (fun z => H z ω) (cube d) 0 (e₁ d)
  rw [map_zero, smul_zero, add_zero] at e
  rw [e, lfppDistance_eq_lfppDistOn]

/-- **Dyadic scaling in law of internal distances** (DGZ Lemma 2.5(2); HA5 D14): for an open set
`V`, a version `H` of `h_{j,j+k} = H_{2^{-(j+k)},2^{-j}}` and a version `H'` of `h_k = H_{2^{-k},1}`
over any white noise, jointly in the pair of points,
`(D_V(x, y)(H))_{x,y} =ᵈ (2^{-j} D_{2^j V}(2^j x, 2^j y)(H'))_{x,y}`. -/
theorem map_lfppDistOn_dyadic_eq {j k : ℕ} {H : Rd d → Ω → ℝ} {H' : Rd d → Ω' → ℝ}
    (hH : IsBandVersion P W κ ((2 : ℝ) ^ (j + k))⁻¹ ((2 : ℝ) ^ j)⁻¹ H)
    (hH' : IsBandVersion P' W' κ ((2 : ℝ) ^ k)⁻¹ 1 H') (hW : IsWhiteNoise P W)
    (hW' : IsWhiteNoise P' W') (hκ : IsLFPPKernel κ) (ξ : ℝ) {V : Set (Rd d)}
    (hV : IsOpen V) :
    P.map (fun ω (q : Rd d × Rd d) => lfppDistOn ξ (fun z => H z ω) V q.1 q.2) =
      P'.map (fun ω (q : Rd d × Rd d) => ((2 : ℝ) ^ j)⁻¹ *
        lfppDistOn ξ (fun z => H' z ω) ((fun z => (2 : ℝ) ^ j • z) '' V) ((2 : ℝ) ^ j • q.1)
          ((2 : ℝ) ^ j • q.2)) := by
  have hr : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  -- the law of `G(H' ∘ T)` for `T z = 2^j z` and `G f = (D_V(x, y)(f))_{x,y}`
  have h := hH'.map_comp_sim_eq_of_measurable (hH.congr_band (dyadic_div_pow j k).symm
      (one_div_dyadic j).symm) hW' hW hκ (LinearIsometryEquiv.refl ℝ (Rd d)) 0 hr (dyadic_pos k)
      (G := fun f (q : Rd d × Rd d) => 1 * lfppDistOn ξ f V q.1 q.2)
      (measurable_lfppDistOn_family hV ξ 1)
  simp only [LinearIsometryEquiv.coe_refl, id, zero_add, one_mul] at h
  refine h.symm.trans ?_
  congr 1
  funext ω q
  -- `D_{T V}(T x, T y)(H') = 2^j · D_V(x, y)(H' ∘ T)`
  have e := lfppDistOn_smul hr ξ (fun z => H' z ω) ((fun z => (2 : ℝ) ^ j • z) '' V) q.1 q.2
  have hpre : (fun z : Rd d => (2 : ℝ) ^ j • z) ⁻¹' ((fun z => (2 : ℝ) ^ j • z) '' V) = V :=
    preimage_image_eq V (smul_right_injective (Rd d) hr.ne')
  rw [hpre] at e
  rw [e, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]

/-- **Scaling in law of internal distances, the packet's form** (DGZ Lemma 2.5(2)): for `m ≤ n`,
an open set `V`, a version `H` of `h_{n-m,n} = H_{2^{-n},2^{-(n-m)}}` and a version `H'` of
`h_m = H_{2^{-m},1}` over any white noise, jointly in the pair of points,
`(D_V(x, y)(H))_{x,y} =ᵈ (2^{-(n-m)} D_{2^{n-m} V}(2^{n-m} x, 2^{n-m} y)(H'))_{x,y}`. -/
theorem map_lfppDistOn_band_scaling_eq {m n : ℕ} (hmn : m ≤ n) {H : Rd d → Ω → ℝ}
    {H' : Rd d → Ω' → ℝ} (hH : IsBandVersion P W κ ((2 : ℝ) ^ n)⁻¹ ((2 : ℝ) ^ (n - m))⁻¹ H)
    (hH' : IsBandVersion P' W' κ ((2 : ℝ) ^ m)⁻¹ 1 H') (hW : IsWhiteNoise P W)
    (hW' : IsWhiteNoise P' W') (hκ : IsLFPPKernel κ) (ξ : ℝ) {V : Set (Rd d)}
    (hV : IsOpen V) :
    P.map (fun ω (q : Rd d × Rd d) => lfppDistOn ξ (fun z => H z ω) V q.1 q.2) =
      P'.map (fun ω (q : Rd d × Rd d) => ((2 : ℝ) ^ (n - m))⁻¹ *
        lfppDistOn ξ (fun z => H' z ω) ((fun z => (2 : ℝ) ^ (n - m) • z) '' V)
          ((2 : ℝ) ^ (n - m) • q.1) ((2 : ℝ) ^ (n - m) • q.2)) := by
  have e : n = (n - m) + m := (Nat.sub_add_cancel hmn).symm
  exact map_lfppDistOn_dyadic_eq (hH.congr_band (by rw [← e]) rfl) hH' hW hW' hκ ξ hV

/-- **Dyadic site-model form** (HA5 D9, D14): for `T z = x₀ + 2^{-j} • O z` (`O` a linear
isometry, e.g. a signed permutation), a version `H` of `h_{j,j+k} = H_{2^{-(j+k)},2^{-j}}` and a
version `H'` of `h_k = H_{2^{-k},1}` over any white noise,
`D_{T U}(x₀, T e₁)(H) =ᵈ 2^{-j} D^ξ(H')`. -/
theorem map_lfppDistOn_dyadic_cube_eq {j k : ℕ} {H : Rd d → Ω → ℝ} {H' : Rd d → Ω' → ℝ}
    (hH : IsBandVersion P W κ ((2 : ℝ) ^ (j + k))⁻¹ ((2 : ℝ) ^ j)⁻¹ H)
    (hH' : IsBandVersion P' W' κ ((2 : ℝ) ^ k)⁻¹ 1 H') (hW : IsWhiteNoise P W)
    (hW' : IsWhiteNoise P' W') (hκ : IsLFPPKernel κ) (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d)
    (ξ : ℝ) :
    P.map (fun ω => lfppDistOn ξ (fun z => H z ω)
        ((fun z => x₀ + ((2 : ℝ) ^ j)⁻¹ • O z) '' cube d) x₀
        (x₀ + ((2 : ℝ) ^ j)⁻¹ • O (e₁ d))) =
      P'.map (fun ω => ((2 : ℝ) ^ j)⁻¹ * lfppDistance d ξ (fun z => H' z ω)) :=
  hH.map_lfppDistOn_sim_cube_eq (hH'.congr_band (dyadic_div_dyadic j k).symm
    (dyadic_div_self j).symm) hW hW' hκ O x₀ (dyadic_pos j) (dyadic_pos (j + k)) ξ

end IsBandVersion

end HigherDimLFPP
