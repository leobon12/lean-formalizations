import InteractingSLE.Spec.Supplement.LP2Path
import InteractingSLE.Spec.Zhan.AvoidMart

/-!
# Lemma LP2: the localized Lyapunov supermartingale

Packet PROVE-LP16. For the canonical single-right-seed evolution and a passive point `x > 0`, the Lyapunov
observable `F = obs k ρ a (aρ/2) θ` of `LP2Calc.lean` along the coordinates `((g_t(x), V_t), B_t)` is localized at the
exit time `σ_{n,M}` of the compact set `{dist(·, region^c) ≥ 1/(n+1), ‖·‖ ≤ n, X ≤ M}` (AvoidMart's `locStop` with
`Φ = gapX`, `L = M`). The coordinates live on all paths:

* `IsGood`, `exists_goodSet`: a measurable full-measure set `G` of good paths (infinite lifetime, continuous Brownian
  path, the frozen pathwise equations);
* `modProc G X`: `X` on `G`, `0` off `G` (adapted to the null augmentation `𝓖`);
* `tGap G W c x`: the tamed passive gap at level `c` driven by `modProc G W`; `coordΛ = (tGap + W, V)`,
  `coordLam = (realDrift c (tGap), 2/(V − W))`, so `coordΛ_t = coordΛ_0 + ∫₀ᵗ coordLam` on every path.

Main results:

* `martingale_lyap`: the localized Itô martingale of `F` (Itô's formula `Ito.martingale_itoLocalized`);
* `lyap_expect_bounds`: `γ M^{λ−2} E[σ] ≤ x^λ` and `E[F(σ)] ≤ x^λ`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped NNReal ENNReal

namespace InteractingSLE.LP.LP2

open QuantumZipper QuantumZipper.RS

/-! ### Interval integrals of pairs -/

theorem intervalIntegrable_pair {f g : ℝ → ℝ} {a b : ℝ} (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable (fun s => ((f s, g s) : ℝ × ℝ)) volume a b :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

theorem intervalIntegral_pair {f g : ℝ → ℝ} {a b : ℝ} (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b) :
    ∫ s in a..b, ((f s, g s) : ℝ × ℝ) = (∫ s in a..b, f s, ∫ s in a..b, g s) := by
  have hfg := intervalIntegrable_pair hf hg
  ext
  · have h := (ContinuousLinearMap.fst ℝ ℝ ℝ).intervalIntegral_comp_comm hfg
    simpa using h.symm
  · have h := (ContinuousLinearMap.snd ℝ ℝ ℝ).intervalIntegral_comp_comm hfg
    simpa using h.symm

section Good

open scoped Classical

variable {Ω : Type*} {κ ρ : ℝ} {xL ρL : Fin 0 → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin 0 → ℝ≥0 → Ω → ℝ}
  {VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-! ### Good paths -/

/-- A good path of the single-right-seed evolution: infinite lifetime, a continuous Brownian path, and the frozen
pathwise equations. -/
def IsGood (κ ρ : ℝ) (xL ρL : Fin 0 → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 0 → ℝ≥0 → Ω → ℝ)
    (VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : Prop :=
  ζ ω = ⊤ ∧ Continuous (B · ω) ∧
    IsIntegratedSLEPath κ xL (fun _ => 0) ρL (fun _ => ρ) (W · ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (B · ω) ⊤

/-- On a good path the Brownian path starts at `0` (the driving equation at time `0`). -/
theorem IsGood.b_zero (hκ : 0 < κ) {ω : Ω} (h : IsGood κ ρ xL ρL W VL VR B ζ ω) : B 0 ω = 0 := by
  have h1 := w_eq_of_path h.2.2 0
  have hw0 : W 0 ω = 0 := h.2.2.1
  have hv0 : VR 0 0 ω = 0 := h.2.2.2.2.1 0
  simp only [hw0, hv0, mul_zero, sub_zero] at h1
  have hs : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  exact (mul_eq_zero.1 h1.symm).resolve_left hs

theorem IsGood.continuous_w {ω : Ω} (h : IsGood κ ρ xL ρL W VL VR B ζ ω) :
    Continuous (W · ω) :=
  (Sec7.IsIntegratedSLEPath.continuous_w_of_top h.2.2).1

theorem IsGood.continuous_v {ω : Ω} (h : IsGood κ ρ xL ρL W VL VR B ζ ω) :
    Continuous (VR 0 · ω) :=
  continuousOn_univ.1 (by simpa using h.2.2.2.2.2.2.2.1 0)


theorem IsGood.w_le_v {ω : Ω} (h : IsGood κ ρ xL ρL W VL VR B ζ ω) (t : ℝ≥0) : W t ω ≤ VR 0 t ω := by
  obtain ⟨-, -, -, -, -, -, -, -, hwvR, -⟩ := h.2.2
  exact hwvR t ENNReal.coe_lt_top 0

theorem IsGood.intervalIntegrable_gap {ω : Ω} (h : IsGood κ ρ xL ρL W VL VR B ζ ω) (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ => (W s.toNNReal ω - VR 0 s.toNNReal ω)⁻¹) volume 0 t := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hgR, -⟩ := h.2.2
  exact hgR t ENNReal.coe_lt_top 0

theorem IsGood.v_eq {ω : Ω} (h : IsGood κ ρ xL ρL W VL VR B ζ ω) (t : ℝ≥0) :
    VR 0 t ω = ∫ s in (0 : ℝ)..t, 2 / (VR 0 s.toNNReal ω - W s.toNNReal ω) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hvReq, -⟩ := h.2.2
  simpa using hvReq t ENNReal.coe_lt_top 0

theorem IsGood.volume_collision {ω : Ω} (h : IsGood κ ρ xL ρL W VL VR B ζ ω) :
    volume {s : ℝ | 0 ≤ s ∧ ((s.toNNReal : ℝ≥0∞) < ⊤) ∧ W s.toNNReal ω = VR 0 s.toNNReal ω} = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcolR, -⟩ := h.2.2
  exact hcolR 0

/-! ### Processes modified off the good set -/

/-- `X` on `G`, `0` off `G`. -/
def modProc (G : Set Ω) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ := if ω ∈ G then X t ω else 0

theorem modProc_of_mem {G : Set Ω} {X : ℝ≥0 → Ω → ℝ} {ω : Ω} (hω : ω ∈ G) (t : ℝ≥0) :
    modProc G X t ω = X t ω := by simp [modProc, hω]

theorem modProc_of_not_mem {G : Set Ω} {X : ℝ≥0 → Ω → ℝ} {ω : Ω} (hω : ω ∉ G) (t : ℝ≥0) :
    modProc G X t ω = 0 := by simp [modProc, hω]

theorem continuous_modProc {G : Set Ω} {X : ℝ≥0 → Ω → ℝ} (hX : ∀ ω ∈ G, Continuous (X · ω)) (ω : Ω) :
    Continuous (modProc G X · ω) := by
  by_cases hω : ω ∈ G
  · simpa only [modProc_of_mem hω] using hX ω hω
  · simp only [modProc_of_not_mem hω]; exact continuous_const

/-! ### The tamed passive gap and the coordinates -/

/-- The tamed gap of the passive point `x` at level `c`, driven by the modified driver. -/
def tGap (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (c x : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  realTamed (sDrive 1 (modProc G W) ω) c x t

/-- The Itô coordinates `(g_t(x), V_t)` (with the tamed gap). -/
def coordΛ (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ) (c x : ℝ) (t : ℝ≥0) (ω : Ω) :
    ℝ × ℝ :=
  (tGap G W c x t ω + modProc G W t ω, modProc G (VR 0) t ω)

/-- Their density `(realDrift c (X), 2/(V − W))`. -/
def coordLam (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ) (c x : ℝ) (s : ℝ) (ω : Ω) :
    ℝ × ℝ :=
  (realDrift c (tGap G W c x s.toNNReal ω),
    2 / (modProc G (VR 0) s.toNNReal ω - modProc G W s.toNNReal ω))

variable {G : Set Ω} {c x : ℝ}

theorem sDrive_one_modProc (ω : Ω) :
    sDrive 1 (modProc G W) ω = fun s : ℝ => modProc G W s.toNNReal ω := by
  funext s; simp [sDrive]

theorem tGap_eq (hWc : ∀ ω, Continuous (modProc G W · ω)) (hc : 0 < c) (ω : Ω) (t : ℝ≥0) :
    tGap G W c x t ω = x + (∫ r in (0 : ℝ)..t, realDrift c (tGap G W c x r.toNNReal ω)) +
      modProc G W t ω • (-1 : ℝ) :=
  realTamed_sDrive_eq hWc 1 hc x ω t

theorem continuous_tGap (hWc : ∀ ω, Continuous (modProc G W · ω)) (hc : 0 < c) (ω : Ω) :
    Continuous (tGap G W c x · ω) :=
  letI : MeasurableSpace Ω := ⊤
  Dynkin.continuous_of_integralEq hWc (lipschitz_realDrift hc).continuous
    (fun y => by rw [Real.norm_eq_abs]; exact abs_realDrift_le hc y)
    (fun ω t => tGap_eq hWc hc ω t) ω

end Good

section Meas

open scoped Classical

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {κ ρ : ℝ} {xL ρL : Fin 0 → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin 0 → ℝ≥0 → Ω → ℝ}
  {VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω} {c x : ℝ}

theorem ae_isGood (hκ : 0 < κ) (hρ : -2 < ρ)
    (hE : IsIntegratedSLEEvolution κ xL (fun _ => 0) ρL (fun _ => ρ) P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, IsGood κ ρ xL ρL W VL VR B ζ ω := by
  filter_upwards [Sec7.ae_lifetime_eq_top_oneForceRight hκ le_rfl hρ hE, hE.1.1.cont, hE.2.2.2.2]
    with ω hζ hc hp
  rw [hζ] at hp
  exact ⟨hζ, hc, hp⟩

/-- A measurable full-measure set inside an almost sure event. -/
theorem exists_measurableSet_subset_of_ae {p : Ω → Prop} (h : ∀ᵐ ω ∂P, p ω) :
    ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, p ω := by
  obtain ⟨N, hsub, hN, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 h)
  refine ⟨Nᶜ, hN.compl, by rwa [compl_compl], fun ω hω => ?_⟩
  by_contra hp
  exact hω (hsub hp)

theorem measurableSet_nullAugmented_of_compl {G : Set Ω} (hG : MeasurableSet G) (hGc : P Gᶜ = 0)
    (t : ℝ≥0) : MeasurableSet[Ito.nullAugmented 𝓕 P t] G := by
  have := Ito.measurableSet_nullAugmented_of_null (𝓕 := 𝓕) hG.compl hGc t
  simpa using this.compl

theorem measurable_modProc {G : Set Ω} (hG : MeasurableSet G) (hGc : P Gᶜ = 0)
    (hGζ : ∀ ω ∈ G, ζ ω = ⊤) {X : ℝ≥0 → Ω → ℝ} (hX : AdaptedBefore 𝓕 ζ X) (t : ℝ≥0) :
    Measurable[Ito.nullAugmented 𝓕 P t] (modProc G X t) := by
  have heq : modProc G X t = fun ω => if ω ∈ G then Girsanov.killed ζ X t ω else 0 := by
    funext ω
    by_cases hω : ω ∈ G
    · simp only [modProc_of_mem hω, hω, ↓reduceIte]
      rw [Girsanov.killed_of_lt (by rw [hGζ ω hω]; exact ENNReal.coe_lt_top)]
    · simp only [modProc_of_not_mem hω, hω, ↓reduceIte]
  rw [heq]
  exact Measurable.ite (measurableSet_nullAugmented_of_compl hG hGc t)
    ((Girsanov.measurable_killed hX t).mono (Ito.le_nullAugmented 𝓕 P t) le_rfl) measurable_const

theorem measurable_tGap {𝓖 : Filtration ℝ≥0 mΩ} (hWm : ∀ t, Measurable[𝓖 t] (modProc G W t))
    (hWc : ∀ ω, Continuous (modProc G W · ω)) (hc : 0 < c) (t : ℝ≥0) :
    Measurable[𝓖 t] (tGap G W c x t) :=
  Dynkin.measurable_of_integralEq 𝓖 hWm hWc (lipschitz_realDrift hc)
    (fun y => by rw [Real.norm_eq_abs]; exact abs_realDrift_le hc y)
    (fun ω t => tGap_eq hWc hc ω t) (continuous_tGap hWc hc) t

end Meas


/-! ### The keep set in the gap coordinates -/

section Keep

variable {κ ρ : ℝ} {n : ℕ} {p : (ℝ × ℝ) × ℝ}

theorem le_gapX_of_infDist (h : 1 / ((n : ℝ) + 1) ≤ infDist p (region κ ρ)ᶜ) :
    1 / ((n : ℝ) + 1) ≤ gapX κ ρ p := by
  have hpU : p ∈ region κ ρ := Zhan.mem_of_one_div_le_infDist h
  set q : (ℝ × ℝ) × ℝ := ((p.1.1 - gapX κ ρ p, p.1.2), p.2) with hq
  have hqU : q ∈ (region κ ρ)ᶜ := fun hq' => by
    have := hq'.1; simp only [hq, gapX] at this; linarith
  have hd : dist p q = gapX κ ρ p := by
    simp only [hq, Prod.dist_eq, Real.dist_eq, sub_sub_cancel, sub_self, abs_zero]
    rw [abs_of_pos hpU.1]; simp [hpU.1.le]
  exact h.trans ((infDist_le_dist_of_mem hqU).trans hd.le)

theorem le_gapD_of_infDist (h : 1 / ((n : ℝ) + 1) ≤ infDist p (region κ ρ)ᶜ) :
    1 / ((n : ℝ) + 1) ≤ gapD p := by
  have hpU : p ∈ region κ ρ := Zhan.mem_of_one_div_le_infDist h
  set q : (ℝ × ℝ) × ℝ := ((p.1.1 - gapD p, p.1.2), p.2) with hq
  have hqU : q ∈ (region κ ρ)ᶜ := fun hq' => by
    have := hq'.2; simp only [hq, gapD] at this; linarith
  have hd : dist p q = gapD p := by
    simp only [hq, Prod.dist_eq, Real.dist_eq, sub_sub_cancel, sub_self, abs_zero]
    rw [abs_of_pos hpU.2]; simp [hpU.2.le]
  exact h.trans ((infDist_le_dist_of_mem hqU).trans hd.le)

/-- The keep set: `X, D ≥ 1/(n+1)`, `X ≤ M`, `‖p‖ ≤ n`. -/
theorem keepSet_bounds {M : ℝ} (hp : p ∈ Zhan.keepSet (region κ ρ) (gapX κ ρ) M n) :
    p ∈ region κ ρ ∧ 1 / ((n : ℝ) + 1) ≤ gapX κ ρ p ∧ 1 / ((n : ℝ) + 1) ≤ gapD p ∧
      gapX κ ρ p ≤ M ∧ ‖p‖ ≤ n :=
  ⟨Zhan.keepSet_subset hp, le_gapX_of_infDist hp.1, le_gapD_of_infDist hp.1, hp.2.2, hp.2.1⟩

end Keep

/-! ### The coordinates on good paths -/

section Coord

open scoped Classical

variable {Ω : Type*} {κ ρ : ℝ} {xL ρL : Fin 0 → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin 0 → ℝ≥0 → Ω → ℝ}
  {VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω} {c x : ℝ}

variable (hgood : ∀ ω ∈ G, IsGood κ ρ xL ρL W VL VR B ζ ω)
include hgood

theorem continuous_modW (ω : Ω) : Continuous (modProc G W · ω) :=
  continuous_modProc (fun ω hω => (hgood ω hω).continuous_w) ω

theorem continuous_modV (ω : Ω) : Continuous (modProc G (VR 0) · ω) :=
  continuous_modProc (fun ω hω => (hgood ω hω).continuous_v) ω

theorem continuous_modB (ω : Ω) : Continuous (modProc G B · ω) :=
  continuous_modProc (fun ω hω => (hgood ω hω).2.1) ω

theorem modW_zero (ω : Ω) : modProc G W 0 ω = 0 := by
  by_cases hω : ω ∈ G
  · rw [modProc_of_mem hω]; exact (hgood ω hω).2.2.1
  · exact modProc_of_not_mem hω 0

theorem modV_zero (ω : Ω) : modProc G (VR 0) 0 ω = 0 := by
  by_cases hω : ω ∈ G
  · rw [modProc_of_mem hω]; exact (hgood ω hω).2.2.2.2.1 0
  · exact modProc_of_not_mem hω 0

theorem modB_zero (hκ : 0 < κ) (ω : Ω) : modProc G B 0 ω = 0 := by
  by_cases hω : ω ∈ G
  · rw [modProc_of_mem hω]; exact (hgood ω hω).b_zero hκ
  · exact modProc_of_not_mem hω 0

theorem modV_ge_modW (ω : Ω) (t : ℝ≥0) : modProc G W t ω ≤ modProc G (VR 0) t ω := by
  by_cases hω : ω ∈ G
  · rw [modProc_of_mem hω, modProc_of_mem hω]
    exact (hgood ω hω).w_le_v t
  · rw [modProc_of_not_mem hω, modProc_of_not_mem hω]

theorem intervalIntegrable_lam₂ (ω : Ω) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun s : ℝ => 2 / (modProc G (VR 0) s.toNNReal ω - modProc G W s.toNNReal ω))
      volume 0 t := by
  by_cases hω : ω ∈ G
  · simp only [modProc_of_mem hω]
    have h := Zhan.intervalIntegrable_two_div_of_inv (w := (W · ω)) (u := (VR 0 · ω))
      ((hgood ω hω).intervalIntegrable_gap t.toNNReal)
    rwa [Real.coe_toNNReal _ ht] at h
  · simp only [modProc_of_not_mem hω, sub_self, div_zero]
    exact intervalIntegrable_const

theorem modV_eq (ω : Ω) (t : ℝ≥0) :
    modProc G (VR 0) t ω =
      ∫ s in (0 : ℝ)..t, 2 / (modProc G (VR 0) s.toNNReal ω - modProc G W s.toNNReal ω) := by
  by_cases hω : ω ∈ G
  · simp only [modProc_of_mem hω]
    exact (hgood ω hω).v_eq t
  · simp [modProc_of_not_mem hω]

theorem continuous_coordΛ (hc : 0 < c) (ω : Ω) : Continuous (coordΛ G W VR c x · ω) :=
  ((continuous_tGap (continuous_modW hgood) hc ω).add (continuous_modW hgood ω)).prodMk
    (continuous_modV hgood ω)

theorem coordΛ_zero (hc : 0 < c) (ω : Ω) : coordΛ G W VR c x 0 ω = (x, 0) := by
  have h := tGap_eq (x := x) (continuous_modW hgood) hc ω 0
  simp only [NNReal.coe_zero, intervalIntegral.integral_same, add_zero, modW_zero hgood,
    zero_smul] at h
  simp only [coordΛ, h, modW_zero hgood, modV_zero hgood, add_zero]

theorem intervalIntegrable_coordLam (hc : 0 < c) (ω : Ω) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun s => coordLam G W VR c x s ω) volume 0 t := by
  refine intervalIntegrable_pair ?_ (intervalIntegrable_lam₂ hgood ω ht)
  exact ((lipschitz_realDrift hc).continuous.comp ((continuous_tGap (continuous_modW hgood) hc ω).comp
    continuous_real_toNNReal)).intervalIntegrable 0 t

theorem coordΛ_eq (hc : 0 < c) (ω : Ω) (t : ℝ≥0) :
    coordΛ G W VR c x t ω = coordΛ G W VR c x 0 ω + ∫ s in (0 : ℝ)..t, coordLam G W VR c x s ω := by
  rw [coordΛ_zero hgood hc]
  unfold coordLam
  have h1 : IntervalIntegrable (fun s : ℝ => realDrift c (tGap G W c x s.toNNReal ω)) volume 0 t :=
    ((lipschitz_realDrift hc).continuous.comp ((continuous_tGap (continuous_modW hgood) hc ω).comp
      continuous_real_toNNReal)).intervalIntegrable 0 t
  rw [intervalIntegral_pair h1 (intervalIntegrable_lam₂ hgood ω t.coe_nonneg)]
  have h := tGap_eq (x := x) (continuous_modW hgood) hc ω t
  simp only [coordΛ, Prod.mk_add_mk, zero_add]
  ext
  · simp only; rw [h, smul_eq_mul]; ring
  · exact modV_eq hgood ω t

theorem gapX_coord {ω : Ω} (hω : ω ∈ G) (t : ℝ≥0) :
    gapX κ ρ (coordΛ G W VR c x t ω, modProc G B t ω) = tGap G W c x t ω := by
  simp only [gapX, coordΛ, modProc_of_mem hω]
  rw [w_eq_of_path (hgood ω hω).2.2 t]
  ring

theorem gapX_sub_gapD_coord {ω : Ω} (hω : ω ∈ G) (t : ℝ≥0) :
    gapX κ ρ (coordΛ G W VR c x t ω, modProc G B t ω) - gapD (coordΛ G W VR c x t ω, modProc G B t ω) =
      VR 0 t ω - W t ω := by
  rw [gapX_coord hgood hω]
  simp only [gapD, coordΛ, modProc_of_mem hω]
  ring

end Coord

/-! ### The localizing time and the localized Itô martingale -/

section Stop

variable {Ω : Type*}

/-- The localizing time at level `(n, M)`: the exit time (capped at `n`) of the coordinates, with the gap tamed at
level `1/(n+1)`, from `{dist(·, region^c) > 1/(n+1), ‖·‖ < n, X < M}`; `0` off `G`. -/
abbrev lyapStop (κ ρ : ℝ) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (x M : ℝ) (n : ℕ) (ω : Ω) : ℝ≥0 :=
  Zhan.locStop G (coordΛ G W VR (1 / ((n : ℝ) + 1)) x) (modProc G B) (region κ ρ) (gapX κ ρ) M n ω

/-- The coordinate path `((g_t(x), V_t), B_t)` at level `n`. -/
abbrev lyapPath (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (x : ℝ)
    (n : ℕ) (t : ℝ≥0) (ω : Ω) : (ℝ × ℝ) × ℝ :=
  Zhan.pathX (coordΛ G W VR (1 / ((n : ℝ) + 1)) x) (modProc G B) t ω

end Stop

section Mart

open scoped Classical

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {κ ρ : ℝ} {xL ρL : Fin 0 → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin 0 → ℝ≥0 → Ω → ℝ}
  {VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω} {x M : ℝ} {n : ℕ}

variable (hκ : 0 < κ)
  (hE : IsIntegratedSLEEvolution κ xL (fun _ => 0) ρL (fun _ => ρ) P 𝓕 W VL VR B ζ)
  (hG : MeasurableSet G) (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsGood κ ρ xL ρL W VL VR B ζ ω)

theorem one_div_succ_pos (n : ℕ) : (0 : ℝ) < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat

include hE hG hGc hgood in
theorem isFilteredBrownianReal_modB :
    IsFilteredBrownianReal (Ito.nullAugmented 𝓕 P) (modProc G B) P :=
  (Ito.isFilteredBrownianReal_modify hE.1 hG hGc fun ω hω => (hgood ω hω).2.1).1

include hE hG hGc hgood in
theorem measurable_coordΛ {c : ℝ} (hc : 0 < c) (t : ℝ≥0) :
    Measurable[Ito.nullAugmented 𝓕 P t] (coordΛ G W VR c x t) := by
  have hGζ : ∀ ω ∈ G, ζ ω = ⊤ := fun ω hω => (hgood ω hω).1
  have hWm := measurable_modProc hG hGc hGζ hE.2.1
  have hVm := measurable_modProc hG hGc hGζ (hE.2.2.2.1 0)
  exact ((measurable_tGap hWm (continuous_modW hgood) hc t).add (hWm t)).prodMk (hVm t)

include hE hG hGc hgood in
theorem isStoppingTime_lyapStop :
    IsStoppingTime (Ito.nullAugmented 𝓕 P)
      fun ω => (lyapStop κ ρ G W VR B x M n ω : WithTop ℝ≥0) :=
  Zhan.isStoppingTime_locStop (isFilteredBrownianReal_modB hE hG hGc hgood) (continuous_modB hgood)
    continuous_gapX.continuousOn (measurable_coordΛ hE hG hGc hgood (one_div_succ_pos n))
    (continuous_coordΛ hgood (one_div_succ_pos n)) (measurableSet_nullAugmented_of_compl hG hGc 0)

variable (hX0 : (((x, 0), 0) : (ℝ × ℝ) × ℝ) ∉ Zhan.exitSet (region κ ρ) (gapX κ ρ) M n)

omit mΩ in
include hκ hgood hX0 in
theorem lyapPath_mem_keepSet {ω : Ω} {t : ℝ≥0} (ht : t ≤ lyapStop κ ρ G W VR B x M n ω) :
    lyapPath G W VR B x n t ω ∈ Zhan.keepSet (region κ ρ) (gapX κ ρ) M n :=
  Zhan.pathX_mem_keepSet (continuous_modB hgood) continuous_gapX.continuousOn
    (continuous_coordΛ hgood (one_div_succ_pos n)) (coordΛ_zero hgood (one_div_succ_pos n))
    (modB_zero hgood hκ) hX0 ht

include hκ hE hG hGc hgood hX0 in
/-- **The localized Itô martingale of the Lyapunov observable.** -/
theorem martingale_lyap (a e θ : ℝ) :
    Martingale (fun t ω => obs κ ρ a e θ (lyapPath G W VR B x n (min t (lyapStop κ ρ G W VR B x M n ω)) ω) -
      ∫ s in (0 : ℝ)..((min t (lyapStop κ ρ G W VR B x M n ω) : ℝ≥0) : ℝ),
        Ito.itoGen (obs κ ρ a e θ) (lyapPath G W VR B x n s.toNNReal ω)
          (coordLam G W VR (1 / ((n : ℝ) + 1)) x s ω)) (Ito.nullAugmented 𝓕 P) P := by
  set c : ℝ := 1 / ((n : ℝ) + 1) with hcdef
  have hc : 0 < c := one_div_succ_pos n
  set σ := lyapStop κ ρ G W VR B x M n with hσdef
  have hσ := isStoppingTime_lyapStop (M := M) (x := x) (n := n) hE hG hGc hgood
  have hΛm := measurable_coordΛ (x := x) hE hG hGc hgood hc
  have hΛc := continuous_coordΛ (x := x) hgood hc
  have hΛσm : ∀ t, Measurable[Ito.nullAugmented 𝓕 P t]
      fun ω => coordΛ G W VR c x (min t (σ ω)) ω := fun t => by
    have h := Ito.measurable_stopped_of_agree (X := coordΛ G W VR c x) hσ hΛm (G := univ)
      (@MeasurableSet.univ _ (Ito.nullAugmented 𝓕 P 0)) ((0 : ℝ), (0 : ℝ)) (fun _ _ _ _ => rfl)
      (fun ω _ => (hΛc ω).continuousOn) t
    simpa using h
  have hK := fun ω t (ht : t ≤ σ ω) => lyapPath_mem_keepSet hκ hgood hX0 ht
  refine Ito.martingale_itoLocalized (isFilteredBrownianReal_modB hE hG hGc hgood) (continuous_modB hgood)
    isOpen_region contDiffOn_obs (Zhan.isCompact_keepSet continuous_gapX.continuousOn)
    Zhan.keepSet_subset hσ hΛσm (fun ω => intervalIntegrable_coordLam hgood hc ω (σ ω).coe_nonneg)
    (fun ω t _ => coordΛ_eq hgood hc ω t) (Kb := n * (2 / c) + n) (fun ω => ?_) hK
  -- the variation bound: `‖λ‖ ≤ 2/c + 2/(V − W)` and `∫₀^σ 2/(V − W) = V_σ ≤ n`
  have hσn : ((σ ω : ℝ≥0) : ℝ) ≤ n := by exact_mod_cast Zhan.locStop_le ω
  have hlam2 := intervalIntegrable_lam₂ hgood ω (σ ω).coe_nonneg
  have hle : ∀ s ∈ Ioc (0 : ℝ) (σ ω), ‖coordLam G W VR c x s ω‖ ≤
      2 / c + 2 / (modProc G (VR 0) s.toNNReal ω - modProc G W s.toNNReal ω) := by
    intro s _
    have h2 : 0 ≤ 2 / (modProc G (VR 0) s.toNNReal ω - modProc G W s.toNNReal ω) :=
      div_nonneg zero_le_two (sub_nonneg.2 (modV_ge_modW hgood ω s.toNNReal))
    have h1 : |realDrift c (tGap G W c x s.toNNReal ω)| ≤ 2 / c := abs_realDrift_le hc _
    have hc2 : 0 ≤ 2 / c := by positivity
    simp only [coordLam, Prod.norm_def, Real.norm_eq_abs]
    rw [abs_of_nonneg h2]
    exact max_le (by linarith) (by linarith)
  have hmono := intervalIntegral.integral_mono_on (σ ω).coe_nonneg
    (intervalIntegrable_coordLam hgood hc ω (σ ω).coe_nonneg).norm
    (intervalIntegrable_const.add hlam2) fun s hs => by
      rcases hs.1.lt_or_eq with h | h
      · exact hle s ⟨h, hs.2⟩
      · subst h
        simp only [coordLam, Real.toNNReal_zero, modW_zero hgood, modV_zero hgood, sub_self,
          div_zero, Prod.norm_def, Real.norm_eq_abs, abs_zero, add_zero]
        exact max_le ((abs_realDrift_le hc _).trans le_rfl) (by positivity)
  rw [intervalIntegral.integral_add intervalIntegrable_const hlam2, intervalIntegral.integral_const,
    ← modV_eq hgood ω (σ ω), smul_eq_mul, sub_zero] at hmono
  have hV : modProc G (VR 0) (σ ω) ω ≤ n := by
    have hk := (keepSet_bounds (hK ω (σ ω) le_rfl)).2.2.2.2
    have : |modProc G (VR 0) (σ ω) ω| ≤ ‖lyapPath G W VR B x n (σ ω) ω‖ := by
      simp only [lyapPath, Zhan.pathX, coordΛ, Prod.norm_def, Real.norm_eq_abs]
      exact (le_max_right _ _).trans (le_max_left _ _)
    exact (le_abs_self _).trans (this.trans hk)
  have : ((σ ω : ℝ≥0) : ℝ) * (2 / c) ≤ n * (2 / c) :=
    mul_le_mul_of_nonneg_right hσn (by positivity)
  linarith

omit mΩ in
include hκ hgood hX0 in
/-- **The drift integral up to the localizing time**: on a good path, `∫₀^σ itoGen F ≤ −γ M^{λ−2} σ`. -/
theorem drift_integral_le {a e θ γ : ℝ} (hl2 : a + e < 2) (hγ : 0 < γ)
    (hdrift : ∀ p ∈ region κ ρ, 0 < gapX κ ρ p - gapD p →
      Ito.itoGen (obs κ ρ a e θ) p (2 / gapX κ ρ p, 2 / (gapX κ ρ p - gapD p)) ≤
        -γ * gapX κ ρ p ^ (a + e - 2)) {ω : Ω} (hω : ω ∈ G) :
    ∫ s in (0 : ℝ)..((lyapStop κ ρ G W VR B x M n ω : ℝ≥0) : ℝ),
        Ito.itoGen (obs κ ρ a e θ) (lyapPath G W VR B x n s.toNNReal ω)
          (coordLam G W VR (1 / ((n : ℝ) + 1)) x s ω) ≤
      -γ * M ^ (a + e - 2) * (lyapStop κ ρ G W VR B x M n ω : ℝ) := by
  set c : ℝ := 1 / ((n : ℝ) + 1) with hcdef
  have hc : 0 < c := one_div_succ_pos n
  set σ := lyapStop κ ρ G W VR B x M n ω with hσdef
  set Φ := obs κ ρ a e θ with hΦdef
  have hσ0 : (0 : ℝ) ≤ σ := σ.coe_nonneg
  have hΛc := continuous_coordΛ (x := x) hgood hc
  have hpathc : Continuous fun s : ℝ => lyapPath G W VR B x n s.toNNReal ω :=
    (Zhan.continuous_pathX hΛc (continuous_modB hgood) ω).comp continuous_real_toNNReal
  have hmem : ∀ s ∈ Icc (0 : ℝ) σ,
      lyapPath G W VR B x n s.toNNReal ω ∈ Zhan.keepSet (region κ ρ) (gapX κ ρ) M n := fun s hs =>
    lyapPath_mem_keepSet hκ hgood hX0 (Real.toNNReal_le_iff_le_coe.2 hs.2)
  have hmapsU : MapsTo (fun s : ℝ => lyapPath G W VR B x n s.toNNReal ω) (uIcc 0 (σ : ℝ)) (region κ ρ) :=
    fun s hs => Zhan.keepSet_subset (hmem s (by rwa [uIcc_of_le hσ0] at hs))
  have hF1 : ContinuousOn (fun p => fderiv ℝ Φ p) (region κ ρ) :=
    (contDiffOn_obs (n := 3)).continuousOn_fderiv_of_isOpen isOpen_region (by norm_num)
  have hF2 : ContinuousOn (fun p => fderiv ℝ (fderiv ℝ Φ) p) (region κ ρ) :=
    ((contDiffOn_obs (n := 3)).fderiv_of_isOpen isOpen_region (by norm_num) :
      ContDiffOn ℝ 1 (fun p => fderiv ℝ Φ p) (region κ ρ)).continuousOn_fderiv_of_isOpen
        isOpen_region le_rfl
  have hc1 : ContinuousOn (fun s : ℝ => Ito.partialFst Φ (lyapPath G W VR B x n s.toNNReal ω))
      (uIcc 0 (σ : ℝ)) :=
    (hF1.comp hpathc.continuousOn hmapsU).clm_comp continuousOn_const
  have hc2 : ContinuousOn (fun s : ℝ => Ito.partialSndSnd Φ (lyapPath G W VR B x n s.toNNReal ω))
      (uIcc 0 (σ : ℝ)) :=
    ((hF2.comp hpathc.continuousOn hmapsU).clm_apply continuousOn_const).clm_apply continuousOn_const
  have hint : IntervalIntegrable (fun s => Ito.itoGen Φ (lyapPath G W VR B x n s.toNNReal ω)
      (coordLam G W VR c x s ω)) volume 0 σ :=
    (Ito.intervalIntegrable_clm_apply hc1 (intervalIntegrable_coordLam hgood hc ω hσ0)).add
      (hc2.intervalIntegrable.const_mul (1 / 2))
  have hae : ∀ᵐ s ∂(volume : Measure ℝ),
      s ∉ {s : ℝ | 0 ≤ s ∧ ((s.toNNReal : ℝ≥0∞) < ⊤) ∧ W s.toNNReal ω = VR 0 s.toNNReal ω} :=
    measure_eq_zero_iff_ae_notMem.1 (hgood ω hω).volume_collision
  have hbound : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) σ)),
      Ito.itoGen Φ (lyapPath G W VR B x n s.toNNReal ω) (coordLam G W VR c x s ω) ≤
        -γ * M ^ (a + e - 2) := by
    refine (ae_restrict_iff' measurableSet_Icc).2 (hae.mono fun s hs hsI => ?_)
    have hne : W s.toNNReal ω ≠ VR 0 s.toNNReal ω := fun h => hs ⟨hsI.1, ENNReal.coe_lt_top, h⟩
    obtain ⟨hU, hXc, -, hXM, -⟩ := keepSet_bounds (hmem s hsI)
    set p := lyapPath G W VR B x n s.toNNReal ω with hp
    have hX : gapX κ ρ p = tGap G W c x s.toNNReal ω := gapX_coord hgood hω s.toNNReal
    have hR : gapX κ ρ p - gapD p = VR 0 s.toNNReal ω - W s.toNNReal ω :=
      gapX_sub_gapD_coord hgood hω s.toNNReal
    have hRpos : 0 < gapX κ ρ p - gapD p := by
      rw [hR]; exact sub_pos.2 (lt_of_le_of_ne ((hgood ω hω).w_le_v _) hne)
    have hlam : coordLam G W VR c x s ω = (2 / gapX κ ρ p, 2 / (gapX κ ρ p - gapD p)) := by
      simp only [coordLam, modProc_of_mem hω]
      rw [hR, ← hX, realDrift_of_le hXc]
    rw [hlam]
    have hXpos : 0 < gapX κ ρ p := hc.trans_le hXc
    have hpow : M ^ (a + e - 2) ≤ gapX κ ρ p ^ (a + e - 2) :=
      Real.rpow_le_rpow_of_nonpos hXpos hXM (by linarith)
    have := hdrift p hU hRpos
    nlinarith
  calc ∫ s in (0 : ℝ)..(σ : ℝ), Ito.itoGen Φ (lyapPath G W VR B x n s.toNNReal ω)
        (coordLam G W VR c x s ω)
      ≤ ∫ _ in (0 : ℝ)..(σ : ℝ), -γ * M ^ (a + e - 2) :=
        intervalIntegral.integral_mono_ae_restrict hσ0 hint intervalIntegrable_const hbound
    _ = -γ * M ^ (a + e - 2) * σ := by
        rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]; ring

include hE hG hGc hgood in
theorem measurable_lyapStop : Measurable fun ω => (lyapStop κ ρ G W VR B x M n ω : ℝ) := by
  have hσ := isStoppingTime_lyapStop (M := M) (x := x) (n := n) hE hG hGc hgood
  have hm : Measurable fun ω => lyapStop κ ρ G W VR B x M n ω := by
    refine measurable_of_Iic fun t => ?_
    have h := (Ito.nullAugmented 𝓕 P).le t _ (hσ t)
    convert h using 1
    ext ω
    simp only [mem_preimage, mem_Iic, mem_ofPred_eq, WithTop.coe_le_coe]
  exact measurable_coe_nnreal_real.comp hm

include hκ hE hG hGc hgood hX0 in
/-- **The expectation bounds.** `γ M^{λ−2} E[σ] ≤ x^λ` and `E[F(σ)] ≤ x^λ`, from the localized martingale, the drift
bound `itoGen F ≤ −γ X^{λ−2} ≤ −γ M^{λ−2}` up to `σ`, and `F ≥ 0`. -/
theorem lyap_expect_bounds [IsProbabilityMeasure P] {a e θ γ : ℝ} (hl2 : a + e < 2) (hγ : 0 < γ)
    (hM : 0 < M) (hx : 0 < x)
    (hdrift : ∀ p ∈ region κ ρ, 0 < gapX κ ρ p - gapD p →
      Ito.itoGen (obs κ ρ a e θ) p (2 / gapX κ ρ p, 2 / (gapX κ ρ p - gapD p)) ≤
        -γ * gapX κ ρ p ^ (a + e - 2))
    (hnn : ∀ p ∈ region κ ρ, 0 ≤ obs κ ρ a e θ p) :
    γ * M ^ (a + e - 2) * ∫ ω, (lyapStop κ ρ G W VR B x M n ω : ℝ) ∂P ≤ x ^ (a + e) ∧
      ∫ ω, obs κ ρ a e θ (lyapPath G W VR B x n (lyapStop κ ρ G W VR B x M n ω) ω) ∂P ≤
        x ^ (a + e) := by
  have hMart := martingale_lyap hκ hE hG hGc hgood hX0 a e θ
  have hsi := hMart.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ (n : ℝ≥0)) MeasurableSet.univ
  simp only [setIntegral_univ] at hsi
  have hp0 : ∀ ω, lyapPath G W VR B x n 0 ω = ((x, 0), 0) := fun ω => by
    show (coordΛ G W VR (1 / ((n : ℝ) + 1)) x 0 ω, modProc G B 0 ω) = ((x, 0), 0)
    rw [coordΛ_zero hgood (one_div_succ_pos n), modB_zero hgood hκ]
  set c : ℝ := 1 / ((n : ℝ) + 1) with hcdef
  have hc : 0 < c := one_div_succ_pos n
  set σ := lyapStop κ ρ G W VR B x M n with hσdef
  set Φ := obs κ ρ a e θ with hΦdef
  have hΦ0 : Φ ((x, 0), 0) = x ^ (a + e) := by
    have h1 : gapX κ ρ ((x, 0), 0) = x := by simp [gapX]
    have h2 : gapD ((x, 0), 0) = x := by simp [gapD]
    rw [hΦdef, obs, h1, h2, lyap_self hx]
  have h0 : ∀ ω, Φ (lyapPath G W VR B x n (min 0 (σ ω)) ω) -
      ∫ s in (0 : ℝ)..((min 0 (σ ω) : ℝ≥0) : ℝ), Ito.itoGen Φ (lyapPath G W VR B x n s.toNNReal ω)
        (coordLam G W VR c x s ω) = x ^ (a + e) := fun ω => by
    rw [min_eq_left zero_le, hp0, hΦ0]; simp
  simp only [h0, integral_const, probReal_univ, one_smul] at hsi
  have hmin : ∀ ω, min (n : ℝ≥0) (σ ω) = σ ω := fun ω => min_eq_right (Zhan.locStop_le ω)
  simp only [hmin] at hsi
  -- the stopped observable is integrable and nonnegative
  have hin : ∀ ω, lyapPath G W VR B x n (σ ω) ω ∈ region κ ρ := fun ω =>
    Zhan.keepSet_subset (lyapPath_mem_keepSet hκ hgood hX0 le_rfl)
  have hmeasF : Measurable fun ω => Φ (lyapPath G W VR B x n (σ ω) ω) :=
    Zhan.measurable_comp_pathX_locStop (isFilteredBrownianReal_modB hE hG hGc hgood)
      (continuous_modB hgood) isOpen_region continuous_gapX.continuousOn
      (measurable_coordΛ hE hG hGc hgood hc) (continuous_coordΛ hgood hc)
      (measurableSet_nullAugmented_of_compl hG hGc 0) (contDiffOn_obs (n := 0)).continuousOn hin
  obtain ⟨C, hC⟩ := (Zhan.isCompact_keepSet (U := region κ ρ) (L := M) (n := n)
    continuous_gapX.continuousOn).exists_bound_of_continuousOn
      ((contDiffOn_obs (n := 0) (a := a) (e := e) (θ := θ)).continuousOn.mono Zhan.keepSet_subset)
  have hFint : Integrable (fun ω => Φ (lyapPath G W VR B x n (σ ω) ω)) P :=
    Integrable.of_bound hmeasF.aestronglyMeasurable C
      (Eventually.of_forall fun ω => hC _ (lyapPath_mem_keepSet hκ hgood hX0 le_rfl))
  have hFnn : ∀ ω, 0 ≤ Φ (lyapPath G W VR B x n (σ ω) ω) := fun ω => hnn _ (hin ω)
  have hσm := measurable_lyapStop (M := M) (x := x) (n := n) hE hG hGc hgood
  have hσint : Integrable (fun ω => (σ ω : ℝ)) P :=
    Integrable.of_bound hσm.aestronglyMeasurable n (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (σ ω).coe_nonneg]; exact_mod_cast Zhan.locStop_le ω)
  have hMn := hMart.integrable (n : ℝ≥0)
  simp only [hmin] at hMn
  set I : Ω → ℝ := fun ω => ∫ s in (0 : ℝ)..((σ ω : ℝ≥0) : ℝ),
    Ito.itoGen Φ (lyapPath G W VR B x n s.toNNReal ω) (coordLam G W VR c x s ω) with hIdef
  have hIint : Integrable I P := by
    have := hFint.sub hMn
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.sub_apply, hIdef]; ring
  have hIle : ∀ ω, I ω ≤ -γ * M ^ (a + e - 2) * (σ ω : ℝ) := by
    intro ω
    by_cases hω : ω ∈ G
    · exact drift_integral_le hκ hgood hX0 hl2 hγ hdrift hω
    · have hσ0 : σ ω = 0 := by simp [hσdef, Zhan.locStop, hω]
      simp [hIdef, hσ0]
  have hsplit : ∫ ω, (Φ (lyapPath G W VR B x n (σ ω) ω) - I ω) ∂P =
      (∫ ω, Φ (lyapPath G W VR B x n (σ ω) ω) ∂P) - ∫ ω, I ω ∂P := integral_sub hFint hIint
  have hIbd : ∫ ω, I ω ∂P ≤ -γ * M ^ (a + e - 2) * ∫ ω, (σ ω : ℝ) ∂P := by
    rw [← integral_const_mul]
    exact integral_mono hIint (hσint.const_mul _) hIle
  have hFnn' : 0 ≤ ∫ ω, Φ (lyapPath G W VR B x n (σ ω) ω) ∂P := integral_nonneg hFnn
  have hσnn : 0 ≤ ∫ ω, (σ ω : ℝ) ∂P := integral_nonneg fun ω => (σ ω).coe_nonneg
  have hMpos : 0 ≤ γ * M ^ (a + e - 2) := mul_nonneg hγ.le (Real.rpow_pos_of_pos hM _).le
  have hkey : x ^ (a + e) = (∫ ω, Φ (lyapPath G W VR B x n (σ ω) ω) ∂P) - ∫ ω, I ω ∂P := by
    rw [hsi, ← hsplit]
  have hprod : 0 ≤ γ * M ^ (a + e - 2) * ∫ ω, (σ ω : ℝ) ∂P := mul_nonneg hMpos hσnn
  constructor <;> nlinarith

include hκ hE hG hGc hgood hX0 in
theorem integrable_lyapObs [IsProbabilityMeasure P] (a e θ : ℝ) :
    Integrable (fun ω => obs κ ρ a e θ (lyapPath G W VR B x n (lyapStop κ ρ G W VR B x M n ω) ω)) P := by
  have hc : (0 : ℝ) < 1 / ((n : ℝ) + 1) := one_div_succ_pos n
  have hin : ∀ ω, lyapPath G W VR B x n (lyapStop κ ρ G W VR B x M n ω) ω ∈ region κ ρ := fun ω =>
    Zhan.keepSet_subset (lyapPath_mem_keepSet hκ hgood hX0 le_rfl)
  have hmeasF : Measurable fun ω =>
      obs κ ρ a e θ (lyapPath G W VR B x n (lyapStop κ ρ G W VR B x M n ω) ω) :=
    Zhan.measurable_comp_pathX_locStop (isFilteredBrownianReal_modB hE hG hGc hgood)
      (continuous_modB hgood) isOpen_region continuous_gapX.continuousOn
      (measurable_coordΛ hE hG hGc hgood hc) (continuous_coordΛ hgood hc)
      (measurableSet_nullAugmented_of_compl hG hGc 0) (contDiffOn_obs (n := 0)).continuousOn hin
  obtain ⟨C, hC⟩ := (Zhan.isCompact_keepSet (U := region κ ρ) (L := M) (n := n)
    continuous_gapX.continuousOn).exists_bound_of_continuousOn
      ((contDiffOn_obs (n := 0) (a := a) (e := e) (θ := θ)).continuousOn.mono Zhan.keepSet_subset)
  exact Integrable.of_bound hmeasF.aestronglyMeasurable C
    (Eventually.of_forall fun ω => hC _ (lyapPath_mem_keepSet hκ hgood hX0 le_rfl))

include hE hG hGc hgood in
theorem integrable_lyapStop [IsProbabilityMeasure P] :
    Integrable (fun ω => (lyapStop κ ρ G W VR B x M n ω : ℝ)) P :=
  Integrable.of_bound (measurable_lyapStop hE hG hGc hgood).aestronglyMeasurable n
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (lyapStop κ ρ G W VR B x M n ω).coe_nonneg]
      exact_mod_cast Zhan.locStop_le ω)

omit [MeasurableSpace Ω] in
/-- Markov's inequality in the form used here. -/
theorem measure_le_le_ofReal {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → ℝ} (hf0 : ∀ ω, 0 ≤ f ω) (hfi : Integrable f P) {ε b : ℝ} (hε : 0 < ε)
    (hb : ∫ ω, f ω ∂P ≤ b) : P {ω | ε ≤ f ω} ≤ ENNReal.ofReal (b / ε) := by
  have h := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hf0) hfi ε
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ hε]
  linarith

include hκ hE hG hGc hgood hX0 in
/-- **The Markov bounds.** For `T > 0`: `P(σ ≥ T) ≤ x^λ/(γ M^{λ−2} T)` and `P(F(σ) ≥ m M^λ) ≤ x^λ/(m M^λ)`. -/
theorem lyap_markov [IsProbabilityMeasure P] {a e θ γ m : ℝ} (hl2 : a + e < 2) (hγ : 0 < γ)
    (hm : 0 < m) (hM : 0 < M) (hx : 0 < x)
    (hdrift : ∀ p ∈ region κ ρ, 0 < gapX κ ρ p - gapD p →
      Ito.itoGen (obs κ ρ a e θ) p (2 / gapX κ ρ p, 2 / (gapX κ ρ p - gapD p)) ≤
        -γ * gapX κ ρ p ^ (a + e - 2))
    (hnn : ∀ p ∈ region κ ρ, 0 ≤ obs κ ρ a e θ p) {T : ℝ} (hT : 0 < T) :
    P {ω | T ≤ (lyapStop κ ρ G W VR B x M n ω : ℝ)} ≤
        ENNReal.ofReal (x ^ (a + e) / (γ * M ^ (a + e - 2)) / T) ∧
      P {ω | m * M ^ (a + e) ≤ obs κ ρ a e θ (lyapPath G W VR B x n (lyapStop κ ρ G W VR B x M n ω) ω)} ≤
        ENNReal.ofReal (x ^ (a + e) / (m * M ^ (a + e))) := by
  obtain ⟨h1, h2⟩ := lyap_expect_bounds hκ hE hG hGc hgood hX0 hl2 hγ hM hx hdrift hnn
  have hMp : 0 < γ * M ^ (a + e - 2) := mul_pos hγ (Real.rpow_pos_of_pos hM _)
  refine ⟨measure_le_le_ofReal (fun ω => (lyapStop κ ρ G W VR B x M n ω).coe_nonneg)
    (integrable_lyapStop hE hG hGc hgood) hT ?_, measure_le_le_ofReal
      (fun ω => hnn _ (Zhan.keepSet_subset (lyapPath_mem_keepSet hκ hgood hX0 le_rfl)))
      (integrable_lyapObs hκ hE hG hGc hgood hX0 a e θ) (mul_pos hm (Real.rpow_pos_of_pos hM _)) h2⟩
  rw [le_div_iff₀ hMp, mul_comm]
  exact h1

end Mart

end InteractingSLE.LP.LP2
