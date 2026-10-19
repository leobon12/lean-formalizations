import HigherDimLFPP.Field.GraphLimit
import HigherDimLFPP.Var.Scaling
import LQGDimension.LFPP.ExpectedSupLimit
import LQGDimension.Gaussian.Chatterjee

/-!
# Lemma 3.2, second sentence: expected suprema with a convergent drift ((3.8″); packet P-F3a, T2)

Source: `source/higher-dimensional-lfpp-limit.pdf`, §3.2, Lemma 3.2 (second sentence, "expected
suprema converge as well"), as restated by planning audit HA2
(`planning/audits/HA2-section-3.md`, findings HA2-09, HA2-10, Details D6 "(3.8″)" and its
corollary "moving finite families", the Lean block (c) `gaussESup`, `Lemma32ESup`); consumers:
HA3 D5 (Lemma 4.3, Step 1d) and HA4 D5 (Lemma 5.2, step 1).

Expected suprema are taken in the lattice convention of `LQGDimension.aE`: the supremum over
finite subfamilies of `LQGDimension.gaussianExpectedMax` (`gaussESup`, HA2's definition).

* **Finite families** (HA2 D6, corollary; HA4 D5, step 1).  `tendsto_gEM`: if PSD covariances
  converge entrywise on a finite family and drifts converge there, the expected maxima converge
  (Chatterjee's bound `LQGDimension.expectedMaxCovLipschitz` plus the drift bound
  `abs_gEM_sub_le_of_drift`).  `tendsto_gEM_graph`: for profiles `f_{δ,i} → f_i` uniformly on
  `[0,1]` and drifts `b_δ → b`,
  `E max_i (δ^{-1/2}⟨h, μ_{δ f_{δ,i}} - μ_{δ0}⟩ + b_δ(i)) → E max_i (G_d(f_i) + b(i))`.
* **Lattice form on compact families of `V_n`** (HA2 (3.8″); HA3 D5, Step 1d).
  `expectedSupLimit_of_injOn` transports `LQGDimension.expectedSupLimit` (stated on compact
  subsets of `Fin D → ℝ`) to any index set with an injective coordinate map into a
  finite-dimensional normed space; `expectedSupLimit_Vg` is the case of `V_n(E)` with the vertex
  values as coordinates.  `tendsto_gaussESup_of` combines it with the finite-family limit.
* **(3.8″)** (`lemma32ESup`, HA2's `Lemma32ESup`, and its log form `tendsto_gaussESup_graph`):
  for `K ⊆ V_n(ℝ^{d-1})` with compact vertex image, a drift `b` continuous on the vertex image and
  `b_δ → b ∘ verts` uniformly on `K`,
  `ESup_K(δ⁻¹ Cov(⟨h, μ_{δf} - μ_{δ0}⟩, ⟨h, μ_{δg} - μ_{δ0}⟩), b_δ) → ESup_K(gCov, b ∘ verts)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace HigherDimLFPP

open LQGDimension (gaussianExpectedMax vecExpectedMax PSDOn)

/-! ## Finite Gaussian families: congruence, reindexing, drift and covariance perturbation -/

section Finite

/-- `gaussianExpectedMax F C b` only depends on the drift on `F`. -/
theorem gEM_congr_drift {ι : Type*} (F : Finset ι) (C : ι → ι → ℝ) {b b' : ι → ℝ}
    (h : ∀ i ∈ F, b i = b' i) : gaussianExpectedMax F C b = gaussianExpectedMax F C b' := by
  unfold LQGDimension.gaussianExpectedMax
  congr 1
  funext x
  congr 1
  funext i
  rw [h i i.2]

/-- `PSDOn F C` only depends on `C` on `F × F`. -/
theorem psdOn_congr {ι : Type*} {F : Finset ι} {C C' : ι → ι → ℝ}
    (h : ∀ i ∈ F, ∀ j ∈ F, C i j = C' i j) (hC : PSDOn F C) : PSDOn F C' := by
  unfold LQGDimension.PSDOn at *
  have e : (Matrix.of fun i j : F => C' i j) = Matrix.of fun i j : F => C i j := by
    ext i j
    simp only [Matrix.of_apply, h i i.2 j j.2]
  rwa [e]

/-- Reindexing a PSD kernel along any map. -/
theorem psdOn_comp {ι κ : Type*} [DecidableEq ι] {F : Finset κ} (g : κ → ι) {C : ι → ι → ℝ}
    (hC : PSDOn (F.image g) C) : PSDOn F (fun p q => C (g p) (g q)) := by
  unfold LQGDimension.PSDOn at *
  exact hC.submatrix fun p : F => (⟨g p, Finset.mem_image_of_mem g p.2⟩ : F.image g)

/-- **Drift perturbation**: `|𝕄_F(C, b) - 𝕄_F(C, b')| ≤ γ` if `|b - b'| ≤ γ` on `F`. -/
theorem abs_gEM_sub_le_of_drift {ι : Type*} (F : Finset ι) {C : ι → ι → ℝ} (hC : PSDOn F C)
    {b b' : ι → ℝ} {γ : ℝ} (hγ : 0 ≤ γ) (h : ∀ i ∈ F, |b i - b' i| ≤ γ) :
    |gaussianExpectedMax F C b - gaussianExpectedMax F C b'| ≤ γ := by
  rcases F.eq_empty_or_nonempty with rfl | hF
  · rw [Var.gEM_empty, Var.gEM_empty, sub_self, abs_zero]
    exact hγ
  obtain ⟨v, -, hv⟩ := LQGDimension.exists_vecExpectedMax_eq_gaussianExpectedMax F C hC
  rw [hv b, hv b', abs_sub_le_iff]
  constructor
  · have := LQGDimension.ESLimit.vecExpectedMax_le_of_drift_le F hF v b b' (γ := γ)
      (fun q hq => by linarith [(abs_le.1 (h q hq)).2])
    linarith
  · have := LQGDimension.ESLimit.vecExpectedMax_le_of_drift_le F hF v b' b (γ := γ)
      (fun q hq => by linarith [(abs_le.1 (h q hq)).1])
    linarith

/-- **Convergence of finite expected maxima** (HA2 D6, liminf step; HA4 D5, step 1): if PSD
covariances converge entrywise on the finite family `F` to a PSD kernel and the drifts converge
on `F`, the expected maxima converge.  Chatterjee's bound
(`LQGDimension.expectedMaxCovLipschitz`) and `abs_gEM_sub_le_of_drift`. -/
theorem tendsto_gEM {ι : Type} (F : Finset ι) {α : Type*} {l : Filter α}
    {Cl : α → ι → ι → ℝ} {C : ι → ι → ℝ} {bl : α → ι → ℝ} {b : ι → ℝ}
    (hPSD : ∀ᶠ a in l, PSDOn F (Cl a)) (hC : PSDOn F C)
    (hCconv : ∀ i ∈ F, ∀ j ∈ F, Tendsto (fun a => Cl a i j) l (𝓝 (C i j)))
    (hbconv : ∀ i ∈ F, Tendsto (fun a => bl a i) l (𝓝 (b i))) :
    Tendsto (fun a => gaussianExpectedMax F (Cl a) (bl a)) l
      (𝓝 (gaussianExpectedMax F C b)) := by
  set γ : α → ℝ := fun a => ∑ i ∈ F, ∑ j ∈ F, |Cl a i j - C i j| with hγ
  set β : α → ℝ := fun a => ∑ i ∈ F, |bl a i - b i| with hβ
  have hγ0 : Tendsto γ l (𝓝 0) := by
    have := tendsto_finsetSum F fun i hi => tendsto_finsetSum F fun j hj =>
      ((hCconv i hi j hj).sub_const (C i j)).abs
    simpa only [sub_self, abs_zero, Finset.sum_const_zero] using this
  have hβ0 : Tendsto β l (𝓝 0) := by
    have := tendsto_finsetSum F fun i hi => ((hbconv i hi).sub_const (b i)).abs
    simpa only [sub_self, abs_zero, Finset.sum_const_zero] using this
  have hbound : Tendsto (fun a => β a + 2 * Real.sqrt (2 * γ a * Real.log F.card)) l (𝓝 0) := by
    have h1 : Tendsto (fun a => 2 * γ a * Real.log F.card) l (𝓝 0) := by
      have := (hγ0.const_mul 2).mul_const (Real.log F.card)
      simpa only [mul_zero, zero_mul] using this
    have h2 := ((Real.continuous_sqrt.tendsto 0).comp h1).const_mul 2
    have := hβ0.add h2
    simpa only [Function.comp_def, Real.sqrt_zero, mul_zero, add_zero] using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun a => norm_nonneg _) ?_ hbound
  filter_upwards [hPSD] with a ha
  rw [Real.norm_eq_abs]
  have e1 : |gaussianExpectedMax F (Cl a) (bl a) - gaussianExpectedMax F (Cl a) b| ≤ β a :=
    abs_gEM_sub_le_of_drift F ha (Finset.sum_nonneg fun i _ => abs_nonneg _) fun i hi =>
      Finset.single_le_sum (f := fun i => |bl a i - b i|) (fun i _ => abs_nonneg _) hi
  have e2 := LQGDimension.expectedMaxCovLipschitz ι F (Cl a) C b (γ a) ha hC fun i hi j hj =>
    (Finset.single_le_sum (f := fun j => |Cl a i j - C i j|) (fun j _ => abs_nonneg _) hj).trans
      (Finset.single_le_sum (f := fun i => ∑ j ∈ F, |Cl a i j - C i j|)
        (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) hi)
  calc |gaussianExpectedMax F (Cl a) (bl a) - gaussianExpectedMax F C b|
      ≤ |gaussianExpectedMax F (Cl a) (bl a) - gaussianExpectedMax F (Cl a) b| +
          |gaussianExpectedMax F (Cl a) b - gaussianExpectedMax F C b| := abs_sub_le _ _ _
    _ ≤ β a + 2 * Real.sqrt (2 * γ a * Real.log F.card) := add_le_add e1 e2

/-- **HA2 D10, joint comparison of expected maxima** (vector form): for two families `x, y` in one
finite-dimensional inner product space and any drift `c`,
`E max_F (⟨x, Z⟩ + c) ≤ E max_F (⟨y, Z⟩ + c) + E max_{F × {±}} ⟨±(x - y), Z⟩`.
(The pointwise inequality `max (a + c) ≤ max (b + c) + max |a - b|`, integrated.) -/
theorem vecExpectedMax_le_add_sign {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (F : Finset ι) (x y : ι → E)
    (c : ι → ℝ) :
    vecExpectedMax F x c ≤ vecExpectedMax F y c +
      vecExpectedMax (F ×ˢ (Finset.univ : Finset Bool))
        (fun p => if p.2 then x p.1 - y p.1 else y p.1 - x p.1) 0 := by
  classical
  rcases F.eq_empty_or_nonempty with rfl | hF
  · have h0 : ∀ (G : Finset (ι × Bool)) (v : ι × Bool → E), G = ∅ →
        vecExpectedMax G v 0 = 0 := by
      intro G v hG
      subst hG
      unfold vecExpectedMax
      have : (fun z : E => ⨆ i : (∅ : Finset (ι × Bool)), ⟪v i, z⟫ + (0 : ι × Bool → ℝ) i) =
          fun _ => (0 : ℝ) := by
        funext z
        exact (iSup_of_empty' _).trans Real.sSup_empty
      rw [this, integral_zero]
    have e1 : vecExpectedMax (∅ : Finset ι) x c = 0 := by
      unfold vecExpectedMax
      have : (fun z : E => ⨆ i : (∅ : Finset ι), ⟪x i, z⟫ + c i) = fun _ => (0 : ℝ) := by
        funext z
        exact (iSup_of_empty' _).trans Real.sSup_empty
      rw [this, integral_zero]
    have e2 : vecExpectedMax (∅ : Finset ι) y c = 0 := by
      unfold vecExpectedMax
      have : (fun z : E => ⨆ i : (∅ : Finset ι), ⟪y i, z⟫ + c i) = fun _ => (0 : ℝ) := by
        funext z
        exact (iSup_of_empty' _).trans Real.sSup_empty
      rw [this, integral_zero]
    rw [e1, e2, h0 _ _ (Finset.empty_product _)]
    simp
  set w : ι × Bool → E := fun p => if p.2 then x p.1 - y p.1 else y p.1 - x p.1 with hw
  have hFB : (F ×ˢ (Finset.univ : Finset Bool)).Nonempty := hF.product Finset.univ_nonempty
  have : Nonempty F := hF.to_subtype
  have hpt : ∀ z : E, (⨆ i : F, ⟪x i, z⟫ + c i) ≤ (⨆ i : F, ⟪y i, z⟫ + c i) +
      ⨆ p : (F ×ˢ (Finset.univ : Finset Bool) : Finset (ι × Bool)),
        ⟪w p, z⟫ + (0 : ι × Bool → ℝ) p := by
    intro z
    refine ciSup_le fun i => ?_
    have h1 : ⟪y i, z⟫ + c i ≤ ⨆ j : F, ⟪y j, z⟫ + c j :=
      le_ciSup (f := fun j : F => ⟪y j, z⟫ + c j) (Set.finite_range _).bddAbove i
    have hmem : ((i : ι), true) ∈ F ×ˢ (Finset.univ : Finset Bool) :=
      Finset.mem_product.2 ⟨i.2, Finset.mem_univ _⟩
    have h2 : ⟪w ((i : ι), true), z⟫ + (0 : ι × Bool → ℝ) ((i : ι), true) ≤
        ⨆ p : (F ×ˢ (Finset.univ : Finset Bool) : Finset (ι × Bool)),
          ⟪w p, z⟫ + (0 : ι × Bool → ℝ) p :=
      le_ciSup (f := fun p : (F ×ˢ (Finset.univ : Finset Bool) : Finset (ι × Bool)) =>
        ⟪w p, z⟫ + (0 : ι × Bool → ℝ) p) (Set.finite_range _).bddAbove ⟨_, hmem⟩
    have e : ⟪w ((i : ι), true), z⟫ + (0 : ι × Bool → ℝ) ((i : ι), true) =
        ⟪x i, z⟫ - ⟪y i, z⟫ := by
      simp only [hw, ite_true, inner_sub_left, Pi.zero_apply, add_zero]
    rw [e] at h2
    linarith
  unfold vecExpectedMax
  have hx := LQGDimension.integrable_iSup_inner_add F x c
  have hy := LQGDimension.integrable_iSup_inner_add F y c
  have hw' := LQGDimension.integrable_iSup_inner_add (F ×ˢ (Finset.univ : Finset Bool)) w 0
  rw [← integral_add hy hw']
  exact integral_mono hx (hy.add hw') hpt

end Finite

/-! ## Graph covariances on finite families -/

section GraphFinite

variable {d : ℕ}

/-- `gCov` is Lipschitz in the sup norm on `[0,1]`:
`|gCov f' g' - gCov f g| ≤ 2π (ε + ε')` if `‖f' - f‖ ≤ ε` and `‖g' - g‖ ≤ ε'` on `[0,1]`. -/
theorem abs_gCov_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g f' g' : ℝ → E} (hf : IntervalIntegrable f volume 0 1)
    (hg : IntervalIntegrable g volume 0 1) (hf' : IntervalIntegrable f' volume 0 1)
    (hg' : IntervalIntegrable g' volume 0 1) {ε ε' : ℝ}
    (hε : ∀ x ∈ Icc (0 : ℝ) 1, ‖f' x - f x‖ ≤ ε) (hε' : ∀ x ∈ Icc (0 : ℝ) 1, ‖g' x - g x‖ ≤ ε') :
    |gCov f' g' - gCov f g| ≤ 2 * Real.pi * (ε + ε') := by
  have i1 : IntervalIntegrable (fun x => ‖f x‖ + ‖g x‖ - ‖f x - g x‖) volume 0 1 :=
    (hf.norm.add hg.norm).sub (hf.sub hg).norm
  have i2 : IntervalIntegrable (fun x => ‖f' x‖ + ‖g' x‖ - ‖f' x - g' x‖) volume 0 1 :=
    (hf'.norm.add hg'.norm).sub (hf'.sub hg').norm
  unfold gCov
  rw [← mul_sub, ← intervalIntegral.integral_sub i2 i1, abs_mul, abs_of_pos Real.pi_pos]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := 2 * (ε + ε')) (f := fun x => (‖f' x‖ + ‖g' x‖ - ‖f' x - g' x‖) -
      (‖f x‖ + ‖g x‖ - ‖f x - g x‖)) fun x hx => ?_
  · rw [Real.norm_eq_abs, sub_zero, abs_one, mul_one] at hb
    calc Real.pi * |∫ x in (0 : ℝ)..1, ((‖f' x‖ + ‖g' x‖ - ‖f' x - g' x‖) -
          (‖f x‖ + ‖g x‖ - ‖f x - g x‖))| ≤ Real.pi * (2 * (ε + ε')) :=
          mul_le_mul_of_nonneg_left hb Real.pi_pos.le
      _ = 2 * Real.pi * (ε + ε') := by ring
  · rw [uIoc_of_le zero_le_one] at hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hx
    have a1 := abs_norm_sub_norm_le (f' x) (f x)
    have a2 := abs_norm_sub_norm_le (g' x) (g x)
    have a3 := abs_norm_sub_norm_le (f' x - g' x) (f x - g x)
    have a4 : ‖f' x - g' x - (f x - g x)‖ ≤ ‖f' x - f x‖ + ‖g' x - g x‖ := by
      rw [show f' x - g' x - (f x - g x) = (f' x - f x) - (g' x - g x) by abel]
      exact norm_sub_le _ _
    have e1 := hε x hx'
    have e2 := hε' x hx'
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(abs_le.1 a1).1, (abs_le.1 a1).2, (abs_le.1 a2).1,
      (abs_le.1 a2).2, (abs_le.1 a3).1, (abs_le.1 a3).2]

/-- (3.2) for the pair `(μ_{δf} - μ_{δ0}, μ_{δg} - μ_{δ0})` of continuous profiles. -/
theorem scaleCov_eq_logCov_graph_zero (hd : 0 < d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    (δ : ℝ) {f g : ℝ → Rd (d - 1)} (hf : Continuous f) (hg : Continuous g) :
    scaleCov κ (Ioi 0) (graphMeasure d δ f) (graphMeasure d δ 0) (graphMeasure d δ g)
      (graphMeasure d δ 0) =
    logCov (graphMeasure d δ f) (graphMeasure d δ 0) (graphMeasure d δ g) (graphMeasure d δ 0) := by
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hg.continuousOn
  set M := max (max C₁ C₂) 0 with hM
  have h1 : ∀ x ∈ Icc (0 : ℝ) 1, ‖f x‖ ≤ M := fun x hx =>
    (hC₁ x hx).trans ((le_max_left _ _).trans (le_max_left _ _))
  have h2 : ∀ x ∈ Icc (0 : ℝ) 1, ‖g x‖ ≤ M := fun x hx =>
    (hC₂ x hx).trans ((le_max_right _ _).trans (le_max_left _ _))
  have h0 : ∀ x ∈ Icc (0 : ℝ) 1, ‖(0 : ℝ → Rd (d - 1)) x‖ ≤ M := fun x _ => by
    simp only [Pi.zero_apply, norm_zero, hM, le_max_right]
  exact scaleCov_eq_logCov_graph (f₁ := f) (f₂ := 0) (f₃ := g) (f₄ := 0) hd hκ hf.measurable
    measurable_const hg.measurable measurable_const h1 h0 h2 h0

/-- The graph covariances `δ⁻¹ logCov(μ_{δf} - μ_{δ0}, μ_{δg} - μ_{δ0})` are PSD on every finite
family of continuous profiles (they are Gram kernels, `psdOn_scaleCov`, and equal `scaleCov` by
(3.2)). -/
theorem psdOn_graph_logCov (hd : 0 < d) {ι : Type*} (F : Finset ι) {δ : ℝ} (hδ : 0 ≤ δ)
    (f : ι → ℝ → Rd (d - 1)) (hf : ∀ i ∈ F, Continuous (f i)) :
    PSDOn F (fun i j => δ⁻¹ * logCov (graphMeasure d δ (f i)) (graphMeasure d δ 0)
      (graphMeasure d δ (f j)) (graphMeasure d δ 0)) := by
  obtain ⟨κ, hκ⟩ := exists_isLFPPKernel d
  have h := Var.psdOn_const_mul (psdOn_scaleCov (κ := κ) (Ioi 0) F
    (fun i => graphMeasure d δ (f i)) (fun _ => graphMeasure d δ 0)) (inv_nonneg.2 hδ)
  refine psdOn_congr (fun i hi j hj => ?_) h
  rw [scaleCov_eq_logCov_graph_zero hd hκ δ (hf i hi) (hf j hj)]

/-- **Moving profiles** (HA2 D6, corollary; HA4 D5, step 1): if `f_{δ,i} → f_i` and
`f_{δ,j} → f_j` uniformly on `[0,1]` (all continuous), then
`δ⁻¹ logCov(μ_{δ f_{δ,i}} - μ_{δ0}, μ_{δ f_{δ,j}} - μ_{δ0}) → gCov f_i f_j`. -/
theorem tendsto_graph_logCov_moving (hd : 0 < d) {f g : ℝ → Rd (d - 1)}
    {fδ gδ : ℝ → ℝ → Rd (d - 1)} (hf : Continuous f) (hg : Continuous g)
    (hfδ : ∀ᶠ δ in 𝓝[>] 0, Continuous (fδ δ)) (hgδ : ∀ᶠ δ in 𝓝[>] 0, Continuous (gδ δ))
    (hfc : TendstoUniformlyOn fδ f (𝓝[>] 0) (Icc 0 1))
    (hgc : TendstoUniformlyOn gδ g (𝓝[>] 0) (Icc 0 1)) :
    Tendsto (fun δ => δ⁻¹ * logCov (graphMeasure d δ (fδ δ)) (graphMeasure d δ 0)
      (graphMeasure d δ (gδ δ)) (graphMeasure d δ 0)) (𝓝[>] 0) (𝓝 (gCov f g)) := by
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hg.continuousOn
  set M := max C₁ C₂ + 1 with hMdef
  have hMpos : 0 ≤ M := by
    have := (norm_nonneg (f 0)).trans (hC₁ 0 ⟨le_rfl, zero_le_one⟩)
    have := le_max_left C₁ C₂
    linarith
  -- eventual bounds from uniform convergence
  have hclose : ∀ {F : ℝ → ℝ → Rd (d - 1)} {F₀ : ℝ → Rd (d - 1)},
      TendstoUniformlyOn F F₀ (𝓝[>] 0) (Icc 0 1) → ∀ η > 0,
      ∀ᶠ δ in 𝓝[>] 0, ∀ x ∈ Icc (0 : ℝ) 1, ‖F δ x - F₀ x‖ ≤ η := by
    intro F F₀ hF η hη
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hF η hη] with δ hδ x hx
    have := hδ x hx
    rw [dist_eq_norm, norm_sub_rev] at this
    exact this.le
  have hM : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ x ∈ Icc (0 : ℝ) 1, ‖fδ δ x‖ ≤ M ∧
      ‖(0 : ℝ → Rd (d - 1)) x‖ ≤ M ∧ ‖gδ δ x‖ ≤ M ∧ ‖(0 : ℝ → Rd (d - 1)) x‖ ≤ M := by
    filter_upwards [hclose hfc 1 one_pos, hclose hgc 1 one_pos] with δ h1 h2 x hx
    have a1 := norm_le_insert' (fδ δ x) (f x)
    have a2 := norm_le_insert' (gδ δ x) (g x)
    have b1 := (hC₁ x hx).trans (le_max_left C₁ C₂)
    have b2 := (hC₂ x hx).trans (le_max_right C₁ C₂)
    refine ⟨by linarith [h1 x hx], by simpa using hMpos, by linarith [h2 x hx],
      by simpa using hMpos⟩
  -- equicontinuity of the moving profiles at interior points
  have hequi : ∀ {F : ℝ → ℝ → Rd (d - 1)} {F₀ : ℝ → Rd (d - 1)}, Continuous F₀ →
      TendstoUniformlyOn F F₀ (𝓝[>] 0) (Icc 0 1) → ∀ x ∈ Ioo (0 : ℝ) 1, ∀ w : ℝ,
      Tendsto (fun δ => F δ (δ * w + x) - F δ x) (𝓝[>] 0) (𝓝 0) := by
    intro F F₀ hF₀ hF x hx w
    have h1 : Tendsto (fun δ : ℝ => δ * w + x) (𝓝[>] 0) (𝓝 x) := by
      have h0 : Tendsto (fun δ : ℝ => δ * w + x) (𝓝 0) (𝓝 (0 * w + x)) :=
        ((continuous_id.mul continuous_const).add continuous_const).tendsto 0
      rw [zero_mul, zero_add] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun δ : ℝ => δ * w + x) (𝓝[>] 0) (𝓝[Icc 0 1] x) :=
      tendsto_nhdsWithin_iff.2 ⟨h1, h1.eventually (Icc_mem_nhds hx.1 hx.2)⟩
    have h3 := (hF.tendsto_comp hF₀.continuousWithinAt h2).sub
      (hF.tendsto_at (Ioo_subset_Icc_self hx))
    rwa [sub_self] at h3
  have hzero : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ w : ℝ, Tendsto (fun δ : ℝ =>
      (0 : ℝ → Rd (d - 1)) (δ * w + x) - (0 : ℝ → Rd (d - 1)) x) (𝓝[>] 0) (𝓝 0) := by
    intro x _ w
    simp
  have h := tendsto_graph_logCov_sub_fourLim hd (l := 𝓝[>] (0 : ℝ)) tendsto_id fδ (fun _ => 0)
    gδ (fun _ => 0) M (by
      filter_upwards [hfδ, hgδ] with δ h1 h2
      exact ⟨h1, continuous_const, h2, continuous_const⟩) hM (hequi hg hgc) hzero
  -- `gCov (fδ δ) (gδ δ) → gCov f g`
  have hcov : Tendsto (fun δ => gCov (fδ δ) (gδ δ)) (𝓝[>] 0) (𝓝 (gCov f g)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hη : 0 < ε / (8 * Real.pi) := by positivity
    filter_upwards [hclose hfc _ hη, hclose hgc _ hη, hfδ, hgδ] with δ h1 h2 c1 c2
    rw [Real.dist_eq]
    have := abs_gCov_sub_le (hf.intervalIntegrable 0 1) (hg.intervalIntegrable 0 1)
      (c1.intervalIntegrable 0 1) (c2.intervalIntegrable 0 1) h1 h2
    have e : 2 * Real.pi * (ε / (8 * Real.pi) + ε / (8 * Real.pi)) = ε / 2 := by
      field_simp
      ring
    linarith
  have h' := h.add hcov
  rw [zero_add] at h'
  refine h'.congr' ?_
  filter_upwards with δ
  simp only [id, fourLim_zero, sub_add_cancel]

/-- **Lemma 3.2 for finite families with moving profiles and drifts** (HA2 D6, corollary;
HA4 D5, step 1): for a finite family `F`, continuous profiles `f_{δ,i} → f_i` uniformly on
`[0,1]` and drifts `b_δ(i) → b(i)`,
`𝕄_F(δ⁻¹ logCov(μ_{δ f_{δ,i}} - μ_{δ0}, μ_{δ f_{δ,j}} - μ_{δ0}), b_δ) → 𝕄_F(gCov(f_i, f_j), b)`. -/
theorem tendsto_gEM_graph (hd : 0 < d) {ι : Type} (F : Finset ι) (f : ι → ℝ → Rd (d - 1))
    (fδ : ℝ → ι → ℝ → Rd (d - 1)) (b : ι → ℝ) (bδ : ℝ → ι → ℝ)
    (hf : ∀ i ∈ F, Continuous (f i)) (hfδ : ∀ᶠ δ in 𝓝[>] 0, ∀ i ∈ F, Continuous (fδ δ i))
    (hconv : ∀ i ∈ F, TendstoUniformlyOn (fun δ => fδ δ i) (f i) (𝓝[>] 0) (Icc 0 1))
    (hb : ∀ i ∈ F, Tendsto (fun δ => bδ δ i) (𝓝[>] 0) (𝓝 (b i))) :
    Tendsto (fun δ => gaussianExpectedMax F (fun i j => δ⁻¹ * logCov (graphMeasure d δ (fδ δ i))
        (graphMeasure d δ 0) (graphMeasure d δ (fδ δ j)) (graphMeasure d δ 0)) (bδ δ))
      (𝓝[>] 0) (𝓝 (gaussianExpectedMax F (fun i j => gCov (f i) (f j)) b)) := by
  refine tendsto_gEM F ?_ (Var.gCov_psdOn F f fun i hi => (hf i hi).intervalIntegrable 0 1)
    (fun i hi j hj => tendsto_graph_logCov_moving hd (hf i hi) (hf j hj)
      (hfδ.mono fun δ h => h i hi) (hfδ.mono fun δ h => h j hj) (hconv i hi) (hconv j hj)) hb
  filter_upwards [hfδ, self_mem_nhdsWithin] with δ h hδ
  exact psdOn_graph_logCov hd F (le_of_lt hδ) (fun i => fδ δ i) h

/-- **Lemma 3.2 for finite families, all-scale covariance form**: as `tendsto_gEM_graph`, with
the covariance `δ⁻¹ Cov(⟨h, μ_{δ f_{δ,i}} - μ_{δ0}⟩, ⟨h, μ_{δ f_{δ,j}} - μ_{δ0}⟩)` of the
all-scale field for an admissible kernel `κ`. -/
theorem tendsto_gEM_graph_scaleCov (hd : 0 < d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {ι : Type}
    (F : Finset ι) (f : ι → ℝ → Rd (d - 1)) (fδ : ℝ → ι → ℝ → Rd (d - 1)) (b : ι → ℝ)
    (bδ : ℝ → ι → ℝ) (hf : ∀ i ∈ F, Continuous (f i))
    (hfδ : ∀ᶠ δ in 𝓝[>] 0, ∀ i ∈ F, Continuous (fδ δ i))
    (hconv : ∀ i ∈ F, TendstoUniformlyOn (fun δ => fδ δ i) (f i) (𝓝[>] 0) (Icc 0 1))
    (hb : ∀ i ∈ F, Tendsto (fun δ => bδ δ i) (𝓝[>] 0) (𝓝 (b i))) :
    Tendsto (fun δ => gaussianExpectedMax F (fun i j => δ⁻¹ * scaleCov κ (Ioi 0)
        (graphMeasure d δ (fδ δ i)) (graphMeasure d δ 0) (graphMeasure d δ (fδ δ j))
        (graphMeasure d δ 0)) (bδ δ))
      (𝓝[>] 0) (𝓝 (gaussianExpectedMax F (fun i j => gCov (f i) (f j)) b)) := by
  refine (tendsto_gEM_graph hd F f fδ b bδ hf hfδ hconv hb).congr' ?_
  filter_upwards [hfδ] with δ h
  refine LQGDimension.gaussianExpectedMax_congr F _ fun i hi j hj => ?_
  rw [scaleCov_eq_logCov_graph_zero hd hκ δ (h i hi) (h j hj)]

end GraphFinite

/-! ## The lattice form: `expectedSupLimit` on index sets with finite-dimensional coordinates -/

section Lattice

/-- **`LQGDimension.expectedSupLimit` transported along an injective coordinate map** into a
finite-dimensional real normed space `X` (HA2 D6, "(3.8″)", parametrization step). -/
theorem expectedSupLimit_of_injOn {ι X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] (φ : ι → X) (K : Set ι) (hinj : InjOn φ K)
    (hK : IsCompact (φ '' K)) (Cδ : ℝ → ι → ι → ℝ) (C : ι → ι → ℝ) (bδ : ℝ → ι → ℝ)
    (b : X → ℝ) (L : ℝ)
    (hCδ : ∀ δ > 0, ∀ F : Finset ι, ↑F ⊆ K → PSDOn F (Cδ δ))
    (hC : ∀ F : Finset ι, ↑F ⊆ K → PSDOn F C)
    (hconv : ∀ θ > 0, ∀ᶠ δ in 𝓝[>] 0, ∀ f ∈ K, ∀ g ∈ K,
      |Cδ δ f g - C f g| ≤ θ ∧ |bδ δ f - b (φ f)| ≤ θ)
    (hmod : ∀ᶠ δ in 𝓝[>] 0, ∀ f ∈ K, ∀ g ∈ K,
      Cδ δ f f - 2 * Cδ δ f g + Cδ δ g g ≤ L * ‖φ f - φ g‖)
    (hb : ContinuousOn b (φ '' K)) :
    ∀ θ > 0, ∀ᶠ δ in 𝓝[>] 0, ∀ F : Finset ι, ↑F ⊆ K → ∃ G : Finset ι, ↑G ⊆ K ∧
      gaussianExpectedMax F (Cδ δ) (bδ δ) ≤ gaussianExpectedMax G C (fun f => b (φ f)) + θ := by
  classical
  intro θ hθ
  rcases K.eq_empty_or_nonempty with hKe | ⟨f₀, hf₀⟩
  · refine Eventually.of_forall fun δ F hF => ⟨∅, by simp, ?_⟩
    have hF0 : F = ∅ := by
      rw [hKe] at hF
      exact Finset.coe_eq_empty.1 (subset_empty_iff.1 hF)
    rw [hF0, Var.gEM_empty, Var.gEM_empty]
    linarith
  have : Nonempty ι := ⟨f₀⟩
  let D := Module.finrank ℝ X
  let e : X ≃L[ℝ] (Fin D → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [Module.finrank_fin_fun])
  let ψ : ι → (Fin D → ℝ) := fun f => e (φ f)
  let ψinv : (Fin D → ℝ) → ι := Function.invFunOn ψ K
  have hψinj : InjOn ψ K := fun f hf g hg h => hinj hf hg (e.injective h)
  have hleft : ∀ f ∈ K, ψinv (ψ f) = f := fun f hf => hψinj.leftInvOn_invFunOn hf
  have hmemK : ∀ p ∈ ψ '' K, ψinv p ∈ K := fun p hp => Function.invFunOn_mem hp
  have hright : ∀ p ∈ ψ '' K, ψ (ψinv p) = p := fun p hp => Function.invFunOn_eq hp
  have hφinv : ∀ p ∈ ψ '' K, φ (ψinv p) = e.symm p := fun p hp => by
    have := congrArg e.symm (hright p hp)
    simpa [ψ] using this
  have hK' : IsCompact (ψ '' K) := by
    have h := hK.image e.continuous
    rwa [image_image] at h
  set L' := max L 0 * ‖(e.symm : (Fin D → ℝ) →L[ℝ] X)‖ with hL'
  have hsub : ∀ F' : Finset (Fin D → ℝ), ↑F' ⊆ ψ '' K → ↑(F'.image ψinv) ⊆ K := by
    intro F' hF' x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
    exact hmemK p (hF' hp)
  have hESL := LQGDimension.expectedSupLimit D (ψ '' K) hK'
    (fun δ p q => Cδ δ (ψinv p) (ψinv q)) (fun p q => C (ψinv p) (ψinv q))
    (fun δ p => bδ δ (ψinv p)) (fun p => b (e.symm p)) L'
    (fun δ hδ F' hF' => psdOn_comp ψinv (hCδ δ hδ _ (hsub F' hF')))
    (fun F' hF' => psdOn_comp ψinv (hC _ (hsub F' hF')))
    (by
      intro η hη
      filter_upwards [hconv η hη] with δ h p hp q hq
      obtain ⟨h1, h2⟩ := h _ (hmemK p hp) _ (hmemK q hq)
      refine ⟨h1, ?_⟩
      rwa [hφinv p hp] at h2)
    (by
      filter_upwards [hmod] with δ h p hp q hq
      refine (h _ (hmemK p hp) _ (hmemK q hq)).trans ?_
      rw [hφinv p hp, hφinv q hq, ← map_sub]
      calc L * ‖e.symm (p - q)‖ ≤ max L 0 * ‖e.symm (p - q)‖ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        _ ≤ max L 0 * (‖(e.symm : (Fin D → ℝ) →L[ℝ] X)‖ * ‖p - q‖) :=
            mul_le_mul_of_nonneg_left
              ((e.symm : (Fin D → ℝ) →L[ℝ] X).le_opNorm (p - q)) (le_max_right _ _)
        _ = L' * ‖p - q‖ := by rw [hL', mul_assoc])
    (hb.comp e.symm.continuous.continuousOn (by
      rintro p ⟨f, hf, rfl⟩
      exact ⟨f, hf, by simp [ψ]⟩))
    θ hθ
  filter_upwards [hESL, self_mem_nhdsWithin] with δ hδ hδpos F hF
  have hF' : ↑(F.image ψ) ⊆ ψ '' K := by
    intro p hp
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hp
    exact mem_image_of_mem ψ (hF hf)
  obtain ⟨G', hG', hle⟩ := hδ (F.image ψ) hF'
  refine ⟨G'.image ψinv, hsub G' hG', ?_⟩
  have e1 : gaussianExpectedMax (F.image ψ) (fun p q => Cδ δ (ψinv p) (ψinv q))
      (fun p => bδ δ (ψinv p)) = gaussianExpectedMax F (Cδ δ) (bδ δ) := by
    rw [Var.gEM_image F ψ _ _ (psdOn_comp ψinv (hCδ δ hδpos _ (hsub _ hF'))),
      LQGDimension.gaussianExpectedMax_congr F (fun i => bδ δ (ψinv (ψ i))) (C' := Cδ δ)
        fun i hi j hj => by simp only [hleft i (hF hi), hleft j (hF hj)]]
    exact gEM_congr_drift F _ fun i hi => by simp only [hleft i (hF hi)]
  have e2 : gaussianExpectedMax (G'.image ψinv) C (fun f => b (φ f)) =
      gaussianExpectedMax G' (fun p q => C (ψinv p) (ψinv q)) (fun p => b (e.symm p)) := by
    rw [Var.gEM_image G' ψinv C _ (hC _ (hsub G' hG'))]
    exact gEM_congr_drift G' _ fun p hp => by simp only [hφinv p (hG' hp)]
  rw [← e1, e2]
  exact hle

/-- **The lattice form on `V_n(E)`** (HA2 (3.8″); HA3 D5, Step 1d): for `K ⊆ V_n(E)` with compact
vertex image, PSD covariances `Cδ → C` uniformly on `K × K` with the modulus
`Cδ(f,f) - 2 Cδ(f,g) + Cδ(g,g) ≤ L ‖verts f - verts g‖`, drifts `bδ → b ∘ verts` uniformly on
`K`, and `b` continuous on the vertex image: for every `θ > 0`, for all small `δ`, every finite
`F ⊆ K` has a finite `G ⊆ K` with `𝕄_F(Cδ, bδ) ≤ 𝕄_G(C, b ∘ verts) + θ`. -/
theorem expectedSupLimit_Vg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} (K : Set (ℝ → E)) (hK : K ⊆ Vg E n)
    (hKc : IsCompact (verts n '' K)) (Cδ : ℝ → (ℝ → E) → (ℝ → E) → ℝ)
    (C : (ℝ → E) → (ℝ → E) → ℝ) (bδ : ℝ → (ℝ → E) → ℝ) (b : (Fin (2 ^ n + 1) → E) → ℝ)
    (L : ℝ) (hCδ : ∀ δ > 0, ∀ F : Finset (ℝ → E), ↑F ⊆ K → PSDOn F (Cδ δ))
    (hC : ∀ F : Finset (ℝ → E), ↑F ⊆ K → PSDOn F C)
    (hconv : TendstoUniformlyOn (fun δ (p : (ℝ → E) × (ℝ → E)) => Cδ δ p.1 p.2)
      (fun p => C p.1 p.2) (𝓝[>] 0) (K ×ˢ K))
    (hbconv : TendstoUniformlyOn bδ (fun f => b (verts n f)) (𝓝[>] 0) K)
    (hmod : ∀ᶠ δ in 𝓝[>] 0, ∀ f ∈ K, ∀ g ∈ K,
      Cδ δ f f - 2 * Cδ δ f g + Cδ δ g g ≤ L * ‖verts n f - verts n g‖)
    (hb : ContinuousOn b (verts n '' K)) :
    ∀ θ > 0, ∀ᶠ δ in 𝓝[>] 0, ∀ F : Finset (ℝ → E), ↑F ⊆ K → ∃ G : Finset (ℝ → E), ↑G ⊆ K ∧
      gaussianExpectedMax F (Cδ δ) (bδ δ) ≤
        gaussianExpectedMax G C (fun f => b (verts n f)) + θ := by
  refine expectedSupLimit_of_injOn (verts n) K ((injOn_verts n).mono hK) hKc Cδ C bδ b L hCδ hC
    ?_ hmod hb
  intro θ hθ
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hconv θ hθ,
    Metric.tendstoUniformlyOn_iff.1 hbconv θ hθ] with δ h1 h2 f hf g hg
  refine ⟨?_, ?_⟩
  · have := h1 (f, g) ⟨hf, hg⟩
    rw [Real.dist_eq, abs_sub_comm] at this
    exact this.le
  · have := h2 f hf
    rw [Real.dist_eq, abs_sub_comm] at this
    exact this.le

end Lattice

/-! ## The lattice expected supremum `gaussESup` and its convergence -/

section ESup

/-- **Lattice expected supremum** (HA2's `gaussESup`, the convention of `LQGDimension.aE`): the
supremum over finite subfamilies `F ⊆ S` of `E max_{i ∈ F} (X_i + b_i)` for the centered
Gaussian family with covariance `C`. -/
def gaussESup {ι : Type*} (S : Set ι) (C : ι → ι → ℝ) (b : ι → ℝ) : EReal :=
  ⨆ F : Finset S, ((gaussianExpectedMax F (fun i j => C i j) (fun i => b i) : ℝ) : EReal)

theorem le_gaussESup {ι : Type*} (S : Set ι) (C : ι → ι → ℝ) (b : ι → ℝ) (F : Finset S) :
    ((gaussianExpectedMax F (fun i j => C i j) (fun i => b i) : ℝ) : EReal) ≤
      gaussESup S C b :=
  le_iSup (fun F : Finset S => ((gaussianExpectedMax F (fun i j => C i j) (fun i => b i) : ℝ) :
    EReal)) F

theorem gaussESup_nonneg {ι : Type*} (S : Set ι) (C : ι → ι → ℝ) (b : ι → ℝ) :
    0 ≤ gaussESup S C b := by
  have := le_gaussESup S C b ∅
  rwa [Var.gEM_empty, EReal.coe_zero] at this

/-- Reindexing a finite family of the subtype `S` to the ambient type. -/
theorem gEM_subtype {ι : Type*} [DecidableEq ι] {S : Set ι} (F : Finset S) (C : ι → ι → ℝ)
    (b : ι → ℝ) (hC : PSDOn (F.image Subtype.val) C) :
    gaussianExpectedMax F (fun i j => C i j) (fun i => b i) =
      gaussianExpectedMax (F.image Subtype.val) C b := by
  rw [Var.gEM_image F Subtype.val C b hC]

/-- **Convergence of lattice expected suprema** from the `expectedSupLimit` upper bound and the
finite-family limit (HA2 D6, "(3.8″)": limsup by `expectedSupLimit`, liminf by Chatterjee). -/
theorem tendsto_gaussESup_of {ι : Type} (K : Set ι) (Cδ : ℝ → ι → ι → ℝ) (C : ι → ι → ℝ)
    (bδ : ℝ → ι → ℝ) (b : ι → ℝ) (hCδ : ∀ δ > 0, ∀ F : Finset ι, ↑F ⊆ K → PSDOn F (Cδ δ))
    (hC : ∀ F : Finset ι, ↑F ⊆ K → PSDOn F C)
    (hCconv : ∀ f ∈ K, ∀ g ∈ K, Tendsto (fun δ => Cδ δ f g) (𝓝[>] 0) (𝓝 (C f g)))
    (hbconv : ∀ f ∈ K, Tendsto (fun δ => bδ δ f) (𝓝[>] 0) (𝓝 (b f)))
    (hupper : ∀ θ > 0, ∀ᶠ δ in 𝓝[>] 0, ∀ F : Finset ι, ↑F ⊆ K → ∃ G : Finset ι, ↑G ⊆ K ∧
      gaussianExpectedMax F (Cδ δ) (bδ δ) ≤ gaussianExpectedMax G C b + θ) :
    Tendsto (fun δ => gaussESup K (Cδ δ) (bδ δ)) (𝓝[>] 0) (𝓝 (gaussESup K C b)) := by
  classical
  have himg : ∀ F : Finset K, ↑(F.image Subtype.val) ⊆ K := by
    intro F x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
    exact y.2
  rw [tendsto_order]
  constructor
  · -- liminf: one finite family at a time
    intro a ha
    obtain ⟨F, hF⟩ := lt_iSup_iff.1 ha
    have hlim : Tendsto (fun δ => gaussianExpectedMax F (fun i j => Cδ δ i j)
        (fun i => bδ δ i)) (𝓝[>] 0)
        (𝓝 (gaussianExpectedMax F (fun i j => C i j) (fun i => b i))) := by
      refine tendsto_gEM F ?_ ?_ (fun i _ j _ => hCconv i i.2 j j.2) (fun i _ => hbconv i i.2)
      · filter_upwards [self_mem_nhdsWithin] with δ hδ
        exact psdOn_comp Subtype.val (hCδ δ hδ _ (himg F))
      · exact psdOn_comp Subtype.val (hC _ (himg F))
    have hlim' := (continuous_coe_real_ereal.tendsto _).comp hlim
    filter_upwards [(tendsto_order.1 hlim').1 a hF] with δ hδ
    exact hδ.trans_le (le_gaussESup K (Cδ δ) (bδ δ) F)
  · -- limsup: `expectedSupLimit`
    intro a ha
    have hL0 := gaussESup_nonneg K C b
    have hLtop : gaussESup K C b ≠ ⊤ := ne_top_of_lt ha
    have hLbot : gaussESup K C b ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot 0) hL0
    obtain ⟨x, hx1, hx2⟩ := EReal.lt_iff_exists_real_btwn.1 ha
    set ℓ := (gaussESup K C b).toReal with hℓ
    have hLℓ : gaussESup K C b = (ℓ : EReal) := (EReal.coe_toReal hLtop hLbot).symm
    have hℓx : ℓ < x := by rw [hLℓ] at hx1; exact EReal.coe_lt_coe_iff.1 hx1
    have hθ : 0 < (x - ℓ) / 2 := by linarith
    filter_upwards [hupper _ hθ, self_mem_nhdsWithin] with δ hδ hδpos
    refine lt_of_le_of_lt ?_ hx2
    refine iSup_le fun F => ?_
    obtain ⟨G, hG, hle⟩ := hδ (F.image Subtype.val) (himg F)
    have hG' : (G.subtype (· ∈ K)).image Subtype.val = G := by
      ext x
      simp only [Finset.mem_image, Finset.mem_subtype]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, hG hx⟩, hx, rfl⟩
    have hGle : gaussianExpectedMax G C b ≤ ℓ := by
      have h1 := le_gaussESup K C b (G.subtype (· ∈ K))
      rw [gEM_subtype _ C b (by rw [hG']; exact hC G hG), hG', hLℓ] at h1
      exact EReal.coe_le_coe_iff.1 h1
    rw [gEM_subtype F (Cδ δ) (bδ δ) (hCδ δ hδpos _ (himg F))]
    refine EReal.coe_le_coe_iff.2 ?_
    linarith

end ESup

/-! ## (3.8″) for graph measures: HA2's `Lemma32ESup` -/

section Lemma32ESup

variable {d : ℕ}

/-- `logCov μ ν μ' ν' = logCov μ' ν' μ ν` for s-finite measures. -/
theorem integral_neglog_swap (α β : Measure (Rd d)) [SFinite α] [SFinite β] :
    ∫ q, -Real.log ‖q.1 - q.2‖ ∂(α.prod β) = ∫ q, -Real.log ‖q.1 - q.2‖ ∂(β.prod α) := by
  rw [← integral_prod_swap]
  simp only [Prod.fst_swap, Prod.snd_swap, norm_sub_rev]

theorem logCov_comm (μ ν μ' ν' : Measure (Rd d)) [SFinite μ] [SFinite ν] [SFinite μ']
    [SFinite ν'] : logCov μ ν μ' ν' = logCov μ' ν' μ ν := by
  unfold logCov
  rw [integral_neglog_swap μ μ', integral_neglog_swap μ ν', integral_neglog_swap ν μ',
    integral_neglog_swap ν ν']
  ring

/-- The canonical distance of the polarized family: for s-finite measures,
`Λ(A - Z, A - Z) - 2 Λ(A - Z, B - Z) + Λ(B - Z, B - Z) = Λ(A - B, A - B)`. -/
theorem logCov_canonical (A B Z : Measure (Rd d)) [SFinite A] [SFinite B] [SFinite Z] :
    logCov A Z A Z - 2 * logCov A Z B Z + logCov B Z B Z = logCov A B A B := by
  unfold logCov
  rw [integral_neglog_swap Z A, integral_neglog_swap B A, integral_neglog_swap Z B]
  ring

/-- **(3.8″)**, log form: for `K ⊆ V_n(ℝ^{d-1})` with compact vertex image, `b` continuous on
the vertex image and `b_δ → b ∘ verts` uniformly on `K`,
`ESup_K(δ⁻¹ logCov(μ_{δf} - μ_{δ0}, μ_{δg} - μ_{δ0}), b_δ) → ESup_K(gCov, b ∘ verts)`. -/
theorem tendsto_gaussESup_graph (hd : 0 < d) (n : ℕ) (K : Set (ℝ → Rd (d - 1)))
    (hK : K ⊆ Vg (Rd (d - 1)) n) (hKc : IsCompact (verts n '' K))
    (b : (Fin (2 ^ n + 1) → Rd (d - 1)) → ℝ) (bδ : ℝ → (ℝ → Rd (d - 1)) → ℝ)
    (hb : ContinuousOn b (verts n '' K))
    (hbδ : TendstoUniformlyOn bδ (fun f => b (verts n f)) (𝓝[>] 0) K) :
    Tendsto (fun δ => gaussESup K (fun f g => δ⁻¹ * logCov (graphMeasure d δ f)
        (graphMeasure d δ 0) (graphMeasure d δ g) (graphMeasure d δ 0)) (bδ δ)) (𝓝[>] 0)
      (𝓝 (gaussESup K gCov (fun f => b (verts n f)))) := by
  obtain ⟨R, hR⟩ := exists_subset_vertBall hK hKc.isBounded
  have hcont : ∀ f ∈ K, Continuous f := fun f hf => Var.Vg_continuous (hK hf)
  have hunif := tendstoUniformlyOn_graph_logCov_of_bounded hd hK hKc.isBounded
  have hPSD : ∀ δ > 0, ∀ F : Finset (ℝ → Rd (d - 1)), ↑F ⊆ K → PSDOn F (fun f g =>
      δ⁻¹ * logCov (graphMeasure d δ f) (graphMeasure d δ 0) (graphMeasure d δ g)
        (graphMeasure d δ 0)) :=
    fun δ hδ F hF => psdOn_graph_logCov hd F hδ.le id fun f hf => hcont f (hF hf)
  have hPSD' : ∀ F : Finset (ℝ → Rd (d - 1)), ↑F ⊆ K → PSDOn F gCov :=
    fun F hF => Var.gCov_psdOn F id fun f hf => (hcont f (hF hf)).intervalIntegrable 0 1
  -- the modulus, from (3.9)
  obtain ⟨C₉, hC₉0, hC₉⟩ := graph_logCov_le (d := d) hd
  have hmod : ∀ᶠ δ in 𝓝[>] 0, ∀ f ∈ K, ∀ g ∈ K,
      δ⁻¹ * logCov (graphMeasure d δ f) (graphMeasure d δ 0) (graphMeasure d δ f)
          (graphMeasure d δ 0) -
        2 * (δ⁻¹ * logCov (graphMeasure d δ f) (graphMeasure d δ 0) (graphMeasure d δ g)
          (graphMeasure d δ 0)) +
        δ⁻¹ * logCov (graphMeasure d δ g) (graphMeasure d δ 0) (graphMeasure d δ g)
          (graphMeasure d δ 0) ≤ C₉ * ‖verts n f - verts n g‖ := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ f hf g hg
    have e := logCov_canonical (graphMeasure d δ f) (graphMeasure d δ g) (graphMeasure d δ 0)
    have hfg : ∀ x ∈ Icc (0 : ℝ) 1, ‖f x - g x‖ ≤ ‖verts n f - verts n g‖ := by
      intro x _
      have h1 := Vg_norm_le_norm_verts (Var.sub_mem_Vg (hK hf) (hK hg)) x
      rwa [verts_sub, Pi.sub_apply] at h1
    have h := hC₉ δ R ‖verts n f - verts n g‖ hδ f g (hcont f hf).measurable
      (hcont g hg).measurable (fun x _ => Vg_norm_le_of_verts (hR hf).1 (hR hf).2 x)
      (fun x _ => Vg_norm_le_of_verts (hR hg).1 (hR hg).2 x) hfg
    calc δ⁻¹ * logCov (graphMeasure d δ f) (graphMeasure d δ 0) (graphMeasure d δ f)
            (graphMeasure d δ 0) -
          2 * (δ⁻¹ * logCov (graphMeasure d δ f) (graphMeasure d δ 0) (graphMeasure d δ g)
            (graphMeasure d δ 0)) +
          δ⁻¹ * logCov (graphMeasure d δ g) (graphMeasure d δ 0) (graphMeasure d δ g)
            (graphMeasure d δ 0)
        = δ⁻¹ * logCov (graphMeasure d δ f) (graphMeasure d δ g) (graphMeasure d δ f)
            (graphMeasure d δ g) := by rw [← e]; ring
      _ ≤ δ⁻¹ * |logCov (graphMeasure d δ f) (graphMeasure d δ g) (graphMeasure d δ f)
            (graphMeasure d δ g)| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (inv_nonneg.2 (le_of_lt hδ))
      _ ≤ C₉ * ‖verts n f - verts n g‖ := h
  refine tendsto_gaussESup_of K _ gCov bδ (fun f => b (verts n f)) hPSD hPSD'
    (fun f hf g hg => hunif.tendsto_at (x := (f, g)) (mk_mem_prod hf hg))
    (fun f hf => hbδ.tendsto_at (x := f) hf) ?_
  exact expectedSupLimit_Vg K hK hKc _ gCov bδ b C₉ hPSD hPSD' hunif hbδ hmod hb

/-- **(3.8″), HA2's `Lemma32ESup`** (all-scale covariance form, admissible kernel `κ`). -/
theorem lemma32ESup (hd : 0 < d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) (n : ℕ)
    (K : Set (ℝ → Rd (d - 1))) (hK : K ⊆ Vg (Rd (d - 1)) n) (hKc : IsCompact (verts n '' K))
    (b : (Fin (2 ^ n + 1) → Rd (d - 1)) → ℝ) (bδ : ℝ → (ℝ → Rd (d - 1)) → ℝ)
    (hb : ContinuousOn b (verts n '' K))
    (hbδ : TendstoUniformlyOn bδ (fun f => b (verts n f)) (𝓝[>] 0) K) :
    Tendsto (fun δ => gaussESup K (fun f g => δ⁻¹ * scaleCov κ (Ioi 0) (graphMeasure d δ f)
        (graphMeasure d δ 0) (graphMeasure d δ g) (graphMeasure d δ 0)) (bδ δ)) (𝓝[>] 0)
      (𝓝 (gaussESup K gCov (fun f => b (verts n f)))) := by
  refine (tendsto_gaussESup_graph hd n K hK hKc b bδ hb hbδ).congr fun δ => ?_
  unfold gaussESup
  congr 1
  funext F
  refine congrArg (fun r : ℝ => (r : EReal)) ?_
  refine LQGDimension.gaussianExpectedMax_congr F _ fun i _ j _ => ?_
  show δ⁻¹ * logCov (graphMeasure d δ (i : ℝ → Rd (d - 1))) (graphMeasure d δ 0)
      (graphMeasure d δ (j : ℝ → Rd (d - 1))) (graphMeasure d δ 0) =
    δ⁻¹ * scaleCov κ (Ioi 0) (graphMeasure d δ (i : ℝ → Rd (d - 1))) (graphMeasure d δ 0)
      (graphMeasure d δ (j : ℝ → Rd (d - 1))) (graphMeasure d δ 0)
  rw [scaleCov_eq_logCov_graph_zero hd hκ δ (Var.Vg_continuous (hK i.2))
    (Var.Vg_continuous (hK j.2))]

end Lemma32ESup

end HigherDimLFPP
