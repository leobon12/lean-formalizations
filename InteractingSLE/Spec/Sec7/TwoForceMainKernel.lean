/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Constructions.Cylinders
import InteractingSLE.Spec.Sobolev.ThinRange

/-!
# Conditional kernels in §7.1: the measure-theoretic steps

Packet PROVE-SEC7-A2 (specification §7.1, pp. 229–252). Abstract probabilistic cores of the kernel
arguments of Aux. lemmas 48, 49, 51, 56 and Proposition 7.3.

* **Equal kernels give equal joint laws** (`map_prod_eq_of_condExp_exp_eq`): Aux. lemma 51 ("Integrating the
  equal kernels against the common stopped driving law proves equality of the full joint laws", p. 242)
  and Aux. lemma 56 ("Equality of the full conditional field kernels and of the driving marginal gives
  equality of the stopped joint laws", p. 251). Two couplings of a random distribution `hᵢ` on `U` with a
  recorded history `Hᵢ`; conditionally on a finer `σ`-algebra `𝒥ᵢ ⊇ σ(Hᵢ)` (e.g. retaining field
  germs) the conditional characteristic functions of `hᵢ` are one common measurable function `Ψ` of
  the history. If the history laws agree, the joint laws agree.
* **Equality of the full laws from nested finite histories** (`map_prod_pi_eq_of_forall_map_eq`):
  Proposition 7.3, p. 243: "The histories through the integer times are nested. … Equality of their
  finite stopped joint laws, each retaining the whole field, gives equality of the full field–curve
  joint laws."
* **Passing conditional characteristic functions to an announced time** (`ae_eq_on_iUnion_of_tendsto`,
  `tendsto_ae_condExp_complex`, `condExp_iSup_eq_on_iUnion`, `aux48_condExp_charFun_limit`): the step
  (PK5) → birth kernel of Aux. lemma 48 (p. 232: "Increasing conditional-expectation convergence applies
  to the bounded random variable on the left … Combining (PK4) and (PK5) therefore gives the asserted
  Gaussian characteristic function conditionally on `Γ_{σ_z−}`").
* **The pasting step** (`aux49_pasting_step`): one step of the finite-batch pasting of Aux. lemma 49
  (p. 234) and of (PF1)–(PF3): with a pocket observable `X` revealed at a birth and an active-field
  observable `Y`, `E[X Y | 𝓗_t] = k_X k_Y`, from the birth kernel (iii), the active kernel (iv) and the
  freezing identity (i) = (GB5).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

namespace InteractingSLE

namespace Sec7

open LQGMetric TopologicalSpace

/-! ### Equal kernels give equal joint laws (Aux. lemmas 51, 56) -/

section KernelLaw

variable {U : Opens ℂ} {Γ : Type*} [mΓ : MeasurableSpace Γ]

/-- In one coupling: if the conditional characteristic function of `h` given `𝒥 ⊇ σ(H)` is
`Ψ(H, ·)`, then `E[1_B(H) e^{i(h, φ)}] = ∫_B Ψ(·, φ) d(law H)`. -/
theorem setIntegral_exp_map_eq_of_condExp {Ψ : Γ → TestOn U → ℂ}
    (hΨ : ∀ φ, Measurable fun x => Ψ x φ) {Ω : Type*} {J mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn U} {H : Ω → Γ} (hh : Measurable h) (hH : Measurable H)
    (hHJ : mΓ.comap H ≤ J) (hJ : J ≤ mΩ) (φ : TestOn U)
    (hc : P[fun ω => Complex.exp (↑(h ω φ) * Complex.I) | J] =ᵐ[P] fun ω => Ψ (H ω) φ)
    {B : Set Γ} (hB : MeasurableSet B) :
    ∫ p in univ ×ˢ B, Complex.exp (↑(p.1 φ) * Complex.I) ∂(P.map fun ω => (h ω, H ω)) =
      ∫ x in B, Ψ x φ ∂(P.map H) := by
  have hUB : MeasurableSet (univ ×ˢ B : Set (DistOn U × Γ)) := MeasurableSet.univ.prod hB
  have hm1 : Measurable fun p : DistOn U × Γ => Complex.exp (↑(p.1 φ) * Complex.I) :=
    Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      ((Sobolev.measurable_distOn_apply φ).comp measurable_fst)).mul_const _)
  rw [setIntegral_map hUB hm1.aestronglyMeasurable (hh.prodMk hH).aemeasurable,
    setIntegral_map hB (hΨ φ).aestronglyMeasurable hH.aemeasurable]
  have hpre : (fun ω => (h ω, H ω)) ⁻¹' (univ ×ˢ B) = H ⁻¹' B := by ext; simp
  rw [hpre]
  have hs : MeasurableSet[J] (H ⁻¹' B) := hHJ _ ⟨B, hB, rfl⟩
  have hint : Integrable (fun ω => Complex.exp (↑(h ω φ) * Complex.I)) P :=
    Sobolev.integrable_exp_mul_I ((Sobolev.measurable_distOn_apply φ).comp hh)
  rw [← setIntegral_condExp hJ hint hs]
  exact setIntegral_congr_ae (hJ _ hs) (hc.mono fun ω h1 _ => h1)

/-- **Equal kernels give equal joint laws** (Aux. lemma 51, p. 242; Aux. lemma 56, p. 251). Two
couplings `(hᵢ, Hᵢ)` of a random distribution on `U` and a recorded history; conditionally on a finer
`σ`-algebra `𝒥ᵢ ⊇ σ(Hᵢ)` the characteristic functions `E[e^{i(hᵢ, φ)} | 𝒥ᵢ]` are the same measurable
function `Ψ(Hᵢ, φ)` of the history (for a Gaussian kernel, `Ψ(x, φ) = e^{i m(x)(φ) - C(x)(φ)/2}`). If
the history laws agree, the joint laws of `(hᵢ, Hᵢ)` agree. -/
theorem map_prod_eq_of_condExp_exp_eq {Ψ : Γ → TestOn U → ℂ} (hΨ : ∀ φ, Measurable fun x => Ψ x φ)
    {Ω₁ : Type*} {J₁ m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {h₁ : Ω₁ → DistOn U} {H₁ : Ω₁ → Γ} (hh₁ : Measurable h₁) (hH₁ : Measurable H₁)
    (hHJ₁ : mΓ.comap H₁ ≤ J₁) (hJ₁ : J₁ ≤ m₁)
    (hc₁ : ∀ φ : TestOn U,
      P₁[fun ω => Complex.exp (↑(h₁ ω φ) * Complex.I) | J₁] =ᵐ[P₁] fun ω => Ψ (H₁ ω) φ)
    {Ω₂ : Type*} {J₂ m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {h₂ : Ω₂ → DistOn U} {H₂ : Ω₂ → Γ} (hh₂ : Measurable h₂) (hH₂ : Measurable H₂)
    (hHJ₂ : mΓ.comap H₂ ≤ J₂) (hJ₂ : J₂ ≤ m₂)
    (hc₂ : ∀ φ : TestOn U,
      P₂[fun ω => Complex.exp (↑(h₂ ω φ) * Complex.I) | J₂] =ᵐ[P₂] fun ω => Ψ (H₂ ω) φ)
    (hlaw : P₁.map H₁ = P₂.map H₂) :
    P₁.map (fun ω => (h₁ ω, H₁ ω)) = P₂.map (fun ω => (h₂ ω, H₂ ω)) := by
  refine Sobolev.measure_eq_of_setIntegral_exp fun φ B hB => ?_
  rw [setIntegral_exp_map_eq_of_condExp hΨ hh₁ hH₁ hHJ₁ hJ₁ φ (hc₁ φ) hB,
    setIntegral_exp_map_eq_of_condExp hΨ hh₂ hH₂ hHJ₂ hJ₂ φ (hc₂ φ) hB, hlaw]

end KernelLaw

/-! ### Full laws from nested finite histories (Proposition 7.3) -/

section Nested

variable {E : Type*} [mE : MeasurableSpace E] {Γ : ℕ → Type*} [∀ n, MeasurableSpace (Γ n)]

omit mE [∀ n, MeasurableSpace (Γ n)] in
/-- A cylinder event of nested histories is read off the `N`-th history. -/
theorem preimage_prod_cylinder_ae_eq {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω}
    {h : Ω → E} {X : ∀ n, Ω → Γ n} {π : ∀ n m, n ≤ m → Γ m → Γ n} {A : Set E} {s : Finset ℕ}
    {S : Set (∀ i : s, Γ i)} {N : ℕ} (hle : ∀ i ∈ s, i ≤ N)
    (hX : ∀ i, ∀ᵐ ω ∂P, ∀ hi : i ≤ N, X i ω = π i N hi (X N ω)) :
    (fun ω => (h ω, fun n => X n ω)) ⁻¹' (A ×ˢ cylinder s S) =ᵐ[P]
      (fun ω => (h ω, X N ω)) ⁻¹' (A ×ˢ ((fun (z : Γ N) (i : s) => π i N (hle i i.2) z) ⁻¹' S)) := by
  have hall : ∀ᵐ ω ∂P, ∀ i, ∀ hi : i ≤ N, X i ω = π i N hi (X N ω) := ae_all_iff.2 hX
  filter_upwards [hall] with ω hω
  have hrs : (s.restrict fun n => X n ω) = fun i : s => π i N (hle i i.2) (X N ω) := by
    funext i
    exact hω i (hle i i.2)
  simp only [mem_preimage, mem_prod, mem_cylinder, hrs]

/-- **Equality of the full joint laws from nested finite histories** (Proposition 7.3, p. 243). Two
couplings of a random element `hᵢ` (the field) with a sequence of histories `Xᵢ n` (the stopped
histories through the integer times) which are nested by common measurable maps (`X n = π(X m)` for
`n ≤ m`, almost surely in both couplings). If for every `n` the joint laws of `(hᵢ, Xᵢ n)` agree, then
the joint laws of `hᵢ` and the whole sequence agree. -/
theorem map_prod_pi_eq_of_forall_map_eq
    {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsFiniteMeasure P₁]
    {h₁ : Ω₁ → E} {X₁ : ∀ n, Ω₁ → Γ n} (hh₁ : Measurable h₁) (hX₁ : ∀ n, Measurable (X₁ n))
    {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsFiniteMeasure P₂]
    {h₂ : Ω₂ → E} {X₂ : ∀ n, Ω₂ → Γ n} (hh₂ : Measurable h₂) (hX₂ : ∀ n, Measurable (X₂ n))
    (hnest : ∀ n m, n ≤ m → ∃ π : Γ m → Γ n, Measurable π ∧
      (∀ᵐ ω ∂P₁, X₁ n ω = π (X₁ m ω)) ∧ ∀ᵐ ω ∂P₂, X₂ n ω = π (X₂ m ω))
    (hlaw : ∀ n, P₁.map (fun ω => (h₁ ω, X₁ n ω)) = P₂.map (fun ω => (h₂ ω, X₂ n ω))) :
    P₁.map (fun ω => (h₁ ω, fun n => X₁ n ω)) = P₂.map (fun ω => (h₂ ω, fun n => X₂ n ω)) := by
  classical
  choose π hπ hπ₁ hπ₂ using hnest
  have hm₁ : Measurable fun ω => (h₁ ω, fun n => X₁ n ω) := hh₁.prodMk (measurable_pi_iff.2 hX₁)
  have hm₂ : Measurable fun ω => (h₂ ω, fun n => X₂ n ω) := hh₂.prodMk (measurable_pi_iff.2 hX₂)
  set C₂ := measurableCylinders Γ
  set C := Set.image2 (fun x1 x2 => x1 ×ˢ x2) {A : Set E | MeasurableSet A} C₂
  have hcylU : (univ : Set (∀ n, Γ n)) ∈ C₂ := by
    rw [mem_measurableCylinders]
    exact ⟨∅, univ, MeasurableSet.univ, by simp [cylinder]⟩
  have hspan₂ : IsCountablySpanning C₂ := ⟨fun _ => univ, fun _ => hcylU, iUnion_const univ⟩
  have hgen : (inferInstance : MeasurableSpace (E × ∀ n, Γ n)) = MeasurableSpace.generateFrom C := by
    calc (inferInstance : MeasurableSpace (E × ∀ n, Γ n))
        = @Prod.instMeasurableSpace _ _ (MeasurableSpace.generateFrom {A : Set E | MeasurableSet A})
            (MeasurableSpace.generateFrom C₂) := by
          rw [MeasurableSpace.generateFrom_measurableSet, generateFrom_measurableCylinders]
      _ = MeasurableSpace.generateFrom C :=
          generateFrom_prod_eq isCountablySpanning_measurableSet hspan₂
  have hrect : ∀ s ∈ C, (P₁.map fun ω => (h₁ ω, fun n => X₁ n ω)) s =
      (P₂.map fun ω => (h₂ ω, fun n => X₂ n ω)) s := by
    rintro _ ⟨A, hA, t, ht, rfl⟩
    rw [mem_measurableCylinders] at ht
    obtain ⟨s, S, hS, rfl⟩ := ht
    set N := s.sup id
    have hle : ∀ i ∈ s, i ≤ N := fun i hi => Finset.le_sup (f := id) hi
    -- the cylinder is read off the `N`-th history
    have hR : Measurable fun (z : Γ N) (i : s) => π i N (hle i i.2) z :=
      measurable_pi_iff.2 fun (i : s) => hπ i N (hle i i.2)
    have hT : MeasurableSet (A ×ˢ ((fun (z : Γ N) (i : s) => π i N (hle i i.2) z) ⁻¹' S)) :=
      hA.prod (hR hS)
    have hcyl : MeasurableSet (A ×ˢ cylinder s S) := hA.prod (measurable_restrict _ hS)
    have hX₁' : ∀ i, ∀ᵐ ω ∂P₁, ∀ hi : i ≤ N, X₁ i ω = π i N hi (X₁ N ω) := fun i => by
      by_cases hi : i ≤ N
      · filter_upwards [hπ₁ i N hi] with ω hω _
        exact hω
      · exact ae_of_all _ fun ω hi' => absurd hi' hi
    have hX₂' : ∀ i, ∀ᵐ ω ∂P₂, ∀ hi : i ≤ N, X₂ i ω = π i N hi (X₂ N ω) := fun i => by
      by_cases hi : i ≤ N
      · filter_upwards [hπ₂ i N hi] with ω hω _
        exact hω
      · exact ae_of_all _ fun ω hi' => absurd hi' hi
    rw [Measure.map_apply hm₁ hcyl, Measure.map_apply hm₂ hcyl,
      measure_congr (preimage_prod_cylinder_ae_eq hle hX₁'),
      measure_congr (preimage_prod_cylinder_ae_eq hle hX₂'), ← Measure.map_apply (hh₁.prodMk (hX₁ N)) hT,
      ← Measure.map_apply (hh₂.prodMk (hX₂ N)) hT, hlaw N]
  refine ext_of_generate_finite C hgen
    (MeasurableSpace.isPiSystem_measurableSet.prod isPiSystem_measurableCylinders) hrect ?_
  have := hrect (univ ×ˢ univ) ⟨univ, MeasurableSet.univ, univ, hcylU, rfl⟩
  rwa [univ_prod_univ] at this

end Nested

/-! ### Passing conditional characteristic functions to an announced time (Aux. lemma 48) -/

section Upward

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- If `Fₙ → F_∞` almost surely, `Fₙ = Ψₙ` almost surely on an increasing sequence of events `Eₙ`, and
`Ψₙ → Ψ'` on `⋃ Eₙ`, then `F_∞ = Ψ'` almost surely on `⋃ Eₙ`. -/
theorem ae_eq_on_iUnion_of_tendsto {α : Type*} [TopologicalSpace α] [T2Space α]
    {F : ℕ → Ω → α} {F' : Ω → α} (hF : ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) atTop (𝓝 (F' ω)))
    {E : ℕ → Set Ω} (hE : Monotone E) {Ψ : ℕ → Ω → α} {Ψ' : Ω → α}
    (hn : ∀ n, ∀ᵐ ω ∂μ, ω ∈ E n → F n ω = Ψ n ω)
    (hlim : ∀ᵐ ω ∂μ, ω ∈ ⋃ n, E n → Tendsto (fun n => Ψ n ω) atTop (𝓝 (Ψ' ω))) :
    ∀ᵐ ω ∂μ, ω ∈ ⋃ n, E n → F' ω = Ψ' ω := by
  filter_upwards [hF, ae_all_iff.2 hn, hlim] with ω hFω hnω hlω hω
  obtain ⟨N, hN⟩ := mem_iUnion.1 hω
  have hev : (fun n => F n ω) =ᶠ[atTop] fun n => Ψ n ω :=
    eventually_atTop.2 ⟨N, fun n hn => hnω n (hE hn hN)⟩
  exact tendsto_nhds_unique (hFω.congr' hev) (hlω hω)

/-- **Lévy's upward theorem for complex variables.** -/
theorem tendsto_ae_condExp_complex [IsFiniteMeasure μ] {𝓖 : Filtration ℕ mΩ} {Y : Ω → ℂ}
    (hY : Integrable Y μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => μ[Y | 𝓖 n] ω) atTop (𝓝 (μ[Y | ⨆ n, 𝓖 n] ω)) := by
  have hre : ∀ m : MeasurableSpace Ω,
      (fun ω => (μ[Y | m] ω).re) =ᵐ[μ] μ[fun ω => (Y ω).re | m] := fun m =>
    Complex.reCLM.comp_condExp_comm hY
  have him : ∀ m : MeasurableSpace Ω,
      (fun ω => (μ[Y | m] ω).im) =ᵐ[μ] μ[fun ω => (Y ω).im | m] := fun m =>
    Complex.imCLM.comp_condExp_comm hY
  filter_upwards [tendsto_ae_condExp (μ := μ) (ℱ := 𝓖) (fun ω => (Y ω).re),
    tendsto_ae_condExp (μ := μ) (ℱ := 𝓖) (fun ω => (Y ω).im), ae_all_iff.2 fun n => hre (𝓖 n),
    ae_all_iff.2 fun n => him (𝓖 n), hre (⨆ n, 𝓖 n), him (⨆ n, 𝓖 n)]
    with ω h1 h2 h3 h4 h5 h6
  have e : ∀ z : ℂ, z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := fun z => (Complex.re_add_im z).symm
  rw [e (μ[Y | ⨆ n, 𝓖 n] ω), h5, h6]
  have hfun : (fun n => μ[Y | 𝓖 n] ω) =
      fun n => ((μ[fun ω => (Y ω).re | 𝓖 n] ω : ℝ) : ℂ) +
        ((μ[fun ω => (Y ω).im | 𝓖 n] ω : ℝ) : ℂ) * Complex.I := by
    funext n
    rw [e (μ[Y | 𝓖 n] ω), h3 n, h4 n]
  rw [hfun]
  exact ((Complex.continuous_ofReal.tendsto _).comp h1).add
    (((Complex.continuous_ofReal.tendsto _).comp h2).mul_const _)

/-- Conditional expectations given the announced `σ`-algebra `⨆ₙ 𝓖ₙ`, on an increasing sequence of
events, from convergent versions at the announcing times. -/
theorem condExp_iSup_eq_on_iUnion [IsFiniteMeasure μ] {𝓖 : Filtration ℕ mΩ} {Y : Ω → ℂ}
    (hY : Integrable Y μ) {E : ℕ → Set Ω} (hE : Monotone E) {Ψ : ℕ → Ω → ℂ} {Ψ' : Ω → ℂ}
    (hn : ∀ n, ∀ᵐ ω ∂μ, ω ∈ E n → μ[Y | 𝓖 n] ω = Ψ n ω)
    (hlim : ∀ᵐ ω ∂μ, ω ∈ ⋃ n, E n → Tendsto (fun n => Ψ n ω) atTop (𝓝 (Ψ' ω))) :
    ∀ᵐ ω ∂μ, ω ∈ ⋃ n, E n → μ[Y | ⨆ n, 𝓖 n] ω = Ψ' ω :=
  ae_eq_on_iUnion_of_tendsto (tendsto_ae_condExp_complex hY) hE hn hlim

/-- The real version (conditional means). -/
theorem condExp_iSup_eq_on_iUnion_real {𝓖 : Filtration ℕ mΩ} [IsFiniteMeasure μ] {Y : Ω → ℝ}
    {E : ℕ → Set Ω} (hE : Monotone E) {Ψ : ℕ → Ω → ℝ} {Ψ' : Ω → ℝ}
    (hn : ∀ n, ∀ᵐ ω ∂μ, ω ∈ E n → μ[Y | 𝓖 n] ω = Ψ n ω)
    (hlim : ∀ᵐ ω ∂μ, ω ∈ ⋃ n, E n → Tendsto (fun n => Ψ n ω) atTop (𝓝 (Ψ' ω))) :
    ∀ᵐ ω ∂μ, ω ∈ ⋃ n, E n → μ[Y | ⨆ n, 𝓖 n] ω = Ψ' ω :=
  ae_eq_on_iUnion_of_tendsto (tendsto_ae_condExp Y) hE hn hlim

/-- **The birth kernel from the announcing kernels** (Aux. lemma 48, (PK5) and its limit, p. 232).
Finitely many observables `Xⱼ = (h, φⱼ)`; on increasing events `Eₙ` (the tests lie in the active domain
at the announcing stop `σₙ`) the conditional characteristic function given `Γ_{σₙ}` is Gaussian with
mean `Mₙ` and covariance `Gₙ`, and on `⋃ Eₙ` the means and covariances converge to `M'`, `G'` (the latter
is (PK4)). Then, given the announced `σ`-algebra `Γ_{σ−} = ⋁ₙ Γ_{σₙ}`, the conditional characteristic
function is the Gaussian one with mean `M'` and covariance `G'` on `⋃ Eₙ`. -/
theorem aux48_condExp_charFun_limit [IsProbabilityMeasure μ] {𝓖 : Filtration ℕ mΩ} {ι : Type*}
    [Fintype ι] {X : ι → Ω → ℝ} (hX : ∀ j, Measurable (X j)) (u : ι → ℝ)
    {E : ℕ → Set Ω} (hE : Monotone E) {M : ℕ → ι → Ω → ℝ} {G : ℕ → ι → ι → Ω → ℝ}
    {M' : ι → Ω → ℝ} {G' : ι → ι → Ω → ℝ}
    (hn : ∀ n, ∀ᵐ ω ∂μ, ω ∈ E n →
      μ[fun ω => Complex.exp (↑(∑ j, u j * X j ω) * Complex.I) | 𝓖 n] ω =
        Complex.exp (↑(∑ j, u j * M n j ω) * Complex.I -
          ↑((1 / 2 : ℝ) * ∑ j, ∑ k, u j * u k * G n j k ω)))
    (hM : ∀ᵐ ω ∂μ, ω ∈ ⋃ n, E n → ∀ j, Tendsto (fun n => M n j ω) atTop (𝓝 (M' j ω)))
    (hG : ∀ᵐ ω ∂μ, ω ∈ ⋃ n, E n → ∀ j k, Tendsto (fun n => G n j k ω) atTop (𝓝 (G' j k ω))) :
    ∀ᵐ ω ∂μ, ω ∈ ⋃ n, E n →
      μ[fun ω => Complex.exp (↑(∑ j, u j * X j ω) * Complex.I) | ⨆ n, 𝓖 n] ω =
        Complex.exp (↑(∑ j, u j * M' j ω) * Complex.I -
          ↑((1 / 2 : ℝ) * ∑ j, ∑ k, u j * u k * G' j k ω)) := by
  have hmeas : Measurable fun ω => ∑ j, u j * X j ω :=
    Finset.measurable_sum _ fun j _ => (hX j).const_mul _
  refine condExp_iSup_eq_on_iUnion (Sobolev.integrable_exp_mul_I hmeas) hE hn ?_
  filter_upwards [hM, hG] with ω hMω hGω hω
  have h1 : Tendsto (fun n => ∑ j, u j * M n j ω) atTop (𝓝 (∑ j, u j * M' j ω)) :=
    tendsto_finsetSum _ fun j _ => (hMω hω j).const_mul _
  have h2 : Tendsto (fun n => (1 / 2 : ℝ) * ∑ j, ∑ k, u j * u k * G n j k ω) atTop
      (𝓝 ((1 / 2 : ℝ) * ∑ j, ∑ k, u j * u k * G' j k ω)) :=
    (tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun k _ =>
      (hGω hω j k).const_mul _).const_mul _
  exact (Complex.continuous_exp.tendsto _).comp
    ((((Complex.continuous_ofReal.tendsto _).comp h1).mul_const _).sub
      ((Complex.continuous_ofReal.tendsto _).comp h2))

end Upward

/-! ### The pasting step (Aux. lemma 49) -/

section Pasting

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]

/-- **The pasting step of Aux. lemma 49** (p. 234; also (PF1)–(PF3)). Let `X` be a bounded observable of
the fields in pockets born at an own-filtration time `τ ≤ t`, measurable for the germ `σ`-algebra
`𝓖 = 𝓖_t` (germs only grow), and `Y` an integrable active-field observable at time `t`. Assume
* (iii) the birth kernel: `E[X | Pτ_τ] = k_X` with `k_X` measurable for the recorded history `𝓗_τ ≤ Pτ_τ`;
* (iv) the active kernel: `E[Y | 𝓖_t] = k_Y` with `k_Y` measurable for the recorded history `𝓗_t ≤ 𝓖_t`;
* (i) freezing, (GB5): `E[X | 𝓗_t] = E[X | 𝓗_τ]`.
Then `E[X Y | 𝓗_t] = k_X k_Y`. -/
theorem aux49_pasting_step {𝓗τ 𝓗t Pτ 𝓖 : MeasurableSpace Ω} (h𝓗τPτ : 𝓗τ ≤ Pτ) (hPτ : Pτ ≤ m₀)
    (h𝓗t𝓖 : 𝓗t ≤ 𝓖) (h𝓖 : 𝓖 ≤ m₀) {X Y kX kY : Ω → ℝ} (hX : StronglyMeasurable[𝓖] X) {C : ℝ}
    (hXb : ∀ᵐ ω ∂μ, ‖X ω‖ ≤ C) (hY : Integrable Y μ)
    (hfreeze : μ[X | 𝓗t] =ᵐ[μ] μ[X | 𝓗τ])
    (hkX : StronglyMeasurable[𝓗τ] kX) (hXk : μ[X | Pτ] =ᵐ[μ] kX)
    (hkY : StronglyMeasurable[𝓗t] kY) (hYk : μ[Y | 𝓖] =ᵐ[μ] kY) :
    μ[X * Y | 𝓗t] =ᵐ[μ] kX * kY := by
  have h𝓗τ : 𝓗τ ≤ m₀ := h𝓗τPτ.trans hPτ
  have hXm : AEStronglyMeasurable[m₀] X μ := (hX.mono h𝓖).aestronglyMeasurable
  have hXi : Integrable X μ := Integrable.of_bound hXm C hXb
  have hXY : Integrable (X * Y) μ := hY.bdd_mul hXm hXb
  have hkYi : Integrable kY μ := integrable_condExp.congr hYk
  have hXkY : Integrable (X * kY) μ := hkYi.bdd_mul hXm hXb
  have hkXi : Integrable kX μ := integrable_condExp.congr hXk
  -- `E[X | 𝓗_t] = k_X`
  have hXt : μ[X | 𝓗t] =ᵐ[μ] kX :=
    calc μ[X | 𝓗t] =ᵐ[μ] μ[X | 𝓗τ] := hfreeze
      _ =ᵐ[μ] μ[μ[X | Pτ] | 𝓗τ] := (condExp_condExp_of_le h𝓗τPτ hPτ).symm
      _ =ᵐ[μ] μ[kX | 𝓗τ] := condExp_congr_ae hXk
      _ = kX := condExp_of_stronglyMeasurable h𝓗τ hkX hkXi
  calc μ[X * Y | 𝓗t] =ᵐ[μ] μ[μ[X * Y | 𝓖] | 𝓗t] := (condExp_condExp_of_le h𝓗t𝓖 h𝓖).symm
    _ =ᵐ[μ] μ[X * kY | 𝓗t] := by
        refine condExp_congr_ae ?_
        filter_upwards [condExp_mul_of_stronglyMeasurable_left hX hXY hY, hYk] with ω h1 h2
        rw [h1, Pi.mul_apply, Pi.mul_apply, h2]
    _ =ᵐ[μ] μ[X | 𝓗t] * kY := condExp_mul_of_stronglyMeasurable_right hkY hXkY hXi
    _ =ᵐ[μ] kX * kY := by
        filter_upwards [hXt] with ω h
        rw [Pi.mul_apply, Pi.mul_apply, h]

end Pasting

end Sec7

end InteractingSLE
