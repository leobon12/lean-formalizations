/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Prop65DDSExp
import QuantumZipper.Proofs.RS.TransienceCanon
import QuantumZipper.Proofs.Probability.BMExistence
import MathFin.Probability.Brownian.ExpMartingaleBrownian
import MathFin.Probability.Brownian.BrownianMartingale

/-!
# Proposition 6.5, Brownian representation, part 3: completion by an independent Brownian motion

Packet PROVE-SEC6-E (specification §6.1, `source/spec/p145-192.md`, `#prop-6.5`, p. 158: "If the
clock has a finite terminal value, the Brownian motion may be completed on an enlarged probability
space").

**Abstract setting.** On `(Ω, P)` a filtration `𝓗`, a continuous process `N` with `N₀ = 0` and a
clock `ℓ` with `ℓ_u ≤ u` and `ℓ_s = min(s, ℓ_u)` for `s ≤ u` (that is, `ℓ_u = min(u, ℓ_∞)`), both
`𝓗`-adapted, such that `e^{a N_u − a² ℓ_u / 2}` is an `𝓗`-martingale in the integral form
`E[W e^{a N_u − a² ℓ_u/2}] = E[W e^{a N_s − a² ℓ_s/2}]` (`W ≥ 0` `𝓗_s`-measurable). On the product
`Ω × Ω₀` with an independent Brownian motion `B` (QuantumZipper's, with its natural filtration),

  `β_u = N_u + B_u − B_{ℓ_u}`

is a Brownian motion (`exists_isBrownianReal_completion`), and `β_u = N_u` when `ℓ_u = u`.

**Proof.** For a box `B₁ × B₂` (`B₁ ∈ 𝓗_s`, `B₂` in the past of `B` at `s`), Fubini splits
`E[1_{B₁×B₂} e^{aβ_u − a²u/2}]` into the `Ω`-factor `e^{a N_u − a² ℓ_u/2}` and the Brownian factor
`e^{a(B_u − B_{ℓ_u}) − a²(u − ℓ_u)/2}`, whose integral over `B₂` equals that at time `s` with the
same `ℓ_u` (independent increments, `lintegral_mul_exp_bmE`), and depends on `ℓ_u` only through
`min(s, ℓ_u) = ℓ_s`; the `Ω`-martingale identity with the weight `1_{B₁} Ψ(ℓ_s)` finishes. Boxes form
a π-system generating `𝓖_s = 𝓗_s ⊗ 𝓑_s`; MathFin's `isBrownianReal_of_expMartingale` concludes.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

namespace InteractingSLE.Sec6.Prop65

/-! ### The Brownian factor -/

section BM

variable {Ω₀ : Type*} [m₀ : MeasurableSpace Ω₀] {P₀ : Measure Ω₀} {B : ℝ≥0 → Ω₀ → ℝ}

/-- The exponent `a(B_r − B_{r∧x}) − a²(r − r∧x)/2` of the Brownian factor. -/
def bmE (B : ℝ≥0 → Ω₀ → ℝ) (a : ℝ) (r x : ℝ≥0) (w : Ω₀) : ℝ :=
  a * (B r w - B (min r x) w) - a ^ 2 * ((r : ℝ) - ((min r x : ℝ≥0) : ℝ)) / 2

omit m₀ in
lemma bmE_factor (a : ℝ) {s t : ℝ≥0} (hst : s ≤ t) (x : ℝ≥0) (w : Ω₀) :
    bmE B a t x w = bmE B a s x w + (a * (B t w - B (max s (min t x)) w) -
      a ^ 2 * ((t : ℝ) - ((max s (min t x) : ℝ≥0) : ℝ)) / 2) := by
  rcases le_total x s with hxs | hsx
  · have h1 : min t x = x := min_eq_right (hxs.trans hst)
    have h2 : min s x = x := min_eq_right hxs
    have h3 : max s x = s := max_eq_left hxs
    simp only [bmE, h1, h2, h3]
    ring
  · rcases le_total x t with hxt | htx
    · have h1 : min t x = x := min_eq_right hxt
      have h2 : min s x = s := min_eq_left hsx
      have h3 : max s x = x := max_eq_right hsx
      simp only [bmE, h1, h2, h3, sub_self]
      ring
    · have h1 : min t x = t := min_eq_left htx
      have h2 : min s x = s := min_eq_left (hst.trans htx)
      have h3 : max s t = t := max_eq_right hst
      simp only [bmE, h1, h2, h3, sub_self]
      ring

omit m₀ in
lemma bmE_min (a : ℝ) (s x : ℝ≥0) (w : Ω₀) : bmE B a s (min s x) w = bmE B a s x w := by
  simp only [bmE, min_self, ← min_assoc]

omit m₀ in
lemma bmE_self (a : ℝ) (s : ℝ≥0) (w : Ω₀) : bmE B a s s w = 0 := by
  simp only [bmE, min_self, sub_self, mul_zero, zero_div]

/-- The exponential moment of a Brownian increment: `E[e^{a(B_t − B_p) − a²(t − p)/2}] = 1`. -/
theorem lintegral_exp_incr [IsProbabilityMeasure P₀] (hB : IsPreBrownianReal B P₀) (a : ℝ)
    {p t : ℝ≥0} (hpt : p ≤ t) :
    ∫⁻ w, ENNReal.ofReal (Real.exp (a * (B t w - B p w) - a ^ 2 * ((t : ℝ) - (p : ℝ)) / 2)) ∂P₀
      = 1 := by
  have hlaw := MathFin.hasLaw_increment hB hpt
  set c : ℝ := a ^ 2 * ((t : ℝ) - (p : ℝ)) / 2 with hc
  have hm : Measurable fun y : ℝ => ENNReal.ofReal (Real.exp (a * y - c)) := by fun_prop
  have h1 : ∫⁻ w, ENNReal.ofReal (Real.exp (a * (B t w - B p w) - c)) ∂P₀ =
      ∫⁻ y, ENNReal.ofReal (Real.exp (a * y - c)) ∂(gaussianReal 0 (t - p)) := by
    rw [← hlaw.map_eq, lintegral_map' hm.aemeasurable hlaw.aemeasurable]
  rw [h1]
  have hint : Integrable (fun y : ℝ => Real.exp (a * y - c)) (gaussianReal 0 (t - p)) := by
    have := (integrable_exp_mul_gaussianReal (μ := 0) (v := t - p) a).mul_const (Real.exp (-c))
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only [← Real.exp_add, sub_eq_add_neg]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun y => (Real.exp_pos _).le)]
  have e : ∀ y : ℝ, Real.exp (a * y - c) = Real.exp (a * y) * Real.exp (-c) := fun y => by
    rw [← Real.exp_add, sub_eq_add_neg]
  simp only [e]
  rw [integral_mul_const, integral_exp_mul_gaussianReal_zero, ← Real.exp_add,
    NNReal.coe_sub hpt, hc]
  simp only [add_neg_cancel, Real.exp_zero, ENNReal.ofReal_one]

/-- **The Brownian factor is a martingale in its time** (integral form): for `s ≤ t`, every `x` and
every `𝓦_s`-measurable `f ≥ 0`, `E[f e^{bmE t x}] = E[f e^{bmE s x}]` (independent increments). -/
theorem lintegral_mul_exp_bmE [IsProbabilityMeasure P₀] {𝓦 : Filtration ℝ≥0 m₀}
    (hB : IsFilteredPreBrownian B 𝓦 P₀) (a : ℝ) {s t : ℝ≥0} (hst : s ≤ t) (x : ℝ≥0)
    {f : Ω₀ → ℝ≥0∞} (hf : Measurable[𝓦 s] f) :
    ∫⁻ w, f w * ENNReal.ofReal (Real.exp (bmE B a t x w)) ∂P₀ =
      ∫⁻ w, f w * ENNReal.ofReal (Real.exp (bmE B a s x w)) ∂P₀ := by
  set p := max s (min t x) with hp
  have hsp : s ≤ p := le_max_left _ _
  have hpt : p ≤ t := max_le hst (min_le_left _ _)
  have hBad : ∀ r, Measurable[𝓦 r] (B r) := fun r => (hB.stronglyAdapted r).measurable
  have hEs : Measurable[𝓦 p] (fun w => bmE B a s x w) := by
    have h1 : Measurable[𝓦 p] (B s) := (hBad s).mono (𝓦.mono hsp) le_rfl
    have h2 : Measurable[𝓦 p] (B (min s x)) :=
      (hBad _).mono (𝓦.mono ((min_le_left _ _).trans hsp)) le_rfl
    exact ((h1.sub h2).const_mul a).sub_const _
  set F : Ω₀ → ℝ≥0∞ := fun w => f w * ENNReal.ofReal (Real.exp (bmE B a s x w)) with hF
  have hFm : Measurable[𝓦 p] F := (hf.mono (𝓦.mono hsp) le_rfl).mul
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hEs))
  set φ : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (a * y - a ^ 2 * ((t : ℝ) - (p : ℝ)) / 2))
    with hφ
  have hφm : Measurable φ := by fun_prop
  set g : Ω₀ → ℝ≥0∞ := fun w => φ ((B t - B p) w) with hg
  have hD : Measurable (B t - B p) :=
    ((hBad t).mono (𝓦.le t) le_rfl).sub ((hBad p).mono (𝓦.le p) le_rfl)
  have hgD : Measurable[MeasurableSpace.comap (B t - B p) inferInstance] g :=
    hφm.comp (Measurable.of_comap_le le_rfl)
  have hind : IndepFun F g P₀ := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left (hB.indep p t hpt).symm
      hFm.comap_le) hgD.comap_le
  have hfac : ∀ w, f w * ENNReal.ofReal (Real.exp (bmE B a t x w)) = (F * g) w := by
    intro w
    simp only [hF, hg, hφ, Pi.mul_apply, Pi.sub_apply]
    rw [bmE_factor a hst x w, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]
  simp_rw [hfac]
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (hFm.mono (𝓦.le p) le_rfl)
    (f := F) (g := g) (hφm.comp hD) hind]
  have h1 : ∫⁻ w, g w ∂P₀ = 1 := lintegral_exp_incr hB.toIsPreBrownianReal a hpt
  rw [h1, mul_one]

end BM

/-! ### The completion -/

section Product

universe u

theorem measurable_completion {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {N : α → ℝ} (hN : Measurable N) {c : α → ℝ≥0} (hc : Measurable c) {B : ℝ≥0 → β → ℝ}
    (hBc : ∀ w, Continuous fun r => B r w) (hBm : ∀ r, Measurable (B r)) (u : ℝ≥0) :
    Measurable fun p : α × β => N p.1 + B u p.2 - B (c p.1) p.2 :=
  ((hN.comp measurable_fst).add ((hBm u).comp measurable_snd)).sub
    ((measurable_uncurry_of_continuous_of_measurable hBc hBm).comp
      ((hc.comp measurable_fst).prodMk measurable_snd))

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The data of the completion: `N` and `ℓ` adapted to `𝓗`, `ℓ_u ≤ u` and `ℓ_s = min(s, ℓ_u)` for
`s ≤ u`, `N` continuous from `N₀ = 0`, and `e^{a N − a² ℓ/2}` an `𝓗`-martingale in integral form. -/
structure IsTCExpMartingale (P : Measure Ω) (𝓗 : Filtration ℝ≥0 mΩ) (N : ℝ≥0 → Ω → ℝ)
    (ℓ : ℝ≥0 → Ω → ℝ≥0) : Prop where
  measurable_N : ∀ u, Measurable[𝓗 u] (N u)
  measurable_ℓ : ∀ u, Measurable[𝓗 u] (ℓ u)
  le : ∀ u ω, ℓ u ω ≤ u
  min_eq : ∀ s u ω, s ≤ u → ℓ s ω = min s (ℓ u ω)
  cont : ∀ ω, Continuous fun u => N u ω
  zero : ∀ ω, N 0 ω = 0
  exp : ∀ (a : ℝ) (s u : ℝ≥0), s ≤ u → ∀ W : Ω → ℝ≥0∞, Measurable[𝓗 s] W →
    ∫⁻ ω, W ω * ENNReal.ofReal (Real.exp (a * N u ω - a ^ 2 * (ℓ u ω : ℝ) / 2)) ∂P =
      ∫⁻ ω, W ω * ENNReal.ofReal (Real.exp (a * N s ω - a ^ 2 * (ℓ s ω : ℝ) / 2)) ∂P

namespace IsTCExpMartingale

variable {𝓗 : Filtration ℝ≥0 mΩ} {N : ℝ≥0 → Ω → ℝ} {ℓ : ℝ≥0 → Ω → ℝ≥0}

theorem continuous_ℓ (h : IsTCExpMartingale P 𝓗 N ℓ) (ω : Ω) : Continuous fun u => ℓ u ω := by
  refine continuous_iff_continuousAt.2 fun u => ?_
  have hev : (fun v => min v (ℓ (u + 1) ω)) =ᶠ[𝓝 u] fun v => ℓ v ω := by
    filter_upwards [gt_mem_nhds (show u < u + 1 from lt_add_one u)] with v hv
    exact (h.min_eq v (u + 1) ω hv.le).symm
  exact (continuous_id.min continuous_const).continuousAt.congr hev

theorem ℓ_zero (h : IsTCExpMartingale P 𝓗 N ℓ) (ω : Ω) : ℓ 0 ω = 0 :=
  le_antisymm (h.le 0 ω) zero_le

/-- **Completion by an independent Brownian motion** (Proposition 6.5, "the Brownian motion may be
completed on an enlarged probability space"): on `Ω × Ω₀`, `β_u = N_u + B_u − B_{ℓ_u}` is a Brownian
motion with continuous paths, the projection to `Ω` pushes the product measure to `P`, and
`β_u = N_u` whenever `ℓ_u = u`. -/
theorem exists_isBrownianReal_completion [IsProbabilityMeasure P]
    (h : IsTCExpMartingale P 𝓗 N ℓ) :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω)
      (β : ℝ≥0 → Ω' → ℝ), IsProbabilityMeasure P' ∧ Measurable π ∧ P'.map π = P ∧
        IsBrownianReal β P' ∧ (∀ ω', Continuous fun u => β u ω') ∧
          ∀ ω' u, ℓ u (π ω') = u → β u ω' = N u (π ω') := by
  obtain ⟨Ω₀, m₀, P₀, B₀, hP₀, hB₀⟩ := QuantumZipper.brownianMotionExists
  obtain ⟨B, hBm, hBc, hB0, hB, -⟩ := QuantumZipper.RS.exists_good_version0 hB₀
  have hFB := hB.toIsPreBrownianReal.isFilteredPreBrownian hBm
  set 𝓦 := Filtration.natural B fun t => (hBm t).stronglyMeasurable with h𝓦
  have hBad : ∀ r, Measurable[𝓦 r] (B r) := fun r => (hFB.stronglyAdapted r).measurable
  set Q : Measure (Ω × Ω₀) := P.prod P₀ with hQ
  set β : ℝ≥0 → Ω × Ω₀ → ℝ := fun u p => N u p.1 + B u p.2 - B (ℓ u p.1) p.2 with hβ
  have hβc : ∀ p, Continuous fun u => β u p := fun p =>
    ((h.cont p.1).add (hBc p.2)).sub ((hBc p.2).comp (h.continuous_ℓ p.1))
  -- the filtration `𝓖_u = 𝓗_u ⊗ 𝓦_u`
  set 𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω₀)) :=
    { seq := fun u => @Prod.instMeasurableSpace Ω Ω₀ (𝓗 u) (𝓦 u)
      mono' := fun _ _ huv => sup_le_sup (MeasurableSpace.comap_mono (𝓗.mono huv))
        (MeasurableSpace.comap_mono (𝓦.mono huv))
      le' := fun u => sup_le_sup (MeasurableSpace.comap_mono (𝓗.le u))
        (MeasurableSpace.comap_mono (𝓦.le u)) } with h𝓖
  have hβm : ∀ u, Measurable[𝓖 u] (β u) := by
    intro u
    have hBu : ∀ w, Continuous fun r => B (min r u) w := fun w =>
      (hBc w).comp (continuous_id.min continuous_const)
    have hBum : ∀ r, Measurable[𝓦 u] (B (min r u)) := fun r =>
      (hBad _).mono (𝓦.mono (min_le_right _ _)) le_rfl
    have := @measurable_completion Ω Ω₀ (𝓗 u) (𝓦 u) (N u) (h.measurable_N u) (ℓ u)
      (h.measurable_ℓ u) (fun r w => B (min r u) w) hBu hBum u
    have e : β u = fun p : Ω × Ω₀ => N u p.1 + B (min u u) p.2 - B (min (ℓ u p.1) u) p.2 := by
      funext p
      simp only [hβ, min_self, min_eq_left (h.le u p.1)]
    rw [e]
    exact this
  have hβm' : ∀ u, Measurable (β u) := fun u => (hβm u).mono (𝓖.le u) le_rfl
  -- the integrand `e^{aβ_r − a² r/2}`
  set f : ℝ → ℝ≥0 → Ω × Ω₀ → ℝ≥0∞ :=
    fun a r p => ENNReal.ofReal (Real.exp (a * β r p - a ^ 2 * (r : ℝ) / 2)) with hf
  have hfm : ∀ a r, Measurable (f a r) := fun a r =>
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (((hβm' r).const_mul a).sub_const _))
  have hbmEm : ∀ a r x, Measurable (bmE B a r x) := fun a r x =>
    (((hBm r).sub (hBm _)).const_mul a).sub_const _
  -- Fubini on boxes
  have hbox : ∀ (a : ℝ) (r : ℝ≥0) {B₁ : Set Ω} {B₂ : Set Ω₀}, MeasurableSet B₁ →
      MeasurableSet B₂ → ∫⁻ p in B₁ ×ˢ B₂, f a r p ∂Q =
        ∫⁻ ω in B₁, ENNReal.ofReal (Real.exp (a * N r ω - a ^ 2 * (ℓ r ω : ℝ) / 2)) *
          ∫⁻ w in B₂, ENNReal.ofReal (Real.exp (bmE B a r (ℓ r ω) w)) ∂P₀ ∂P := by
    intro a r B₁ B₂ _ _
    rw [hQ, ← Measure.prod_restrict, lintegral_prod _ (hfm a r).aemeasurable]
    refine lintegral_congr fun ω => ?_
    rw [← lintegral_const_mul (f := fun w => ENNReal.ofReal (Real.exp (bmE B a r (ℓ r ω) w))) _
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hbmEm a r (ℓ r ω))))]
    refine lintegral_congr fun w => ?_
    simp only [hf, hβ, bmE, min_eq_right (h.le r ω)]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  -- the Brownian integral as a function of the clock value
  set Ψ : ℝ → ℝ≥0 → Set Ω₀ → ℝ≥0 → ℝ≥0∞ :=
    fun a s B₂ y => ∫⁻ w in B₂, ENNReal.ofReal (Real.exp (bmE B a s y w)) ∂P₀ with hΨ
  have hΨm : ∀ a s {B₂ : Set Ω₀}, MeasurableSet B₂ → Measurable (Ψ a s B₂) := by
    intro a s B₂ hB₂
    have h2 : Measurable fun q : ℝ≥0 × Ω₀ => B (min s q.1) q.2 :=
      (measurable_uncurry_of_continuous_of_measurable (u := fun y w => B (min s y) w)
        (fun w => (hBc w).comp (continuous_const.min continuous_id)) fun y => hBm _)
    have h3 : Measurable fun q : ℝ≥0 × Ω₀ => (((min s q.1 : ℝ≥0)) : ℝ) :=
      (NNReal.continuous_coe.comp (continuous_const.min continuous_id)).measurable.comp
        measurable_fst
    have hj : Measurable fun q : ℝ≥0 × Ω₀ => bmE B a s q.1 q.2 :=
      ((((hBm s).comp measurable_snd).sub h2).const_mul a).sub
        (((measurable_const.sub h3).const_mul _).div_const _)
    have hj' : Measurable fun q : ℝ≥0 × Ω₀ => (Prod.snd ⁻¹' B₂).indicator
        (fun q => ENNReal.ofReal (Real.exp (bmE B a s q.1 q.2))) q :=
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hj)).indicator
        (measurable_snd hB₂)
    have e : Ψ a s B₂ = fun y => ∫⁻ w, (Prod.snd ⁻¹' B₂).indicator
        (fun q => ENNReal.ofReal (Real.exp (bmE B a s q.1 q.2))) (y, w) ∂P₀ := by
      funext y
      simp only [hΨ]
      rw [← lintegral_indicator hB₂]
      rfl
    rw [e]
    exact hj'.lintegral_prod_right'
  have hind1 : ∀ {B₂ : Set Ω₀}, MeasurableSet B₂ → ∀ g : Ω₀ → ℝ≥0∞,
      ∫⁻ w in B₂, g w ∂P₀ = ∫⁻ w, B₂.indicator (fun _ => (1 : ℝ≥0∞)) w * g w ∂P₀ := by
    intro B₂ hB₂ g
    rw [← lintegral_indicator hB₂]
    refine lintegral_congr fun w => ?_
    by_cases hw : w ∈ B₂ <;> simp [hw]
  -- the box identity
  have hboxeq : ∀ (a : ℝ) {s t : ℝ≥0}, s ≤ t → ∀ {B₁ : Set Ω} {B₂ : Set Ω₀},
      MeasurableSet[𝓗 s] B₁ → MeasurableSet[𝓦 s] B₂ →
        ∫⁻ p in B₁ ×ˢ B₂, f a t p ∂Q = ∫⁻ p in B₁ ×ˢ B₂, f a s p ∂Q := by
    intro a s t hst B₁ B₂ hB₁ hB₂
    have hB₁' : MeasurableSet B₁ := 𝓗.le s _ hB₁
    have hB₂' : MeasurableSet B₂ := 𝓦.le s _ hB₂
    rw [hbox a t hB₁' hB₂', hbox a s hB₁' hB₂']
    have hin : ∀ r : ℝ≥0, s ≤ r → ∀ ω, ∫⁻ w in B₂, ENNReal.ofReal (Real.exp
        (bmE B a r (ℓ r ω) w)) ∂P₀ = Ψ a s B₂ (ℓ s ω) := by
      intro r hsr ω
      have h1B : Measurable[𝓦 s] (B₂.indicator (fun _ => (1 : ℝ≥0∞))) :=
        measurable_const.indicator hB₂
      rw [hind1 hB₂', lintegral_mul_exp_bmE hFB a hsr (ℓ r ω) h1B, ← hind1 hB₂', hΨ]
      simp only
      rw [h.min_eq s r ω hsr]
      refine lintegral_congr fun w => ?_
      rw [bmE_min]
    simp only [hin t hst, hin s le_rfl]
    set W : Ω → ℝ≥0∞ := B₁.indicator fun ω => Ψ a s B₂ (ℓ s ω) with hW
    have hWm : Measurable[𝓗 s] W := ((hΨm a s hB₂').comp (h.measurable_ℓ s)).indicator hB₁
    have hconv : ∀ r : ℝ≥0, ∫⁻ ω in B₁, ENNReal.ofReal (Real.exp (a * N r ω -
        a ^ 2 * (ℓ r ω : ℝ) / 2)) * Ψ a s B₂ (ℓ s ω) ∂P = ∫⁻ ω, W ω *
          ENNReal.ofReal (Real.exp (a * N r ω - a ^ 2 * (ℓ r ω : ℝ) / 2)) ∂P := by
      intro r
      rw [← lintegral_indicator hB₁']
      refine lintegral_congr fun ω => ?_
      by_cases hω : ω ∈ B₁
      · simp only [hW, indicator_of_mem hω, mul_comm]
      · simp only [hW, indicator_of_notMem hω, zero_mul]
    rw [hconv t, hconv s, h.exp a s t hst W hWm]
  -- total mass
  have htot : ∀ a r, ∫⁻ p, f a r p ∂Q = 1 := by
    intro a r
    have := hboxeq a (zero_le (a := r)) (B₁ := univ) (B₂ := univ) (@MeasurableSet.univ _ (𝓗 0))
      (@MeasurableSet.univ _ (𝓦 0))
    simp only [univ_prod_univ, Measure.restrict_univ] at this
    rw [this]
    have h0 : ∀ p, f a 0 p = 1 := fun p => by
      simp [hf, hβ, h.zero, h.ℓ_zero, hB0]
    simp only [h0, lintegral_const, measure_univ, mul_one]
  -- every set of `𝓖_s`
  have hall : ∀ (a : ℝ) {s t : ℝ≥0}, s ≤ t → ∀ A, MeasurableSet[𝓖 s] A →
      ∫⁻ p in A, f a t p ∂Q = ∫⁻ p in A, f a s p ∂Q := by
    intro a s t hst A hA
    refine MeasurableSpace.induction_on_inter
      (C := fun A _ => ∫⁻ p in A, f a t p ∂Q = ∫⁻ p in A, f a s p ∂Q)
      (@generateFrom_prod Ω Ω₀ (𝓗 s) (𝓦 s)).symm (@isPiSystem_prod Ω Ω₀ (𝓗 s) (𝓦 s))
      ?_ ?_ ?_ ?_ A hA
    · simp
    · rintro _ ⟨B₁, hB₁, B₂, hB₂, rfl⟩
      exact hboxeq a hst hB₁ hB₂
    · intro A' hA' hC
      have hA'm : MeasurableSet A' := 𝓖.le s _ hA'
      have h1 := lintegral_add_compl (μ := Q) (f a t) hA'm
      have h2 := lintegral_add_compl (μ := Q) (f a s) hA'm
      rw [htot] at h1 h2
      have hfin : ∫⁻ p in A', f a s p ∂Q ≠ ∞ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top (h2 ▸ le_self_add)
      rw [hC] at h1
      exact (ENNReal.add_right_inj hfin).1 (h1.trans h2.symm)
    · intro g hdisj hgm hC
      have hgm' : ∀ i, MeasurableSet (g i) := fun i => 𝓖.le s _ (hgm i)
      rw [lintegral_iUnion hgm' hdisj, lintegral_iUnion hgm' hdisj]
      exact tsum_congr hC
  have hmart : ∀ (a : ℝ) {s t : ℝ≥0}, s ≤ t → ∀ {A : Set (Ω × Ω₀)}, MeasurableSet[𝓖 s] A →
      ∫ p in A, Real.exp (a * β t p - a ^ 2 * (t : ℝ) / 2) ∂Q =
        ∫ p in A, Real.exp (a * β s p - a ^ 2 * (s : ℝ) / 2) ∂Q := by
    intro a s t hst A hA
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun p => (Real.exp_pos _).le)
      (Real.measurable_exp.comp (((hβm' t).const_mul a).sub_const _)).aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun p => (Real.exp_pos _).le)
      (Real.measurable_exp.comp (((hβm' s).const_mul a).sub_const _)).aestronglyMeasurable]
    exact congrArg ENNReal.toReal (hall a hst A hA)
  refine ⟨Ω × Ω₀, inferInstance, Q, Prod.fst, β, inferInstance, measurable_fst, ?_, ?_, hβc, ?_⟩
  · rw [hQ, Measure.map_fst_prod, measure_univ, one_smul]
  · refine MathFin.isBrownianReal_of_expMartingale (𝓕 := 𝓖) (fun T =>
      ⟨fun u => (hβm u).stronglyMeasurable, ae_of_all _ fun p => ?_,
        fun a s t hst _ A hA => hmart a hst hA⟩) (ae_of_all _ hβc)
    simp [hβ, h.zero, h.ℓ_zero, hB0]
  · intro p u hℓu
    simp only [hβ, hℓu, add_sub_cancel_right]

end IsTCExpMartingale

end Product

end InteractingSLE.Sec6.Prop65
