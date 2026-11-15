/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BHMeanReal

/-!
# The boundary-hitting mean identification: the explored hull's sides

Packet PROVE-BHMEAN. At a real point `x ≠ 0` of the joint chart whose landing point lies in the closed relative hull
(the relative hull image), the joint parametrization lands on the closed explored hull, and the explored curve's own
coupling mean minus the candidate is

`GE(T(y)) − G(y) − χ (Im log f_t' − jointLift)(Ψi(f̃_u⁻¹ y))`,  `T = f_t ∘ Ψi ∘ f̃_u⁻¹`.

Both words are the side heights `±λ` on the two hull images (`IsSideWord`), so the limit vanishes once the
**transition** `T` lands at a real point `T(x)` of the explored hull image with the sign of `x`, and the one integer
lift of `T'` is zero there (Astra's Q3 §3.3: "the transition from its own chart to the relative chart reflects across
the connected interval containing the entire old counterflow base. Its derivative is positive … N(t) = 0").

* **`RelTransition`**: these transition facts on the relative hull image, with `T` injective there (the reflected
  transition is a strictly increasing real map) — the one remaining geometric input, isolated;
* `landing_mem_closure`: the joint parametrization lands on the closed explored hull;
* **`explored_side`**: the explored-side alternative of `HasUnionWordBoundary`, along `𝓝[ℍ] x`;
* first steps toward `RelTransition` (the single-lift argument): `jointChart` (a project `Chart`),
  `isConformal_jointChart`, `coe_dom_jointChart`, `isDerivLog_jointLog`; **`exists_int_jointChart`** (on a ball whose
  real points land off `ℍ ∖ K_t`, the argument difference tends to one `2πn`: Schwarz reflection of the transition,
  `Lemma71O.exists_int_wall`); **`tendsto_lift_sub_zero_of_untouched`** (the integer is `0` at a real point whose
  joint landing point is an untouched real point off `cl A ∪ cl K_t`).

Deterministic. Conditional helpers with distinct names; they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Filter Set Topology Metric Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)

namespace InteractingSLE.Supp8.BHMean

/-- **The transition of the relative configuration on the relative hull image** (the geometric input of the explored
side): a boundary map `T` of `f_t ∘ Ψi ∘ f̃_u⁻¹`, injective on the relative hull image off `0`, such that at every such
point `x` the transition tends to the real point `T x ≠ 0` of the explored hull image, of the sign of `x`, and the
inherited argument difference `Im log f_t' − jointLift` tends to `0` (the integer lift is zero). -/
def RelTransition (Ψ Ψi LΨ : ℂ → ℂ) (w Wr : ℝ → ℝ) (t u : ℝ) : Prop :=
  ∃ T : ℝ → ℝ,
    InjOn T {x : ℝ | x ≠ 0 ∧ extendFrom H (fwdMapInv Wr u) (x : ℂ) ∈ closure (fwdHull Wr u)} ∧
    ∀ x : ℝ, x ≠ 0 → extendFrom H (fwdMapInv Wr u) (x : ℂ) ∈ closure (fwdHull Wr u) →
      (0 < T x ↔ 0 < x) ∧ T x ≠ 0 ∧ extendFrom H (fwdMapInv w t) (T x : ℂ) ∈ closure (fwdHull w t) ∧
      Tendsto (fun y => fwdMap w t (jointInv Ψi Wr u y)) (𝓝[H] (x : ℂ)) (𝓝 (T x : ℂ)) ∧
      Tendsto (fun y => (logDerivFwd w t (jointInv Ψi Wr u y)).im - jointLift Ψ LΨ Wr u (jointInv Ψi Wr u y))
        (𝓝[H] (x : ℂ)) (𝓝 0)

section Side

variable {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {w Wr : ℝ → ℝ} {ηr : ℝ → ℂ} {t u χ lam : ℝ}
  {βE βu : ℝ → ℝ} {SE Su : Finset ℝ} {GE G u₀ w₂ : ℂ → ℝ}

/-- **The joint parametrization lands on the closed explored hull** at a real point of the relative hull image. -/
theorem landing_mem_closure (hΨ : IsRetainedChart A Ψ Ψi LΨ) (hw : Continuous w) (ht : 0 ≤ t)
    (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    (hWr : Continuous Wr) (hu : 0 ≤ u) {y p : ℂ} (hy : y ∈ closure (fwdHull Wr u))
    (hp : Tendsto Ψi (𝓝[H] y) (𝓝 p)) : p ∈ closure (fwdHull w t) := by
  have hKH : fwdHull Wr u ⊆ H := (isHPHull_fwdHull hWr hu).1
  have hNe : (𝓝[fwdHull Wr u] y).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hy
  have h1 : Tendsto Ψi (𝓝[fwdHull Wr u] y) (𝓝 p) := hp.mono_left (nhdsWithin_mono y hKH)
  refine mem_closure_of_tendsto h1 (eventually_nhdsWithin_of_forall fun v hv => ?_)
  rw [← hK] at hv
  obtain ⟨z, hz, rfl⟩ := hv
  rw [hΨ.inv_fwd (fwdHull_subset_compl hd hw ht hz)]
  exact hz

/-- **The explored-side alternative** of `HasUnionWordBoundary` at a real point `x ≠ 0` of the relative hull image
(off the jumps of `βu`, with `T x` off the jumps of `βE`): the joint parametrization lands at a point `p` of `K_t ∪ ℝ`
off the closed retained set, and the explored mean minus the candidate tends to `0`. -/
theorem explored_side (hΨ : IsRetainedChart A Ψ Ψi LΨ) (hw : Continuous w) (ht : 0 ≤ t)
    (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u)
    (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    (hGE : IsBoundedHarmonicExtension βE SE GE) (hG : IsBoundedHarmonicExtension βu Su G)
    (hsE : IsSideWord βE SE (fwdMapInv w t) (fwdHull w t) lam)
    (hsu : IsSideWord βu Su (fwdMapInv Wr u) (fwdHull Wr u) lam)
    (hw₂ : EqOn (fun z => w₂ z + u₀ z) (fun z => GE (fwdMap w t z) - χ * (logDerivFwd w t z).im)
      (H \ fwdHull w t))
    {T : ℝ → ℝ} {x : ℝ} (hx0 : x ≠ 0) (hxK : extendFrom H (fwdMapInv Wr u) (x : ℂ) ∈ closure (fwdHull Wr u))
    (hxS : x ∉ Su) (hTS : T x ∉ SE) (hsign : 0 < T x ↔ 0 < x) (hT0 : T x ≠ 0)
    (hTK : extendFrom H (fwdMapInv w t) (T x : ℂ) ∈ closure (fwdHull w t))
    (hTl : Tendsto (fun y => fwdMap w t (jointInv Ψi Wr u y)) (𝓝[H] (x : ℂ)) (𝓝 (T x : ℂ)))
    (hLl : Tendsto (fun y => (logDerivFwd w t (jointInv Ψi Wr u y)).im - jointLift Ψ LΨ Wr u (jointInv Ψi Wr u y))
      (𝓝[H] (x : ℂ)) (𝓝 0)) :
    ∃ p : ℂ, Tendsto (jointInv Ψi Wr u) (𝓝[H] (x : ℂ)) (𝓝 p) ∧ p ∈ fwdHull w t ∪ {z : ℂ | z.im = 0} ∧
      (∃ r > 0, A ∩ ball p r ⊆ fwdHull w t) ∧
      Tendsto (fun y => (w₂ (jointInv Ψi Wr u y) + u₀ (jointInv Ψi Wr u y)) -
        (G (jointFwd Ψ Wr u (jointInv Ψi Wr u y)) - χ * jointLift Ψ LΨ Wr u (jointInv Ψi Wr u y)))
        (𝓝[H] (x : ℂ)) (𝓝 0) := by
  set yc : ℂ := extendFrom H (fwdMapInv Wr u) (x : ℂ) with hycdef
  have hxbar : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hycb : yc ∈ Hbar := extendFrom_mem_Hbar hηr hWr hWr0 hu hxbar
  have hlimF : Tendsto (fwdMapInv Wr u) (𝓝[H] (x : ℂ)) (𝓝[H] yc) :=
    tendsto_nhdsWithin_iff.2 ⟨(hηr.hasBdryLimits hWr hWr0 hu).tendsto hxbar,
      eventually_nhdsWithin_of_forall fun v hv => QuantumZipper.RS.fwdMapInv_mem_H hWr hWr0 hu hv⟩
  -- the landing point of `Ψi` at `yc`
  have hland : ∃ p, Tendsto Ψi (𝓝[H] yc) (𝓝 p) := by
    by_cases hyH : yc ∈ H
    · exact ⟨Ψi yc, (hΨ.diff_inv.continuousOn.continuousAt (QuantumZipper.isOpen_H.mem_nhds hyH)).tendsto.mono_left
        nhdsWithin_le_nhds⟩
    · have hyim : yc.im = 0 := le_antisymm (not_lt.1 hyH) hycb
      have hyr : yc = (yc.re : ℂ) := by
        apply Complex.ext
        · simp
        · simp [hyim]
      obtain ⟨p, hp⟩ := hΨ.inv_lands yc.re
      rw [← hyr] at hp
      exact ⟨p, hp⟩
  obtain ⟨p, hp⟩ := hland
  have hjoint : Tendsto (jointInv Ψi Wr u) (𝓝[H] (x : ℂ)) (𝓝 p) := hp.comp hlimF
  have hpK : p ∈ closure (fwdHull w t) := landing_mem_closure hΨ hw ht hK hd hWr hu hxK hp
  have hpA : p ∉ closure A := Set.disjoint_left.1 hd hpK
  have hpbar : p ∈ Hbar := by
    rw [← closure_H]; exact closure_mono (isHPHull_fwdHull hw ht).1 hpK
  have hpKR : p ∈ fwdHull w t ∪ {z : ℂ | z.im = 0} := by
    by_cases hpH : p ∈ H
    · left
      by_contra hpn
      have hopen : IsOpen (H \ fwdHull w t) := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hw ht
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen p ⟨hpH, hpn⟩
      obtain ⟨z, hzK, hzb⟩ := Metric.mem_closure_iff.1 hpK r hr
      exact (hball (by rw [mem_ball, dist_comm]; exact hzb)).2 hzK
    · exact Or.inr (le_antisymm (not_lt.1 hpH) hpbar)
  obtain ⟨r, hr, hball⟩ := GB6.exists_ball_disjoint_of_notMem_closure hpA
  refine ⟨p, hjoint, hpKR, ⟨r, hr, fun z hz => absurd hz.1 (Set.disjoint_left.1 hball hz.2)⟩, ?_⟩
  -- the limit
  have hJC : ∀ y ∈ H, jointInv Ψi Wr u y ∈ H \ fwdHull w t := fun y hy => by
    have h := jointInv_mem hΨ hw ht hWr hWr0 hu hK hd hy
    exact ⟨h.1, fun hk => h.2 (Or.inr hk)⟩
  have hTH : Tendsto (fun y => fwdMap w t (jointInv Ψi Wr u y)) (𝓝[H] (x : ℂ)) (𝓝[H] (T x : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hTl, eventually_nhdsWithin_of_forall fun y hy =>
      QuantumZipper.FwdHolo.mapsTo_fwdMap hw ht (hJC y hy)⟩
  have hGEl := (hGE.2.2 (T x) hTS).comp hTH
  have hGl : Tendsto G (𝓝[H] (x : ℂ)) (𝓝 (βu x)) := hG.2.2 x hxS
  have hsum := (hGEl.sub hGl).sub (hLl.const_mul χ)
  have hβ : βE (T x) = βu x := by
    rw [hsE (T x) hTS hT0 hTK, hsu x hxS hx0 hxK]
    simp only [hsign]
  rw [hβ, sub_self, mul_zero, sub_zero] at hsum
  refine hsum.congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
  have e2 := hw₂ (hJC y hy)
  simp only at e2
  simp only [Function.comp, jointLift, jointFwd_jointInv hΨ hw ht hWr hWr0 hu hK hd hy, e2]
  ring

end Side

/-! ### The joint chart and its local integer lift -/

/-- The joint chart `(f̃_u ∘ Ψ, Ψi ∘ f̃_u⁻¹, jointLift)` as a project `Chart`. -/
def jointChart (Ψ Ψi LΨ : ℂ → ℂ) (Wr : ℝ → ℝ) (u : ℝ) : Chart :=
  (jointFwd Ψ Wr u, jointInv Ψi Wr u, jointLift Ψ LΨ Wr u)

section Integer

variable {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {w Wr : ℝ → ℝ} {η : ℝ → ℂ} {t u : ℝ}

theorem isConformal_jointChart (hΨ : IsRetainedChart A Ψ Ψi LΨ) (hw : Continuous w) (ht : 0 ≤ t)
    (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hu : 0 ≤ u)
    (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A)) :
    (jointChart Ψ Ψi LΨ Wr u).IsConformal := by
  refine ⟨?_, fun y hy => (jointInv_mem hΨ hw ht hWr hWr0 hu hK hd hy).1, fun y hy =>
    jointFwd_jointInv hΨ hw ht hWr hWr0 hu hK hd hy⟩
  have h := (isConformalBijection_diskInv hΨ hw ht hWr hWr0 hu hK hd).1
  intro y hy
  have hF : DifferentiableAt ℂ (fwdMapInv Wr u) y :=
    (isConformalBijection_fwdMapInv hWr hWr0 hu).1.differentiableAt (QuantumZipper.isOpen_H.mem_nhds hy)
  have hP : DifferentiableAt ℂ Ψi (fwdMapInv Wr u y) :=
    hΨ.diff_inv.differentiableAt (QuantumZipper.isOpen_H.mem_nhds (QuantumZipper.RS.fwdMapInv_mem_H hWr hWr0 hu hy))
  exact (hP.comp y hF).differentiableWithinAt

theorem coe_dom_jointChart (hΨ : IsRetainedChart A Ψ Ψi LΨ) (hw : Continuous w) (ht : 0 ≤ t)
    (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hu : 0 ≤ u)
    (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A)) :
    ((jointChart Ψ Ψi LΨ Wr u).dom : Set ℂ) = H \ (A ∪ fwdHull w t) := by
  rw [(isConformal_jointChart hΨ hw ht hWr hWr0 hu hK hd).coe_dom]
  exact image_jointInv hΨ hw ht hWr hWr0 hu hK hd

/-- The complex logarithm of the joint chart's derivative. -/
def jointLog (Ψ LΨ : ℂ → ℂ) (Wr : ℝ → ℝ) (u : ℝ) (z : ℂ) : ℂ := logDerivFwd Wr u (Ψ z) + LΨ z

theorem isDerivLog_jointLog (hΨ : IsRetainedChart A Ψ Ψi LΨ) (hw : Continuous w) (ht : 0 ≤ t)
    (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hu : 0 ≤ u)
    (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A)) :
    IsDerivLog (jointFwd Ψ Wr u) (jointLog Ψ LΨ Wr u) (H \ (A ∪ fwdHull w t)) := by
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨hzA, hzK⟩ := (mem_C_iff hΨ hw ht hWr hWr0 hu hK hd).1 hz
    have h2 : DifferentiableAt ℂ Ψ z := hΨ.conf.1.differentiableAt (hΨ.isOpen.mem_nhds hzA)
    have h1 : DifferentiableAt ℂ (logDerivFwd Wr u) (Ψ z) :=
      (isDerivLog_fwdMap hWr hu).1.differentiableAt ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hWr hu).mem_nhds hzK)
    have h3 : DifferentiableAt ℂ LΨ z := hΨ.log.1.differentiableAt (hΨ.isOpen.mem_nhds hzA)
    exact ((h1.comp z h2).add h3).differentiableWithinAt
  · obtain ⟨hzA, hzK⟩ := (mem_C_iff hΨ hw ht hWr hWr0 hu hK hd).1 hz
    have h1 : DifferentiableAt ℂ (fwdMap Wr u) (Ψ z) :=
      (QuantumZipper.FwdHolo.differentiableOn_fwdMap hWr hu).differentiableAt
        ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hWr hu).mem_nhds hzK)
    have h2 : DifferentiableAt ℂ Ψ z := hΨ.conf.1.differentiableAt (hΨ.isOpen.mem_nhds hzA)
    rw [show jointFwd Ψ Wr u = fwdMap Wr u ∘ Ψ from rfl, deriv_comp z h1 h2, ← (isDerivLog_fwdMap hWr hu).2 _ hzK,
      ← hΨ.log.2 z hzA, jointLog, Complex.exp_add]

/-- **The local integer lift of the transition** (the first step of the single-lift argument): if the joint
parametrization lands off `ℍ ∖ K_t` at every real point of `B(x, r)`, then for one integer `n` the inherited argument
difference `Im log f_t' − jointLift` tends to `2πn` at every real point of a smaller ball (`Lemma71O.exists_int_wall`:
Schwarz reflection of `f_t ∘ Ψi ∘ f̃_u⁻¹` with positive derivative). -/
theorem exists_int_jointChart (hΨ : IsRetainedChart A Ψ Ψi LΨ) (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hu : 0 ≤ u)
    (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    {x r : ℝ} (hr : 0 < r)
    (hland : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → ∃ p, p ∉ H \ fwdHull w t ∧
      Tendsto (jointInv Ψi Wr u) (𝓝[H] z) (𝓝 p)) :
    ∃ n : ℤ, ∃ ε > 0, ε ≤ r ∧ ∀ z ∈ ball (x : ℂ) ε, z.im = 0 →
      Tendsto (fun y => (logDerivFwd w t (jointInv Ψi Wr u y)).im - jointLift Ψ LΨ Wr u (jointInv Ψi Wr u y))
        (𝓝[H] z) (𝓝 (2 * Real.pi * n)) := by
  have hCt : H \ (A ∪ fwdHull w t) ⊆ H \ fwdHull w t := fun z hz => ⟨hz.1, fun h => hz.2 (Or.inr h)⟩
  obtain ⟨n, ε, hε, hεr, hlim⟩ := Sec7.Lemma71O.exists_int_wall hη hw hw0 ht
    (isConformal_jointChart hΨ hw ht hWr hWr0 hu hK hd) (coe_dom_jointChart hΨ hw ht hWr hWr0 hu hK hd)
    (isDerivLog_jointLog hΨ hw ht hWr hWr0 hu hK hd) hCt hr hland
  refine ⟨n, ε, hε, hεr, fun z hz hz0 => (hlim z hz hz0).congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)⟩
  simp only [jointChart, jointLog, jointLift, Complex.sub_im, Complex.add_im]

/-- **The pinning of the integer** (the single-lift argument's normalization): at a real point `x` of the joint chart
off the relative hull image whose joint landing point `p` is a real point off `cl A ∪ cl K_t` (an untouched original
real point next to the explored base), the inherited argument difference tends to `0`: all three arguments vanish
there ((CA2) for both chains and `IsRetainedChart.lift_real`). -/
theorem tendsto_lift_sub_zero_of_untouched (hΨ : IsRetainedChart A Ψ Ψi LΨ) (hw : Continuous w) (hw0 : w 0 = 0)
    (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) {ηr : ℝ → ℂ} (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u)
    (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    {x : ℝ} (hy : extendFrom H (fwdMapInv Wr u) (x : ℂ) ∉ closure (fwdHull Wr u)) {p : ℂ}
    (hp : Tendsto (jointInv Ψi Wr u) (𝓝[H] (x : ℂ)) (𝓝 p)) (hpim : p.im = 0) (hpA : p ∉ closure A)
    (hpK : p ∉ closure (fwdHull w t)) :
    Tendsto (fun y => (logDerivFwd w t (jointInv Ψi Wr u y)).im - jointLift Ψ LΨ Wr u (jointInv Ψi Wr u y))
      (𝓝[H] (x : ℂ)) (𝓝 0) := by
  have hpr : p = (p.re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hpim]
  set yc : ℂ := extendFrom H (fwdMapInv Wr u) (x : ℂ) with hycdef
  have hyim : yc.im = 0 := im_extendFrom_eq_zero_of_notMem_closure hηr hWr hWr0 hu hy
  have hyr : yc = (yc.re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hyim]
  have hxbar : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hlimF : Tendsto (fwdMapInv Wr u) (𝓝[H] (x : ℂ)) (𝓝[H] yc) :=
    tendsto_nhdsWithin_iff.2 ⟨(hηr.hasBdryLimits hWr hWr0 hu).tendsto hxbar,
      eventually_nhdsWithin_of_forall fun v hv => QuantumZipper.RS.fwdMapInv_mem_H hWr hWr0 hu hv⟩
  have hJC : ∀ y ∈ H, jointInv Ψi Wr u y ∈ H \ (A ∪ fwdHull w t) := fun y hy =>
    jointInv_mem hΨ hw ht hWr hWr0 hu hK hd hy
  -- the explored argument
  have h1 : Tendsto (fun y => (logDerivFwd w t (jointInv Ψi Wr u y)).im) (𝓝[H] (x : ℂ)) (𝓝 0) := by
    have hl := tendsto_im_logDerivFwd_of_notMem_closure hw hw0 ht (y := p.re) (by rw [← hpr]; exact hpK)
    rw [← hpr] at hl
    exact hl.comp (tendsto_nhdsWithin_iff.2 ⟨hp, eventually_nhdsWithin_of_forall fun y hy => (hJC y hy).1⟩)
  -- the relative argument
  have h2 : Tendsto (fun y => (logDerivFwd Wr u (fwdMapInv Wr u y)).im) (𝓝[H] (x : ℂ)) (𝓝 0) := by
    have hl := tendsto_im_logDerivFwd_of_notMem_closure hWr hWr0 hu (y := yc.re) (by rw [← hyr]; exact hy)
    rw [← hyr] at hl
    exact hl.comp hlimF
  -- the retained chart's argument
  have h3 : Tendsto (fun y => (LΨ (jointInv Ψi Wr u y)).im) (𝓝[H] (x : ℂ)) (𝓝 0) := by
    have hl := hΨ.lift_real p.re (by rw [← hpr]; exact hpA)
    rw [← hpr] at hl
    exact hl.comp (tendsto_nhdsWithin_iff.2 ⟨hp, eventually_nhdsWithin_of_forall fun y hy =>
      ⟨(hJC y hy).1, fun h => (hJC y hy).2 (Or.inl h)⟩⟩)
  have hsum := h1.sub (h2.add h3)
  rw [add_zero, sub_zero] at hsum
  refine hsum.congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
  have hFv := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWr hWr0 hu hy
  simp only [jointLift, jointInv, hΨ.fwd_inv _ hFv.1]

end Integer

end InteractingSLE.Supp8.BHMean
