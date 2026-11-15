/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BHMeanStatement

/-!
# The boundary-hitting mean identification: the joint chart of the relative configuration

Packet PROVE-BHMEAN. In the setting of `RelUnionWordBoundaryStatement` (retained set `A` with chart `Ψ`, explored hull
`K_t`, relative hull `K̃_u = Ψ(K_t)`, closed hulls disjoint), the joint complement `C = ℍ ∖ (A ∪ K_t)` is the image of
`ℍ` under `jointInv = Ψi ∘ f̃_u⁻¹`, with inverse `jointFwd = f̃_u ∘ Ψ`:

* `mem_C_iff`, `jointInv_mem`, `jointFwd_mem`, `jointFwd_jointInv`, `jointInv_jointFwd`;
* `isPreconnected_C`, `connectedComponentIn_C`: `C` is connected (one component);
* `isConformalBijection_jointFwd` (`C → ℍ`), `isConformalBijection_diskInv` (`𝔻 → C`, through `cayleyInv`);
* `jointLift` and `deriv_jointFwd`: the inherited argument `Im log f̃_u' ∘ Ψ + Im LΨ` of `jointFwd'`, continuous on
  `C`.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Filter Set Topology Metric Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper.CA (cayley cayleyInv)

namespace InteractingSLE.Supp8.BHMean

variable {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {w Wr : ℝ → ℝ} {t u : ℝ}

/-- The joint inverse `Ψi ∘ f̃_u⁻¹ : ℍ → C`. -/
def jointInv (Ψi : ℂ → ℂ) (Wr : ℝ → ℝ) (u : ℝ) (y : ℂ) : ℂ := Ψi (fwdMapInv Wr u y)

/-- The joint chart `f̃_u ∘ Ψ : C → ℍ`. -/
def jointFwd (Ψ : ℂ → ℂ) (Wr : ℝ → ℝ) (u : ℝ) (z : ℂ) : ℂ := fwdMap Wr u (Ψ z)

/-- The inherited argument of the joint chart. -/
def jointLift (Ψ LΨ : ℂ → ℂ) (Wr : ℝ → ℝ) (u : ℝ) (z : ℂ) : ℝ :=
  (logDerivFwd Wr u (Ψ z)).im + (LΨ z).im

theorem IsRetainedChart.inv_fwd (hΨ : IsRetainedChart A Ψ Ψi LΨ) {z : ℂ} (hz : z ∈ H \ A) : Ψi (Ψ z) = z :=
  hΨ.conf.2.injOn (hΨ.inv_mem _ (hΨ.conf.2.mapsTo hz)) hz (hΨ.fwd_inv _ (hΨ.conf.2.mapsTo hz))

theorem fwdHull_subset_compl (hd : Disjoint (closure (fwdHull w t)) (closure A)) (hw : Continuous w) (ht : 0 ≤ t) :
    fwdHull w t ⊆ H \ A := fun _ hz =>
  ⟨(isHPHull_fwdHull hw ht).1 hz, fun hA => Set.disjoint_left.1 hd (subset_closure hz) (subset_closure hA)⟩

section Chart

variable (hΨ : IsRetainedChart A Ψ Ψi LΨ) (hw : Continuous w) (ht : 0 ≤ t)
  (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hu : 0 ≤ u)
  (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))

include hΨ hw ht hWr hWr0 hu hK hd


theorem mem_C_iff {z : ℂ} : z ∈ H \ (A ∪ fwdHull w t) ↔ z ∈ H \ A ∧ Ψ z ∈ H \ fwdHull Wr u := by
  constructor
  · rintro ⟨hzH, hzn⟩
    have hzA : z ∈ H \ A := ⟨hzH, fun h => hzn (Or.inl h)⟩
    refine ⟨hzA, hΨ.conf.2.mapsTo hzA, fun hK' => ?_⟩
    rw [← hK] at hK'
    obtain ⟨z', hz', he⟩ := hK'
    have := hΨ.conf.2.injOn (fwdHull_subset_compl hd hw ht hz') hzA he
    exact hzn (Or.inr (this ▸ hz'))
  · rintro ⟨⟨hzH, hzA⟩, -, hzK⟩
    refine ⟨hzH, ?_⟩
    rintro (h | h)
    · exact hzA h
    · exact hzK (hK ▸ mem_image_of_mem Ψ h)

theorem jointInv_mem {y : ℂ} (hy : y ∈ H) : jointInv Ψi Wr u y ∈ H \ (A ∪ fwdHull w t) := by
  have h1 := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWr hWr0 hu hy
  rw [mem_C_iff hΨ hw ht hWr hWr0 hu hK hd]
  refine ⟨hΨ.inv_mem _ h1.1, ?_⟩
  simp only [jointInv]
  rw [hΨ.fwd_inv _ h1.1]
  exact h1

theorem jointFwd_mem {z : ℂ} (hz : z ∈ H \ (A ∪ fwdHull w t)) : jointFwd Ψ Wr u z ∈ H :=
  QuantumZipper.FwdHolo.mapsTo_fwdMap hWr hu ((mem_C_iff hΨ hw ht hWr hWr0 hu hK hd).1 hz).2

theorem jointFwd_jointInv {y : ℂ} (hy : y ∈ H) : jointFwd Ψ Wr u (jointInv Ψi Wr u y) = y := by
  have h1 := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWr hWr0 hu hy
  simp only [jointFwd, jointInv]
  rw [hΨ.fwd_inv _ h1.1, QuantumZipper.RS.fwdMap_fwdMapInv hWr hWr0 hu hy]

theorem jointInv_jointFwd {z : ℂ} (hz : z ∈ H \ (A ∪ fwdHull w t)) : jointInv Ψi Wr u (jointFwd Ψ Wr u z) = z := by
  obtain ⟨hzA, hzK⟩ := (mem_C_iff hΨ hw ht hWr hWr0 hu hK hd).1 hz
  simp only [jointFwd, jointInv]
  rw [QuantumZipper.RS.fwdMapInv_fwdMap hWr hWr0 hu hzK, hΨ.inv_fwd hzA]

theorem continuousOn_jointInv : ContinuousOn (jointInv Ψi Wr u) H :=
  hΨ.diff_inv.continuousOn.comp (isConformalBijection_fwdMapInv hWr hWr0 hu).1.continuousOn
    fun _ hy => (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWr hWr0 hu hy).1

theorem image_jointInv : jointInv Ψi Wr u '' H = H \ (A ∪ fwdHull w t) := by
  refine Subset.antisymm ?_ fun z hz => ⟨jointFwd Ψ Wr u z, jointFwd_mem hΨ hw ht hWr hWr0 hu hK hd hz,
    jointInv_jointFwd hΨ hw ht hWr hWr0 hu hK hd hz⟩
  rintro _ ⟨y, hy, rfl⟩
  exact jointInv_mem hΨ hw ht hWr hWr0 hu hK hd hy

theorem isPreconnected_C : IsPreconnected (H \ (A ∪ fwdHull w t)) := by
  rw [← image_jointInv hΨ hw ht hWr hWr0 hu hK hd]
  exact (convex_halfSpace_im_gt 0).isPreconnected.image _ (continuousOn_jointInv hΨ hw ht hWr hWr0 hu hK hd)

theorem connectedComponentIn_C {z₀ : ℂ} (hz₀ : z₀ ∈ H \ (A ∪ fwdHull w t)) :
    connectedComponentIn (H \ (A ∪ fwdHull w t)) z₀ = H \ (A ∪ fwdHull w t) :=
  (isPreconnected_C hΨ hw ht hWr hWr0 hu hK hd).connectedComponentIn hz₀

theorem differentiableAt_jointFwd {z : ℂ} (hz : z ∈ H \ (A ∪ fwdHull w t)) :
    DifferentiableAt ℂ (jointFwd Ψ Wr u) z := by
  obtain ⟨hzA, hzK⟩ := (mem_C_iff hΨ hw ht hWr hWr0 hu hK hd).1 hz
  have h1 : DifferentiableAt ℂ (fwdMap Wr u) (Ψ z) :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hWr hu).differentiableAt
      ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hWr hu).mem_nhds hzK)
  have h2 : DifferentiableAt ℂ Ψ z := hΨ.conf.1.differentiableAt (hΨ.isOpen.mem_nhds hzA)
  exact h1.comp z h2

theorem isConformalBijection_jointFwd :
    IsConformalBijection (jointFwd Ψ Wr u) (H \ (A ∪ fwdHull w t)) H := by
  refine ⟨fun z hz => (differentiableAt_jointFwd hΨ hw ht hWr hWr0 hu hK hd hz).differentiableWithinAt,
    ⟨fun z hz => jointFwd_mem hΨ hw ht hWr hWr0 hu hK hd hz, fun z hz z' hz' he => ?_, fun y hy => ?_⟩⟩
  · rw [← jointInv_jointFwd hΨ hw ht hWr hWr0 hu hK hd hz, he, jointInv_jointFwd hΨ hw ht hWr hWr0 hu hK hd hz']
  · exact ⟨jointInv Ψi Wr u y, jointInv_mem hΨ hw ht hWr hWr0 hu hK hd hy,
      jointFwd_jointInv hΨ hw ht hWr hWr0 hu hK hd hy⟩

/-- **The disk parametrization of the joint complement**: `jointInv ∘ cayleyInv : 𝔻 → C`. -/
theorem isConformalBijection_diskInv :
    IsConformalBijection (fun ζ => jointInv Ψi Wr u (cayleyInv ζ)) (ball 0 1) (H \ (A ∪ fwdHull w t)) := by
  have hc1 : ∀ ζ ∈ ball (0 : ℂ) 1, ζ ≠ 1 := fun ζ hζ h => by
    rw [h, mem_ball, dist_zero_right, norm_one] at hζ; exact lt_irrefl _ hζ
  refine ⟨?_, ⟨fun ζ hζ => jointInv_mem hΨ hw ht hWr hWr0 hu hK hd (QuantumZipper.CA.cayleyInv_mem_H hζ),
    fun ζ hζ ζ' hζ' he => ?_, fun z hz => ?_⟩⟩
  · intro ζ hζ
    have hy := QuantumZipper.CA.cayleyInv_mem_H hζ
    have h1 : DifferentiableAt ℂ (fwdMapInv Wr u) (cayleyInv ζ) :=
      (isConformalBijection_fwdMapInv hWr hWr0 hu).1.differentiableAt (QuantumZipper.isOpen_H.mem_nhds hy)
    have h2 : DifferentiableAt ℂ Ψi (fwdMapInv Wr u (cayleyInv ζ)) :=
      hΨ.diff_inv.differentiableAt (QuantumZipper.isOpen_H.mem_nhds
        (QuantumZipper.RS.fwdMapInv_mem_H hWr hWr0 hu hy))
    exact (h2.comp ζ (h1.comp ζ (QuantumZipper.CA.differentiableAt_cayleyInv (hc1 ζ hζ)))).differentiableWithinAt
  · have he' := congrArg (jointFwd Ψ Wr u) he
    simp only at he'
    rw [jointFwd_jointInv hΨ hw ht hWr hWr0 hu hK hd (QuantumZipper.CA.cayleyInv_mem_H hζ),
      jointFwd_jointInv hΨ hw ht hWr hWr0 hu hK hd (QuantumZipper.CA.cayleyInv_mem_H hζ')] at he'
    rw [← QuantumZipper.CA.cayley_cayleyInv (hc1 ζ hζ), he', QuantumZipper.CA.cayley_cayleyInv (hc1 ζ' hζ')]
  · have hy := jointFwd_mem hΨ hw ht hWr hWr0 hu hK hd hz
    refine ⟨cayley (jointFwd Ψ Wr u z), QuantumZipper.CA.cayley_mem_ball hy, ?_⟩
    simp only
    rw [QuantumZipper.CA.cayleyInv_cayley (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (le_of_lt hy)),
      jointInv_jointFwd hΨ hw ht hWr hWr0 hu hK hd hz]

theorem continuousOn_jointLift : ContinuousOn (jointLift Ψ LΨ Wr u) (H \ (A ∪ fwdHull w t)) := by
  intro z hz
  obtain ⟨hzA, hzK⟩ := (mem_C_iff hΨ hw ht hWr hWr0 hu hK hd).1 hz
  have hΨc : ContinuousAt Ψ z := (hΨ.conf.1.differentiableAt (hΨ.isOpen.mem_nhds hzA)).continuousAt
  have h1 : ContinuousAt (fun z => (logDerivFwd Wr u (Ψ z)).im) z :=
    continuous_im.continuousAt.comp ((continuousAt_logDerivFwd hWr hu hzK).comp hΨc)
  have h2 : ContinuousAt (fun z => (LΨ z).im) z :=
    continuous_im.continuousAt.comp (hΨ.log.1.differentiableAt (hΨ.isOpen.mem_nhds hzA)).continuousAt
  exact (h1.add h2).continuousWithinAt

/-- **The inherited argument of the joint chart**: `jointFwd' = ‖jointFwd'‖ e^{i L}` with `L = jointLift`. -/
theorem deriv_jointFwd {z : ℂ} (hz : z ∈ H \ (A ∪ fwdHull w t)) :
    deriv (jointFwd Ψ Wr u) z = ‖deriv (jointFwd Ψ Wr u) z‖ * Complex.exp (jointLift Ψ LΨ Wr u z * Complex.I) := by
  obtain ⟨hzA, hzK⟩ := (mem_C_iff hΨ hw ht hWr hWr0 hu hK hd).1 hz
  have h1 : DifferentiableAt ℂ (fwdMap Wr u) (Ψ z) :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hWr hu).differentiableAt
      ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hWr hu).mem_nhds hzK)
  have h2 : DifferentiableAt ℂ Ψ z := hΨ.conf.1.differentiableAt (hΨ.isOpen.mem_nhds hzA)
  have hchain : deriv (jointFwd Ψ Wr u) z = deriv (fwdMap Wr u) (Ψ z) * deriv Ψ z :=
    deriv_comp z h1 h2
  have e1 := (isDerivLog_fwdMap hWr hu).2 (Ψ z) hzK
  have e2 := hΨ.log.2 z hzA
  set a : ℂ := logDerivFwd Wr u (Ψ z) + LΨ z with ha
  have hexp : deriv (jointFwd Ψ Wr u) z = Complex.exp a := by
    rw [hchain, ← e1, ← e2, ha, Complex.exp_add]
  have hL : jointLift Ψ LΨ Wr u z = a.im := by simp only [jointLift, ha, Complex.add_im]
  rw [hexp, hL, Complex.norm_exp]
  conv_lhs => rw [← Complex.re_add_im a]
  rw [Complex.exp_add, Complex.ofReal_exp]

end Chart

end InteractingSLE.Supp8.BHMean
