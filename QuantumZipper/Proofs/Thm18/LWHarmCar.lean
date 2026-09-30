import QuantumZipper.Proofs.Thm18.LWHarmMeas
import QuantumZipper.Proofs.Complex.CaraExt
import QuantumZipper.Proofs.Complex.CaraBdrySurj
import QuantumZipper.Proofs.Complex.KoebeBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, LW-FAR route (D60): harmonic measure in bounded domains with ULC boundary

Task LW-HARM (A) + (B). For a bounded domain `D = ψ(ℍ)` (`ψ` conformal) whose frontier lies in
a closed, bounded, uniformly locally connected set `E ⊆ ℂ \ D` (`CA.Car.CarHyp`, `CA.Topo.ULC`),
the repository's Carathéodory extension theorem (`CA.Car.continuousOn_extension`, Pommerenke,
*Boundary Behaviour of Conformal Maps*, Thm 2.1; boundary surjectivity
`CA.Car.frontier_eq_insert_range`, Pommerenke Thm 2.6) gives the boundary parametrization
`LWBdryParam` of `LWHarmMeas.lean`, with inverse `invFunOn ψ ℍ` holomorphic
(`CA.Koebe.hasDerivAt_invFunOn_of_injOn`). Hence (Garnett–Marshall, *Harmonic Measure*, Ch. I
(1.6), p. 5):

`lwHarm_exists_car`: every bounded `A` disjoint from `D`, whose closure misses some frontier
point of `D`, has a harmonic measure `IsHarmMeas D A h`.

The frontier point off `closure A` is moved to `∞` by the automorphism `w ↦ t₁ − 1/w` of `ℍ`
(own elementary step). This covers `bddPart (ℍ \ ξ)` for a crosscut `ξ`, and `D₁ \ η`, once
`CarHyp` and `ULC` are checked for these domains (their frontier is contained in
`ξ ∪ η ∪ [real segment]`, a finite union of arcs: `CA.Topo.ULC.image_Icc`, `ULC.union`).
-/

noncomputable section

open MeasureTheory Filter Set Metric Complex
open scoped Topology Real

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

open QuantumZipper.CA

lemma lwHarm_ev_far_H {p : ℂ → Prop} (h : ∀ᶠ w in Bornology.cobounded ℂ ⊓ 𝓟 H, p w) :
    ∃ R, ∀ w ∈ H, R < ‖w‖ → p w := by
  rw [eventually_inf_principal] at h
  obtain ⟨R, -, hR⟩ := (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).eventually_iff.1 h
  exact ⟨R, fun w hw hwR => hR (by simpa [mem_closedBall, dist_zero_right] using hwR) hw⟩

/-- A limit at `∞` inside `ℍ` passes to the continuous extension on `ℍ̄`. -/
lemma lwHarm_tendsto_Hbar {ψ F : ℂ → ℂ} (hEq : EqOn F ψ H) (hF : ContinuousOn F Hbar) {p : ℂ}
    (hψ : Tendsto ψ (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 p)) :
    Tendsto F (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (𝓝 p) := by
  refine (Metric.nhds_basis_closedBall.tendsto_right_iff).2 fun ε hε => ?_
  obtain ⟨R, hR⟩ := lwHarm_ev_far_H (hψ.eventually (closedBall_mem_nhds p hε))
  rw [eventually_inf_principal]
  filter_upwards [Bornology.isBounded_def.1 (isBounded_closedBall (x := (0 : ℂ)) (r := R))]
    with w hw hwH
  have hU : IsOpen {u : ℂ | R < ‖u‖} := isOpen_lt continuous_const continuous_norm
  have hwU : w ∈ {u : ℂ | R < ‖u‖} := by
    simpa [mem_closedBall, dist_zero_right] using hw
  have hcl : w ∈ closure (H ∩ {u : ℂ | R < ‖u‖}) := by
    have hwc : w ∈ closure H := by rw [CA.Car.closure_H_eq_Hbar]; exact hwH
    exact hU.closure_inter ⟨hwc, hwU⟩
  have hc : ContinuousWithinAt F (H ∩ {u : ℂ | R < ‖u‖}) w :=
    (hF w hwH).mono (inter_subset_left.trans H_subset_Hbar)
  have hsub : F '' (H ∩ {u : ℂ | R < ‖u‖}) ⊆ closedBall p ε := by
    rintro _ ⟨u, ⟨huH, huR⟩, rfl⟩
    rw [hEq huH]; exact hR u huH huR
  exact (closure_minimal hsub isClosed_closedBall) (hc.mem_closure_image hcl)

/-- The boundary parametrization given by the Carathéodory extension. -/
lemma lwHarm_param_of_car {ψ F : ℂ → ℂ} {D E : Set ℂ} {R₀ : ℝ} (h : Car.CarHyp ψ D E R₀)
    (hEq : EqOn F ψ H) (hF : ContinuousOn F Hbar) (hFr : ∀ x : ℝ, F x ∈ frontier D) :
    LWBdryParam D F (Function.invFunOn ψ H) := by
  have hex : ∀ z ∈ D, ∃ a ∈ H, ψ a = z := fun z hz => h.bij.surjOn hz
  refine ⟨h.isOpen, ?_, fun z hz => Function.invFunOn_mem (hex z hz), ?_, hF, ?_, ?_⟩
  · intro z hz
    obtain ⟨ζ, hζ, rfl⟩ := hex z hz
    exact (Koebe.hasDerivAt_invFunOn_of_injOn isOpen_H h.holo h.bij.injOn hζ).differentiableAt
      |>.differentiableWithinAt
  · intro z hz
    rw [hEq (Function.invFunOn_mem (hex z hz))]
    exact Function.invFunOn_eq (hex z hz)
  · intro w hw
    rw [hEq hw]; exact h.bij.mapsTo hw
  · intro t ht
    have := hFr t
    rw [h.isOpen.frontier_eq] at this
    exact this.2 ht

/-- Existence when the limit of `ψ` at `∞` is off `closure A`. -/
theorem lwHarm_exists_car_of_inf {ψ : ℂ → ℂ} {D E A : Set ℂ} {R₀ : ℝ}
    (h : Car.CarHyp ψ D E R₀) (hE : Topo.ULC E) (hA : Bornology.IsBounded A) (hAD : Disjoint A D)
    (hinf : ∀ p, Tendsto ψ (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 p) → p ∉ closure A) :
    ∃ hm : ℂ → ℝ, IsHarmMeas D A hm := by
  obtain ⟨F, hEq, hF, hFr, wInf, -, hInf⟩ := Car.continuousOn_extension h hE
  exact ⟨_, lwHarm_isHarmMeas (lwHarm_param_of_car h hEq hF hFr) hA hAD
    (Or.inr ⟨wInf, hinf wInf hInf, lwHarm_tendsto_Hbar hEq hF hInf⟩)⟩

/-- The automorphism `w ↦ t₁ − 1/w` of `ℍ`. -/
def lwHarmMob (t₁ : ℝ) (w : ℂ) : ℂ := (t₁ : ℂ) - w⁻¹

lemma lwHarmMob_im (t₁ : ℝ) (w : ℂ) : (lwHarmMob t₁ w).im = w.im / Complex.normSq w := by
  simp [lwHarmMob, Complex.inv_im, neg_div]

lemma lwHarmMob_mapsTo (t₁ : ℝ) : MapsTo (lwHarmMob t₁) H H := by
  intro w hw
  have hw' : 0 < w.im := hw
  show 0 < (lwHarmMob t₁ w).im
  rw [lwHarmMob_im]
  exact div_pos hw' (Complex.normSq_pos.2 fun h0 => by simp [h0] at hw')

lemma lwHarmMob_bijOn (t₁ : ℝ) : BijOn (lwHarmMob t₁) H H := by
  refine ⟨lwHarmMob_mapsTo t₁, ?_, ?_⟩
  · intro a _ b _ hab
    simpa [lwHarmMob] using hab
  · intro u hu
    have hu' : 0 < u.im := hu
    have hne : (t₁ : ℂ) - u ≠ 0 := fun h0 => by
      have := congrArg Complex.im h0; simp at this; linarith
    refine ⟨((t₁ : ℂ) - u)⁻¹, ?_, ?_⟩
    · show 0 < (((t₁ : ℂ) - u)⁻¹).im
      rw [Complex.inv_im, Complex.normSq_apply]
      simp only [sub_im, ofReal_im, zero_sub, neg_neg]
      refine div_pos hu' ?_
      have : (t₁ - u.re) * (t₁ - u.re) + -u.im * -u.im = (t₁ - u.re) ^ 2 + u.im ^ 2 := by ring
      simp only [sub_re, ofReal_re]
      nlinarith [sq_nonneg (t₁ - u.re)]
    · simp [lwHarmMob]

lemma lwHarmMob_diffOn (t₁ : ℝ) : DifferentiableOn ℂ (lwHarmMob t₁) H := by
  intro w hw
  have hw0 : w ≠ 0 := fun h0 => by
    have : (0 : ℝ) < w.im := hw
    simp [h0] at this
  exact ((differentiableAt_const _).sub (differentiableAt_inv hw0)).differentiableWithinAt

/-- **Harmonic measure exists** in a bounded domain with ULC boundary for every bounded `A`
disjoint from `D` whose closure misses a frontier point of `D`. -/
theorem lwHarm_exists_car {ψ : ℂ → ℂ} {D E A : Set ℂ} {R₀ : ℝ}
    (h : Car.CarHyp ψ D E R₀) (hE : Topo.ULC E) (hA : Bornology.IsBounded A) (hAD : Disjoint A D)
    (hq : ∃ q ∈ frontier D, q ∉ closure A) :
    ∃ hm : ℂ → ℝ, IsHarmMeas D A hm := by
  obtain ⟨F, hEq, hF, hFr, wInf, -, hInf⟩ := Car.continuousOn_extension h hE
  by_cases hw : wInf ∈ closure A
  · obtain ⟨q, hqD, hqA⟩ := hq
    rw [Car.frontier_eq_insert_range h hEq hF hInf] at hqD
    rcases hqD with rfl | ⟨t₁, rfl⟩
    · exact absurd hw hqA
    -- move `t₁` to `∞`
    have h1 : Car.CarHyp (ψ ∘ lwHarmMob t₁) D E R₀ :=
      ⟨h.holo.comp (lwHarmMob_diffOn t₁) (lwHarmMob_mapsTo t₁),
        h.bij.comp (lwHarmMob_bijOn t₁), h.isOpen, h.bdd, h.isClosed, h.frontier_sub,
        h.sub_compl, h.E_bdd⟩
    refine lwHarm_exists_car_of_inf h1 hE hA hAD fun p hp => ?_
    have hlim : Tendsto (ψ ∘ lwHarmMob t₁) (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 (F t₁)) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨δ, hδ, hc⟩ := Metric.continuousWithinAt_iff.1
        (hF (t₁ : ℂ) (lwHarm_real_mem_Hbar t₁)) ε hε
      rw [eventually_inf_principal]
      filter_upwards [Bornology.isBounded_def.1
        (isBounded_closedBall (x := (0 : ℂ)) (r := δ⁻¹))] with w hw hwH
      have hwn : δ⁻¹ < ‖w‖ := by simpa [mem_closedBall, dist_zero_right] using hw
      have hMH := lwHarmMob_mapsTo t₁ hwH
      simp only [Function.comp_apply]
      rw [← hEq hMH]
      refine hc (H_subset_Hbar hMH) ?_
      rw [dist_eq_norm]
      simp only [lwHarmMob, sub_sub_cancel_left, norm_neg, norm_inv]
      have hδ' : 0 < δ⁻¹ := inv_pos.2 hδ
      calc ‖w‖⁻¹ < (δ⁻¹)⁻¹ := inv_strictAnti₀ hδ' hwn
        _ = δ := inv_inv δ
    have := Car.neBot_cobounded_inf_H
    rw [tendsto_nhds_unique hp hlim]
    exact hqA
  · exact lwHarm_exists_car_of_inf h hE hA hAD fun p hp => by
      have := Car.neBot_cobounded_inf_H
      rw [tendsto_nhds_unique hp hInf]; exact hw

end LWFar
end Thm18Asm
end QuantumZipper
