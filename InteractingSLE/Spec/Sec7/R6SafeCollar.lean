/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux41Full

/-!
# Collars of a contained pocket along a shared wall, in the outer Jordan coordinate

PROVE-R6-SAFE, round 4c (toward `R6FaceR`'s collars). For a bounded Jordan domain `C` with a Jordan coordinate
`ψ : C → ℍ` (`Sec6.IsJordanCoord`, which contains the Carathéodory boundary extension):

* `ψ` is proper at every point `p ∈ C̄ ∖ {x₀}`: points of `C̄ ∖ {x₀}` whose coordinates approach `ψ p` approach `p`
  (`jordan_mem_ball_of_mem_ball`; compactness of `C̄`, injectivity, and `ψ → ∞` at `x₀`);
* its inverse `invFunOn ψ C` is continuous on `ℍ` (`continuousOn_invFunOn_jordan`);
* **the collar**: for an open `U ⊆ C` whose frontier inside `C` lies in a closed `M`, every point `p ∈ Ū ∩ ∂C`,
  `p ≠ x₀`, `p ∉ M` (an interior point of a wall shared by `U` and `C`) has a half-disc `ℍ ∩ B(ψ p, r) ⊆ ψ(U)`
  (`exists_halfDisc_subset_image`): the preimage of a small half-disc is connected, lies near `p` (so misses
  `∂U`), and meets `U`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec7.R6Safe

variable {C : Set ℂ} {x₀ y₀ : ℂ} {ψ : ℂ → ℂ}

/-- **Properness of a Jordan coordinate** (bounded domain): for `p ∈ C̄ ∖ {x₀}` and `ε > 0`, every point of
`C̄ ∖ {x₀}` whose coordinate is close enough to `ψ p` is `ε`-close to `p`. -/
theorem jordan_mem_ball_of_mem_ball (hψ : Sec6.IsJordanCoord C x₀ y₀ ψ) (hCb : IsBounded C) {p : ℂ}
    (hp : p ∈ closure C \ {x₀}) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ z ∈ closure C \ {x₀}, ψ z ∈ ball (ψ p) r → z ∈ ball p ε := by
  obtain ⟨hcont, hinj, -, -, -, -, hinf⟩ := hψ
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ z ∈ closure C \ {x₀}, ψ z ∈ ball (ψ p) (1 / ((n : ℝ) + 1)) ∧ z ∉ ball p ε :=
    fun n => hcon _ (by positivity)
  choose z hzK hzψ hzp using hseq
  have hK : IsCompact (closure C) := hCb.isCompact_closure
  obtain ⟨a, haK, φ, hφ, hlim⟩ := hK.tendsto_subseq (fun n => (hzK n).1)
  have hψlim : Tendsto (fun n => ψ (z (φ n))) atTop (𝓝 (ψ p)) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨N, fun n hn => ?_⟩
    have h1 := mem_ball.1 (hzψ (φ n))
    have h2 : (1 : ℝ) / ((φ n : ℕ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      have : (N : ℝ) ≤ φ n := by exact_mod_cast hn.trans (hφ.id_le n)
      gcongr
    linarith
  have hamem : a ∉ ball p ε := by
    have hcl : IsClosed (ball p ε)ᶜ := isOpen_ball.isClosed_compl
    exact hcl.mem_of_tendsto hlim (Eventually.of_forall fun n => hzp (φ n))
  by_cases hax : a = x₀
  · subst hax
    have hwithin : Tendsto (fun n => z (φ n)) atTop (𝓝[closure C \ {a}] a) :=
      tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => hzK (φ n)⟩
    have hcob := hinf.comp hwithin
    have hnorm := (tendsto_norm_cobounded_atTop.comp hcob)
    exact not_tendsto_atTop_of_tendsto_nhds (hψlim.norm) hnorm
  · have haK' : a ∈ closure C \ {x₀} := ⟨haK, hax⟩
    have hwithin : Tendsto (fun n => z (φ n)) atTop (𝓝[closure C \ {x₀}] a) :=
      tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => hzK (φ n)⟩
    have h2 := ((hcont a haK').tendsto).comp hwithin
    have heq : ψ a = ψ p := tendsto_nhds_unique h2 hψlim
    have hap : a = p := hinj haK' hp heq
    exact hamem (hap ▸ mem_ball_self hε)

/-- **The inverse of a Jordan coordinate is continuous on `ℍ`** (bounded domain). -/
theorem continuousOn_invFunOn_jordan (hψ : Sec6.IsJordanCoord C x₀ y₀ ψ) (hCb : IsBounded C) (hx₀ : x₀ ∉ C) :
    ContinuousOn (Function.invFunOn ψ C) H := by
  have hbij := hψ.2.2.2.1.2
  rw [Metric.continuousOn_iff]
  intro w hw ε hε
  have hp : Function.invFunOn ψ C w ∈ C := Function.invFunOn_mem (hbij.surjOn hw)
  have hpw : ψ (Function.invFunOn ψ C w) = w := Function.invFunOn_eq (hbij.surjOn hw)
  obtain ⟨r, hr, hball⟩ := jordan_mem_ball_of_mem_ball hψ hCb
    (p := Function.invFunOn ψ C w) ⟨subset_closure hp, fun h => hx₀ (h ▸ hp)⟩ hε
  refine ⟨r, hr, fun w' hw' hd => ?_⟩
  have hp' : Function.invFunOn ψ C w' ∈ C := Function.invFunOn_mem (hbij.surjOn hw')
  have hpw' : ψ (Function.invFunOn ψ C w') = w' := Function.invFunOn_eq (hbij.surjOn hw')
  have h := hball (Function.invFunOn ψ C w') ⟨subset_closure hp', fun h => hx₀ (h ▸ hp')⟩
    (by rw [hpw', hpw]; exact hd)
  exact h

/-- **The collar of a contained domain along a shared wall** (outer Jordan coordinate `ψ` of a bounded `C`): if
`U ⊆ C` is open, `∂U ∩ C ⊆ M` with `M` closed, and `p ∈ Ū ∩ ∂C`, `p ≠ x₀`, `p ∉ M`, then some half-disc
`ℍ ∩ B(ψ p, r)` lies in `ψ(U)`. -/
theorem exists_halfDisc_subset_image (hψ : Sec6.IsJordanCoord C x₀ y₀ ψ) (hCb : IsBounded C) (hx₀ : x₀ ∉ C)
    {U M : Set ℂ} (hUo : IsOpen U) (hUC : U ⊆ C) (hM : IsClosed M) (hfr : frontier U ∩ C ⊆ M) {p : ℂ}
    (hpU : p ∈ closure U) (hpC : p ∈ closure C) (hpx : p ≠ x₀) (hpM : p ∉ M) :
    ∃ r > 0, H ∩ ball (ψ p) r ⊆ ψ '' U := by
  have hbij := hψ.2.2.2.1.2
  obtain ⟨δ, hδ, hδM⟩ := Metric.isOpen_iff.1 hM.isOpen_compl p hpM
  obtain ⟨r, hr, hball⟩ := jordan_mem_ball_of_mem_ball hψ hCb ⟨hpC, hpx⟩ hδ
  refine ⟨r, hr, ?_⟩
  set D := H ∩ ball (ψ p) r with hD
  set S := Function.invFunOn ψ C '' D with hS
  have hDH : D ⊆ H := inter_subset_left
  have hSpre : IsPreconnected S :=
    (((convex_halfSpace_gt Complex.imLm.isLinear 0 : Convex ℝ H).inter (convex_ball _ _)).isPreconnected).image _
      ((continuousOn_invFunOn_jordan hψ hCb hx₀).mono hDH)
  have hSC : ∀ w ∈ D, Function.invFunOn ψ C w ∈ C := fun w hw => Function.invFunOn_mem (hbij.surjOn hw.1)
  have hSψ : ∀ w ∈ D, ψ (Function.invFunOn ψ C w) = w := fun w hw => Function.invFunOn_eq (hbij.surjOn hw.1)
  -- `S` lies near `p`, hence off the frontier of `U`
  have hSsub : S ⊆ U ∪ (closure U)ᶜ := by
    rintro _ ⟨w, hw, rfl⟩
    have hzC := hSC w hw
    have hzb : Function.invFunOn ψ C w ∈ ball p δ :=
      hball _ ⟨subset_closure hzC, fun h => hx₀ (h ▸ hzC)⟩ (by rw [hSψ w hw]; exact hw.2)
    by_cases hzU : Function.invFunOn ψ C w ∈ U
    · exact Or.inl hzU
    · refine Or.inr fun hcl => hδM hzb ?_
      exact hfr ⟨⟨hcl, by rwa [hUo.interior_eq]⟩, hzC⟩
  -- `S` meets `U`
  have hcontp := (hψ.1 p ⟨hpC, hpx⟩)
  obtain ⟨ρ, hρ, hρψ⟩ := Metric.continuousWithinAt_iff.1 hcontp r hr
  obtain ⟨u, huU, hud⟩ := Metric.mem_closure_iff.1 hpU ρ hρ
  have huC := hUC huU
  have huD : ψ u ∈ D := ⟨hbij.mapsTo huC, hρψ ⟨subset_closure huC, fun h => hx₀ (h ▸ huC)⟩
    (by rw [dist_comm]; exact hud)⟩
  have huS : u ∈ S := ⟨ψ u, huD, hbij.injOn.leftInvOn_invFunOn huC⟩
  have hSU : S ⊆ U := hSpre.subset_left_of_subset_union hUo isClosed_closure.isOpen_compl
    (disjoint_compl_right.mono_right (compl_subset_compl.2 subset_closure)) hSsub ⟨u, huS, huU⟩
  intro w hw
  exact ⟨_, hSU ⟨w, hw, rfl⟩, hSψ w hw⟩

end InteractingSLE.Sec7.R6Safe
