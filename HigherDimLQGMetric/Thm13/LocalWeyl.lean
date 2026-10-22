import HigherDimLQGMetric.Thm13.LocalFactor
import HigherDimLQGMetric.Thm13.BddLimit

/-! Local internal distances for every continuous Weyl perturbation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set Metric TopologicalSpace
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l8_localInternal_bounds_inside_of_bounded_limits
    {d : ℕ} {κ : Rd d → ℝ}
    (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    (g : DistRd d) (D : ContMetric d) (hD : D.IsLength)
    (hB : ∀ f' : C(Rd d, ℝ), (∃ M : ℝ, ∀ x, |f' x| ≤ M) →
      Tendsto (fun n =>
        (l8_truncScaledMetric hd hκ ξ (hεs n) (addFun g f')).1)
        atTop (𝓝 (weylMetric ξ f' D hD).1))
    (f : C(Rd d, ℝ))
    (W U : Opens (Rd d))
    (hWc : IsPreconnected (W : Set (Rd d)))
    (hK : IsCompact (closure (W : Set (Rd d))))
    (hWU : closure (W : Set (Rd d)) ⊆ U)
    (u v : Rd d) (hu : u ∈ W) (hv : v ∈ W) :
    (weylMetric ξ f D hD).internal U u v ≤
      l8_localInternal hd hκ ξ εs hεs W (addFun g f) u v ∧
    l8_localInternal hd hκ ξ εs hεs W (addFun g f) u v ≤
      (weylMetric ξ f D hD).internal W u v := by
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall (0 : Rd d)
  let R : ℝ := max R₀ 0 + 1
  have hKR : closure (W : Set (Rd d)) ⊆ ball (0 : Rd d) R := by
    intro x hx
    have hxR := hR₀ hx
    rw [mem_closedBall] at hxR
    rw [mem_ball]
    dsimp [R]
    exact lt_of_le_of_lt hxR (by linarith [le_max_left R₀ 0])
  let T : Opens (Rd d) := ⟨ball (0 : Rd d) R, isOpen_ball⟩
  let V : Opens (Rd d) :=
    ⟨(U : Set (Rd d)) ∩ T, U.isOpen.inter T.isOpen⟩
  have hKV : closure (W : Set (Rd d)) ⊆ V :=
    fun x hx => ⟨hWU hx, hKR hx⟩
  obtain ⟨f', hf'bd, hff'⟩ :=
    l8_exists_bounded_agree_ball f (0 : Rd d) R
  have hffT : EqOn (⇑f) (⇑f') T := by
    intro x hx
    exact hff' (ball_subset_closedBall hx)
  have hres : restrictTo T (addFun g f) =
      restrictTo T (addFun g f') :=
    restrictTo_addFun_congr T g hffT
  have hloc : l8_localInternal hd hκ ξ εs hεs W
      (addFun g f) u v =
      l8_localInternal hd hκ ξ εs hεs W
        (addFun g f') u v :=
    l8_localInternal_congr_of_restrictTo hd hκ ξ εs hεs
      hεt W T hK hKR hres u v
  let Df : ContMetric d := weylMetric ξ f D hD
  let Df' : ContMetric d := weylMetric ξ f' D hD
  have hVEq : Df.internal V u v = Df'.internal V u v :=
    l8_weyl_internal_congr ξ D hD f f' V.isOpen
      (fun x hx => hffT hx.2) u v
  have hWEq : Df.internal W u v = Df'.internal W u v :=
    l8_weyl_internal_congr ξ D hD f f' W.isOpen
      (fun x hx => hffT (hKR (subset_closure hx))) u v
  let Dn : ℕ → ContMetric d := fun n =>
    l8_truncScaledMetric hd hκ ξ (hεs n) (addFun g f')
  have hDn (n : ℕ) : (Dn n).IsLength :=
    l8_truncScaledMetric_isLength hd hκ ξ (hεs n) (addFun g f')
  have hconv : Tendsto (fun n => (Dn n).1) atTop (𝓝 Df'.1) :=
    hB f' hf'bd
  constructor
  · calc
      Df.internal U u v ≤ Df.internal V u v :=
        Df.internal_anti (fun x hx => hx.1) u v
      _ = Df'.internal V u v := hVEq
      _ ≤ l8_localInternal hd hκ ξ εs hεs W
          (addFun g f') u v :=
        l8_internal_liminf_ge_enlarged_domain Dn Df'
          (weylMetric_isLength hD) hconv W V hWc hK hKV u v hu hv
      _ = l8_localInternal hd hκ ξ εs hεs W
          (addFun g f) u v := hloc.symm
  · calc
      l8_localInternal hd hκ ξ εs hεs W
          (addFun g f) u v =
        l8_localInternal hd hκ ξ εs hεs W
          (addFun g f') u v := hloc
      _ ≤ Df'.internal W u v :=
        l8_internal_liminf_le_internal Dn Df' hDn hconv W hWc u v hu hv
      _ = Df.internal W u v := hWEq.symm

theorem l8_localFormula_eq_weyl_internal_of_bounded_limits
    {d : ℕ} {κ : Rd d → ℝ}
    (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    (g : DistRd d) (D : ContMetric d) (hD : D.IsLength)
    (hB : ∀ f' : C(Rd d, ℝ), (∃ M : ℝ, ∀ x, |f' x| ≤ M) →
      Tendsto (fun n =>
        (l8_truncScaledMetric hd hκ ξ (hεs n) (addFun g f')).1)
        atTop (𝓝 (weylMetric ξ f' D hD).1))
    (f : C(Rd d, ℝ)) (U : Opens (Rd d)) (u v : Rd d) :
    l8_localFormula hd hκ ξ εs hεs U (addFun g f) u v =
      (weylMetric ξ f D hD).internal U u v := by
  let Df : ContMetric d := weylMetric ξ f D hD
  have hlow : Df.internal U u v ≤
      l8_localFormula hd hκ ξ εs hεs U (addFun g f) u v := by
    unfold l8_localFormula
    apply le_iInf
    intro i
    let W := l7a_compDomain U i
    by_cases hu : u ∈ W
    · by_cases hv : v ∈ W
      · exact (l8_localInternal_bounds_inside_of_bounded_limits
          hd hκ ξ εs hεs hεt g D hD hB f W U
          (l7a_compDomain_connected U i).isPreconnected
          (l7a_compDomain_closure_compact U i)
          (l7a_compDomain_closure_subset U i) u v hu hv).1
      · have htop : l8_localInternal hd hκ ξ εs hεs W
            (addFun g f) u v = ⊤ := by
          unfold l8_localInternal
          have heq : (fun n =>
              (l8_truncScaledMetric hd hκ ξ (hεs n)
                (addFun g f)).internal W u v) =
              (fun _ : ℕ => (⊤ : ℝ≥0∞)) := by
            funext n
            exact (l8_truncScaledMetric hd hκ ξ (hεs n)
              (addFun g f)).internal_eq_top_of_notMem_right hv
          rw [heq, liminf_const]
        rw [htop]
        exact le_top
    · have htop : l8_localInternal hd hκ ξ εs hεs W
          (addFun g f) u v = ⊤ := by
        unfold l8_localInternal
        have heq : (fun n =>
            (l8_truncScaledMetric hd hκ ξ (hεs n)
              (addFun g f)).internal W u v) =
            (fun _ : ℕ => (⊤ : ℝ≥0∞)) := by
          funext n
          exact (l8_truncScaledMetric hd hκ ξ (hεs n)
            (addFun g f)).internal_eq_top_of_notMem_left hu
        rw [heq, liminf_const]
      rw [htop]
      exact le_top
  have hupp : l8_localFormula hd hκ ξ εs hεs U
      (addFun g f) u v ≤ Df.internal U u v := by
    rw [l7a_internal_eq_iInf_compDomain]
    unfold l8_localFormula
    apply iInf_mono
    intro i
    let W := l7a_compDomain U i
    by_cases hu : u ∈ W
    · by_cases hv : v ∈ W
      · exact (l8_localInternal_bounds_inside_of_bounded_limits
          hd hκ ξ εs hεs hεt g D hD hB f W U
          (l7a_compDomain_connected U i).isPreconnected
          (l7a_compDomain_closure_compact U i)
          (l7a_compDomain_closure_subset U i) u v hu hv).2
      · rw [Df.internal_eq_top_of_notMem_right hv]
        exact le_top
    · rw [Df.internal_eq_top_of_notMem_left hu]
      exact le_top
  exact le_antisymm hupp hlow

end HigherDimLQGMetric
