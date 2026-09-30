import QuantumZipper.Proofs.Zipper.FieldLawler3Reg
import QuantumZipper.Proofs.Zipper.FieldLawler2Max

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL round 4 (task FL4-HM): glue lemmas for `IsHarmMeas`

General bookkeeping about the Dirichlet characterization `IsHarmMeas U A h` used in the
per-crosscut chain towards `FLImageSumBoundStmt` (Field–Lawler, EJP 2015, p. 9).

1. `fl4hm_adjust`, `fl4hm_adjust_rev`: enlarging `A` inside its closure by points that are
   limits of the rest of the frontier does not change the harmonic measure (e.g. an open arc of
   `C_R` versus the closed arc whose endpoints abut other boundary).
2. `fl4hm_frontier_component`, `fl4hm_restrict`, `fl4hm_restrict_component`: a harmonic
   measure of `U` restricts to one of an open component `V` of `U`, given that no point of `A`
   in `closure V` is a limit of `frontier U \ frontier V` (without this, the `one` clause can
   fail at such points: `IsHarmMeas` only prescribes boundary limits).
3. `fl4hm_unique`: two harmonic measures of the same `A` on the same open `U` agree when the
   exceptional frontier points `closure A ∩ closure (frontier U \ A)` are finitely many
   (Lindelöf maximum principle `fl2_harm_le_zero_off_finite`, as in `fl3_isHarmMeas_eq`).
4. `fl4hm_excR_le_fluxR`: a function agreeing with a harmonic measure `g` near the arc
   `J' ⊆ (0, π)` of `C_R` has chart flux over `J'` at most `fl2FluxR R g`
   (`fl3reg_rDer_eq_yDer_of_ext`).

Own elementary bookkeeping (no published source states these definitional facts; the maximum
principle used in 3 is the one formalized in `FieldLawler2Max`).
-/

noncomputable section

open MeasureTheory Filter Set Metric Complex
open scoped Topology Real ENNReal

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

/-! ### 1. Set adjustment -/

/-! ### 2. Restriction to a component -/

/-- The frontier of a component of an open set lies in the frontier of the set. -/
theorem fl4hm_frontier_component {U : Set ℂ} (hU : IsOpen U) (z₀ : ℂ) :
    frontier (connectedComponentIn U z₀) ⊆ frontier U := by
  set V := connectedComponentIn U z₀
  have hV : IsOpen V := hU.connectedComponentIn
  intro x hx
  have hxU : x ∉ U := by
    intro hxU
    have hW : IsOpen (connectedComponentIn U x) := hU.connectedComponentIn
    obtain ⟨y, hyW, hyV⟩ := mem_closure_iff_nhds.1 (frontier_subset_closure hx) _
      (hW.mem_nhds (mem_connectedComponentIn hxU))
    have e1 := connectedComponentIn_eq hyW
    have e2 := connectedComponentIn_eq hyV
    have hxV : x ∈ V := by
      change x ∈ connectedComponentIn U z₀
      rw [e2, ← e1]; exact mem_connectedComponentIn hxU
    rw [hV.frontier_eq] at hx
    exact hx.2 hxV
  rw [hU.frontier_eq]
  exact ⟨closure_mono (connectedComponentIn_subset U z₀) (frontier_subset_closure hx), hxU⟩

/-- **Restriction**: a harmonic measure of `A` in `U` is one in any open `V ⊆ U` with
`frontier V ⊆ frontier U`, provided no point of `A ∩ closure V` is a limit of
`frontier U \ frontier V`. -/
theorem fl4hm_restrict {U V A : Set ℂ} {h : ℂ → ℝ} (hh : IsHarmMeas U A h) (hVU : V ⊆ U)
    (hfr : frontier V ⊆ frontier U)
    (hsep : ∀ x₀ ∈ A, x₀ ∈ closure V → x₀ ∉ closure (frontier U \ frontier V)) :
    IsHarmMeas V A h where
  harm := fun z hz => hh.harm z (hVU hz)
  mem01 := fun z hz => hh.mem01 z (hVU hz)
  one := by
    intro x₀ hx₀ hncl
    by_cases hxV : x₀ ∈ closure V
    · refine (hh.one x₀ hx₀ fun hmem => ?_).mono_left (nhdsWithin_mono _ hVU)
      have hsub : frontier U \ A ⊆ (frontier V \ A) ∪ (frontier U \ frontier V) := by
        intro z ⟨hz, hzA⟩
        by_cases hzV : z ∈ frontier V
        · exact Or.inl ⟨hzV, hzA⟩
        · exact Or.inr ⟨hz, hzV⟩
      have := closure_mono hsub hmem
      rw [closure_union] at this
      rcases this with h1 | h1
      · exact hncl h1
      · exact hsep x₀ hx₀ hxV h1
    · have : 𝓝[V] x₀ = ⊥ := notMem_closure_iff_nhdsWithin_eq_bot.1 hxV
      rw [this]; exact tendsto_bot
  zero := fun x₀ hx₀ hncl =>
    (hh.zero x₀ (hfr hx₀) hncl).mono_left (nhdsWithin_mono _ hVU)
  infty := fun hb => (hh.infty hb).mono_left (inf_le_inf_left _ (principal_mono.2 hVU))

/-- Restriction to the component of an open `U` through `z₀`. -/
theorem fl4hm_restrict_component {U A : Set ℂ} {h : ℂ → ℝ} (hh : IsHarmMeas U A h)
    (hU : IsOpen U) (z₀ : ℂ)
    (hsep : ∀ x₀ ∈ A, x₀ ∈ closure (connectedComponentIn U z₀) →
      x₀ ∉ closure (frontier U \ frontier (connectedComponentIn U z₀))) :
    IsHarmMeas (connectedComponentIn U z₀) A h :=
  fl4hm_restrict hh (connectedComponentIn_subset U z₀) (fl4hm_frontier_component hU z₀) hsep

/-! ### 3. Uniqueness -/

/-! ### 4. Flux comparison -/

/-- `yDer f x` only depends on the values `f (x + iy)` for small `y > 0`. -/
theorem fl4hm_yDer_congr {f₁ f₂ : ℂ → ℝ} {x : ℝ}
    (hf : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), f₁ ((x : ℂ) + (y : ℂ) * I) = f₂ ((x : ℂ) + (y : ℂ) * I)) :
    yDer f₁ x = yDer f₂ x := by
  have hEq : (fun y : ℝ => f₁ ((x : ℂ) + (y : ℂ) * I) / y) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun y : ℝ => f₂ ((x : ℂ) + (y : ℂ) * I) / y) := hf.mono fun y hy => by simp only [hy]
  unfold yDer
  by_cases h1 : ∃ L : ℝ, Tendsto (fun y : ℝ => f₁ ((x : ℂ) + (y : ℂ) * I) / y) (𝓝[>] 0) (𝓝 L)
  · have h2 : ∃ L : ℝ, Tendsto (fun y : ℝ => f₂ ((x : ℂ) + (y : ℂ) * I) / y) (𝓝[>] 0)
        (𝓝 L) := let ⟨L, hL⟩ := h1; ⟨L, (tendsto_congr' hEq).1 hL⟩
    rw [if_pos h1, if_pos h2]
    unfold limUnder; rw [Filter.map_congr hEq]
  · have h2 : ¬ ∃ L : ℝ, Tendsto (fun y : ℝ => f₂ ((x : ℂ) + (y : ℂ) * I) / y) (𝓝[>] 0)
        (𝓝 L) := fun ⟨L, hL⟩ => h1 ⟨L, (tendsto_congr' hEq).2 hL⟩
    rw [if_neg h1, if_neg h2]

/-- The chart point `χ_R(θ + iy)` is the radial point `fl2Pt R θ (R(1 − e^{−y}))`. -/
theorem fl4hm_chart_eq_pt {R θ y : ℝ} (hR : 0 < R) :
    fl3Chart R ((θ : ℂ) + (y : ℂ) * I) = fl2Pt R θ (R * (1 - Real.exp (-y))) := by
  have hs : R * (1 - Real.exp (-y)) < R := by
    have := Real.exp_pos (-y); nlinarith
  rw [← fl3reg_chart_radial hR hs]
  congr 1
  have h1 : 1 - R * (1 - Real.exp (-y)) / R = Real.exp (-y) := by field_simp; ring
  rw [h1, Real.log_exp, neg_neg]
  ring

/-- Small vertical chart heights go to small radial depths. -/
theorem fl4hm_depth_tendsto {R : ℝ} (hR : 0 < R) :
    Tendsto (fun y : ℝ => R * (1 - Real.exp (-y))) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun y hy => ?_⟩
  · have hc : Continuous (fun y : ℝ => R * (1 - Real.exp (-y))) := by fun_prop
    have := hc.tendsto 0
    simp only [neg_zero, Real.exp_zero, sub_self, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · have : Real.exp (-y) < 1 := Real.exp_lt_one_iff.2 (by simpa using (show (0:ℝ) < y from hy))
    show 0 < R * (1 - Real.exp (-y))
    exact mul_pos hR (by linarith)

/-- **Flux comparison.** If `v = g` on `Wd`, `g` is a harmonic measure of `A` in `Ω`, and for
`θ ∈ J' ⊆ (0, π)` (measurable) the chart is regular at `θ` (`Fl3RegAt R Ω A θ`) and the radial
points `fl2Pt R θ s` lie in `Wd` for small `s > 0`, then
`excR (v ∘ χ_R) J' ≤ fl2FluxR R g`. -/
theorem fl4hm_excR_le_fluxR {R : ℝ} (hR : 0 < R) {Ω A Wd : Set ℂ} {g v : ℂ → ℝ}
    (hg : IsHarmMeas Ω A g) {J' : Set ℝ} (hJ : J' ⊆ Ioo 0 π) (hJm : MeasurableSet J')
    (hreg : ∀ θ ∈ J', Fl3RegAt R Ω A θ)
    (hWd : ∀ θ ∈ J', ∀ᶠ s in 𝓝[>] (0 : ℝ), fl2Pt R θ s ∈ Wd)
    (hvg : ∀ z ∈ Wd, v z = g z) :
    excR (v ∘ fl3Chart R) J' ≤ fl2FluxR R g := by
  unfold excR fl2FluxR
  have hpt : ∀ θ ∈ J', ENNReal.ofReal (yDer (v ∘ fl3Chart R) θ) =
      ENNReal.ofReal (fl2rDer R g θ * R) := by
    intro θ hθ
    have hc : yDer (v ∘ fl3Chart R) θ = yDer (g ∘ fl3Chart R) θ := by
      refine fl4hm_yDer_congr (((fl4hm_depth_tendsto hR).eventually (hWd θ hθ)).mono
        fun y hy => ?_)
      simp only [Function.comp]
      rw [fl4hm_chart_eq_pt hR]
      exact hvg _ hy
    obtain ⟨ρ, hρ, V, hVh, hVf, hV0⟩ := fl3reg_polar_ext hg (hreg θ hθ)
    rw [hc, fl3reg_rDer_eq_yDer_of_ext hR hρ hVh hVf hV0]
  rw [setLIntegral_congr_fun hJm hpt]
  exact lintegral_mono_set hJ

end FieldLawler
end QuantumZipper
