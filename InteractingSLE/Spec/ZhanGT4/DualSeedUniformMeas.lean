/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedMeas
import InteractingSLE.Spec.ZhanGT4.DualSeedBoundRegularity

/-!
# Alive-event measurability of the normalized seeded density

Packet PROVE-ZHAN-GT4-A22. Divided differences use the measurable derivative
on the diagonal, so this argument also applies at the entrance time.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A moving divided difference is measurable from its endpoint values and
the derivative at its first endpoint, including on the diagonal. -/
theorem measurable_indicator_dslope {G : Set Ω} (_hG : MeasurableSet G)
    {f : Ω → ℝ → ℝ} {U V DU : Ω → ℝ}
    (hU : Measurable (G.indicator U)) (hV : Measurable (G.indicator V))
    (hFU : Measurable (G.indicator fun ω => f ω (U ω)))
    (hFV : Measurable (G.indicator fun ω => f ω (V ω)))
    (hDU : Measurable (G.indicator DU))
    (hD : ∀ ω ∈ G, deriv (f ω) (U ω) = DU ω) :
    Measurable (G.indicator fun ω => dslope (f ω) (U ω) (V ω)) := by
  classical
  have hm : Measurable (fun ω => if G.indicator V ω = G.indicator U ω then
      G.indicator DU ω else
      (G.indicator (fun ω => f ω (V ω)) ω - G.indicator (fun ω => f ω (U ω)) ω) /
        (G.indicator V ω - G.indicator U ω)) :=
    hDU.ite (measurableSet_eq_fun hV hU) ((hFV.sub hFU).div (hV.sub hU))
  convert hm using 1
  funext ω
  by_cases hω : ω ∈ G
  · simp only [indicator_of_mem hω]
    by_cases he : V ω = U ω
    · simp only [he, ↓reduceIte, dslope_same, hD ω hω]
    · simp only [he, ↓reduceIte, dslope_of_ne _ he, slope_def_field]
  · simp only [indicator_of_notMem hω, ↓reduceIte]

namespace SeedData

/-- Measurability of the finite gap family from A21's component outputs. -/
theorem measurable_indicator_gapVal {n : ℕ} {d : Ω → SeedData n} {G : Set Ω}
    (hG : MeasurableSet G) {t : ℝ}
    (hA0 : Measurable (G.indicator fun ω => (d ω).A 0 t))
    (hA20 : Measurable (G.indicator fun ω => (d ω).A20 t))
    (hA21 : Measurable (G.indicator fun ω => (d ω).A21 t))
    (hB0 : ∀ m, Measurable (G.indicator fun ω => (d ω).B0 t m))
    (hB1 : ∀ m, Measurable (G.indicator fun ω => (d ω).B1 t m))
    (hW : Measurable (G.indicator fun ω => (d ω).W t))
    (hV0 : Measurable (G.indicator fun ω => (d ω).V₀ t))
    (hV : ∀ m, Measurable (G.indicator fun ω => (d ω).V m t)) :
    ∀ i, Measurable (G.indicator fun ω => (d ω).gapVal i t) := by
  have subm : ∀ {f g : Ω → ℝ}, Measurable (G.indicator f) →
      Measurable (G.indicator g) → Measurable (G.indicator fun ω => f ω - g ω) := by
    intro f g hf hg
    convert hf.sub hg using 1
    funext ω
    by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω, Pi.sub_apply]
    · simp only [indicator_of_notMem hω, Pi.sub_apply, sub_self]
  intro i
  rcases i with i | i
  · fin_cases i
    · exact subm hA20 hA0
    · exact hA21
    · exact subm hV0 hW
  · rcases i with ⟨i, m⟩ | ⟨i, m, k⟩
    · fin_cases i
      · exact subm (hB0 m) hA0
      · exact subm hA20 (hB0 m)
      · exact hB1 m
      · exact subm (hV m) hW
      · exact subm hV0 (hV m)
    · by_cases hmk : m = k
      · simpa only [gapVal, hmk, ↓reduceIte] using
          (measurable_const.indicator hG : Measurable (G.indicator fun _ : Ω => (1 : ℝ)))
      · fin_cases i
        · simpa [gapVal, hmk] using subm (hB0 m) (hB0 k)
        · simpa [gapVal, hmk] using subm (hV m) (hV k)

/-- The normalized log is measurable on an alive event even when seed
coordinates coincide. Only the diagonal derivative identity is needed. -/
theorem measurable_indicator_normEll {n : ℕ} {d : Ω → SeedData n} {G : Set Ω}
    (hG : MeasurableSet G) {t κ : ℝ} {rr : Fin n → ℝ}
    (hdκ : ∀ ω, (d ω).κ = κ) (hdr : ∀ ω, (d ω).r = rr)
    (hA : ∀ k, Measurable (G.indicator fun ω => (d ω).A k t))
    (hA20 : Measurable (G.indicator fun ω => (d ω).A20 t))
    (hA21 : Measurable (G.indicator fun ω => (d ω).A21 t))
    (hL : Measurable (G.indicator fun ω => (d ω).L t))
    (hB0 : ∀ m, Measurable (G.indicator fun ω => (d ω).B0 t m))
    (hB1 : ∀ m, Measurable (G.indicator fun ω => (d ω).B1 t m))
    (hW : Measurable (G.indicator fun ω => (d ω).W t))
    (hV0 : Measurable (G.indicator fun ω => (d ω).V₀ t))
    (hV : ∀ m, Measurable (G.indicator fun ω => (d ω).V m t))
    (hD : ∀ ω ∈ G, ∀ m, deriv ((d ω).F 0 t) ((d ω).V m t) = (d ω).B1 t m) :
    Measurable (G.indicator fun ω => (d ω).normEll t) := by
  have hpair : ∀ m k, Measurable (G.indicator fun ω =>
      dslope ((d ω).F 0 t) ((d ω).V k t) ((d ω).V m t)) := fun m k =>
    measurable_indicator_dslope hG (hV k) (hV m) (hB0 k) (hB0 m) (hB1 k)
      (fun ω hω => hD ω hω k)
  have hmark : ∀ m, Measurable (G.indicator fun ω =>
      dslope ((d ω).F 0 t) ((d ω).V m t) ((d ω).W t)) := fun m =>
    measurable_indicator_dslope hG (hV m) hW (hB0 m) (hA 0) (hB1 m)
      (fun ω hω => hD ω hω m)
  have hb := Finset.measurable_sum (Finset.univ : Finset (Fin n)) (fun m _ =>
    (((hB1 m).log.const_mul (dualGamma κ (rr m))).add
      ((((hA20.sub (hB0 m)).div (hV0.sub (hV m))).log).const_mul (-(κ / 4) * rr m))))
  have hp := Finset.measurable_sum
    ((Finset.univ : Finset (Fin n × Fin n)).filter fun p => p.1 < p.2)
    (fun p _ => ((hpair p.1 p.2).log).const_mul (dualDelta κ (rr p.1) (rr p.2)))
  have hs := Finset.measurable_sum (Finset.univ : Finset (Fin n))
    (fun m _ => ((hmark m).log).const_mul (rr m))
  have hm := (((((hA21.log.const_mul ((3 * κ - 8) / 16)).sub
    (hL.const_mul (dualLambda κ))).add hb).add hp).add
    (((hA 1).log.const_mul (dualAlpha κ)).sub
      ((((hA 0).sub hA20).div (hW.sub hV0)).log.const_mul (1 / 2)) |>.add hs))
  convert hm.indicator hG using 1
  funext ω
  by_cases hω : ω ∈ G
  · simp only [indicator_of_mem hω, Pi.add_apply, Pi.sub_apply, Pi.div_apply,
      normEll, hdκ ω, hdr ω, pairSum]
  · simp only [indicator_of_notMem hω]

end SeedData

/-- A21's component measurability supplies both alive-event inputs needed
for continuous stopped versions, with no positive-time restriction. -/
theorem measurable_seed_norm_and_gaps
    {𝓕 : Filtration ℝ≥0 mΩ} {n : ℕ} {X : ℝ≥0 → Ω → ℝ}
    {d : Ω → SeedData n} {A : Set ℂ} {φ : ℂ → ℂ} {ζ₀ : ℝ}
    {G : Set Ω} {T : Ω → ℝ}
    (hXm : ∀ u, Measurable[𝓕 u] (X u)) (hXc : ∀ ω, Continuous (X · ω))
    (hdW : ∀ ω, (d ω).W = Ito.rpath (X · ω))
    (hdφ : ∀ ω, (d ω).φ = φ) (hdζ : ∀ ω, (d ω).ζ₀ = ζ₀)
    (q : ℝ≥0) (hG : MeasurableSet[𝓕 q] G)
    (hqT : ∀ ω ∈ G, (q : ℝ) ≤ T ω)
    (h : ∀ ω ∈ G, OwnData (d ω).W A (d ω).φ (T ω) (d ω).a (d ω).W')
    (hv₀ : ∀ ω ∈ G, ∃ v₀ : ℝ → ℂ,
      QuantumZipper.IsForwardSol (d ω).W' (d ω).ζ₀ ((d ω).a (T ω)) v₀)
    (hcl : ∀ ω ∈ G, ∀ m, ∃ ρ > 0,
      Disjoint (ball ((d ω).V m q : ℂ) ρ) (imgHull (d ω).W A q))
    (hVm : ∀ m, Measurable[𝓕 q] (G.indicator fun ω => (d ω).V m q))
    {κ : ℝ} {rr : Fin n → ℝ}
    (hdκ : ∀ ω, (d ω).κ = κ) (hdr : ∀ ω, (d ω).r = rr)
    (hV₀m : Measurable[𝓕 q] (G.indicator fun ω => (d ω).V₀ q))
    (hG₀m : Measurable[𝓕 q] (G.indicator fun ω => (d ω).G₀ q)) :
    (∀ i, Measurable[𝓕 q] (G.indicator fun ω => (d ω).gapVal i q)) ∧
      Measurable[𝓕 q] (G.indicator fun ω => (d ω).normEll q) := by
  obtain ⟨hA, hI0, hD0, hL, hB0, hB1, hW⟩ :=
    measurable_seed_parts hXm hXc hdW hdφ hdζ q hG hqT h hv₀ hcl hVm
  have hA21 : Measurable[𝓕 q] (G.indicator fun ω => (d ω).A21 q) := by
    convert hD0.div hG₀m using 1
    funext ω
    by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω, SeedData.A21, Pi.div_apply]
    · simp only [indicator_of_notMem hω, Pi.div_apply, zero_div]
  refine ⟨SeedData.measurable_indicator_gapVal hG (hA 0) hI0 hA21 hB0 hB1 hW hV₀m hVm,
    SeedData.measurable_indicator_normEll hG hdκ hdr hA hI0 hA21 hL hB0 hB1 hW hV₀m hVm ?_⟩
  intro ω hω m
  obtain ⟨ρ, hρ, hclear⟩ := hcl ω hω m
  have hdiff := ((h ω hω).ownExt_props ⟨q.coe_nonneg, hqT ω hω⟩ hclear).1
  exact (d ω).deriv_F_zero
    (hdiff.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity))))

end InteractingSLE.ZhanGT4
