/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedRowIdHeight

/-!
# The concrete seeded row martingale from the original opposite force law

Packet PROVE-ZHAN-GT4-A22. The row is identified with the actual fused
source density before applying the landed source-record stochastic theorem.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol fwdMap fwdHull)
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Original Brownian/force data, two-view geometry and D9 imply the
actual stopped seeded row's martingale, continuity, boundedness and entrance
one. No row martingale or density-identification premise is used. -/
theorem seedHeightField_row_facts {n : ℕ} {P : Measure Ω} {κ S p s : ℝ} (hκ : 0 < κ)
    (rr : Fin n → ℝ) (W₁ : ℝ → ℝ) (V : Fin n → ℝ → ℝ)
    (W₂ : Ω → ℝ → ℝ) (as Ws bt Wt : Ω → ℝ → ℝ → ℝ)
    (𝓕 : Filtration ℝ≥0 mΩ) (B D : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0)
    (hS : 0 < S) (hT : ∀ ω, 0 < T ω) (hs : s ∈ Icc (0 : ℝ) S)
    (h0 : ∀ ω, W₂ ω 0 = p)
    (hdW : ∀ ω, (fun u => W₂ ω u - W₂ ω 0) = driftDriver (Real.sqrt (16 / κ)) B D ω)
    (h : ∀ ω, TwoViewRect W₁ (W₂ ω) S (T ω) (as ω) (Ws ω) (bt ω) (Wt ω))
    (hq₁ : ∀ ω, ∃ q, IsForwardSol W₁ ((W₂ ω 0 : ℝ) : ℂ) S q)
    (hW₂ : ∀ ω, Continuous (W₂ ω))
    (hq₂ : ∀ ω, ∃ q, IsForwardSol (W₂ ω) (0 : ℂ) (T ω) q)
    (hV : ∀ m, V m 0 = 0)
    (hclear : ∀ ω m, ∃ ρ > (0 : ℝ), ∀ v ∈ Icc (0 : ℝ) (T ω),
      Disjoint (ball (V m s : ℂ) ρ) (frzChart W₁ s '' fwdHull (W₂ ω) v))
    (hne : ∀ ω v, v ∈ Icc (0 : ℝ) (T ω) →
      ∀ i, (seedSView κ rr W₁ (W₂ ω) (as ω) (Ws ω) V v).gapVal i s ≠ 0)
    (hB : IsFilteredBrownianReal 𝓕 B P) (hDm : ∀ u, Measurable[𝓕 u] (D u))
    (hBc : ∀ ω, Continuous (B · ω)) (hDc : ∀ ω, Continuous (D · ω))
    (hVm : ∀ u : ℝ≥0, Measurable[𝓕 u] fun ω => (frzChart (W₂ ω) u 0).re - p)
    (hStop : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0))
    {rad a₀ γ Γ lam L Tm c₀ C₀ : ℝ} (hr : 0 < rad) (ha : 0 < a₀) (hg : 0 < γ)
    (hc : 0 < c₀) (hC : 0 ≤ C₀) (hL : ScaleOK rad a₀ γ Γ lam Tm L)
    (hTTm : ∀ ω, (T ω : ℝ) ≤ Tm)
    (hd9 : ∀ ω, (seedTView κ rr W₁ (W₂ ω) (bt ω) (Wt ω) V s).D9Const
      (fwdHull (fun u => W₁ u - p) s) (T ω) rad a₀ γ Γ lam)
    (hζ₀ : ∀ m, V m s ≠ W₁ s) (hζ : Function.Injective fun m => V m s)
    (hgap : ∀ ω, ∀ t ∈ Icc (0 : ℝ) (T ω),
      c₀ ≤ |(fwdMap (W₂ ω) t 0).re| ∧ |(fwdMap (W₂ ω) t 0).re| ≤ C₀)
    (hD : ∀ ω, ∀ t ∈ Icc (0 : ℝ) (T ω),
      HasDerivWithinAt (fun u : ℝ => D u.toNNReal ω)
        ((16 / κ) * (-1 / 2 + ∑ m, -(κ / 4) * rr m) /
          (W₂ ω t - (frzChart (W₂ ω) t 0).re)) (Icc (0 : ℝ) (T ω)) t) :
    Martingale (fun (t : ℝ≥0) ω =>
      seedHeightField (fun v ω => seedSView κ rr W₁ (W₂ ω) (as ω) (Ws ω) V v)
        ω s (min (t : ℝ) (T ω))) 𝓕 P ∧
    (∀ ω, Continuous fun t : ℝ≥0 =>
      seedHeightField (fun v ω => seedSView κ rr W₁ (W₂ ω) (as ω) (Ws ω) V v)
        ω s (min (t : ℝ) (T ω))) ∧
    (∃ C : ℝ, ∀ (t : ℝ≥0) ω, |seedHeightField
      (fun v ω => seedSView κ rr W₁ (W₂ ω) (as ω) (Ws ω) V v) ω s (min (t : ℝ) (T ω))| ≤ C) ∧
    ∀ ω, seedHeightField (fun v ω => seedSView κ rr W₁ (W₂ ω) (as ω) (Ws ω) V v) ω s 0 = 1 := by
  let e := fun ω => seedTView κ rr W₁ (W₂ ω) (bt ω) (Wt ω) V s
  have hown : ∀ ω, OwnData (e ω).W (fwdHull (fun u => W₁ u - p) s) (e ω).φ
      (T ω) (e ω).a (e ω).W' := by
    intro ω
    obtain ⟨T', hTT', ho, -⟩ := (h ω).tOwn s hs
    have he := ho.restrict (NNReal.coe_pos.2 (hT ω)) hTT'
    simpa only [e, seedTView, h0 ω] using he
  have hq0 : ∀ ω, ∃ q, IsForwardSol (e ω).W' (e ω).ζ₀ ((e ω).a (T ω)) q := by
    intro ω
    obtain ⟨T', hTT', ho, q, hq⟩ := (h ω).tOwn s hs
    exact ⟨q, isForwardSol_restrict hq (ho.mapsTo_clock ⟨(T ω).coe_nonneg, hTT'⟩).2⟩
  have hqa : ∀ ω m, ∃ q, IsForwardSol (e ω).W' ((e ω).ζ m) ((e ω).a (T ω)) q :=
    fun ω m => ((h ω).seed_mark_factors (κ := κ) (r := rr) hS
      (NNReal.coe_pos.2 (hT ω)) hs (hclear ω) m).1
  have hqS : ∀ ω, ∃ q, IsForwardSol (e ω).W ((-p : ℝ) : ℂ) (T ω) q := by
    intro ω
    obtain ⟨q, hq⟩ := hq₂ ω
    have he := (isForwardSol_sub_const_iff (c := W₂ ω 0) (z := 0)).2 hq
    refine ⟨q, ?_⟩
    simpa only [e, seedTView, zero_sub, h0 ω] using he
  have hsource : ∀ ω u, (e ω).seedAccessSource (-p) u = (frzChart (W₂ ω) u 0).re - p := by
    intro ω u
    simpa only [e, h0 ω] using seedTView_source κ rr W₁ (W₂ ω) (bt ω) (Wt ω) V s u
  have hden : ∀ ω t, (e ω).W t - (e ω).seedAccessSource (-p) t =
      W₂ ω t - (frzChart (W₂ ω) t 0).re := by
    intro ω t
    rw [hsource]
    change (W₂ ω t - W₂ ω 0) - _ = _
    rw [h0 ω]
    ring
  have hf := seedAccess_density_facts (div_pos (by norm_num) hκ) (fun m => -(κ / 4) * rr m)
    𝓕 B D T e (p := -p) hdW (fun _ => rfl) (fun _ => rfl)
    (φ := frzChart (fun u => W₁ u - p) s) (ζ₀ := W₁ s - p) (ζ := fun m => V m s - p)
    (fun ω => by simp only [e, seedTView, h0 ω])
    (fun ω => by simp only [e, seedTView, h0 ω])
    (fun ω => by simp only [e, seedTView, h0 ω]) hB hDm hBc hDc hVm
    (fun ω u _ => (hsource ω u).symm) hStop hr ha hg hc hC hL hTTm hown hd9 hq0 hqa
    (fun ω m he => hζ₀ m (by
      change V m s - W₂ ω 0 = W₁ s - W₂ ω 0 at he
      linarith only [he]))
    (fun ω m k he => hζ (by
      change V m s - W₂ ω 0 = V k s - W₂ ω 0 at he
      linarith only [he])) hqS
    (fun ω t ht => by
      simpa only [e, seedTView, fwdMap_sub_const, h0 ω, ofReal_neg, neg_add_cancel]
        using hgap ω t ht)
    (fun ω t ht => by rw [hden]; exact hD ω t ht)
  have he := seedHeightField_row_eq_density hκ.ne' hS hT h hs hq₁ hW₂ hq₂ hV hclear hne
  simp_rw [h0] at he
  have heq : (fun (t : ℝ≥0) ω => seedHeightField
      (fun v ω => seedSView κ rr W₁ (W₂ ω) (as ω) (Ws ω) V v) ω s (min (t : ℝ) (T ω))) =
      (fun (t : ℝ≥0) ω => (e ω).seedAccessDensity (-p) (T ω) t) := funext fun t => funext (he t)
  refine ⟨heq ▸ hf.1, ?_, ?_, ?_⟩
  · intro ω
    exact (hf.2.1 ω).congr fun t => (he t ω).symm
  · obtain ⟨C, hC⟩ := hf.2.2.1
    exact ⟨C, fun t ω => by rw [he t ω]; exact hC t ω⟩
  · intro ω
    simpa only [NNReal.coe_zero, min_eq_left (T ω).coe_nonneg] using (he 0 ω).trans (hf.2.2.2 ω)

end InteractingSLE.ZhanGT4
