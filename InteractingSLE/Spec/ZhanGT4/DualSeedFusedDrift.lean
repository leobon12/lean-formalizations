/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFusedPiece
import InteractingSLE.Spec.ZhanGT4.DualSeedFusedMeas
import InteractingSLE.Spec.ZhanGT4.DualSeedFieldMart

/-!
# The actual fused opposite field along its force-point driver

Packet PROVE-ZHAN-GT4-A22. Derive the random-field Itô hypotheses from
protected D9 geometry, adapted original coordinates and the one-source
driving equation. No opposite-field regularity or generator is assumed.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol fwdMap)
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Construct the fused opposite field from actual protected source data.
The original marginal carries the single charge `κ * (-1/2 + ∑ r)`.
The field is regular from time zero, since its original source is separated. -/
theorem exists_isDriftLogField_seedAccess {n : ℕ} {κ : ℝ} (hκ : 0 < κ) (rr : Fin n → ℝ)
    (𝓕 : Filtration ℝ≥0 mΩ) (B D : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) (d : Ω → FrzData n)
    {A : Set ℂ} {φ : ℂ → ℂ} {ζ₀ p : ℝ} {ζ : Fin n → ℝ} {V : Ω → ℝ → ℝ}
    (hdW : ∀ ω, (d ω).W = driftDriver (Real.sqrt κ) B D ω)
    (hdκ : ∀ ω, (d ω).κ = κ) (hdr : ∀ ω, (d ω).r = rr) (hdφ : ∀ ω, (d ω).φ = φ)
    (hdζ₀ : ∀ ω, (d ω).ζ₀ = ζ₀) (hdζ : ∀ ω, (d ω).ζ = ζ)
    (hBm : ∀ u, Measurable[𝓕 u] (B u)) (hDm : ∀ u, Measurable[𝓕 u] (D u))
    (hBc : ∀ ω, Continuous (B · ω)) (hDc : ∀ ω, Continuous (D · ω))
    (hVm : ∀ u : ℝ≥0, Measurable[𝓕 u] fun ω => V ω u)
    (hV : ∀ ω, ∀ u ∈ Icc (0 : ℝ) (S ω), V ω u = (d ω).seedAccessSource p u)
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    {r a₀ γ Γ lam L Tm c₀ C₀ : ℝ} (hr : 0 < r) (ha : 0 < a₀) (hg : 0 < γ)
    (hc : 0 < c₀) (hC : 0 ≤ C₀) (hL : ScaleOK r a₀ γ Γ lam Tm L)
    (hST : ∀ ω, (S ω : ℝ) ≤ Tm)
    (h : ∀ ω, OwnData (d ω).W A (d ω).φ (S ω) (d ω).a (d ω).W')
    (hd9 : ∀ ω, (d ω).D9Const A (S ω) r a₀ γ Γ lam)
    (hq₀ : ∀ ω, ∃ q, IsForwardSol (d ω).W' (d ω).ζ₀ ((d ω).a (S ω)) q)
    (hq : ∀ ω m, ∃ q, IsForwardSol (d ω).W' ((d ω).ζ m) ((d ω).a (S ω)) q)
    (hζ₀ : ∀ ω m, (d ω).ζ m ≠ (d ω).ζ₀) (hζ : ∀ ω, Function.Injective (d ω).ζ)
    (hqS : ∀ ω, ∃ q, IsForwardSol (d ω).W (p : ℂ) (S ω) q)
    (hgap : ∀ ω, ∀ t ∈ Icc (0 : ℝ) (S ω),
      c₀ ≤ |(fwdMap (d ω).W t p).re| ∧ |(fwdMap (d ω).W t p).re| ≤ C₀)
    (hD : ∀ ω, ∀ t ∈ Icc (0 : ℝ) (S ω),
      HasDerivWithinAt (fun s : ℝ => D s.toNNReal ω)
        ((d ω).κ * (d ω).seedAccessExponent / ((d ω).W t - (d ω).seedAccessSource p t))
        (Icc (0 : ℝ) (S ω)) t) :
    ∃ ρ K : ℝ, 0 < ρ ∧ IsDriftLogField 𝓕 (Real.sqrt κ) ρ K B D
      (fun ω t => (d ω).κ * (d ω).seedAccessExponent / ((d ω).W t - (d ω).seedAccessSource p t)) 0 S
      (fun ω => (d ω).seedAccessEll p) (fun ω => (d ω).seedAccessX p)
      (fun ω => (d ω).seedAccessXX p) (fun ω => (d ω).seedAccessXXX p) (fun ω => (d ω).seedAccessT p) := by
  obtain ⟨ρ, K, hρ, hK, hpiece⟩ := exists_seedAccess_piece_constants κ rr hr ha hg hc hC hL
  let Cb := |κ * (-1 / 2 + ∑ m, rr m)| / c₀
  have hCb : 0 ≤ Cb := by dsimp only [Cb]; positivity
  have hK' : K ≤ K + Cb := le_add_of_nonneg_right hCb
  have hfacts (ω : Ω) := tube_of_isLogField (ℓ := (d ω).seedAccessEll p)
    (ℓx := (d ω).seedAccessX p) (ℓxx := (d ω).seedAccessXX p)
    (ℓxxx := (d ω).seedAccessXXX p) (ℓt := (d ω).seedAccessT p)
    (W := (d ω).W) (ε := 0) (S := (S ω : ℝ)) (ρ := ρ) (K := K) (R₀ := 3 * ρ)
    le_rfl (fun t ht => ?_)
  · have hm (t : ℝ≥0) :
        Measurable[𝓕 t] ({ω | t ≤ S ω}.indicator fun ω => (d ω).seedAccessEll p t ((d ω).W t)) ∧
        Measurable[𝓕 t] ({ω | t ≤ S ω}.indicator fun ω => (d ω).seedAccessX p t ((d ω).W t)) ∧
        Measurable[𝓕 t] ({ω | t ≤ S ω}.indicator fun ω => (d ω).seedAccessXX p t ((d ω).W t)) := by
      let X : ℝ≥0 → Ω → ℝ := fun u ω => Real.sqrt κ * B u ω + D u ω
      have hXm : ∀ u, Measurable[𝓕 u] (X u) := fun u => ((hBm u).const_mul _).add (hDm u)
      have hXc : ∀ ω, Continuous (X · ω) := fun ω => (continuous_const.mul (hBc ω)).add (hDc ω)
      have hWX : ∀ ω, (d ω).W = Ito.rpath (X · ω) := fun ω => by rw [hdW ω]; rfl
      have hGt := measurableSet_ge_of_isStoppingTime hS t
      have hFM : ∀ u ∈ Icc (0 : ℝ) t,
          @FrzMeas Ω (𝓕 t) (fun ω => (d ω).W) (fun ω => (d ω).W') (fun ω => (d ω).a)
            A φ (fun ω => (S ω : ℝ)) {ω | t ≤ S ω} u := by
        intro u hu
        exact frzMeas_of_adaptedX hXm hXc hWX hGt
          (fun ω _ => by rw [← hdφ ω]; exact h ω) hu
          (fun ω hω => ⟨hu.1, hu.2.trans (NNReal.coe_le_coe.2 hω)⟩)
      have hVmeas : ∀ u ∈ Icc (0 : ℝ) t,
          Measurable[𝓕 t] ({ω | t ≤ S ω}.indicator fun ω => V ω u) := by
        intro u hu
        have hh := ((hVm u.toNNReal).mono (𝓕.mono (Real.toNNReal_le_iff_le_coe.2 hu.2)) le_rfl).indicator hGt
        simpa only [Real.coe_toNNReal u hu.1] using hh
      exact @measurable_seedAccess_log_jet Ω (𝓕 t) n d A φ (fun ω => (S ω : ℝ)) {ω | t ≤ S ω}
        t κ ζ₀ p rr ζ V hdφ hdκ hdr hdζ₀ hdζ t.coe_nonneg hFM
        (fun ω _ => by rw [← hdζ₀ ω]; exact hq₀ ω)
        (fun m ω _ => by rw [← hdζ ω]; exact hq ω m)
        (fun ω _ => hqS ω)
        (fun ω hω u hu => hV ω u ⟨hu.1, hu.2.trans (NNReal.coe_le_coe.2 hω)⟩) hVmeas
    have he4 : 4 * (3 * ρ / 4) = 3 * ρ := by ring
    have htube (ω : Ω) : driftTube (Real.sqrt κ) B D 0 (S ω) (4 * (3 * ρ / 4)) ω =
        {z : ℝ × ℝ | z.1 ∈ Icc (0 : ℝ) (S ω) ∧ |z.2 - (d ω).W z.1| < 3 * ρ} := by
      rw [he4, hdW ω]; rfl
    refine ⟨3 * ρ / 4, K + Cb, by positivity, ?_⟩
    refine ⟨fun _ => bot_le, add_nonneg hK hCb, hD, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ω
      have hsource : ContinuousOn ((d ω).seedAccessSource p) (Icc (0 : ℝ) (S ω)) := fun t ht =>
        ((source_gmap_rates (h ω).cont (hqS ω).choose_spec ht).1).continuousWithinAt
      apply continuousOn_const.div ((h ω).cont.continuousOn.sub hsource)
      intro t ht
      apply SeedData.ne_zero_of_le_abs hc
      simpa only [Pi.sub_apply, FrzData.seedAccessSource, sub_add_eq_sub_sub_swap, sub_self, zero_sub, abs_neg]
        using (hgap ω t ht).1
    · intro ω t ht
      have he : |(d ω).W t - (d ω).seedAccessSource p t| = |(fwdMap (d ω).W t p).re| := by
        simp only [FrzData.seedAccessSource, sub_add_eq_sub_sub_swap, sub_self, zero_sub, abs_neg]
      have hb : |(d ω).κ * (d ω).seedAccessExponent /
          ((d ω).W t - (d ω).seedAccessSource p t)| ≤ Cb := by
        rw [abs_div, he, hdκ ω, FrzData.seedAccessExponent, hdr ω]
        exact div_le_div_of_nonneg_left (abs_nonneg _) hc (hgap ω t ht).1
      exact hb.trans (le_add_of_nonneg_left hK)
    · intro ω z hz; simp only [NNReal.coe_zero, htube ω] at hz; exact ((hfacts ω).1 z hz).1
    · intro ω z hz; simp only [NNReal.coe_zero, htube ω] at hz; exact ((hfacts ω).1 z hz).2.1
    · intro ω z hz; simp only [NNReal.coe_zero, htube ω] at hz; exact ((hfacts ω).1 z hz).2.2.1
    · intro ω z hz; simp only [NNReal.coe_zero, htube ω] at hz; exact ((hfacts ω).1 z hz).2.2.2.1
    · intro ω; simp only [NNReal.coe_zero, htube ω]; exact (hfacts ω).2.1
    · intro ω; simp only [NNReal.coe_zero, htube ω]; exact (hfacts ω).2.2.1
    · intro ω; simp only [NNReal.coe_zero, htube ω]; exact (hfacts ω).2.2.2.1
    · intro ω; simp only [NNReal.coe_zero, htube ω]; exact (hfacts ω).2.2.2.2
    · intro ω z hz
      simp only [NNReal.coe_zero, htube ω] at hz
      obtain ⟨b0, b1, b2, b3, bt⟩ := ((hfacts ω).1 z hz).2.2.2.2
      exact ⟨b0.trans hK', b1.trans hK', b2.trans hK', b3.trans hK', bt.trans hK'⟩
    · intro ω t ht
      have hh := (d ω).seedAccess_gen_eq_zero (h ω) (by rw [hdκ ω]; exact hκ.ne')
        (hq₀ ω).choose_spec (fun m => (hq ω m).choose_spec) (hζ₀ ω) (hζ ω) (hqS ω).choose_spec ht
      rw [hdW ω, hdκ ω] at hh
      rw [Real.sq_sqrt hκ.le, hdκ ω, hdW ω]
      exact hh
    · intro t _; simpa only [← hdW] using (hm t).1
    · intro t _; simpa only [← hdW] using (hm t).2.1
    · intro t _; simpa only [← hdW] using (hm t).2.2
  · obtain ⟨δ, hδ, hδW⟩ := Metric.continuous_iff.1 (h ω).cont t ρ hρ
    refine ⟨max 0 (t - δ / 2), min (S ω) (t + δ / 2), box_mem_nhdsWithin_Icc (by positivity),
      ⟨max_le ht.1 (by linarith), le_min ht.2 (by linarith)⟩, ?_⟩
    have hJ : Icc (max 0 (t - δ / 2)) (min (S ω : ℝ) (t + δ / 2)) ⊆ Icc 0 (S ω) := fun u hu =>
      ⟨(le_max_left _ _).trans hu.1, hu.2.trans (min_le_left _ _)⟩
    refine hpiece (d ω) (hdκ ω) (hdr ω) (hST ω) (h ω) (hd9 ω) (hq₀ ω) (hq ω)
      (hζ₀ ω) (hζ ω) (hqS ω) (hgap ω) hJ fun u hu => ?_
    have h1 := (le_max_right (0 : ℝ) (t - δ / 2)).trans hu.1
    have h2 := hu.2.trans (min_le_right (S ω : ℝ) (t + δ / 2))
    have hh := hδW u (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith only [h1, h2, hδ])
    rwa [Real.dist_eq] at hh

end InteractingSLE.ZhanGT4
