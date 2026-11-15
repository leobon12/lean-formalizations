/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualTwoDirEncl

/-!
# The second time direction: A14's column martingale with curve `1` frozen, and its density

Packet PROVE-ZHAN-GT4-A15. Source: Astra, *Follow-up proofs*, §A.1.4 (`source/external/AstraIG1/ig1_followup_proofs.txt`
L357–L407, R38): "Reflection of the construction proves the corresponding martingale in the other coordinate."

* A14's random selections are the canonical deterministic ones: `frzWidth = stairH` and `frzImgSel = imgSelD` once the
  height cap `t̄` exceeds every height (`coe_frzWidth_eq_stairH`, `frzImgSel_eq_imgSelD`), so A14's density is `exp` of
  the canonical `s`-view `ℓ` (`frzDens_eq_exp_sEll`).
-/

set_option autoImplicit false

noncomputable section

open Finset Set MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull drive)

section Select

variable {Ω : Type*} {ι : Type*} [Fintype ι] {n : ℕ}

/-- **A14's staircase width is the staircase height function of the transposed staircase** once the height cap
exceeds every height. -/
theorem coe_frzWidth_eq_stairH {S₁ : ι → Ω → ℝ≥0} {S₂ : ι → ℝ} {tb : ℝ} (htb : ∀ i, S₂ i ≤ tb) (y : ℝ) (ω : Ω) :
    ((frzWidth S₁ S₂ tb y ω : ℝ≥0) : ℝ) = stairH S₂ (fun i => (S₁ i ω : ℝ)) y := by
  have hfilt : (univ.filter fun i => y ≤ min (S₂ i) tb) = univ.filter fun i => y ≤ S₂ i := by
    congr 1; funext i; rw [min_eq_left (htb i)]
  unfold frzWidth stairH
  rw [hfilt]
  apply le_antisymm
  · have h0 : 0 ≤ (insert 0 ((univ.filter fun i => y ≤ S₂ i).image fun i => (S₁ i ω : ℝ))).max'
        (insert_nonempty _ _) := le_max' _ _ (mem_insert_self _ _)
    rw [← NNReal.coe_mk _ h0, NNReal.coe_le_coe]
    refine Finset.sup_le fun i hi => ?_
    rw [← NNReal.coe_le_coe, NNReal.coe_mk]
    exact le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem (fun i => (S₁ i ω : ℝ)) hi))
  · refine max'_le _ _ _ fun x hx => ?_
    rcases mem_insert.1 hx with rfl | hx
    · exact NNReal.coe_nonneg _
    · obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
      exact NNReal.coe_le_coe.2 (Finset.le_sup (f := fun i => S₁ i ω) hi)

/-- **A14's random image data are the canonical ones.** -/
theorem frzImgSel_eq_imgSelD {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {W₂ : ℝ → ℝ} {S₁ : ι → Ω → ℝ≥0} {S₂ : ι → ℝ} {tb : ℝ}
    (htb : ∀ i, S₂ i ≤ tb) (y : ℝ) (ω : Ω) :
    frzImgSel κ B W₂ S₁ S₂ tb y ω = imgSelD (drive κ B ω) W₂ (stairH S₂ (fun i => (S₁ i ω : ℝ)) y) y := by
  have e1 : frzImgSel κ B W₂ S₁ S₂ tb y ω = imgSelD (drive κ B ω) W₂ (frzWidth S₁ S₂ tb y ω : ℝ) y := rfl
  rw [e1, coe_frzWidth_eq_stairH htb y ω]

/-- **A14's density is `exp` of the canonical `s`-view `ℓ`** (height cap above every height). -/
theorem frzDens_eq_exp_sEll {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {W₂ : ℝ → ℝ} {S₁ : ι → Ω → ℝ≥0} {S₂ : ι → ℝ} {tb : ℝ}
    (htb : ∀ i, S₂ i ≤ tb) (rr p : Fin n → ℝ) (ω : Ω) (x y : ℝ) :
    frzDens κ B W₂ S₁ S₂ tb rr p ω x y =
      Real.exp (sEll κ rr (drive κ B ω) W₂ (sSelA (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂)
        (sSelW (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂) p x y) := by
  unfold frzDens
  rw [frzN_eq_sView]
  simp only [sEll, frzImgSel_eq_imgSelD htb]
  rfl

end Select

/-! ### The `t`-direction column martingale (curve `1` frozen) -/

section TDir

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} {n : ℕ} {ι : Type*}
  [Fintype ι]

/-- **The second time direction** (§A.1.4, "Reflection of the construction proves the corresponding martingale in
the other coordinate"): curve `2` is `√(16/κ) B + x₂` (`B` a Brownian motion of `𝓕` under `P`) with exit times `S₂ i`
from its enclosures `H₂ i`; curve `1` is a frozen continuous path `W₁` from `0` staying in `H₁ i` up to the heights
`S₁ i`. In coordinates translated by `−x₂`, A14's column product of the `t`-view density (dual parameter `16/κ`, dual
charges `−(κ/4) r_m`, marks `p_m − x₂`) is a bounded right-continuous martingale, with a bound `K` that depends only on
the enclosure data (not on the frozen path). This is A14's `martingale_colProd_frozen_left` for the translated
configuration. -/
theorem martingale_colProd_tView {κ : ℝ} (hκ : 0 < κ) {B : ℝ≥0 → Ω → ℝ} (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) {H₁ H₂ : ι → Set ℂ} (hH₁ : ∀ i, IsHPHull (H₁ i))
    (hH₂ : ∀ i, IsHPHull (H₂ i)) {δ : ι → ℝ} (hδ : ∀ i, 0 < δ i)
    (hsep : ∀ i, ∀ a ∈ H₂ i, ∀ z ∈ H₁ i, 2 * δ i ≤ ‖a - z‖) {q d : ι → ℝ} (hd : ∀ i, 0 < d i)
    (hq : ∀ i, 0 < q i) (hqH : ∀ i, Disjoint (Metric.ball (q i : ℂ) (2 * d i)) (H₁ i ∪ H₂ i)) {p : Fin n → ℝ}
    (hpH : ∀ i m, Disjoint (Metric.ball (p m : ℂ) (2 * d i)) (H₁ i ∪ H₂ i)) (hpinj : Function.Injective p)
    (Tm : ℝ) (rr : Fin n → ℝ) {x₂ : ℝ} (hqx : ∀ i, q i < x₂) :
    ∃ K : ℝ, ∀ {S₂ : ι → Ω → ℝ≥0}, (∀ i, IsStoppingTime 𝓕 fun ω => (S₂ i ω : WithTop ℝ≥0)) →
      (∀ i ω, 0 < S₂ i ω) → (∀ i ω, (S₂ i ω : ℝ) ≤ Tm) →
      (∀ i ω, fwdHull (fun u => drive (16 / κ) B ω u + x₂) (S₂ i ω) ⊆ H₂ i) →
      ∀ {W₁ : ℝ → ℝ}, Continuous W₁ → W₁ 0 = 0 →
      ∀ {S₁ : ι → ℝ}, (∀ i, 0 < S₁ i) → (∀ i, S₁ i ≤ Tm) → (∀ i, fwdHull W₁ (S₁ i) ⊆ H₁ i) →
      ∀ {tb : ℝ}, 0 < tb →
        Martingale (colProd (frzDens (16 / κ) B (fun u => W₁ u - x₂) S₂ S₁ tb (fun m => -(κ / 4) * rr m)
          (fun m => p m - x₂)) S₂ S₁ tb) 𝓕 P ∧
        (∀ ω t, ContinuousWithinAt (colProd (frzDens (16 / κ) B (fun u => W₁ u - x₂) S₂ S₁ tb
          (fun m => -(κ / 4) * rr m) (fun m => p m - x₂)) S₂ S₁ tb · ω) (Ici t) t) ∧
        ∀ s ω, |colProd (frzDens (16 / κ) B (fun u => W₁ u - x₂) S₂ S₁ tb (fun m => -(κ / 4) * rr m)
          (fun m => p m - x₂)) S₂ S₁ tb s ω| ≤ K := by
  -- the translated enclosures: curve `2` grows in `G`, curve `1` is frozen in `F`
  set G : ι → Set ℂ := fun j => transl (-x₂) (H₂ j) with hG
  set F : ι → Set ℂ := fun j => transl (-x₂) (H₁ j) with hF
  have hsep' : ∀ j, ∀ a ∈ F j, ∀ z ∈ G j, 2 * δ j ≤ ‖a - z‖ := fun j =>
    sep_transl (fun a ha z hz => by rw [norm_sub_rev]; exact hsep j z hz a ha) (-x₂)
  have hunion : ∀ j, transl (-x₂) (H₁ j ∪ H₂ j) = G j ∪ F j := fun j => by
    simp only [hG, hF, transl, Set.image_union, Set.union_comm]
  have hpH' : ∀ j m, Disjoint (Metric.ball (((fun m => p m - x₂) m : ℝ) : ℂ) (2 * d j)) (G j ∪ F j) :=
    fun j m => by
      have := disjoint_ball_transl (hpH j m) (-x₂)
      rw [hunion j] at this
      simpa [sub_eq_add_neg] using this
  have hqH' : ∀ j, Disjoint (Metric.ball (((fun j => q j - x₂) j : ℝ) : ℂ) (2 * d j)) (G j ∪ F j) := fun j => by
    have := disjoint_ball_transl (hqH j) (-x₂)
    rw [hunion j] at this
    simpa [sub_eq_add_neg] using this
  have hpinj' : Function.Injective (fun m => p m - x₂) := fun m k hmk => hpinj (by simpa using hmk)
  have hκ' : 0 < 16 / κ := by positivity
  obtain ⟨K, hK⟩ := martingale_colProd_frozen_left (𝓕 := 𝓕) (P := P) hκ' hB hBc hB0
    (fun j => isHPHull_transl (hH₂ j) (-x₂)) (fun j => isHPHull_transl (hH₁ j) (-x₂)) hδ hsep' hd
    (fun j => by show q j - x₂ < 0; linarith [hqx j]) hqH' hpH' hpinj' Tm (fun m => -(κ / 4) * rr m)
  refine ⟨K, fun {S₂} hS₂ hS₂0 hS₂m hK₂ {W₁} hW₁ hW₁0 {S₁} hS₁0 hS₁m hK₁ {tb} htb => ?_⟩
  have hU : Continuous fun u => W₁ u - x₂ := hW₁.sub continuous_const
  have hK₂' : ∀ i ω, fwdHull (drive (16 / κ) B ω) (S₂ i ω) ⊆ G i := fun i ω => by
    intro z hz
    have h1 : z + (x₂ : ℂ) ∈ fwdHull (fun u => drive (16 / κ) B ω u + x₂) (S₂ i ω) := by
      rw [ConformalImageFull.fwdHull_add_const]; exact ⟨z, hz, rfl⟩
    rw [hG, mem_transl_iff]
    simpa using hK₂ i ω h1
  have hstart : ∀ i, (((fun u => W₁ u - x₂) 0 : ℝ) : ℂ) ∈ closure (F i) := fun i => by
    have h0 := start_mem_closure_fwdHull hW₁ (hS₁0 i)
    rw [hW₁0] at h0
    have := mem_closure_transl (closure_mono (hK₁ i) h0) (-x₂)
    simpa [hW₁0] using this
  exact hK hS₂ hS₂0 hS₂m hK₂' hU hstart (fun i => by simp only [hW₁0]; linarith [hq i]) hS₁0 hS₁m
    (fun i => fwdHull_sub_const_subset (hK₁ i)) htb

end TDir

/-! ### The `t`-direction density is the canonical `t`-view `ℓ` -/

/-- **The `t`-view `ℓ` of the pair `(W₁, V + x₂)` is the `s`-view `ℓ` of the translated pair `(V, W₁ − x₂)` with the
roles exchanged** (dual parameter, dual charges, translated marks), when `V 0 = 0`. -/
theorem tEll_eq_sEll {n : ℕ} {ι : Type*} [Fintype ι] (κ : ℝ) (r p : Fin n → ℝ) (W₁ V : ℝ → ℝ) (hV0 : V 0 = 0)
    (x₂ : ℝ) (S₁ S₂ : ι → ℝ) (x y : ℝ) :
    tEll κ r W₁ (fun u => V u + x₂) (tSelA W₁ (fun u => V u + x₂) S₁ S₂) (tSelW W₁ (fun u => V u + x₂) S₁ S₂) p x y =
      sEll (16 / κ) (fun m => -(κ / 4) * r m) V (fun u => W₁ u - x₂) (sSelA V (fun u => W₁ u - x₂) S₂ S₁)
        (sSelW V (fun u => W₁ u - x₂) S₂ S₁) (fun m => p m - x₂) y x := by
  have e1 : (fun s => V s + x₂ - (V 0 + x₂)) = V := by funext s; rw [hV0]; ring
  have e2 : (fun s => W₁ s - (V 0 + x₂)) = fun s => W₁ s - x₂ := by funext s; rw [hV0, zero_add]
  have e3 : (fun m => p m - (V 0 + x₂)) = fun m => p m - x₂ := by funext m; rw [hV0, zero_add]
  have e4 : V y + x₂ - (V 0 + x₂) = V y := by rw [hV0]; ring
  have e5 : W₁ x - (V 0 + x₂) = W₁ x - x₂ := by rw [hV0, zero_add]
  simp only [tEll, sEll, tView, sView, tSelA, tSelW, sSelA, sSelW, e1, e2, e3, e4, e5]

section TDens

variable {Ω : Type*} {n : ℕ} {ι : Type*} [Fintype ι]

/-- **The `t`-direction density of `martingale_colProd_tView` is `exp` of the canonical `t`-view `ℓ`** of the pair
(curve `1` = `W₁`, curve `2` = `√(16/κ) B + x₂`), at (curve-`2` time `y`, curve-`1` height `x`). -/
theorem frzDens_tView_eq_exp_tEll {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} (hB0 : ∀ ω, B 0 ω = 0) {W₁ : ℝ → ℝ} {x₂ : ℝ}
    {S₂ : ι → Ω → ℝ≥0} {S₁ : ι → ℝ} {tb : ℝ} (htb : ∀ i, S₁ i ≤ tb) (rr p : Fin n → ℝ) (ω : Ω) (y x : ℝ) :
    frzDens (16 / κ) B (fun u => W₁ u - x₂) S₂ S₁ tb (fun m => -(κ / 4) * rr m) (fun m => p m - x₂) ω y x =
      Real.exp (tEll κ rr W₁ (fun u => drive (16 / κ) B ω u + x₂)
        (tSelA W₁ (fun u => drive (16 / κ) B ω u + x₂) S₁ (fun i => (S₂ i ω : ℝ)))
        (tSelW W₁ (fun u => drive (16 / κ) B ω u + x₂) S₁ (fun i => (S₂ i ω : ℝ))) p x y) := by
  rw [frzDens_eq_exp_sEll htb, tEll_eq_sEll κ rr p W₁ _ (QuantumZipper.drive_zero (hB0 ω))]

end TDens

/-! ### The inner integral over curve `2`: the `s`-view patch times the `t`-marginal has mean one -/

section Inner

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} {n : ℕ} {ι : Type*}
  [Fintype ι]

/-- The normalised factor of a positive density: `N(x, y) N(0, 0)/(N(x, 0) N(0, y)) = exp(normLog (log N))`. -/
theorem normFactor_exp (L : ℝ → ℝ → ℝ) (x y : ℝ) :
    Real.exp (L x y) * Real.exp (L 0 0) / (Real.exp (L x 0) * Real.exp (L 0 y)) = Real.exp (normLog L x y) := by
  unfold normLog
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_sub]
  congr 1; ring

/-- **The `t`-direction mean (D12)–(D11), curve `1` frozen**: for every frozen continuous path `W₁` of curve `1` (from
`0`, in `H₁ i` up to the heights `S₁ i`) and curve `2` = `√(16/κ) B + x₂` with its exit times `S₂ i`,
`E[M*_s(T, T) · Ñ_t(maxS₂, 0)/Ñ_t(0, 0)] = 1`, where `M*_s` is the (D11) patch of the **`s`-view** normalised density of
the pair `(W₁, curve 2)` and the second factor is the `t`-view density at curve-`1` height `0` (the marginal factor of
curve `2`). This is the curve-`2` integral of the patched coupling density with the curve-`1` path fixed (Fubini's
inner integral). -/
theorem integral_patch_mul_tMarg_eq_one {κ : ℝ} (hκ : 0 < κ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {H₁ H₂ : ι → Set ℂ} (hH₁ : ∀ i, IsHPHull (H₁ i)) (hH₂ : ∀ i, IsHPHull (H₂ i)) {δ : ι → ℝ} (hδ : ∀ i, 0 < δ i)
    (hsep : ∀ i, ∀ a ∈ H₂ i, ∀ z ∈ H₁ i, 2 * δ i ≤ ‖a - z‖) {q d : ι → ℝ} (hd : ∀ i, 0 < d i)
    (hq : ∀ i, 0 < q i) (hqH : ∀ i, Disjoint (Metric.ball (q i : ℂ) (2 * d i)) (H₁ i ∪ H₂ i)) {p : Fin n → ℝ}
    (hpH : ∀ i m, Disjoint (Metric.ball (p m : ℂ) (2 * d i)) (H₁ i ∪ H₂ i)) (hpinj : Function.Injective p)
    {Tm : ℝ} (hTm : 0 < Tm) (rr : Fin n → ℝ) {x₂ : ℝ} (hx₂ : ∀ i, ((x₂ : ℝ) : ℂ) ∈ closure (H₂ i))
    (hqx : ∀ i, q i < x₂)
    {S₂ : ι → Ω → ℝ≥0} (hS₂ : ∀ i, IsStoppingTime 𝓕 fun ω => (S₂ i ω : WithTop ℝ≥0)) (hS₂0 : ∀ i ω, 0 < S₂ i ω)
    (hS₂m : ∀ i ω, (S₂ i ω : ℝ) ≤ Tm) (hK₂ : ∀ i ω, fwdHull (fun u => drive (16 / κ) B ω u + x₂) (S₂ i ω) ⊆ H₂ i)
    {W₁ : ℝ → ℝ} (hW₁ : Continuous W₁) (hW₁0 : W₁ 0 = 0) {S₁ : ι → ℝ} (hS₁0 : ∀ i, 0 < S₁ i)
    (hS₁m : ∀ i, S₁ i ≤ Tm) (hK₁ : ∀ i, fwdHull W₁ (S₁ i) ⊆ H₁ i) :
    ∫ ω, patch S₁ (fun i => (S₂ i ω : ℝ))
        (fun x y => Real.exp (normLog (sEll κ rr W₁ (fun u => drive (16 / κ) B ω u + x₂)
          (sSelA W₁ (fun u => drive (16 / κ) B ω u + x₂) S₁ (fun i => (S₂ i ω : ℝ)))
          (sSelW W₁ (fun u => drive (16 / κ) B ω u + x₂) S₁ (fun i => (S₂ i ω : ℝ))) p) x y)) Tm Tm *
      Real.exp (tEll κ rr W₁ (fun u => drive (16 / κ) B ω u + x₂)
          (tSelA W₁ (fun u => drive (16 / κ) B ω u + x₂) S₁ (fun i => (S₂ i ω : ℝ)))
          (tSelW W₁ (fun u => drive (16 / κ) B ω u + x₂) S₁ (fun i => (S₂ i ω : ℝ))) p 0
          (min (maxIn (stairCols fun i => (S₂ i ω : ℝ))) Tm) -
        tEll κ rr W₁ (fun u => drive (16 / κ) B ω u + x₂)
          (tSelA W₁ (fun u => drive (16 / κ) B ω u + x₂) S₁ (fun i => (S₂ i ω : ℝ)))
          (tSelW W₁ (fun u => drive (16 / κ) B ω u + x₂) S₁ (fun i => (S₂ i ω : ℝ))) p 0 0) ∂P = 1 := by
  obtain ⟨K, hK⟩ := martingale_colProd_tView (𝓕 := 𝓕) (P := P) hκ hB hBc hB0 hH₁ hH₂ hδ hsep hd hq hqH hpH hpinj
    Tm rr hqx
  obtain ⟨hM, -, -⟩ := hK hS₂ hS₂0 hS₂m hK₂ hW₁ hW₁0 hS₁0 hS₁m hK₁ hTm
  have hP : IsProbabilityMeasure P := hB.isProbabilityMeasure'
  set N := frzDens (16 / κ) B (fun u => W₁ u - x₂) S₂ S₁ Tm (fun m => -(κ / 4) * rr m) (fun m => p m - x₂) with hNdef
  have hN : ∀ ω x y, 0 < N ω x y := fun ω x y => Real.exp_pos _
  set s₀ : ℝ≥0 := Tm.toNNReal with hs₀
  have hs₀R : (s₀ : ℝ) = Tm := Real.coe_toNNReal _ hTm.le
  have hS₂s : ∀ i ω, S₂ i ω ≤ s₀ := fun i ω => by
    rw [← NNReal.coe_le_coe, hs₀R]; exact hS₂m i ω
  have h1 := (integral_colProd_eq_one hN hM).2 s₀ hS₂s
  rw [← h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only
  set W₂ : ℝ → ℝ := fun u => drive (16 / κ) B ω u + x₂ with hW₂
  have hW₂0 : W₂ 0 = x₂ := by simp [hW₂, QuantumZipper.drive_zero (hB0 ω)]
  -- the enclosure data of the pair `(W₁, W₂)`
  have hE : TwoEncl W₁ W₂ S₁ (fun i => (S₂ i ω : ℝ)) H₁ H₂ δ q d p Tm :=
    { cont₁ := hW₁, cont₂ := (QuantumZipper.drive_continuous (hBc ω)).add continuous_const, zero₁ := hW₁0,
      hull₁ := hH₁, hull₂ := hH₂, δpos := hδ, sep := hsep, dpos := hd, qpos := hq, qH := hqH, pH := hpH,
      pinj := hpinj, start₂ := fun i => by rw [hW₂0]; exact hx₂ i, qW := fun i => by rw [hW₂0]; exact hqx i,
      S₁pos := hS₁0, S₂pos := fun i => hS₂0 i ω, S₁le := hS₁m, S₂le := fun i => hS₂m i ω, K₁ := hK₁,
      K₂ := fun i => hK₂ i ω }
  -- the column product is the transposed patch times the marginal factor
  have hcol := colProd_eq_colProdT N S₁ Tm (hS₂s · ω)
  rw [← hcol]
  have hpm := patch_mul_marginal (S₁ := fun i => (S₂ i ω : ℝ)) (S₂ := S₁) (fun i => (S₂ i ω).coe_nonneg)
    (N := N ω) (hN ω) s₀.coe_nonneg Tm
  have hcolP : colProd N S₂ S₁ Tm s₀ ω = ∏ c ∈ stairCols (fun i => (S₂ i ω : ℝ)),
      (N ω (min c s₀) (min (stairH (fun i => (S₂ i ω : ℝ)) S₁ c) Tm) /
        N ω (min (prevIn (stairCols fun i => (S₂ i ω : ℝ)) c) s₀)
          (min (stairH (fun i => (S₂ i ω : ℝ)) S₁ c) Tm)) := rfl
  rw [hcolP, ← hpm]
  -- identify the density
  have hNe : ∀ y x, N ω y x = Real.exp (tEll κ rr W₁ W₂ (tSelA W₁ W₂ S₁ (fun i => (S₂ i ω : ℝ)))
      (tSelW W₁ W₂ S₁ (fun i => (S₂ i ω : ℝ))) p x y) := fun y x =>
    frzDens_tView_eq_exp_tEll hB0 hS₁m rr p ω y x
  simp only [hNe, normFactor_exp (fun y x => tEll κ rr W₁ W₂ (tSelA W₁ W₂ S₁ (fun i => (S₂ i ω : ℝ)))
      (tSelW W₁ W₂ S₁ (fun i => (S₂ i ω : ℝ))) p x y)]
  have hsym : ∀ x y, normLog (fun y x => tEll κ rr W₁ W₂ (tSelA W₁ W₂ S₁ (fun i => (S₂ i ω : ℝ)))
      (tSelW W₁ W₂ S₁ (fun i => (S₂ i ω : ℝ))) p x y) y x =
      normLog (tEll κ rr W₁ W₂ (tSelA W₁ W₂ S₁ (fun i => (S₂ i ω : ℝ)))
        (tSelW W₁ W₂ S₁ (fun i => (S₂ i ω : ℝ))) p) x y := fun x y => by
    unfold normLog; ring
  simp only [hsym]
  rw [← patch_twoView (fun i => (hS₁0 i).le) (fun i => (S₂ i ω).coe_nonneg) hκ.ne' hE.cont₁ hE.cont₂
    hE.twoViewRect hE.twoViewMarks hTm.le s₀.coe_nonneg, hs₀R, ← Real.exp_sub]

end Inner

end InteractingSLE.ZhanGT4
