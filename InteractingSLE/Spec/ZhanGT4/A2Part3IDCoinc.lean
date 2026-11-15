/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2Part3IDMain
import InteractingSLE.Spec.Sec2.Assembly3Path

/-!
# A.2 part 3, (I1): image words with coincident marks

Packet PROVE-ZHAN-A2P3-ID. (I1) is stated for every image word whose nearest mark is left of the source; its marks
may coincide (a null event in the application, but allowed by the statement). Coincident marks of an integrated
`SLE_κ(ρ)` path stay coincident; the path is then a *split* of a path of the merged, strictly ordered word. This file
provides the reindexing tools:

* `idProp_of_paths`: `IdProp` depends only on the driver, the nearest mark and the target;
* **`IsIntegratedSLEPath.splitAlong`**, `IsIntegratedSLEEvolution.splitAlong`: an integrated path of a word `x̃`
  (weights `ρ̃`) read along a monotone surjection `π` is an integrated path of `x̃ ∘ π` with any weights `ρ` whose
  fibre sums are `ρ̃` (the driving drift and the threshold sums are fibrewise sums);
* **`IsIntegratedSLEPath.dropHead`**, `IsIntegratedSLEEvolution.dropHead`: a leading left mark of weight `0` can be
  dropped (it changes no drift and no threshold sum; at a finite lifetime it has a left limit, being decreasing in time
  and bounded below by the next mark);
* `law_of_ae_idProp`, `HasIdPropEvolution`, `law_of_hasIdPropEvolution`: one evolution with `IdProp` almost surely
  gives the full canonical law; `HasIdPropEvolution.split` transfers it from a merged word;
* `hasIdPropEvolution_of_word` (the core of `law_idSet_G3` for a general strictly ordered left word whose target is
  behind the nearest mark) and `hasIdPropEvolution_phantom2`, `hasIdPropEvolution_phantom1` (the target is the
  nearest mark: an auxiliary weight-zero mark in front, `ae_newHorizon_top_weak`, then `dropHead`);
* the coincidence patterns `hasIdPropEvolution_{G3,Eight}_c…` of the two image words.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A2P3ID

open Sec2.Assembly Sec7.RandRestart Zhan.Retarget Theorem14.BR3Ref

/-! ### `IdProp` depends only on three paths -/

theorem idProp_iff_pair {n : ℕ} (i₀ k : Fin n) (w : ℝ≥0 → ℝ) (vL : Fin n → ℝ≥0 → ℝ) (τ : ℝ≥0∞) :
    IdProp i₀ k w vL τ ↔ IdProp (0 : Fin 2) 1 w ![vL i₀, vL k] τ := Iff.rfl

/-- **`IdProp` transfers along equal paths** (other index sets allowed). -/
theorem idProp_of_paths {n n' : ℕ} {i₀ k : Fin n} {i₀' k' : Fin n'} {w : ℝ≥0 → ℝ} {vL : Fin n → ℝ≥0 → ℝ}
    {vL' : Fin n' → ℝ≥0 → ℝ} {τ : ℝ≥0∞} (h0 : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → vL i₀ t = vL' i₀' t)
    (hk : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → vL k t = vL' k' t) (hP : IdProp i₀ k w vL τ) : IdProp i₀' k' w vL' τ := by
  rw [idProp_iff_pair] at hP ⊢
  refine idProp_congr (fun t ht => ⟨rfl, fun i => ?_⟩) hP
  fin_cases i
  · exact h0 t ht
  · exact hk t ht

/-! ### Fibrewise sums -/

section Fibre

variable {n n' : ℕ} (π : Fin n → Fin n') {ρ : Fin n → ℝ} {ρ' : Fin n' → ℝ}

theorem sum_filter_comp_of_fibre (hρ : ∀ k, ρ' k = ∑ i ∈ univ.filter (fun i => π i = k), ρ i)
    (p : Fin n' → Prop) [DecidablePred p] :
    ∑ i ∈ univ.filter (fun i => p (π i)), ρ i = ∑ k ∈ univ.filter p, ρ' k := by
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [← Finset.sum_fiberwise (s := univ) (g := π) (f := fun i => if p (π i) then ρ i else 0)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hρ k]
  split_ifs with hk
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]; simp [hk]
  · refine Finset.sum_eq_zero fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]; simp [hk]

theorem sum_mul_comp_of_fibre (hρ : ∀ k, ρ' k = ∑ i ∈ univ.filter (fun i => π i = k), ρ i) (f : Fin n' → ℝ) :
    ∑ i, ρ i * f (π i) = ∑ k, ρ' k * f k := by
  rw [← Finset.sum_fiberwise (s := univ) (g := π) (f := fun i => ρ i * f (π i))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hρ k, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.1 hi).2]

end Fibre

/-! ### Splitting along a monotone surjection -/

section Split

variable {a : ℝ} {n n' nR : ℕ} {xL' ρL' : Fin n' → ℝ} {xR ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ}
  {vL' : Fin n' → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

theorem threshold_comp_iff {π : Fin n → Fin n'} {ρL : Fin n → ℝ}
    (hρ : ∀ k, ρL' k = ∑ i ∈ univ.filter (fun i => π i = k), ρL i) (w₀ : ℝ) (u : Fin n' → ℝ) (r : Fin nR → ℝ) :
    ForceWord.ThresholdCondition ρL ρR w₀ (fun i => u (π i)) r ↔ ForceWord.ThresholdCondition ρL' ρR w₀ u r := by
  unfold ForceWord.ThresholdCondition
  rw [sum_filter_comp_of_fibre π hρ (fun k => u k = w₀)]

/-- **Splitting a word along a monotone surjection.** -/
theorem IsIntegratedSLEPath.splitAlong (π : Fin n → Fin n') (hπ : Monotone π) (hsurj : Function.Surjective π)
    {ρL : Fin n → ℝ} (hρ : ∀ k, ρL' k = ∑ i ∈ univ.filter (fun i => π i = k), ρL i)
    (h : IsIntegratedSLEPath a xL' xR ρL' ρR w vL' vR b ζ) :
    IsIntegratedSLEPath a (fun i => xL' (π i)) xR ρL ρR w (fun i => vL' (π i)) vR b ζ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩ := h
  refine ⟨h1, fun k => h2 _, h3, h4, fun k => h5 _, h6, fun t ht => (h7 t ht).comp_monotone hπ,
    fun t ht k => h8 t ht _, h9, h10, fun t ht k => h11 t ht _, h12, fun t ht => ?_,
    fun t ht k => h14 t ht _, h15, fun k => h16 _, h17, fun t ht hth => ?_, fun hz => ?_, ?_⟩
  · rw [h13 t ht]
    congr 2
    have e : ∀ (r : Fin n' → ℝ) (j : Fin n'), (∫ s in (0 : ℝ)..t, r j / (w s.toNNReal - vL' j s.toNNReal)) =
        r j * ∫ s in (0 : ℝ)..t, (w s.toNNReal - vL' j s.toNNReal)⁻¹ := fun r j => by
      rw [← intervalIntegral.integral_const_mul]; simp only [div_eq_mul_inv]
    have e' : ∀ i : Fin n, (∫ s in (0 : ℝ)..t, ρL i / (w s.toNNReal - vL' (π i) s.toNNReal)) =
        ρL i * ∫ s in (0 : ℝ)..t, (w s.toNNReal - vL' (π i) s.toNNReal)⁻¹ := fun i => by
      rw [← intervalIntegral.integral_const_mul]; simp only [div_eq_mul_inv]
    simp only [e ρL', e']
    exact (sum_mul_comp_of_fibre π hρ fun j => ∫ s in (0 : ℝ)..t, (w s.toNNReal - vL' j s.toNNReal)⁻¹).symm
  · exact h18 t ht ((threshold_comp_iff hρ _ _ _).1 hth)
  · exact (threshold_comp_iff hρ _ xL' xR).2 (h19 hz)
  · intro T hT hTζ w₀ u₀ r₀ hlim
    choose σ hσ using hsurj
    have hc : Continuous fun p : ℝ × (Fin n → ℝ) × (Fin nR → ℝ) => (p.1, (fun k => p.2.1 (σ k)), p.2.2) := by
      fun_prop
    have h' := (hc.tendsto _).comp hlim
    have hlim' : Tendsto (fun t => (w t, fun k => vL' k t, fun j => vR j t)) (𝓝[<] T)
        (𝓝 (w₀, fun k => u₀ (σ k), r₀)) := by
      refine h'.congr' (Eventually.of_forall fun t => ?_)
      simp only [Function.comp_apply, hσ]
    have hth := h20 T hT hTζ w₀ _ r₀ hlim'
    have hu : u₀ = fun i => u₀ (σ (π i)) := by
      funext i
      have hi : Tendsto (fun t => vL' (π i) t) (𝓝[<] T) (𝓝 (u₀ i)) := tendsto_pi_nhds.1 hlim.snd_nhds.fst_nhds i
      have hi' : Tendsto (fun t => vL' (π i) t) (𝓝[<] T) (𝓝 (u₀ (σ (π i)))) := by
        have := tendsto_pi_nhds.1 hlim.snd_nhds.fst_nhds (σ (π i))
        simpa only [hσ] using this
      have : NeBot (𝓝[<] T) := nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
      exact tendsto_nhds_unique hi hi'
    rw [hu]
    exact (threshold_comp_iff hρ _ (fun k => u₀ (σ k)) r₀).2 hth

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}

/-- **Splitting an evolution along a monotone surjection.** -/
theorem IsIntegratedSLEEvolution.splitAlong {VL' : Fin n' → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (π : Fin n → Fin n') (hπ : Monotone π) (hsurj : Function.Surjective π) {ρL : Fin n → ℝ}
    (hρ : ∀ k, ρL' k = ∑ i ∈ univ.filter (fun i => π i = k), ρL i)
    (hE : IsIntegratedSLEEvolution a xL' xR ρL' ρR P 𝓕 W VL' VR B ζ') :
    IsIntegratedSLEEvolution a (fun i => xL' (π i)) xR ρL ρR P 𝓕 W (fun i => VL' (π i)) VR B ζ' := by
  obtain ⟨hB, hW, hVL, hVR, hpath⟩ := hE
  refine ⟨hB, hW, fun k => hVL _, hVR, ?_⟩
  filter_upwards [hpath] with ω hp
  exact IsIntegratedSLEPath.splitAlong π hπ hsurj hρ hp

end Split

/-! ### Dropping a leading weight-zero left mark -/

section Drop

variable {a : ℝ} {n nR : ℕ} {xL ρL : Fin (n + 1) → ℝ} {xR ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ}
  {vL : Fin (n + 2) → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {p : ℝ}

theorem sum_filter_cons_zero (u : Fin (n + 2) → ℝ) (w₀ : ℝ) :
    ∑ i ∈ univ.filter (fun i => u i = w₀), (Fin.cons 0 ρL : Fin (n + 2) → ℝ) i =
      ∑ i ∈ univ.filter (fun i => u i.succ = w₀), ρL i := by
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_succ]
  simp

theorem threshold_cons_zero_iff (w₀ : ℝ) (u : Fin (n + 2) → ℝ) (r : Fin nR → ℝ) :
    ForceWord.ThresholdCondition (Fin.cons 0 ρL : Fin (n + 2) → ℝ) ρR w₀ u r ↔
      ForceWord.ThresholdCondition ρL ρR w₀ (fun i => u i.succ) r := by
  unfold ForceWord.ThresholdCondition
  rw [sum_filter_cons_zero]

/-- **Dropping a leading left mark of weight `0`.** -/
theorem IsIntegratedSLEPath.dropHead
    (h : IsIntegratedSLEPath a (Fin.cons p xL) xR (Fin.cons 0 ρL) ρR w vL vR b ζ) :
    IsIntegratedSLEPath a xL xR ρL ρR w (fun i => vL i.succ) vR b ζ := by
  have hfp := h.isForcePath
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩ := h
  refine ⟨h1, fun k => by simpa using h2 k.succ, h3, h4, fun k => h5 _, h6,
    fun t ht => (h7 t ht).comp_monotone (Fin.strictMono_succ).monotone, fun t ht k => h8 t ht _, h9, h10,
    fun t ht k => h11 t ht _, h12, fun t ht => ?_, fun t ht k => by simpa using h14 t ht k.succ, h15,
    fun k => h16 _, h17, fun t ht hth => h18 t ht ((threshold_cons_zero_iff _ _ _).2 hth),
    fun hz => ?_, ?_⟩
  · rw [h13 t ht, Fin.sum_univ_succ]
    simp
  · have := (threshold_cons_zero_iff (ρL := ρL) (ρR := ρR) 0 (Fin.cons p xL) xR).1 (h19 hz)
    simpa using this
  · intro T hT hTζ w₀ u₀ r₀ hlim
    -- the dropped mark is decreasing in time and bounded below by the next mark
    have hIio : Iio T ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} := fun t ht => by
      rw [← hTζ]; exact_mod_cast ht
    have hanti : AntitoneOn (vL 0) (Iio T) := (hfp.antitoneOn_vL 0).mono hIio
    have h1T : Tendsto (vL 1) (𝓝[<] T) (𝓝 (u₀ 0)) := by
      have := tendsto_pi_nhds.1 hlim.snd_nhds.fst_nhds 0
      simpa using this
    have hNe : NeBot (𝓝[<] T) := nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
    have hge1 : ∀ t ∈ Iio T, u₀ 0 ≤ vL 1 t := by
      intro t ht
      refine le_of_tendsto h1T ?_
      filter_upwards [Ioo_mem_nhdsLT ht] with s hs
      exact (hfp.antitoneOn_vL 1) (hIio ht) (hIio hs.2) hs.1.le
    have hbdd : BddBelow (vL 0 '' Iio T) := by
      refine ⟨u₀ 0, ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      exact (hge1 t ht).trans (hfp.antitone_vL (hIio ht) (Fin.zero_le 1))
    have h0T := hanti.tendsto_nhdsLT hbdd
    set v₀ := sInf (vL 0 '' Iio T)
    have hlim' : Tendsto (fun t => (w t, fun i => vL i t, fun j => vR j t)) (𝓝[<] T)
        (𝓝 (w₀, (Fin.cons v₀ u₀ : Fin (n + 2) → ℝ), r₀)) := by
      refine hlim.fst_nhds.prodMk_nhds ((tendsto_pi_nhds.2 fun i => ?_).prodMk_nhds hlim.snd_nhds.snd_nhds)
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using h0T
      · simpa using tendsto_pi_nhds.1 hlim.snd_nhds.fst_nhds j
    have := (threshold_cons_zero_iff (ρL := ρL) (ρR := ρR) w₀ (Fin.cons v₀ u₀) r₀).1 (h20 T hT hTζ w₀ _ r₀ hlim')
    simpa using this

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}

/-- **Dropping a leading weight-zero left mark of an evolution.** -/
theorem IsIntegratedSLEEvolution.dropHead {VL : Fin (n + 2) → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hE : IsIntegratedSLEEvolution a (Fin.cons p xL) xR (Fin.cons 0 ρL) ρR P 𝓕 W VL VR B ζ') :
    IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W (fun i => VL i.succ) VR B ζ' := by
  obtain ⟨hB, hW, hVL, hVR, hpath⟩ := hE
  refine ⟨hB, hW, fun k => hVL _, hVR, ?_⟩
  filter_upwards [hpath] with ω hp
  exact IsIntegratedSLEPath.dropHead hp

end Drop

/-! ### The canonical law of the code event from one evolution -/

section Law

variable {κ : ℝ} {nL : ℕ}

/-- **One evolution with `IdProp` almost surely gives the full canonical law** (`BR3Ref.ae_mem_lawSetS_of_ae`). -/
theorem law_of_ae_idProp (hκ : 0 < κ) {xL : Fin nL → ℝ} {xR : Fin 0 → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin 0 → ℝ}
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin 0 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (i₀ k : Fin nL)
    (h : ∀ᵐ ω ∂P, IdProp i₀ k (W · ω) (fun i t => VL i t ω) (ζ ω)) :
    ∀ᵐ f ∂Sec2.Restart.wienerPath, ((xL, xR), enc f) ∈ lawSetS κ ρL ρR (idSet i₀ k) :=
  ae_mem_lawSetS_of_ae hκ (fun _ j => j.elim0) hE (measurableSet_idSet i₀ k)
    (Ψ := fun w vL _ τ => IdProp i₀ k w vL τ) (fun _ _ _ => Iff.rfl)
    (fun _ _ _ _ _ _ _ h hw => idProp_congr (fun t ht => ⟨(h t ht).1, (h t ht).2.1⟩) hw) h

/-- An evolution of a word, together with `IdProp` almost surely (a witness for `law_of_ae_idProp`). -/
def HasIdPropEvolution (κ : ℝ) {n : ℕ} (xL ρL : Fin n → ℝ) (xR : Fin 0 → ℝ) (i₀ k : Fin n) : Prop :=
  ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P) (𝓕 : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin n → ℝ≥0 → Ω → ℝ) (VR : Fin 0 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
    IsIntegratedSLEEvolution κ xL xR ρL ![] P 𝓕 W VL VR B ζ ∧
      ∀ᵐ ω ∂P, IdProp i₀ k (W · ω) (fun i t => VL i t ω) (ζ ω)

theorem law_of_hasIdPropEvolution (hκ : 0 < κ) {xL ρL : Fin nL → ℝ} {xR : Fin 0 → ℝ} {i₀ k : Fin nL}
    (h : HasIdPropEvolution κ xL ρL xR i₀ k) :
    ∀ᵐ f ∂Sec2.Restart.wienerPath, ((xL, xR), enc f) ∈ lawSetS κ ρL ![] (idSet i₀ k) := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE, hId⟩ := h
  exact law_of_ae_idProp hκ hE i₀ k hId

/-- **Transfer along a split**: an `IdProp` evolution of the merged word gives one of the word with coincident marks. -/
theorem HasIdPropEvolution.split {n n' : ℕ} {xL ρL : Fin n → ℝ} {xL' ρL' : Fin n' → ℝ} {xR : Fin 0 → ℝ}
    {i₀' k' : Fin n'} (h : HasIdPropEvolution κ xL' ρL' xR i₀' k') (π : Fin n → Fin n') (hπ : Monotone π)
    (hsurj : Function.Surjective π) (hρ : ∀ k, ρL' k = ∑ i ∈ univ.filter (fun i => π i = k), ρL i)
    (hx : ∀ i, xL' (π i) = xL i) {i₀ k : Fin n} (h0 : π i₀ = i₀') (hk : π k = k') :
    HasIdPropEvolution κ xL ρL xR i₀ k := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE, hId⟩ := h
  have hE' := IsIntegratedSLEEvolution.splitAlong π hπ hsurj hρ hE
  have hxe : (fun i => xL' (π i)) = xL := funext hx
  rw [hxe] at hE'
  refine ⟨Ω, mΩ, P, hP, 𝓕, W, fun i => VL (π i), VR, B, ζ, hE', ?_⟩
  filter_upwards [hId] with ω hω
  exact idProp_of_paths (fun t _ => by rw [h0]) (fun t _ => by rw [hk]) hω

/-- **The strong case**: a strictly decreasing left word whose target (Lean index `j ≥ 1`) is behind the nearest
mark, with the hypotheses of `ae_gap_and_newHorizon_top` for its reflection. -/
theorem hasIdPropEvolution_of_word (hκ : 0 < κ) {j m : ℕ} {xL ρL : Fin (j + 1 + m) → ℝ} (xR : Fin 0 → ℝ)
    (hsa : StrictAnti xL) (h0 : xL ⟨0, by omega⟩ < 0) (hj : 1 ≤ j)
    (hpre : ∀ i : Fin (j + 1 + m), (i : ℕ) < j → -2 < ∑ l ∈ univ.filter (· ≤ i), ρL l)
    (hnL : Sec4.HasGroupEndSums (κ / 2 - 2) (LP.retargetρL κ (![] : Fin 0 → ℝ) ρL) (-LP.retargetXL (-xR) (-xL)))
    (hnR : Sec4.HasGroupEndSums (κ / 2 - 2) (LP.retargetρR ρL) (LP.retargetXR (-xL))) :
    HasIdPropEvolution κ xL ρL xR ⟨0, by omega⟩ (LP.retargetIdx j m) := by
  have hle0 : ∀ i : Fin (j + 1 + m), (⟨0, by omega⟩ : Fin (j + 1 + m)) ≤ i := fun i =>
    Fin.le_iff_val_le_val.2 (Nat.zero_le _)
  have hxL0 : ∀ i, xL i ≤ 0 := fun i => (hsa.antitone (hle0 i)).trans h0.le
  have hF : IsOrderedForceWord xL xR := ⟨hsa.antitone, hxL0, fun i => i.elim0, fun i => i.elim0⟩
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ hF (ρL := ρL) (ρR := ![])
  refine ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE, ?_⟩
  have hD : LP.IsDistinctForceWord (-xR) (-xL) :=
    ⟨⟨fun i => i.elim0, fun i => i.elim0, hsa.antitone.neg, fun i => by simp [hxL0 i]⟩, fun i => i.elim0,
      hsa.neg⟩
  have hres := ae_gap_and_newHorizon_top hκ hD hj (by simpa using h0) hpre hnL hnR hE.reflect
  filter_upwards [hres, hE.ae_isIntegratedSLEPath] with ω hω hp
  have hfp := hp.isForcePath
  have hk0 : (⟨0, by omega⟩ : Fin (j + 1 + m)) < LP.retargetIdx j m := by
    rw [Fin.lt_def]; simp only [LP.retargetIdx, Fin.val_castAdd, Fin.val_last]; omega
  refine idProp_of_gap hfp.continuousOn_w (hfp.continuousOn_vL _) (hfp.continuousOn_vL _)
    (by rw [hfp.vL_zero]; exact (hsa hk0).trans h0) (fun t ht => ?_) ?_
  · have := hω.1 t (by simpa using ht)
    simpa using this
  · have := hω.2
    simpa [Sec5.Aux22Strip.retargetHorizon, LP.retargetPos, hfp.vL_zero] using this

/-- **The coincident-target case, 2 marks**: the target is the nearest mark. An auxiliary left mark of weight `0` at
half the target's position is put in front (`Fin.cons`); the weak retargeted noncollision
(`ae_newHorizon_top_weak`, only the old target protected) gives the infinite new horizon, and the auxiliary mark is
dropped (`IsIntegratedSLEEvolution.dropHead`). -/
theorem hasIdPropEvolution_phantom2 (hκ : 0 < κ) {xL ρL : Fin 2 → ℝ} (xR : Fin 0 → ℝ) (hsa : StrictAnti xL)
    (h0 : xL 0 < 0)
    (hnL : Sec4.HasGroupEndSums (κ / 2 - 2) (LP.retargetρL (j := 1) (m := 1) κ (![] : Fin 0 → ℝ) (Fin.cons 0 ρL))
      (-LP.retargetXL (j := 1) (m := 1) (-xR) (-(Fin.cons (xL 0 / 2) xL : Fin (2 + 1) → ℝ))))
    (hnR : Theorem14.GW0.RightGroupEndsAdmissible
      (LP.retargetXR (j := 1) (m := 1) (-(Fin.cons (xL 0 / 2) xL : Fin (2 + 1) → ℝ)))
      (LP.retargetρR (j := 1) (m := 1) (Fin.cons 0 ρL))) :
    HasIdPropEvolution κ xL ρL xR 0 0 := by
  set xP : Fin (2 + 1) → ℝ := Fin.cons (xL 0 / 2) xL with hxP
  have hle0 : ∀ i : Fin 2, (0 : Fin 2) ≤ i := fun i => Fin.zero_le i
  have hxL0 : ∀ i, xL i ≤ xL 0 := fun i => hsa.antitone (hle0 i)
  have hsaP : StrictAnti xP := by
    refine Fin.strictAnti_iff_succ_lt.2 fun i => ?_
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp only [hxP, Fin.cons_succ, Fin.castSucc_zero, Fin.cons_zero]; linarith
    · simp only [hxP, Fin.cons_succ]
      rw [show (Fin.castSucc i'.succ : Fin (2 + 1)) = (Fin.castSucc i').succ from rfl, Fin.cons_succ]
      exact hsa (Fin.castSucc_lt_succ (i := i'))
  have hxP0 : ∀ i, xP i ≤ 0 := fun i => by
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp only [hxP, Fin.cons_zero]; linarith
    · simp only [hxP, Fin.cons_succ]; linarith [hxL0 i']
  have hF : IsOrderedForceWord xP xR := ⟨hsaP.antitone, hxP0, fun i => i.elim0, fun i => i.elim0⟩
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ hF (ρL := (Fin.cons 0 ρL : Fin (2 + 1) → ℝ)) (ρR := ![])
  have hD : LP.IsDistinctForceWord (-xR) (-xP) :=
    ⟨⟨fun i => i.elim0, fun i => i.elim0, hsaP.antitone.neg, fun i => by simp [hxP0 i]⟩, fun i => i.elim0,
      hsaP.neg⟩
  have hres := ae_newHorizon_top_weak (j := 1) (m := 1) hκ hD le_rfl
    (fun i hi => by
      have hi0 : i = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
      subst hi0
      simp [Finset.sum_filter])
    hnL hnR hE.reflect
  refine ⟨Ω, mΩ, P, hP, 𝓕, W, fun i => VL i.succ, VR, B, ζ, IsIntegratedSLEEvolution.dropHead hE, ?_⟩
  filter_upwards [hres, hE.ae_isIntegratedSLEPath] with ω hω hp
  have hfp := hp.isForcePath
  have hk : (LP.retargetIdx 1 1 : Fin (1 + 1 + 1)) = (1 : Fin (2 + 1)) := rfl
  have hId : IdProp (1 : Fin (2 + 1)) 1 (W · ω) (fun i t => VL i t ω) (ζ ω) := by
    refine idProp_of_gap hfp.continuousOn_w (hfp.continuousOn_vL 1) (hfp.continuousOn_vL 1)
      (by rw [hfp.vL_zero]; show xL 0 < 0; exact h0) (fun t ht => ?_) ?_
    · have := lt_of_lt_sepTime ht
      linarith
    · have := hω
      simpa [Sec5.Aux22Strip.retargetHorizon, LP.retargetPos, hk, hfp.vL_zero] using this
  exact idProp_of_paths (fun t _ => rfl) (fun t _ => rfl) hId

/-- **The coincident-target case, 1 marks**: the target is the nearest mark. An auxiliary left mark of weight `0` at
half the target's position is put in front (`Fin.cons`); the weak retargeted noncollision
(`ae_newHorizon_top_weak`, only the old target protected) gives the infinite new horizon, and the auxiliary mark is
dropped (`IsIntegratedSLEEvolution.dropHead`). -/
theorem hasIdPropEvolution_phantom1 (hκ : 0 < κ) {xL ρL : Fin 1 → ℝ} (xR : Fin 0 → ℝ) (hsa : StrictAnti xL)
    (h0 : xL 0 < 0)
    (hnL : Sec4.HasGroupEndSums (κ / 2 - 2) (LP.retargetρL (j := 1) (m := 0) κ (![] : Fin 0 → ℝ) (Fin.cons 0 ρL))
      (-LP.retargetXL (j := 1) (m := 0) (-xR) (-(Fin.cons (xL 0 / 2) xL : Fin (1 + 1) → ℝ))))
    (hnR : Theorem14.GW0.RightGroupEndsAdmissible
      (LP.retargetXR (j := 1) (m := 0) (-(Fin.cons (xL 0 / 2) xL : Fin (1 + 1) → ℝ)))
      (LP.retargetρR (j := 1) (m := 0) (Fin.cons 0 ρL))) :
    HasIdPropEvolution κ xL ρL xR 0 0 := by
  set xP : Fin (1 + 1) → ℝ := Fin.cons (xL 0 / 2) xL with hxP
  have hle0 : ∀ i : Fin 1, (0 : Fin 1) ≤ i := fun i => Fin.zero_le i
  have hxL0 : ∀ i, xL i ≤ xL 0 := fun i => hsa.antitone (hle0 i)
  have hsaP : StrictAnti xP := by
    refine Fin.strictAnti_iff_succ_lt.2 fun i => ?_
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp only [hxP, Fin.cons_succ, Fin.castSucc_zero, Fin.cons_zero]; linarith
    · simp only [hxP, Fin.cons_succ]
      rw [show (Fin.castSucc i'.succ : Fin (1 + 1)) = (Fin.castSucc i').succ from rfl, Fin.cons_succ]
      exact hsa (Fin.castSucc_lt_succ (i := i'))
  have hxP0 : ∀ i, xP i ≤ 0 := fun i => by
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp only [hxP, Fin.cons_zero]; linarith
    · simp only [hxP, Fin.cons_succ]; linarith [hxL0 i']
  have hF : IsOrderedForceWord xP xR := ⟨hsaP.antitone, hxP0, fun i => i.elim0, fun i => i.elim0⟩
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ hF (ρL := (Fin.cons 0 ρL : Fin (1 + 1) → ℝ)) (ρR := ![])
  have hD : LP.IsDistinctForceWord (-xR) (-xP) :=
    ⟨⟨fun i => i.elim0, fun i => i.elim0, hsaP.antitone.neg, fun i => by simp [hxP0 i]⟩, fun i => i.elim0,
      hsaP.neg⟩
  have hres := ae_newHorizon_top_weak (j := 1) (m := 0) hκ hD le_rfl
    (fun i hi => by
      have hi0 : i = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
      subst hi0
      simp [Finset.sum_filter])
    hnL hnR hE.reflect
  refine ⟨Ω, mΩ, P, hP, 𝓕, W, fun i => VL i.succ, VR, B, ζ, IsIntegratedSLEEvolution.dropHead hE, ?_⟩
  filter_upwards [hres, hE.ae_isIntegratedSLEPath] with ω hω hp
  have hfp := hp.isForcePath
  have hk : (LP.retargetIdx 1 0 : Fin (1 + 1 + 0)) = (1 : Fin (1 + 1)) := rfl
  have hId : IdProp (1 : Fin (1 + 1)) 1 (W · ω) (fun i t => VL i t ω) (ζ ω) := by
    refine idProp_of_gap hfp.continuousOn_w (hfp.continuousOn_vL 1) (hfp.continuousOn_vL 1)
      (by rw [hfp.vL_zero]; show xL 0 < 0; exact h0) (fun t ht => ?_) ?_
    · have := lt_of_lt_sepTime ht
      linarith
    · have := hω
      simpa [Sec5.Aux22Strip.retargetHorizon, LP.retargetPos, hk, hfp.vL_zero] using this
  exact idProp_of_paths (fun t _ => rfl) (fun t _ => rfl) hId

end Law

/-! ### The coincidence patterns of the two image words -/

section Patterns

open ZhanGT4.A2X

/-- **(G3) the coincidence pattern `c01`** (`cij`: image marks `i`, `j` coincide; the others are
strict): the merged word, split back along `π` (`HasIdPropEvolution.split`). -/
theorem hasIdPropEvolution_G3_c01 {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) {xL : Fin 4 → ℝ}
    (xR : Fin 0 → ℝ) (h0 : xL 0 < 0) (e01 : xL 1 = xL 0) (l12 : xL 2 < xL 1) (l23 : xL 3 < xL 2) :
    HasIdPropEvolution κ xL (largeG3ImgRhoL κ) xR 0 2 := by
  have hκ0 : 0 < κ := by linarith
  have hs := hasIdPropEvolution_of_word (j := 1) (m := 1) (xL := ![xL 0, xL 2, xL 3])
      (ρL := ![κ / 2 - 2, -(κ / 2), κ - 6]) hκ0 xR
      (Fin.strictAnti_iff_succ_lt.2 fun i => by fin_cases i <;> simp <;> linarith) (by simpa using h0) (by norm_num)
      (fun i hi => by
        fin_cases i <;> simp at hi; (simp [Finset.sum_filter]; try linarith))
      (fun j _ => by
        fin_cases j <;> (simp [LP.retargetρL, Finset.sum_filter, Fin.sum_univ_succ, Fin.append,
          Fin.addCases, Fin.subNat, Fin.cast]; try linarith))
      (fun j _ => by
        fin_cases j; (simp [LP.retargetρR]; try linarith))
  refine hs.split ![0, 0, 1, 2] (fun a b hab => by fin_cases a <;> fin_cases b <;> simp_all)
    (fun k => by
      fin_cases k
      · exact ⟨0, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩)
    (fun k => by fin_cases k <;> (simp [Finset.sum_filter, Fin.sum_univ_succ, largeG3ImgRhoL]; try ring))
    (fun i => by fin_cases i <;> simp; linarith) rfl rfl

/-- **(G3) the coincidence pattern `c12`** (`cij`: image marks `i`, `j` coincide; the others are
strict): the merged word, split back along `π` (`HasIdPropEvolution.split`). -/
theorem hasIdPropEvolution_G3_c12 {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) {xL : Fin 4 → ℝ}
    (xR : Fin 0 → ℝ) (h0 : xL 0 < 0) (l01 : xL 1 < xL 0) (e12 : xL 2 = xL 1) (l23 : xL 3 < xL 2) :
    HasIdPropEvolution κ xL (largeG3ImgRhoL κ) xR 0 2 := by
  have hκ0 : 0 < κ := by linarith
  have hs := hasIdPropEvolution_of_word (j := 1) (m := 1) (xL := ![xL 0, xL 1, xL 3])
      (ρL := ![κ - 4, 2 - κ, κ - 6]) hκ0 xR
      (Fin.strictAnti_iff_succ_lt.2 fun i => by fin_cases i <;> simp <;> linarith) (by simpa using h0) (by norm_num)
      (fun i hi => by
        fin_cases i <;> simp at hi; (simp [Finset.sum_filter]; try linarith))
      (fun j _ => by
        fin_cases j <;> (simp [LP.retargetρL, Finset.sum_filter, Fin.sum_univ_succ, Fin.append,
          Fin.addCases, Fin.subNat, Fin.cast]; try linarith))
      (fun j _ => by
        fin_cases j; (simp [LP.retargetρR]; try linarith))
  refine hs.split ![0, 1, 1, 2] (fun a b hab => by fin_cases a <;> fin_cases b <;> simp_all)
    (fun k => by
      fin_cases k
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨3, rfl⟩)
    (fun k => by fin_cases k <;> (simp [Finset.sum_filter, Fin.sum_univ_succ, largeG3ImgRhoL]; try ring))
    (fun i => by fin_cases i <;> simp; linarith) rfl rfl

/-- **(G3) the coincidence pattern `c23`** (`cij`: image marks `i`, `j` coincide; the others are
strict): the merged word, split back along `π` (`HasIdPropEvolution.split`). -/
theorem hasIdPropEvolution_G3_c23 {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) {xL : Fin 4 → ℝ}
    (xR : Fin 0 → ℝ) (h0 : xL 0 < 0) (l01 : xL 1 < xL 0) (l12 : xL 2 < xL 1) (e23 : xL 3 = xL 2) :
    HasIdPropEvolution κ xL (largeG3ImgRhoL κ) xR 0 2 := by
  have hκ0 : 0 < κ := by linarith
  have hs := hasIdPropEvolution_of_word (j := 2) (m := 0) (xL := ![xL 0, xL 1, xL 2])
      (ρL := ![κ - 4, 2 - κ / 2, κ / 2 - 6]) hκ0 xR
      (Fin.strictAnti_iff_succ_lt.2 fun i => by fin_cases i <;> simp <;> linarith) (by simpa using h0) (by norm_num)
      (fun i hi => by
        fin_cases i <;> simp at hi <;> (simp [Finset.sum_filter, Fin.sum_univ_succ]; try linarith))
      (fun j _ => by
        fin_cases j; (simp [LP.retargetρL, Fin.sum_univ_succ, Fin.append,
          Fin.addCases, Fin.subNat, Fin.cast]; try linarith))
      (fun j _ => by
        fin_cases j <;> (simp [LP.retargetρR, Finset.sum_filter, Fin.sum_univ_succ]; try linarith))
  refine hs.split ![0, 1, 2, 2] (fun a b hab => by fin_cases a <;> fin_cases b <;> simp_all)
    (fun k => by
      fin_cases k
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩)
    (fun k => by fin_cases k <;> (simp [Finset.sum_filter, Fin.sum_univ_succ, largeG3ImgRhoL]; try ring))
    (fun i => by fin_cases i <;> simp; linarith) rfl rfl

/-- **(G3) the coincidence pattern `c01c23`** (`cij`: image marks `i`, `j` coincide; the others are
strict): the merged word, split back along `π` (`HasIdPropEvolution.split`). -/
theorem hasIdPropEvolution_G3_c01c23 {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) {xL : Fin 4 → ℝ}
    (xR : Fin 0 → ℝ) (h0 : xL 0 < 0) (e01 : xL 1 = xL 0) (l12 : xL 2 < xL 1) (e23 : xL 3 = xL 2) :
    HasIdPropEvolution κ xL (largeG3ImgRhoL κ) xR 0 2 := by
  have hκ0 : 0 < κ := by linarith
  have hs := hasIdPropEvolution_of_word (j := 1) (m := 0) (xL := ![xL 0, xL 2]) (ρL := ![κ / 2 - 2, κ / 2 - 6]) hκ0 xR
      (Fin.strictAnti_iff_succ_lt.2 fun i => by fin_cases i; simp; linarith) (by simpa using h0) (by norm_num)
      (fun i hi => by
        fin_cases i <;> simp at hi; (simp [Finset.sum_filter]; try linarith))
      (fun j _ => by
        fin_cases j; (simp [LP.retargetρL, Fin.sum_univ_succ, Fin.append,
          Fin.addCases, Fin.subNat, Fin.cast]; try linarith))
      (fun j _ => by
        fin_cases j; (simp [LP.retargetρR]; try linarith))
  refine hs.split ![0, 0, 1, 1] (fun a b hab => by fin_cases a <;> fin_cases b <;> simp_all)
    (fun k => by
      fin_cases k
      · exact ⟨0, rfl⟩
      · exact ⟨2, rfl⟩)
    (fun k => by fin_cases k <;> (simp [Finset.sum_filter, Fin.sum_univ_succ, largeG3ImgRhoL]; try ring))
    (fun i => by fin_cases i <;> simp <;> linarith) rfl rfl

/-- **(G3) the coincidence pattern `c12c23`** (`cij`: image marks `i`, `j` coincide; the others are
strict): the merged word, split back along `π` (`HasIdPropEvolution.split`). -/
theorem hasIdPropEvolution_G3_c12c23 {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) {xL : Fin 4 → ℝ}
    (xR : Fin 0 → ℝ) (h0 : xL 0 < 0) (l01 : xL 1 < xL 0) (e12 : xL 2 = xL 1) (e23 : xL 3 = xL 2) :
    HasIdPropEvolution κ xL (largeG3ImgRhoL κ) xR 0 2 := by
  have hκ0 : 0 < κ := by linarith
  have hs := hasIdPropEvolution_of_word (j := 1) (m := 0) (xL := ![xL 0, xL 1]) (ρL := ![κ - 4, -4]) hκ0 xR
      (Fin.strictAnti_iff_succ_lt.2 fun i => by fin_cases i; simp; linarith) (by simpa using h0) (by norm_num)
      (fun i hi => by
        fin_cases i <;> simp at hi; (simp [Finset.sum_filter]; try linarith))
      (fun j _ => by
        fin_cases j; (simp [LP.retargetρL, Fin.sum_univ_succ, Fin.append,
          Fin.addCases, Fin.subNat, Fin.cast]; try linarith))
      (fun j _ => by
        fin_cases j; (simp [LP.retargetρR]; try linarith))
  refine hs.split ![0, 1, 1, 1] (fun a b hab => by fin_cases a <;> fin_cases b <;> simp_all)
    (fun k => by
      fin_cases k
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩)
    (fun k => by fin_cases k <;> (simp [Finset.sum_filter, Fin.sum_univ_succ, largeG3ImgRhoL]; try ring))
    (fun i => by fin_cases i <;> simp <;> linarith) rfl rfl

/-- **(G3) the coincidence pattern `c01c12`** (`cij`: image marks `i`, `j` coincide; the others are
strict): the merged word, split back along `π` (`HasIdPropEvolution.split`). -/
theorem hasIdPropEvolution_G3_c01c12 {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) {xL : Fin 4 → ℝ}
    (xR : Fin 0 → ℝ) (h0 : xL 0 < 0) (e01 : xL 1 = xL 0) (e12 : xL 2 = xL 1) (l23 : xL 3 < xL 2) :
    HasIdPropEvolution κ xL (largeG3ImgRhoL κ) xR 0 2 := by
  have hκ0 : 0 < κ := by linarith
  have hs := hasIdPropEvolution_phantom2 (xL := ![xL 0, xL 3]) (ρL := ![-2, κ - 6]) hκ0 xR
      (Fin.strictAnti_iff_succ_lt.2 fun i => by fin_cases i; simp; linarith ) (by simpa using h0)
      (fun j _ => by
        fin_cases j <;> (simp [LP.retargetρL, Finset.sum_filter, Fin.sum_univ_succ, Fin.append,
          Fin.addCases, Fin.subNat, Fin.cast]; try linarith))
      (fun j _ => by
        fin_cases j; (simp [LP.retargetρR]; try linarith))
  refine hs.split ![0, 0, 0, 1] (fun a b hab => by fin_cases a <;> fin_cases b <;> simp_all)
    (fun k => by
      fin_cases k
      · exact ⟨0, rfl⟩
      · exact ⟨3, rfl⟩)
    (fun k => by fin_cases k <;> (simp [Finset.sum_filter, Fin.sum_univ_succ, largeG3ImgRhoL]; try ring))
    (fun i => by fin_cases i <;> simp <;> linarith) rfl rfl

/-- **(G3) the coincidence pattern `call`** (`cij`: image marks `i`, `j` coincide; the others are
strict): the merged word, split back along `π` (`HasIdPropEvolution.split`). -/
theorem hasIdPropEvolution_G3_call {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) {xL : Fin 4 → ℝ}
    (xR : Fin 0 → ℝ) (h0 : xL 0 < 0) (e01 : xL 1 = xL 0) (e12 : xL 2 = xL 1) (e23 : xL 3 = xL 2) :
    HasIdPropEvolution κ xL (largeG3ImgRhoL κ) xR 0 2 := by
  have hκ0 : 0 < κ := by linarith
  have hs := hasIdPropEvolution_phantom1 (xL := ![xL 0]) (ρL := ![κ - 8]) hκ0 xR
      (Fin.strictAnti_iff_succ_lt.2 fun i => i.elim0) (by simpa using h0)
      (fun j _ => by
        fin_cases j; (simp [LP.retargetρL, Fin.sum_univ_succ, Fin.append,
          Fin.addCases, Fin.subNat, Fin.cast]; try linarith))
      (fun j _ => by
        fin_cases j; (simp [LP.retargetρR]; try linarith))
  refine hs.split ![0, 0, 0, 0] (fun a b hab => by fin_cases a <;> fin_cases b <;> simp_all)
    (fun k => by
      fin_cases k
      · exact ⟨0, rfl⟩)
    (fun k => by fin_cases k; (simp [Finset.sum_filter, Fin.sum_univ_succ, largeG3ImgRhoL]; try ring))
    (fun i => by fin_cases i <;> simp <;> linarith) rfl rfl

/-- **(Eight) the coincidence pattern `c12`** (`cij`: image marks `i`, `j` coincide; the others are
strict): the merged word, split back along `π` (`HasIdPropEvolution.split`). -/
theorem hasIdPropEvolution_Eight_c12 {κ : ℝ} (hκ4 : 8 ≤ κ) {xL : Fin 3 → ℝ}
    (xR : Fin 0 → ℝ) (h0 : xL 0 < 0) (l01 : xL 1 < xL 0) (e12 : xL 2 = xL 1) :
    HasIdPropEvolution κ xL (largeEightImgRhoL κ) xR 0 1 := by
  have hκ0 : 0 < κ := by linarith
  have hs := hasIdPropEvolution_of_word (j := 1) (m := 0) (xL := ![xL 0, xL 1]) (ρL := ![(κ - 4) / 2, 2 - κ / 2]) hκ0 xR
      (Fin.strictAnti_iff_succ_lt.2 fun i => by fin_cases i; simp; linarith) (by simpa using h0) (by norm_num)
      (fun i hi => by
        fin_cases i <;> simp at hi; (simp [Finset.sum_filter]; try linarith))
      (fun j _ => by
        fin_cases j; (simp [LP.retargetρL, Fin.sum_univ_succ, Fin.append,
          Fin.addCases, Fin.subNat, Fin.cast]; try linarith))
      (fun j _ => by
        fin_cases j; (simp [LP.retargetρR]; try linarith))
  refine hs.split ![0, 1, 1] (fun a b hab => by fin_cases a <;> fin_cases b <;> simp_all)
    (fun k => by
      fin_cases k
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩)
    (fun k => by fin_cases k <;> (simp [Finset.sum_filter, Fin.sum_univ_succ, largeEightImgRhoL]; try ring))
    (fun i => by fin_cases i <;> simp; linarith) rfl rfl

/-- **(Eight) the coincidence pattern `c01`** (`cij`: image marks `i`, `j` coincide; the others are
strict): the merged word, split back along `π` (`HasIdPropEvolution.split`). -/
theorem hasIdPropEvolution_Eight_c01 {κ : ℝ} (hκ4 : 8 ≤ κ) {xL : Fin 3 → ℝ}
    (xR : Fin 0 → ℝ) (h0 : xL 0 < 0) (e01 : xL 1 = xL 0) (l12 : xL 2 < xL 1) :
    HasIdPropEvolution κ xL (largeEightImgRhoL κ) xR 0 1 := by
  have hκ0 : 0 < κ := by linarith
  have hs := hasIdPropEvolution_phantom2 (xL := ![xL 0, xL 2]) (ρL := ![-2, 2]) hκ0 xR
      (Fin.strictAnti_iff_succ_lt.2 fun i => by fin_cases i; simp; linarith ) (by simpa using h0)
      (fun j _ => by
        fin_cases j <;> (simp [LP.retargetρL, Finset.sum_filter, Fin.sum_univ_succ, Fin.append,
          Fin.addCases, Fin.subNat, Fin.cast]; try linarith))
      (fun j _ => by
        fin_cases j; (simp [LP.retargetρR]; try linarith))
  refine hs.split ![0, 0, 1] (fun a b hab => by fin_cases a <;> fin_cases b <;> simp_all)
    (fun k => by
      fin_cases k
      · exact ⟨0, rfl⟩
      · exact ⟨2, rfl⟩)
    (fun k => by fin_cases k <;> (simp [Finset.sum_filter, Fin.sum_univ_succ, largeEightImgRhoL]; try ring))
    (fun i => by fin_cases i <;> simp; linarith) rfl rfl

/-- **(Eight) the coincidence pattern `call`** (`cij`: image marks `i`, `j` coincide; the others are
strict): the merged word, split back along `π` (`HasIdPropEvolution.split`). -/
theorem hasIdPropEvolution_Eight_call {κ : ℝ} (hκ4 : 8 ≤ κ) {xL : Fin 3 → ℝ}
    (xR : Fin 0 → ℝ) (h0 : xL 0 < 0) (e01 : xL 1 = xL 0) (e12 : xL 2 = xL 1) :
    HasIdPropEvolution κ xL (largeEightImgRhoL κ) xR 0 1 := by
  have hκ0 : 0 < κ := by linarith
  have hs := hasIdPropEvolution_phantom1 (xL := ![xL 0]) (ρL := ![0]) hκ0 xR
      (Fin.strictAnti_iff_succ_lt.2 fun i => i.elim0) (by simpa using h0)
      (fun j _ => by
        fin_cases j; (simp [LP.retargetρL, Fin.sum_univ_succ, Fin.append,
          Fin.addCases, Fin.subNat, Fin.cast]; try linarith))
      (fun j _ => by
        fin_cases j; (simp [LP.retargetρR]; try linarith))
  refine hs.split ![0, 0, 0] (fun a b hab => by fin_cases a <;> fin_cases b <;> simp_all)
    (fun k => by
      fin_cases k
      · exact ⟨0, rfl⟩)
    (fun k => by fin_cases k; (simp [Finset.sum_filter, Fin.sum_univ_succ, largeEightImgRhoL]; try ring))
    (fun i => by fin_cases i <;> simp <;> linarith) rfl rfl

end Patterns

end InteractingSLE.ZhanGT4.A2P3ID
