/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71MMain
import InteractingSLE.Spec.Sec7.PocketTraversal
import InteractingSLE.Spec.Supplement.CounterflowRange

/-!
# Lemma 7.1, P (a): boundary limits of the inverse pocket chart

Packet PROVE-LEMMA71M, first step of the side limits (`Lemma71M.PocketSideLimit`): the inverse chart of the active
component has a limit at every real point. Here the pocket part: the pocket construction of PROVE-LEMMA71K comes with a
boundary map `Ψ` of the Cayley image `Ĉ = cayley(C)` (continuous and injective on `cl Ĉ ∖ {b}`, `‖Ψ‖ → ∞` at the
closing point `b`, `ψ = Ψ ∘ cayley` on `C`). Then `Ψ` maps `cl Ĉ ∖ {b}` onto `ℍ̄`, and its inverse is continuous there:

* `exists_subseq_tendsto_cayley_inv`: along any sequence of `ℍ` tending to `q ∈ ℍ̄`, `cayley ∘ ψ⁻¹` has a subsequence
  converging to a point `z ≠ b` of `cl Ĉ` with `Ψ z = q` (compactness of `cl Ĉ`, the blow-up at `b`, continuity of `Ψ`);
* **`tendsto_cayley_inv_of_ext`**: `cayley ∘ ψ⁻¹` converges at every `q ∈ ℍ̄` from `ℍ`, to the unique `z ∈ cl Ĉ ∖ {b}`
  with `Ψ z = q`;
* **`tendsto_inv_of_ext`**: if moreover `1 ∉ cl Ĉ ∖ {b}`, `ψ⁻¹` itself converges at `q`, to `cayleyInv z`;
* **`exists_tendsto_pocketInv`**: for a segment curve `γ'` and `t < capLife γ'`, the inverse chart `pocketInv` of the
  active component converges at every point of `ℍ̄` from `ℍ` (`f_t⁻¹` has boundary limits because the capacity
  reparametrization of `γ'` is a continuous generating trace, `PocketTraversal.IsDrivenCurve.isGeneratingTrace` and
  `TraceClose.hasBdryLimits_of_isLoewnerTraceLT`; then `ψ⁻¹` at the limit point, `tendsto_inv_of_ext`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma71M

open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)

section Ext

variable {C : Set ℂ} {c : Chart} {Ψ : ℂ → ℂ} {b : ℂ}

/-- Along a sequence of `ℍ` tending to `q`, a subsequence of `cayley ∘ ψ⁻¹` converges to a point `z ≠ b` of `cl Ĉ`
with `Ψ z = q`. -/
theorem exists_subseq_tendsto_cayley_inv (hc : c.IsConformal) (hdom : (c.dom : Set ℂ) = C) (hCH : C ⊆ H)
    (hbC : b ∉ cayley '' C) (hΨc : ContinuousOn Ψ (closure (cayley '' C) \ {b}))
    (hΨtop : Tendsto (fun x => ‖Ψ x‖) (𝓝[closure (cayley '' C) \ {b}] b) atTop)
    (hΨe : ∀ x ∈ C, c.1 x = Ψ (cayley x)) {q : ℂ} {y : ℕ → ℂ} (hyH : ∀ n, y n ∈ H)
    (hy : Tendsto y atTop (𝓝 q)) :
    ∃ z ∈ closure (cayley '' C) \ {b}, Ψ z = q ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => cayley (c.2.1 (y (φ n)))) atTop (𝓝 z) := by
  have hS : IsCompact (closure (cayley '' C)) := by
    refine (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset isClosed_closure ?_
    refine closure_minimal ?_ isClosed_closedBall
    rintro _ ⟨x, hx, rfl⟩
    exact ball_subset_closedBall (QuantumZipper.CA.cayley_mem_ball (hCH hx))
  have hmemC : ∀ n, c.2.1 (y n) ∈ C := fun n => by
    rw [← hdom]; exact hc.inv_mem_dom (hyH n)
  have hgK : ∀ n, cayley (c.2.1 (y n)) ∈ closure (cayley '' C) \ {b} := fun n =>
    ⟨subset_closure (mem_image_of_mem _ (hmemC n)), fun h => hbC ⟨_, hmemC n, h⟩⟩
  have hΨg : ∀ n, Ψ (cayley (c.2.1 (y n))) = y n := fun n => by
    rw [← hΨe _ (hmemC n), hc.2.2 _ (hyH n)]
  obtain ⟨z, hzS, φ, hφ, hlim⟩ := hS.tendsto_subseq (x := fun n => cayley (c.2.1 (y n))) fun n => (hgK n).1
  have hyφ : Tendsto (fun n => y (φ n)) atTop (𝓝 q) := hy.comp hφ.tendsto_atTop
  have hzb : z ≠ b := by
    rintro rfl
    have hK : Tendsto (fun n => cayley (c.2.1 (y (φ n)))) atTop (𝓝[closure (cayley '' C) \ {z}] z) :=
      tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => hgK (φ n)⟩
    have h1 := hΨtop.comp hK
    have h2 : Tendsto (fun n => ‖y (φ n)‖) atTop (𝓝 ‖q‖) := (continuous_norm.tendsto q).comp hyφ
    refine not_tendsto_atTop_of_tendsto_nhds h2 (h1.congr fun n => ?_)
    simp only [Function.comp_apply, hΨg]
  have hzK : z ∈ closure (cayley '' C) \ {b} := ⟨hzS, hzb⟩
  refine ⟨z, hzK, ?_, φ, hφ, hlim⟩
  have hK : Tendsto (fun n => cayley (c.2.1 (y (φ n)))) atTop (𝓝[closure (cayley '' C) \ {b}] z) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => hgK (φ n)⟩
  have h1 := ((hΨc z hzK).tendsto).comp hK
  refine tendsto_nhds_unique (h1.congr fun n => ?_) hyφ
  simp only [Function.comp_apply, hΨg]

/-- **The inverse pocket chart has boundary limits in the Cayley picture**: for `q ∈ ℍ̄`, `cayley ∘ ψ⁻¹` converges
at `q` from `ℍ` to the unique point `z ∈ cl Ĉ ∖ {b}` with `Ψ z = q`. -/
theorem tendsto_cayley_inv_of_ext (hc : c.IsConformal) (hdom : (c.dom : Set ℂ) = C) (hCH : C ⊆ H)
    (hbC : b ∉ cayley '' C) (hΨc : ContinuousOn Ψ (closure (cayley '' C) \ {b}))
    (hΨi : InjOn Ψ (closure (cayley '' C) \ {b}))
    (hΨtop : Tendsto (fun x => ‖Ψ x‖) (𝓝[closure (cayley '' C) \ {b}] b) atTop)
    (hΨe : ∀ x ∈ C, c.1 x = Ψ (cayley x)) {q : ℂ} (hq : q ∈ closure H) :
    ∃ z ∈ closure (cayley '' C) \ {b}, Ψ z = q ∧
      Tendsto (fun y => cayley (c.2.1 y)) (𝓝[H] q) (𝓝 z) := by
  obtain ⟨y, hyH, hy⟩ := mem_closure_iff_seq_limit.1 hq
  obtain ⟨z, hzK, hΨz, -⟩ := exists_subseq_tendsto_cayley_inv hc hdom hCH hbC hΨc hΨtop hΨe hyH hy
  refine ⟨z, hzK, hΨz, ?_⟩
  by_contra hne
  rw [Metric.tendsto_nhdsWithin_nhds] at hne
  push Not at hne
  obtain ⟨ε, hε, hbad⟩ := hne
  have hδ : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  choose y' hy'H hy'q hy'z using fun n => hbad _ (hδ n)
  have hy' : Tendsto y' atTop (𝓝 q) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => (hy'q n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨z', hz'K, hΨz', φ, hφ, hlim⟩ := exists_subseq_tendsto_cayley_inv hc hdom hCH hbC hΨc hΨtop hΨe hy'H hy'
  have hzz : z' = z := hΨi hz'K hzK (hΨz'.trans hΨz.symm)
  rw [hzz] at hlim
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlim) ε hε
  exact absurd (hN N le_rfl) (not_lt.2 (hy'z (φ N)))

/-- **The inverse pocket chart has boundary limits**: if moreover `1 ∉ cl Ĉ ∖ {b}` (the pocket is bounded, or `∞` is
its closing point), `ψ⁻¹` converges at every `q ∈ ℍ̄` from `ℍ`, to `cayleyInv z` with `Ψ z = q`. -/
theorem tendsto_inv_of_ext (hc : c.IsConformal) (hdom : (c.dom : Set ℂ) = C) (hCH : C ⊆ H)
    (hbC : b ∉ cayley '' C) (hΨc : ContinuousOn Ψ (closure (cayley '' C) \ {b}))
    (hΨi : InjOn Ψ (closure (cayley '' C) \ {b}))
    (hΨtop : Tendsto (fun x => ‖Ψ x‖) (𝓝[closure (cayley '' C) \ {b}] b) atTop)
    (hΨe : ∀ x ∈ C, c.1 x = Ψ (cayley x)) (h1 : (1 : ℂ) ∉ closure (cayley '' C) \ {b}) {q : ℂ}
    (hq : q ∈ closure H) :
    ∃ z ∈ closure (cayley '' C) \ {b}, Ψ z = q ∧ Tendsto c.2.1 (𝓝[H] q) (𝓝 (cayleyInv z)) := by
  obtain ⟨z, hzK, hΨz, hlim⟩ := tendsto_cayley_inv_of_ext hc hdom hCH hbC hΨc hΨi hΨtop hΨe hq
  refine ⟨z, hzK, hΨz, ?_⟩
  have hz1 : z ≠ 1 := fun h => h1 (h ▸ hzK)
  have hca : ContinuousAt cayleyInv z :=
    QuantumZipper.CA.continuousOn_cayleyInv.continuousAt (isOpen_ne.mem_nhds hz1)
  refine (hca.tendsto.comp hlim).congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
  have hmem : c.2.1 y ∈ C := by rw [← hdom]; exact hc.inv_mem_dom hy
  exact QuantumZipper.CA.cayleyInv_cayley (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (hCH hmem).le)

end Ext

/-! ### The inverse chart of the active component -/

section Active

variable {C : Set ℂ} {c : Chart} {Ψ : ℂ → ℂ} {b : ℂ}

/-- A continuous clamped driver agreeing with `rpath w` on `[0, t₂]` for some `t₂ > t`. -/
theorem exists_clamp_eqOn {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    ∃ (W : ℝ → ℝ) (t₂ : ℝ), Continuous W ∧ W 0 = 0 ∧ (t : ℝ) < t₂ ∧ EqOn W (Ito.rpath w) (Icc 0 t₂) := by
  obtain ⟨t₂, htt₂, ht₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  refine ⟨Ito.clampDrv (Ito.rpath w) t₂, t₂, Ito.continuous_clampDrv t₂.coe_nonneg (Ito.continuousOn_rpath hw ht₂ζ),
    ?_, by exact_mod_cast htt₂, Ito.clampDrv_eqOn⟩
  rw [Ito.clampDrv_eqOn (W := Ito.rpath w) ⟨le_rfl, t₂.coe_nonneg⟩]
  show w (0 : ℝ).toNNReal = 0
  rw [Real.toNNReal_zero, hw0]

/-- **The inverse chart of the active component has boundary limits.** For a conformal pocket chart with boundary map
`Ψ` as in `tendsto_inv_of_ext`, a segment curve `γ'` (the mapped segment) and `t < capLife γ'`, at every `x ∈ ℍ̄`
the inverse chart `pocketInv c (segDriver γ') t` converges from `ℍ`, to `cayleyInv z` for a point `z ≠ b` of the
closed Cayley image of the pocket. -/
theorem exists_tendsto_pocketInv (hc : c.IsConformal) (hdom : (c.dom : Set ℂ) = C) (hCH : C ⊆ H)
    (hbC : b ∉ cayley '' C) (hΨc : ContinuousOn Ψ (closure (cayley '' C) \ {b}))
    (hΨi : InjOn Ψ (closure (cayley '' C) \ {b}))
    (hΨtop : Tendsto (fun x => ‖Ψ x‖) (𝓝[closure (cayley '' C) \ {b}] b) atTop)
    (hΨe : ∀ x ∈ C, c.1 x = Ψ (cayley x)) (h1 : (1 : ℂ) ∉ closure (cayley '' C) \ {b}) {γ' : ℝ → ℂ}
    (hΓ : Lemma71C.IsSegCurve γ') {t : ℝ≥0} (ht : (t : ℝ≥0∞) < Lemma71C.capLife γ') {x : ℂ} (hx : x ∈ Hbar) :
    ∃ z ∈ closure (cayley '' C) \ {b},
      Tendsto (pocketInv c (fun s => Lemma71C.segDriver γ' s) t) (𝓝[H] x) (𝓝 (cayleyInv z)) := by
  set w : ℝ≥0 → ℝ := fun s => Lemma71C.segDriver γ' s with hwdef
  have hw : ContinuousOn w {s | (s : ℝ≥0∞) < Lemma71C.capLife γ'} := hΓ.segDriver_spec.2.1
  have hw0 : w 0 = 0 := hΓ.segDriver_spec.1
  obtain ⟨W, t₂, hW, hW0, htt₂, hEq⟩ := exists_clamp_eqOn hw hw0 ht
  have hc' := hc.loewner hW hW0 t.coe_nonneg
  have hf : ∀ z, QuantumZipper.fwdMap W t z = QuantumZipper.fwdMap (Ito.rpath w) t z := fun z =>
    Ito.fwdMap_congr_of_eqOn_of_le hEq htt₂.le
  have hK : QuantumZipper.fwdHull W t = QuantumZipper.fwdHull (Ito.rpath w) t :=
    InteractingSLE.fwdHull_eq_of_eqOn t.coe_nonneg htt₂ fun r hr => hEq hr
  have h1c : (c.loewner W t).1 = pocketFwd c w t := funext fun z => hf (c.1 z)
  have hdomc : ((c.loewner W t).dom : Set ℂ) = pocketDom c w t := by
    rw [hc'.coe_dom]
    show (fun z => c.2.1 (QuantumZipper.fwdMapInv W t z)) '' H = c.2.1 '' (H \ QuantumZipper.fwdHull (Ito.rpath w) t)
    rw [← image_image c.2.1 (QuantumZipper.fwdMapInv W t), QuantumZipper.RS.image_fwdMapInv_H hW hW0 t.coe_nonneg,
      hK]
  -- boundary limits of `f_t⁻¹`
  have hF : ∃ q ∈ Hbar, Tendsto (QuantumZipper.fwdMapInv W t) (𝓝[H] x) (𝓝 q) := by
    have : (𝓝[H] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by rwa [closure_H])
    rcases (zero_le (a := t)).eq_or_lt with h0 | hpos
    · subst h0
      refine ⟨x, hx, ?_⟩
      have heq : ∀ y ∈ H, QuantumZipper.fwdMapInv W ((0 : ℝ≥0) : ℝ) y = y := fun y hy => by
        rw [NNReal.coe_zero]; exact fwdMapInv_zero_time hW hW0 hy
      exact (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr'
        (eventually_nhdsWithin_of_forall fun y hy => (heq y hy).symm)
    · have hgen := (PocketTraversal.isDrivenCurve_of_isSegCurve hΓ).isGeneratingTrace (T := (t : ℝ≥0∞)) ht
      have hη := Theorem14.CounterflowRange.isLoewnerTraceLT_of_isGeneratingTrace hgen
      have hη' : IsLoewnerTraceLT W t (fun s : ℝ => PocketTraversal.capTrace γ' s.toNNReal) := by
        refine ⟨hη.1, hη.2.1, fun s hs0 hst => ?_⟩
        rw [← hη.2.2 s hs0 hst]
        exact InteractingSLE.fwdHull_eq_of_eqOn hs0 (hst.trans htt₂) fun r hr => hEq hr
      have hησ : ContinuousOn (fun s : ℝ => PocketTraversal.capTrace γ' s.toNNReal) (Icc 0 (t : ℝ)) :=
        hgen.2.1.comp continuous_real_toNNReal.continuousOn fun s hs =>
          ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)
      have hB := TraceClose.hasBdryLimits_of_isLoewnerTraceLT hη' hW hW0 (NNReal.coe_pos.2 hpos) hησ
      refine ⟨extendFrom H (QuantumZipper.fwdMapInv W t) x, ?_, hB.tendsto hx⟩
      rw [← closure_H]
      exact mem_closure_of_tendsto (hB.tendsto hx) (eventually_nhdsWithin_of_forall fun y hy =>
        QuantumZipper.RS.fwdMapInv_mem_H hW hW0 t.coe_nonneg hy)
  obtain ⟨q, hq, hFq⟩ := hF
  obtain ⟨z, hzK, -, hcz⟩ := tendsto_inv_of_ext hc hdom hCH hbC hΨc hΨi hΨtop hΨe h1 (by rwa [closure_H])
  refine ⟨z, hzK, ?_⟩
  have hl := Theorem14.CounterflowRange.tendsto_loewner_inv (f := fun _ => cayleyInv z) hW hW0 t.coe_nonneg hFq hcz
  refine hl.congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
  exact (pocketInv_eq hc hw hw0 ht hc' h1c hdomc hy).symm

end Active

/-! ### Almost surely, on the pocket construction -/

section Pocket

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {β α γ : Ω → ℝ≥0 → ℂ} {C : Ω → Set ℂ}
  {c : Ω → Chart} {γ' : Ω → ℝ → ℂ}

/-- **Almost surely the inverse chart of the active component has a limit at every point of `ℍ̄`**, at every capacity
time below the terminal one, for the pocket construction of PROVE-LEMMA71K (the boundary map `Ψ`, the closing point
removed; `1` is a wall point only at the wall time `1`, so it is the closing point when it lies in the closed
pocket). -/
theorem ae_exists_tendsto_pocketInv (hpc : Lemma71K.IsPocketConstruction P β α γ C c γ') :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < Lemma71C.capLife (γ' ω) → ∀ x ∈ Hbar, ∃ p : ℂ,
      Tendsto (pocketInv (c ω) (fun s => Lemma71C.segDriver (γ' ω) s) t) (𝓝[H] x) (𝓝 p) := by
  obtain ⟨hC, -, hconf, hdom, -, -, -, -, -, -, hseg, -, hΨ⟩ := hpc
  filter_upwards [hΨ] with ω ⟨a', b', Ψ, hmp, hΨc, hΨi, _, _, hΨtop, hΨe, _⟩ t ht x hx
  have hCH : C ω ⊆ H := (hC ω).2.2.2
  have hopen : IsOpen (cayley '' C ω) :=
    SmallGammaGeodesics.CC.isOpen_image_conf (hC ω).1
      (QuantumZipper.CA.differentiableOn_cayley_Hbar.mono fun z hz => show (0 : ℝ) ≤ z.im from le_of_lt (hCH hz))
      (QuantumZipper.CA.bijOn_cayley_H.injOn.mono hCH)
  have hbC : Lemma71K.wallPt (α ω) b' ∉ cayley '' C ω := by
    have hf := hmp.2.2.2.2.2.2.1
    rw [hopen.frontier_eq] at hf
    exact hf.2
  have h1 : (1 : ℂ) ∉ closure (cayley '' C ω) \ {Lemma71K.wallPt (α ω) b'} := by
    rintro ⟨h1c, h1b⟩
    have hw1 : Lemma71K.wallPt (α ω) 1 = 1 := WangWu.toDisc_one _
    have hmemI : (1 : ℝ) ∈ {s ∈ Icc (0 : ℝ) 1 | Lemma71K.wallPt (α ω) s ∈ closure (cayley '' C ω)} :=
      ⟨⟨zero_le_one, le_rfl⟩, by rw [hw1]; exact h1c⟩
    rw [hmp.2.2.2.1] at hmemI
    have hb1 : b' = 1 := le_antisymm hmp.2.2.1 hmemI.2
    exact h1b (Set.mem_singleton_iff.2 (by rw [hb1, hw1]))
  obtain ⟨z, -, hz⟩ := exists_tendsto_pocketInv (hconf ω) (hdom ω) hCH hbC hΨc hΨi hΨtop hΨe h1 (hseg ω) ht hx
  exact ⟨_, hz⟩

end Pocket

end InteractingSLE.Sec7.Lemma71M
