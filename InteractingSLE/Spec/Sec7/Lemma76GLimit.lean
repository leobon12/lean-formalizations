/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76GProb

/-!
# Lemma 7.6's chart boundary values: the pathwise limits

Packet PROVE-LEMMA76G (proof of Lemma 7.6, pp. 268–269). Pathwise limits of `(v + 𝔥₀ + χ arg φ′) ∘ ψ` at a real
chart point `w` of G7's retained chart, `v` a harmonic representative of the union mean:

* **untouched real points** (`tendsto_untouched`; p. 268: "Original real boundary intervals carry the original
  data"): local-set decay of the centred mean, the original datum `b(x)` of `𝔥₀` and Aux. 57 for the lift;
* **sides of a prefix** (`tendsto_side`; p. 268–269: "the new-slit germs `∓λ − θ₂χ` … the first path's sides"): the
  union mean minus the single-path range mean tends to `0` (Proposition 3.8 twice), the single-path heights, and
  Aux. 57 for the transition of lifts; the side and the slit bound are hypotheses here, supplied in the assembly by
  `Lemma76GSide`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Sec7

namespace Lemma76G

open LQGMetric (DistOn TestOn)
open LocalSets Sec6 Restart Supp7 Lemma76F SideHeightBox

section Pathwise

variable {Ω : Type*} [MeasurableSpace Ω] {d : RetData Ω}

omit [MeasurableSpace Ω] in
theorem RetData.D_subset_H {ω : Ω} : d.D ω ⊆ H := fun _ hz => hz.1

omit [MeasurableSpace Ω] in
theorem RetData.D_subset_compl_K {ω : Ω} : d.D ω ⊆ H \ (d.K ω ∩ H) := fun _ hz =>
  ⟨hz.1, fun h => hz.2 (mem_fillH_of_mem_closure hz.1 (subset_closure h.1))⟩

/-- **The chart limit at an untouched real point**: the original datum `b(x)`. -/
theorem tendsto_untouched (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {u₀ v : ℂ → ℝ} {χ : ℝ} {b : ℝ → ℝ}
    {J : Finset ℝ} (hu₀ : ∀ y ∉ J, Tendsto u₀ (𝓝[H] ((y : ℝ) : ℂ)) (𝓝 (b y))) {A : Set ℂ} (hA : A = d.K ω ∩ H)
    (hdec : ∀ x : ℝ, (∃ r > 0, Disjoint (ball ((x : ℝ) : ℂ) r) A) → Tendsto v (𝓝[H \ A] ((x : ℝ) : ℂ)) (𝓝 0))
    {w x : ℝ} (hx : d.inv ω w = x) (hxK : ((x : ℝ) : ℂ) ∉ d.K ω) (hxJ : x ∉ J) :
    Tendsto (fun z => v (d.inv ω z) + u₀ (d.inv ω z) + χ * d.lift ω (d.inv ω z)) (𝓝[H] ((w : ℝ) : ℂ))
      (𝓝 (b x)) := by
  obtain ⟨hT, hcl⟩ := RetData.IsMeasGood.tendsto_inv_real hd hE w
  rw [hx] at hT hcl
  obtain ⟨r, hr, hrK⟩ := Metric.isOpen_iff.1 (hd.isCompact_K ω).isClosed.isOpen_compl _ hxK
  have hdis : Disjoint (ball ((x : ℝ) : ℂ) r) (d.K ω) := Set.disjoint_left.2 fun z hz hzK => hrK hz hzK
  have hdisF := Restart.disjoint_ball_fillH_of_mem_closure (hd.isCompact_K ω).isClosed hdis hcl
  have hDA : d.D ω ⊆ H \ A := hA ▸ RetData.D_subset_compl_K
  have h1 := (hdec x ⟨r, hr, hdis.mono_right (hA ▸ inter_subset_left)⟩).comp
    (hT.mono_right (nhdsWithin_mono _ hDA))
  have hTH : Tendsto (d.inv ω) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝[H] ((x : ℝ) : ℂ)) :=
    hT.mono_right (nhdsWithin_mono _ RetData.D_subset_H)
  have h2 := (hu₀ x hxJ).comp hTH
  have h3 := ((RetData.IsMeasGood.tendsto_lift_of_disjoint hd ω hr hdisF).comp hTH).const_mul χ
  have := (h1.add h2).add h3
  simpa only [zero_add, mul_zero, add_zero, Function.comp_def] using this

/-- **The chart limit on a side of a prefix** (the template's `SideHeightBox.tendsto_side_right` with the side and
the single-path height along the approach supplied as hypotheses). -/
theorem tendsto_side (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {γ : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} {q : ℝ≥0}
    (hp : IsPathGood γ ζ x) {W : ℝ≥0 → ℝ} (hg : IsGeneratingTrace W ζ (fun t => γ t - x))
    (hWc : ContinuousOn W {s | (s : ℝ≥0∞) < ζ}) (hW0 : W 0 = 0) (hq : (q : ℝ≥0∞) < ζ) (hq0 : 0 < q)
    (hsub : γ '' Icc 0 q ⊆ d.K ω) {A : Set ℂ} (hA : A ⊆ d.K ω ∩ H) {u₀ v vA : ℂ → ℝ} {χ c : ℝ} {w : ℝ}
    {ρ : ℝ} (hρ : 0 < ρ) (hloc : d.K ω ∩ ball (d.inv ω w) ρ ⊆ γ '' Icc 0 q)
    (hcmp : Tendsto (fun z => v z - vA z) (𝓝[H \ (d.K ω ∩ H ∪ A)] (d.inv ω w)) (𝓝 0)) {y : ℝ}
    (hfy : Tendsto (fun z => physF W q x (d.inv ω z)) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 ((y : ℝ) : ℂ)))
    (hsh : Tendsto (fun z => vA z + u₀ z + χ * (QuantumZipper.logDerivFwd (fun r : ℝ => W r.toNNReal) q (z - x)).im)
      (map (d.inv ω) (𝓝[H] ((w : ℝ) : ℂ))) (𝓝 c)) :
    Tendsto (fun z => v (d.inv ω z) + u₀ (d.inv ω z) + χ * d.lift ω (d.inv ω z)) (𝓝[H] ((w : ℝ) : ℂ))
      (𝓝 c) := by
  obtain ⟨hT, -⟩ := RetData.IsMeasGood.tendsto_inv_real hd hE w
  have hDB : d.D ω ⊆ H \ (d.K ω ∩ H ∪ A) := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    rintro (h | h)
    · exact (RetData.D_subset_compl_K hz).2 h
    · exact (RetData.D_subset_compl_K hz).2 (hA h)
  have h3 := hcmp.comp (hT.mono_right (nhdsWithin_mono _ hDB))
  have h1 := tendsto_map'_iff.1 hsh
  have h2 : Tendsto (fun z => d.lift ω (d.inv ω z) -
      (QuantumZipper.logDerivFwd (fun r : ℝ => W r.toNNReal) q (d.inv ω z - x)).im) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 0) := by
    rw [tendsto_iff_ultrafilter]
    intro U hU
    have hV : ((U.map (d.inv ω) : Ultrafilter ℂ) : Filter ℂ) ≤ 𝓝[d.D ω] (d.inv ω w) := by
      rw [Ultrafilter.coe_map]; exact (map_mono hU).trans hT
    have hfV : Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q (z - x))
        (U.map (d.inv ω) : Ultrafilter ℂ) (𝓝 ((y : ℝ) : ℂ)) := by
      rw [Ultrafilter.coe_map]
      exact tendsto_map'_iff.2 (hfy.mono_left hU)
    have := RetData.IsMeasGood.tendsto_lift_sub hd ω hg hWc hW0 hp.1 hq hq0 hsub hρ hloc _ hV hfV
    rw [Ultrafilter.coe_map] at this
    exact tendsto_map'_iff.1 this
  have hsum := h3.add (h1.add (h2.const_mul χ))
  rw [zero_add, mul_zero, add_zero] at hsum
  refine hsum.congr fun z => ?_
  simp only [Function.comp_apply]
  ring

/-! ### The pathwise assembly -/

/-- **The chart boundary values of the union mean at a disjoint pair** (pathwise): outside the jumps of the word and
the six chart points of the zones, `(v + 𝔥₀ + χ arg φ′) ∘ ψ` tends to the word datum. The inputs are the local
comparisons with the two single-path range means (`hcmp₁`, `hcmp₂`), the single-path side heights with the
transported slit bound (`hsh₁`, `hsh₂`) and the decay of the union mean at untouched real points (`hdec`). -/
theorem exists_finite_tendsto_word (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}
    {x₁ x₂ : ℝ} (hs : IsSetting α ζ₁ x₁ d.u β ζ₂ x₂ d.r (d.fwd ω) (d.inv ω) (d.lift ω))
    (hK : d.K ω = prefixSet α d.u β d.r) {W₁ W₂ : ℝ≥0 → ℝ} (hg₁ : IsGeneratingTrace W₁ ζ₁ (fun t => α t - x₁))
    (hWc₁ : ContinuousOn W₁ {s | (s : ℝ≥0∞) < ζ₁}) (hW0₁ : W₁ 0 = 0)
    (hg₂ : IsGeneratingTrace W₂ ζ₂ (fun t => β t - x₂)) (hWc₂ : ContinuousOn W₂ {s | (s : ℝ≥0∞) < ζ₂})
    (hW0₂ : W₂ 0 = 0) {χ g₁ g₂ g₃ g₄ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {u₀ v vA₁ vA₂ : ℂ → ℝ}
    (hu₀ : ∀ y ∉ J, Tendsto u₀ (𝓝[H] ((y : ℝ) : ℂ)) (𝓝 (b y)))
    (hdec : ∀ x : ℝ, (∃ r > 0, Disjoint (ball ((x : ℝ) : ℂ) r) (d.K ω ∩ H)) →
      Tendsto v (𝓝[H \ (d.K ω ∩ H)] ((x : ℝ) : ℂ)) (𝓝 0))
    (hcmp₁ : ∀ p : ℂ, p ∈ d.K ω ∩ H ∪ {z : ℂ | z.im = 0} → p ∈ α '' Icc 0 d.u ∩ H ∪ {z : ℂ | z.im = 0} →
      (∃ ρ > 0, α '' Icc 0 d.u ∩ H ∩ ball p ρ ⊆ d.K ω ∩ H) → (∃ ρ > 0, d.K ω ∩ H ∩ ball p ρ ⊆ α '' Icc 0 d.u ∩ H) →
      Tendsto (fun z => v z - vA₁ z) (𝓝[H \ (d.K ω ∩ H ∪ α '' Icc 0 d.u ∩ H)] p) (𝓝 0))
    (hcmp₂ : ∀ p : ℂ, p ∈ d.K ω ∩ H ∪ {z : ℂ | z.im = 0} → p ∈ β '' Icc 0 d.r ∩ H ∪ {z : ℂ | z.im = 0} →
      (∃ ρ > 0, β '' Icc 0 d.r ∩ H ∩ ball p ρ ⊆ d.K ω ∩ H) → (∃ ρ > 0, d.K ω ∩ H ∩ ball p ρ ⊆ β '' Icc 0 d.r ∩ H) →
      Tendsto (fun z => v z - vA₂ z) (𝓝[H \ (d.K ω ∩ H ∪ β '' Icc 0 d.r ∩ H)] p) (𝓝 0))
    (hsh₁ : ∀ (p : ℂ) (F : Filter ℂ), F.NeBot → F ≤ 𝓝[H \ fillH (α '' Icc 0 d.u)] p → ∀ y : ℝ,
      Tendsto (physF W₁ d.u x₁) F (𝓝 (y : ℂ)) →
      (0 < y → (∃ (p' : ℂ) (G : Filter ℂ) (y' : ℝ), G.NeBot ∧ G ≤ 𝓝[H \ fillH (α '' Icc 0 d.u)] p' ∧
          Tendsto (physF W₁ d.u x₁) G (𝓝 (y' : ℂ)) ∧ y < y' ∧ p' ∈ H) →
        Tendsto (fun z => vA₁ z + u₀ z + χ * (QuantumZipper.logDerivFwd (fun s : ℝ => W₁ s.toNNReal) d.u
          (z - x₁)).im) F (𝓝 g₄)) ∧
      (y < 0 → (∃ (p' : ℂ) (G : Filter ℂ) (y' : ℝ), G.NeBot ∧ G ≤ 𝓝[H \ fillH (α '' Icc 0 d.u)] p' ∧
          Tendsto (physF W₁ d.u x₁) G (𝓝 (y' : ℂ)) ∧ y' < y ∧ p' ∈ H) →
        Tendsto (fun z => vA₁ z + u₀ z + χ * (QuantumZipper.logDerivFwd (fun s : ℝ => W₁ s.toNNReal) d.u
          (z - x₁)).im) F (𝓝 g₃)))
    (hsh₂ : ∀ (p : ℂ) (F : Filter ℂ), F.NeBot → F ≤ 𝓝[H \ fillH (β '' Icc 0 d.r)] p → ∀ y : ℝ,
      Tendsto (physF W₂ d.r x₂) F (𝓝 (y : ℂ)) →
      (0 < y → (∃ (p' : ℂ) (G : Filter ℂ) (y' : ℝ), G.NeBot ∧ G ≤ 𝓝[H \ fillH (β '' Icc 0 d.r)] p' ∧
          Tendsto (physF W₂ d.r x₂) G (𝓝 (y' : ℂ)) ∧ y < y' ∧ p' ∈ H) →
        Tendsto (fun z => vA₂ z + u₀ z + χ * (QuantumZipper.logDerivFwd (fun s : ℝ => W₂ s.toNNReal) d.r
          (z - x₂)).im) F (𝓝 g₂)) ∧
      (y < 0 → (∃ (p' : ℂ) (G : Filter ℂ) (y' : ℝ), G.NeBot ∧ G ≤ 𝓝[H \ fillH (β '' Icc 0 d.r)] p' ∧
          Tendsto (physF W₂ d.r x₂) G (𝓝 (y' : ℂ)) ∧ y' < y ∧ p' ∈ H) →
        Tendsto (fun z => vA₂ z + u₀ z + χ * (QuantumZipper.logDerivFwd (fun s : ℝ => W₂ s.toNNReal) d.r
          (z - x₂)).im) F (𝓝 g₁)))
    {c₀ : BoundaryWord} (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hc₀J : c₀.jumps = J)
    (hc₀b : ∀ y ∉ J, c₀.fn y = b y) :
    ∃ E : Set ℝ, E.Finite ∧ ∀ w : ℝ, w ∉ E →
      Tendsto (fun z => v (d.inv ω z) + u₀ (d.inv ω z) + χ * d.lift ω (d.inv ω z)) (𝓝[H] ((w : ℝ) : ℂ))
        (𝓝 (((zoneData (d.fwd ω) α d.u β d.r).word c₀ g₁ g₂ g₃ g₄).fn w)) := by
  set z := zoneData (d.fwd ω) α d.u β d.r with hzdef
  have hz := hs.zoneData_good
  set c := z.word c₀ g₁ g₂ g₃ g₄ with hcdef
  set ψ := d.inv ω with hψdef
  have hD : d.D ω = H \ fillH (prefixSet α d.u β d.r) := by
    show H \ fillH (d.K ω) = _
    rw [hK]
  have hB : d.K ω ∩ H = prefixSet α d.u β d.r ∩ H := by rw [hK]
  have hRL := hs.R₂_lt_L₁
  -- the approach to a chart point and the single-path domains
  have happ : ∀ w : ℝ, map ψ (𝓝[H] ((w : ℝ) : ℂ)) ≤ 𝓝[d.D ω] (ψ w) := fun w =>
    (RetData.IsMeasGood.tendsto_inv_real hd hE w).1
  have hne : ∀ w : ℝ, (map ψ (𝓝[H] ((w : ℝ) : ℂ))).NeBot := fun w => (neBot_nhdsWithin_H w).map _
  have hD₁ : d.D ω ⊆ H \ fillH (α '' Icc 0 d.u) := hD ▸ IsSetting.fill₁_subset
  have hD₂ : d.D ω ⊆ H \ fillH (β '' Icc 0 d.r) := hD ▸ IsSetting.fill₂_subset
  have hmemB : ∀ p ∈ prefixSet α d.u β d.r, p ∈ d.K ω ∩ H ∪ {z : ℂ | z.im = 0} := by
    intro p hp
    by_cases hpH : p ∈ H
    · exact Or.inl ⟨hK ▸ hp, hpH⟩
    · right
      have h0 : 0 ≤ p.im := by
        rcases hp with hp | hp
        exacts [hs.im₁ p hp, hs.im₂ p hp]
      exact le_antisymm (not_lt.1 hpH) h0
  -- the first prefix
  have hside₁ : ∀ w : ℝ, z.L₁ < w → w < z.R₁ → w ≠ z.M₁ →
      (w < z.M₁ → Tendsto (fun z' => v (ψ z') + u₀ (ψ z') + χ * d.lift ω (ψ z')) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 g₃)) ∧
      (z.M₁ < w → Tendsto (fun z' => v (ψ z') + u₀ (ψ z') + χ * d.lift ω (ψ z')) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 g₄)) := by
    intro w h1 h2 hwM
    have hα := hs.mem₁_of_mem_Ioo h1 h2
    have hu0 : 0 < d.u := by
      refine pos_iff_ne_zero.2 fun hu => hwM ?_
      have hψw : ψ w = α d.u := by
        obtain ⟨s, hs', hse⟩ := hα
        have : s = d.u := le_antisymm (hu ▸ hs'.2) (hu ▸ zero_le)
        rw [← hse, this]
      exact ofReal_injective (hs.chartPt_tip₁.2.2 w (ofReal_mem_Hbar w) hψw)
    obtain ⟨hlim, hmono, htip⟩ := hs.side₁ hu0 hg₁ hWc₁ hW0₁
    have hM₁ : z.R₂ < z.M₁ := hRL.trans_le hz.L₁_le
    have hwR : z.R₂ < w := hRL.trans h1
    -- the other prefix stays away
    obtain ⟨ρ, hρ, hρβ⟩ := Metric.isOpen_iff.1 hs.isCompact₂.isClosed.isOpen_compl (ψ w)
      (fun h => Set.disjoint_left.1 hs.disj hα h)
    have hloc : d.K ω ∩ ball (ψ w) ρ ⊆ α '' Icc 0 d.u := by
      rintro q ⟨hqK, hqb⟩
      rw [hK] at hqK
      rcases hqK with hq | hq
      · exact hq
      · exact absurd hq (hρβ hqb)
    have hA₁ : α '' Icc 0 d.u ∩ H ⊆ d.K ω ∩ H := fun q hq => ⟨hK ▸ Or.inl hq.1, hq.2⟩
    have hcmp := hcmp₁ (ψ w) (hmemB _ (Or.inl hα)) (by
        by_cases hpH : ψ w ∈ H
        · exact Or.inl ⟨hα, hpH⟩
        · exact Or.inr (le_antisymm (not_lt.1 hpH) (hs.im₁ _ hα)))
      ⟨1, one_pos, fun q hq => hA₁ hq.1⟩ ⟨ρ, hρ, fun q hq => ⟨hloc ⟨hq.1.1, hq.2⟩, hq.1.2⟩⟩
    have hFle : map ψ (𝓝[H] ((w : ℝ) : ℂ)) ≤ 𝓝[H \ fillH (α '' Icc 0 d.u)] (ψ w) :=
      (happ w).trans (nhdsWithin_mono _ hD₁)
    have hfy := hlim w hwR
    have hsh := hsh₁ (ψ w) _ (hne w) hFle _ (tendsto_map'_iff.2 hfy)
    have htend := fun c' (hsh' : Tendsto (fun z => vA₁ z + u₀ z + χ * (QuantumZipper.logDerivFwd
        (fun s : ℝ => W₁ s.toNNReal) d.u (z - x₁)).im) (map ψ (𝓝[H] ((w : ℝ) : ℂ))) (𝓝 c')) =>
      tendsto_side (c := c') hd hE hs.hp₁ hg₁ hWc₁ hW0₁ hs.hpair.1 hu0 (hK ▸ subset_union_left) hA₁ hρ hloc hcmp
        hfy hsh'
    refine ⟨fun hlt => ?_, fun hgt => ?_⟩
    · have hy : bdryVal (physF W₁ d.u x₁) ψ w < 0 := htip ▸ hmono hwR hM₁ hlt
      obtain ⟨w', hw', hw'H⟩ := exists_mem_H_of_forall_mem hs.hp₁ hs.ha hs.ψc hs.ψd hs.ψi
        (fun _ hv => hs.im_nonneg hv) h1 fun t ht => hs.mem₁_of_mem_Ioo ht.1 (ht.2.trans h2)
      have hw'R : z.R₂ < w' := hRL.trans hw'.1
      exact htend _ (hsh.2 hy ⟨ψ w', _, _, hne w', (happ w').trans (nhdsWithin_mono _ hD₁),
        tendsto_map'_iff.2 (hlim w' hw'R), hmono hw'R hwR hw'.2, hw'H⟩)
    · have hy : 0 < bdryVal (physF W₁ d.u x₁) ψ w := htip ▸ hmono hM₁ hwR hgt
      obtain ⟨w', hw', hw'H⟩ := exists_mem_H_of_forall_mem hs.hp₁ hs.ha hs.ψc hs.ψd hs.ψi
        (fun _ hv => hs.im_nonneg hv) h2 fun t ht => hs.mem₁_of_mem_Ioo (h1.trans ht.1) ht.2
      have hw'R : z.R₂ < w' := hwR.trans hw'.1
      exact htend _ (hsh.1 hy ⟨ψ w', _, _, hne w', (happ w').trans (nhdsWithin_mono _ hD₁),
        tendsto_map'_iff.2 (hlim w' hw'R), hmono hwR hw'R hw'.1, hw'H⟩)
  -- the second prefix
  have hside₂ : ∀ w : ℝ, z.L₂ < w → w < z.R₂ →
      (w < z.M₂ → Tendsto (fun z' => v (ψ z') + u₀ (ψ z') + χ * d.lift ω (ψ z')) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 g₁)) ∧
      (z.M₂ < w → Tendsto (fun z' => v (ψ z') + u₀ (ψ z') + χ * d.lift ω (ψ z')) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 g₂)) := by
    intro w h1 h2
    have hβ := hs.mem₂_of_mem_Ioo h1 h2
    have hb0 : 0 < d.r := by
      refine pos_iff_ne_zero.2 fun h => ?_
      have h1 := hs.hpair.2.2.1
      rw [h] at h1
      exact (ne_of_gt (show (0 : ℝ) < (β 0).im from h1)) hs.h0₂
    obtain ⟨hlim, hmono, htip⟩ := hs.side₂ hg₂ hWc₂ hW0₂
    have hM₂ : z.M₂ < z.L₁ := lt_of_le_of_lt hz.M₂_le hRL
    have hwL : w < z.L₁ := h2.trans hRL
    obtain ⟨ρ, hρ, hρα⟩ := Metric.isOpen_iff.1 hs.isCompact₁.isClosed.isOpen_compl (ψ w)
      (fun h => Set.disjoint_left.1 hs.disj h hβ)
    have hloc : d.K ω ∩ ball (ψ w) ρ ⊆ β '' Icc 0 d.r := by
      rintro q ⟨hqK, hqb⟩
      rw [hK] at hqK
      rcases hqK with hq | hq
      · exact absurd hq (hρα hqb)
      · exact hq
    have hA₂ : β '' Icc 0 d.r ∩ H ⊆ d.K ω ∩ H := fun q hq => ⟨hK ▸ Or.inr hq.1, hq.2⟩
    have hcmp := hcmp₂ (ψ w) (hmemB _ (Or.inr hβ)) (by
        by_cases hpH : ψ w ∈ H
        · exact Or.inl ⟨hβ, hpH⟩
        · exact Or.inr (le_antisymm (not_lt.1 hpH) (hs.im₂ _ hβ)))
      ⟨1, one_pos, fun q hq => hA₂ hq.1⟩ ⟨ρ, hρ, fun q hq => ⟨hloc ⟨hq.1.1, hq.2⟩, hq.1.2⟩⟩
    have hFle : map ψ (𝓝[H] ((w : ℝ) : ℂ)) ≤ 𝓝[H \ fillH (β '' Icc 0 d.r)] (ψ w) :=
      (happ w).trans (nhdsWithin_mono _ hD₂)
    have hfy := hlim w hwL
    have hsh := hsh₂ (ψ w) _ (hne w) hFle _ (tendsto_map'_iff.2 hfy)
    have htend := fun c' (hsh' : Tendsto (fun z => vA₂ z + u₀ z + χ * (QuantumZipper.logDerivFwd
        (fun s : ℝ => W₂ s.toNNReal) d.r (z - x₂)).im) (map ψ (𝓝[H] ((w : ℝ) : ℂ))) (𝓝 c')) =>
      tendsto_side (c := c') hd hE hs.hp₂ hg₂ hWc₂ hW0₂ hs.hpair.2.1 hb0 (hK ▸ subset_union_right) hA₂ hρ hloc
        hcmp hfy hsh'
    refine ⟨fun hlt => ?_, fun hgt => ?_⟩
    · have hy : bdryVal (physF W₂ d.r x₂) ψ w < 0 := htip ▸ hmono hwL hM₂ hlt
      obtain ⟨w', hw', hw'H⟩ := exists_mem_H_of_forall_mem hs.hp₂ hs.hb hs.ψc hs.ψd hs.ψi
        (fun _ hv => hs.im_nonneg hv) h1 fun t ht => hs.mem₂_of_mem_Ioo ht.1 (ht.2.trans h2)
      have hw'L : w' < z.L₁ := hw'.2.trans hwL
      exact htend _ (hsh.2 hy ⟨ψ w', _, _, hne w', (happ w').trans (nhdsWithin_mono _ hD₂),
        tendsto_map'_iff.2 (hlim w' hw'L), hmono hw'L hwL hw'.2, hw'H⟩)
    · have hy : 0 < bdryVal (physF W₂ d.r x₂) ψ w := htip ▸ hmono hM₂ hwL hgt
      obtain ⟨w', hw', hw'H⟩ := exists_mem_H_of_forall_mem hs.hp₂ hs.hb hs.ψc hs.ψd hs.ψi
        (fun _ hv => hs.im_nonneg hv) h2 fun t ht => hs.mem₂_of_mem_Ioo (h1.trans ht.1) ht.2
      have hw'L : w' < z.L₁ := hw'.2.trans hRL
      exact htend _ (hsh.1 hy ⟨ψ w', _, _, hne w', (happ w').trans (nhdsWithin_mono _ hD₂),
        tendsto_map'_iff.2 (hlim w' hw'L), hmono hwL hw'L hw'.1, hw'H⟩)
  -- the exceptional set and the case analysis
  refine ⟨(c.jumps : Set ℝ) ∪ {z.L₂, z.M₂, z.R₂, z.L₁, z.M₁, z.R₁},
    (Finset.finite_toSet _).union (toFinite _), fun w hw => ?_⟩
  simp only [mem_union, Finset.mem_coe, mem_insert_iff, mem_singleton_iff, not_or] at hw
  obtain ⟨hwj, hwL₂, hwM₂, hwR₂, hwL₁, hwM₁, hwR₁⟩ := hw
  have hjump : ∀ x : ℝ, z.T x = w → (z.T x ∈ c.jumps) → False := fun x hT h => hwj (hT ▸ h)
  rcases lt_or_gt_of_ne hwL₂ with h | hL₂
  · obtain ⟨he, hx0, hT⟩ := hs.zone₀_of_lt h
    have hu := hs.untouched_of_zone (Or.inl hx0)
    have hxJ : (ψ w).re ∉ J := fun hj => hjump _ hT (ZW.mem_jumps_zone₀ hx0 (hc₀J ▸ hj) hc₀)
    have hval : c.fn w = b (ψ w).re := by
      rw [show c.fn w = c.fn (z.T (ψ w).re) from congrArg c.fn hT.symm, ZW.fn_zone₀ hz hc₀ hx0, hc₀b _ hxJ]
    rw [hval]
    exact tendsto_untouched hd hE hu₀ rfl hdec he (hK ▸ hu.1) hxJ
  rcases lt_or_gt_of_ne hwM₂ with h | hM₂
  · rw [ZW.fn_side₁ hz hc₀ hL₂ h]
    exact (hside₂ w hL₂ (h.trans_le hz.M₂_le)).1 h
  rcases lt_or_gt_of_ne hwR₂ with h | hR₂
  · rw [ZW.fn_side₂ hz hc₀ hM₂ h]
    exact (hside₂ w (lt_of_le_of_lt hz.L₂_le hM₂) h).2 hM₂
  rcases lt_or_gt_of_ne hwL₁ with h | hL₁
  · obtain ⟨he, hx1, hT⟩ := hs.zone₁_of_mem hR₂ h
    have hu := hs.untouched_of_zone (Or.inr (Or.inl hx1))
    have hxJ : (ψ w).re ∉ J := fun hj => hjump _ hT (ZW.mem_jumps_zone₁ hz hx1 (hc₀J ▸ hj) hc₀)
    have hval : c.fn w = b (ψ w).re := by
      rw [show c.fn w = c.fn (z.T (ψ w).re) from congrArg c.fn hT.symm, ZW.fn_zone₁ hz hc₀ hx1, hc₀b _ hxJ]
    rw [hval]
    exact tendsto_untouched hd hE hu₀ rfl hdec he (hK ▸ hu.1) hxJ
  rcases lt_or_gt_of_ne hwM₁ with h | hM₁
  · rw [ZW.fn_side₃ hz hc₀ hL₁ h]
    exact (hside₁ w hL₁ (h.trans_le hz.M₁_le) (ne_of_lt h)).1 h
  rcases lt_or_gt_of_ne hwR₁ with h | hR₁
  · rw [ZW.fn_side₄ hz hc₀ hM₁ h]
    exact (hside₁ w (lt_of_le_of_lt hz.L₁_le hM₁) h (ne_of_gt hM₁)).2 hM₁
  · obtain ⟨he, hx2, hT⟩ := hs.zone₂_of_lt hR₁
    have hu := hs.untouched_of_zone (Or.inr (Or.inr hx2))
    have hxJ : (ψ w).re ∉ J := fun hj => hjump _ hT (ZW.mem_jumps_zone₂ hx2 (hc₀J ▸ hj) hc₀)
    have hval : c.fn w = b (ψ w).re := by
      rw [show c.fn w = c.fn (z.T (ψ w).re) from congrArg c.fn hT.symm, ZW.fn_zone₂ hz hc₀ hx2, hc₀b _ hxJ]
    rw [hval]
    exact tendsto_untouched hd hE hu₀ rfl hdec he (hK ▸ hu.1) hxJ

end Pathwise

end Lemma76G

end Sec7

end InteractingSLE
