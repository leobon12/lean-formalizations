/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3CanonComp
import InteractingSLE.Spec.Supplement.SB2LoFut
import InteractingSLE.Spec.Supplement.GW4LeafPiece
import InteractingSLE.Spec.Supplement.SBLuPath

/-!
# Lemma S3 for the lower walk: the walk bookkeeping of the composed second chart

Worker PROVE-R6-CORNER (Theorem 1.4, Lemma S3 with the roles of the histories exchanged, supplement p. 631).
Deterministic. `Canon.exists_s3_geometry_lower` needs, for the second history `β₀([0, t_R + b])` (a proper
parametrization of the lower walk), the bookkeeping identities relating `β₀` to the staged run: the fill identity with
`P ∪ ĝ(α[0, q])`, the inclusion of the cut piece, and that interior boundary values of the old chart lie on the
prefix. This file proves them from GW1's per-step facts, using PROVE-SB2-LIFTSET's future parts (`Lk.FutPart`,
`Lk.futPart_run`):

* `image_Icc_eq_of_split`: a split `range β₀ = P ∪ T` at `β₀(τ)` (`T` preconnected, unbounded, meeting `P` only there,
  `P` preconnected through `0`) gives `β₀([0, τ]) = P`;
* `boundary_mem_of_mem_H`: interior boundary values of a domain chart of `ℍ ∖ fill P₀` lie on `P₀`;
* `split_of_futPart`; **`exists_s3_geometry_lower_of_split`**: the lower-orientation geometry with the bookkeeping
  premises replaced by one split;
* **`futPart_cut`**: the old part plus a simple launched piece cut at chart time `q` is a future part at the cut point
  (the tip set is `ĝ(α[0, S])`, `CounterflowRange.tipSet_stopped_eq_of_tendsto`; the trace is unique,
  `GW4Leaf.eqOn_of_isGeneratingTrace`; injectivity separates the two halves); **`futPart_cut_run`**: along the run;
* **`walk_second_chart_inputs`**: for the actual walk (done at `N`, `β₀` a proper parametrization of its physical set,
  a piece launched at `j < N`), the run-chart package, `0 ∈ P`, preconnectedness, and the split at every cut —
  every premise of `exists_s3_geometry_lower_of_split` except finite fibres; `walk_finite_fibre`: those
  (`LuM.pinv_prefix_walk`, with GW1's tip coordinates and injective traces).

R48 (as amended for Theorem 1.4): nothing here uses Theorem 1.4 or `Theorem14Statement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv)

namespace InteractingSLE.Theorem14.SB.S3.Walk

open Geo Canon
open Supp9B (IsProperCurve leftSide rightSide closedRightSide)

/-- **A split of the range of a proper curve at one of its points is its initial arc.** If the range of a proper curve
`β₀` from `0` is `P ∪ T`, with `T` preconnected, unbounded, through `β₀(τ)` and meeting `P` only there, and `P`
preconnected through `0` and `β₀(τ)`, then `β₀([0, τ]) = P` (`Lk.subset_head_of_split` for `⊇`, the closed embedding
of `β₀` for `⊆`). -/
theorem image_Icc_eq_of_split {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0) {P T : Set ℂ} {τ : ℝ≥0}
    (hr : range β₀ = P ∪ T) (hTc : IsPreconnected T) (hTu : ¬ Bornology.IsBounded T) (hτT : β₀ τ ∈ T)
    (hPT : ∀ z ∈ T, z ∈ P → z = β₀ τ) (hPc : IsPreconnected P) (h0P : (0 : ℂ) ∈ P) (hτP : β₀ τ ∈ P) :
    β₀ '' Icc 0 τ = P := by
  have hPr : P ⊆ range β₀ := by rw [hr]; exact subset_union_left
  have hTr : T ⊆ range β₀ := by rw [hr]; exact subset_union_right
  apply Subset.antisymm
  · have he := Lk.isClosedEmbedding_of_isProperCurve hβ
    have hI : IsPreconnected (β₀ ⁻¹' P) := by
      rw [← he.isInducing.isPreconnected_image, image_preimage_eq_of_subset hPr]; exact hPc
    have h0I : (0 : ℝ≥0) ∈ β₀ ⁻¹' P := by show β₀ 0 ∈ P; rw [hβ0]; exact h0P
    rintro _ ⟨t, ht, rfl⟩
    exact hI.Icc_subset h0I hτP ht
  · have h := Lk.subset_head_of_split hβ hPr hTr hTc hTu hτT
      (fun z hz => by rw [mem_singleton_iff]; exact hPT z hz.2 hz.1)
    intro z hz
    obtain ⟨t, ht, rfl⟩ := h hz
    exact ⟨t, ⟨zero_le, ht⟩, rfl⟩

/-- **Interior boundary values of a domain chart lie on the obstacle**: for a domain chart of `ℍ ∖ fill P₀` (`P₀`
closed) with a continuous boundary map `ĝ`, every real point whose boundary value is in `ℍ` lands on `P₀` (it is a
limit of the domain, not in it, and a bounded component of `ℍ ∖ P₀` cannot touch the unbounded one). -/
theorem boundary_mem_of_mem_H {P₀ : Set ℂ} (hP₀ : IsClosed P₀) {c : Chart} (hD : IsDomainChart (H \ fillH P₀) c)
    {gc : ℂ → ℂ} (hgc : ContinuousOn gc Hbar) (hgi : EqOn gc c.2.1 H) {x : ℝ} (hx : gc x ∈ H) : gc x ∈ P₀ := by
  have hxH : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ ((x : ℂ)).im by simp
  have hxnH : (x : ℂ) ∉ H := fun h => by
    have : (0 : ℝ) < ((x : ℂ)).im := h
    simp at this
  have hnot := Lk.ext_notMem_image hD.isConformal.1 hD.isConformal.injOn hgc hgi hxH hxnH
  rw [hD.image_eq] at hnot
  have hfill : gc x ∈ fillH P₀ := by
    by_contra hn
    exact hnot ⟨hx, hn⟩
  have hne : (𝓝[H] (x : ℂ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact hxH
  have hlim : Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (gc x)) := by
    refine ((hgc x hxH).tendsto.mono_left (nhdsWithin_mono _ fun z hz =>
      le_of_lt (show (0 : ℝ) < z.im from hz))).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz using hgi hz
  have hcl : gc x ∈ closure (H \ fillH P₀) :=
    mem_closure_of_tendsto hlim (eventually_nhdsWithin_of_forall fun z hz => hD.inv_mem hz)
  by_contra hP
  have hP' : gc x ∉ closure P₀ := by rw [hP₀.closure_eq]; exact hP
  rcases hfill.2 with h1 | hbd
  · exact hP' h1
  have hU : IsOpen (H \ closure P₀) := QuantumZipper.isOpen_H.sdiff isClosed_closure
  have hCo : IsOpen (connectedComponentIn (H \ closure P₀) (gc x)) := hU.connectedComponentIn
  have hxC : gc x ∈ connectedComponentIn (H \ closure P₀) (gc x) := mem_connectedComponentIn ⟨hx, hP'⟩
  obtain ⟨w, hwC, hwD⟩ := mem_closure_iff.1 hcl _ hCo hxC
  apply hwD.2
  refine ⟨hwD.1, Or.inr ?_⟩
  rw [← connectedComponentIn_eq hwC]
  exact hbd

/-- A done future part of a walk is a split of the range of every proper parametrization of the walk. -/
theorem split_of_futPart {β₀ : ℝ≥0 → ℂ} {s : ExplState} {P : Set ℂ} {q : ℂ}
    (hβr : range β₀ = GW1Bookkeep.statePhysicalSet 0 s) (hF : Lk.FutPart P q s)
    (hd : Exist.StagedLaw.stStatus s = GW1Conn.stDone) :
    ∃ T : Set ℂ, range β₀ = P ∪ T ∧ IsPreconnected T ∧ ¬ Bornology.IsBounded T ∧ q ∈ T ∧
      ∀ z ∈ T, z ∈ P → z = q := by
  obtain ⟨T, hT, hTc, hqT, hTP, -, hunb⟩ := hF
  exact ⟨T, hβr.trans hT, hTc, hunb hd, hqT, hTP⟩

/-- **The lower-orientation S3 geometry from a split of the walk** (`exists_s3_geometry_lower` with its bookkeeping
premises replaced by one split of the range of `β₀` at the cut point: `range β₀ = (P ∪ ĝ(α[0, q])) ∪ T`, `T`
preconnected, unbounded, through `ĝ(α(q))` and meeting `P ∪ ĝ(α[0, q])` only there — e.g. a done `Lk.FutPart` of the
actual walk, `split_of_futPart`). Then `β₀([0, t_R + b]) = P ∪ ĝ(α[0, q])` (`image_Icc_eq_of_split`), which gives the
fill identity and the inclusion, and interior boundary values of the old chart lie on `P`
(`boundary_mem_of_mem_H`). -/
theorem exists_s3_geometry_lower_of_split {p : ℝ → ℂ} (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im)
    {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0) (hA : p '' Icc 0 1 ⊆ closedLeftSide β₀)
    {c₀ : Chart} {g : ℂ → ℂ} (hc : IsRightEntryChart (p '' Icc 0 1) (realMax (p '' Icc 0 1)) c₀)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c₀.2.1 H)
    (hgf : ∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite) :
    ∃ (tR : ℝ≥0) (γ : ℝ≥0 → ℂ),
      β₀ tR = realMax (p '' Icc 0 1) ∧ IsProperCurve γ ∧ γ 0 = 0 ∧ (∀ s, g (γ s) = β₀ (tR + s)) ∧
      ∀ a b t : ℝ≥0, t ∈ Ioo a b → β₀ '' Icc (tR + a) (tR + b) ⊆ p '' Icc 0 1 → β₀ (tR + b) ∈ H →
        (γ t).re < 0 ∧ (𝓝[H] (γ t)).NeBot ∧
        Filter.map g (𝓝[H] (γ t)) ≤ 𝓟 (rightSide β₀ ∩ (H \ fillH (p '' Icc 0 1 ∪ β₀ '' Icc 0 (tR + b)))) ∧
        Filter.map g (𝓝[H] (γ t)) ≤ 𝓝[H \ fillH (p '' Icc 0 1 ∪ β₀ '' Icc 0 (tR + b))] (β₀ (tR + t)) ∧
        (∀ S T : Set ℂ, β₀ '' Icc (tR + a) (tR + b) ⊆ S →
          S ⊆ fillH (p '' Icc 0 1 ∪ β₀ '' Icc 0 (tR + b)) → T ⊆ fillH (p '' Icc 0 1 ∪ β₀ '' Icc 0 (tR + b)) →
          ∃ r > 0, Filter.map g (𝓝[H] (γ t)) ≤ 𝓝[FinRel.freeNear T S (β₀ (tR + t)) r] (β₀ (tR + t))) ∧
        ∀ {P : Set ℂ} {c : Chart} {s₁ : ℝ} {gc : ℂ → ℂ} {C : ℝ} {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {α : ℝ≥0 → ℂ}
          {q : ℝ≥0}, IsDomainChart (H \ fillH P) c → IsCompact P → IsHPHull (fillH P) →
          IsMapOut (fillH P) (fun z => c.1 z + (s₁ : ℂ)) → ContinuousOn gc Hbar → EqOn gc c.2.1 H →
          (∀ p ∈ Hbar, ‖gc p - p‖ ≤ C) → (∀ z, (gc ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite) →
          IsGeneratingTrace w ζ α → ContinuousOn w {s | (s : ℝ≥0∞) < ζ} → w 0 = 0 →
          InjOn α {t | (t : ℝ≥0∞) ≤ ζ} → (q : ℝ≥0∞) < ζ → 0 < q → α q ∈ H →
          (0 : ℂ) ∈ P → IsPreconnected (P ∪ gc '' (α '' Icc 0 q)) → β₀ (tR + b) = gc (α q) →
          (∃ T : Set ℂ, range β₀ = (P ∪ gc '' (α '' Icc 0 q)) ∪ T ∧ IsPreconnected T ∧
            ¬ Bornology.IsBounded T ∧ gc (α q) ∈ T ∧ ∀ z ∈ T, z ∈ P ∪ gc '' (α '' Icc 0 q) → z = gc (α q)) →
          IsMapOut (fillH (β₀ '' Icc 0 (tR + b)))
              (fun z => fwdMap (fun r : ℝ => w r.toNNReal) q (c.1 z) + ((w q + s₁ : ℝ) : ℂ)) ∧
            ∃ y : ℝ, 0 < y ∧ gc (extendFrom H (fwdMapInv (fun r : ℝ => w r.toNNReal) q) y) = β₀ (tR + t) ∧
              Tendsto (fun z => fwdMap (fun r : ℝ => w r.toNNReal) q (c.1 z) + ((w q + s₁ : ℝ) : ℂ))
                (Filter.map g (𝓝[H] (γ t))) (𝓝[H] ((y + (w q + s₁) : ℝ) : ℂ)) ∧
              ∃ r > 0, Disjoint (ball ((y + (w q + s₁) : ℝ) : ℂ) r)
                ((fun z => fwdMap (fun r : ℝ => w r.toNNReal) q (c.1 z) + ((w q + s₁ : ℝ) : ℂ)) ''
                  (fillH (p '' Icc 0 1 ∪ β₀ '' Icc 0 (tR + b)) \ fillH (β₀ '' Icc 0 (tR + b))))
    := by
  obtain ⟨tR, γ, htR, hγ, hγ0, hlift, hall⟩ := exists_s3_geometry_lower hp hp0 hpH hβ hβ0 hA hc hgc hgi hgf
  refine ⟨tR, γ, htR, hγ, hγ0, hlift, fun a b t ht harc hqH => ?_⟩
  obtain ⟨hneg, hne, hFR, hFJ, hacc, hsec⟩ := hall a b t ht harc hqH
  refine ⟨hneg, hne, hFR, hFJ, hacc, fun {P c s₁ gc C w ζ α q} hD hPc hPh hmo₁ hgc' hgi' hC hgf' hα hw hw0 hinj
    hq hq0 hαq h0P hPc' htip hsplit => ?_⟩
  obtain ⟨T, hr, hTc, hTu, hqT, hTP⟩ := hsplit
  have hqmem : gc (α q) ∈ P ∪ gc '' (α '' Icc 0 q) := Or.inr ⟨α q, ⟨q, ⟨zero_le, le_rfl⟩, rfl⟩, rfl⟩
  have heq := image_Icc_eq_of_split hβ hβ0 hr hTc hTu (htip ▸ hqT) (htip ▸ hTP) hPc' (Or.inl h0P)
    (htip ▸ hqmem)
  refine hsec hD hPc hPh hmo₁ hgc' hgi' hC hgf' hα hw hw0 hinj hq hq0 hαq (by rw [heq]) htip
    (by rw [heq]; exact subset_union_right) fun x hx => ?_
  rw [heq]
  exact Or.inl (boundary_mem_of_mem_H hPc.isClosed hD hgc' hgi' hx)

section Cut

open Exist Exist.Staged Exist.StagedLaw GW1Bookkeep GW1W

/-- **The cut of a launched piece at an intermediate time is a future part** (deterministic). At a launch from an
unfinished state `s` whose new piece is simple (`PieceSimpleAt`: it meets the old physical part only at its seed),
for the continuous boundary map `ĝ` of the launch chart and the piece's generating trace `α`, the old physical part
together with the piece up to `q` is split from the rest of the piece at `ĝ(α(q))`: the tip set is `ĝ(α[0, S])`
(`CounterflowRange.tipSet_stopped_eq_of_tendsto`), `α` is the piece's own trace (`GW4Leaf.eqOn_of_isGeneratingTrace`),
and the injectivity of the physical piece separates `[0, q]` from `[q, S]`. -/
theorem futPart_cut {s : ExplState} (hnd : stStatus s ≠ stDone) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ)
    (hP : PieceSimpleAt (stChart s) D.1 D.2 (statePhysicalSet 0 s) (stPt s) (stPt (ExplState.launch s k D θ ⊤)))
    {gc : ℂ → ℂ} (hgc : ContinuousOn gc Hbar) (hgi : EqOn gc (stChart s).2.1 H)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace D.1 D.2 α) {q : ℝ≥0} (hq : (q : ℝ≥0∞) ≤ D.2) :
    Lk.FutPart (statePhysicalSet 0 s ∪ gc '' (α '' Icc 0 q)) (gc (α q)) (ExplState.launch s k D θ ⊤) := by
  obtain ⟨f, α₀, C, hf, hC, -, hW0, hWc, hgen, htr, hinj, hstart, hend, hmeet⟩ := hP
  set X : Set ℝ≥0 := {t : ℝ≥0 | (t : ℝ≥0∞) ≤ D.2} with hX
  have hWc' : ContinuousOn D.1 {t : ℝ≥0 | (t : ℝ≥0∞) < D.2} :=
    hWc.mono fun t (ht : (t : ℝ≥0∞) < D.2) => show (t : ℝ≥0∞) ≤ D.2 from le_of_lt ht
  have hαH : ∀ t ∈ X, α t ∈ Hbar := fun t ht => Sec7.IsGeneratingTrace.mem_Hbar hα hWc' hW0 ht
  have hfg : ∀ p ∈ Hbar, gc p = f p := by
    intro p hp
    have hne : (𝓝[H] p).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact hp
    have h1 : Tendsto (stChart s).2.1 (𝓝[H] p) (𝓝 (gc p)) := by
      refine ((hgc p hp).tendsto.mono_left (nhdsWithin_mono _ fun z hz =>
        le_of_lt (show (0 : ℝ) < z.im from hz))).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz using hgi hz
    exact tendsto_nhds_unique h1 (hf p hp)
  have hαeq : ∀ t ∈ X, α t = α₀ t := fun t ht => GW4Leaf.eqOn_of_isGeneratingTrace hgen hα hWc' hW0 t ht
  have hphys : ∀ t ∈ X, gc (α t) = f (α₀ t) := fun t ht => by rw [hfg _ (hαH t ht), hαeq t ht]
  have htip : (stChart s).tipSet (fun r => D.1 (min (r : ℝ≥0∞) D.2).toNNReal) D.2 = gc '' (α '' X) :=
    CounterflowRange.tipSet_stopped_eq_of_tendsto hα hWc hW0 fun t ht => by
      rw [hfg _ (hαH t ht)]; exact hf _ (hαH t ht)
  have hset := GW1WalkChain.statePhysicalSet_launch 0 s k D θ ⊤
  simp only [min_top_left] at hset
  rw [htip] at hset
  set Y : Set ℝ≥0 := {t : ℝ≥0 | q ≤ t ∧ (t : ℝ≥0∞) ≤ D.2} with hY
  have hYX : Y ⊆ X := fun t ht => ht.2
  have hIX : Icc 0 q ⊆ X := fun t ht => (ENNReal.coe_le_coe.2 ht.2).trans hq
  have hqY : q ∈ Y := ⟨le_rfl, hq⟩
  have hYc : IsPreconnected Y := by
    have : Y.OrdConnected := ⟨fun x hx y hy z hz => ⟨hx.1.trans hz.1, (ENNReal.coe_le_coe.2 hz.2).trans hy.2⟩⟩
    exact this.isPreconnected
  have hcont : ContinuousOn (fun t => gc (α t)) X := hgc.comp hα.2.1 fun t ht => hαH t ht
  have hinj' : InjOn (fun t => gc (α t)) X := fun t ht t' ht' he => by
    have : f (α₀ t) = f (α₀ t') := by rw [← hphys t ht, ← hphys t' ht']; exact he
    exact hinj ht ht' this
  refine ⟨gc '' (α '' Y), ?_, ?_, ⟨α q, ⟨q, hqY, rfl⟩, rfl⟩, ?_, ?_, ?_⟩
  · rw [hset, union_assoc]
    congr 1
    ext z
    constructor
    · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      rcases le_total t q with htq | hqt
      · exact Or.inl ⟨α t, ⟨t, ⟨zero_le, htq⟩, rfl⟩, rfl⟩
      · exact Or.inr ⟨α t, ⟨t, ⟨hqt, ht⟩, rfl⟩, rfl⟩
    · rintro (⟨_, ⟨t, ht, rfl⟩, rfl⟩ | ⟨_, ⟨t, ht, rfl⟩, rfl⟩)
      · exact ⟨α t, ⟨t, hIX ht, rfl⟩, rfl⟩
      · exact ⟨α t, ⟨t, hYX ht, rfl⟩, rfl⟩
  · rw [image_image]; exact hYc.image _ (hcont.mono hYX)
  · rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩ hzP
    rcases hzP with hold | ⟨_, ⟨t', ht', rfl⟩, he⟩
    · have hmem : gc (α t) ∈ (stChart s).tipSet (fun r => D.1 (min (r : ℝ≥0∞) D.2).toNNReal) D.2 ∩
          statePhysicalSet 0 s := ⟨by rw [htip]; exact ⟨α t, ⟨t, hYX ht, rfl⟩, rfl⟩, hold⟩
      rw [hmeet, mem_singleton_iff, ← hphys 0 (show ((0 : ℝ≥0) : ℝ≥0∞) ≤ D.2 from by simp)] at hmem
      have ht0 : t = 0 := hinj' (hYX ht) (show ((0 : ℝ≥0) : ℝ≥0∞) ≤ D.2 by simp) hmem
      have hq0 : q = 0 := le_antisymm (ht0 ▸ ht.1) zero_le
      rw [ht0, hq0]
    · have htt : t' = t := hinj' (hIX ht') (hYX ht) he
      have hq' : t = q := le_antisymm (htt ▸ ht'.2) ht.1
      rw [hq']
  · intro hnd'
    by_cases htop : D.2 = ⊤
    · exact absurd (launch_eq_of_top (s := s) (k := k) (θ := θ) (d := D) (t := ⊤)
        (by simp only [htop, min_self])).2.2.2.2.1 hnd'
    · have hS : ((D.2.toNNReal : ℝ≥0) : ℝ≥0∞) = D.2 := ENNReal.coe_toNNReal htop
      have hSX : D.2.toNNReal ∈ Y := ⟨by rw [← ENNReal.coe_le_coe, hS]; exact hq, hS.le⟩
      rw [← hend htop, ← hphys _ (hYX hSX)]
      exact ⟨α _, ⟨_, hSX, rfl⟩, rfl⟩
  · intro hdone hbd
    by_cases htop : D.2 = ⊤
    · obtain ⟨M, hM⟩ := hbd.subset_closedBall 0
      obtain ⟨t, ht⟩ := ((htr htop).eventually (eventually_gt_atTop (max (M + C) 0))).and
        (eventually_ge_atTop q) |>.exists
      have htY : t ∈ Y := ⟨ht.2, by rw [htop]; exact le_top⟩
      have h1 := hM ⟨α t, ⟨t, htY, rfl⟩, rfl⟩
      rw [mem_closedBall_zero_iff, hphys t (hYX htY)] at h1
      have h2 := hC (α₀ t) (by rw [← hαeq t (hYX htY)]; exact hαH t (hYX htY))
      have h3 := norm_sub_norm_le (α₀ t) (α₀ t - f (α₀ t))
      rw [sub_sub_cancel, norm_sub_rev] at h3
      have := lt_of_le_of_lt (le_max_left _ _) ht.1
      linarith
    · have hnd' : stStatus (ExplState.launch s k D θ ⊤) ≠ stDone := by
        obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
        simp only [ExplState.launch, min_top_left, htop, ↓reduceIte, not_top_lt]
        split_ifs <;> try (intro heq; cases heq)
        all_goals (rcases status with _ | _ | _ | _ | _ | _ <;> intro heq <;> cases heq)
      exact absurd hdone hnd'

end Cut

section CutRun

open Exist Exist.Staged Exist.StagedLaw GW1Bookkeep GW1W

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ} {right : Bool} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The cut of a launched walk piece stays a future part along the run** (GW1's per-step facts: piece simplicity
and connector clearance, the hypotheses of `Lk.futPart_run`). -/
theorem futPart_cut_run
    (hP : ∀ k c θ',
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k = some (c, θ') →
      (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) : ℂ) ∈
        statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) →
      PieceSimpleAt c (D k).1 (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2)
        (statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k))
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k))
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1))))
    (hC : GW1WalkChain.WalkConnectorClearance (κ := κ) (b := b) (jumps := jumps)
      (boundaryWalkSpec b jumps θ right) D)
    {j : ℕ} {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (j + 1)).2.2.2.1 j = some (c, θ'))
    {gc : ℂ → ℂ} (hgc : ContinuousOn gc Hbar) (hgi : EqOn gc c.2.1 H)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (D j).1 (D j).2 α) {q : ℝ≥0} (hq : (q : ℝ≥0∞) ≤ (D j).2) :
    ∀ N, j + 1 ≤ N → Lk.FutPart
      (statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D j) ∪ gc '' (α '' Icc 0 q))
      (gc (α q)) (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D N) := by
  set spec := boundaryWalkSpec b jumps θ right with hspec
  have hn : (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j ≠ none := by
    rw [hl]; exact Option.some_ne_none _
  have hnd : stStatus (ExplState.run κ b jumps spec D j) ≠ stDone := Lx.stStatus_ne_done_of_launches spec D hl
  have hpt := (Lk.prefix_facts hP hC j).2 hnd
  have hpiece := hP j c θ' hl hpt
  have heq := GW1W.launch_walk hn
  obtain ⟨hev, hlen⟩ := GW1W.even_of_launches_walk hn
  have htime : instrTime spec j = ⊤ := by
    simp only [spec, instrTime, GW1Conn.getElem?_boundaryWalkSpec, hlen, hev, ↓reduceIte]
  obtain ⟨_, _, hc⟩ := eq_launch_of_launches spec D hl
  rw [htime, min_top_left, hc, heq] at hpiece
  have hgi' : EqOn gc (stChart (ExplState.run κ b jumps spec D j)).2.1 H := by
    rw [show stChart (ExplState.run κ b jumps spec D j) = c from hc.symm]; exact hgi
  have h₀ := futPart_cut hnd j (D j) θ hpiece hgc hgi' hα hq
  rw [← heq] at h₀
  exact fun N hN => Lk.futPart_run hP hC h₀ N hN

/-- **All second-chart inputs of the lower-orientation S3 geometry for the actual walk** (deterministic). For a walk
run with regular launched pieces and GW1's per-step facts, done at `N`, a proper parametrization `β₀` of its physical
set, and a piece launched at `j < N`: the prefix `P` before the piece has the run-chart package
(`Canon.runChart_package`), contains `0`, and for the piece's generating trace `α` and every chart time `q` up to its
lifetime, `P ∪ ĝ(α[0, q])` is preconnected and the range of `β₀` splits at `ĝ(α(q))` — the premises of
`exists_s3_geometry_lower_of_split` other than the boundary map's finite fibres. -/
theorem walk_second_chart_inputs
    (hP : ∀ k c θ',
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k = some (c, θ') →
      (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) : ℂ) ∈
        statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) →
      PieceSimpleAt c (D k).1 (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2)
        (statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k))
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k))
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1))))
    (hC : GW1WalkChain.WalkConnectorClearance (κ := κ) (b := b) (jumps := jumps)
      (boundaryWalkSpec b jumps θ right) D)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k =
        some (c, θ') → GW1P.PieceRegular (D k).1 (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2))
    {N : ℕ} (hdN : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D N) = stDone)
    {β₀ : ℝ≥0 → ℂ}
    (hβr : range β₀ = statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D N))
    {j : ℕ} {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (j + 1)).2.2.2.1 j = some (c, θ'))
    (hjN : j < N) :
    ∃ (s₁ : ℝ) (gc : ℂ → ℂ) (Cg : ℝ),
      IsDomainChart
        (H \ fillH (statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D j))) c ∧
      IsCompact (statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D j)) ∧
      IsHPHull (fillH (statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D j))) ∧
      IsMapOut (fillH (statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D j)))
        (fun z => c.1 z + (s₁ : ℂ)) ∧
      ContinuousOn gc Hbar ∧ EqOn gc c.2.1 H ∧
      (∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ ∀ w : ℂ, 0 ≤ w.im → ‖w‖ ≤ C₁ * ‖gc w‖ + C₂) ∧
      (∀ p ∈ Hbar, ‖gc p - p‖ ≤ Cg) ∧
      (0 : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D j) ∧
      ∀ α : ℝ≥0 → ℂ, IsGeneratingTrace (D j).1 (D j).2 α → ∀ q : ℝ≥0, (q : ℝ≥0∞) ≤ (D j).2 →
        IsPreconnected (statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D j) ∪
          gc '' (α '' Icc 0 q)) ∧
        ∃ T : Set ℂ, range β₀ =
            (statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D j) ∪
              gc '' (α '' Icc 0 q)) ∪ T ∧ IsPreconnected T ∧ ¬ Bornology.IsBounded T ∧ gc (α q) ∈ T ∧
          ∀ z ∈ T, z ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D j) ∪
            gc '' (α '' Icc 0 q) → z = gc (α q) := by
  set spec := boundaryWalkSpec b jumps θ right with hspec
  have hnd : stStatus (ExplState.run κ b jumps spec D j) ≠ stDone := Lx.stStatus_ne_done_of_launches spec D hl
  obtain ⟨_, _, hc⟩ := eq_launch_of_launches spec D hl
  obtain ⟨s₁, gc, Cg, hD, hPc, hPh, hmo, hgc, hgi, hgb, -, hC'⟩ := Canon.runChart_package spec D hreg j hnd
  have hPP : prefixPhysSet κ b jumps spec D j = statePhysicalSet 0 (ExplState.run κ b jumps spec D j) := rfl
  rw [hPP] at hD hPc hPh hmo
  have hcs : stChart (ExplState.run κ b jumps spec D j) = c := hc.symm
  rw [hcs] at hD hmo hgi
  refine ⟨s₁, gc, Cg, hD, hPc, hPh, hmo, hgc, hgi, hgb, hC', Or.inl (Or.inl rfl), fun α hα q hq => ?_⟩
  have hF := futPart_cut_run hP hC hl hgc hgi hα hq N hjN
  obtain ⟨T, hr, hTc, hTu, hqT, hTP⟩ := split_of_futPart hβr hF hdN
  refine ⟨?_, T, hr, hTc, hTu, hqT, hTP⟩
  -- the prefix and the cut piece are preconnected through the seed
  have hpre := (Lk.prefix_facts hP hC j).1
  have hpt := (Lk.prefix_facts hP hC j).2 hnd
  have hpiece := hP j c θ' hl hpt
  have hn : (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j ≠ none := by
    rw [hl]; exact Option.some_ne_none _
  obtain ⟨hev, hlen⟩ := GW1W.even_of_launches_walk hn
  have htime : instrTime spec j = ⊤ := by
    simp only [spec, instrTime, GW1Conn.getElem?_boundaryWalkSpec, hlen, hev, ↓reduceIte]
  rw [htime, min_top_left] at hpiece
  obtain ⟨f, α₀, C, hf, -, -, hW0, hWc, hgen, -, -, hstart, -, -⟩ := hpiece
  have hWc' : ContinuousOn (D j).1 {t : ℝ≥0 | (t : ℝ≥0∞) < (D j).2} :=
    hWc.mono fun t (ht : (t : ℝ≥0∞) < (D j).2) => show (t : ℝ≥0∞) ≤ (D j).2 from le_of_lt ht
  have h0X : ((0 : ℝ≥0) : ℝ≥0∞) ≤ (D j).2 := by simp
  have hα0H : α 0 ∈ Hbar := Sec7.IsGeneratingTrace.mem_Hbar hα hWc' hW0 h0X
  have hseed : gc (α 0) = (stPt (ExplState.run κ b jumps spec D j) : ℂ) := by
    have hne : (𝓝[H] (α 0)).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact hα0H
    have h1 : Tendsto c.2.1 (𝓝[H] (α 0)) (𝓝 (gc (α 0))) := by
      refine ((hgc _ hα0H).tendsto.mono_left (nhdsWithin_mono _ fun z hz =>
        le_of_lt (show (0 : ℝ) < z.im from hz))).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz using hgi hz
    have h2 := tendsto_nhds_unique h1 (hf _ hα0H)
    rw [h2, ← hstart, GW4Leaf.eqOn_of_isGeneratingTrace hgen hα hWc' hW0 0 h0X]
  have hIc : IsPreconnected (gc '' (α '' Icc 0 q)) := by
    rw [image_image]
    refine isPreconnected_Icc.image _ (hgc.comp (hα.2.1.mono fun t ht => (ENNReal.coe_le_coe.2 ht.2).trans hq)
      fun t ht => Sec7.IsGeneratingTrace.mem_Hbar hα hWc' hW0 ((ENNReal.coe_le_coe.2 ht.2).trans hq))
  refine hpre.union _ hpt ⟨α 0, ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩, hseed⟩ hIc
  
end CutRun

open Exist.Staged Exist.StagedLaw GW1Bookkeep in
/-- **The walk's run chart has finite fibres** at every unfinished state (regular launches, injective traces and GW1's
tip coordinates: the prefix is a finite-fibre path, `LuM.pinv_prefix_walk`, `Lk.finite_fibre_of_pinv`). With
`walk_second_chart_inputs` and `exists_s3_geometry_lower_of_split` this supplies every second-chart input of the
lower-orientation S3 geometry for the actual walk. -/
theorem walk_finite_fibre {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ} {right : Bool}
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : LuM.RegLaunches κ b jumps (boundaryWalkSpec b jumps θ right) D)
    (hinj : ∀ j, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (j + 1)).2.2.2.1 j ≠ none →
      InjOn (LuM.trOf (D j)) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D j).2})
    (htip : GW1WalkChain.WalkTipCoordinates κ b jumps (boundaryWalkSpec b jumps θ right) D) {j : ℕ}
    (hnd : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D j) ≠ stDone) {c : Chart}
    (hD : IsDomainChart
      (H \ fillH (statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D j))) c)
    {gc : ℂ → ℂ} (hgc : ContinuousOn gc Hbar) (hgi : EqOn gc c.2.1 H)
    (hgb : ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ ∀ w : ℂ, 0 ≤ w.im → ‖w‖ ≤ C₁ * ‖gc w‖ + C₂) :
    ∀ z, (gc ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite :=
  Lk.finite_fibre_of_pinv (LuM.pinv_prefix_walk hreg hinj htip le_rfl j hnd).1 hD hgc hgi hgb

end InteractingSLE.Theorem14.SB.S3.Walk
