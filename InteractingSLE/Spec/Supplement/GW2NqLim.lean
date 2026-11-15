/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NcEnd

/-!
# At a first contact the relative trace has a finite limit or tends to `∞` (D84)

Packet PROVE-GW2-NEARIMG2, decision D84 item (1). Setting of `GW2NcRel`: the first root-`x` contact `τ` of `x + γ`
with the retained prefix `α([0, s])`.

**The dichotomy** (`tendsto_or_tendsto_norm_relTr`). The cluster-set lemma (`YuanCharacterisation`) gives a limit `ξ`
of `−1/relBdry(x + γ t)` as `t ↑ τ`, in the fibre of the contact point under the boundary extension `F̄_s` of the
inverse map (`exists_tendsto_inv_relBdry`). If `ξ ≠ 0` the relative trace has the finite limit `−1/ξ − relBdry(x)`.
If `ξ = 0` it tends to `∞`. A contact away from the tip has `ξ ≠ 0`, because `F̄_s(0) = α(s)`. A contact at the tip
can have either. When the tip `α(s)` is a double point of `α`, the fibre of `α(s)` also contains a point `ξ ≠ 0`.

**A finite limit gives the canonical driver** (`exists_canon_of_tendsto`). This is round 3's `exists_canon_of_contact`
with "contact away from the tip" weakened to "a finite limit", which was the only use it made of that hypothesis. The
driver also agrees with the glued driver `cDrv` below the clock (used in `GW2NqTip`). **`CanonContactLimStatement`**
is RELDET's `CanonContactStatement` with the premise `contact ≠ tip` replaced by the finite limit; it is proved
(`canonContactLimStatement`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

universe u

namespace InteractingSLE.Theorem14.GW2Ni

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.CoordB Supp8.GB6.ReadD GW2TipSystem GW2Rz

section Chart

variable {U : ℝ → ℝ} {s : ℝ}

/-- **The fibre form of the cluster-set lemma for the relative chart.** If `−1/P → q` along `l` with `P` in the safe
set, then `−1/relBdry(P)` converges along `l` to a point of the fibre of `q` under the boundary extension of the
inverse map. -/
theorem exists_tendsto_inv_relBdry (hU : Continuous U) (hU0 : U 0 = 0) (hs : 0 ≤ s)
    (hB : HasBdryLimits (fwdMapInv U s))
    (hR : ∀ x : ℂ, x.im = 0 → extendFrom H (fwdMapInv U s) x ∉ extendFrom H (fwdMapInv U s) '' H)
    {ι : Type*} [TopologicalSpace ι] {l : Filter ι} [l.NeBot] {P : ι → ℂ}
    (hconn : ∀ U' ∈ l, ∃ S ∈ l, S ⊆ U' ∧ IsPreconnected S ∧ ContinuousOn P S)
    (hP : ∀ᶠ t in l, P t ∈ relSafe U s ∧ P t ≠ 0) {q : ℂ} (hq : Tendsto (fun t => -(P t)⁻¹) l (𝓝 q)) :
    ∃ ξ : ℂ, extendFrom H (fwdMapInv U s) ξ = q ∧ Tendsto (fun t => -(relBdry U s (P t))⁻¹) l (𝓝 ξ) := by
  obtain ⟨C, hC⟩ := exists_norm_fwdMap_sub_le hU hU0 hs
  set F := extendFrom H (fwdMapInv U s) with hF
  have hext : ∀ v ∈ H, F v = fwdMapInv U s v := fun v hv => extendFrom_fwdMapInv_eq hU hU0 hs hv
  have hd : DifferentiableOn ℂ F H :=
    (QuantumZipper.RS.differentiableOn_fwdMapInv hU hU0 hs).congr fun v hv => hext v hv
  have hinj : InjOn F H := fun a ha b hb hab => by
    rw [hext a ha, hext b hb] at hab
    have := congrArg (fwdMap U s) hab
    rwa [QuantumZipper.RS.fwdMap_fwdMapInv hU hU0 hs ha, QuantumZipper.RS.fwdMap_fwdMapInv hU hU0 hs hb] at this
  set G : ι → ℂ := fun t => -(relBdry U s (P t))⁻¹ with hG
  have hspec : ∀ t, P t ∈ relSafe U s → P t ≠ 0 → relBdry U s (P t) ≠ 0 ∧ G t ∈ Hbar ∧
      ‖G t‖ ≤ ‖(P t)⁻¹‖ + C ∧ F (G t) = -(P t)⁻¹ := fun t h1 h2 => relBdry_spec hU hU0 hs hB hC h1 h2
  have hconnG : ∀ U' ∈ l, ∃ S ∈ l, S ⊆ U' ∧ IsPreconnected S ∧ ContinuousOn G S := by
    intro U' hU'
    obtain ⟨S, hSl, hSU, hSc, hPS⟩ := hconn (U' ∩ {t | P t ∈ relSafe U s ∧ P t ≠ 0}) (inter_mem hU' hP)
    refine ⟨S, hSl, fun t ht => (hSU ht).1, hSc, ?_⟩
    have hB' : ContinuousOn (fun t => relBdry U s (P t)) S :=
      (continuousOn_relBdry hU hU0 hs).comp hPS fun t ht => (hSU ht).2.1
    exact (hB'.inv₀ fun t ht => (hspec t (hSU ht).2.1 (hSU ht).2.2).1).neg
  have hGH : ∀ᶠ t in l, G t ∈ Hbar := hP.mono fun t ht => (hspec t ht.1 ht.2).2.1
  have hnorm : ∀ᶠ t in l, ‖(P t)⁻¹‖ ≤ ‖q‖ + 1 := by
    have h := (hq.norm).eventually (gt_mem_nhds (lt_add_one ‖q‖))
    filter_upwards [h] with t ht
    rw [norm_neg] at ht
    exact ht.le
  have hGR : ∀ᶠ t in l, ‖G t‖ ≤ ‖q‖ + 1 + C := by
    filter_upwards [hP, hnorm] with t ht hn
    exact (hspec t ht.1 ht.2).2.2.1.trans (add_le_add hn le_rfl)
  have hFG : Tendsto (fun t => F (G t)) l (𝓝 q) := by
    refine hq.congr' ?_
    filter_upwards [hP] with t ht
    exact (hspec t ht.1 ht.2).2.2.2.symm
  obtain ⟨ξ, -, hFξ, hGξ⟩ := YuanCharacterisation.exists_tendsto_of_tendsto_comp_filter hd hB.continuousOn hinj hR
    hconnG hGH hGR hFG
  exact ⟨ξ, hFξ, hGξ⟩

end Chart

/-- If `f ≠ 0` eventually and `−1/f → 0`, then `‖f‖ → ∞`. -/
theorem tendsto_norm_of_tendsto_neg_inv_zero {ι : Type*} {l : Filter ι} {f : ι → ℂ} (hf : ∀ᶠ t in l, f t ≠ 0)
    (h : Tendsto (fun t => -(f t)⁻¹) l (𝓝 0)) : Tendsto (fun t => ‖f t‖) l atTop := by
  have h1 : Tendsto (fun t => ‖-(f t)⁻¹‖) l (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa only [norm_zero] using h.norm
    · filter_upwards [hf] with t ht
      exact norm_pos_iff.2 (neg_ne_zero.2 (inv_ne_zero ht))
  refine (tendsto_inv_nhdsGT_zero.comp h1).congr' ?_
  filter_upwards [hf] with t _
  simp only [Function.comp_apply, norm_neg, norm_inv, inv_inv]

section Sample

variable {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
  {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) ⊤ α)
  (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
  {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x) (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1)
  {w : ℝ≥0 → ℝ} (hwc : Continuous w) (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w ⊤ γ)
  {τ : ℝ≥0} (hT : firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
    ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) = (τ : ℝ≥0∞))

include hα hW hW0 hζ hx harc hwc hw0 hγ hT in
/-- **At a first contact the relative trace has a finite limit or tends to `∞`** (at any contact point). -/
theorem tendsto_or_tendsto_norm_relTr :
    (∃ ℓ : ℂ, Tendsto (fun t => relBdry (rdrv (cfRec s W ζ ω)) s ((x : ℂ) + γ t) -
      relBdry (rdrv (cfRec s W ζ ω)) s x) (𝓝[<] τ) (𝓝 ℓ)) ∨
    Tendsto (fun t => ‖relBdry (rdrv (cfRec s W ζ ω)) s ((x : ℂ) + γ t) -
      relBdry (rdrv (cfRec s W ζ ω)) s x‖) (𝓝[<] τ) atTop := by
  have he : IsRegularDriver (w, (⊤ : ℝ≥0∞)) := Gm.isRegularDriver_top hwc hw0
  set U : ℝ → ℝ := Ito.rpath (W · ω) with hUdef
  have hU : Continuous U := hW.comp continuous_real_toNNReal
  have hU0 : U 0 = 0 := by simp only [hUdef, Ito.rpath, Real.toNNReal_zero, hW0]
  have hαS : IsGeneratingTrace (W · ω) (s : ℝ≥0∞) α :=
    ⟨hα.1, hα.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top, fun t ht => hα.2.2 t (ht.trans_le le_top)⟩
  obtain ⟨hB, -⟩ := LoewnerConcat.prefix_boundary hW hW0 hαS
  have hR : ∀ p : ℂ, p.im = 0 → extendFrom H (fwdMapInv U s) p ∉ extendFrom H (fwdMapInv U s) '' H := by
    rintro p hp ⟨q, hq, hpq⟩
    refine LoewnerConcat.extendFrom_real_notMem_bdry hW hW0 hαS hp ?_
    rw [← hpq, extendFrom_fwdMapInv_eq hU hU0 s.coe_nonneg hq]
    exact QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hU hU0 s.coe_nonneg hq
  obtain ⟨C, hC⟩ := exists_norm_fwdMap_sub_le hU hU0 s.coe_nonneg
  have hτ0 : 0 < τ := contact_pos' W ω hα hx harc hγ hT
  have hγc : Continuous γ := continuousOn_univ.1 (hγ.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hαc : Continuous α := continuousOn_univ.1 (hα.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hPc : Continuous fun t => (x : ℂ) + γ t := continuous_const.add hγc
  have hAcpt : IsCompact ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) := by
    have hcompact : IsCompact (α '' Icc 0 s) := isCompact_Icc.image hαc
    simpa only [image_image] using hcompact.image OnePoint.continuous_coe
  have hηc : Continuous fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ) :=
    continuous_sphereInv.comp (OnePoint.continuous_coe.comp hPc)
  obtain ⟨u, -, hpu⟩ := firstContactTime_mem hηc hAcpt.isClosed hT
  have hz := (SourceC.sphereInv_eq_iff _ _).1 hpu.symm
  have hP0τ : (x : ℂ) + γ τ ≠ 0 := fun h => by
    rw [h, zero_mul, zero_add] at hz
    exact one_ne_zero hz
  have : (𝓝[<] τ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hτ0⟩
  have hconn : ∀ U' ∈ 𝓝[<] τ, ∃ S ∈ 𝓝[<] τ, S ⊆ U' ∧ IsPreconnected S ∧
      ContinuousOn (fun t => (x : ℂ) + γ t) S := by
    intro U' hU'
    obtain ⟨l', hl', hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hτ0).1 hU'
    exact ⟨Ioo l' τ, Ioo_mem_nhdsLT hl', hsub, isPreconnected_Ioo, hPc.continuousOn⟩
  have hP : ∀ᶠ t in 𝓝[<] τ, (x : ℂ) + γ t ∈ relSafe U s ∧ (x : ℂ) + γ t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin, ((hPc.tendsto τ).eventually_ne hP0τ).filter_mono nhdsWithin_le_nhds]
      with t ht hne'
    refine ⟨?_, hne'⟩
    have h := RootH29.trace_mem_record_relSafe W ζ ω hα hW hW0 hζ hx harc he hγ (lt_min_of_contact hT ht) le_rfl
    rw [GW2Bh.relSafe_record_eq s hW0 hW hζ] at h
    exact h
  have hq : Tendsto (fun t => -((x : ℂ) + γ t)⁻¹) (𝓝[<] τ) (𝓝 (-((x : ℂ) + γ τ)⁻¹)) :=
    (((hPc.tendsto τ).inv₀ hP0τ).neg).mono_left nhdsWithin_le_nhds
  obtain ⟨ξ, -, hξ⟩ := exists_tendsto_inv_relBdry hU hU0 s.coe_nonneg hB hR hconn hP hq
  have e := GW2Bh.relBdry_record_eq s hW0 hW hζ (W := W) (ζ := ζ) (ω := ω)
  rw [e]
  by_cases hξ0 : ξ = 0
  · right
    rw [hξ0] at hξ
    have hne : ∀ᶠ t in 𝓝[<] τ, relBdry U s ((x : ℂ) + γ t) ≠ 0 :=
      hP.mono fun t ht => (relBdry_spec hU hU0 s.coe_nonneg hB hC ht.1 ht.2).1
    have h := tendsto_norm_of_tendsto_neg_inv_zero hne hξ
    refine tendsto_atTop_mono (fun t => ?_) (tendsto_atTop_add_const_right _ (-‖relBdry U s x‖) h)
    have := norm_sub_norm_le (relBdry U s ((x : ℂ) + γ t)) (relBdry U s x)
    change ‖relBdry U s ((x : ℂ) + γ t)‖ + -‖relBdry U s x‖ ≤ ‖relBdry U s ((x : ℂ) + γ t) - relBdry U s x‖
    linarith
  · left
    refine ⟨-ξ⁻¹ - relBdry U s x, ?_⟩
    refine Tendsto.sub_const (((hξ.inv₀ hξ0).neg).congr' ?_) _
    filter_upwards [hP] with t _
    simp only [inv_neg, inv_inv, neg_neg]
    rfl

variable {ℓ : ℂ}

include hα hW hW0 hζ hx harc hwc hw0 hγ hT in
/-- **The relative trace is bounded before the contact when it has a finite limit there.** -/
theorem exists_relTr_bound_of_tendsto
    (hρ : Tendsto (fun t => relBdry (rdrv (cfRec s W ζ ω)) s ((x : ℂ) + γ t) -
      relBdry (rdrv (cfRec s W ζ ω)) s x) (𝓝[<] τ) (𝓝 ℓ)) :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ≥0, t < τ → ‖relBdry (rdrv (cfRec s W ζ ω)) s ((x : ℂ) + γ t) -
      relBdry (rdrv (cfRec s W ζ ω)) s x‖ ≤ B := by
  have he : IsRegularDriver (w, (⊤ : ℝ≥0∞)) := Gm.isRegularDriver_top hwc hw0
  set ρ := fun t => relBdry (rdrv (cfRec s W ζ ω)) s ((x : ℂ) + γ t) - relBdry (rdrv (cfRec s W ζ ω)) s x
    with hρdef
  have hτ0 : 0 < τ := contact_pos' W ω hα hx harc hγ hT
  have hγc : Continuous γ := continuousOn_univ.1 (hγ.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hρc : ContinuousOn ρ (Iio τ) :=
    ((continuousOn_relBdry (continuous_rdrv _) (rdrv_zero _) s.coe_nonneg).comp
      (continuous_const.add hγc).continuousOn fun t ht =>
        RootH29.trace_mem_record_relSafe W ζ ω hα hW hW0 hζ hx harc he hγ (lt_min_of_contact hT ht) le_rfl).sub
      continuousOn_const
  obtain ⟨T, hTτ, hT'⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hτ0).1
    (hρ.eventually (closedBall_mem_nhds ℓ one_pos))
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
    (hρc.mono fun r hr => lt_of_le_of_lt hr.2 hTτ)
  refine ⟨max (max C (‖ℓ‖ + 1)) 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun t ht => ?_⟩
  rcases le_or_gt t T with h | h
  · exact (hC t ⟨zero_le, h⟩).trans ((le_max_left _ _).trans (le_max_left _ _))
  · have h1 : ρ t ∈ closedBall ℓ 1 := hT' ⟨h, ht⟩
    rw [mem_closedBall, dist_eq_norm] at h1
    have h2 := norm_le_norm_add_norm_sub' (ρ t) ℓ
    refine le_trans ?_ ((le_max_right _ _).trans (le_max_left _ _))
    change ‖ρ t‖ ≤ ‖ℓ‖ + 1
    linarith

include hα hW hW0 hζ hs hx harc hwc hw0 hγ hT in
/-- **The root-`x` clock is bounded before the contact when the relative trace has a finite limit there.** -/
theorem exists_clock_bound_of_tendsto
    (hρ : Tendsto (fun t => relBdry (rdrv (cfRec s W ζ ω)) s ((x : ℂ) + γ t) -
      relBdry (rdrv (cfRec s W ζ ω)) s x) (𝓝[<] τ) (𝓝 ℓ)) :
    ∃ M : ℝ, ∀ t : ℝ≥0, t < τ → gClk x s (cfRec s W ζ ω) w t ≤ M := by
  obtain ⟨h0, hm, hc⟩ := cClk_props W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT
  obtain ⟨B, hB, hρB⟩ := exists_relTr_bound_of_tendsto W ζ ω hα hW hW0 hζ hx harc hwc hw0 hγ hT hρ
  set a := gClk x s (cfRec s W ζ ω) w with hadef
  refine ⟨B ^ 2 / 2, fun t ht => ?_⟩
  obtain ⟨v, htv, hvτ⟩ := exists_between ht
  have hv0 : 0 < v := lt_of_le_of_lt zero_le htv
  have hτ0 : (0 : ℝ≥0) ∈ Iio τ := lt_of_le_of_lt zero_le ht
  have hat : 0 ≤ a t := h0 ▸ hm.monotoneOn hτ0 ht zero_le
  have hatv : a t < a v := hm ht hvτ htv
  have hgen := isGeneratingTrace_cDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hvτ
  set u : ℝ≥0 := (a t).toNNReal with hudef
  have hu : (u : ℝ) = a t := Real.coe_toNNReal _ hat
  have hulv : (u : ℝ≥0∞) < ENNReal.ofReal (a v) := by rw [ENNReal.coe_lt_ofReal, hu]; exact hatv
  have hfill := hgen.2.2 u hulv
  set tip := fun u' => RootI30.capacityTipRead x s v u' (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤)) with htipdef
  have hsub : tip '' Icc 0 u ⊆ closedBall ((0 : ℝ) : ℂ) B := by
    rintro _ ⟨u', hu', rfl⟩
    have hmem : (u' : ℝ) ∈ Icc (a 0) (a t) := by
      rw [h0]
      exact ⟨u'.coe_nonneg, hu ▸ NNReal.coe_le_coe.2 hu'.2⟩
    obtain ⟨t', ht', hat'⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ t)
      (hc.mono fun r hr => lt_of_le_of_lt hr.2 ht) hmem
    have hu'eq : u' = (a t').toNNReal := by rw [hat', Real.toNNReal_coe]
    rw [mem_closedBall, Complex.ofReal_zero, dist_zero_right, htipdef]
    dsimp only
    rw [hu'eq, tip_eq_c W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT (ht'.2.trans htv.le) hvτ]
    exact hρB t' (lt_of_le_of_lt ht'.2 ht)
  have hcpt : IsCompact (tip '' Icc 0 u) := by
    refine isCompact_Icc.image_of_continuousOn (hgen.2.1.mono fun u' hu' => ?_)
    show (u' : ℝ≥0∞) ≤ ENNReal.ofReal (a v)
    exact (ENNReal.coe_le_coe.2 hu'.2).trans hulv.le
  have hK := Gm.subset_closedBall_of_isFilling (fun _ hz => hz.1) hcpt hfill hsub
  rw [Complex.ofReal_zero, hu] at hK
  obtain ⟨R, hRc, hR0, -, hReq⟩ := exists_chain_cDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hv0 hvτ
  have h1 : fwdHull (fun r : ℝ => cDrv x s (cfRec s W ζ ω) w τ r.toNNReal) (a t) =
      fwdHull (fun r : ℝ => R r.toNNReal) (a t) := by
    refine InteractingSLE.fwdHull_eq_of_eqOn hat (show a t < (a t + a v) / 2 by linarith) fun r hr => ?_
    refine hReq _ ?_
    rw [Real.coe_toNNReal _ hr.1]
    linarith [hr.2]
  rw [h1] at hK
  have h2 := QuantumZipper.TipXE.two_mul_le_sq_of_fwdHull_subset (A := fun r : ℝ => R r.toNNReal)
    (hRc.comp continuous_real_toNNReal) (by simp only [Real.toNNReal_zero, hR0]) hat hB hK
  linarith

include hα hW hW0 hζ hs hx harc hwc hw0 hγ hT in
/-- **The canonical relative driver before a first contact where the relative trace has a finite limit** (one
sample; round 3's `exists_canon_of_contact` with the finite limit in place of a contact away from the tip). It
agrees with the glued driver `cDrv` below the clock. -/
theorem exists_canon_of_tendsto
    (hρ : Tendsto (fun t => relBdry (rdrv (cfRec s W ζ ω)) s ((x : ℂ) + γ t) -
      relBdry (rdrv (cfRec s W ζ ω)) s x) (𝓝[<] τ) (𝓝 ℓ)) :
    ∃ Wc : ℝ≥0 → ℝ, Continuous Wc ∧ Wc 0 = 0 ∧
      (∀ t : ℝ≥0, t < τ → fwdHull (fun q : ℝ => Wc q.toNNReal) (gClk x s (cfRec s W ζ ω) w t) =
        (fun z : ℂ => z + ((-GW2Bf.relBase x s (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤)) : ℝ) : ℂ)) ''
          RootH29.forwardHull x s t (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤))) ∧
      (∃ (ζc : ℝ≥0∞) (ηc : ℝ≥0 → ℂ), IsGeneratingTrace Wc ζc ηc ∧
        ENNReal.ofReal (GW2Bh.contactLifeX x s (cfRec s W ζ ω) w γ α) ≤ ζc) ∧
      (∀ u v : ℝ≥0, v < τ → (u : ℝ) < gClk x s (cfRec s W ζ ω) w v →
        Wc u = cDrv x s (cfRec s W ζ ω) w τ u) ∧
      ∃ M : ℝ, ∀ t : ℝ≥0, t < τ → gClk x s (cfRec s W ζ ω) w t ≤ M := by
  obtain ⟨h0, hm, hc⟩ := cClk_props W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT
  obtain ⟨M, hM⟩ := exists_clock_bound_of_tendsto W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hρ
  have hτ0 : 0 < τ := contact_pos' W ω hα hx harc hγ hT
  set a := gClk x s (cfRec s W ζ ω) w with hadef
  set D := cDrv x s (cfRec s W ζ ω) w τ with hDdef
  set ρ := fun t => relBdry (rdrv (cfRec s W ζ ω)) s ((x : ℂ) + γ t) - relBdry (rdrv (cfRec s W ζ ω)) s x
    with hρdef
  have hD0 : D 0 = 0 := cDrv_zero W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT
  have hann : ∀ t, t < τ → 0 ≤ a t := fun t ht => h0 ▸ hm.monotoneOn (lt_of_le_of_lt zero_le ht) ht zero_le
  -- the relative life `L = sup a([0, τ))`
  have hbdd : BddAbove (a '' Iio τ) := ⟨M, by rintro _ ⟨t, ht, rfl⟩; exact hM t ht⟩
  set L := sSup (a '' Iio τ) with hLdef
  have haL : ∀ t, t < τ → a t < L := fun t ht => by
    obtain ⟨t', htt', ht'τ⟩ := exists_between ht
    exact (hm ht ht'τ htt').trans_le (le_csSup hbdd ⟨t', ht'τ, rfl⟩)
  have hLex : ∀ y : ℝ, y < L → ∃ t, t < τ ∧ y < a t := fun y hy => by
    obtain ⟨_, ⟨t, ht, rfl⟩, h⟩ := exists_lt_of_lt_csSup (Set.Nonempty.image a ⟨0, hτ0⟩) hy
    exact ⟨t, ht, h⟩
  have hL0 : 0 < L := h0 ▸ haL 0 hτ0
  set L' : ℝ≥0 := L.toNNReal with hL'def
  have hL'0 : 0 < L' := Real.toNNReal_pos.2 hL0
  have hlt : ∀ u : ℝ≥0, u < L' ↔ (u : ℝ) < L := fun u => Real.lt_toNNReal_iff_coe_lt
  have hcontD : ∀ u : ℝ≥0, u < L' → ContinuousAt D u := fun u hu => by
    obtain ⟨v, hvτ, hv⟩ := hLex u ((hlt u).1 hu)
    exact continuousAt_cDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hvτ hv
  -- the relative trace on `[0, L]`
  set ηc : ℝ≥0 → ℂ := fun u => if u < L' then LP.traceAt u D else ℓ with hηdef
  set tip := fun (v u : ℝ≥0) => RootI30.capacityTipRead x s v u (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤))
    with htipdef
  have hgen : ∀ v, v < τ → IsGeneratingTrace D (ENNReal.ofReal (a v)) (tip v) := fun v hvτ =>
    isGeneratingTrace_cDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hvτ
  have hηeq : ∀ v u : ℝ≥0, v < τ → (u : ℝ) < a v → ηc u = tip v u := fun v u hvτ hu => by
    have huL : u < L' := (hlt u).2 (hu.trans (haL v hvτ))
    simp only [hηdef, huL, ↓reduceIte]
    exact LP.traceAt_eq_of_isGeneratingTrace (hgen v hvτ)
      (continuousOn_cDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hvτ) hD0 (ENNReal.coe_lt_ofReal.2 hu)
  have hηρ : ∀ t, t < τ → ηc (a t).toNNReal = ρ t := fun t ht => by
    have htL : (a t).toNNReal < L' := (hlt _).2 (by rw [Real.coe_toNNReal _ (hann t ht)]; exact haL t ht)
    simp only [hηdef, htL, ↓reduceIte]
    exact traceAt_cDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT ht
  have hη0 : ηc 0 = 0 := by
    have h := hηρ 0 hτ0
    rw [h0, Real.toNNReal_zero] at h
    rw [h]
    simp only [hρdef, hγ.1, add_zero, sub_self]
  have hηlim : Tendsto ηc (𝓝[<] L') (𝓝 ℓ) := by
    refine tendsto_iff_forall_eventually_mem.2 fun V hV => ?_
    obtain ⟨T, hTτ, hT'⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hτ0).1 (hρ.eventually hV)
    have hmem : Ioo (a T).toNNReal L' ∈ 𝓝[<] L' :=
      Ioo_mem_nhdsLT ((hlt _).2 (by rw [Real.coe_toNNReal _ (hann T hTτ)]; exact haL T hTτ))
    filter_upwards [hmem] with u hu
    obtain ⟨t₁, ht₁τ, ht₁⟩ := hLex u ((hlt u).1 hu.2)
    have hTu : a T < u := (Real.toNNReal_lt_iff_lt_coe (hann T hTτ)).1 hu.1
    have hTt₁ : T ≤ t₁ := ((hm.lt_iff_lt hTτ ht₁τ).1 (hTu.trans ht₁)).le
    obtain ⟨t, ht, hat⟩ := intermediate_value_Icc hTt₁ (hc.mono fun r hr => lt_of_le_of_lt hr.2 ht₁τ)
      ⟨hTu.le, ht₁.le⟩
    have htτ : t < τ := lt_of_le_of_lt ht.2 ht₁τ
    have hTt : T < t := (hm.lt_iff_lt hTτ htτ).1 (hat ▸ hTu)
    have hueq : u = (a t).toNNReal := by rw [hat, Real.toNNReal_coe]
    rw [hueq, hηρ t htτ]
    exact hT' ⟨hTt, htτ⟩
  have hgenD : IsGeneratingTrace D (L' : ℝ≥0∞) ηc := by
    refine ⟨hη0, fun u hu => ?_, fun u hu => ?_⟩
    · rcases lt_or_eq_of_le (ENNReal.coe_le_coe.1 hu) with h | h
      · obtain ⟨v, hvτ, hv⟩ := hLex u ((hlt u).1 h)
        have hnhds : {u' : ℝ≥0 | (u' : ℝ) < a v} ∈ 𝓝 u :=
          (isOpen_lt NNReal.continuous_coe continuous_const).mem_nhds hv
        have hct : ContinuousAt (tip v) u := by
          refine ((hgen v hvτ).2.1.mono fun u' hu' => ?_).continuousAt hnhds
          exact (ENNReal.coe_lt_ofReal.2 hu').le
        exact (hct.congr (Filter.eventually_of_mem hnhds fun u' hu' =>
          (hηeq v u' hvτ hu').symm)).continuousWithinAt
      · subst h
        have hset : {u : ℝ≥0 | (u : ℝ≥0∞) ≤ (L' : ℝ≥0∞)} = Iic L' := by
          ext u
          simp only [mem_ofPred_eq, ENNReal.coe_le_coe, mem_Iic]
        rw [hset]
        refine continuousWithinAt_Iio_iff_Iic.1 ?_
        have hηL : ηc L' = ℓ := by simp only [hηdef, lt_irrefl, ↓reduceIte]
        show Tendsto ηc (𝓝[<] L') (𝓝 (ηc L'))
        rw [hηL]
        exact hηlim
    · have huL : u < L' := ENNReal.coe_lt_coe.1 hu
      obtain ⟨v, hvτ, hv⟩ := hLex u ((hlt u).1 huL)
      have hfill := (hgen v hvτ).2.2 u (ENNReal.coe_lt_ofReal.2 hv)
      have himg : ηc '' Icc 0 u = tip v '' Icc 0 u :=
        image_congr fun u' hu' => hηeq v u' hvτ ((NNReal.coe_le_coe.2 hu'.2).trans_lt hv)
      rw [himg]
      exact hfill
  -- the driver limit at `L`, and the frozen driver
  obtain ⟨cL, hcL⟩ := RetEnd.exists_tendsto_driver_of_isGeneratingTrace hgenD
    (fun u hu => (hcontD u (ENNReal.coe_lt_coe.1 hu)).continuousWithinAt) hD0 hL'0
  set Wc : ℝ≥0 → ℝ := fun u => if u < L' then D u else cL with hWcdef
  have hWcD : ∀ u, u < L' → Wc u = D u := fun u hu => by simp only [hWcdef, hu, ↓reduceIte]
  have hWcc : ∀ u, L' ≤ u → Wc u = cL := fun u hu => by simp only [hWcdef, not_lt.2 hu, ↓reduceIte]
  have hWcont : Continuous Wc := by
    refine continuous_iff_continuousAt.2 fun u => ?_
    rcases lt_trichotomy u L' with h | h | h
    · exact (hcontD u h).congr (Filter.eventually_of_mem (Iio_mem_nhds h) fun u' hu' => (hWcD u' hu').symm)
    · subst h
      refine continuousAt_iff_continuous_left_right.2 ⟨continuousWithinAt_Iio_iff_Iic.1 ?_, ?_⟩
      · show Tendsto Wc (𝓝[<] L') (𝓝 (Wc L'))
        rw [hWcc L' le_rfl]
        exact hcL.congr' (eventually_nhdsWithin_of_forall fun u' hu' => (hWcD u' hu').symm)
      · exact continuousWithinAt_const.congr (fun y hy => hWcc y hy) (hWcc L' le_rfl)
    · exact continuousAt_const.congr
        (Filter.eventually_of_mem (Ioi_mem_nhds h) fun u' hu' => (hWcc u' (le_of_lt hu')).symm)
  have hhullWc : ∀ q : ℝ, 0 ≤ q → q < L →
      fwdHull (fun r : ℝ => Wc r.toNNReal) q = fwdHull (fun r : ℝ => D r.toNNReal) q := fun q hq hqL => by
    refine InteractingSLE.fwdHull_eq_of_eqOn hq (show q < (q + L) / 2 by linarith) fun r hr => ?_
    refine hWcD _ ((hlt _).2 ?_)
    rw [Real.coe_toNNReal _ hr.1]
    linarith [hr.2]
  refine ⟨Wc, hWcont, by rw [hWcD 0 hL'0, hD0], fun t ht => ?_, ⟨L', ηc, ?_, ?_⟩,
    fun u v hvτ hu => hWcD u ((hlt u).2 (hu.trans (haL v hvτ))), M, hM⟩
  · rw [hhullWc _ (hann t ht) (haL t ht)]
    exact hull_cDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT ht
  · refine ⟨hgenD.1, hgenD.2.1, fun u hu => ?_⟩
    rw [hhullWc _ u.coe_nonneg ((hlt u).1 (ENNReal.coe_lt_coe.1 hu))]
    exact hgenD.2.2 u hu
  · have hcl : GW2Bh.contactLifeX x s (cfRec s W ζ ω) w γ α = L := by
      unfold GW2Bh.contactLifeX
      rw [hT]
      simp only [ENNReal.coe_lt_coe]
      rfl
    rw [hcl]
    exact le_rfl

end Sample

/-- **The canonical relative driver at a first contact where the relative trace has a finite limit** (RELDET's
`CanonContactStatement` with the premise "the contact point is not the tip" replaced by the finite limit; the contact
may be at the tip). -/
def CanonContactLimStatement : Prop :=
  ∀ {Ω : Type u} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) {α : ℝ≥0 → ℂ},
    IsGeneratingTrace (W · ω) ⊤ α → Continuous (W · ω) → W 0 ω = 0 → ζ ω = ⊤ →
    ∀ {s : ℝ≥0}, 0 < s → ∀ {x : ℝ}, 0 ≤ x → (∀ u ∈ Icc 0 s, x * ‖α u‖ < 1) →
    ∀ {w : ℝ≥0 → ℝ}, Continuous w → w 0 = 0 → ∀ {γ : ℝ≥0 → ℂ}, IsGeneratingTrace w ⊤ γ →
    ∀ τ : ℝ≥0, firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
        ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) = (τ : ℝ≥0∞) →
    (∃ ℓ : ℂ, Tendsto (fun t => relBdry (rdrv (cfRec s W ζ ω)) s ((x : ℂ) + γ t) -
      relBdry (rdrv (cfRec s W ζ ω)) s x) (𝓝[<] τ) (𝓝 ℓ)) →
    ∃ Wc : ℝ≥0 → ℝ, Continuous Wc ∧ Wc 0 = 0 ∧
      (∀ t : ℝ≥0, t < τ → fwdHull (fun q : ℝ => Wc q.toNNReal) (gClk x s (cfRec s W ζ ω) w t) =
        (fun z : ℂ => z + ((-GW2Bf.relBase x s (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤)) : ℝ) : ℂ)) ''
          RootH29.forwardHull x s t (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤))) ∧
      (∃ (ζc : ℝ≥0∞) (ηc : ℝ≥0 → ℂ), IsGeneratingTrace Wc ζc ηc ∧
        ENNReal.ofReal (GW2Bh.contactLifeX x s (cfRec s W ζ ω) w γ α) ≤ ζc) ∧
      ∃ M : ℝ, ∀ t : ℝ≥0, t < τ → gClk x s (cfRec s W ζ ω) w t ≤ M

/-- **`CanonContactLimStatement` holds** (no inputs). -/
theorem canonContactLimStatement : CanonContactLimStatement.{u} := by
  intro Ω W ζ ω α hα hW hW0 hζ s hs x hx harc w hwc hw0 γ hγ τ hT ⟨ℓ, hρ⟩
  obtain ⟨Wc, hWc, hWc0, hK, hL, -, hM⟩ :=
    exists_canon_of_tendsto W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hρ
  exact ⟨Wc, hWc, hWc0, hK, hL, hM⟩

end InteractingSLE.Theorem14.GW2Ni
