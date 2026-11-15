/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Q3StopAnnounce

/-!
# GW2's relative determination, part 5: versions stopped by a capped gauge

Packet PROVE-GW2-RELDET (`GW2RdVersionStatement`, handoff §4.1). GB6's versions
(`HullId.isGB6RelVersionR_coord`, `Q3Stop.isGB6RelVersionA_coord`) are the measurable relative driver frozen at the
level stops of ONE causal gauge whose life is the life `L` of the relative coordinates (`HullId.HasLiveReadout`,
`HullId.exists_readoutCoord_of_liveReadout`). GW2's explored flow line must also be stopped before its continuation
threshold, i.e. at the relative clock of its lifetime, which is before `L`. Here the gauge is CAPPED by a second causal
gauge `Gζ` (nonnegative, positive before a cap time `Lζ`, zero at `Lζ` when `Lζ < L`):

* **`exists_capReadout`**: coordinates and a live readout, together with a cap gauge, give coordinates and an
  almost-sure separation readout of the gauge `min(G, Gζ)` with life `Lg ≤ L′`, `Lg = min(L, Lζ)` on the record event;
* **`isGB6RelVersionR_capCoord`**, **`isGB6RelVersionA_capCoord`**: the level stops of a readout with a life `Lg`
  at most the coordinates' life give announced R-form versions (the proofs of GB6 with the two lives separated);
* `exists_lt_coordStop_cap`: the stops exhaust every relative time below `Lg`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2Rd

open Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.RelDrv.Version Supp8.GB6.HullId Supp8.GB6.SourceC Supp8.Q3Stop
  Exist.StagedLaw

section Cap

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {s : ℝ≥0}
  {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {D : ℝ≥0 → Ω → ℝ} {L : Ω → ℝ≥0∞}

/-- A continuous function, nonnegative and dominated by a function tending to `0`, tends to `0`. -/
theorem tendsto_min_zero {f g : ℝ≥0 → ℝ} {T : ℝ≥0} (hf : Tendsto f (𝓝[<] T) (𝓝 0))
    (hfpos : ∀ᶠ t in 𝓝[<] T, 0 ≤ f t) (hg : ∀ t, 0 ≤ g t) :
    Tendsto (fun t => min (f t) (g t)) (𝓝[<] T) (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hf
    (hfpos.mono fun t ht => le_min ht (hg t)) (Eventually.of_forall fun _ => min_le_left _ _)

/-- **A capped separation readout.** From relative coordinates `(D, L)` with a live readout `G`, and a nonnegative
causal cap gauge `Gζ` that (on the record event) is continuous before `L`, positive before `min(L, Lζ)` and zero at
`Lζ` when `Lζ < L`, there are coordinates `(D′, L′)` and an almost-sure separation readout of `min(G, Gζ)` (cut off
the record event) whose life `Lg ≤ L′` is `min(L, Lζ)` on the record event. -/
theorem exists_capReadout (hC : RelativeDriverCoordinates s P W Wα ζα γ α D L)
    (hrecm : Measurable (gb6Rec s Wα ζα)) (hgood : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → GB6RecGood s Wα ζα α ω)
    (hL : HasLiveReadout s P (gb6Rec s Wα ζα) D L)
    {Gζ : GaugeReadout} (hGζm : ∀ t, Measurable (Gζ t)) (hGζc : IsCausal Gζ) (hGζ0 : ∀ t p, 0 ≤ Gζ t p)
    {Lζ : Ω → ℝ≥0∞}
    (hζ : ∀ᵐ ω ∂P, gb6Rec s Wα ζα ω ∈ gb6TS s → 0 < Lζ ω ∧
      ContinuousOn (fun t => Gζ t (gb6Rec s Wα ζα ω, fun u => D u ω)) {t | (t : ℝ≥0∞) < L ω} ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → (t : ℝ≥0∞) < Lζ ω → 0 < Gζ t (gb6Rec s Wα ζα ω, fun u => D u ω)) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → (t : ℝ≥0∞) = Lζ ω → Gζ t (gb6Rec s Wα ζα ω, fun u => D u ω) = 0) :
    ∃ (D' : ℝ≥0 → Ω → ℝ) (L' Lg : Ω → ℝ≥0∞) (g : ℝ≥0 → Ω → ℝ) (G' : GaugeReadout),
      RelativeDriverCoordinates s P W Wα ζα γ α D' L' ∧ AESeparationReadout P (gb6Rec s Wα ζα) D' Lg g G' ∧
      (∀ ω, Lg ω ≤ L' ω) ∧ (∀ ω, gb6Rec s Wα ζα ω ∈ gb6TS s → L' ω = L ω ∧ ∀ t, D' t ω = D t ω) ∧
      ∀ᵐ ω ∂P, gb6Rec s Wα ζα ω ∈ gb6TS s → Lg ω = min (L ω) (Lζ ω) := by
  classical
  obtain ⟨G, hGm, hGc, hreg⟩ := hL
  set rec := gb6Rec s Wα ζα with hrec
  set E₀ : Set Ω := rec ⁻¹' gb6TS s with hE₀def
  have hE₀ : MeasurableSet E₀ := hrecm (measurableSet_gb6TS s)
  have hboth : ∀ᵐ ω ∂P, rec ω ∈ gb6TS s →
      (ContinuousOn (fun t => G t (rec ω, fun u => D u ω)) {t | (t : ℝ≥0∞) < L ω} ∧
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → 0 < G t (rec ω, fun u => D u ω)) ∧
        ∀ T : ℝ≥0, (T : ℝ≥0∞) = L ω → Tendsto (fun t => G t (rec ω, fun u => D u ω)) (𝓝[<] T) (𝓝 0)) ∧
      (0 < Lζ ω ∧
        ContinuousOn (fun t => Gζ t (rec ω, fun u => D u ω)) {t | (t : ℝ≥0∞) < L ω} ∧
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → (t : ℝ≥0∞) < Lζ ω → 0 < Gζ t (rec ω, fun u => D u ω)) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → (t : ℝ≥0∞) = Lζ ω → Gζ t (rec ω, fun u => D u ω) = 0) := by
    filter_upwards [hreg, hζ] with ω h1 h2 hm
    exact ⟨h1 hm, h2 hm⟩
  obtain ⟨Gd, hGdm, hGdae, hGd⟩ := exists_measurable_good hboth
  set E₁ : Set Ω := E₀ ∩ Gd with hE₁def
  have hE₁ : MeasurableSet E₁ := hE₀.inter hGdm
  set D' : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ E₀ then D t ω else 0 with hD'def
  set L' : Ω → ℝ≥0∞ := fun ω => if ω ∈ E₀ then L ω else ⊤ with hL'def
  set G' : GaugeReadout := fun t p => if p.1 ∈ gb6TS s then min (G t p) (Gζ t p) else 1 with hG'def
  set F : Ω → ℝ≥0 → ℝ := fun ω t => min (G t (rec ω, fun u => D u ω)) (Gζ t (rec ω, fun u => D u ω)) with hFdef
  set g : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ E₁ then (if (t : ℝ≥0∞) < L ω then F ω t else 0)
    else fbGauge (L' ω) t with hgdef
  set Lg : Ω → ℝ≥0∞ := fun ω => if ω ∈ E₁ then min (L ω) (Lζ ω) else L' ω with hLgdef
  have hDE : ∀ ω ∈ E₀, (fun u => D' u ω) = fun u => D u ω := fun ω hω => funext fun u => ite_eq_left hω
  have hLE : ∀ ω ∈ E₀, L' ω = L ω := fun ω hω => ite_eq_left hω
  have hL'm : Measurable L' := Measurable.ite hE₀ hC.life_measurable measurable_const
  have hD'm : ∀ t, Measurable (D' t) := fun t => Measurable.ite hE₀ (hC.measurable t) measurable_const
  have hrd : Measurable fun ω => (rec ω, fun u => D u ω) :=
    hrecm.prodMk (measurable_pi_iff.2 fun u => hC.measurable u)
  have hFm : ∀ t, Measurable fun ω => F ω t := fun t => ((hGm t).comp hrd).min ((hGζm t).comp hrd)
  have hL'pos : ∀ ω, 0 < L' ω := fun ω => by
    by_cases hω : ω ∈ E₀
    · rw [hLE ω hω]; exact hC.life_pos ω
    · simp only [hL'def, hω, ↓reduceIte, ENNReal.zero_lt_top]
  have hFnn : ∀ ω ∈ E₁, ∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → 0 ≤ F ω t := fun ω hω t ht =>
    le_min ((hGd ω hω.2 hω.1).1.2.1 t ht).le (hGζ0 _ _)
  refine ⟨D', L', Lg, g, G', ⟨hD'm, hL'm, hL'pos, fun ω => ?_, fun ω => ?_, ?_, ?_⟩, ⟨fun t => ?_, fun ω => ?_,
    fun ω => ?_, fun ω t ht => ?_, fun ω t ht => ?_, fun t => ?_, ?_, ?_⟩, fun ω => ?_, fun ω hω => ?_, ?_⟩
  -- RelativeDriverCoordinates
  · by_cases hω : ω ∈ E₀
    · rw [hLE ω hω, hDE ω hω]; exact hC.continuous ω
    · simp only [hD'def, hω, ↓reduceIte]; exact continuousOn_const
  · by_cases hω : ω ∈ E₀
    · simp only [hD'def, hω, ↓reduceIte]; exact hC.zero ω
    · simp only [hD'def, hω, ↓reduceIte]
  · intro t A hA
    exact (measurableSet_lt measurable_const hL'm).inter (hD'm t hA)
  · filter_upwards [hC.relative, hgood] with ω hrel hg hs hαs
    have hω : ω ∈ E₀ := (mem_gb6TS_iff hg).1 ⟨hs, hαs⟩
    have hD : (fun r : ℝ => D' r.toNNReal ω) = fun r : ℝ => D r.toNNReal ω := funext fun r => ite_eq_left hω
    rw [hLE ω hω, hD]
    exact hrel hs hαs
  -- AESeparationReadout
  · exact Measurable.ite hE₁ (Measurable.ite (measurableSet_lt measurable_const hC.life_measurable) (hFm t)
      measurable_const) (measurable_fbGauge hL'm t)
  · by_cases hω : ω ∈ E₁
    · simp only [hgdef, hω, ↓reduceIte]
      have h := hGd ω hω.2 hω.1
      refine continuous_glue (ContinuousOn.inf h.1.1 h.2.2.1) fun T hT => ?_
      refine tendsto_min_zero (h.1.2.2 T hT) ?_ (fun t => hGζ0 _ _)
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (h.1.2.1 t (hT ▸ ENNReal.coe_lt_coe.2 ht)).le
    · simp only [hgdef, hω, ↓reduceIte]
      exact continuous_fbGauge _
  · by_cases hω : ω ∈ E₁
    · have h := hGd ω hω.2 hω.1
      have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < L ω := by rw [ENNReal.coe_zero]; exact hC.life_pos ω
      have h0' : ((0 : ℝ≥0) : ℝ≥0∞) < Lζ ω := by rw [ENNReal.coe_zero]; exact h.2.1
      simp only [hgdef, hω, h0, ↓reduceIte]
      exact lt_min (h.1.2.1 0 h0) (h.2.2.2.1 0 h0 h0')
    · simp only [hgdef, hω, ↓reduceIte]
      exact fbGauge_pos (by rw [ENNReal.coe_zero]; exact hL'pos ω)
  · by_cases hω : ω ∈ E₁
    · have h := hGd ω hω.2 hω.1
      have ht' : (t : ℝ≥0∞) < min (L ω) (Lζ ω) := by simpa only [hLgdef, hω, ↓reduceIte] using ht
      simp only [hgdef, hω, (lt_min_iff.1 ht').1, ↓reduceIte]
      exact lt_min (h.1.2.1 t (lt_min_iff.1 ht').1) (h.2.2.2.1 t (lt_min_iff.1 ht').1 (lt_min_iff.1 ht').2)
    · have ht' : (t : ℝ≥0∞) < L' ω := by simpa only [hLgdef, hω, ↓reduceIte] using ht
      simp only [hgdef, hω, ↓reduceIte]
      exact fbGauge_pos ht'
  · by_cases hω : ω ∈ E₁
    · have h := hGd ω hω.2 hω.1
      have ht' : (t : ℝ≥0∞) = min (L ω) (Lζ ω) := by simpa only [hLgdef, hω, ↓reduceIte] using ht
      rcases le_total (L ω) (Lζ ω) with hle | hle
      · rw [min_eq_left hle] at ht'
        have hn : ¬ (t : ℝ≥0∞) < L ω := by rw [ht']; exact lt_irrefl _
        simp only [hgdef, hω, hn, ↓reduceIte]
      · rw [min_eq_right hle] at ht'
        rcases eq_or_lt_of_le hle with heq | hlt
        · have hn : ¬ (t : ℝ≥0∞) < L ω := by rw [ht', heq]; exact lt_irrefl _
          simp only [hgdef, hω, hn, ↓reduceIte]
        · have htL : (t : ℝ≥0∞) < L ω := ht' ▸ hlt
          simp only [hgdef, hω, htL, ↓reduceIte, hFdef]
          rw [h.2.2.2.2 t htL ht']
          exact min_eq_right (h.1.2.1 t htL).le
    · have ht' : (t : ℝ≥0∞) = L' ω := by simpa only [hLgdef, hω, ↓reduceIte] using ht
      simp only [hgdef, hω, ↓reduceIte]
      exact fbGauge_terminal ht'
  · exact Measurable.ite (measurableSet_preimage measurable_fst (measurableSet_gb6TS s))
      ((hGm t).min (hGζm t)) measurable_const
  · intro t r w w' hw
    simp only [hG'def]
    split_ifs
    · rw [hGc t r w w' hw, hGζc t r w w' hw]
    · rfl
  · filter_upwards [hGdae] with ω hωG
    by_cases hω : ω ∈ E₀
    · have hω₁ : ω ∈ E₁ := ⟨hω, hωG⟩
      have hr : rec ω ∈ gb6TS s := hω
      have h := hGd ω hωG hω
      have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < L ω := by rw [ENNReal.coe_zero]; exact hC.life_pos ω
      refine ⟨?_, fun t ht => ?_⟩
      · simp only [hG'def, hgdef, hr, hω₁, h0, ↓reduceIte, hFdef]
        have hz : ∀ u ≤ (0 : ℝ≥0), (fun _ : ℝ≥0 => (0 : ℝ)) u = D u ω := fun u hu => by
          rw [nonpos_iff_eq_zero.1 hu, hC.zero ω]
        rw [hGc 0 _ _ _ hz, hGζc 0 _ _ _ hz]
      · have ht' : (t : ℝ≥0∞) < min (L ω) (Lζ ω) := by simpa only [hLgdef, hω₁, ↓reduceIte] using ht
        simp only [hG'def, hgdef, hr, hω₁, (lt_min_iff.1 ht').1, ↓reduceIte, hFdef]
        rw [hDE ω hω]
    · have hr : rec ω ∉ gb6TS s := hω
      have hω₁ : ω ∉ E₁ := fun h => hω h.1
      have hL' : L' ω = ⊤ := ite_eq_right hω
      refine ⟨?_, fun t _ => ?_⟩
      · simp only [hG'def, hgdef, hr, hω₁, ↓reduceIte, hL', fbGauge_top]
      · simp only [hG'def, hgdef, hr, hω₁, ↓reduceIte, hL', fbGauge_top]
  · by_cases hω : ω ∈ E₁
    · simp only [hLgdef, hω, ↓reduceIte, hLE ω hω.1]
      exact min_le_left _ _
    · simp only [hLgdef, hω, ↓reduceIte, le_refl]
  · exact ⟨hLE ω hω, fun t => ite_eq_left hω⟩
  · filter_upwards [hGdae] with ω hωG hm
    have hω₁ : ω ∈ E₁ := ⟨hm, hωG⟩
    simp only [hLgdef, hω₁, ↓reduceIte]

/-- **GB6's gauge-stop versions for a readout with a shorter life** (`HullId.isGB6RelVersionR_coord` with the life
`Lg` of the readout at most the life `L` of the coordinates). -/
theorem isGB6RelVersionR_capCoord {Lg : Ω → ℝ≥0∞} {g : ℝ≥0 → Ω → ℝ} {G : GaugeReadout}
    (hC : RelativeDriverCoordinates s P W Wα ζα γ α D L)
    (hread : AESeparationReadout P (gb6Rec s Wα ζα) D Lg g G) (hle : ∀ ω, Lg ω ≤ L ω) (m : ℕ) :
    IsGB6RelVersionR s P W Wα ζα γ α (coordDriver (D := D) (g := g) m)
      (fun ω => (coordStop (g := g) m ω : ℝ≥0∞)) := by
  have hvg : ∀ ω, (coordStop (g := g) m ω : ℝ≥0∞) < Lg ω :=
    fun ω => localStop_lt (hread.continuous ω) (hread.zero_pos ω) (hread.terminal ω) m
  have hv : ∀ ω, (coordStop (g := g) m ω : ℝ≥0∞) < L ω := fun ω => (hvg ω).trans_le (hle ω)
  have hvm : Measurable (coordStop (g := g) m) :=
    measurable_gaugeStop hread.measurable hread.continuous
      (((hread.measurable 0).div_const 2).min
        (measurable_const : Measurable fun _ : Ω => 1 / ((m : ℝ) + 1))) (m + 1)
  have hε : Measurable (recLevel G m) := measurable_recLevel hread.readout_measurable m
  have hrd : ∀ᵐ ω ∂P, recLevel G m (gb6Rec s Wα ζα ω) = gaugeLevel (g 0 ω) m ∧
      ∀ u ≤ gaugeStop (g · ω) (recLevel G m (gb6Rec s Wα ζα ω)) (m + 1),
        G u (gb6Rec s Wα ζα ω, fun u => coordDriver (D := D) (g := g) m u ω) = g u ω := by
    filter_upwards [hread.readout] with ω hω
    have hεω : recLevel G m (gb6Rec s Wα ζα ω) = gaugeLevel (g 0 ω) m := by
      change gaugeLevel (G 0 (gb6Rec s Wα ζα ω, fun _ => 0)) m = _
      rw [hω.1]
    refine ⟨hεω, fun u hu => ?_⟩
    rw [hεω] at hu
    have hu' : u ≤ coordStop (g := g) m ω := hu
    calc
      _ = G u (gb6Rec s Wα ζα ω, fun u => D u ω) := hread.causal u _ _ _ fun v hv' =>
        freeze_eq (hv'.trans hu')
      _ = g u ω := hω.2 u ((ENNReal.coe_le_coe.2 hu').trans_lt (hvg ω))
  refine ⟨⟨fun t => measurable_freeze hC.adapted hC.continuous hvm hv t,
    continuous_freeze hC.continuous hv, ?_, ?_, measurable_coe_nnreal_ennreal.comp hvm, ?_, ?_⟩,
    hitRule G (recLevel G m) (m + 1), measurable_hitRule hread.readout_measurable hε,
    isPathRule_hitRule hread.causal, ?_⟩
  · intro ω
    simpa only [coordDriver, freeze, zero_min] using hC.zero ω
  · intro ω t ht
    exact freeze_after (ENNReal.coe_le_coe.1 ht)
  · intro t
    refine ⟨prefixHitSet G (recLevel G m) (m + 1) t,
      measurableSet_prefixHitSet hread.readout_measurable hε _ _, isDetUpTo_prefixHitSet hread.causal _ _ _, ?_⟩
    filter_upwards [hrd] with ω hω
    have htst := mem_prefixHitSet_iff (hread.continuous ω) (by positivity : (0 : ℝ≥0) < m + 1)
      (show recLevel G m (gb6Rec s Wα ζα ω) < g 0 ω by
        rw [hω.1]; exact gaugeLevel_lt (hread.zero_pos ω) m) hω.2 t
    rw [hω.1] at htst
    exact ENNReal.coe_le_coe.trans htst.symm
  · filter_upwards [hC.relative] with ω hrel hs hαs
    obtain ⟨hcover, hK⟩ := hrel hs hαs
    refine ⟨ENNReal.coe_pos.2 (localStop_pos (hread.continuous ω) (hread.zero_pos ω) m),
      fun u hu => hcover u (hu.trans (hv ω)), fun t ht hav => ?_⟩
    obtain ⟨ha0, -, hKt⟩ := hK t ht
    exact (fwdHull_freeze_eq (hC.continuous ω) (hv ω) ha0 (ENNReal.ofReal_le_coe.1 hav)).trans hKt
  · filter_upwards [hrd] with ω hω
    rw [hitRule_eq_gaugeStop (hread.continuous ω) (by positivity : (0 : ℝ≥0) < m + 1)
      (show recLevel G m (gb6Rec s Wα ζα ω) < g 0 ω by
        rw [hω.1]; exact gaugeLevel_lt (hread.zero_pos ω) m) hω.2, hω.1]
    rfl

/-- **The capped gauge-stop versions are announced** (`Q3Stop.isGB6RelVersionA_coord` with the two lives
separated). -/
theorem isGB6RelVersionA_capCoord {Lg : Ω → ℝ≥0∞} {g : ℝ≥0 → Ω → ℝ} {G : GaugeReadout}
    (hC : RelativeDriverCoordinates s P W Wα ζα γ α D L)
    (hread : AESeparationReadout P (gb6Rec s Wα ζα) D Lg g G) (hle : ∀ ω, Lg ω ≤ L ω) (m : ℕ) :
    IsGB6RelVersionA s P W Wα ζα γ α (coordDriver (D := D) (g := g) m)
      (fun ω => (coordStop (g := g) m ω : ℝ≥0∞)) :=
  ⟨isGB6RelVersionR_capCoord hC hread hle m, annRules G m, measurable_annRules hread.readout_measurable m,
    isPathRule_annRules hread.causal m, annRules_ne_top G m, monotone_annRules G m, by
      filter_upwards [ae_annRules_coord hread m] with ω hω _ using hω⟩

/-- The capped stops are below the readout's life. -/
theorem coordStop_lt_cap {Lg : Ω → ℝ≥0∞} {g : ℝ≥0 → Ω → ℝ} {G : GaugeReadout}
    (hread : AESeparationReadout P (gb6Rec s Wα ζα) D Lg g G) (m : ℕ) (ω : Ω) :
    (coordStop (g := g) m ω : ℝ≥0∞) < Lg ω :=
  localStop_lt (hread.continuous ω) (hread.zero_pos ω) (hread.terminal ω) m

/-- **The capped stops exhaust the readout's life.** -/
theorem exists_lt_coordStop_cap {Lg : Ω → ℝ≥0∞} {g : ℝ≥0 → Ω → ℝ} {G : GaugeReadout}
    (hread : AESeparationReadout P (gb6Rec s Wα ζα) D Lg g G) {ω : Ω} {u : ℝ} (hu : ENNReal.ofReal u < Lg ω) :
    ∃ m, ENNReal.ofReal u < (coordStop (g := g) m ω : ℝ≥0∞) := by
  obtain ⟨m, hm⟩ := exists_lt_localStop (hread.continuous ω) (t := u.toNNReal) fun v hv =>
    hread.positive ω v ((ENNReal.coe_le_coe.2 hv).trans_lt hu)
  exact ⟨m, ENNReal.coe_lt_coe.2 hm⟩

end Cap

end InteractingSLE.Theorem14.GW2Rd
