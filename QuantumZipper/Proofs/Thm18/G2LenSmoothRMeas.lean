import QuantumZipper.Proofs.Thm18.G2LenSmoothGap
import QuantumZipper.Proofs.Thm18.G2RootRCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 smoothing, `R` side: measurable tools for the rooted measure `g3RootIntR`

The `R`-side twin of the measurability part of `G2LenSmoothGap.lean`:

* `measurable_g3CutLenRM`: the cut length `(g3ν₀ + g3ν₂)[0, y − κ]` is jointly measurable
  (reflection `y ↦ −y` and `measurable_measure_Icc_zero`);
* `g3RootIntR_cut_eq`: under `g3RootIntR`, events that force the margin in region 2 may use it in
  place of the honest cut length `g3CutLenR` (`ae_g3Fid_sets`);
* `g3RootR`: for `0 < b < t₂ + r₂`, a measure on `Ω₀ × ℝ × ℝ` (length `ℓ` uniform on
  `(0, ν_h[0, b]]`, point `y = lenRight ν ℓ`) with `g3RootR γ i b T = g3RootIntR γ i 1_T` for
  measurable `T` keeping `y` in `(a, b)`, `a > 0` (`g3RootR_apply_eq`; the quantile transform
  `setLIntegral_Ioc_lenRight`, as in `g3LenRoot_rootedR` but without the truncation);
* `g3RootIntR_le_top`: `g3RootIntR` of an indicator is finite for `0 < γ < 2`
  (`E ν_h[0, c] < ∞` for `c < 1`, from `ν_h = |t| ν_{zField 1}` off `0` and the unit-normalized
  first moment `lintegral_qBoundaryMeasure_zField_one_Icc_lt_top`).

Own elementary proofs (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

theorem measurable_g3sum₂' (γ : ℝ) (i : G3Idx) :
    Measurable fun ω : Ω₀ => g3ν₀ γ i ω + g3ν₂ γ i ω :=
  (measurable_g3sum₂ γ i).mono
    (sup_le (localSigma_le gffBase.gff _ _) (outsideSigma2_le gffBase.gff _ _ _ _)) le_rfl

/-- The **measurable cut length at `R`**: `(g3ν₀ + g3ν₂)[0, y − κ]`. -/
def g3CutLenRM (γ : ℝ) (i : G3Idx) (κ : ℝ) (ω : Ω₀) (y : ℝ) : ℝ :=
  ((g3ν₀ γ i ω + g3ν₂ γ i ω) (Icc 0 (y - κ))).toReal

theorem measurable_g3sum₂_neg_Icc (γ : ℝ) (i : G3Idx) :
    Measurable fun p : Ω₀ × ℝ =>
      ((g3ν₀ γ i p.1 + g3ν₂ γ i p.1).map fun x : ℝ => -x) (Icc p.2 0) :=
  measurable_measure_Icc_zero (μ := fun ω => (g3ν₀ γ i ω + g3ν₂ γ i ω).map fun x : ℝ => -x)
    ((Measure.measurable_map _ measurable_neg).comp (measurable_g3sum₂' γ i))
    (fun ω b => by
      rw [map_neg_Icc, neg_zero]; exact g3ν₀₂_Icc_ne_top γ i ω _)

theorem measurable_g3CutLenRM (γ : ℝ) (i : G3Idx) (κ : ℝ) :
    Measurable fun q : Ω₀ × ℝ × ℝ => g3CutLenRM γ i κ q.1 q.2.2 := by
  have h2 : Measurable fun q : Ω₀ × ℝ × ℝ => ((q.1, κ - q.2.2) : Ω₀ × ℝ) :=
    measurable_fst.prodMk (measurable_const.sub (measurable_snd.comp measurable_snd))
  have h3 : Measurable fun q : Ω₀ × ℝ × ℝ =>
      ((g3ν₀ γ i q.1 + g3ν₂ γ i q.1).map fun x : ℝ => -x) (Icc (κ - q.2.2) 0) :=
    Measurable.comp (g := fun p : Ω₀ × ℝ =>
        ((g3ν₀ γ i p.1 + g3ν₂ γ i p.1).map fun x : ℝ => -x) (Icc p.2 0))
      (f := fun q : Ω₀ × ℝ × ℝ => ((q.1, κ - q.2.2) : Ω₀ × ℝ)) (measurable_g3sum₂_neg_Icc γ i) h2
  have e : (fun q : Ω₀ × ℝ × ℝ => g3CutLenRM γ i κ q.1 q.2.2) = fun q =>
      (((g3ν₀ γ i q.1 + g3ν₂ γ i q.1).map fun x : ℝ => -x) (Icc (κ - q.2.2) 0)).toReal := by
    funext q
    rw [map_neg_Icc, neg_zero, neg_sub]
    rfl
  rw [e]
  exact h3.ennreal_toReal

theorem g3CutLenRM_mono (γ : ℝ) (i : G3Idx) (ω : Ω₀) (y : ℝ) {κ κ' : ℝ} (h : κ ≤ κ') :
    g3CutLenRM γ i κ' ω y ≤ g3CutLenRM γ i κ ω y :=
  ENNReal.toReal_mono (g3ν₀₂_Icc_ne_top γ i _ _)
    (measure_mono (Icc_subset_Icc_right (by linarith)))

theorem G3Idx.lt_of_margin₂ (i : G3Idx) {m y : ℝ} (hm : 0 ≤ m) (h : |y - i.t₂| + m < i.r₂) :
    i.t₂ - i.r₂ < y ∧ y < i.t₂ + i.r₂ := by
  have h1 := le_abs_self (y - i.t₂)
  have h2 := neg_abs_le (y - i.t₂)
  constructor <;> linarith

theorem g3RootIntR_cut_eq {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) {κ : ℝ} (hκ : 0 ≤ κ)
    {m : ℝ} (hm : 0 ≤ m) (P : Ω₀ × ℝ × ℝ → ℝ → Prop)
    (hP : ∀ q c, P q c → |q.2.2 - i.t₂| + m < i.r₂) :
    g3RootIntR γ i ({q | P q (g3CutLenR γ κ q.1 q.2.2)}.indicator 1) =
      g3RootIntR γ i ({q | P q (g3CutLenRM γ i κ q.1 q.2.2)}.indicator 1) := by
  unfold g3RootIntR
  refine lintegral_congr_ae ?_
  filter_upwards [ae_g3Fid_sets hγ hγ2] with ω hω
  refine setLIntegral_congr_fun measurableSet_Icc fun y hy => ?_
  set ℓ := (g3Hν γ ω (Icc 0 y)).toReal
  have hmarg : ∀ c, P (ω, ℓ, y) c → g3CutLenR γ κ ω y = g3CutLenRM γ i κ ω y := by
    intro c hc
    have hy2 := (i.lt_of_margin₂ hm (hP _ _ hc)).2
    have hsub : Icc 0 (y - κ) ⊆ Ioo (-(3 * i.η / 4)) (1 / 2 + i.η / 4) := fun z hz =>
      ⟨by linarith [hz.1, i.hη], by linarith [hz.2, i.t₂_add_r₂]⟩
    unfold g3CutLenR g3CutLenRM
    rw [(hω i).2 _ hsub]
  have e : ((ω, ℓ, y) ∈ {q : Ω₀ × ℝ × ℝ | P q (g3CutLenR γ κ q.1 q.2.2)}) ↔
      ((ω, ℓ, y) ∈ {q : Ω₀ × ℝ × ℝ | P q (g3CutLenRM γ i κ q.1 q.2.2)}) := by
    show P (ω, ℓ, y) (g3CutLenR γ κ ω y) ↔ P (ω, ℓ, y) (g3CutLenRM γ i κ ω y)
    constructor
    · intro h; rwa [← hmarg _ h]
    · intro h
      have := hmarg _ h
      rwa [this]
  by_cases h : (ω, ℓ, y) ∈ {q : Ω₀ × ℝ × ℝ | P q (g3CutLenR γ κ q.1 q.2.2)}
  · rw [indicator_of_mem h, indicator_of_mem (e.1 h)]
  · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h (e.2 h'))]

theorem g3RootIntR_eq_of_idx {γ : ℝ} {i i' : G3Idx} (h : i.t₂ + i.r₂ = i'.t₂ + i'.r₂)
    (F : Ω₀ × ℝ × ℝ → ℝ≥0∞) : g3RootIntR γ i F = g3RootIntR γ i' F := by
  unfold g3RootIntR; rw [h]

/-! ## Finiteness -/

theorem lintegral_hν_Icc_zero_lt_top {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {c : ℝ} (_hc0 : 0 ≤ c)
    (hc : c < 1) : ∫⁻ ω, g3Hν γ ω (Icc 0 c) ∂gffBase.P < ⊤ := by
  have hle : ∀ᵐ ω ∂gffBase.P, g3Hν γ ω (Icc 0 c) ≤
      ENNReal.ofReal c * qBoundaryMeasure γ (BdryExist.zField gffBase.X 1 ω) (Icc 0 c) := by
    filter_upwards [qBoundaryMeasure_normField_restrict (X := gffBase.X) gffBase.gff hγ hγ2]
      with ω hω
    set ν₁ := qBoundaryMeasure γ (BdryExist.zField gffBase.X 1 ω)
    show qBoundaryMeasure γ (normField γ gffBase.X ω) (Icc 0 c) ≤ _
    rw [hω, withDensity_apply _ measurableSet_Icc]
    calc ∫⁻ t in Icc 0 c, ENNReal.ofReal |t| ∂(ν₁.restrict {0}ᶜ)
        ≤ ∫⁻ _ in Icc 0 c, ENNReal.ofReal c ∂(ν₁.restrict {0}ᶜ) := by
          refine setLIntegral_mono measurable_const fun t ht => ENNReal.ofReal_le_ofReal ?_
          rw [abs_of_nonneg ht.1]
          exact ht.2
      _ = ENNReal.ofReal c * (ν₁.restrict {0}ᶜ) (Icc 0 c) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal c * ν₁ (Icc 0 c) := by
          refine mul_le_mul' le_rfl ?_
          rw [Measure.restrict_apply measurableSet_Icc]
          exact measure_mono Set.inter_subset_left
  have hfin := lintegral_qBoundaryMeasure_zField_one_Icc_lt_top (X := gffBase.X)
    (P := gffBase.P) gffBase.gff hγ hγ2 (u := 0) (v := c) (by norm_num) hc
  exact lt_of_le_of_lt ((lintegral_mono_ae hle).trans_eq
    (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)

theorem g3RootIntR_indicator_lt_top {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx)
    (T : Set (Ω₀ × ℝ × ℝ)) : g3RootIntR γ i (T.indicator 1) < ⊤ := by
  refine lt_of_le_of_lt ?_ (lintegral_hν_Icc_zero_lt_top hγ hγ2 (c := i.t₂ + i.r₂)
    (by linarith [i.t₂_add_r₂, i.hη]) (by linarith [i.t₂_add_r₂, i.hη, i.hηδ, i.hδ]))
  unfold g3RootIntR
  refine lintegral_mono fun ω => ?_
  calc ∫⁻ y in Icc 0 (i.t₂ + i.r₂), T.indicator 1 (ω, (g3Hν γ ω (Icc 0 y)).toReal, y) ∂g3Hν γ ω
      ≤ ∫⁻ _ in Icc 0 (i.t₂ + i.r₂), 1 ∂g3Hν γ ω :=
        lintegral_mono fun y => indicator_le_self' (fun _ _ => zero_le_one) _
    _ = g3Hν γ ω (Icc 0 (i.t₂ + i.r₂)) := by
        rw [setLIntegral_one]

/-! ## The rooted measure at `R` as a measure -/

/-- The domain `{0 < ℓ ≤ (ν₀ + ν₂)[0, b]}`. -/
def g3DomR (γ : ℝ) (i : G3Idx) (b : ℝ) : Set (Ω₀ × ℝ) :=
  {p | 0 < p.2 ∧ ENNReal.ofReal p.2 ≤ (g3ν₀ γ i p.1 + g3ν₂ γ i p.1) (Icc 0 b)}

theorem measurableSet_g3DomR (γ : ℝ) (i : G3Idx) (b : ℝ) : MeasurableSet (g3DomR γ i b) :=
  (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le (ENNReal.measurable_ofReal.comp measurable_snd)
      (((Measure.measurable_coe measurableSet_Icc).comp (measurable_g3sum₂' γ i)).comp
        measurable_fst))

/-- The partner map `(ω, ℓ) ↦ (ω, ℓ, lenRight (ν₀ + ν₂) ℓ)`. -/
def g3PtR (γ : ℝ) (i : G3Idx) (p : Ω₀ × ℝ) : Ω₀ × ℝ × ℝ :=
  (p.1, p.2, lenRight (g3ν₀ γ i p.1 + g3ν₂ γ i p.1) p.2)

theorem measurable_g3PtR (γ : ℝ) (i : G3Idx) : Measurable (g3PtR γ i) :=
  measurable_fst.prodMk (measurable_snd.prodMk (Measurable.comp
    (g := fun q : Measure ℝ × ℝ => lenRight q.1 q.2)
    (f := fun p : Ω₀ × ℝ => (g3ν₀ γ i p.1 + g3ν₂ γ i p.1, p.2)) measurable_lenRight
    ((measurable_g3sum₂' γ i).comp measurable_fst |>.prodMk measurable_snd)))

/-- **The rooted measure at `R` below `b`.** -/
def g3RootR (γ : ℝ) (i : G3Idx) (b : ℝ) : Measure (Ω₀ × ℝ × ℝ) :=
  ((gffBase.P.prod volume).restrict (g3DomR γ i b)).map (g3PtR γ i)

/-- **Length-rooted = rooted at `R`** without truncation, for events keeping `y ∈ (a, b)`. -/
theorem g3RootR_apply_eq {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx)
    {T : Set (Ω₀ × ℝ × ℝ)} (hT : MeasurableSet T) {a b : ℝ} (ha : 0 < a) (hb0 : 0 < b)
    (hb : b < i.t₂ + i.r₂) (hTsub : ∀ q ∈ T, a < q.2.2 ∧ q.2.2 < b) :
    g3RootR γ i b T = g3RootIntR γ i (T.indicator 1) := by
  have hS : MeasurableSet (g3PtR γ i ⁻¹' T) := measurable_g3PtR γ i hT
  rw [g3RootR, Measure.map_apply (measurable_g3PtR γ i) hT, Measure.restrict_apply hS,
    Measure.prod_apply (hS.inter (measurableSet_g3DomR γ i b)), g3RootIntR]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_g3Fid_sets hγ hγ2, G3Fid.ae_normField_good gffBase.gff hγ hγ2]
    with ω hω hgood
  set m := g3ν₀ γ i ω + g3ν₂ γ i ω with hm
  have hwinsub : Icc 0 b ⊆ Ioo (-(3 * i.η / 4)) (1 / 2 + i.η / 4) := fun z hz =>
    ⟨by linarith [hz.1, i.hη], by linarith [hz.2, i.t₂_add_r₂]⟩
  have hwin : ∀ s ⊆ Icc 0 b, m s = g3Hν γ ω s := fun s hs => (hω i).2 s (hs.trans hwinsub)
  have hat : ∀ t ∈ Icc 0 b, m {t} = 0 := fun t ht => by
    rw [hwin {t} (singleton_subset_iff.2 ht)]; exact hgood.2.2 t
  have hD : m (Icc 0 b) ≠ ⊤ := g3ν₀₂_Icc_ne_top γ i ω b
  have hsec' : MeasurableSet {ℓ : ℝ | (ω, ℓ, lenRight m ℓ) ∈ T} :=
    (measurable_const.prodMk (measurable_id.prodMk (measurable_lenRight_left m))) hT
  have hfT : Measurable fun q : ℝ × ℝ => T.indicator (1 : Ω₀ × ℝ × ℝ → ℝ≥0∞) (ω, q.1, q.2) :=
    (measurable_one.indicator hT).comp (measurable_const.prodMk measurable_id)
  have hset : Prod.mk ω ⁻¹' (g3PtR γ i ⁻¹' T ∩ g3DomR γ i b) =
      {ℓ : ℝ | (ω, ℓ, lenRight m ℓ) ∈ T} ∩ Ioc 0 (m (Icc 0 b)).toReal := by
    ext ℓ
    simp only [mem_preimage, mem_inter_iff, g3DomR, mem_setOf_eq, mem_Ioc]
    constructor
    · rintro ⟨hP, h0, hl⟩
      exact ⟨hP, h0, (ENNReal.ofReal_le_iff_le_toReal hD).1 hl⟩
    · rintro ⟨hP, h0, hl⟩
      exact ⟨hP, h0, (ENNReal.ofReal_le_iff_le_toReal hD).2 hl⟩
  have e1 : volume (Prod.mk ω ⁻¹' (g3PtR γ i ⁻¹' T ∩ g3DomR γ i b)) =
      ∫⁻ ℓ in Ioc 0 (m (Icc 0 b)).toReal,
        T.indicator (1 : Ω₀ × ℝ × ℝ → ℝ≥0∞) (ω, ℓ, lenRight m ℓ) := by
    rw [hset, ← Measure.restrict_apply hsec', ← lintegral_indicator_one hsec']
    rfl
  rw [e1, setLIntegral_Ioc_lenRight (f := fun q : ℝ × ℝ => T.indicator 1 (ω, q.1, q.2))
    hb0 (g3ν₀₂_Icc_ne_top γ i ω) hat hfT]
  have hres : m.restrict (Icc 0 b) = (g3Hν γ ω).restrict (Icc 0 b) := by
    ext s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
    exact hwin _ inter_subset_right
  show ∫⁻ y, _ ∂(m.restrict (Icc 0 b)) = _
  rw [hres]
  rw [setLIntegral_congr_fun measurableSet_Icc (g := fun y =>
    T.indicator (1 : Ω₀ × ℝ × ℝ → ℝ≥0∞) (ω, (g3Hν γ ω (Icc 0 y)).toReal, y))
    fun y hy => by simp only; rw [hwin (Icc 0 y) (Icc_subset_Icc_right hy.2)]]
  rw [← lintegral_indicator measurableSet_Icc, ← lintegral_indicator measurableSet_Icc]
  refine lintegral_congr fun y => ?_
  by_cases hF : (ω, (g3Hν γ ω (Icc 0 y)).toReal, y) ∈ T
  · have hy := hTsub _ hF
    rw [indicator_of_mem (show y ∈ Icc 0 b from ⟨by linarith [hy.1], hy.2.le⟩),
      indicator_of_mem (show y ∈ Icc 0 (i.t₂ + i.r₂) from ⟨by linarith [hy.1], by linarith [hy.2]⟩)]
  · simp [Set.indicator_apply, hF]

end Thm18Asm
end QuantumZipper
