import QuantumZipper.Proofs.Thm18.G3PlX

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3 above G2 with abstract zooms: the honest window integral against scheme `C`

Generalized copy (D92) of the zoom-dependent parts of `G3PlDefs.lean` (`g3plHonSet`,
`g3plHon`), `G3PlMain.lean` (`g3pl_core`, zoom part), `G3PlX.lean` (`g3plHonX`,
`g3plHonSet_volume_eq`, `g3plHon_eq_honX`) and `G3PlWire.lean` (`g3TWedgePlainStmt_of_honest`,
with the wedge side removed), with the plain zooms `zoomLaw γ L` at `x` and at `R(x)` replaced by
abstract zooms `Z L`, `Z' L` (`Z L h y : LawD`). The only property of the zooms used is joint
measurability (`hZm`, `hZm'`, where the originals use `measurable_zoomLaw`). All zoom-free
lemmas (exceptional sets `g3plN`, `g3pl_fine`, window choices `g3pl_exists_U₀`, `g3pl_exists_m`,
the weight `g3plW`, `g3pl_integral_eq`, the quantile change of variables) are reused.

Headline `g3plHonX_schemeC_Z`: for every window `δ ∈ (0, 1/4]`, the normalized honest
boundary-point window integral `U⁻¹ g3plHonXZ` is `ε`-close, for small `U`, a margin `m`, all
small `η` and all levels `L`, to the weighted scheme-`C` integral with the weight `g3plW`, whose
margin mass is `ε`-close to `1`.

Sheffield, arXiv:1012.4797, proof of Thm. 1.8, §5.4, pp. 70–72. Own bookkeeping copied from the
originals.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm

local notation "Ω₀" => gffBase.Ω

variable {Z Z' : ℝ → FieldSample → ℝ → LawD}

/-! ## Scheme `C` with abstract zooms -/

/-- `g3pUf` with the abstract zoom `Z`. -/
def g3pUfZ (Z : ℝ → FieldSample → ℝ → LawD) (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx) (p : Ω₀ × ℝ) :
    LawD := Z i.C (g3pField γ g p.1) (g3pX γ g i p)

/-- `g3pVf` with the abstract zoom `Z'`. -/
def g3pVfZ (Z' : ℝ → FieldSample → ℝ → LawD) (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx) (p : Ω₀ × ℝ) :
    LawD := Z' i.C (g3pField γ g p.1) (g3pR γ g i p)

theorem measurable_g3pUfZ (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx) : Measurable (g3pUfZ Z γ g i) :=
  (hZm i.C).comp (((measurable_g3pField γ g).comp measurable_fst).prodMk
    ((measurable_g3pX γ g i).mono (sig_le_g3 i _ _) le_rfl))

theorem measurable_g3pVfZ (hZm' : ∀ C, Measurable fun q : FieldSample × ℝ => Z' C q.1 q.2)
    (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx) : Measurable (g3pVfZ Z' γ g i) :=
  (hZm' i.C).comp (((measurable_g3pField γ g).comp measurable_fst).prodMk
    ((measurable_g3pR γ g i).mono (sig_le_g3 i _ _) le_rfl))

/-! ## The honest window integrals -/

/-- `g3plHonSet` with abstract zooms. -/
def g3plHonSetZ (Z Z' : ℝ → FieldSample → ℝ → LawD) (γ δ U L : ℝ) (s t : Set LawD) (ω : Ω₀) :
    Set ℝ :=
  {ℓ | ℓ ∈ Ioc 0 U ∧ ENNReal.ofReal ℓ ≤ g3plV γ ω (Icc (-δ) 0) ∧
    Z L (g3plF γ ω) (lenLeft (g3plV γ ω) ℓ) ∈ s ∧
    Z' L (g3plF γ ω) (lenRight (g3plV γ ω) ℓ) ∈ t}

/-- `g3plHon` with abstract zooms. -/
def g3plHonZ (Z Z' : ℝ → FieldSample → ℝ → LawD) (γ δ U L : ℝ) (s t : Set LawD) : ℝ≥0∞ :=
  ∫⁻ ω, volume (g3plHonSetZ Z Z' γ δ U L s t ω) ∂gffBase.P

/-- `g3plHonX` with abstract zooms: the honest boundary-point window integral of scheme `C`. -/
def g3plHonXZ (Z Z' : ℝ → FieldSample → ℝ → LawD) (γ δ U L : ℝ) (s t : Set LawD) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ b in g3plXWin γ δ U ω,
    s.indicator 1 (Z L (g3plF γ ω) b) *
      t.indicator 1 (Z' L (g3plF γ ω) (g3zPartner γ (g3plF γ ω) b)) ∂(g3plV γ ω)
    ∂gffBase.P

/-- **The exceptional-set comparison** (zoom part of `g3pl_core`). -/
theorem g3pl_coreZ {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) {U m : ℝ}
    (hm0 : 0 < m) (hmδ : m ≤ i.δ / 4) (hm16 : m ≤ 1 / 16) (hηm : i.η ≤ m) (s t : Set LawD) :
    let A := g3pUfZ Z γ (g3wProf γ) i ⁻¹' s ∩ g3pVfZ Z' γ (g3wProf γ) i ⁻¹' t ∩
      g3pMarg γ (g3wProf γ) i m
    let K := ∫⁻ ω, volume ({ℓ | (ω, ℓ) ∈ A ∩ g3plWin U} ∩
      Ioc 0 (g3pMass γ (g3wProf γ) i ω).toReal) ∂gffBase.P
    let Bd := ∫⁻ ω, g3plBd i.δ U m (g3plV γ ω) ∂gffBase.P
    K ≤ g3plHonZ Z Z' γ i.δ U i.C s t + Bd ∧ g3plHonZ Z Z' γ i.δ U i.C s t ≤ K + Bd := by
  intro A K Bd
  have hBm : AEMeasurable (fun ω => g3plBd i.δ U m (g3plV γ ω)) gffBase.P :=
    (measurable_g3plBd _ _ _).comp_aemeasurable (aemeasurable_g3plV hγ hγ2)
  have fine : ∀ᵐ ω ∂gffBase.P, ∀ ℓ, ℓ ∈ Ioc 0 U → ℓ ∉ g3plN i.δ U m (g3plV γ ω) →
      ENNReal.ofReal ℓ ≤ g3plV γ ω (Icc (-i.δ) 0) ∧ ℓ ≤ (g3pMass γ (g3wProf γ) i ω).toReal ∧
      g3pX γ (g3wProf γ) i (ω, ℓ) = lenLeft (g3plV γ ω) ℓ ∧
      g3pR γ (g3wProf γ) i (ω, ℓ) = lenRight (g3plV γ ω) ℓ ∧
      (ω, ℓ) ∈ g3pMarg γ (g3wProf γ) i m := by
    filter_upwards [ae_g3pFid_sets hγ hγ2] with ω hF ℓ hℓ hN
    have hN' : ¬(g3plBadE i.δ U (g3plV γ ω) = 1 ∨
        ENNReal.ofReal ℓ ≤ g3plV γ ω (Icc (-(3 * m)) 0) ∨
        ENNReal.ofReal ℓ ≤ g3plV γ ω (Icc 0 (3 * m))) := fun h => hN ⟨hℓ, h⟩
    push Not at hN'
    exact g3pl_fine i hm0 hmδ hm16 hηm (hF i).1 (hF i).2 hN'.1 hℓ hN'.2.1 hN'.2.2
  have hK : K ≤ g3plHonZ Z Z' γ i.δ U i.C s t + Bd := by
    unfold g3plHonZ
    rw [← lintegral_add_right' _ hBm]
    refine lintegral_mono_ae (fine.mono fun ω hω => ?_)
    refine (measure_mono (t := g3plHonSetZ Z Z' γ i.δ U i.C s t ω ∪ g3plN i.δ U m (g3plV γ ω))
      ?_).trans ((measure_union_le _ _).trans (add_le_add le_rfl (volume_g3plN_le _ _ _ _)))
    rintro ℓ ⟨⟨⟨⟨hs, ht⟩, -⟩, hW⟩, hI⟩
    have hℓ : ℓ ∈ Ioc 0 U := ⟨hI.1, hW⟩
    by_cases hN : ℓ ∈ g3plN i.δ U m (g3plV γ ω)
    · exact Or.inr hN
    · obtain ⟨h1, -, hX, hR, -⟩ := hω ℓ hℓ hN
      refine Or.inl ⟨hℓ, h1, ?_, ?_⟩
      · have : Z i.C (g3pField γ (g3wProf γ) ω) (g3pX γ (g3wProf γ) i (ω, ℓ)) ∈ s := hs
        rwa [hX] at this
      · have : Z' i.C (g3pField γ (g3wProf γ) ω) (g3pR γ (g3wProf γ) i (ω, ℓ)) ∈ t := ht
        rwa [hR] at this
  have hH : g3plHonZ Z Z' γ i.δ U i.C s t ≤ K + Bd := by
    unfold g3plHonZ
    rw [← lintegral_add_right' _ hBm]
    refine lintegral_mono_ae (fine.mono fun ω hω => ?_)
    refine (measure_mono (t := ({ℓ | (ω, ℓ) ∈ A ∩ g3plWin U} ∩
      Ioc 0 (g3pMass γ (g3wProf γ) i ω).toReal) ∪ g3plN i.δ U m (g3plV γ ω))
      ?_).trans ((measure_union_le _ _).trans (add_le_add le_rfl (volume_g3plN_le _ _ _ _)))
    rintro ℓ ⟨hℓ, -, hs, ht⟩
    by_cases hN : ℓ ∈ g3plN i.δ U m (g3plV γ ω)
    · exact Or.inr hN
    · obtain ⟨-, h2, hX, hR, hM⟩ := hω ℓ hℓ hN
      refine Or.inl ⟨⟨⟨⟨?_, ?_⟩, hM⟩, hℓ.2⟩, hℓ.1, h2⟩
      · show Z i.C (g3pField γ (g3wProf γ) ω) (g3pX γ (g3wProf γ) i (ω, ℓ)) ∈ s
        rw [hX]; exact hs
      · show Z' i.C (g3pField γ (g3wProf γ) ω) (g3pR γ (g3wProf γ) i (ω, ℓ)) ∈ t
        rw [hR]; exact ht
  exact ⟨hK, hH⟩

theorem measurable_zoomZ_pt (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (L : ℝ) (y : FieldSample) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable fun b => Z L y (f b) :=
  (hZm L).comp (f := fun b => (y, f b)) (measurable_const.prodMk hf)

/-- **The quantile change of variables, pathwise** (abstract zooms). -/
theorem g3plHonSetZ_volume_eq
    (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (hZm' : ∀ C, Measurable fun q : FieldSample × ℝ => Z' C q.1 q.2)
    {γ : ℝ} {δ U L : ℝ} (hδ : 0 < δ) (hU : 0 < U) {s t : Set LawD}
    (hs : MeasurableSet s) (ht : MeasurableSet t) {ω : Ω₀}
    (hat : ∀ a : ℝ, g3plV γ ω {a} = 0)
    (hpos : ∀ a b : ℝ, a < b → (0 ≤ a ∨ b ≤ 0) → 0 < g3plV γ ω (Ioo a b)) :
    volume (g3plHonSetZ Z Z' γ δ U L s t ω) = ∫⁻ b in g3plXWin γ δ U ω,
      s.indicator 1 (Z L (g3plF γ ω) b) *
        t.indicator 1 (Z' L (g3plF γ ω) (g3zPartner γ (g3plF γ ω) b)) ∂(g3plV γ ω) := by
  set ν := g3plV γ ω with hν
  have hfin : ∀ b : ℝ, ν (Icc b 0) ≠ ⊤ := fun b => (qBoundaryMeasure_Icc_lt_top γ _ _ _).ne
  set M := ν (Icc (-δ) 0) with hM
  have hMt : M ≠ ⊤ := hfin _
  have hM0 : 0 < M.toReal := ENNReal.toReal_pos
    ((hpos (-δ) 0 (by linarith) (Or.inr le_rfl)).trans_le
      (measure_mono Ioo_subset_Icc_self)).ne' hMt
  set U' := min U M.toReal with hU'
  have hU'0 : 0 < U' := lt_min hU hM0
  have hU'M : ENNReal.ofReal U' ≤ M :=
    (ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans (ENNReal.ofReal_toReal hMt).le
  have hzm : Measurable fun b : ℝ => Z L (g3plF γ ω) b :=
    measurable_zoomZ_pt hZm L _ measurable_id
  have hmass : Measurable fun b : ℝ => (ν (Icc b 0)).toReal := by
    refine ENNReal.measurable_toReal.comp (Antitone.measurable fun a b hab => ?_)
    exact measure_mono (Icc_subset_Icc_left hab)
  have hpart : Measurable fun b : ℝ => g3zPartner γ (g3plF γ ω) b :=
    measurable_lenRight.comp (f := fun b : ℝ => (ν, (ν (Icc b 0)).toReal))
      (measurable_const.prodMk hmass)
  have hFm : Measurable fun b => s.indicator (1 : LawD → ℝ≥0∞) (Z L (g3plF γ ω) b) *
      t.indicator 1 (Z' L (g3plF γ ω) (g3zPartner γ (g3plF γ ω) b)) :=
    ((measurable_one.indicator hs).comp hzm).mul
      ((measurable_one.indicator ht).comp (measurable_zoomZ_pt hZm' L _ hpart))
  have hcov := g1_setLIntegral_lenLeft_eq_win hU'0 hat
    (fun u v huv hv => hpos u v huv (Or.inr hv)) hfin ⟨δ, hδ, hU'M⟩ hFm
  have hwin : {b : ℝ | b < 0 ∧ ν (Icc b 0) ≤ ENNReal.ofReal U'} = g3plXWin γ δ U ω := by
    ext b
    simp only [g3plXWin, mem_setOf_eq, hU', ENNReal.ofReal_min, ENNReal.ofReal_toReal hMt,
      le_min_iff]
    exact Iff.rfl
  rw [hwin] at hcov
  rw [← hcov]
  have hT : MeasurableSet {ℓ : ℝ | Z L (g3plF γ ω) (lenLeft ν ℓ) ∈ s ∧
      Z' L (g3plF γ ω) (lenRight ν ℓ) ∈ t} :=
    ((measurable_zoomZ_pt hZm L _ (measurable_lenLeft_left ν)) hs).inter
      ((measurable_zoomZ_pt hZm' L _ (measurable_lenRight.comp (f := fun ℓ : ℝ => (ν, ℓ))
        (measurable_const.prodMk measurable_id))) ht)
  have hset : g3plHonSetZ Z Z' γ δ U L s t ω = {ℓ : ℝ | Z L (g3plF γ ω) (lenLeft ν ℓ) ∈ s ∧
      Z' L (g3plF γ ω) (lenRight ν ℓ) ∈ t} ∩ Ioc 0 U' := by
    ext ℓ
    simp only [g3plHonSetZ, mem_setOf_eq, mem_inter_iff, mem_Ioc, hU', le_min_iff]
    constructor
    · rintro ⟨⟨h0, hU⟩, hM', hs', ht'⟩
      exact ⟨⟨hs', ht'⟩, h0, hU, (ENNReal.ofReal_le_iff_le_toReal hMt).1 hM'⟩
    · rintro ⟨⟨hs', ht'⟩, h0, hU, hM'⟩
      exact ⟨⟨h0, hU⟩, (ENNReal.ofReal_le_iff_le_toReal hMt).2 hM', hs', ht'⟩
  rw [hset, ← Measure.restrict_apply' measurableSet_Ioc, ← lintegral_indicator_one hT]
  refine setLIntegral_congr_fun measurableSet_Ioc fun ℓ hℓ => ?_
  have hℓM : ENNReal.ofReal ℓ ≤ M := (ENNReal.ofReal_le_ofReal hℓ.2).trans hU'M
  have hlen : (ν (Icc (lenLeft ν ℓ) 0)).toReal = ℓ := by
    rw [measure_Icc_lenLeft_eq hδ hfin (fun a _ => hat a) hℓM, ENNReal.toReal_ofReal hℓ.1.le]
  have hP : g3zPartner γ (g3plF γ ω) (lenLeft ν ℓ) = lenRight ν ℓ := by
    show lenRight ν (ν (Icc (lenLeft ν ℓ) 0)).toReal = lenRight ν ℓ
    rw [hlen]
  simp only [hP]
  by_cases h1 : Z L (g3plF γ ω) (lenLeft ν ℓ) ∈ s <;>
    by_cases h2 : Z' L (g3plF γ ω) (lenRight ν ℓ) ∈ t <;>
    simp [Set.indicator, h1, h2]

/-- `g3plHonZ = g3plHonXZ`. -/
theorem g3plHonZ_eq_honXZ (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (hZm' : ∀ C, Measurable fun q : FieldSample × ℝ => Z' C q.1 q.2)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {δ U L : ℝ} (hδ : 0 < δ)
    (hU : 0 < U) {s t : Set LawD} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    g3plHonZ Z Z' γ δ U L s t = g3plHonXZ Z Z' γ δ U L s t := by
  unfold g3plHonZ g3plHonXZ
  refine lintegral_congr_ae ?_
  filter_upwards [ae_g3pField_good hγ hγ2, ae_g3plV_Ioo_pos hγ hγ2] with ω hω hpos
  exact g3plHonSetZ_volume_eq hZm hZm' hδ hU hs ht hω.2.2.1 hpos

end R18
end QuantumZipper
