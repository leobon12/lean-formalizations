import QuantumZipper.Proofs.Thm18.G2FixMixRoot

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 at fixed regions, the `R(x)` side: from the length coordinate to the rooted measure

The length partner `R = lenRight (ν₀ + ν₂) ℓ` of the scheme is the point with `ν_h[0, R] = ℓ`,
where the Palm length `ℓ` is Lebesgue on `(0, M(ω)]`, `M = g3Mass = ν_h[−δ, 0]` a.s. Changing
variables `ℓ = ν_h[0, y]` turns the length-rooted measure into the rooted measure at `R`:

  `g3LenRoot{(ω, ℓ, R) ∈ T} = E ∫_{[0, t₂+r₂]} 1_T(h, ν_h[0,y], y) 1{ν_h[0,y] ≤ M} ν_h(dy)`

for events `T` that keep `R` strictly inside `(0, t₂ + r₂)` (`g3LenRoot_rootedR`). This is the
second half of Sheffield's setting (arXiv:1012.4797, proof of Theorem 1.8, p. 71: "the same
applies when we zoom in near `R(x)`"), with the same conditioning as at `x`.

* `lenRight_eq_neg_lenLeft`: `lenRight m ℓ = −lenLeft (m ∘ neg) ℓ` (reflection);
* `setLIntegral_Ioc_lenRight`: the change of variables of `G2FixMixRoot.lean`, reflected;
* `G2FixMixRootRStmt`, `g2FixMixLenR_of_root`.

Own elementary proofs (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

/-! ## Reflection -/

theorem preimage_neg_Icc' (a b : ℝ) : (fun x : ℝ => -x) ⁻¹' Icc a b = Icc (-b) (-a) := by
  ext x
  simp only [mem_preimage, mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

theorem map_neg_Icc (m : Measure ℝ) (a b : ℝ) :
    (m.map fun x : ℝ => -x) (Icc a b) = m (Icc (-b) (-a)) := by
  rw [Measure.map_apply measurable_neg measurableSet_Icc, preimage_neg_Icc']

theorem lenRight_eq_neg_lenLeft (m : Measure ℝ) (ℓ : ℝ) :
    lenRight m ℓ = -lenLeft (m.map fun x : ℝ => -x) ℓ := by
  unfold lenRight lenLeft
  rw [neg_neg]
  congr 1
  ext y
  simp only [mem_ofPred_eq, map_neg_Icc, neg_neg, neg_zero]

/-- **Change of variables** `ℓ = m[0, y]` (no atoms on `[0, δ]`). -/
theorem setLIntegral_Ioc_lenRight {m : Measure ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hfin : ∀ b : ℝ, m (Icc 0 b) ≠ ⊤) (hat : ∀ t ∈ Icc 0 δ, m {t} = 0)
    {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ℓ in Ioc 0 (m (Icc 0 δ)).toReal, f (ℓ, lenRight m ℓ) =
      ∫⁻ y in Icc 0 δ, f ((m (Icc 0 y)).toReal, y) ∂m := by
  set m' := m.map fun x : ℝ => -x with hm'
  have hfin' : ∀ b : ℝ, m' (Icc b 0) ≠ ⊤ := fun b => by
    rw [hm', map_neg_Icc, neg_zero]; exact hfin _
  have hat' : ∀ t ∈ Icc (-δ) 0, m' {t} = 0 := fun t ht => by
    rw [hm', ← Icc_self, map_neg_Icc, Icc_self]
    exact hat _ ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hf' : Measurable fun q : ℝ × ℝ => f (q.1, -q.2) :=
    hf.comp (measurable_fst.prodMk measurable_snd.neg)
  have key := setLIntegral_Ioc_lenLeft hδ hfin' hat' hf'
  have e1 : m' (Icc (-δ) 0) = m (Icc 0 δ) := by rw [hm', map_neg_Icc, neg_zero, neg_neg]
  rw [e1] at key
  have e2 : ∀ ℓ, -lenLeft m' ℓ = lenRight m ℓ := fun ℓ => (lenRight_eq_neg_lenLeft m ℓ).symm
  simp only [e2] at key
  rw [key, hm', Measure.restrict_map measurable_neg measurableSet_Icc, preimage_neg_Icc',
    neg_zero, neg_neg]
  have hanti : Antitone fun x : ℝ => ((m.map fun x : ℝ => -x) (Icc x 0)).toReal :=
    fun a b hab => ENNReal.toReal_mono (hfin' a) (measure_mono (Icc_subset_Icc_left hab))
  have hg : Measurable fun x : ℝ => f (((m.map fun x : ℝ => -x) (Icc x 0)).toReal, -x) :=
    hf.comp (hanti.measurable.prodMk measurable_neg)
  rw [lintegral_map hg measurable_neg]
  refine lintegral_congr fun y => ?_
  simp only [map_neg_Icc, neg_neg, neg_zero]

/-! ## The scheme at `R(x)` -/

/-- **The (unnormalized) rooted measure at `R`**:
`g3RootIntR γ i F = E ∫_{[0, t₂+r₂]} F(h, ν_h[0,y], y) ν_h(dy)`. -/
def g3RootIntR (γ : ℝ) (i : G3Idx) (F : Ω₀ × ℝ × ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ y in Icc 0 (i.t₂ + i.r₂), F (ω, (g3Hν γ ω (Icc 0 y)).toReal, y) ∂(g3Hν γ ω)
    ∂gffBase.P

/-- The truncation `ℓ ≤ M(ω)` (a partner `x ∈ [−δ, 0]` exists). -/
def g3TM (γ : ℝ) (i : G3Idx) : Set (Ω₀ × ℝ × ℝ) := {q | ENNReal.ofReal q.2.1 ≤ g3Mass γ i q.1}

theorem measurableSet_g3TM (γ : ℝ) (i : G3Idx) : MeasurableSet (g3TM γ i) :=
  measurableSet_le (ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_snd))
    ((measurable_g3Mass γ i).comp measurable_fst)

theorem g3ν₀₂_Icc_ne_top (γ : ℝ) (i : G3Idx) (ω : Ω₀) (b : ℝ) :
    (g3ν₀ γ i ω + g3ν₂ γ i ω) (Icc 0 b) ≠ ⊤ := by
  have h₁ := bdryM_le_qBoundaryMeasure γ (gapField γ i.t₁ i.r₁ i.t₂ i.r₂ gffBase.X ω) (Icc 0 b)
  have h₂ := bdryM_le_qBoundaryMeasure γ (regionField γ i.t₂ i.r₂ gffBase.X ω) (Icc 0 b)
  rw [Measure.add_apply]
  exact (ENNReal.add_lt_top.2
    ⟨h₁.trans_lt (qBoundaryMeasure_Icc_lt_top γ _ _ _),
      h₂.trans_lt (qBoundaryMeasure_Icc_lt_top γ _ _ _)⟩).ne

/-- Beyond the mass of `[0, b]`, the partner is not in `(a, b)` (`0 < a`). -/
theorem lenRight_not_mem_of_gt {m : Measure ℝ} {a b ℓ : ℝ} (ha : 0 < a)
    (hℓ : m (Icc 0 b) < ENNReal.ofReal ℓ) : ¬ (a < lenRight m ℓ ∧ lenRight m ℓ < b) := by
  rintro ⟨h1, h2⟩
  set S := {y : ℝ | 0 < y ∧ ENNReal.ofReal ℓ ≤ m (Icc 0 y)} with hS
  have hRS : lenRight m ℓ = sInf S := rfl
  rcases S.eq_empty_or_nonempty with he | hne
  · rw [hRS, he, Real.sInf_empty] at h1; linarith
  · have hlow : b ≤ sInf S := le_csInf hne fun y hy => by
      by_contra hyb
      exact absurd (hy.2.trans (measure_mono (Icc_subset_Icc_right (not_le.1 hyb).le)))
        (not_le.2 hℓ)
    rw [hRS] at h2; linarith

theorem measurable_lenRight_left (m : Measure ℝ) : Measurable fun ℓ : ℝ => lenRight m ℓ :=
  Measurable.comp (g := fun q : Measure ℝ × ℝ => lenRight q.1 q.2)
    (f := fun ℓ : ℝ => ((m, ℓ) : Measure ℝ × ℝ)) measurable_lenRight
    (measurable_const.prodMk measurable_id)

theorem G3Idx.t₂_add_r₂ (i : G3Idx) : i.t₂ + i.r₂ = 1 / 2 + i.η / 4 := by
  unfold G3Idx.t₂ G3Idx.r₂; ring

theorem G3Idx.t₂_sub_r₂ (i : G3Idx) : i.t₂ - i.r₂ = 3 * i.η / 4 := by
  unfold G3Idx.t₂ G3Idx.r₂; ring

/-- **Length-rooted = rooted, at `R`**, for events keeping `R` in `(a, b)`, `0 < a`,
`b < t₂ + r₂`. -/
theorem g3LenRoot_rootedR {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx)
    {T : Set (Ω₀ × ℝ × ℝ)} (hT : MeasurableSet T) {a b : ℝ} (ha : 0 < a) (hb0 : 0 < b)
    (hb : b < i.t₂ + i.r₂) (hTsub : ∀ q ∈ T, a < q.2.2 ∧ q.2.2 < b) :
    g3LenRoot γ i {p | (p.1, p.2, g3R γ i p) ∈ T} =
      g3RootIntR γ i ((T ∩ g3TM γ i).indicator 1) := by
  have hS : MeasurableSet {p : Ω₀ × ℝ | (p.1, p.2, g3R γ i p) ∈ T} :=
    (measurable_fst.prodMk (measurable_snd.prodMk (measurable_g3R' γ i))) hT
  have hTM : MeasurableSet (T ∩ g3TM γ i) := hT.inter (measurableSet_g3TM γ i)
  rw [g3LenRoot_apply γ i hS, g3RootIntR]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_g3Fid_sets hγ hγ2, G3Fid.ae_normField_good gffBase.gff hγ hγ2]
    with ω hω hgood
  set m := g3ν₀ γ i ω + g3ν₂ γ i ω with hm
  have hwinsub : Icc 0 b ⊆ Ioo (-(3 * i.η / 4)) (1 / 2 + i.η / 4) := fun z hz =>
    ⟨by linarith [hz.1, i.hη], by linarith [hz.2, i.t₂_add_r₂]⟩
  have hwin : ∀ s ⊆ Icc 0 b, m s = g3Hν γ ω s := fun s hs => (hω i).2 s (hs.trans hwinsub)
  have hat : ∀ t ∈ Icc 0 b, m {t} = 0 := fun t ht => by
    rw [hwin {t} (singleton_subset_iff.2 ht)]; exact hgood.2.2 t
  have hM : g3Mass γ i ω ≠ ⊤ := (g3Mass_lt_top γ i ω).ne
  have hD : m (Icc 0 b) ≠ ⊤ := g3ν₀₂_Icc_ne_top γ i ω b
  have hsec' : MeasurableSet {ℓ : ℝ | (ω, ℓ, lenRight m ℓ) ∈ T ∩ g3TM γ i} :=
    (measurable_const.prodMk (measurable_id.prodMk (measurable_lenRight_left m))) hTM
  have hfT : Measurable fun q : ℝ × ℝ =>
      (T ∩ g3TM γ i).indicator (1 : Ω₀ × ℝ × ℝ → ℝ≥0∞) (ω, q.1, q.2) :=
    (measurable_one.indicator hTM).comp (measurable_const.prodMk measurable_id)
  have hset : {ℓ : ℝ | (ω, ℓ, g3R γ i (ω, ℓ)) ∈ T} ∩ Ioc 0 (g3Mass γ i ω).toReal =
      {ℓ : ℝ | (ω, ℓ, lenRight m ℓ) ∈ T ∩ g3TM γ i} ∩ Ioc 0 (m (Icc 0 b)).toReal := by
    ext ℓ
    constructor
    · rintro ⟨hP, h0, hMl⟩
      refine ⟨⟨hP, (ENNReal.ofReal_le_iff_le_toReal hM).2 hMl⟩, h0, ?_⟩
      by_contra hc
      exact lenRight_not_mem_of_gt ha ((ENNReal.lt_ofReal_iff_toReal_lt hD).2 (not_le.1 hc))
        (hTsub _ hP)
    · rintro ⟨⟨hP, hTl⟩, h0, -⟩
      exact ⟨hP, h0, (ENNReal.ofReal_le_iff_le_toReal hM).1 hTl⟩
  have e1 : volume ({ℓ : ℝ | (ω, ℓ, g3R γ i (ω, ℓ)) ∈ T} ∩ Ioc 0 (g3Mass γ i ω).toReal) =
      ∫⁻ ℓ in Ioc 0 (m (Icc 0 b)).toReal,
        (T ∩ g3TM γ i).indicator (1 : Ω₀ × ℝ × ℝ → ℝ≥0∞) (ω, ℓ, lenRight m ℓ) := by
    rw [hset, ← Measure.restrict_apply hsec', ← lintegral_indicator_one hsec']
    rfl
  rw [e1, setLIntegral_Ioc_lenRight (f := fun q : ℝ × ℝ => (T ∩ g3TM γ i).indicator 1 (ω, q.1, q.2))
    hb0 (g3ν₀₂_Icc_ne_top γ i ω) hat hfT]
  have hres : m.restrict (Icc 0 b) = (g3Hν γ ω).restrict (Icc 0 b) := by
    ext s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
    exact hwin _ inter_subset_right
  show ∫⁻ y, _ ∂(m.restrict (Icc 0 b)) = _
  rw [hres]
  rw [setLIntegral_congr_fun measurableSet_Icc (g := fun y =>
    (T ∩ g3TM γ i).indicator (1 : Ω₀ × ℝ × ℝ → ℝ≥0∞) (ω, (g3Hν γ ω (Icc 0 y)).toReal, y))
    fun y hy => by simp only; rw [hwin (Icc 0 y) (Icc_subset_Icc_right hy.2)]]
  rw [← lintegral_indicator measurableSet_Icc, ← lintegral_indicator measurableSet_Icc]
  refine lintegral_congr fun y => ?_
  by_cases hF : (ω, (g3Hν γ ω (Icc 0 y)).toReal, y) ∈ T
  · have hy := hTsub _ hF
    rw [indicator_of_mem (show y ∈ Icc 0 b from ⟨by linarith [hy.1], hy.2.le⟩),
      indicator_of_mem (show y ∈ Icc 0 (i.t₂ + i.r₂) from ⟨by linarith [hy.1], by linarith [hy.2]⟩)]
  · simp [Set.indicator_apply, hF]

/-! ## The `R`-side node in rooted form -/

/-- The rooted event `{zoom at y ∈ t, y a margin m inside region 2, (h, ν_h[0,y]) ∈ G}`. -/
def g3RootEvR (γ : ℝ) (i : G3Idx) (t : Set LawD) (m : ℝ) (G : Set (Ω₀ × ℝ)) :
    Set (Ω₀ × ℝ × ℝ) :=
  {q | zoomLaw γ i.C (normField γ gffBase.X q.1) q.2.2 ∈ t ∧ |q.2.2 - i.t₂| + m < i.r₂ ∧
    (q.1, q.2.1) ∈ G}

/-- The rooted event `{y a margin m inside region 2, (h, ν_h[0,y]) ∈ G}`. -/
def g3RootEvR0 (i : G3Idx) (m : ℝ) (G : Set (Ω₀ × ℝ)) : Set (Ω₀ × ℝ × ℝ) :=
  {q | |q.2.2 - i.t₂| + m < i.r₂ ∧ (q.1, q.2.1) ∈ G}

/-- **Conditional Proposition 5.5 at `R(x)`, rooted form**: under the rooted measure
`E ∫_{[0, t₂+r₂]} 1{ν_h[0,y] ≤ M} · ν_h(dy)` (`g3RootIntR`, `g3TM`; `M = g3Mass = ν_h[−δ,0]`
a.s.), the zoom of `h` at `y` (a margin `m` inside region 2) is asymptotically independent,
as `C → ∞` and uniformly, of every event `G` of the field outside the two regions and the length
`ν_h[0, y]`, with limit law `ν`. -/
def G2FixMixRootRStmt (γ : ℝ) (ν : Measure LawD) : Prop :=
  ∀ t ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∀ ε > 0, ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx,
    i.1 = (δ, η, C) → ∀ G : Set (gffBase.Ω × ℝ),
      MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
      |(g3RootIntR γ i ((g3RootEvR γ i t m G ∩ g3TM γ i).indicator 1)).toReal -
        ν.real t * (g3RootIntR γ i ((g3RootEvR0 i m G ∩ g3TM γ i).indicator 1)).toReal| ≤ ε

theorem measurableSet_g3RootEvR0 (i : G3Idx) (m : ℝ) {G : Set (Ω₀ × ℝ)}
    (hG : MeasurableSet G) : MeasurableSet (g3RootEvR0 i m G) := by
  have hf : Measurable fun q : Ω₀ × ℝ × ℝ => |q.2.2 - i.t₂| + m := by fun_prop
  exact (measurableSet_lt hf measurable_const).inter
    ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)) hG)

theorem measurableSet_g3RootEvR (γ : ℝ) (i : G3Idx) {t : Set LawD} (ht : MeasurableSet t)
    (m : ℝ) {G : Set (Ω₀ × ℝ)} (hG : MeasurableSet G) : MeasurableSet (g3RootEvR γ i t m G) :=
  ((measurable_zoomLaw γ i.C).comp (((measurable_normField_g3 γ).comp measurable_fst).prodMk
    (measurable_snd.comp measurable_snd)) ht).inter (measurableSet_g3RootEvR0 i m hG)

theorem g3RootEvR0_sub (i : G3Idx) (m : ℝ) (G : Set (Ω₀ × ℝ)) :
    ∀ q ∈ g3RootEvR0 i m G, i.t₂ - i.r₂ + m < q.2.2 ∧ q.2.2 < i.t₂ + i.r₂ - m := by
  intro q hq
  have h := hq.1
  constructor
  · have := neg_abs_le (q.2.2 - i.t₂); linarith
  · have := le_abs_self (q.2.2 - i.t₂); linarith

/-- **The `R`-side length-rooted node from the rooted node.** -/
theorem g2FixMixLenR_of_root {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ν : Measure LawD}
    (h : G2FixMixRootRStmt γ ν) : G2FixMixLenRStmt γ ν := by
  intro t ht δ η m hm ε hε
  filter_upwards [h t ht δ η m hm ε hε] with C hC i hi G hG
  have hGm : MeasurableSet G := (le_sup_right.trans (sig_le_g3 i i.t₁ i.r₁)) G hG
  by_cases hmr : m < i.r₂
  · have ha : 0 < i.t₂ - i.r₂ + m := by rw [i.t₂_sub_r₂]; linarith [i.hη]
    have hb0 : 0 < i.t₂ + i.r₂ - m := by linarith [i.t₂_add_r₂, i.hη]
    have hb : i.t₂ + i.r₂ - m < i.t₂ + i.r₂ := by linarith
    have e1 : g3Vf γ i ⁻¹' t ∩ {p | |g3R γ i p - i.t₂| + m < i.r₂} ∩ G =
        {p | (p.1, p.2, g3R γ i p) ∈ g3RootEvR γ i t m G} := by
      ext p
      simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, g3RootEvR, g3Vf, Prod.mk.eta]
      tauto
    have e2 : {p | |g3R γ i p - i.t₂| + m < i.r₂} ∩ G =
        {p | (p.1, p.2, g3R γ i p) ∈ g3RootEvR0 i m G} := by
      ext p
      simp only [mem_inter_iff, mem_ofPred_eq, g3RootEvR0, Prod.mk.eta]
    have r1 : (g3LenRoot γ i).real {p | (p.1, p.2, g3R γ i p) ∈ g3RootEvR γ i t m G} =
        (g3RootIntR γ i ((g3RootEvR γ i t m G ∩ g3TM γ i).indicator 1)).toReal := by
      rw [measureReal_def, g3LenRoot_rootedR hγ hγ2 i
        (measurableSet_g3RootEvR γ i (measurableSet_lawCyl ht) m hGm) ha hb0 hb
        (fun q hq => g3RootEvR0_sub i m G q hq.2)]
    have r2 : (g3LenRoot γ i).real {p | (p.1, p.2, g3R γ i p) ∈ g3RootEvR0 i m G} =
        (g3RootIntR γ i ((g3RootEvR0 i m G ∩ g3TM γ i).indicator 1)).toReal := by
      rw [measureReal_def, g3LenRoot_rootedR hγ hγ2 i (measurableSet_g3RootEvR0 i m hGm) ha hb0 hb
        (g3RootEvR0_sub i m G)]
    rw [e1, e2, r1, r2]
    exact hC i hi G hG
  · have hE : {p : Ω₀ × ℝ | |g3R γ i p - i.t₂| + m < i.r₂} = ∅ := by
      ext p
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      linarith [abs_nonneg (g3R γ i p - i.t₂), not_lt.1 hmr]
    rw [hE, inter_empty, empty_inter]
    simp only [measureReal_empty, mul_zero, sub_zero, abs_zero]
    exact hε.le

/-- **`G2FixMixStmt` from the two rooted nodes.** -/
theorem g2FixMixStmt_of_root {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {μ ν : Measure LawD}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hX : G2FixMixRootXStmt γ μ) (hR : G2FixMixRootRStmt γ ν) : G2FixMixStmt γ :=
  g2FixMixStmt_of_len hγ hγ2 (g2FixMixLenX_of_root hγ hγ2 hX) (g2FixMixLenR_of_root hγ hγ2 hR)

end Thm18Asm
end QuantumZipper
