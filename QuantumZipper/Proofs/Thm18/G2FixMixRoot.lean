import QuantumZipper.Proofs.Thm18.G2FixMixLen
import QuantumZipper.Proofs.Thm18.G2FullMixCampbell

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 at fixed regions, the `x` side: from the length coordinate to the rooted measure

Sheffield (arXiv:1012.4797, Lemma 5.6, p. 66, and Proposition 5.5, p. 65) works with the rooted
measure "sample `h` from `ν_h[−δ, 0] dh`, then `x` from `ν_h|[−δ,0]`", conditioning on the lengths
`L₁ = ν_h[a, x]`. The scheme instead samples the Palm length `ℓ` uniformly on `(0, M(ω)]` and sets
`x = lenLeft (ν₁ + ν₀) ℓ` (`g3LenRoot`, `G2FixMixLen.lean`). This file identifies the two:

* `measure_Icc_lenLeft_eq`: if `m` has no atoms on `[−δ, 0]`, then `m[lenLeft m ℓ, 0] = ℓ` for
  every `ℓ ∈ (0, m[−δ,0]]` (the quantile transform inverts the distribution function);
* `setLIntegral_Ioc_lenLeft`: `∫_{(0, m[−δ,0]]} f(ℓ, lenLeft m ℓ) dℓ = ∫_{[−δ,0]} f(m[x,0], x) m(dx)`
  (from the quantile transform `map_lenLeft_restrict_Ioc`, `G2FullMixCampbell.lean`);
* `g3LenRoot_rooted`: a.s. `ν₁ + ν₀ = ν_h` on `[−δ, 0]` (F2, `ae_g3Fid_sets`) and `ν_h` has no
  atoms (`G3Fid.ae_normField_good`), so for every measurable `T`

    `g3LenRoot{(ω, ℓ, x(ω,ℓ)) ∈ T} = E ∫_{[−δ,0]} 1_T(h, ν_h[x,0], x) ν_h(dx)`  (`g3RootInt`),

  with the **honest** boundary measure `ν_h = qBoundaryMeasure γ h` of Theorem 1.2's field;
* `G2FixMixRootXStmt`: the `x`-half of `G2FixMixStmt` for the rooted measure (Sheffield's
  Prop. 5.5 with the conditioning of the proof of Thm 1.8, p. 71: the field outside the two
  regions and the length `ν_h[x, 0]`), and `g2FixMixLenX_of_root`.

Own elementary proofs (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

/-! ## The quantile transform inverts the distribution function -/

/-- **No atoms**: `m[lenLeft m ℓ, 0] = ℓ` for `ℓ ∈ (0, m[−δ,0]]`. -/
theorem measure_Icc_lenLeft_eq {m : Measure ℝ} {δ ℓ : ℝ} (hδ : 0 < δ)
    (hfin : ∀ b : ℝ, m (Icc b 0) ≠ ⊤) (hat : ∀ t ∈ Icc (-δ) 0, m {t} = 0)
    (hℓ : ENNReal.ofReal ℓ ≤ m (Icc (-δ) 0)) :
    m (Icc (lenLeft m ℓ) 0) = ENNReal.ofReal ℓ := by
  set x := lenLeft m ℓ with hx
  have hxδ : -δ ≤ x := le_lenLeft_of_mass_le hδ hℓ
  have hx0 : x ≤ 0 := lenLeft_nonpos m ℓ
  refine le_antisymm ?_ ?_
  · -- `m[x, 0] = m(x, 0] = sup_n m[x + 1/(n+1), 0] ≤ ℓ`
    have hU : Ioc x 0 = ⋃ n : ℕ, Icc (x + 1 / ((n : ℝ) + 1)) 0 := by
      ext y
      simp only [mem_Ioc, mem_iUnion, mem_Icc]
      constructor
      · rintro ⟨h1, h2⟩
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h1)
        exact ⟨n, by linarith, h2⟩
      · rintro ⟨n, h1, h2⟩
        have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        exact ⟨by linarith, h2⟩
    have hmono : Monotone fun n : ℕ => Icc (x + 1 / ((n : ℝ) + 1)) (0 : ℝ) := by
      intro a b hab
      refine Icc_subset_Icc_left ?_
      have : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
      linarith
    have hIoc : m (Ioc x 0) ≤ ENNReal.ofReal ℓ := by
      rw [hU, hmono.measure_iUnion]
      refine iSup_le fun n => ?_
      set b := x + 1 / ((n : ℝ) + 1) with hb
      rcases lt_trichotomy b 0 with hb0 | hb0 | hb0
      · have ha : 0 < -b := neg_pos.2 hb0
        have hiff := neg_le_lenLeft_iff hδ hfin hℓ ha
        rw [neg_neg] at hiff
        have hnot : ¬ b ≤ lenLeft m ℓ := by
          rw [← hx]; have : 0 < 1 / ((n : ℝ) + 1) := by positivity
          linarith
        have := mt hiff.2 hnot
        exact (not_le.1 this).le
      · rw [hb0, Icc_self, hat 0 ⟨by linarith, le_rfl⟩]; exact bot_le
      · rw [Icc_eq_empty (not_le.2 hb0), measure_empty]; exact bot_le
    calc m (Icc x 0) ≤ m ({x} ∪ Ioc x 0) := measure_mono fun y hy => by
          rcases eq_or_lt_of_le hy.1 with h | h
          · exact Or.inl h.symm
          · exact Or.inr ⟨h, hy.2⟩
      _ ≤ m {x} + m (Ioc x 0) := measure_union_le _ _
      _ = m (Ioc x 0) := by rw [hat x ⟨hxδ, hx0⟩, zero_add]
      _ ≤ _ := hIoc
  · have h := ofReal_le_mass_Icc_of_lenLeft (a := -x) hδ hℓ (hfin _) (by rw [neg_neg])
    rwa [neg_neg] at h

/-- **Change of variables** `ℓ = m[x, 0]` (no atoms on `[−δ, 0]`). -/
theorem setLIntegral_Ioc_lenLeft {m : Measure ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hfin : ∀ b : ℝ, m (Icc b 0) ≠ ⊤) (hat : ∀ t ∈ Icc (-δ) 0, m {t} = 0)
    {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ℓ in Ioc 0 (m (Icc (-δ) 0)).toReal, f (ℓ, lenLeft m ℓ) =
      ∫⁻ x in Icc (-δ) 0, f ((m (Icc x 0)).toReal, x) ∂m := by
  have hanti : Antitone fun x : ℝ => (m (Icc x 0)).toReal := fun a b hab =>
    ENNReal.toReal_mono (hfin a) (measure_mono (Icc_subset_Icc_left hab))
  have hg : Measurable fun x : ℝ => f ((m (Icc x 0)).toReal, x) :=
    hf.comp (hanti.measurable.prodMk measurable_id)
  rw [← map_lenLeft_restrict_Ioc hδ hfin, lintegral_map hg (measurable_lenLeft_left m)]
  refine setLIntegral_congr_fun measurableSet_Ioc fun ℓ hℓ => ?_
  have hℓM : ENNReal.ofReal ℓ ≤ m (Icc (-δ) 0) :=
    (ENNReal.ofReal_le_ofReal hℓ.2).trans_eq (ENNReal.ofReal_toReal (hfin _))
  show f (ℓ, lenLeft m ℓ) = f ((m (Icc (lenLeft m ℓ) 0)).toReal, lenLeft m ℓ)
  rw [measure_Icc_lenLeft_eq hδ hfin hat hℓM, ENNReal.toReal_ofReal hℓ.1.le]

/-! ## The rooted measure of the scheme -/

/-- **The (unnormalized) rooted measure** with the length coordinate:
`g3RootInt γ i F = E ∫_{[−δ,0]} F(h, ν_h[x,0], x) ν_h(dx)`, `ν_h = qBoundaryMeasure γ h`,
`h = normField γ X₀` (Sheffield, Lemma 5.6, p. 66). -/
def g3RootInt (γ : ℝ) (i : G3Idx) (F : Ω₀ × ℝ × ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ x in Icc (-i.δ) 0, F (ω, (g3Hν γ ω (Icc x 0)).toReal, x) ∂(g3Hν γ ω) ∂gffBase.P

/-- **Length-rooted = rooted.** -/
theorem g3LenRoot_rooted {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx)
    {T : Set (Ω₀ × ℝ × ℝ)} (hT : MeasurableSet T) :
    g3LenRoot γ i {p | (p.1, p.2, g3X γ i p) ∈ T} = g3RootInt γ i (T.indicator 1) := by
  have hS : MeasurableSet {p : Ω₀ × ℝ | (p.1, p.2, g3X γ i p) ∈ T} :=
    (measurable_fst.prodMk (measurable_snd.prodMk (measurable_g3X' γ i))) hT
  have hδ : 0 < i.δ := i.hη.trans i.hηδ
  rw [g3LenRoot_apply γ i hS, g3RootInt]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_g3Fid_sets hγ hγ2, G3Fid.ae_normField_good gffBase.gff hγ hγ2]
    with ω hω hgood
  set m := g3ν₁ γ i ω + g3ν₀ γ i ω with hm
  have hwin : ∀ s ⊆ Icc (-i.δ) 0, m s = g3Hν γ ω s := fun s hs =>
    (hω i).1 s (hs.trans (Icc_neg_subset_win i (by linarith [i.hη])))
  have hat : ∀ t ∈ Icc (-i.δ) 0, m {t} = 0 := fun t ht => by
    rw [hwin {t} (singleton_subset_iff.2 ht)]; exact hgood.2.2 t
  have hfT : Measurable fun q : ℝ × ℝ => T.indicator (1 : Ω₀ × ℝ × ℝ → ℝ≥0∞) (ω, q.1, q.2) :=
    (measurable_one.indicator hT).comp (measurable_const.prodMk measurable_id)
  have hsec : MeasurableSet {ℓ : ℝ | (ω, ℓ, g3X γ i (ω, ℓ)) ∈ T} :=
    measurable_prodMk_left hS
  -- the section as a set integral of the indicator
  have e1 : volume ({ℓ : ℝ | (ω, ℓ, g3X γ i (ω, ℓ)) ∈ T} ∩
      Ioc 0 (g3Mass γ i ω).toReal) =
      ∫⁻ ℓ in Ioc 0 (m (Icc (-i.δ) 0)).toReal,
        T.indicator (1 : Ω₀ × ℝ × ℝ → ℝ≥0∞) (ω, ℓ, lenLeft m ℓ) := by
    rw [show g3Mass γ i ω = m (Icc (-i.δ) 0) from rfl]
    calc volume ({ℓ : ℝ | (ω, ℓ, g3X γ i (ω, ℓ)) ∈ T} ∩ Ioc 0 (m (Icc (-i.δ) 0)).toReal)
        = (volume.restrict (Ioc 0 (m (Icc (-i.δ) 0)).toReal))
            {ℓ : ℝ | (ω, ℓ, g3X γ i (ω, ℓ)) ∈ T} := (Measure.restrict_apply hsec).symm
      _ = ∫⁻ ℓ in Ioc 0 (m (Icc (-i.δ) 0)).toReal,
            {ℓ : ℝ | (ω, ℓ, g3X γ i (ω, ℓ)) ∈ T}.indicator 1 ℓ :=
          (lintegral_indicator_one hsec).symm
      _ = _ := by
        refine lintegral_congr fun ℓ => ?_
        by_cases h : (ω, ℓ, g3X γ i (ω, ℓ)) ∈ T
        · rw [indicator_of_mem (show ℓ ∈ {ℓ : ℝ | (ω, ℓ, g3X γ i (ω, ℓ)) ∈ T} from h),
            indicator_of_mem (show (ω, ℓ, lenLeft m ℓ) ∈ T from h)]
          rfl
        · rw [indicator_of_notMem (show ℓ ∉ {ℓ : ℝ | (ω, ℓ, g3X γ i (ω, ℓ)) ∈ T} from h),
            indicator_of_notMem (show (ω, ℓ, lenLeft m ℓ) ∉ T from h)]
  rw [e1, setLIntegral_Ioc_lenLeft (f := fun q : ℝ × ℝ => T.indicator 1 (ω, q.1, q.2)) hδ
    (g3ν_Icc_ne_top γ i ω) hat hfT]
  -- replace `m` by the honest `ν_h` on `[−δ, 0]`
  have hres : m.restrict (Icc (-i.δ) 0) = (g3Hν γ ω).restrict (Icc (-i.δ) 0) := by
    ext s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
    exact hwin _ inter_subset_right
  show ∫⁻ x, _ ∂(m.restrict (Icc (-i.δ) 0)) = _
  rw [hres]
  refine setLIntegral_congr_fun measurableSet_Icc fun x hx => ?_
  simp only
  rw [hwin (Icc x 0) (Icc_subset_Icc_left hx.1)]

/-! ## The `x`-side node in rooted form -/

/-- The rooted event `{zoom at x ∈ s, x a margin m inside region 1, (h, ν_h[x,0]) ∈ G}`. -/
def g3RootEvX (γ : ℝ) (i : G3Idx) (s : Set LawD) (m : ℝ) (G : Set (Ω₀ × ℝ)) :
    Set (Ω₀ × ℝ × ℝ) :=
  {q | zoomLaw γ i.C (normField γ gffBase.X q.1) q.2.2 ∈ s ∧ |q.2.2 - i.t₁| + m < i.r₁ ∧
    (q.1, q.2.1) ∈ G}

/-- The rooted event `{x a margin m inside region 1, (h, ν_h[x,0]) ∈ G}`. -/
def g3RootEvX0 (i : G3Idx) (m : ℝ) (G : Set (Ω₀ × ℝ)) : Set (Ω₀ × ℝ × ℝ) :=
  {q | |q.2.2 - i.t₁| + m < i.r₁ ∧ (q.1, q.2.1) ∈ G}

/-- **Conditional Proposition 5.5 at `x`, rooted form** (Sheffield, arXiv:1012.4797, Prop. 5.5,
p. 65, with the conditioning of the proof of Thm 1.8, p. 71): under the rooted measure
`E ∫_{[−δ,0]} · ν_h(dx)` (`g3RootInt`), the zoom of `h` at `x` (a margin `m` inside region 1)
is asymptotically independent, as `C → ∞` and uniformly, of every event `G` of the field outside
the two regions and the length `ν_h[x, 0]`, with limit law `μ`. -/
def G2FixMixRootXStmt (γ : ℝ) (μ : Measure LawD) : Prop :=
  ∀ s ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∀ ε > 0, ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx,
    i.1 = (δ, η, C) → ∀ G : Set (gffBase.Ω × ℝ),
      MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
      |(g3RootInt γ i ((g3RootEvX γ i s m G).indicator 1)).toReal -
        μ.real s * (g3RootInt γ i ((g3RootEvX0 i m G).indicator 1)).toReal| ≤ ε

theorem measurableSet_g3RootEvX0 (i : G3Idx) (m : ℝ) {G : Set (Ω₀ × ℝ)}
    (hG : MeasurableSet G) : MeasurableSet (g3RootEvX0 i m G) := by
  have hf : Measurable fun q : Ω₀ × ℝ × ℝ => |q.2.2 - i.t₁| + m := by fun_prop
  exact (measurableSet_lt hf measurable_const).inter
    ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)) hG)

theorem measurableSet_g3RootEvX (γ : ℝ) (i : G3Idx) {s : Set LawD} (hs : MeasurableSet s)
    (m : ℝ) {G : Set (Ω₀ × ℝ)} (hG : MeasurableSet G) : MeasurableSet (g3RootEvX γ i s m G) :=
  ((measurable_zoomLaw γ i.C).comp (((measurable_normField_g3 γ).comp measurable_fst).prodMk
    (measurable_snd.comp measurable_snd)) hs).inter (measurableSet_g3RootEvX0 i m hG)

/-- **The `x`-side length-rooted node from the rooted node.** -/
theorem g2FixMixLenX_of_root {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {μ : Measure LawD}
    (h : G2FixMixRootXStmt γ μ) : G2FixMixLenXStmt γ μ := by
  intro s hs δ η m hm ε hε
  filter_upwards [h s hs δ η m hm ε hε] with C hC i hi G hG
  have hGm : MeasurableSet G := (le_sup_right.trans (sig_le_g3 i i.t₁ i.r₁)) G hG
  have e1 : g3Uf γ i ⁻¹' s ∩ {p | |g3X γ i p - i.t₁| + m < i.r₁} ∩ G =
      {p | (p.1, p.2, g3X γ i p) ∈ g3RootEvX γ i s m G} := by
    ext p
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, g3RootEvX, g3Uf, Prod.mk.eta]
    tauto
  have e2 : {p | |g3X γ i p - i.t₁| + m < i.r₁} ∩ G =
      {p | (p.1, p.2, g3X γ i p) ∈ g3RootEvX0 i m G} := by
    ext p
    simp only [mem_inter_iff, mem_ofPred_eq, g3RootEvX0, Prod.mk.eta]
  have r1 : (g3LenRoot γ i).real {p | (p.1, p.2, g3X γ i p) ∈ g3RootEvX γ i s m G} =
      (g3RootInt γ i ((g3RootEvX γ i s m G).indicator 1)).toReal := by
    rw [measureReal_def,
      g3LenRoot_rooted hγ hγ2 i (measurableSet_g3RootEvX γ i (measurableSet_lawCyl hs) m hGm)]
  have r2 : (g3LenRoot γ i).real {p | (p.1, p.2, g3X γ i p) ∈ g3RootEvX0 i m G} =
      (g3RootInt γ i ((g3RootEvX0 i m G).indicator 1)).toReal := by
    rw [measureReal_def, g3LenRoot_rooted hγ hγ2 i (measurableSet_g3RootEvX0 i m hGm)]
  rw [e1, e2, r1, r2]
  exact hC i hi G hG

end Thm18Asm
end QuantumZipper
