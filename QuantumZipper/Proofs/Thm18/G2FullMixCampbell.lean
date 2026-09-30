import QuantumZipper.Proofs.Thm18.G2FullMixLeb
import QuantumZipper.Proofs.Thm18.G3GeoCore

/-!
# G2 (full field, mixing form): the Palm point is `ν_h|[−δ,0]`-distributed given the field

The Palm point of the concrete G3 scheme is `x = lenLeft m ℓ` (`m = ν₁ + ν₀`, the boundary length
read from region 1 and the gap), where, given the field, `ℓ` is Lebesgue on `(0, m[−δ, 0]]`
(`g3PalmLaw_apply_eq_lebesgue`). The **quantile transform** `ℓ ↦ lenLeft m ℓ` (first point to the
left of `0` with `m[x, 0] ≥ ℓ`) pushes Lebesgue measure on `(0, m[−δ,0]]` to `m|[−δ,0]`
(`map_lenLeft_restrict_Ioc`), for any measure `m` finite on the intervals `[b, 0]`. Hence
(`g3PalmLaw_fst_g3X`):

  `P_Palm((ω, x) ∈ T) = Z⁻¹ ∫ (ν₁ + ν₀)|[−δ,0]{x : (ω, x) ∈ T} dP₀(ω)`,

i.e. the Palm law of `(field, x)` is the rooted measure "sample `h` from `ν_h[−δ,0] dh`
(normalized), then `x` from `ν_h|[−δ,0]`" of Sheffield, arXiv:1012.4797, Lemma 5.6 (p. 66) and
Proposition 5.5 (p. 65); the Duplantier–Sheffield Palm formula (arXiv:0808.1560, §3.3, p. 22;
`PalmNorm.palm_formula_norm`) applies to it.

The quantile transform is standard (e.g. the "inverse transform sampling" for a Stieltjes
measure); no mathlib version was found (grep `quantile`, `Stieltjes`), so this is an own
elementary proof (AGENT_GUIDE cost rule): both sides are finite measures on `ℝ` agreeing on every
`[c, ∞)` (`ext_of_Ici`), by the level characterization `−a ≤ lenLeft m ℓ ↔ ℓ ≤ m[−a, 0]`
(`le_lenLeft_of_mass_le`, `ofReal_le_mass_Icc_of_lenLeft`, `G3GeoCore.lean`), and at `c = 0` by
continuity from above.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

theorem lenLeft_nonpos (m : Measure ℝ) (ℓ : ℝ) : lenLeft m ℓ ≤ 0 := by
  rw [lenLeft_eq_neg_sInf, neg_nonpos]
  exact Real.sInf_nonneg fun y hy => hy.1.le

theorem measurable_lenLeft_left (m : Measure ℝ) : Measurable fun ℓ : ℝ => lenLeft m ℓ := by
  exact Measurable.comp (g := fun q : Measure ℝ × ℝ => lenLeft q.1 q.2)
    (f := fun ℓ : ℝ => ((m, ℓ) : Measure ℝ × ℝ)) measurable_lenLeft
    (measurable_const.prodMk measurable_id)

/-- **Level characterization of the Palm point.** -/
theorem neg_le_lenLeft_iff {m : Measure ℝ} {δ ℓ a : ℝ} (hδ : 0 < δ)
    (hfin : ∀ b : ℝ, m (Icc b 0) ≠ ⊤) (hℓ : ENNReal.ofReal ℓ ≤ m (Icc (-δ) 0)) (ha : 0 < a) :
    -a ≤ lenLeft m ℓ ↔ ENNReal.ofReal ℓ ≤ m (Icc (-a) 0) :=
  ⟨fun hx => ofReal_le_mass_Icc_of_lenLeft hδ hℓ (hfin _) hx, fun h => le_lenLeft_of_mass_le ha h⟩

/-- **Quantile transform**: `lenLeft m` pushes Lebesgue measure on `(0, m[−δ, 0]]` to
`m|[−δ, 0]`. -/
theorem map_lenLeft_restrict_Ioc {m : Measure ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hfin : ∀ b : ℝ, m (Icc b 0) ≠ ⊤) :
    (volume.restrict (Ioc 0 (m (Icc (-δ) 0)).toReal)).map (lenLeft m) =
      m.restrict (Icc (-δ) 0) := by
  set M := m (Icc (-δ) 0) with hMdef
  have hM : M ≠ ⊤ := hfin _
  have hmeas := measurable_lenLeft_left m
  have : IsFiniteMeasure (volume.restrict (Ioc 0 M.toReal)) :=
    isFiniteMeasure_restrict.2 (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have : IsFiniteMeasure (m.restrict (Icc (-δ) 0)) := isFiniteMeasure_restrict.2 hM
  have hIoc : ∀ ℓ ∈ Ioc 0 M.toReal, ENNReal.ofReal ℓ ≤ M := fun ℓ hℓ =>
    (ENNReal.ofReal_le_ofReal hℓ.2).trans_eq (ENNReal.ofReal_toReal hM)
  set μ₁ := (volume.restrict (Ioc 0 M.toReal)).map (lenLeft m) with hμ₁
  set μ₂ := m.restrict (Icc (-δ) 0) with hμ₂
  have hmap : ∀ c : ℝ, μ₁ (Ici c) = volume (lenLeft m ⁻¹' Ici c ∩ Ioc 0 M.toReal) := fun c => by
    rw [hμ₁, Measure.map_apply hmeas measurableSet_Ici,
      Measure.restrict_apply (hmeas measurableSet_Ici)]
  have hres : ∀ c : ℝ, μ₂ (Ici c) = m (Ici c ∩ Icc (-δ) 0) := fun c =>
    Measure.restrict_apply measurableSet_Ici
  have hne : ∀ c : ℝ, c ≠ 0 → μ₁ (Ici c) = μ₂ (Ici c) := by
    intro c hc0
    rw [hmap, hres]
    rcases lt_or_gt_of_ne hc0 with hc | hc
    · rcases le_or_gt c (-δ) with hcδ | hcδ
      · have e1 : lenLeft m ⁻¹' Ici c ∩ Ioc 0 M.toReal = Ioc 0 M.toReal := by
          refine inter_eq_right.2 fun ℓ hℓ => ?_
          exact hcδ.trans (le_lenLeft_of_mass_le hδ (hIoc ℓ hℓ))
        have e2 : Ici c ∩ Icc (-δ) 0 = Icc (-δ) 0 :=
          inter_eq_right.2 fun x hx => hcδ.trans hx.1
        rw [e1, e2, Real.volume_Ioc, sub_zero, ENNReal.ofReal_toReal hM]
      · have hcM : m (Icc c 0) ≤ M := measure_mono (Icc_subset_Icc_left hcδ.le)
        have e1 : lenLeft m ⁻¹' Ici c ∩ Ioc 0 M.toReal = Ioc 0 (m (Icc c 0)).toReal := by
          ext ℓ
          simp only [mem_inter_iff, mem_preimage, mem_Ici, mem_Ioc]
          constructor
          · rintro ⟨hx, h0, hℓ⟩
            have hiff := neg_le_lenLeft_iff hδ hfin (hIoc ℓ ⟨h0, hℓ⟩) (neg_pos.2 hc)
            rw [neg_neg] at hiff
            exact ⟨h0, (ENNReal.ofReal_le_iff_le_toReal (hfin c)).1 (hiff.1 hx)⟩
          · rintro ⟨h0, hℓ⟩
            have hℓM : ℓ ≤ M.toReal := hℓ.trans (ENNReal.toReal_mono hM hcM)
            have hiff := neg_le_lenLeft_iff hδ hfin (hIoc ℓ ⟨h0, hℓM⟩) (neg_pos.2 hc)
            rw [neg_neg] at hiff
            exact ⟨hiff.2 ((ENNReal.ofReal_le_iff_le_toReal (hfin c)).2 hℓ), h0, hℓM⟩
        have e2 : Ici c ∩ Icc (-δ) 0 = Icc c 0 := by
          ext x
          simp only [mem_inter_iff, mem_Ici, mem_Icc]
          constructor
          · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
          · rintro ⟨h1, h3⟩; exact ⟨h1, by linarith, h3⟩
        rw [e1, e2, Real.volume_Ioc, sub_zero, ENNReal.ofReal_toReal (hfin c)]
    · have e1 : lenLeft m ⁻¹' Ici c ∩ Ioc 0 M.toReal = ∅ := by
        ext ℓ
        simp only [mem_inter_iff, mem_preimage, mem_Ici, mem_empty_iff_false, iff_false,
          not_and]
        intro hx
        exact absurd (hx.trans (lenLeft_nonpos m ℓ)) (not_le.2 hc)
      have e2 : Ici c ∩ Icc (-δ) 0 = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_Ici, mem_Icc, mem_empty_iff_false, iff_false, not_and]
        intro h1 _ h3
        linarith
      rw [e1, e2, measure_empty, measure_empty]
  refine Measure.ext_of_Ici μ₁ μ₂ fun c => ?_
  rcases ne_or_eq c 0 with hc | rfl
  · exact hne c hc
  -- `c = 0`: continuity from above along `Ici (-r)`, `r ↓ 0`
  have hlim : ∀ μ : Measure ℝ, IsFiniteMeasure μ →
      Tendsto (μ ∘ fun r : ℝ => Ici (-r)) (𝓝[Ioi 0] 0) (𝓝 (μ (⋂ r > (0 : ℝ), Ici (-r)))) :=
    fun μ _ => tendsto_measure_biInter_gt (fun r _ => measurableSet_Ici.nullMeasurableSet)
      (fun r r' _ hrr => Ici_subset_Ici.2 (by linarith)) ⟨1, one_pos, measure_ne_top _ _⟩
  have hI : (⋂ r > (0 : ℝ), Ici (-r)) = Ici 0 := by
    ext x
    simp only [mem_iInter, mem_Ici]
    constructor
    · intro h
      refine le_of_forall_pos_le_add fun e he => ?_
      have := h e he
      linarith
    · intro h r hr; linarith
  have t1 := hlim μ₁ inferInstance
  have t2 := hlim μ₂ inferInstance
  rw [hI] at t1 t2
  refine tendsto_nhds_unique t1 (t2.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (hne (-r) (neg_ne_zero.2 (ne_of_gt hr))).symm

section Palm

variable (γ : ℝ) (i : G3Idx)

local notation "Ω₀" => gffBase.Ω

theorem g3ν_Icc_ne_top (ω : Ω₀) (b : ℝ) : (g3ν₁ γ i ω + g3ν₀ γ i ω) (Icc b 0) ≠ ⊤ := by
  have h₁ := bdryM_le_qBoundaryMeasure γ (regionField γ i.t₁ i.r₁ gffBase.X ω) (Icc b 0)
  have h₂ := bdryM_le_qBoundaryMeasure γ (gapField γ i.t₁ i.r₁ i.t₂ i.r₂ gffBase.X ω) (Icc b 0)
  rw [Measure.add_apply]
  exact (ENNReal.add_lt_top.2
    ⟨h₁.trans_lt (qBoundaryMeasure_Icc_lt_top γ _ _ _),
      h₂.trans_lt (qBoundaryMeasure_Icc_lt_top γ _ _ _)⟩).ne

end Palm

end Thm18Asm
end QuantumZipper
