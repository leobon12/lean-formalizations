import QuantumZipper.Proofs.Thm18.ZqT7VRed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-TYP (8): the length-partner map does not charge null sets

For a locally finite atomless measure `m` on `ℝ`, the length partner
`R(x) = lenRight m (m[x, 0])` of `x < 0` is the composition of the distribution function with the
right quantile function, so it maps `m|(−∞,0]` into a measure absolutely continuous with respect
to `m|(0,∞)`: by the quantile transform (`map_lenLeft_restrict_Ioc`), `m|[−δ,0]` is the image of
Lebesgue measure on `(0, m[−δ,0]]` under `lenLeft m`, `R ∘ lenLeft m = lenRight m` there
(`measure_Icc_lenLeft_eq`, no atoms), and `lenRight m` pushes Lebesgue measure on
`(0, m[0,K]]` to `m|[0,K]` (reflection of the quantile transform, `map_lenRight_restrict_Ioc`).
For `x ≥ 0`, `R(x) = lenRight m 0 = 0`. Hence `partner_ae_not_mem` and
`g3ZqTVPartnerStmt_holds` (the boundary measure of `V + logSing` is a.s. atomless,
`WedgeBdry.ae_bReg_logSing`).

Own elementary proof (AGENT_GUIDE cost rule: standard quantile-transform facts).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace ZqT

theorem preimage_neg_Icc' (a b : ℝ) : (Neg.neg ⁻¹' Icc a b : Set ℝ) = Icc (-b) (-a) := by
  ext x
  simp only [mem_preimage, mem_Icc]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- `lenRight` is `lenLeft` of the reflected measure, reflected. -/
theorem lenRight_eq_neg_lenLeft_map (m : Measure ℝ) (ℓ : ℝ) :
    lenRight m ℓ = -lenLeft (m.map Neg.neg) ℓ := by
  have e : ∀ y : ℝ, (m.map Neg.neg) (Icc (-y) 0) = m (Icc 0 y) := fun y => by
    rw [Measure.map_apply measurable_neg measurableSet_Icc, preimage_neg_Icc', neg_zero, neg_neg]
  simp only [lenLeft, lenRight, neg_neg, e]

/-- **Quantile transform on the right.** -/
theorem map_lenRight_restrict_Ioc {m : Measure ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hfin : ∀ b : ℝ, m (Icc 0 b) ≠ ⊤) :
    (volume.restrict (Ioc 0 (m (Icc 0 δ)).toReal)).map (lenRight m) = m.restrict (Icc 0 δ) := by
  set m' := m.map Neg.neg with hm'
  have e : ∀ y : ℝ, m' (Icc (-y) 0) = m (Icc 0 y) := fun y => by
    rw [hm', Measure.map_apply measurable_neg measurableSet_Icc, preimage_neg_Icc', neg_zero,
      neg_neg]
  have hfin' : ∀ b : ℝ, m' (Icc b 0) ≠ ⊤ := fun b => by
    have := e (-b); rw [neg_neg] at this; rw [this]; exact hfin _
  have h := map_lenLeft_restrict_Ioc (m := m') hδ hfin'
  rw [e] at h
  have hf : lenRight m = Neg.neg ∘ lenLeft m' := funext fun ℓ => lenRight_eq_neg_lenLeft_map m ℓ
  rw [hf, ← Measure.map_map measurable_neg (measurable_lenLeft_left m'), h,
    Measure.restrict_map measurable_neg measurableSet_Icc,
    Measure.map_map measurable_neg measurable_neg]
  have hid : (Neg.neg ∘ Neg.neg : ℝ → ℝ) = id := funext fun x => neg_neg x
  rw [hid, Measure.map_id, preimage_neg_Icc', neg_zero, neg_neg]

/-- `lenRight m 0 = 0`. -/
theorem lenRight_zero (m : Measure ℝ) : lenRight m 0 = 0 := by
  have : {y : ℝ | 0 < y ∧ ENNReal.ofReal 0 ≤ m (Icc 0 y)} = Ioi 0 := by
    ext y; simp
  rw [lenRight, this, csInf_Ioi]

/-- `lenRight m ℓ > 0` needs `ℓ ≤ m[0, K]` for some `K`. -/
theorem exists_nat_of_lenRight_pos {m : Measure ℝ} {ℓ : ℝ} (h : 0 < lenRight m ℓ) :
    ∃ K : ℕ, ENNReal.ofReal ℓ ≤ m (Icc 0 K) := by
  by_contra hn
  push_neg at hn
  have hempty : {y : ℝ | 0 < y ∧ ENNReal.ofReal ℓ ≤ m (Icc 0 y)} = ∅ := by
    ext y
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_le]
    intro hy
    obtain ⟨K, hK⟩ := exists_nat_ge y
    exact lt_of_le_of_lt (measure_mono (Icc_subset_Icc_right hK)) (hn K)
  rw [lenRight, hempty, Real.sInf_empty] at h
  exact lt_irrefl _ h

/-- **The partner map does not charge null subsets of `(0, ∞)`.** -/
theorem partner_ae_not_mem {m : Measure ℝ} [IsLocallyFiniteMeasure m] (hat : ∀ t, m {t} = 0)
    {S : Set ℝ} (hS : S ⊆ Ioi 0) (h0 : m S = 0) :
    ∀ᵐ x ∂m, lenRight m (m (Icc x 0)).toReal ∉ S := by
  obtain ⟨S', hSS', hS'm, hS'0, hS'pos⟩ : ∃ S' : Set ℝ, S ⊆ S' ∧ MeasurableSet S' ∧ m S' = 0 ∧
      S' ⊆ Ioi 0 :=
    ⟨toMeasurable m S ∩ Ioi 0, fun x hx => ⟨subset_toMeasurable m S hx, hS hx⟩,
      (measurableSet_toMeasurable m S).inter measurableSet_Ioi,
      measure_mono_null inter_subset_left (by rw [measure_toMeasurable]; exact h0),
      inter_subset_right⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ → ℝ, ∀ x, R x = lenRight m (m (Icc x 0)).toReal :=
    ⟨fun x => lenRight m (m (Icc x 0)).toReal, fun _ => rfl⟩
  suffices H : m (R ⁻¹' S') = 0 by
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) H
    have hx' : lenRight m (m (Icc x 0)).toReal ∈ S := not_not.1 hx
    show R x ∈ S'
    rw [hR]; exact hSS' hx'
  have hfin : ∀ b : ℝ, m (Icc b 0) ≠ ⊤ := fun b => measure_Icc_lt_top.ne
  have hfin0 : ∀ b : ℝ, m (Icc 0 b) ≠ ⊤ := fun b => measure_Icc_lt_top.ne
  have hFm : Measurable fun x : ℝ => (m (Icc x 0)).toReal :=
    Antitone.measurable fun x y hxy =>
      ENNReal.toReal_mono (hfin x) (measure_mono (Icc_subset_Icc_left hxy))
  have hmeas : Measurable (lenRight m) :=
    measurable_lenRight.comp (measurable_const.prodMk measurable_id)
  have hRm : Measurable R := by
    have e : R = fun x => lenRight m (m (Icc x 0)).toReal := funext hR
    rw [e]; exact hmeas.comp hFm
  have hT : MeasurableSet (R ⁻¹' S') := hRm hS'm
  -- the right quantile does not charge `S'`
  have hL : volume {ℓ : ℝ | 0 < ℓ ∧ lenRight m ℓ ∈ S'} = 0 := by
    have hsub : {ℓ : ℝ | 0 < ℓ ∧ lenRight m ℓ ∈ S'} ⊆
        ⋃ K : ℕ, Ioc 0 (m (Icc 0 ((K : ℝ) + 1))).toReal ∩ lenRight m ⁻¹' S' := by
      rintro ℓ ⟨hℓ, hℓS⟩
      obtain ⟨K, hK⟩ := exists_nat_of_lenRight_pos (hS'pos hℓS)
      refine mem_iUnion.2 ⟨K, ⟨hℓ, ?_⟩, hℓS⟩
      rw [← ENNReal.ofReal_le_iff_le_toReal (hfin0 _)]
      exact hK.trans (measure_mono (Icc_subset_Icc_right (by linarith)))
    refine measure_mono_null hsub (measure_iUnion_null fun K => ?_)
    have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
    rw [inter_comm, ← Measure.restrict_apply (hmeas hS'm), ← Measure.map_apply hmeas hS'm,
      map_lenRight_restrict_Ioc hK hfin0, Measure.restrict_apply hS'm]
    exact measure_mono_null inter_subset_left hS'0
  -- the left half-line: quantile transform
  have hleft : ∀ n : ℕ, m (R ⁻¹' S' ∩ Icc (-((n : ℝ) + 1)) 0) = 0 := by
    intro n
    have hδ : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hmap := map_lenLeft_restrict_Ioc (m := m) hδ hfin
    rw [← Measure.restrict_apply hT, ← hmap, Measure.map_apply (measurable_lenLeft_left m) hT,
      Measure.restrict_apply (measurable_lenLeft_left m hT)]
    refine measure_mono_null ?_ hL
    rintro ℓ ⟨hℓT, hℓ⟩
    have hℓM : ENNReal.ofReal ℓ ≤ m (Icc (-((n : ℝ) + 1)) 0) :=
      (ENNReal.ofReal_le_iff_le_toReal (hfin _)).2 hℓ.2
    have hlen : (m (Icc (lenLeft m ℓ) 0)).toReal = ℓ := by
      rw [measure_Icc_lenLeft_eq hδ hfin (fun t _ => hat t) hℓM, ENNReal.toReal_ofReal hℓ.1.le]
    refine ⟨hℓ.1, ?_⟩
    have h1 : R (lenLeft m ℓ) ∈ S' := hℓT
    rwa [hR, hlen] at h1
  -- the right half-line: the partner is `0`
  have hright : R ⁻¹' S' ∩ Ici 0 = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
    have h0' : m (Icc x 0) = 0 := by
      rcases (show (0 : ℝ) ≤ x from hx.2).lt_or_eq with hx' | hx'
      · rw [Icc_eq_empty (not_le.2 hx'), measure_empty]
      · rw [← hx', Icc_self]; exact hat 0
    have h1 : R x ∈ S' := hx.1
    rw [hR, h0', ENNReal.toReal_zero, lenRight_zero] at h1
    exact lt_irrefl (0 : ℝ) (hS'pos h1)
  have hcover : R ⁻¹' S' ⊆ (⋃ n : ℕ, R ⁻¹' S' ∩ Icc (-((n : ℝ) + 1)) 0) ∪ (R ⁻¹' S' ∩ Ici 0) := by
    intro x hx
    rcases le_or_gt 0 x with h | h
    · exact Or.inr ⟨hx, h⟩
    · obtain ⟨n, hn⟩ := exists_nat_gt (-x)
      exact Or.inl (mem_iUnion.2 ⟨n, hx, by linarith, h.le⟩)
  refine measure_mono_null hcover ?_
  rw [hright, union_empty]
  exact measure_iUnion_null hleft

open R18 in
/-- **`G3ZqTVPartnerStmt` holds.** -/
theorem g3ZqTVPartnerStmt_holds : G3ZqTVPartnerStmt := by
  intro γ hγ hγ2 Ω'' _ P'' _ V hV hV0
  filter_upwards [WedgeBdry.ae_bReg_logSing hγ hγ2 (alpha_lt_Qc hγ hγ2) P'' V hV]
    with ω hω S hS h0
  have hB : WedgeBdry.BReg γ (V ω + F2.logSingField (γ ^ 2)) := by
    rw [g3pl4_logSingField_eq hγ]; exact hω
  have := hB.1.qBoundaryMeasure_spec.1
  exact partner_ae_not_mem hB.noAtom hS h0

end ZqT
end Thm18Asm
end QuantumZipper
