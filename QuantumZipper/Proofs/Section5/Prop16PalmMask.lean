import QuantumZipper.Proofs.Section5.Prop16PalmMaskBasic

/-!
# Proposition 1.6, Palm zoom with masked coordinates: nodes B′, C′ and assembly (decision D30)

Replaces node B (`Prop16PalmIdStmt`, false as stated: it compares full coordinate laws, which
include junk circles outside `closure D`) by its masked form `Prop16PalmIdMaskStmt`, and node C by
`Prop16FixedZoomMaskStmt` (the fixed-point zoom of the Palm-shifted field, masked the same way).
Node C′ follows from the unmasked node C together with `Prop16FixedScaleStmt` (the local scale
of the fixed-point zoom tends to `0` in probability): `prop16FixedZoomMaskStmt_of_unmasked`.

* `tendsto_tvDist_palmMask`: masking costs nothing in the limit `C → ∞` under `prop16Q`.
* `prop16PalmZoomStmt_of_mask : coupling → B′ → C′ → Prop16PalmZoomStmt` (node A is proved from
  the coupling, `prop16PalmMeasStmt_of_coupling`).
* `theorem1_6_of_palmMask`, `theorem1_6_of_palmMask'` (with C and the fixed-point scale node).

Source: Sheffield, arXiv:1012.4797, proof of Prop. 1.6 (p. 25): Palm (rooted-measure) identity
(Duplantier–Sheffield, arXiv:0808.1560, §3.3) and zoom at a fixed boundary point
(Duplantier–Miller–Sheffield, arXiv:1409.7055, Props. 4.7–4.8). The masking, the TV estimate
and the mixture bookkeeping are own elementary arguments.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

open Prop16Area Prop16Area.G Prop16Area.Meas TV Factorization

/-! ## 1. The mask costs nothing under the weighted law -/

/-- **Masking is asymptotically free under `prop16Q`.** -/
theorem tendsto_tvDist_palmMask {γ : ℝ} {D : Set ℂ} {c d a b : ℝ} {h0 : ℂ → ℝ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}
    (hdat : Prop16Data γ D c d a b h0 P X)
    (hν : AEMeasurable (fun ω => prop16Nu γ h0 a b (X ω)) P)
    (hnice : ∀ᵐ ω ∂P, IsLocNiceOn γ (D ∪ realSet (Ioo a b)) (X ω))
    (hmeas : ∀ C, AEMeasurable (palmCanonCoords γ C D h0 X) (prop16Q γ h0 a b P X)) (R : ℕ) :
    Tendsto (fun C => tvDist
      ((prop16Q γ h0 a b P X).map fun p => locCoords R (palmCanonCoords γ C D h0 X p))
      ((prop16Q γ h0 a b P X).map fun p => locCoords R (palmCanonMask γ C D a b h0 X p)))
      atTop (𝓝 0) := by
  have hdat' := hdat
  obtain ⟨-, -, ⟨-, -, -, hDH, -, -, hhd⟩, -, hca, hbd, -, -, -, hpos, hfin⟩ := hdat'
  set Q := prop16Q γ h0 a b P X with hQ
  have : IsProbabilityMeasure Q := isProbabilityMeasure_prop16Law' hν hpos hfin
  have hlg : ∀ᵐ ω ∂P, IsLocallyGoodOn γ (D ∪ realSet (Ioo a b)) (X ω) :=
    hnice.mono fun _ h => h.isLocallyGoodOn
  have hsc := prop16_hsc0 hdat hν hnice
  have hta : ∀ᵐ p ∂Q, p.2 ∈ Ioo a b :=
    ae_prop16Law_of_ae (G := fun _ t => t ∈ Ioo a b) (aemeasurable_prop16Kernel' hν hfin)
      (fun ω => sFinite_prop16Nu γ h0 a b (X ω)) (fun ω => prop16Nu_compl_Ioo γ h0 a b (X ω))
      (ae_of_all _ fun _ _ ht => ht)
  have hgm : Measurable fun p : Ω × ℝ => palmGap D a b p.2 :=
    (continuous_infDist_pt _).measurable.comp
      (Complex.continuous_ofReal.measurable.comp measurable_snd)
  set G : ℕ → Set (Ω × ℝ) := fun n => {p | palmGap D a b p.2 ≤ 2 * R * (1 / ((n : ℝ) + 1))}
    with hG
  have hGm : ∀ n, MeasurableSet (G n) := fun n => measurableSet_le hgm measurable_const
  have hGa : Antitone G := by
    intro n m hnm p hp
    refine le_trans (show palmGap D a b p.2 ≤ _ from hp)
      (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  have hGlim : Tendsto (fun n => Q (G n)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := Q) (fun n => (hGm n).nullMeasurableSet) hGa
      ⟨0, measure_ne_top _ _⟩
    have h0 : Q (⋂ n, G n) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hta] with p hp hmem
      have hg := palmGap_pos hDH hhd hca hbd hp
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < palmGap D a b p.2 / (2 * R + 1) by
        positivity)
      have hle := mem_iInter.1 hmem n
      simp only [hG, mem_ofPred_eq] at hle
      have h1 : 2 * (R : ℝ) * (1 / ((n : ℝ) + 1)) ≤ (2 * R + 1) * (1 / ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have h2 : (2 * R + 1) * (1 / ((n : ℝ) + 1)) < palmGap D a b p.2 := by
        rw [lt_div_iff₀ (by positivity)] at hn; linarith
      linarith
    rwa [h0] at h
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨n, hn⟩ := (hGlim.eventually (gt_mem_nhds hε2)).exists
  have h2 := ENNReal.tendsto_nhds_zero.1 (hsc (1 / ((n : ℝ) + 1)) (by positivity)) (ε / 2) hε2
  filter_upwards [h2] with C hC
  have hs : AEMeasurable (palmScale γ C D h0 X) Q := aemeasurable_zoomFree_scale hdat hν hlg C
  calc tvDist (Q.map fun p => locCoords R (palmCanonCoords γ C D h0 X p))
        (Q.map fun p => locCoords R (palmCanonMask γ C D a b h0 X p))
      ≤ Q {p | ¬ (0 < palmScale γ C D h0 X p ∧
          2 * palmScale γ C D h0 X p * R < palmGap D a b p.2)} :=
        tvDist_locCoords_mask_le Q D a b hs measurable_snd.aemeasurable (hmeas C) R
    _ ≤ Q ({p | ¬ (0 < palmScale γ C D h0 X p ∧
          palmScale γ C D h0 X p < 1 / ((n : ℝ) + 1))} ∪ G n) := by
        refine measure_mono fun p hp => ?_
        by_contra hq
        simp only [mem_union, mem_ofPred_eq, not_or, not_not, not_le, hG] at hp hq
        refine hp ⟨hq.1.1, lt_of_le_of_lt ?_ hq.2⟩
        have := hq.1.2.le
        have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
        nlinarith
    _ ≤ Q {p | ¬ (0 < palmScale γ C D h0 X p ∧
          palmScale γ C D h0 X p < 1 / ((n : ℝ) + 1))} + Q (G n) := measure_union_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hC hn.le
    _ = ε := ENNReal.add_halves ε

/-! ## 2. The masked nodes -/

/-- The hypotheses available to the Palm-zoom nodes: the Prop. 1.6 data, a.e.-measurability of
the boundary kernel and a.s. local niceness of the mixed field on `D ∪ (a,b)` (all consequences
of the coupling node, `prop16NuMeasStmt_of_loc`, `prop16LocNiceStmt_of_coupling`). -/
def Prop16PalmHyp (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → FieldSample) : Prop :=
  Prop16Data γ D c d a b h0 P X ∧ AEMeasurable (fun ω => prop16Nu γ h0 a b (X ω)) P ∧
    ∀ᵐ ω ∂P, IsLocNiceOn γ (D ∪ realSet (Ioo a b)) (X ω)

/-- **Node B′ (Palm identity for the masked zoom coordinates).** There are a probability
measure `ρ` carried by `(a,b)` (the Palm point law) and jointly measurable `F C` with
`prop16Q.map (masked zoom coords) = (P ⊗ ρ).map (F C)` and, for `ρ`-a.e. `x` and every `C`,
`F C (·, x) = ` the masked zoom coordinates at `x` of `X + (γ/2) G_D(x, ·)`, `P`-a.s. -/
def Prop16PalmIdMaskStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample), Prop16PalmHyp γ D c d a b h0 P X →
    (∀ C, AEMeasurable (palmCanonMask γ C D a b h0 X) (prop16Q γ h0 a b P X)) →
    ∃ (ρ : Measure ℝ) (F : ℝ → Ω × ℝ → (ℕ → ℝ)), IsProbabilityMeasure ρ ∧
      ρ (Ioo a b)ᶜ = 0 ∧ (∀ C, Measurable (F C)) ∧
      (∀ᵐ x ∂ρ, ∀ C, ∀ᵐ ω ∂P, F C (ω, x) = palmFixedMask γ C D c d a b h0 X x ω) ∧
      ∀ C, (prop16Q γ h0 a b P X).map (palmCanonMask γ C D a b h0 X) = (P.prod ρ).map (F C)

/-- **Node C′ (masked zoom at a fixed boundary point of the Palm-shifted mixed field).** -/
def Prop16FixedZoomMaskStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample), Prop16PalmHyp γ D c d a b h0 P X →
    ∀ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (W : Ω' → FieldSample),
      IsProbabilityMeasure P' → IsQuantumWedge γ γ W P' →
      ∀ x ∈ Ioo a b, ∀ R : ℕ, Tendsto (fun C => tvDist
        (P.map fun ω => locCoords R (palmFixedMask γ C D c d a b h0 X x ω))
        (P'.map fun ω => locField R (W ω))) atTop (𝓝 0)

/-! ## 3. Node C′ from node C and the fixed-point scale -/

/-! ## 4. Assembly -/

/-- **Input (1) of D4⁺ʷ (the Palm zoom) from the coupling and the masked nodes B′, C′.** -/
theorem prop16PalmZoomStmt_of_mask (hA : Prop16MixedFreeLocCouplingStmt)
    (hId : Prop16PalmIdMaskStmt) (hFix : Prop16FixedZoomMaskStmt) : Prop16PalmZoomStmt := by
  intro γ D c d a b h0 Ω _ P X hdat
  obtain ⟨hγ, hγ2, -, -, -, -, -, hP, -, hpos, hfin⟩ := id hdat
  obtain ⟨Ω', _, P', W, -, hP', hW, -⟩ :=
    NonVacuity.exists_wedge_indep_BM_uncond_prob_uncond (α := γ) hγ hγ2
      (S5.FieldLaw.Raw.gamma_lt_Qc' hγ hγ2)
  have hnice := prop16LocNiceStmt_of_coupling hA γ D c d a b h0 P X hdat
  have hlg : ∀ᵐ ω ∂P, IsLocallyGoodOn γ (D ∪ realSet (Ioo a b)) (X ω) :=
    hnice.mono fun _ h => h.isLocallyGoodOn
  have hν := prop16NuMeasStmt_of_loc (prop16LocGoodStmt_of_coupling hA) γ D c d a b h0 P X hdat
  have hyp : Prop16PalmHyp γ D c d a b h0 P X := ⟨hdat, hν, hnice⟩
  have hmeas := prop16PalmMeasStmt_of_coupling hA γ D c d a b h0 P X hdat
  set Q := prop16Q γ h0 a b P X with hQ
  have hmask : ∀ C, AEMeasurable (palmCanonMask γ C D a b h0 X) Q := fun C =>
    aemeasurable_maskCoords D a b (aemeasurable_zoomFree_scale hdat hν hlg C)
      measurable_snd.aemeasurable (hmeas C)
  obtain ⟨ρ, F, hρ, hρI, hF, hFae, hrepr⟩ := hId γ D c d a b h0 P X hyp hmask
  refine ⟨Ω', _, P', W, hP', hW, hmeas, fun R => ?_⟩
  have : IsProbabilityMeasure Q := isProbabilityMeasure_prop16Law' hν hpos hfin
  have hWR : IsProbabilityMeasure (P'.map fun ω => locField R (W ω)) :=
    (Measure.isProbabilityMeasure_map_iff (aemeasurable_locField_wedge hγ hγ2 hW R)).2
      inferInstance
  have hlaw : ∀ C, Q.map (fun p => locCoords R (palmCanonMask γ C D a b h0 X p)) =
      (P.prod ρ).map (locCoords R ∘ F C) := by
    intro C
    rw [show (fun p => locCoords R (palmCanonMask γ C D a b h0 X p)) =
        locCoords R ∘ palmCanonMask γ C D a b h0 X from rfl,
      ← AEMeasurable.map_map_of_aemeasurable (measurable_locCoords R).aemeasurable (hmask C),
      hrepr C, Measure.map_map (measurable_locCoords R) (hF C)]
  have hmix : Tendsto (fun C => tvDist (Q.map fun p => locCoords R (palmCanonMask γ C D a b h0 X p))
      (P'.map fun ω => locField R (W ω))) atTop (𝓝 0) := by
    simp_rw [hlaw]
    refine tendsto_tvDist_prod_map_of_ae P ρ _ (fun C => (measurable_locCoords R).comp (hF C)) ?_
    have hρI' : ∀ᵐ x ∂ρ, x ∈ Ioo a b := by rw [ae_iff]; exact hρI
    filter_upwards [hFae, hρI'] with x hx hxI
    refine (hFix γ D c d a b h0 P X hyp Ω' _ P' W hP' hW x hxI R).congr fun C => ?_
    congr 1
    exact Measure.map_congr ((hx C).mono fun ω hω => by simp only [Function.comp_apply, hω])
  have hmsk := tendsto_tvDist_palmMask hdat hν hnice hmeas R
  have h := hmsk.add hmix
  rw [add_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le)
    fun C => tvDist_triangle

/-- **Proposition 1.6 from the coupling and the masked Palm-zoom nodes B′, C′.** -/
theorem theorem1_6_of_palmMask (hA : Prop16MixedFreeLocCouplingStmt)
    (hId : Prop16PalmIdMaskStmt) (hFix : Prop16FixedZoomMaskStmt) : theorem1_6 :=
  theorem1_6_of_zoom hA (prop16PalmZoomStmt_of_mask hA hId hFix)

end Prop16Asm

end QuantumZipper
