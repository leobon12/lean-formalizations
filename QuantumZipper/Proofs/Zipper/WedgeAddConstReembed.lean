import QuantumZipper.Proofs.Zipper.WedgeAddConstReDet
import QuantumZipper.Proofs.Zipper.WedgeAddConstMain

/-!
# WEDGE-ADDCONST (6): the re-embedding node `WedgeReembedStmt`

Sheffield, arXiv:1012.4797, §1.6, (1.8): the canonical description of a quantum surface does not
depend on the chosen embedding. For the reference wedge `W = canonical γ Z`,
`Z = wedgeField (lateralPart X) A Q`, and a constant `k`, almost surely (per data coordinate)

  `data (canonical γ (W + k)) = data (canonical γ (Z + k))`:

`W + k` and `rescale (Z + k) Q s` (`s = scaleParam γ Z`) have the same regularized averages
(`avgReg_addConst_rescale`), and `canonical γ (rescale y Q s)` has the data of `canonical γ y`
(`y = Z + k`): on circles deterministically (`rescale_rescale_fc`), on each test function under
the continuum limit `ae_contPair_plain` (`rescale_rescale_eq_of_lim`). The law identity follows by
`S5.FieldLaw.Raw.map_prod_eq_of_ae` (finite-dimensional marginals), as in the proof of B4(d)
(`WedgeCReg.wedgeRefReflectStmt_holds`).

Own elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace F1

open Factorization CoordsFull

theorem canonical_addConst_canonical_eq {γ : ℝ} {z : FieldSample} (hg : IsLQGGood γ z)
    (hs : 0 < scaleParam γ z) (k : ℝ) :
    canonical γ (addConst (canonical γ z) k) =
      canonical γ (rescale (addConst z k) (Qc γ) (scaleParam γ z)) := by
  obtain ⟨F, hF⟩ := hg.1
  exact canonical_congr (avgReg_addConst_rescale hF (Qc γ) k hs) γ

theorem coordsFull_canonical_rescale {γ : ℝ} (hγ : 0 < γ) {y : FieldSample}
    (hy : IsLQGGood γ y) {s : ℝ} (hs : 0 < s) (hsy : 0 < scaleParam γ y) :
    coordsFull (canonical γ (rescale y (Qc γ) s)) = coordsFull (canonical γ y) := by
  obtain ⟨G, hG⟩ := hy.1
  have e : canonical γ (rescale y (Qc γ) s) =
      rescale (rescale y (Qc γ) s) (Qc γ) (scaleParam γ y / s) := by
    rw [canonical, GoodTransforms.scaleParam_rescale hy hγ hs]
  rw [e, show canonical γ y = rescale y (Qc γ) (scaleParam γ y) from rfl]
  funext i
  have h := rescale_rescale_fc hG (Qc γ) hs (div_pos hsy hs) (fullIndex i).1
    (WedgeTK.fullIndex_pos i)
  rw [mul_div_cancel₀ _ hs.ne'] at h
  exact h

theorem tendsto_witness_add {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F) {c : ℝ}
    (hc : 0 < c) {ν : Measure ℂ} [IsFiniteMeasure ν] {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ Hbar) (hνK : ∀ᵐ u ∂ν, u ∈ K) (k : ℝ) {L : ℝ}
    (h : Tendsto (fun r => ∫ u, F ((c : ℂ) * u, r) ∂ν) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun r => ∫ u, (F ((c : ℂ) * u, r) + k) ∂ν) (𝓝[>] 0)
      (𝓝 (L + k * ν.real univ)) := by
  refine (h.add_const (k * ν.real univ)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [integral_add (integrable_witness_mul hF hc hr hK hKH hνK) (integrable_const k),
    integral_const, smul_eq_mul, mul_comm k]

theorem rescale_addConst_dens {γ k : ℝ} (hγ : 0 < γ) {z : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith z F) (hg : IsLQGGood γ (addConst z k)) {s : ℝ} (hs : 0 < s)
    (hsy : 0 < scaleParam γ (addConst z k)) {f : ℂ → ℝ} (hfc : Continuous f)
    (hfs : HasCompactSupport f) (hfH : tsupport f ⊆ H)
    (hc : ∃ L, Tendsto (fun r => ∫ u, F (((scaleParam γ (addConst z k) : ℝ) : ℂ) * u, r)
      ∂(volume.withDensity fun z => ENNReal.ofReal (f z))) (𝓝[>] 0) (𝓝 L)) :
    canonical γ (rescale (addConst z k) (Qc γ) s)
        (volume.withDensity fun z => ENNReal.ofReal (f z)) =
      canonical γ (addConst z k) (volume.withDensity fun z => ENNReal.ofReal (f z)) := by
  obtain ⟨hfin, hae⟩ := F1.B4d.withDensity_facts hfc hfs
  have hKH : tsupport f ⊆ Hbar := hfH.trans F1.B4d.H_subset_Hbar
  obtain ⟨L, hL⟩ := hc
  have e : canonical γ (rescale (addConst z k) (Qc γ) s) =
      rescale (rescale (addConst z k) (Qc γ) s) (Qc γ) (scaleParam γ (addConst z k) / s) := by
    rw [canonical, GoodTransforms.scaleParam_rescale hg hγ hs]
  have hsb : s * (scaleParam γ (addConst z k) / s) = scaleParam γ (addConst z k) :=
    mul_div_cancel₀ _ hs.ne'
  rw [e, show canonical γ (addConst z k) =
    rescale (addConst z k) (Qc γ) (scaleParam γ (addConst z k)) from rfl]
  have h := rescale_rescale_eq_of_lim (hF.addConst' k) (Qc γ) hs (div_pos hsy hs) _ hfs hKH hae
    (L := L + k * (volume.withDensity fun z => ENNReal.ofReal (f z)).real univ)
    (by rw [hsb]; exact tendsto_witness_add hF hsy hfs hKH hae k hL)
  rw [hsb] at h
  exact h

theorem pairRaw_canonical_rescale_addConst {γ k : ℝ} (hγ : 0 < γ) {z : FieldSample}
    {F : ℂ × ℝ → ℝ} (hF : IsRegularWith z F) (hg : IsLQGGood γ (addConst z k)) {s : ℝ}
    (hs : 0 < s) (hsy : 0 < scaleParam γ (addConst z k)) (ρ : TestFun H)
    (hc : ∀ f ∈ ({ρ.1, -ρ.1} : Set (ℂ → ℝ)), ∃ L, Tendsto (fun r => ∫ u,
      F (((scaleParam γ (addConst z k) : ℝ) : ℂ) * u, r)
        ∂(volume.withDensity fun z => ENNReal.ofReal (f z))) (𝓝[>] 0) (𝓝 L)) :
    pairRaw (canonical γ (rescale (addConst z k) (Qc γ) s)) ρ.1 =
      pairRaw (canonical γ (addConst z k)) ρ.1 := by
  obtain ⟨hρs, hρc, hρH⟩ := ρ.2
  unfold pairRaw
  rw [rescale_addConst_dens hγ hF hg hs hsy hρs.continuous hρc hρH (hc ρ.1 (mem_insert _ _)),
    rescale_addConst_dens hγ hF hg hs hsy (f := fun z => -ρ.1 z) hρs.continuous.neg hρc.neg
      (by rw [show (fun z => -ρ.1 z) = -ρ.1 from rfl, tsupport_neg]; exact hρH)
      (hc (-ρ.1) (mem_insert_of_mem _ rfl))]

/-- **The re-embedding node holds.** -/
theorem wedgeReembedStmt_holds {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ) :
    WedgeReembedStmt γ α := by
  intro Ω' _ P' _ X A hX hA hI k
  set Z : Ω' → FieldSample :=
    fun ω => wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ) with hZ
  have hZg : ∀ᵐ ω ∂P', IsLQGGood γ (Z ω) :=
    LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hα Ω' _ P' X A inferInstance hX hA hI
  have hZp := Wire2.ae_hasAreaProfile_wedgeField hγ hγ2 hα hX hA hI
  have hZc : AEMeasurable (fun ω => coords (Z ω)) P' :=
    WedgeMeas.aemeasurable_coords_wedgeField hX.measurable_coord hA
  have hWD := WedgeMeas.aemeasurable_wedgeRefData hX hA hZg H
  have hWc : AEMeasurable (fun ω => coords (WedgeMeas.wedgeRef γ X A ω)) P' :=
    (WedgeCan4.measurable_piC.comp_aemeasurable hWD.fst).congr
      (ae_of_all _ fun ω => WedgeCan4.piC_coordsFull (WedgeMeas.wedgeRef γ X A ω))
  have hWg : ∀ᵐ ω ∂P', IsLQGGood γ (WedgeMeas.wedgeRef γ X A ω) :=
    (Wire2.ae_wedge_canonical_spec hγ hγ2 hα hX hA hI).mono fun ω h => h.2.1
  have hadd : Measurable fun c : ℕ → ℝ => fun j => c j + k := by fun_prop
  have hc1 : AEMeasurable (fun ω => coords (addConst (WedgeMeas.wedgeRef γ X A ω) k)) P' :=
    (hadd.comp_aemeasurable hWc).congr (ae_of_all _ fun ω => (coords_addConst _ k).symm)
  have hc2 : AEMeasurable (fun ω => coords (wedgeShift γ X A k ω)) P' :=
    (hadd.comp_aemeasurable hZc).congr (ae_of_all _ fun ω => (coords_addConst _ k).symm)
  have hf := WedgeMeas.aemeasurable_dataFull_canonical hc1 (hWg.mono fun ω h => h.addConst k) H
  have hg := WedgeMeas.aemeasurable_dataFull_canonical hc2 (hZg.mono fun ω h => h.addConst k) H
  refine S5.FieldLaw.Raw.map_prod_eq_of_ae hf hg ?_ fun ρ => ?_
  · filter_upwards [hZg, hZp] with ω hg hp
    have hs := (CanonicalGood.scaleParam_spec hp).1
    have hsy := (CanonicalGood.scaleParam_spec (hasAreaProfile_addConst hg hp k)).1
    show coordsFull (canonical γ (addConst (canonical γ (Z ω)) k)) =
      coordsFull (canonical γ (addConst (Z ω) k))
    rw [canonical_addConst_canonical_eq hg hs k,
      coordsFull_canonical_rescale hγ (hg.addConst k) hs hsy]
  · filter_upwards [hZg, hZp, ae_contPair_plain hX (WedgeCan4.ae_continuous_wedgeProcess hA)
      (Qc γ) ρ] with ω hg hp hc
    have hs := (CanonicalGood.scaleParam_spec hp).1
    have hsy := (CanonicalGood.scaleParam_spec (hasAreaProfile_addConst hg hp k)).1
    obtain ⟨F, hF⟩ := hg.1
    show pairRaw (canonical γ (addConst (canonical γ (Z ω)) k)) ρ.1 =
      pairRaw (canonical γ (addConst (Z ω) k)) ρ.1
    rw [canonical_addConst_canonical_eq hg hs k]
    exact pairRaw_canonical_rescale_addConst hγ hF.congr_evalReg (hg.addConst k) hs hsy ρ
      (hc _ hsy)

/-- **Field-level B4(c) from the translation node alone.** -/
theorem wedgeAddConstLawStmt_of_shift
    (hS : ∀ γ α : ℝ, 0 < γ → γ < 2 → α < Qc γ → WedgeShiftLawStmt γ α) :
    WedgeAddConstLawStmt :=
  wedgeAddConstLawStmt_of_nodes (fun _ _ hγ hγ2 hα => wedgeReembedStmt_holds hγ hγ2 hα) hS

end F1
end QuantumZipper
