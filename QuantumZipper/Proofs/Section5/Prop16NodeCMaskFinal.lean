import QuantumZipper.Proofs.Section5.Prop16NodeCMaskLaw

/-!
# Proposition 1.6, node C′ (masked): masked law determinacy and assembly

* `Prop16PalmShiftGoodStmt` (**remaining node**): for a mixed GFF `X` on `D`, free on `[c,d]`,
  a.s. locally nice on `D ∪ (a,b)`, and `x ∈ (a,b)`: for every `C`, almost surely the zoomed
  Palm-shifted field `(X + (γ/2) G_D(x,·))(· + x) + C/γ + 𝔥₀(x)` has a local area measure on
  `D − x` (a genuine vague limit). Mathematically: on `D` the Palm shift `G_D(x, ·)` is continuous
  (`x` is a boundary point), so this follows from local niceness of `X` on `D` as in
  `exists_limit_of_agree` (`Prop16LocalAssembly.lean`), once `mixedGreenSample D S x` is known to
  agree on the dyadic circles inside `D` with a function continuous on `D` (cf. the kernel form
  `mixedGreenSample_eq`, `Prop16NodeBKernel.lean`, near the free arc).
* `prop16FixedLawMask_of_good : Prop16PalmShiftGoodStmt → Prop16FixedLawMaskStmt`: the masked
  coordinates are a.s. `palmMaskRead ∘ admCoords` (locality, `palmCanonMask_congr`,
  `circAgree_reconstruct_admCoords`; exactness on the good event, `palmMaskRead_eq`), a
  measurable function of the admissible coordinates, whose law does not depend on the mixed GFF
  (`map_admCoords_eq`).
* `prop16FixedZoomMask_of_goodN2`, `theorem1_6_of_palmMaskGood`: node C′ and Proposition 1.6
  from D3⁺(i) (N2 form), `Prop16PalmShiftGoodStmt` and the Markov node
  `Prop16NodeCMarkovMaskStmt`.

Sources: Sheffield, arXiv:1012.4797, proof of Prop. 1.6 (p. 25); law determinacy of a Gaussian
process by its covariance on countably many coordinates (finite-dimensional Gaussian laws plus
the monotone class lemma, Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*
(2016), Appendix A1). Bookkeeping: own elementary arguments.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

open TV Factorization Prop16Area Prop16Area.Meas

/-- **Local area measure of the zoomed Palm-shifted mixed field** (remaining node). -/
def Prop16PalmShiftGoodStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ), 0 < γ → γ < 2 → K3.Prop16Geometry D c d →
    a < b → c ≤ a → b ≤ d →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → FieldSample),
      IsProbabilityMeasure P → IsMixedGFF D (realSet (Icc c d)) X P →
      (∀ᵐ ω ∂P, IsLocNiceOn γ (D ∪ realSet (Ioo a b)) (X ω)) →
      ∀ x ∈ Ioo a b, ∀ C : ℝ, ∀ᵐ ω ∂P, ∃ m, IsVagueLimitOn (zoomDomain D x)
        (areaApprox γ (zoomFree γ C h0 (palmMixedField γ D (realSet (Icc c d)) X x) (ω, x))) m

/-- The masked coordinates are a.s. the measurable reading of the admissible coordinates. -/
theorem ae_palmFixedMask_eq_read (hG : Prop16PalmShiftGoodStmt) {γ : ℝ} {D : Set ℂ}
    {c d a b : ℝ} {h0 : ℂ → ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hgeo : K3.Prop16Geometry D c d)
    (hab : a < b) (hca : c ≤ a) (hbd : b ≤ d) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → FieldSample) (hP : IsProbabilityMeasure P)
    (hX : IsMixedGFF D (realSet (Icc c d)) X P)
    (hn : ∀ᵐ ω ∂P, IsLocNiceOn γ (D ∪ realSet (Ioo a b)) (X ω)) {x : ℝ} (hx : x ∈ Ioo a b)
    (C : ℝ) :
    ∀ᵐ ω ∂P, palmFixedMask γ C D c d a b h0 X x ω =
      palmMaskRead γ C D c d a b h0 x (admCoords D (realSet (Icc c d)) (X ω)) := by
  obtain ⟨hDo, -, -, hDH, -⟩ := id hgeo
  obtain ⟨W, hWo, hWV⟩ := locGood_exists_open hgeo hca hbd
  have hVW : D ∪ realSet (Ioo a b) ⊆ W := fun z hz => by
    have : z ∈ W ∩ Hbar := by rw [hWV]; exact hz
    exact this.1
  have hWxo : IsOpen ((fun z => z + (x : ℂ)) ⁻¹' W) :=
    hWo.preimage (continuous_id.add continuous_const)
  filter_upwards [hG γ D c d a b h0 hγ hγ2 hgeo hab hca hbd P X hP hX hn x hx C] with ω hω
  obtain ⟨m, hm⟩ := hω
  set v := admCoords D (realSet (Icc c d)) (X ω) with hv
  have hag : G.CircAgree W (palmMixedField γ D (realSet (Icc c d)) X x ω)
      (palmFam γ D c d x v) := fun n k z hz hW => by
    have := circAgree_reconstruct_admCoords hgeo hca hbd hWo hWV (X ω) n k z hz hW
    simp only [palmMixedField, palmFam, Pi.add_apply, this]
    rfl
  have e1 : palmFixedMask γ C D c d a b h0 X x ω =
      palmCanonMask γ C D a b h0 (palmFam γ D c d x) (v, x) :=
    palmCanonMask_congr hWo hDo hDH hVW _ _ ω v x hag
  have hgood : v ∈ goodSet γ (palmZr γ C D c d h0 x) fun _ => zoomDomain D x := by
    show ∃ m, IsVagueLimitOn (zoomDomain D x) (areaApprox γ (palmZr γ C D c d h0 x v)) m
    rw [palmZr, areaApprox_recon]
    have h' : G.CircAgree ((fun z => z + (x : ℂ)) ⁻¹' W)
        (zoomFree γ C h0 (palmFam γ D c d x) (v, x))
        (zoomFree γ C h0 (palmMixedField γ D (realSet (Icc c d)) X x) (ω, x)) :=
      circAgree_zoomFree_nc hWo (circAgree_symm_nc hag) γ C (h0 x) x
    exact ⟨m, G.isVagueLimitOn_of_circAgree hWxo h' (zoomDomain_subset_H hDH x)
      (fun z hz => hVW (Or.inl hz)) hm⟩
  rw [e1, palmMaskRead_eq hDo hDH hgood]

/-- **Masked law determinacy from the local-area node.** -/
theorem prop16FixedLawMask_of_good (hG : Prop16PalmShiftGoodStmt) : Prop16FixedLawMaskStmt := by
  intro γ D c d a b h0 hγ hγ2 hgeo hab hca hbd Ω _ P X Ω₀ _ P₀ Y hP hP₀ hX hY hnX hnY x hx C
  obtain ⟨hDo, -, -, hDH, -⟩ := id hgeo
  have hkX := ae_palmFixedMask_eq_read (h0 := h0) hG hγ hγ2 hgeo hab hca hbd P X hP hX hnX hx C
  have hkY := ae_palmFixedMask_eq_read (h0 := h0) hG hγ hγ2 hgeo hab hca hbd P₀ Y hP₀ hY hnY hx C
  have hmX := measurable_admCoords (D := D) (S := realSet (Icc c d)) hX.measurable_coord
  have hmY := measurable_admCoords (D := D) (S := realSet (Icc c d)) hY.measurable_coord
  have hR := measurable_palmMaskRead (γ := γ) (C := C) (c := c) (d := d) (a := a) (b := b)
    (h0 := h0) (x := x) hDo hDH
  refine ⟨(hR.comp hmY).aemeasurable.congr (hkY.mono fun ω h => h.symm), fun R => ?_⟩
  rw [Measure.map_congr (hkX.mono fun ω h => congrArg (locCoords R) h),
    Measure.map_congr (hkY.mono fun ω h => congrArg (locCoords R) h)]
  have hlaw := map_admCoords_eq (P := P) (P' := P₀) hX hY
  have hF := (measurable_locCoords R).comp hR
  calc P.map (fun ω => locCoords R (palmMaskRead γ C D c d a b h0 x
          (admCoords D (realSet (Icc c d)) (X ω))))
        = (P.map fun ω => admCoords D (realSet (Icc c d)) (X ω)).map
            (locCoords R ∘ palmMaskRead γ C D c d a b h0 x) :=
        (Measure.map_map hF hmX).symm
    _ = (P₀.map fun ω => admCoords D (realSet (Icc c d)) (Y ω)).map
            (locCoords R ∘ palmMaskRead γ C D c d a b h0 x) := by rw [hlaw]
    _ = _ := Measure.map_map hF hmY

/-- **Node C′** from D3⁺(i) (N2 form), the local-area node and the Markov coupling. -/
theorem prop16FixedZoomMask_of_goodN2 (hN2 : D3Plus.D3PlusIN2RichStmt)
    (hG : Prop16PalmShiftGoodStmt) (hK : Prop16NodeCMarkovMaskStmt) : Prop16FixedZoomMaskStmt :=
  prop16FixedZoomMask_of_splitN2 hN2 (prop16FixedLawMask_of_good hG) hK

end Prop16Asm

end QuantumZipper
