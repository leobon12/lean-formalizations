import QuantumZipper.Proofs.Section5.Prop16MeasScale
import QuantumZipper.Proofs.Section5.Prop16MeasCoords

/-!
# Proposition 1.6, node D4-MEAS (part 5): `hY` and `hmeas` for Proposition 1.6's objects

For Proposition 1.6's pre-limit objects (`Statements/Prop16.lean`)
`x C p = zoomField γ C (ofFun 𝔥₀ + X p.1) p.2` on `zoomDomain D p.2`, and
`Y C p = canonicalOn γ (x C p) (zoomDomain D p.2)` on `canonicalDomainOn γ (x C p) (zoomDomain D p.2)`,
with any measure `μ` on `Ω × ℝ` (in Theorem 1.6, `μ = prop16Law …`):

* `aemeasurable_scaleParam_prop16`: the scale parameter is a.e.-measurable;
* `aemeasurable_coords_prop16Y'`: the raw coordinates of `Y C` are a.e.-measurable (`hY`);
* `aemeasurable_integral_prop16Y`: the area pairings of `Y C` are a.e.-measurable (`hmeas`);
* `prop16_areaConvergesInLawOn_of_inputs`: D4-a (coordinate form) for these objects.

The inputs are that the events "the local area measure of the zoomed field on `D − t`, resp. of
the canonical field on its domain, is a genuine vague limit" are null-measurable. The domains
are exhausted by the cut-offs `openBump D n` composed with the affine maps `z ↦ z + t`,
`z ↦ a z + t` (`isBumpFamily_comp`). Own elementary arguments (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Area

namespace Meas

open LQGMeas TV Factorization

variable {α : Type*} [MeasurableSpace α]

/-- Cut-offs of `D` pulled back by a measurable family of continuous maps. -/
theorem isBumpFamily_comp {D : Set ℂ} (hD : IsOpen D) (hDc : Dᶜ.Nonempty) {g : α → ℂ → ℂ}
    (hg : Measurable fun q : α × ℂ => g q.1 q.2) (hgc : ∀ p, Continuous (g p)) :
    IsBumpFamily (fun p => g p ⁻¹' D) (fun n p z => openBump D n (g p z)) where
  meas n := (continuous_openBump D n).measurable.comp hg
  cont n p := (continuous_openBump D n).comp (hgc p)
  nonneg n p z := openBump_nonneg D n _
  le_one n p z := openBump_le_one D n _
  tsupp n p := (tsupport_comp_subset_preimage (openBump D n) (hgc p)).trans
    (preimage_mono (tsupport_openBump_subset D n))
  mono p z := openBump_mono D (g p z)
  reach p z hz := (openBump_eventually_one hD hDc hz).exists

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The zoomed field of Proposition 1.6. -/
abbrev zf (γ C : ℝ) (h0 : ℂ → ℝ) (X : Ω → FieldSample) (p : Ω × ℝ) : FieldSample :=
  zoomField γ C (ofFun h0 + X p.1) p.2

/-- **Scale parameter of the zoomed field**, given null-measurability of its good event. -/
theorem aemeasurable_scaleParam_prop16 (γ C : ℝ) (h0 : ℂ → ℝ) {D : Set ℂ} (hD : IsOpen D)
    (hDH : D ⊆ H) {X : Ω → FieldSample}
    (hX : ∀ μ : Measure ℂ, Measurable fun ω => X ω μ) {μ : Measure (Ω × ℝ)}
    (hG : NullMeasurableSet {p : Ω × ℝ | ∃ m, IsVagueLimitOn (zoomDomain D p.2)
      (areaApprox γ (zf γ C h0 X p)) m} μ) :
    AEMeasurable (fun p => scaleParamOn γ (zf γ C h0 X p) (zoomDomain D p.2)) μ := by
  have hDc : Dᶜ.Nonempty := ⟨0, fun h => by simpa [H] using hDH h⟩
  have hxm : Measurable fun p : Ω × ℝ => recon (zf γ C h0 X p) :=
    measurable_reconstruct.comp (measurable_coords_zoomField γ C h0 hX)
  have hφ := isBumpFamily_comp (α := Ω × ℝ) hD hDc (g := fun p z => z + (p.2 : ℂ))
    (by fun_prop) (fun p => by fun_prop)
  have h := aemeasurable_scaleParamOn (γ := γ) (x := fun p => recon (zf γ C h0 X p)) hxm hφ
    (μ := μ) (by
      refine hG.congr (Eventually.of_forall fun p => ?_)
      change _ = (∃ m, IsVagueLimitOn _ (areaApprox γ (recon _)) m)
      rw [areaApprox_recon]; rfl)
  refine h.congr (Eventually.of_forall fun p => ?_)
  exact scaleParamOn_recon γ _ _

/-- **`hY` for Proposition 1.6** (coordinate form). -/
theorem aemeasurable_coords_prop16Y' (γ C : ℝ) (h0 : ℂ → ℝ) {D : Set ℂ} (hD : IsOpen D)
    (hDH : D ⊆ H) {X : Ω → FieldSample}
    (hX : ∀ μ : Measure ℂ, Measurable fun ω => X ω μ) {μ : Measure (Ω × ℝ)}
    (hG : NullMeasurableSet {p : Ω × ℝ | ∃ m, IsVagueLimitOn (zoomDomain D p.2)
      (areaApprox γ (zf γ C h0 X p)) m} μ) :
    AEMeasurable (fun p => coords (canonicalOn γ (zf γ C h0 X p) (zoomDomain D p.2))) μ :=
  aemeasurable_coords_prop16Y γ C h0 D hX (aemeasurable_scaleParam_prop16 γ C h0 hD hDH hX hG)

/-- The canonical field of Proposition 1.6. -/
abbrev cf (γ C : ℝ) (h0 : ℂ → ℝ) (D : Set ℂ) (X : Ω → FieldSample) (p : Ω × ℝ) : FieldSample :=
  canonicalOn γ (zf γ C h0 X p) (zoomDomain D p.2)

/-- The domain of the canonical field of Proposition 1.6. -/
abbrev cd (γ C : ℝ) (h0 : ℂ → ℝ) (D : Set ℂ) (X : Ω → FieldSample) (p : Ω × ℝ) : Set ℂ :=
  canonicalDomainOn γ (zf γ C h0 X p) (zoomDomain D p.2)

/-- **`hmeas` for Proposition 1.6**, given null-measurability of the two good events. -/
theorem aemeasurable_integral_prop16Y (γ C : ℝ) (h0 : ℂ → ℝ) {D : Set ℂ} (hD : IsOpen D)
    (hDH : D ⊆ H) {X : Ω → FieldSample}
    (hX : ∀ μ : Measure ℂ, Measurable fun ω => X ω μ) {μ : Measure (Ω × ℝ)}
    (hG0 : NullMeasurableSet {p : Ω × ℝ | ∃ m, IsVagueLimitOn (zoomDomain D p.2)
      (areaApprox γ (zf γ C h0 X p)) m} μ)
    (hG1 : NullMeasurableSet {p : Ω × ℝ | ∃ m, IsVagueLimitOn (cd γ C h0 D X p)
      (areaApprox γ (cf γ C h0 D X p)) m} μ)
    {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    AEMeasurable (fun p => ∫ z, f z ∂qAreaMeasureOn γ (cf γ C h0 D X p) (cd γ C h0 D X p)) μ := by
  have hDc : Dᶜ.Nonempty := ⟨0, fun h => by simpa [H] using hDH h⟩
  have ha := aemeasurable_scaleParam_prop16 γ C h0 hD hDH hX hG0
  have hy := aemeasurable_coords_prop16Y' γ C h0 hD hDH hX hG0
  obtain ⟨a', ham, ha_ae⟩ := ha
  obtain ⟨y', hym, hy_ae⟩ := hy
  have hφ := isBumpFamily_comp (α := Ω × ℝ) hD hDc
    (g := fun p z => (a' p : ℂ) * z + (p.2 : ℂ)) (by fun_prop) (fun p => by fun_prop)
  have hx : Measurable fun p => reconstruct (y' p) := measurable_reconstruct.comp hym
  -- a.e. identification of the objects
  have hae : ∀ᵐ p ∂μ, qAreaMeasureOn γ (cf γ C h0 D X p) (cd γ C h0 D X p) =
      qAreaMeasureOn γ (reconstruct (y' p)) ((fun z => (a' p : ℂ) * z + (p.2 : ℂ)) ⁻¹' D) ∧
      ((∃ m, IsVagueLimitOn (cd γ C h0 D X p) (areaApprox γ (cf γ C h0 D X p)) m) =
        (∃ m, IsVagueLimitOn ((fun z => (a' p : ℂ) * z + (p.2 : ℂ)) ⁻¹' D)
          (areaApprox γ (reconstruct (y' p))) m)) := by
    filter_upwards [ha_ae, hy_ae] with p h1 h2
    have hU : cd γ C h0 D X p = (fun z => (a' p : ℂ) * z + (p.2 : ℂ)) ⁻¹' D := by
      ext z
      simp only [cd, canonicalDomainOn, mem_preimage]
      rw [h1]
      exact Iff.rfl
    have hA : areaApprox γ (reconstruct (y' p)) = areaApprox γ (cf γ C h0 D X p) := by
      rw [← h2]; exact areaApprox_recon γ _
    refine ⟨?_, ?_⟩
    · rw [hU, ← h2]; exact (qAreaMeasureOn_recon γ _ _).symm
    · rw [hU, hA]
  have hG1' : NullMeasurableSet (goodSet γ (fun p => reconstruct (y' p))
      (fun p => (fun z => (a' p : ℂ) * z + (p.2 : ℂ)) ⁻¹' D)) μ :=
    hG1.congr (by filter_upwards [hae] with p hp; exact hp.2)
  refine (aemeasurable_integral_qAreaMeasureOn (μ := μ) hx hφ hG1' hf hfc).congr ?_
  filter_upwards [hae] with p hp
  rw [hp.1]

end Meas

end Prop16Area

end QuantumZipper
