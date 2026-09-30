import QuantumZipper.Proofs.Complex.KernelChordR
import QuantumZipper.Proofs.Complex.KernelChordRight

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-PSIEXT: the Carathéodory boundary extension of the inverse uniformizer

For a simple chord `η`, a side component `D` (left or right) and a normalized uniformizer
`φ : D → ℍ`, the inverse `ψ = invFunOn φ D` extends from `ℍ` to a **measurable** map `ψe : ℂ → ℂ`,
continuous on `Hbar`, with `ψe(Hbar) ⊆ Hbar` (`exists_measurable_ext_left`,
`exists_measurable_ext_right`). This is the extension clause of `G1RC.PsiExt`.

Route (all analytic pieces are in the repository):

* `CA.Car.continuousOn_extension` (Carathéodory's continuity theorem, Pommerenke, *Boundary
  Behaviour of Conformal Maps* (1992), Thm 2.1/2.6) for `cayley ∘ ψ`, whose standing hypotheses
  are `CA.Uniformizer.carHyp_cayley_comp`: it gives `F` continuous on `Hbar` with
  `F = cayley ∘ ψ` on `ℍ`, and the limit `wInf` of `cayley ∘ ψ` at `∞`;
* `wInf = 1` (the tip `∞ ∈ ∂D` corresponds to `∞ ∈ ∂ℍ`): copied from the proof of
  `G1Chord.exists_boundary_values_normalized` (G1PkgLeftBV.lean), which uses the normalization
  `‖φ z‖ → ∞` at `∞ ∈ D`; then `F x ≠ 1` for real `x` by C6
  (`CA.Car.eq_of_isPreconnected_diff` with `isPreconnected_thetaCurve_diff_one`), so
  `G = cayleyInv ∘ F` is continuous on `Hbar` and equals `ψ` on `ℍ`;
* `G(Hbar) ⊆ closure (ψ '' ℍ) ⊆ closure ℍ = Hbar`;
* right component: reflection `refl z = −conj z` (`refl ∘ φ ∘ refl` is a normalized uniformizer of
  `leftComponent (refl ∘ η)`), as in `CA.Uniformizer.exists_normalizedUniformizer_rightComponent`;
* measurability: `ψe = Hbar.indicator G` (`measurable_indicator_of_continuous_on_closed`, own
  elementary proof).

Source: Pommerenke 1992, Thm 2.6 (through the `CA` nodes); the assembly is own bookkeeping.
-/

noncomputable section

open Set Metric Filter Function Bornology Complex
open scoped Topology ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

open QuantumZipper.CA QuantumZipper.CA.Uniformizer QuantumZipper.CA.Kernel

/-! ## Measurability of the indicator of a function continuous on a closed set -/

/-- **Measurability of `s.indicator G`** for `s` closed and `G` continuous on `s`. Own elementary
proof: for closed `t` the preimage `s ∩ G ⁻¹' t` is closed (continuity of `G` on the closed set
`s`) and the rest of the preimage is `sᶜ` or `∅`; the closed sets generate the Borel σ-algebra. -/
theorem measurable_indicator_of_continuous_on_closed {s : Set ℂ} (hs : IsClosed s) {G : ℂ → ℂ}
    (hG : ContinuousOn G s) : Measurable (s.indicator G) := by
  have hcont : Continuous (s.domRestrict G) := continuousOn_iff_continuous_domRestrict.1 hG
  have hpre : ∀ t : Set ℂ, IsClosed t → MeasurableSet ((s.indicator G) ⁻¹' t) := by
    intro t ht
    obtain ⟨u, hu, hue⟩ := isClosed_induced_iff.1 (ht.preimage hcont)
    have hsu : s ∩ G ⁻¹' t = s ∩ u := by
      ext z
      constructor
      · rintro ⟨hzs, hGz⟩
        refine ⟨hzs, ?_⟩
        have hz : (⟨z, hzs⟩ : s) ∈ (s.domRestrict G) ⁻¹' t := hGz
        rw [← hue] at hz
        exact hz
      · rintro ⟨hzs, hzu⟩
        refine ⟨hzs, ?_⟩
        have hz : (⟨z, hzs⟩ : s) ∈ (s.domRestrict G) ⁻¹' t := by rw [← hue]; exact hzu
        exact hz
    have hset : (s.indicator G) ⁻¹' t = (s ∩ u) ∪ (sᶜ ∩ {_z : ℂ | (0 : ℂ) ∈ t}) := by
      ext z
      rw [mem_preimage]
      by_cases hzs : z ∈ s
      · rw [Set.indicator_of_mem hzs, ← hsu]
        constructor
        · intro hz
          exact Or.inl ⟨hzs, hz⟩
        · rintro (⟨-, hz⟩ | ⟨hzn, -⟩)
          · exact hz
          · exact absurd hzs hzn
      · rw [Set.indicator_of_notMem hzs]
        constructor
        · intro hz
          exact Or.inr ⟨hzs, hz⟩
        · rintro (⟨hz, -⟩ | ⟨-, hz⟩)
          · exact absurd hz hzs
          · exact hz
    rw [hset]
    refine (hs.measurableSet.inter hu.measurableSet).union
      (hs.isOpen_compl.measurableSet.inter ?_)
    by_cases h0 : (0 : ℂ) ∈ t
    · simp [h0]
    · simp [h0]
  exact measurable_of_isClosed hpre

/-! ## The continuous extension -/

/-- `ψ` agrees on `ℍ` with a map continuous on `Hbar` sending `Hbar` into `Hbar`. -/
def HasHbarExt (ψ : ℂ → ℂ) : Prop :=
  ∃ G : ℂ → ℂ, ContinuousOn G Hbar ∧ MapsTo G Hbar Hbar ∧ EqOn ψ G H

/-- The measurable modification `Hbar.indicator G` of a continuous extension. -/
theorem exists_measurable_of_hasHbarExt {ψ : ℂ → ℂ} (h : HasHbarExt ψ) :
    ∃ ψe : ℂ → ℂ, Measurable ψe ∧ ContinuousOn ψe Hbar ∧ MapsTo ψe Hbar Hbar ∧ EqOn ψ ψe H := by
  obtain ⟨G, hc, hm, he⟩ := h
  refine ⟨Hbar.indicator G, measurable_indicator_of_continuous_on_closed isClosed_Hbar hc,
    hc.congr fun z hz => indicator_of_mem hz G, fun z hz => ?_, fun z hz => ?_⟩
  · rw [indicator_of_mem hz]; exact hm hz
  · rw [indicator_of_mem (H_subset_Hbar hz)]; exact he hz

/-- **Left component.** The inverse of a normalized uniformizer of `leftComponent η` has a
continuous extension to `Hbar` with values in `Hbar` (Carathéodory, Pommerenke 1992, Thm 2.6). -/
theorem hasHbarExt_left {η : ℝ → ℂ} (hη : IsSimpleChord η) {φ : ℂ → ℂ}
    (hφ : IsNormalizedUniformizer (leftComponent η) φ) :
    HasHbarExt (invFunOn φ (leftComponent η)) := by
  obtain ⟨hbij, hd, -, hinf⟩ := hφ
  set D := leftComponent η with hD
  have hDo : IsOpen D := isOpen_leftComponent hη
  set ψ := invFunOn φ D
  have hψb : BijOn ψ H D := BijOn.symm hbij.invOn_invFunOn.symm hbij
  have hψd : DifferentiableOn ℂ ψ H := fun v hv => by
    obtain ⟨z, hz, rfl⟩ := hbij.surjOn hv
    exact (Koebe.hasDerivAt_invFunOn_of_injOn hDo hd hbij.injOn hz).differentiableAt
      |>.differentiableWithinAt
  have hinv : LeftInvOn ψ φ D := hbij.invOn_invFunOn.1
  have h := carHyp_cayley_comp hη hψb hψd
  obtain ⟨F, hEq, hF, -, wInf, -, hInf⟩ := Car.continuousOn_extension h (ulc_thetaCurve hη)
  have hfr := Car.frontier_eq_insert_range h hEq hF hInf
  have hMaps : MapsTo (cayley ∘ ψ) H (ball 0 1) := fun z hz => h.bdd (h.bij.mapsTo hz)
  have hnotΩ : ∀ w : ℂ, ‖w‖ = 1 → w ∉ cayley '' D := fun w hw hwΩ => by
    have := h.bdd hwΩ
    rw [mem_ball_zero_iff, hw] at this
    exact lt_irrefl 1 this
  -- the point at infinity: `wInf = 1` (verbatim from G1PkgLeftBV.lean)
  have hwInf : wInf = 1 := by
    have : (cobounded ℂ ⊓ 𝓟 D).NeBot := neBot_cobounded_inf_leftComponent hη
    have hp1 : (1 : ℂ) ∈ frontier (cayley '' D) := by
      rw [h.isOpen.frontier_eq]
      refine ⟨?_, hnotΩ _ (by simp)⟩
      exact mem_closure_of_tendsto (tendsto_cayley_cobounded.mono_left inf_le_left)
        (eventually_inf_principal.2 (Eventually.of_forall fun z hz => mem_image_of_mem cayley hz))
    obtain ⟨ζ, -, hζ, hlim⟩ := tendsto_cayley_comp_inv hbij.mapsTo hinv hEq hF hInf hMaps
      (q := 1) (l := cobounded ℂ ⊓ 𝓟 D) (by simp)
      (Car.eq_of_isPreconnected_diff h hEq hF hInf (isPreconnected_thetaCurve_diff_one hη))
      (hfr ▸ hp1) (mem_inf_of_right (mem_principal_self _))
      (tendsto_cayley_cobounded.mono_left inf_le_left)
    have h1 : Tendsto (fun z => cayley (φ z)) (cobounded ℂ ⊓ 𝓟 D) (𝓝 1) :=
      tendsto_cayley_cobounded.comp (tendsto_norm_atTop_iff_cobounded.1 hinf)
    have hζ1 : ζ = 1 := tendsto_nhds_unique hlim h1
    rcases hζ with ⟨-, hw⟩ | ⟨hne, -⟩
    · exact hw
    · exact absurd hζ1 hne
  -- `F ≠ 1` on `Hbar`
  have hne : ∀ z ∈ Hbar, F z ≠ 1 := by
    intro z hz
    rcases (show (0 : ℝ) ≤ z.im from hz).lt_or_eq with hz' | hz'
    · rw [hEq (show z ∈ H from hz')]
      exact ne_one_of_mem_unitBall (hMaps (show z ∈ H from hz'))
    · have hzr : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← hz'])
      rw [hzr]
      exact (Car.eq_of_isPreconnected_diff h hEq hF hInf
        (isPreconnected_thetaCurve_diff_one hη)).2 hwInf z.re
  have hGc : ContinuousOn (cayleyInv ∘ F) Hbar :=
    continuousOn_cayleyInv.comp hF fun z hz => hne z hz
  have hGe : EqOn ψ (cayleyInv ∘ F) H := by
    intro z hz
    show ψ z = cayleyInv (F z)
    rw [hEq hz]
    exact (cayleyInv_cayley (add_I_ne_zero_of_mem_Hbar
      (H_subset_Hbar (leftComponent_subset_H η (hψb.mapsTo hz))))).symm
  refine ⟨cayleyInv ∘ F, hGc, fun z hz => ?_, hGe⟩
  have hcl : z ∈ closure H := by rw [Car.closure_H_eq_Hbar]; exact hz
  have h1 := ((hGc z hz).mono H_subset_Hbar).mem_closure_image hcl
  have h2 : (cayleyInv ∘ F) '' H ⊆ H := by
    rintro _ ⟨w, hw, rfl⟩
    rw [← hGe hw]
    exact leftComponent_subset_H η (hψb.mapsTo hw)
  have h3 := closure_mono h2 h1
  rwa [Car.closure_H_eq_Hbar] at h3

theorem refl_mem_Hbar {z : ℂ} (hz : z ∈ Hbar) : refl z ∈ Hbar := by
  show (0 : ℝ) ≤ (refl z).im
  simpa [Uniformizer.refl] using (show (0 : ℝ) ≤ z.im from hz)

/-- The reflected uniformizer `refl ∘ φ ∘ refl` of a normalized uniformizer of the right
component is a normalized uniformizer of `leftComponent (refl ∘ η)` (the converse direction of
`exists_normalizedUniformizer_rightComponent`, same argument). -/
theorem isNormalizedUniformizer_refl_of_right {η : ℝ → ℂ} (hη : IsSimpleChord η) {φ : ℂ → ℂ}
    (hφ : IsNormalizedUniformizer (rightComponent η) φ) :
    IsNormalizedUniformizer (leftComponent (refl ∘ η)) (refl ∘ φ ∘ refl) := by
  obtain ⟨hbij, hd, h0, hinf⟩ := hφ
  have hRo := isOpen_rightComponent_qz hη
  refine ⟨bijOn_refl_H.comp (hbij.comp (bijOn_refl_left η)), fun z hz => ?_, ?_, ?_⟩
  · have hz' := (bijOn_refl_left η).mapsTo hz
    exact (differentiableAt_refl_comp_refl
      (hd.differentiableAt (hRo.mem_nhds hz'))).differentiableWithinAt
  · have h1 : Tendsto refl (𝓝[leftComponent (refl ∘ η)] 0) (𝓝[rightComponent η] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_mem_nhdsWithin.mono fun z hz =>
        (bijOn_refl_left η).mapsTo hz⟩
      have := (continuous_refl.tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := leftComponent (refl ∘ η)))
      simpa [Uniformizer.refl] using this
    have h2 := (continuous_refl.tendsto 0).comp (h0.comp h1)
    simpa [Uniformizer.refl, Function.comp_def] using h2
  · have h1 : Tendsto refl (cobounded ℂ ⊓ 𝓟 (leftComponent (refl ∘ η)))
        (cobounded ℂ ⊓ 𝓟 (rightComponent η)) := by
      refine tendsto_inf.2 ⟨?_, tendsto_principal.2 (eventually_inf_principal.2
        (Eventually.of_forall fun z hz => (bijOn_refl_left η).mapsTo hz))⟩
      rw [← tendsto_norm_atTop_iff_cobounded]
      simpa [Uniformizer.refl] using tendsto_norm_cobounded_atTop.mono_left
        (inf_le_left : cobounded ℂ ⊓ 𝓟 (leftComponent (refl ∘ η)) ≤ cobounded ℂ)
    simpa [Uniformizer.refl, Function.comp_def] using hinf.comp h1

/-- **Right component**, by reflection from the left one. -/
theorem hasHbarExt_right {η : ℝ → ℂ} (hη : IsSimpleChord η) {φ : ℂ → ℂ}
    (hφ : IsNormalizedUniformizer (rightComponent η) φ) :
    HasHbarExt (invFunOn φ (rightComponent η)) := by
  have hφ' := isNormalizedUniformizer_refl_of_right hη hφ
  obtain ⟨G, hGc, hGm, hGe⟩ := hasHbarExt_left (isSimpleChord_refl_comp hη) hφ'
  refine ⟨refl ∘ G ∘ refl, ?_, fun z hz => refl_mem_Hbar (hGm (refl_mem_Hbar hz)), ?_⟩
  · exact continuous_refl.comp_continuousOn
      (hGc.comp continuous_refl.continuousOn fun z hz => refl_mem_Hbar hz)
  · intro w hw
    have hw' : refl w ∈ H := refl_mem_H_iff.2 hw
    set u := invFunOn (refl ∘ φ ∘ refl) (leftComponent (refl ∘ η)) (refl w) with hu
    have huL : u ∈ leftComponent (refl ∘ η) := (BijOn.symm hφ'.1.invOn_invFunOn.symm hφ'.1).mapsTo hw'
    have hφu : (refl ∘ φ ∘ refl) u = refl w := hφ'.1.invOn_invFunOn.2 hw'
    have hRu : refl u ∈ rightComponent η := (bijOn_refl_left η).mapsTo huL
    have hφRu : φ (refl u) = w := by
      have := congrArg refl hφu
      simpa using this
    have hx : invFunOn φ (rightComponent η) w ∈ rightComponent η :=
      (BijOn.symm hφ.1.invOn_invFunOn.symm hφ.1).mapsTo hw
    have hφx : φ (invFunOn φ (rightComponent η) w) = w := hφ.1.invOn_invFunOn.2 hw
    have heq : invFunOn φ (rightComponent η) w = refl u :=
      hφ.1.injOn hx hRu (hφx.trans hφRu.symm)
    show invFunOn φ (rightComponent η) w = refl (G (refl w))
    rw [heq, ← hGe hw']

/-- **The extension clause of `PsiExt`, both sides.** -/
theorem exists_measurable_ext_left {η : ℝ → ℂ} (hη : IsSimpleChord η) {φ : ℂ → ℂ}
    (hφ : IsNormalizedUniformizer (leftComponent η) φ) :
    ∃ ψe : ℂ → ℂ, Measurable ψe ∧ ContinuousOn ψe Hbar ∧ MapsTo ψe Hbar Hbar ∧
      EqOn (invFunOn φ (leftComponent η)) ψe H :=
  exists_measurable_of_hasHbarExt (hasHbarExt_left hη hφ)

theorem exists_measurable_ext_right {η : ℝ → ℂ} (hη : IsSimpleChord η) {φ : ℂ → ℂ}
    (hφ : IsNormalizedUniformizer (rightComponent η) φ) :
    ∃ ψe : ℂ → ℂ, Measurable ψe ∧ ContinuousOn ψe Hbar ∧ MapsTo ψe Hbar Hbar ∧
      EqOn (invFunOn φ (rightComponent η)) ψe H :=
  exists_measurable_of_hasHbarExt (hasHbarExt_right hη hφ)

end G1RC
end Thm18Asm
end QuantumZipper
