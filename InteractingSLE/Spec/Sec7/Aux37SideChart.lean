/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37FrameAssembly
import InteractingSLE.Spec.Sec6.Aux31Outer
import InteractingSLE.Spec.Supplement.R6RefPhase

/-!
# Aux. lemma 37's side germ: a Loewner map read through the flow chart of the pocket

Packet PROVE-STRIPSYS42. Specification §6.2, Aux. lemma 37's proof (`source/spec/p193-240.md` L104–L136,
pp. 198–200: "Each transition from either own coordinate to `Φ` takes the same incident collar to the upper
half-plane. It extends across a smaller open real interval by Schwarz reflection").

For a flow chart `c` of the change pocket (`Aux119Bdry.IsFlowChart`), its landing map `land c` (the boundary extension
of `c⁻¹`) and the reading `Ψ ∘ cayley` (`read_land`: it inverts `land c` on `ℍ̄`):

* `tendsto_land`, `continuousOn_land`, `land_of_mem_H`, `read_land`, `continuousWithinAt_read`, `injOn_land`: the
  landing API of the flow chart;
* **`exists_ext`**: for a convex region `S ⊆ ℍ` with compact closure, a landing map `ℓ` (continuous on `ℍ̄`, with a
  reading `κ` inverting it) and a coordinate change `M` (the identity or `m(z) = −1/z`), if `M ∘ ℓ` maps the points of
  `S̄ ∩ ℍ` into `D_T = ℍ ∖ K_T` of a continuous Loewner trace, then `g_T` extends continuously and injectively to
  `M(ℓ(S̄))`, with `f̄_T ∘ G = id`, real values at the points off `D_T` (Aux. lemma 30, `Sec6.exists_bdryExt_fwdMap`,
  through the local connectivity of convex regions);
* **`isRealBoundaryConformal_ext`**: the transition `G ∘ M ∘ ℓ` from the chart to the Loewner coordinate is conformal
  on every upper half-disc in `S` with real boundary values on its diameter (`R16.IsRealBoundaryConformal`), when the
  diameter lands off `D_T`.

No Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, `*_of_param` (R43, R48).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Function Complex
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open QuantumZipper.CA (cayley cayleyInv)
open InteractingSLE.WangWu (negInv)
open InteractingSLE.YuanSimpleApprox (trMap)
open scoped NNReal Real

namespace InteractingSLE.Sec7.Aux37Side

open WangWu Lemma71I PocketCoord PocketJordan Aux119Bdry Lemma71O

/-! ### The landing map of the flow chart -/

section Land

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {Ψ : ℂ → ℂ} {c : Chart}

theorem tendsto_land (hF : IsFlowChart R L r Ψ c) {q : ℂ} (hq : q ∈ Hbar) :
    Tendsto c.2.1 (𝓝[H] q) (𝓝 (land c q)) := by
  obtain ⟨z, -, -, hz⟩ := hF.exists_tendsto hq
  rwa [land, extendFrom_eq (by rw [closure_H]; exact hq) hz]

theorem continuousOn_land (hF : IsFlowChart R L r Ψ c) : ContinuousOn (land c) Hbar :=
  continuousOn_extendFrom (by rw [closure_H]) fun q hq => ⟨_, tendsto_land hF hq⟩

theorem land_of_mem_H (hF : IsFlowChart R L r Ψ c) {w : ℂ} (hw : w ∈ H) : land c w = c.2.1 w := by
  have hca : ContinuousAt c.2.1 w :=
    (hF.conf.1.continuousOn.continuousAt (QuantumZipper.isOpen_H.mem_nhds hw))
  exact extendFrom_eq (subset_closure hw) (hca.tendsto.mono_left nhdsWithin_le_nhds)

/-- The landing point is a boundary-uniformizer point: `cayley (land c q)` lies in the closed Cayley image off the
closing contact, and `Ψ` reads `q` there. -/
theorem land_props (hF : IsFlowChart R L r Ψ c) {q : ℂ} (hq : q ∈ Hbar) :
    cayley (land c q) ∈ closure (cayley '' changePocket R L r) \ {closePt R L r} ∧
      Ψ (cayley (land c q)) = q ∧ land c q + I ≠ 0 := by
  obtain ⟨z, hz, hΨz, -⟩ := hF.exists_tendsto hq
  have hl := hF.land_eq hq hz hΨz
  have hz1 := hF.ne_one hz
  have hc : cayley (land c q) = z := by rw [hl, QuantumZipper.CA.cayley_cayleyInv hz1]
  refine ⟨hc ▸ hz, hc ▸ hΨz, fun h0 => ?_⟩
  have hI : land c q = -I := eq_neg_of_add_eq_zero_left h0
  rw [hl] at hI
  have h1 : (1 : ℂ) - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz1)
  have h2 : I * (1 + z) = -I * (1 - z) := by
    have := hI
    unfold cayleyInv at this
    rw [div_eq_iff h1] at this
    exact this
  have h3 : I * 2 = 0 := by linear_combination h2
  simp [Complex.ext_iff] at h3

theorem read_land (hF : IsFlowChart R L r Ψ c) {q : ℂ} (hq : q ∈ Hbar) : Ψ (cayley (land c q)) = q :=
  (land_props hF hq).2.1

theorem injOn_land (hF : IsFlowChart R L r Ψ c) : InjOn (land c) Hbar := fun q hq q' hq' h => by
  rw [← read_land hF hq, ← read_land hF hq', h]

/-- The reading `Ψ ∘ cayley` is continuous at every landing point, within the landing image of `ℍ̄`. -/
theorem continuousWithinAt_read (hF : IsFlowChart R L r Ψ c) {q : ℂ} (hq : q ∈ Hbar) :
    ContinuousWithinAt (fun z => Ψ (cayley z)) (land c '' Hbar) (land c q) := by
  obtain ⟨hmem, -, hI⟩ := land_props hF hq
  have hcay : ContinuousAt cayley (land c q) :=
    QuantumZipper.CA.continuousOn_cayley.continuousAt
      (isOpen_ne.mem_nhds (show land c q ≠ -I from fun h => hI (by rw [h]; ring)))
  have hΨ : ContinuousWithinAt Ψ (closure (cayley '' changePocket R L r) \ {closePt R L r}) (cayley (land c q)) :=
    hF.unif.cont _ hmem
  refine hΨ.comp hcay.continuousWithinAt ?_
  rintro _ ⟨q', hq', rfl⟩
  exact (land_props hF hq').1

end Land

/-! ### The boundary extension of a Loewner map on a chart region -/

section Ext

variable {V : ℝ → ℝ} {γ : ℝ → ℂ} {T : ℝ} {ℓ κ M M' : ℂ → ℂ} {S : Set ℂ}

/-- The closure of the image of a region with compact closure under a map continuous on the closure. -/
theorem closure_image_eq {f : ℂ → ℂ} (hK : IsCompact (closure S)) (hf : ContinuousOn f (closure S)) :
    closure (f '' S) = f '' closure S :=
  Subset.antisymm ((hK.image_of_continuousOn hf).isClosed.closure_subset_iff.2 (image_mono subset_closure))
    hf.image_closure

/-- **The boundary extension of `g_T` on a chart region** (Aux. lemma 30 through a chart; see the module docstring). -/
theorem exists_ext (hη : IsLoewnerTrace V γ) (hV : Continuous V) (hV0 : V 0 = 0) (hT : 0 ≤ T)
    (hSc : Convex ℝ S) (hSH : S ⊆ H) (hK : IsCompact (closure S)) (hKH : closure S ⊆ Hbar)
    (hℓc : ContinuousOn ℓ Hbar) (hκ : ∀ q ∈ Hbar, κ (ℓ q) = q)
    (hκc : ∀ q ∈ Hbar, ContinuousWithinAt κ (ℓ '' Hbar) (ℓ q))
    (hMc : ContinuousOn M (ℓ '' closure S)) (hM' : ∀ z ∈ ℓ '' closure S, M' (M z) = z)
    (hM'c : ∀ z ∈ ℓ '' closure S, ContinuousAt M' (M z))
    (hD : ∀ q ∈ closure S, q ∈ H → M (ℓ q) ∈ H \ fwdHull V T) :
    ∃ G : ℂ → ℂ, ContinuousOn G (M '' (ℓ '' closure S)) ∧ InjOn G (M '' (ℓ '' closure S)) ∧
      MapsTo G (M '' (ℓ '' closure S)) Hbar ∧ (∀ z ∈ M '' (ℓ '' closure S), trMap V 0 T (G z) = z) ∧
      (∀ z ∈ M '' (ℓ '' closure S), z ∈ H \ fwdHull V T → G z = fwdMap V T z) ∧
      ∀ z ∈ M '' (ℓ '' closure S), z ∉ H \ fwdHull V T → (G z).im = 0 := by
  set F : ℂ → ℂ := fun q => M (ℓ q) with hFdef
  have hFc : ContinuousOn F (closure S) := hMc.comp (hℓc.mono hKH) (mapsTo_image _ _)
  have himg : M '' (ℓ '' closure S) = F '' closure S := by rw [image_image]
  have hcl : closure (F '' S) = F '' closure S := closure_image_eq hK hFc
  have hAD : F '' S ⊆ H \ fwdHull V T := by
    rintro _ ⟨q, hq, rfl⟩
    exact hD q (subset_closure hq) (hSH hq)
  -- the reading of `F`
  have hΦ : ∀ q ∈ closure S, κ (M' (F q)) = q := fun q hq => by
    simp only [hFdef]
    rw [hM' _ ⟨q, hq, rfl⟩, hκ q (hKH hq)]
  have hloc : ∀ p ∈ closure (F '' S), p ∉ H \ fwdHull V T → Sec6.IsLocConnWithin (F '' S) p := by
    intro p hp hpD ε hε
    rw [hcl] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    obtain ⟨ρ, hρ, hρF⟩ := Metric.continuousWithinAt_iff.1 (hFc q hq) ε hε
    refine ⟨F '' (S ∩ ball q ρ), ?_, ?_, ?_⟩
    · rintro _ ⟨q', hq', rfl⟩
      exact ⟨⟨q', hq'.1, rfl⟩, hρF (subset_closure hq'.1) hq'.2⟩
    · exact ((hSc.inter (convex_ball q ρ)).isPreconnected).image _
        (hFc.mono (inter_subset_left.trans subset_closure))
    · -- the reading `κ ∘ M'` is continuous at `F q` within the region
      have hMt : MapsTo M' (F '' S) (ℓ '' Hbar) := by
        rintro _ ⟨q', hq', rfl⟩
        rw [hM' _ ⟨q', subset_closure hq', rfl⟩]
        exact ⟨q', hKH (subset_closure hq'), rfl⟩
      have hcw : ContinuousWithinAt (fun z => κ (M' z)) (F '' S) (F q) := by
        have h1 : ContinuousWithinAt κ (ℓ '' Hbar) (M' (F q)) := by
          rw [hM' _ ⟨q, hq, rfl⟩]; exact hκc q (hKH hq)
        exact h1.comp (hM'c _ ⟨q, hq, rfl⟩).continuousWithinAt hMt
      have hmem : (fun z => κ (M' z)) ⁻¹' ball q ρ ∈ 𝓝[F '' S] (F q) := by
        have e : (fun z => κ (M' z)) (F q) = q := hΦ q hq
        exact hcw (by rw [e]; exact ball_mem_nhds q hρ)
      refine mem_of_superset (inter_mem hmem self_mem_nhdsWithin) ?_
      rintro _ ⟨hz1, ⟨q', hq', rfl⟩⟩
      refine ⟨q', ⟨hq', ?_⟩, rfl⟩
      have := hz1
      simp only [mem_preimage] at this
      rwa [hΦ q' (subset_closure hq')] at this
  obtain ⟨G, h1, h2, h3, h4, h5, h6⟩ := Sec6.exists_bdryExt_fwdMap hη hV hV0 hT hAD hloc
  rw [hcl, ← himg] at h1 h2 h3 h4 h5 h6
  exact ⟨G, h1, h2, h3, h4, h5, h6⟩

/-- **The transition from the chart to the Loewner coordinate is conformal with real boundary values** on every upper
half-disc of the region whose diameter lands off `D_T`. -/
theorem isRealBoundaryConformal_ext (hV : Continuous V) (hT : 0 ≤ T) (hKH : closure S ⊆ Hbar)
    (hℓc : ContinuousOn ℓ Hbar) (hκ : ∀ q ∈ Hbar, κ (ℓ q) = q)
    (hMc : ContinuousOn M (ℓ '' closure S)) (hM' : ∀ z ∈ ℓ '' closure S, M' (M z) = z)
    (hD : ∀ q ∈ closure S, q ∈ H → M (ℓ q) ∈ H \ fwdHull V T)
    {G : ℂ → ℂ} (hGc : ContinuousOn G (M '' (ℓ '' closure S))) (hGi : InjOn G (M '' (ℓ '' closure S)))
    (hGD : ∀ z ∈ M '' (ℓ '' closure S), z ∈ H \ fwdHull V T → G z = fwdMap V T z)
    (hGR : ∀ z ∈ M '' (ℓ '' closure S), z ∉ H \ fwdHull V T → (G z).im = 0)
    {ξ ρ : ℝ} (hball : Hbar ∩ ball (ξ : ℂ) ρ ⊆ closure S)
    (hreal : ∀ q ∈ closure S, q ∉ H → M (ℓ q) ∉ H \ fwdHull V T)
    (hdiff : DifferentiableOn ℂ (fun w => M (ℓ w)) (H ∩ ball (ξ : ℂ) ρ)) :
    R16.IsRealBoundaryConformal (fun w => G (M (ℓ w))) ξ ρ := by
  have hHb : H ∩ ball (ξ : ℂ) ρ ⊆ closure S := fun w hw => hball ⟨QuantumZipper.H_subset_Hbar hw.1, hw.2⟩
  have hmem : ∀ w ∈ closure S, M (ℓ w) ∈ M '' (ℓ '' closure S) := fun w hw => ⟨ℓ w, ⟨w, hw, rfl⟩, rfl⟩
  have heq : EqOn (fun w => G (M (ℓ w))) (fun w => fwdMap V T (M (ℓ w))) (H ∩ ball (ξ : ℂ) ρ) := fun w hw =>
    hGD _ (hmem w (hHb hw)) (hD w (hHb hw) hw.1)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine DifferentiableOn.congr ?_ heq
    exact (QuantumZipper.FwdHolo.differentiableOn_fwdMap hV hT).comp hdiff fun w hw => hD w (hHb hw) hw.1
  · refine hGc.comp (hMc.comp (hℓc.mono fun w hw => hKH (hball hw)) ?_) ?_
    · intro w hw; exact ⟨w, hball hw, rfl⟩
    · intro w hw; exact hmem w (hball hw)
  · intro z hz hz0
    have hzH : z ∈ Hbar := show 0 ≤ z.im by rw [hz0]
    have hzS := hball ⟨hzH, hz⟩
    exact hGR _ (hmem z hzS) (hreal z hzS fun h => by
      have : (0 : ℝ) < z.im := h
      linarith)
  · intro w hw
    rw [heq hw]
    exact QuantumZipper.FwdHolo.mapsTo_fwdMap hV hT (hD w (hHb hw) hw.1)
  · intro w hw w' hw' h
    have h1 := hGi (hmem w (hHb hw)) (hmem w' (hHb hw')) h
    have h2 : ℓ w = ℓ w' := by
      rw [← hM' _ ⟨w, hHb hw, rfl⟩, ← hM' _ ⟨w', hHb hw', rfl⟩, h1]
    rw [← hκ w (hKH (hHb hw)), ← hκ w' (hKH (hHb hw')), h2]

end Ext

end InteractingSLE.Sec7.Aux37Side
