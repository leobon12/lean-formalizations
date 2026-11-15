/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37AssemblyCfGerm

/-!
# Aux. lemma 37 at one rational witness: the pathwise exclusion from the germs and the witness frame

Packet PROVE-STRIPSYS39, item (3), pathwise part. Specification §6.2, Aux. lemma 37's proof (`source/spec/p193-240.md`
L104–L136, pp. 198–200).

At one sample, the source excludes a witness of attachment progress on a wall `A ∈ {α, β^{(q)}}` by comparing, along
one approach `F` to a wall point `z₀ = A(t₀)` from the pocket side, the flow-side germ of the mean at the rational
time `r` (G1), the counterflow-side germ of the mean at the rational time `s` (G2), the flat clock between `r` and `s`
(FC) and the branch relation of the two charts (BR). This file isolates the geometry the four comparisons need as
the **witness frames** `IsRightWitnessFrame` (on `α`) and `IsLeftWitnessFrame` (on `β^{(q)}`):

* the wall point `z₀ = A(t₀)` off the other wall and off the angle change; the counterflow hull at `r` absent from a
  ball around `z₀` (G1's input); `z₀` in the hull at `s` with the walls near `z₀` inside it (G2's input);
* an approach `F ≠ ⊥` from the pocket that is also an approach from off the exploration at `s`, eventually inside one
  component of `ℍ ∖ E_s` that is also a component of `ℍ ∖ E_r` (FC's input);
* the counterflow chart's real limit `y` along `F`, off the word's jumps, **on the traversal side (PFI3)**: `y > 0`,
  left of every right force position, on `α`; `y < 0`, right of every left force position, on `β^{(q)}`;
* the branch relation `Im(L_Ψ − L_f) → 2πk` for every own chart of the wall beyond `z₀` (deterministic, from the
  transition's real boundary values: `Aux37Germ.exists_int_tendsto_im_sub_of_transition`, see `brClause_of_transition`).

* **`false_of_rightFrame`**, **`false_of_leftFrame`**: given the three field statements at the sample (G1's and G2's
  germs for the representatives and FC's agreement), a witness frame is impossible ((PFI4), with the counterflow
  chart's branch shift `2πχ` on `α`).
* `false_of_flat_germs_shift`: (PFI4) with the counterflow germ shifted by `2πjχ`.

No Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, `*_of_param` (R43, R48).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology Bornology Function Complex
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Aux37Assembly

open QuantumZipper (H Hbar chiC fwdHull fwdMap logDerivFwd)
open WangWu (negInv revChart)
open PocketCoord

/-! ### (PFI4) with a branch shift -/

section Shift

/-- **(PFI4) with the counterflow germ shifted by `2πjχ`**: the shift is absorbed by the branch integer. -/
theorem false_of_flat_germs_shift {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {F : Filter ℂ} [F.NeBot]
    {Mr Ms u₀ : ℂ → ℝ} {Lf Lc : ℂ → ℂ} {ε θ : ℝ}
    (hside : (ε = 1 ∧ θ ∈ Ioc (-(π / 2)) (π / 2)) ∨ (ε = -1 ∧ θ ∈ Ico (-(π / 2)) (π / 2)))
    (hFC : Mr =ᶠ[F] Ms)
    (hG1 : Tendsto (fun z => Mr z + u₀ z + chiC κ * (Lf z).im) F (𝓝 (ε * sleLambda κ - θ * chiC κ)))
    (j : ℤ) (hG2 : Tendsto (fun z => Ms z + u₀ z + chiC κ * (Lc z).im) F
      (𝓝 (ε * sleLambda (16 / κ) - π * chiC κ + 2 * π * j * chiC κ)))
    (k : ℤ) (hBR : Tendsto (fun z => (Lc z - Lf z).im) F (𝓝 (2 * π * k))) : False := by
  set Lc' : ℂ → ℂ := fun z => Lc z - ((2 * π * j : ℝ) : ℂ) * I with hLc'
  have him : ∀ z, (Lc' z).im = (Lc z).im - 2 * π * j := fun z => by
    simp only [hLc', sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_one, mul_zero, add_zero]
  have hG2' : Tendsto (fun z => Ms z + u₀ z + chiC κ * (Lc' z).im) F
      (𝓝 (ε * sleLambda (16 / κ) - π * chiC κ)) := by
    have := hG2.sub_const (2 * π * j * chiC κ)
    simp only [add_sub_cancel_right] at this
    refine this.congr fun z => ?_
    rw [him]
    ring
  have hBR' : Tendsto (fun z => (Lc' z - Lf z).im) F (𝓝 (2 * π * ((k - j : ℤ) : ℝ))) := by
    have := hBR.sub_const (2 * π * j)
    rw [show 2 * π * (k : ℝ) - 2 * π * j = 2 * π * ((k - j : ℤ) : ℝ) by push_cast; ring] at this
    refine this.congr fun z => ?_
    rw [sub_im, sub_im, him]
    ring
  exact Aux37Germ.false_of_flat_germs_strip hκ hκ4 hside hFC hG1 hG2' hBR'

end Shift

/-! ### The witness frames -/

section Frame

variable {nL nR : ℕ}

/-- **The witness frame on the right wall `α`** (pathwise geometry of Aux. lemma 37's comparison at one sample):
`R = α`, `L = β^{(q)}` (stage time `r`), counterflow hulls `Ar`, `As` at the rational times `r₀ ≤ s₀`, explorations
`Er = Ar ∪ Wu`, `Es = As ∪ Wu` (`Wu` the walls), counterflow driver `w`, own driver `d` of `α`, counterflow force
positions `posL`, `posR` at `s₀`. See the module docstring. -/
def IsRightWitnessFrame (R L : ℝ≥0 → ℂ) (r : ℝ≥0) (Ar As Wu Er Es : Set ℂ) (w d : ℝ → ℝ) (s₀ : ℝ≥0)
    (posL : Fin nL → ℝ) (posR : Fin nR → ℝ) : Prop :=
  ∃ t₀ : ℝ≥0, R t₀ ∉ range L ∧ t₀ ≠ 1 ∧ (∃ ε > 0, Ar ∩ ball (R t₀) ε = ∅) ∧ R t₀ ∈ As ∧
    (∃ ε > 0, Wu ∩ ball (R t₀) ε ⊆ As) ∧
    ∃ F : Filter ℂ, F.NeBot ∧ F ≤ 𝓝[changePocket R L r] (R t₀) ∧ F ≤ 𝓝[H \ Es] (R t₀) ∧
      (∃ z ∈ H \ Es, connectedComponentIn (H \ Es) z = connectedComponentIn (H \ Er) z ∧
        ∀ᶠ x in F, x ∈ connectedComponentIn (H \ Es) z) ∧
      (∃ y : ℝ, Tendsto (fun z => fwdMap w s₀ (negInv z)) F (𝓝 (y : ℂ)) ∧ y ∉ forceJumpSet posL posR ∧
        0 < y ∧ ∀ i, y ≤ posR i) ∧
      ∀ q' : ℝ≥0, t₀ < q' → ∃ k : ℤ,
        Tendsto (fun z => (Sec5.GlueImg.logDerivPsi w s₀ z - logDerivFwd d q' z).im) F (𝓝 (2 * π * k))

/-- **The witness frame on the left wall `β^{(q)}`** (as `IsRightWitnessFrame`, with the wall point `L(t₀)` off `α`
and off the stage time `r`, and the counterflow chart's limit `y < 0` right of every left force position). -/
def IsLeftWitnessFrame (R L : ℝ≥0 → ℂ) (r : ℝ≥0) (Ar As Wu Er Es : Set ℂ) (w d : ℝ → ℝ) (s₀ : ℝ≥0)
    (posL : Fin nL → ℝ) (posR : Fin nR → ℝ) : Prop :=
  ∃ t₀ : ℝ≥0, L t₀ ∉ range R ∧ t₀ ≠ r ∧ (∃ ε > 0, Ar ∩ ball (L t₀) ε = ∅) ∧ L t₀ ∈ As ∧
    (∃ ε > 0, Wu ∩ ball (L t₀) ε ⊆ As) ∧
    ∃ F : Filter ℂ, F.NeBot ∧ F ≤ 𝓝[changePocket R L r] (L t₀) ∧ F ≤ 𝓝[H \ Es] (L t₀) ∧
      (∃ z ∈ H \ Es, connectedComponentIn (H \ Es) z = connectedComponentIn (H \ Er) z ∧
        ∀ᶠ x in F, x ∈ connectedComponentIn (H \ Es) z) ∧
      (∃ y : ℝ, Tendsto (fun z => fwdMap w s₀ (negInv z)) F (𝓝 (y : ℂ)) ∧ y ∉ forceJumpSet posL posR ∧
        y < 0 ∧ ∀ i, posL i ≤ y) ∧
      ∀ q' : ℝ≥0, t₀ < q' → ∃ k : ℤ,
        Tendsto (fun z => (Sec5.GlueImg.logDerivPsi w s₀ z - logDerivFwd d q' z).im) F (𝓝 (2 * π * k))

end Frame

/-! ### The pathwise exclusion -/

section Exclusion

variable {κ : ℝ} {nL nR : ℕ} {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {Ar As Wu Er Es : Set ℂ} {w d : ℝ → ℝ} {s₀ : ℝ≥0}
  {posL : Fin nL → ℝ} {posR : Fin nR → ℝ} {vr vs u₀ : ℂ → ℝ}

/-- **No witness frame on the right wall** (Aux. lemma 37, (PFI2)–(PFI4) at one sample, `ε = −1`): given, at the
sample, the right-wall flow-side germs of the representative `vr` at `r₀` (G1), the counterflow-side germ of the
representative `vs` at `s₀` on the positive side (G2), and the flat clock's agreement of `vr` and `vs` on the
components unchanged between `r₀` and `s₀` (FC), a right witness frame is impossible. -/
theorem false_of_rightFrame (hκ : 0 < κ) (hκ4 : κ < 4) {θ₁ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2))
    (hG1 : ∀ t₀ : ℝ≥0, R t₀ ∉ range L → t₀ ≠ 1 → (∃ ε > 0, Ar ∩ ball (R t₀) ε = ∅) → ∃ q' : ℝ≥0, t₀ < q' ∧
      Tendsto (fun z => vr z + u₀ z + chiC κ * (logDerivFwd d q' z).im) (𝓝[changePocket R L r] (R t₀))
        (𝓝 (-sleLambda κ - (if t₀ < 1 then -(π / 2) else θ₁) * chiC κ)))
    (hG2 : ∀ z₀ ∈ As, (∃ ε > 0, Wu ∩ ball z₀ ε ⊆ As) → ∀ F : Filter ℂ, F ≤ 𝓝[H \ Es] z₀ → ∀ y : ℝ,
      Tendsto (fun z => fwdMap w s₀ (negInv z)) F (𝓝 (y : ℂ)) → y ∉ forceJumpSet posL posR → 0 < y →
        (∀ i, y ≤ posR i) → Tendsto (fun z => vs z + u₀ z + chiC κ * (Sec5.GlueImg.logDerivPsi w s₀ z).im) F
          (𝓝 (-sleLambda (16 / κ) + π * chiC κ)))
    (hFC : ∀ z ∈ H \ Es, connectedComponentIn (H \ Es) z = connectedComponentIn (H \ Er) z →
      ∀ x ∈ connectedComponentIn (H \ Es) z, vr x = vs x)
    (hfr : IsRightWitnessFrame R L r Ar As Wu Er Es w d s₀ posL posR) : False := by
  obtain ⟨t₀, hoff, hne, hAr, hAs, hWu, F, hFne, hF1, hFE, ⟨z, hz, hcomp, hFcomp⟩, ⟨y, hy, hyJ, hy0, hyR⟩,
    hBR⟩ := hfr
  obtain ⟨q', hq', hlim⟩ := hG1 t₀ hoff hne hAr
  obtain ⟨k, hk⟩ := hBR q' hq'
  have hG2' := hG2 _ hAs hWu F hFE y hy hyJ hy0 hyR
  have hFCeq : vr =ᶠ[F] vs := Aux37Germ.eventuallyEq_of_flatClock (hFC z hz hcomp) hFcomp
  have hside : ((-1 : ℝ) = 1 ∧ (if t₀ < 1 then -(π / 2) else θ₁) ∈ Ioc (-(π / 2)) (π / 2)) ∨
      ((-1 : ℝ) = -1 ∧ (if t₀ < 1 then -(π / 2) else θ₁) ∈ Ico (-(π / 2)) (π / 2)) := by
    refine Or.inr ⟨rfl, ?_⟩
    split_ifs
    · exact ⟨le_rfl, by linarith [Real.pi_pos]⟩
    · exact Ioo_subset_Ico_self hθ₁
  refine false_of_flat_germs_shift (u₀ := u₀) hκ hκ4 hside hFCeq ?_ 1 ?_ k hk
  · rw [neg_one_mul]
    exact hlim.mono_left hF1
  · convert hG2' using 2
    push_cast
    ring

/-- **No witness frame on the left wall** (as `false_of_rightFrame`, `ε = 1`, the counterflow germ on the negative
side, no branch shift). -/
theorem false_of_leftFrame (hκ : 0 < κ) (hκ4 : κ < 4) {θ₂ : ℝ} (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2))
    (hG1 : ∀ t₀ : ℝ≥0, L t₀ ∉ range R → t₀ ≠ r → (∃ ε > 0, Ar ∩ ball (L t₀) ε = ∅) → ∃ q' : ℝ≥0, t₀ < q' ∧
      Tendsto (fun z => vr z + u₀ z + chiC κ * (logDerivFwd d q' z).im) (𝓝[changePocket R L r] (L t₀))
        (𝓝 (sleLambda κ - (if t₀ < r then π / 2 else θ₂) * chiC κ)))
    (hG2 : ∀ z₀ ∈ As, (∃ ε > 0, Wu ∩ ball z₀ ε ⊆ As) → ∀ F : Filter ℂ, F ≤ 𝓝[H \ Es] z₀ → ∀ y : ℝ,
      Tendsto (fun z => fwdMap w s₀ (negInv z)) F (𝓝 (y : ℂ)) → y ∉ forceJumpSet posL posR → y < 0 →
        (∀ i, posL i ≤ y) → Tendsto (fun z => vs z + u₀ z + chiC κ * (Sec5.GlueImg.logDerivPsi w s₀ z).im) F
          (𝓝 (sleLambda (16 / κ) - π * chiC κ)))
    (hFC : ∀ z ∈ H \ Es, connectedComponentIn (H \ Es) z = connectedComponentIn (H \ Er) z →
      ∀ x ∈ connectedComponentIn (H \ Es) z, vr x = vs x)
    (hfr : IsLeftWitnessFrame R L r Ar As Wu Er Es w d s₀ posL posR) : False := by
  obtain ⟨t₀, hoff, hne, hAr, hAs, hWu, F, hFne, hF1, hFE, ⟨z, hz, hcomp, hFcomp⟩, ⟨y, hy, hyJ, hy0, hyL⟩,
    hBR⟩ := hfr
  obtain ⟨q', hq', hlim⟩ := hG1 t₀ hoff hne hAr
  obtain ⟨k, hk⟩ := hBR q' hq'
  have hG2' := hG2 _ hAs hWu F hFE y hy hyJ hy0 hyL
  have hFCeq : vr =ᶠ[F] vs := Aux37Germ.eventuallyEq_of_flatClock (hFC z hz hcomp) hFcomp
  have hside : ((1 : ℝ) = 1 ∧ (if t₀ < r then π / 2 else θ₂) ∈ Ioc (-(π / 2)) (π / 2)) ∨
      ((1 : ℝ) = -1 ∧ (if t₀ < r then π / 2 else θ₂) ∈ Ico (-(π / 2)) (π / 2)) := by
    refine Or.inl ⟨rfl, ?_⟩
    split_ifs
    · exact ⟨by linarith [Real.pi_pos], le_rfl⟩
    · exact hθ₂
  refine false_of_flat_germs_shift (u₀ := u₀) hκ hκ4 hside hFCeq ?_ 0 ?_ k hk
  · rw [one_mul]
    exact hlim.mono_left hF1
  · convert hG2' using 2
    push_cast
    ring

end Exclusion

/-! ### The branch clause from the transition's real boundary values -/

section Branch

/-- **The frames' branch clause from the transition** ((BR), p. 199): for continuous drivers `d` (own chart
`f = fwdMap d q′` of the wall) and `w` (counterflow chart `Ψ = m ∘ f_s ∘ m`), if near the own-chart limit `x` of the
approach the inverse `g` of the own chart maps a half-disc into both chart domains and `Ψ ∘ g` has real boundary
values there (`R16.IsRealBoundaryConformal`), then `Im(L_Ψ − L_f) → 2πk` along the approach. -/
theorem brClause_of_transition {w d : ℝ → ℝ} (hw : Continuous w) (hd : Continuous d) (s₀ q' : ℝ≥0) {x ρ : ℝ}
    {g : ℂ → ℂ} (hρ : 0 < ρ)
    (hg : MapsTo g (H ∩ ball (x : ℂ) ρ) ((H \ fwdHull d q') ∩ (H \ negInv '' fwdHull w s₀)))
    (hgc : ContinuousOn g (H ∩ ball (x : ℂ) ρ)) (hfg : ∀ v ∈ H ∩ ball (x : ℂ) ρ, fwdMap d q' (g v) = v)
    (hgf : ∀ z ∈ (H \ fwdHull d q') ∩ (H \ negInv '' fwdHull w s₀), fwdMap d q' z ∈ H ∩ ball (x : ℂ) ρ →
      g (fwdMap d q' z) = z)
    (hψ : R16.IsRealBoundaryConformal (revChart w s₀ ∘ g) x ρ) {F : Filter ℂ}
    (hF : Tendsto (fwdMap d q') F (𝓝[H] (x : ℂ)))
    (hFD : ∀ᶠ z in F, z ∈ (H \ fwdHull d q') ∩ (H \ negInv '' fwdHull w s₀)) :
    ∃ k : ℤ, Tendsto (fun z => (Sec5.GlueImg.logDerivPsi w s₀ z - logDerivFwd d q' z).im) F (𝓝 (2 * π * k)) := by
  have hD : IsOpen ((H \ fwdHull d q') ∩ (H \ negInv '' fwdHull w s₀)) :=
    (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hd q'.coe_nonneg).inter
      (Sec5.GlueImg.isOpen_H_diff_negInv_fwdHull hw s₀.coe_nonneg)
  have hLf := (isDerivLog_fwdMap hd q'.coe_nonneg).mono
    (inter_subset_left (s := H \ fwdHull d q') (t := H \ negInv '' fwdHull w s₀))
  have hLc := (Sec5.GlueImg.isDerivLog_revChart hw s₀.coe_nonneg).mono
    (inter_subset_right (s := H \ fwdHull d q') (t := H \ negInv '' fwdHull w s₀))
  exact Aux37Germ.exists_int_tendsto_im_sub_of_transition hD hLf hLc hρ hg hgc hfg hgf hψ hF hFD

end Branch

end InteractingSLE.Sec7.Aux37Assembly
