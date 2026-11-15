/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.KernelDriver

/-!
# The general restart kernel

Packet PROVE-RESTARTKERNEL. **The general theorem** behind the restart kernels of Lemma G7 (`KernelG7.lean`), the
first-contact restart (R2′) (`KernelFC.lean`), GB6's relative law (its part (d)), the counterflow restarts of §5 and
Lemma 7.6's continuation law: for curves coupled with a field and stopped at stopping times of their histories, the
conditional law of (chart field, continuations) given the stopped histories is the canonical one in the chart of the
active component, as soon as

* **(R1)** conditionally on the stopped histories `𝒢`, on the event `M`, the chart field has the Gaussian
  characteristic functional of the GFF with the word of the datum `β` (the field off the union is the conditional mean
  plus a zero-boundary GFF, and the mean has the boundary word given by the side heights); and
* **(Det)** almost surely on `M`, each continuation (read in the chart, with its lifetime) is the decoded canonical
  flow code of the chart field with the word and seed of `β` (W8's proof, p. 541: "Universal finite-force determination
  now identifies each actual conditional future … as the canonical flow of the same conditional field").

Then for **every** Markov kernel `K` disintegrating the restart variable over the datum on `M` (and one exists when the
canonical space is standard Borel), for almost every datum `c`, under `K c` the chart field is a GFF with the word of
`c` and every continuation is its flow line (`IsFlowLine`), or drives it (`IsFlowLineDriver`).

## Main results

* **`restartKernel_isFlowLine_of_codeMatch`** (every disintegrating kernel) and **`exists_restartKernel_of_codeMatch`**
  (existence), for a countable family of trace continuations with canonical flow codes (`IsFlowCode`);
* **`restartKernel_isFlowLineDriver_of_codeMatch`**, `exists_restartKernel_of_driverCodeMatch`: the same for driver
  continuations with canonical driver codes (`IsDriverCode`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

open LQGMetric Sec2.Assembly

section General

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {C S : Type} [MeasurableSpace C] [MeasurableSpace S] {M : Set Ω} {β : Ω → C} {X : Ω → S}
  {w : C → BoundaryWord} {H : S → DistOn upperHalfPlaneOpens} {ι : Type*} [Countable ι] {κ : ℝ}

/-- **The general restart kernel, trace form, for every disintegrating kernel.** (R1) for the chart field `H ∘ X` given
`𝒢` on `M` with the word `w ∘ β`, and (Det) for a countable family of continuation coordinates `(Γ i, U i)` (each
continuous on its closed lifetime interval at every point of `S`) with canonical flow codes `F i` of angles `θ i` from
seeds `x i ∘ β`, give: for every Markov kernel `K` disintegrating `(β, X)` on `M`, for almost every datum `c`, the word
`w c` is sorted, `H` is a GFF with it under `K c`, and every `Γ i` with lifetime `U i` is the angle-`θ i` flow line of
`H` from `x i c` under `K c`. -/
theorem restartKernel_isFlowLine_of_codeMatch (h𝒢 : 𝒢 ≤ mΩ) (hM : MeasurableSet[𝒢] M)
    (hβ : Measurable[𝒢] β) (hw : Measurable w) (hX : Measurable X) (hH : Measurable H)
    (hsort : ∀ᵐ ω ∂P, ω ∈ M → (w (β ω)).IsSorted)
    (hR1 : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
      P[fun ω' => Complex.exp (Complex.I * (H (X ω') φ : ℂ)) | 𝒢] ω = gaussCF (w (β ω)) φ)
    {x : ι → C → ℝ} (hx : ∀ i, Measurable (x i)) {θ : ι → ℝ} {Γ : ι → S → ℝ≥0 → ℂ}
    (hΓ : ∀ i t, Measurable fun s => Γ i s t) {U : ι → S → ℝ≥0∞} (hU : ∀ i, Measurable (U i))
    (hΓc : ∀ i s, ContinuousOn (Γ i s) {t | (t : ℝ≥0∞) ≤ U i s})
    {F : ι → (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hF : ∀ i, IsFlowCode κ (θ i) (F i))
    (hdet : ∀ i, ∀ᵐ ω ∂P, ω ∈ M →
      IsCodeMatch (F i ((w (β ω), x i (β ω)), H (X ω))) (Γ i (X ω)) (U i (X ω)))
    (K : Kernel C S) [IsMarkovKernel K]
    (hlaw : (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K) :
    ∀ᵐ c ∂(P.restrict M).map β, (w c).IsSorted ∧ IsGFFWithBoundaryData (K c) H (w c).fn (w c).jumps ∧
      ∀ i, IsFlowLine κ (w c).fn (w c).jumps (x i c) (θ i) (K c) H (Γ i) (U i) := by
  have hβm : Measurable β := hβ.mono h𝒢 le_rfl
  have hMm : MeasurableSet M := h𝒢 _ hM
  have hgff := ae_isGFFWithBoundaryData_of_condExp_word h𝒢 hM hβ hw hsort hX hH hlaw hR1
  have hfl : ∀ i, ∀ᵐ c ∂(P.restrict M).map β,
      IsFlowLine κ (w c).fn (w c).jumps (x i c) (θ i) (K c) H (Γ i) (U i) := fun i =>
    ae_isFlowLine_of_codeMatch hMm hβm hX hlaw hw (hx i) hH (hΓ i) (hU i) (hΓc i) (hF i) hgff (hdet i)
  filter_upwards [hgff, ae_all_iff.2 hfl] with c ⟨hcs, hcg⟩ hc
  exact ⟨hcs, hcg, hc⟩

/-- **The general restart kernel, trace form, existence**: on a standard Borel canonical space, the conditional law of
the restart variable given the datum on `M` is a Markov kernel with the conclusions of
`restartKernel_isFlowLine_of_codeMatch`. -/
theorem exists_restartKernel_of_codeMatch [StandardBorelSpace S] [Nonempty S] (h𝒢 : 𝒢 ≤ mΩ)
    (hM : MeasurableSet[𝒢] M) (hβ : Measurable[𝒢] β) (hw : Measurable w) (hX : Measurable X)
    (hH : Measurable H) (hsort : ∀ᵐ ω ∂P, ω ∈ M → (w (β ω)).IsSorted)
    (hR1 : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
      P[fun ω' => Complex.exp (Complex.I * (H (X ω') φ : ℂ)) | 𝒢] ω = gaussCF (w (β ω)) φ)
    {x : ι → C → ℝ} (hx : ∀ i, Measurable (x i)) {θ : ι → ℝ} {Γ : ι → S → ℝ≥0 → ℂ}
    (hΓ : ∀ i t, Measurable fun s => Γ i s t) {U : ι → S → ℝ≥0∞} (hU : ∀ i, Measurable (U i))
    (hΓc : ∀ i s, ContinuousOn (Γ i s) {t | (t : ℝ≥0∞) ≤ U i s})
    {F : ι → (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hF : ∀ i, IsFlowCode κ (θ i) (F i))
    (hdet : ∀ i, ∀ᵐ ω ∂P, ω ∈ M →
      IsCodeMatch (F i ((w (β ω), x i (β ω)), H (X ω))) (Γ i (X ω)) (U i (X ω))) :
    ∃ K : Kernel C S, IsMarkovKernel K ∧
      (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K ∧
      ∀ᵐ c ∂(P.restrict M).map β, (w c).IsSorted ∧ IsGFFWithBoundaryData (K c) H (w c).fn (w c).jumps ∧
        ∀ i, IsFlowLine κ (w c).fn (w c).jumps (x i c) (θ i) (K c) H (Γ i) (U i) := by
  obtain ⟨K, hK, hlaw⟩ := exists_isMarkovKernel_map_eq_compProd P M (hβ.mono h𝒢 le_rfl) hX
  exact ⟨K, hK, hlaw, restartKernel_isFlowLine_of_codeMatch h𝒢 hM hβ hw hX hH hsort hR1 hx hΓ hU hΓc hF hdet K
    hlaw⟩

/-- **The general restart kernel, driver form, for every disintegrating kernel**: as
`restartKernel_isFlowLine_of_codeMatch`, for a countable family of driver coordinates `(WC i, L i)` (each continuous
before its lifetime at every point of `S`) with canonical driver codes `F i` of angles `θ i`; the conclusion is the
frozen `IsFlowLineDriver` under `K c`. -/
theorem restartKernel_isFlowLineDriver_of_codeMatch (h𝒢 : 𝒢 ≤ mΩ) (hM : MeasurableSet[𝒢] M)
    (hβ : Measurable[𝒢] β) (hw : Measurable w) (hX : Measurable X) (hH : Measurable H)
    (hsort : ∀ᵐ ω ∂P, ω ∈ M → (w (β ω)).IsSorted)
    (hR1 : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
      P[fun ω' => Complex.exp (Complex.I * (H (X ω') φ : ℂ)) | 𝒢] ω = gaussCF (w (β ω)) φ)
    {θ : ι → ℝ} {WC : ι → ℝ≥0 → S → ℝ} (hWC : ∀ i t, Measurable (WC i t)) {L : ι → S → ℝ≥0∞}
    (hL : ∀ i, Measurable (L i)) (hWCc : ∀ i s, ContinuousOn (fun t => WC i t s) {t | (t : ℝ≥0∞) < L i s})
    {F : ι → BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞} (hF : ∀ i, IsDriverCode κ (θ i) (F i))
    (hdet : ∀ i, ∀ᵐ ω ∂P, ω ∈ M →
      IsDriverCodeMatch (F i (w (β ω), H (X ω))) (fun t => WC i t (X ω)) (L i (X ω)))
    (K : Kernel C S) [IsMarkovKernel K]
    (hlaw : (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K) :
    ∀ᵐ c ∂(P.restrict M).map β, (w c).IsSorted ∧ IsGFFWithBoundaryData (K c) H (w c).fn (w c).jumps ∧
      ∀ i, IsFlowLineDriver κ (w c).fn (w c).jumps (θ i) (K c) H (WC i) (L i) := by
  have hβm : Measurable β := hβ.mono h𝒢 le_rfl
  have hMm : MeasurableSet M := h𝒢 _ hM
  have hgff := ae_isGFFWithBoundaryData_of_condExp_word h𝒢 hM hβ hw hsort hX hH hlaw hR1
  have hfl : ∀ i, ∀ᵐ c ∂(P.restrict M).map β,
      IsFlowLineDriver κ (w c).fn (w c).jumps (θ i) (K c) H (WC i) (L i) := fun i =>
    ae_isFlowLineDriver_of_codeMatch hMm hβm hX hlaw hw hH (hWC i) (hL i) (hWCc i) (hF i) hgff (hdet i)
  filter_upwards [hgff, ae_all_iff.2 hfl] with c ⟨hcs, hcg⟩ hc
  exact ⟨hcs, hcg, hc⟩

/-- **The general restart kernel, driver form, existence** (standard Borel canonical space). -/
theorem exists_restartKernel_of_driverCodeMatch [StandardBorelSpace S] [Nonempty S] (h𝒢 : 𝒢 ≤ mΩ)
    (hM : MeasurableSet[𝒢] M) (hβ : Measurable[𝒢] β) (hw : Measurable w) (hX : Measurable X)
    (hH : Measurable H) (hsort : ∀ᵐ ω ∂P, ω ∈ M → (w (β ω)).IsSorted)
    (hR1 : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
      P[fun ω' => Complex.exp (Complex.I * (H (X ω') φ : ℂ)) | 𝒢] ω = gaussCF (w (β ω)) φ)
    {θ : ι → ℝ} {WC : ι → ℝ≥0 → S → ℝ} (hWC : ∀ i t, Measurable (WC i t)) {L : ι → S → ℝ≥0∞}
    (hL : ∀ i, Measurable (L i)) (hWCc : ∀ i s, ContinuousOn (fun t => WC i t s) {t | (t : ℝ≥0∞) < L i s})
    {F : ι → BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞} (hF : ∀ i, IsDriverCode κ (θ i) (F i))
    (hdet : ∀ i, ∀ᵐ ω ∂P, ω ∈ M →
      IsDriverCodeMatch (F i (w (β ω), H (X ω))) (fun t => WC i t (X ω)) (L i (X ω))) :
    ∃ K : Kernel C S, IsMarkovKernel K ∧
      (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K ∧
      ∀ᵐ c ∂(P.restrict M).map β, (w c).IsSorted ∧ IsGFFWithBoundaryData (K c) H (w c).fn (w c).jumps ∧
        ∀ i, IsFlowLineDriver κ (w c).fn (w c).jumps (θ i) (K c) H (WC i) (L i) := by
  obtain ⟨K, hK, hlaw⟩ := exists_isMarkovKernel_map_eq_compProd P M (hβ.mono h𝒢 le_rfl) hX
  exact ⟨K, hK, hlaw, restartKernel_isFlowLineDriver_of_codeMatch h𝒢 hM hβ hw hX hH hsort hR1 hWC hL hWCc hF
    hdet K hlaw⟩

end General

end Restart

end InteractingSLE
