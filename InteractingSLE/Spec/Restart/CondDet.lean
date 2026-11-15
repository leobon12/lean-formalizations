/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowCodeMain
import InteractingSLE.Spec.Restart.KernelMain

/-!
# Conditional determination (Det) and the restart kernel: the two directions

Packet PROVE-CONDDET. PROVE-RESTARTKERNEL's general restart kernel (`restartKernel_isFlowLine_of_codeMatch`) turns
(R1) (the chart field is conditionally a GFF with the word) and the pathwise identity **(Det)** (almost surely the
continuation matches the canonical flow code of the chart field) into: under almost every kernel measure the
continuation is the flow line of the chart field. Its code hypothesis `IsFlowCode` is unsatisfiable (`FlowCode.lean`);
this file restates it with the corrected canonical codes (`IsCanonicalFlowCode`, proved from Theorems 1.2–1.3 in
`FlowCodeMain.lean`) and proves the converse, so that (Det) is **equivalent** to the kernel conclusion:

* `ae_isFlowLine_of_codeMatch_canonical`, `ae_isFlowLineDriver_of_codeMatch_canonical`,
  **`restartKernel_isFlowLine_of_codeMatch_canonical`**, `restartKernel_isFlowLineDriver_of_codeMatch_canonical`: the
  restart kernel theorems with canonical codes;
* `ae_mem_of_ae_ae_compProd`: an event that holds for almost every datum under almost every kernel measure holds almost
  surely on `M` (the lift back);
* **`ae_codeMatch_of_ae_isFlowLine`**, `ae_driverCodeMatch_of_ae_isFlowLineDriver`: (Det) from the kernel side
  (determination under each kernel measure, Theorem 1.2, then the lift back);
* **`restartKernel_codeMatch_iff`**, `restartKernel_driverCodeMatch_iff`: under (R1), (Det) for a family of
  continuations holds iff under almost every kernel measure each continuation is the flow line (resp. drives it).

So (Det) carries exactly the content "the conditional future is the flow line of the conditional field" (W8's proof,
p. 541: nested Gaussian kernels, the outer-word mean identification, Theorem 2.4 under the conditional law), and does
not depend on which canonical code is used.

**R43.** Canonical codes use Theorems 1.2–1.3; these lemmas serve Theorems 1.4–1.5's restarts only.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

open LQGMetric Sec2.Assembly

/-! ### The kernel lemmas with canonical codes -/

section Kernel

variable {Ω : Type*} {C S : Type} [MeasurableSpace Ω] [MeasurableSpace C] [MeasurableSpace S] {P : Measure Ω}
  [IsFiniteMeasure P] {M : Set Ω} {β : Ω → C} {X : Ω → S} {K : Kernel C S} [IsMarkovKernel K]
  {w : C → BoundaryWord} {H : S → DistOn upperHalfPlaneOpens} {κ θ : ℝ}

/-- **The continuation is the flow line under almost every kernel measure** (`ae_isFlowLine_of_codeMatch` with a
canonical flow code). -/
theorem ae_isFlowLine_of_codeMatch_canonical (hM : MeasurableSet M) (hβ : Measurable β) (hX : Measurable X)
    (hlaw : (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K) (hw : Measurable w)
    {x : C → ℝ} (hx : Measurable x) (hH : Measurable H) {Γ : S → ℝ≥0 → ℂ} (hΓ : ∀ t, Measurable fun s => Γ s t)
    {U : S → ℝ≥0∞} (hU : Measurable U) (hΓc : ∀ s, ContinuousOn (Γ s) {t | (t : ℝ≥0∞) ≤ U s})
    {F : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞} (hF : IsCanonicalFlowCode κ θ F)
    (hgff : ∀ᵐ c ∂(P.restrict M).map β, (w c).IsSorted ∧ IsGFFWithBoundaryData (K c) H (w c).fn (w c).jumps)
    (hdet : ∀ᵐ ω ∂P, ω ∈ M → IsCodeMatch (F ((w (β ω), x (β ω)), H (X ω))) (Γ (X ω)) (U (X ω))) :
    ∀ᵐ c ∂(P.restrict M).map β, IsFlowLine κ (w c).fn (w c).jumps (x c) θ (K c) H Γ U := by
  set G : C × S → (PCode × PCode) × ℝ≥0∞ := fun p => F ((w p.1, x p.1), H p.2) with hGdef
  have hGm : Measurable G := hF.1.comp (((hw.comp measurable_fst).prodMk (hx.comp measurable_fst)).prodMk
    (hH.comp measurable_snd))
  have hE := measurableSet_codeMatchSet hGm hΓ hU
  have hK := ae_ae_of_map_eq_compProd hM hβ hX hlaw hE (by
    filter_upwards [hdet] with ω hω hωM
    exact mem_codeMatchSet_of_codeMatch (G := G) (p := (β ω, X ω)) (hω hωM))
  filter_upwards [hK, hgff] with c hc ⟨hcs, hcg⟩
  refine hF.2.1 (w c) (x c) hcs (K c) H Γ U hcg hU ?_
  filter_upwards [hc] with s hs
  exact codeMatch_of_mem_codeMatchSet (G := G) (p := (c, s)) (hΓc s) hs

/-- **The driver coordinate drives the flow line under almost every kernel measure** (with a canonical driver code). -/
theorem ae_isFlowLineDriver_of_codeMatch_canonical (hM : MeasurableSet M) (hβ : Measurable β) (hX : Measurable X)
    (hlaw : (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K) (hw : Measurable w)
    (hH : Measurable H) {WC : ℝ≥0 → S → ℝ} (hWC : ∀ t, Measurable (WC t)) {L : S → ℝ≥0∞} (hL : Measurable L)
    (hWCc : ∀ s, ContinuousOn (fun t => WC t s) {t | (t : ℝ≥0∞) < L s})
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞} (hF : IsCanonicalDriverCode κ θ F)
    (hgff : ∀ᵐ c ∂(P.restrict M).map β, (w c).IsSorted ∧ IsGFFWithBoundaryData (K c) H (w c).fn (w c).jumps)
    (hdet : ∀ᵐ ω ∂P, ω ∈ M → IsDriverCodeMatch (F (w (β ω), H (X ω))) (fun t => WC t (X ω)) (L (X ω))) :
    ∀ᵐ c ∂(P.restrict M).map β, IsFlowLineDriver κ (w c).fn (w c).jumps θ (K c) H WC L := by
  set G : C × S → PCode × ℝ≥0∞ := fun p => F (w p.1, H p.2) with hGdef
  have hGm : Measurable G := hF.1.comp ((hw.comp measurable_fst).prodMk (hH.comp measurable_snd))
  have hE := measurableSet_driverCodeMatch hGm hWC hL
  have hK := ae_ae_of_map_eq_compProd hM hβ hX hlaw hE (by
    filter_upwards [hdet] with ω hω hωM
    exact hω hωM)
  filter_upwards [hK, hgff] with c hc ⟨hcs, hcg⟩
  exact hF.2.1 (w c) hcs (K c) H WC L hcg hWC hL hWCc hc

/-! ### The lift back -/

omit [IsFiniteMeasure P] [IsMarkovKernel K] in
/-- **The lift back**: an event of `(datum, restart point)` that holds for almost every datum under almost every
kernel measure holds almost surely on `M`. -/
theorem ae_mem_of_ae_ae_compProd (hM : MeasurableSet M) (hβ : Measurable β) (hX : Measurable X)
    (hlaw : (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K) {E : Set (C × S)}
    (hE : MeasurableSet E) (h : ∀ᵐ c ∂(P.restrict M).map β, ∀ᵐ s ∂(K c), (c, s) ∈ E) :
    ∀ᵐ ω ∂P, ω ∈ M → (β ω, X ω) ∈ E := by
  have h1 : ∀ᵐ p ∂((P.restrict M).map β ⊗ₘ K), p ∈ E := Measure.ae_compProd_of_ae_ae hE h
  rw [← hlaw] at h1
  have h2 := (ae_map_iff (hβ.prodMk hX).aemeasurable hE).1 h1
  exact (ae_restrict_iff' hM).1 h2

omit [IsFiniteMeasure P] in
/-- **(Det) from the kernel side**: if under almost every kernel measure the continuation is the flow line of the
chart field, then almost surely on `M` it matches the canonical flow code of the chart field (determination under each
kernel measure, then the lift back). -/
theorem ae_codeMatch_of_ae_isFlowLine (hM : MeasurableSet M) (hβ : Measurable β) (hX : Measurable X)
    (hlaw : (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K) (hw : Measurable w)
    {x : C → ℝ} (hx : Measurable x) (hH : Measurable H) {Γ : S → ℝ≥0 → ℂ} (hΓ : ∀ t, Measurable fun s => Γ s t)
    {U : S → ℝ≥0∞} (hU : Measurable U) (hΓc : ∀ s, ContinuousOn (Γ s) {t | (t : ℝ≥0∞) ≤ U s})
    {F : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞} (hF : IsCanonicalFlowCode κ θ F)
    (hfl : ∀ᵐ c ∂(P.restrict M).map β, IsFlowLine κ (w c).fn (w c).jumps (x c) θ (K c) H Γ U) :
    ∀ᵐ ω ∂P, ω ∈ M → IsCodeMatch (F ((w (β ω), x (β ω)), H (X ω))) (Γ (X ω)) (U (X ω)) := by
  set G : C × S → (PCode × PCode) × ℝ≥0∞ := fun p => F ((w p.1, x p.1), H p.2) with hGdef
  have hGm : Measurable G := hF.1.comp (((hw.comp measurable_fst).prodMk (hx.comp measurable_fst)).prodMk
    (hH.comp measurable_snd))
  have hE := measurableSet_codeMatchSet hGm hΓ hU
  have h := ae_mem_of_ae_ae_compProd hM hβ hX hlaw hE (by
    filter_upwards [hfl] with c hc
    filter_upwards [hF.2.2 (w c) (x c) (K c) H Γ U hc] with s hs
    exact mem_codeMatchSet_of_codeMatch (G := G) (p := (c, s)) hs)
  filter_upwards [h] with ω hω hωM
  exact codeMatch_of_mem_codeMatchSet (G := G) (p := (β ω, X ω)) (hΓc _) (hω hωM)

omit [IsFiniteMeasure P] in
/-- **(Det) for drivers from the kernel side.** -/
theorem ae_driverCodeMatch_of_ae_isFlowLineDriver (hM : MeasurableSet M) (hβ : Measurable β) (hX : Measurable X)
    (hlaw : (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K) (hw : Measurable w)
    (hH : Measurable H) {WC : ℝ≥0 → S → ℝ} (hWC : ∀ t, Measurable (WC t)) {L : S → ℝ≥0∞} (hL : Measurable L)
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞} (hF : IsCanonicalDriverCode κ θ F)
    (hfl : ∀ᵐ c ∂(P.restrict M).map β, IsFlowLineDriver κ (w c).fn (w c).jumps θ (K c) H WC L) :
    ∀ᵐ ω ∂P, ω ∈ M → IsDriverCodeMatch (F (w (β ω), H (X ω))) (fun t => WC t (X ω)) (L (X ω)) := by
  set G : C × S → PCode × ℝ≥0∞ := fun p => F (w p.1, H p.2) with hGdef
  have hGm : Measurable G := hF.1.comp ((hw.comp measurable_fst).prodMk (hH.comp measurable_snd))
  have hE := measurableSet_driverCodeMatch hGm hWC hL
  exact ae_mem_of_ae_ae_compProd hM hβ hX hlaw hE (by
    filter_upwards [hfl] with c hc
    exact hF.2.2 (w c) (K c) H WC L hc)

end Kernel

/-! ### The restart kernel with canonical codes, and (Det) as an equivalence -/

section General

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {C S : Type} [MeasurableSpace C] [MeasurableSpace S] {M : Set Ω} {β : Ω → C} {X : Ω → S}
  {w : C → BoundaryWord} {H : S → DistOn upperHalfPlaneOpens} {ι : Type*} [Countable ι] {κ : ℝ}

/-- **The general restart kernel with canonical flow codes** (`restartKernel_isFlowLine_of_codeMatch` with the
corrected code predicate): (R1) and (Det) give, for every disintegrating Markov kernel, for almost every datum, the
GFF with the word and every continuation a flow line of the chart field. -/
theorem restartKernel_isFlowLine_of_codeMatch_canonical (h𝒢 : 𝒢 ≤ mΩ) (hM : MeasurableSet[𝒢] M)
    (hβ : Measurable[𝒢] β) (hw : Measurable w) (hX : Measurable X) (hH : Measurable H)
    (hsort : ∀ᵐ ω ∂P, ω ∈ M → (w (β ω)).IsSorted)
    (hR1 : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
      P[fun ω' => Complex.exp (Complex.I * (H (X ω') φ : ℂ)) | 𝒢] ω = gaussCF (w (β ω)) φ)
    {x : ι → C → ℝ} (hx : ∀ i, Measurable (x i)) {θ : ι → ℝ} {Γ : ι → S → ℝ≥0 → ℂ}
    (hΓ : ∀ i t, Measurable fun s => Γ i s t) {U : ι → S → ℝ≥0∞} (hU : ∀ i, Measurable (U i))
    (hΓc : ∀ i s, ContinuousOn (Γ i s) {t | (t : ℝ≥0∞) ≤ U i s})
    {F : ι → (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hF : ∀ i, IsCanonicalFlowCode κ (θ i) (F i))
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
    ae_isFlowLine_of_codeMatch_canonical hMm hβm hX hlaw hw (hx i) hH (hΓ i) (hU i) (hΓc i) (hF i) hgff (hdet i)
  filter_upwards [hgff, ae_all_iff.2 hfl] with c ⟨hcs, hcg⟩ hc
  exact ⟨hcs, hcg, hc⟩

/-- **The general restart kernel with canonical driver codes.** -/
theorem restartKernel_isFlowLineDriver_of_codeMatch_canonical (h𝒢 : 𝒢 ≤ mΩ) (hM : MeasurableSet[𝒢] M)
    (hβ : Measurable[𝒢] β) (hw : Measurable w) (hX : Measurable X) (hH : Measurable H)
    (hsort : ∀ᵐ ω ∂P, ω ∈ M → (w (β ω)).IsSorted)
    (hR1 : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
      P[fun ω' => Complex.exp (Complex.I * (H (X ω') φ : ℂ)) | 𝒢] ω = gaussCF (w (β ω)) φ)
    {θ : ι → ℝ} {WC : ι → ℝ≥0 → S → ℝ} (hWC : ∀ i t, Measurable (WC i t)) {L : ι → S → ℝ≥0∞}
    (hL : ∀ i, Measurable (L i)) (hWCc : ∀ i s, ContinuousOn (fun t => WC i t s) {t | (t : ℝ≥0∞) < L i s})
    {F : ι → BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hF : ∀ i, IsCanonicalDriverCode κ (θ i) (F i))
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
    ae_isFlowLineDriver_of_codeMatch_canonical hMm hβm hX hlaw hw hH (hWC i) (hL i) (hWCc i) (hF i) hgff (hdet i)
  filter_upwards [hgff, ae_all_iff.2 hfl] with c ⟨hcs, hcg⟩ hc
  exact ⟨hcs, hcg, hc⟩

/-- **(Det) is equivalent to the kernel conclusion.** Under (R1), for every disintegrating Markov kernel, (Det) for a
countable family of continuations with canonical flow codes holds iff under almost every kernel measure each
continuation is the flow line of the chart field. -/
theorem restartKernel_codeMatch_iff (h𝒢 : 𝒢 ≤ mΩ) (hM : MeasurableSet[𝒢] M)
    (hβ : Measurable[𝒢] β) (hw : Measurable w) (hX : Measurable X) (hH : Measurable H)
    (hsort : ∀ᵐ ω ∂P, ω ∈ M → (w (β ω)).IsSorted)
    (hR1 : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
      P[fun ω' => Complex.exp (Complex.I * (H (X ω') φ : ℂ)) | 𝒢] ω = gaussCF (w (β ω)) φ)
    {x : ι → C → ℝ} (hx : ∀ i, Measurable (x i)) {θ : ι → ℝ} {Γ : ι → S → ℝ≥0 → ℂ}
    (hΓ : ∀ i t, Measurable fun s => Γ i s t) {U : ι → S → ℝ≥0∞} (hU : ∀ i, Measurable (U i))
    (hΓc : ∀ i s, ContinuousOn (Γ i s) {t | (t : ℝ≥0∞) ≤ U i s})
    {F : ι → (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hF : ∀ i, IsCanonicalFlowCode κ (θ i) (F i))
    (K : Kernel C S) [IsMarkovKernel K]
    (hlaw : (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K) :
    (∀ i, ∀ᵐ ω ∂P, ω ∈ M →
      IsCodeMatch (F i ((w (β ω), x i (β ω)), H (X ω))) (Γ i (X ω)) (U i (X ω))) ↔
      ∀ᵐ c ∂(P.restrict M).map β, ∀ i, IsFlowLine κ (w c).fn (w c).jumps (x i c) (θ i) (K c) H (Γ i) (U i) := by
  have hβm : Measurable β := hβ.mono h𝒢 le_rfl
  have hMm : MeasurableSet M := h𝒢 _ hM
  constructor
  · intro hdet
    filter_upwards [restartKernel_isFlowLine_of_codeMatch_canonical h𝒢 hM hβ hw hX hH hsort hR1 hx hΓ hU hΓc hF
      hdet K hlaw] with c hc
    exact hc.2.2
  · intro hfl i
    exact ae_codeMatch_of_ae_isFlowLine hMm hβm hX hlaw hw (hx i) hH (hΓ i) (hU i) (hΓc i) (hF i)
      (hfl.mono fun c hc => hc i)

/-- **(Det) for drivers is equivalent to the kernel conclusion.** -/
theorem restartKernel_driverCodeMatch_iff (h𝒢 : 𝒢 ≤ mΩ) (hM : MeasurableSet[𝒢] M)
    (hβ : Measurable[𝒢] β) (hw : Measurable w) (hX : Measurable X) (hH : Measurable H)
    (hsort : ∀ᵐ ω ∂P, ω ∈ M → (w (β ω)).IsSorted)
    (hR1 : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
      P[fun ω' => Complex.exp (Complex.I * (H (X ω') φ : ℂ)) | 𝒢] ω = gaussCF (w (β ω)) φ)
    {θ : ι → ℝ} {WC : ι → ℝ≥0 → S → ℝ} (hWC : ∀ i t, Measurable (WC i t)) {L : ι → S → ℝ≥0∞}
    (hL : ∀ i, Measurable (L i)) (hWCc : ∀ i s, ContinuousOn (fun t => WC i t s) {t | (t : ℝ≥0∞) < L i s})
    {F : ι → BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hF : ∀ i, IsCanonicalDriverCode κ (θ i) (F i))
    (K : Kernel C S) [IsMarkovKernel K]
    (hlaw : (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K) :
    (∀ i, ∀ᵐ ω ∂P, ω ∈ M →
      IsDriverCodeMatch (F i (w (β ω), H (X ω))) (fun t => WC i t (X ω)) (L i (X ω))) ↔
      ∀ᵐ c ∂(P.restrict M).map β, ∀ i, IsFlowLineDriver κ (w c).fn (w c).jumps (θ i) (K c) H (WC i) (L i) := by
  have hβm : Measurable β := hβ.mono h𝒢 le_rfl
  have hMm : MeasurableSet M := h𝒢 _ hM
  constructor
  · intro hdet
    filter_upwards [restartKernel_isFlowLineDriver_of_codeMatch_canonical h𝒢 hM hβ hw hX hH hsort hR1 hWC hL
      hWCc hF hdet K hlaw] with c hc
    exact hc.2.2
  · intro hfl i
    exact ae_driverCodeMatch_of_ae_isFlowLineDriver hMm hβm hX hlaw hw hH (hWC i) (hL i) (hF i)
      (hfl.mono fun c hc => hc i)

end General

end Restart

end InteractingSLE
