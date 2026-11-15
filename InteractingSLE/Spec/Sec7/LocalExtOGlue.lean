/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma72CLocal
import InteractingSLE.Spec.Sec7.LocalExtOTilt

/-!
# Gluing conditional local-set decompositions over countably many pieces

Packet PROVE-LOCEXT-O. At a restart the locality of the restarted hulls is first obtained on countably many disjoint
pieces `E n` of the cell (the pieces of an announcing sequence of the lifetime, and of the energy of the restart word's
source), each with its own conditioning σ-algebra `𝒢 n ∋ E n`. This file glues them on the sample space itself:

* `pieceSigma`: the σ-algebra of the measurable events whose trace on every piece `E n` lies in `𝒢 n`;
* `pieceGlue`: a function equal to `f n` on `E n`, and `measurable_pieceGlue`;
* **`isCondZeroBoundaryGFF_pieceSigma`**: conditional zero-boundary laws given `𝒢 n` under every `Q[· | E n]` glue to
  the conditional law given `pieceSigma` under `Q` (when the pieces cover `Q`-almost everything);
* **`isLocalSet_of_pieces`**: hence `IsLocalSet` (`Lemma72C.isLocalSet_of_isCondZeroBoundaryGFF`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Function
open scoped ENNReal NNReal

namespace InteractingSLE

namespace LocalExt

open QuantumZipper LQGMetric LocalSets

section Pieces

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {E : ℕ → Set Ω} {𝒢 : ℕ → MeasurableSpace Ω}

/-- **The piecewise σ-algebra**: measurable events whose trace on each piece `E n` is an event of `𝒢 n`. -/
@[instance_reducible]
def pieceSigma (hE : ∀ n, MeasurableSet[𝒢 n] (E n)) : MeasurableSpace Ω where
  MeasurableSet' S := MeasurableSet[mΩ] S ∧ ∀ n, MeasurableSet[𝒢 n] (S ∩ E n)
  measurableSet_empty := ⟨MeasurableSet.empty, fun n => by
    rw [empty_inter]; exact @MeasurableSet.empty _ (𝒢 n)⟩
  measurableSet_compl S hS := ⟨hS.1.compl, fun n => by
    have e : Sᶜ ∩ E n = E n \ (S ∩ E n) := by ext ω; simp [and_comm]
    rw [e]
    exact (hE n).diff (hS.2 n)⟩
  measurableSet_iUnion f hf := ⟨MeasurableSet.iUnion fun i => (hf i).1, fun n => by
    rw [iUnion_inter]
    exact MeasurableSet.iUnion fun i => (hf i).2 n⟩

theorem pieceSigma_le (hE : ∀ n, MeasurableSet[𝒢 n] (E n)) : pieceSigma hE ≤ mΩ := fun _ hS => hS.1

theorem measurableSet_pieceSigma_iff (hE : ∀ n, MeasurableSet[𝒢 n] (E n)) {S : Set Ω} :
    MeasurableSet[pieceSigma hE] S ↔ MeasurableSet S ∧ ∀ n, MeasurableSet[𝒢 n] (S ∩ E n) := Iff.rfl

open Classical in
/-- **A function glued from the pieces**: `f n` on `E n`, and `d` off their union. -/
def pieceGlue {β : Type*} (E : ℕ → Set Ω) (f : ℕ → Ω → β) (d : β) (ω : Ω) : β :=
  if h : ∃ n, ω ∈ E n then f (Nat.find h) ω else d

omit mΩ in
theorem pieceGlue_of_mem {β : Type*} (hdisj : Pairwise (Disjoint on E)) (f : ℕ → Ω → β) (d : β) {n : ℕ} {ω : Ω}
    (hω : ω ∈ E n) : pieceGlue E f d ω = f n ω := by
  classical
  have h : ∃ n, ω ∈ E n := ⟨n, hω⟩
  have hn : Nat.find h = n := by
    by_contra hne
    exact Set.disjoint_left.1 (hdisj hne) (Nat.find_spec h) hω
  unfold pieceGlue
  split_ifs
  rw [hn]

omit mΩ in
theorem pieceGlue_of_notMem {β : Type*} (f : ℕ → Ω → β) (d : β) {ω : Ω} (hω : ∀ n, ω ∉ E n) :
    pieceGlue E f d ω = d := by
  classical
  unfold pieceGlue
  split_ifs with h
  · obtain ⟨n, hn⟩ := h
    exact absurd hn (hω n)
  · rfl

/-- **The glued function is measurable for the piecewise σ-algebra.** -/
theorem measurable_pieceGlue {β : Type*} [MeasurableSpace β] (hE : ∀ n, MeasurableSet[𝒢 n] (E n))
    (h𝒢 : ∀ n, 𝒢 n ≤ mΩ) (hdisj : Pairwise (Disjoint on E)) {f : ℕ → Ω → β}
    (hf : ∀ n, Measurable[𝒢 n] (f n)) (d : β) :
    Measurable[pieceSigma hE] (pieceGlue E f d) := by
  intro S hS
  have hpre : ∀ n, pieceGlue E f d ⁻¹' S ∩ E n = f n ⁻¹' S ∩ E n := fun n => by
    ext ω
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩; rw [pieceGlue_of_mem hdisj f d h2] at h1; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; rw [pieceGlue_of_mem hdisj f d h2]; exact ⟨h1, h2⟩
  have hEm : ∀ n, MeasurableSet (E n) := fun n => h𝒢 n _ (hE n)
  refine ⟨?_, fun n => by rw [hpre n]; exact (hf n hS).inter (hE n)⟩
  have e : pieceGlue E f d ⁻¹' S = (⋃ n, f n ⁻¹' S ∩ E n) ∪ ({ω | d ∈ S} ∩ (⋃ n, E n)ᶜ) := by
    ext ω
    simp only [mem_preimage, mem_union, mem_iUnion, mem_inter_iff, mem_compl_iff, mem_ofPred_eq]
    by_cases hω : ∃ n, ω ∈ E n
    · obtain ⟨n, hn⟩ := hω
      rw [pieceGlue_of_mem hdisj f d hn]
      constructor
      · intro h; exact Or.inl ⟨n, h, hn⟩
      · rintro (⟨m, h1, h2⟩ | ⟨-, h3⟩)
        · rwa [← pieceGlue_of_mem hdisj f d h2, pieceGlue_of_mem hdisj f d hn] at h1
        · exact absurd ⟨n, hn⟩ h3
    · simp only [not_exists] at hω
      rw [pieceGlue_of_notMem f d hω]
      constructor
      · intro h; exact Or.inr ⟨h, by simp only [not_exists]; exact hω⟩
      · rintro (⟨m, -, h2⟩ | ⟨h, -⟩)
        · exact absurd h2 (hω m)
        · exact h
  rw [e]
  refine (MeasurableSet.iUnion fun n => ((hf n).mono (h𝒢 n) le_rfl hS).inter (hEm n)).union ?_
  exact (MeasurableSet.const _).inter (MeasurableSet.iUnion hEm).compl

/-- An `𝒢 n`-measurable function on every piece, globally measurable, is measurable for the piecewise σ-algebra. -/
theorem measurable_pieceSigma_of_eqOn {β : Type*} [MeasurableSpace β] (hE : ∀ n, MeasurableSet[𝒢 n] (E n))
    {f : Ω → β} (hf : Measurable f) {g : ℕ → Ω → β} (hg : ∀ n, Measurable[𝒢 n] (g n))
    (hfg : ∀ n, ∀ ω ∈ E n, f ω = g n ω) : Measurable[pieceSigma hE] f := by
  intro S hS
  refine ⟨hf hS, fun n => ?_⟩
  have e : f ⁻¹' S ∩ E n = g n ⁻¹' S ∩ E n := by
    ext ω
    simp only [mem_inter_iff, mem_preimage]
    exact ⟨fun ⟨h1, h2⟩ => ⟨hfg n ω h2 ▸ h1, h2⟩, fun ⟨h1, h2⟩ => ⟨(hfg n ω h2).symm ▸ h1, h2⟩⟩
  rw [e]
  exact (hg n hS).inter (hE n)

end Pieces

/-! ### Gluing conditional zero-boundary laws -/

section Glue

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {E : ℕ → Set Ω} {𝒢 : ℕ → MeasurableSpace Ω}

/-- Set integrals over an event of a piece under the conditioned measure. -/
theorem setIntegral_cond_of_subset {Q : Measure Ω} {F : Set Ω} {T : Set Ω} (hT : MeasurableSet T) (hTF : T ⊆ F) (f : Ω → ℂ) :
    ∫ ω in T, f ω ∂(Q[|F]) = (Q F)⁻¹.toReal • ∫ ω in T, f ω ∂Q := by
  rw [ProbabilityTheory.cond, Measure.restrict_smul, integral_smul_measure, Measure.restrict_restrict hT,
    inter_eq_left.2 hTF]

/-- **Gluing.** If the pieces `E n` (disjoint, `E n ∈ 𝒢 n`) cover `Q`-almost everything and, under every `Q[· | E n]`
of positive mass, `X` is conditionally a zero-boundary GFF on `U` given `𝒢 n`, then `X` is conditionally a
zero-boundary GFF on `U` given the piecewise σ-algebra under `Q` (the variances being measurable for it). -/
theorem isCondZeroBoundaryGFF_pieceSigma {Q : Measure Ω} [IsFiniteMeasure Q]
    (hE : ∀ n, MeasurableSet[𝒢 n] (E n)) (h𝒢 : ∀ n, 𝒢 n ≤ mΩ) (hdisj : Pairwise (Disjoint on E))
    (hcov : Q (⋃ n, E n)ᶜ = 0) {U : Ω → Set ℂ} (hUo : ∀ ω, IsOpen (U ω) ∧ U ω ⊆ H)
    {X : Ω → DistOn upperHalfPlaneOpens} (hX : Measurable X)
    (hU : ∀ φ : TestOn upperHalfPlaneOpens, Measurable[pieceSigma hE] fun ω => zeroGFFTestCov (U ω) φ φ)
    (hpiece : ∀ n, Q (E n) ≠ 0 → IsCondZeroBoundaryGFF (Q[|E n]) (𝒢 n) U X) :
    IsCondZeroBoundaryGFF Q (pieceSigma hE) U X := by
  intro φ
  have hEm : ∀ n, MeasurableSet (E n) := fun n => h𝒢 n _ (hE n)
  set F : Ω → ℂ := fun ω => Complex.exp (Complex.I * (X ω φ : ℂ)) with hFdef
  set c' : Ω → ℂ := fun ω => ((Real.exp (-(1 / 2) * zeroGFFTestCov (U ω) φ φ) : ℝ) : ℂ) with hc'def
  have hFm : Measurable F := GFF.measurable_exp_I_mul ((measurable_distOn_apply φ).comp hX)
  have hFb : ∀ ω, ‖F ω‖ ≤ 1 := fun ω => (norm_cexp_I_mul _).le
  have hc'm : StronglyMeasurable[pieceSigma hE] c' :=
    (Complex.measurable_ofReal.comp (Real.measurable_exp.comp ((hU φ).const_mul _))).stronglyMeasurable
  have hc'b : ∀ ω, ‖c' ω‖ ≤ 1 := fun ω => by
    rw [hc'def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have := zeroGFFTestCov_self_nonneg (hUo ω).1 (hUo ω).2 φ
    nlinarith
  have hc'mΩ : Measurable c' := hc'm.measurable.mono (pieceSigma_le hE) le_rfl
  have hint : ∀ μ : Measure Ω, IsFiniteMeasure μ → Integrable F μ ∧ Integrable c' μ := fun μ _ =>
    ⟨Integrable.of_bound hFm.aestronglyMeasurable 1 (Eventually.of_forall hFb),
      Integrable.of_bound hc'mΩ.aestronglyMeasurable 1 (Eventually.of_forall hc'b)⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (pieceSigma_le hE) (hint Q inferInstance).1
    (fun S _ _ => (hint Q inferInstance).2.integrableOn) ?_ hc'm.aestronglyMeasurable).symm
  intro S hS _
  have hSm : MeasurableSet S := hS.1
  -- piece by piece
  have hp : ∀ n, ∫ ω in S ∩ E n, c' ω ∂Q = ∫ ω in S ∩ E n, F ω ∂Q := by
    intro n
    by_cases hn : Q (E n) = 0
    · have h0 : Q (S ∩ E n) = 0 := measure_mono_null inter_subset_right hn
      rw [setIntegral_measure_zero _ h0, setIntegral_measure_zero _ h0]
    · have hfin : IsFiniteMeasure (Q[|E n]) := inferInstance
      have hc := hpiece n hn φ
      have hT : MeasurableSet[𝒢 n] (S ∩ E n) := hS.2 n
      have h1 := setIntegral_condExp (h𝒢 n) (hint _ hfin).1 hT
      have h2 : ∫ ω in S ∩ E n, (Q[|E n])[F | 𝒢 n] ω ∂(Q[|E n]) = ∫ ω in S ∩ E n, c' ω ∂(Q[|E n]) :=
        setIntegral_congr_ae (h𝒢 n _ hT) (hc.mono fun ω hω _ => hω)
      have h3 := h1.symm.trans h2
      rw [setIntegral_cond_of_subset (hSm.inter (hEm n)) inter_subset_right,
        setIntegral_cond_of_subset (hSm.inter (hEm n)) inter_subset_right] at h3
      have hne : (Q (E n))⁻¹.toReal ≠ 0 :=
        ENNReal.toReal_ne_zero.2 ⟨ENNReal.inv_ne_zero.2 (measure_ne_top Q _), ENNReal.inv_ne_top.2 hn⟩
      exact (smul_right_injective ℂ hne h3).symm
  -- the union of the pieces
  have hSU : S =ᵐ[Q] ⋃ n, S ∩ E n := by
    refine ae_eq_set.2 ⟨measure_mono_null (fun ω hω => ?_) hcov, ?_⟩
    · simp only [Set.mem_sdiff, mem_iUnion, mem_inter_iff, not_exists, not_and] at hω
      simp only [mem_compl_iff, mem_iUnion, not_exists]
      exact fun n hn => hω.2 n hω.1 hn
    · rw [sdiff_eq_empty.2 (iUnion_subset fun n => inter_subset_left), measure_empty]
  have hdisj' : Pairwise (Disjoint on fun n => S ∩ E n) := fun m n hmn =>
    (hdisj hmn).mono inter_subset_right inter_subset_right
  rw [setIntegral_congr_set hSU, setIntegral_congr_set hSU,
    integral_iUnion (fun n => hSm.inter (hEm n)) hdisj' (hint Q inferInstance).2.integrableOn,
    integral_iUnion (fun n => hSm.inter (hEm n)) hdisj' (hint Q inferInstance).1.integrableOn]
  exact tsum_congr hp

/-- **Locality from pieces.** On the sample space itself: a relatively closed random set `A` and a part `h₁`, both
measurable for the piecewise σ-algebra, `h₁` harmonic off `A`, and on every piece of positive mass `h − h₁` conditionally
a zero-boundary GFF on `ℍ ∖ A` given `𝒢 n` under `Q[· | E n]`; then `A` is a local set of `h` under `Q`. -/
theorem isLocalSet_of_pieces {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hE : ∀ n, MeasurableSet[𝒢 n] (E n)) (h𝒢 : ∀ n, 𝒢 n ≤ mΩ) (hdisj : Pairwise (Disjoint on E))
    (hcov : Q (⋃ n, E n)ᶜ = 0) {A : Ω → Set ℂ} (hA : Measurable[pieceSigma hE, hittingSigma] A)
    (hAc : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) {h h₁ : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (hh₁ : Measurable[pieceSigma hE] h₁) (hharm : ∀ᵐ ω ∂Q, IsHarmonicDistOn (h₁ ω) (H \ A ω))
    (hpiece : ∀ n, Q (E n) ≠ 0 →
      IsCondZeroBoundaryGFF (Q[|E n]) (𝒢 n) (fun ω => H \ A ω) (fun ω => h ω - h₁ ω)) :
    IsLocalSet A h Q := by
  have hh₁m : Measurable h₁ := hh₁.mono (pieceSigma_le hE) le_rfl
  have hXm : Measurable fun ω => h ω - h₁ ω := measurable_distOn_iff.2 fun φ =>
    ((measurable_distOn_apply φ).comp hh).sub ((measurable_distOn_apply φ).comp hh₁m)
  have hU : ∀ φ : TestOn upperHalfPlaneOpens,
      Measurable[pieceSigma hE] fun ω => zeroGFFTestCov (H \ A ω) φ φ := fun φ =>
    measurable_zeroGFFTestCov_compl_random hA hAc (ψ₁ := fun _ => φ) (ψ₂ := fun _ => φ)
      (fun _ => measurable_const) (fun _ => measurable_const)
  exact Sec7.Lemma72C.isLocalSet_of_isCondZeroBoundaryGFF (pieceSigma_le hE) hA hh hh₁ (ae_of_all _ hAc) hharm
    (isCondZeroBoundaryGFF_pieceSigma hE h𝒢 hdisj hcov (fun ω => ⟨(hAc ω).2, sdiff_subset⟩) hXm hU hpiece)

end Glue

end LocalExt

end InteractingSLE
