import QuantumZipper.Proofs.Complex.KernelChordStatement
import QuantumZipper.Proofs.Complex.UniformizerRight

/-!
# KT2 for the right component (D7: `φ(1) = 1`), from the left version

`chordKernelTheoremRight_of_left`: the right-component version of KT2 follows from the left one
by the reflection `refl z = −conj z` (`UniformizerRight.lean`): `rightComponent η =
refl '' leftComponent (refl ∘ η)`, and `φ` is right-normalized for `η` iff `refl ∘ φ ∘ refl` is
left-normalized for `refl ∘ η`; `refl` is an isometry of `ℂ` and of the chordal metric. This
symmetry argument is Sheffield's "by symmetry" (§5.4) and our own elementary transport.
-/

noncomputable section

open Set Metric Filter Topology Complex Function Bornology
open QuantumZipper.CA.Uniformizer

namespace QuantumZipper.CA.Kernel

/-- `φ` is the right-normalized uniformizer of `η` (D7): normalized, with `φ(1) = 1`. -/
def IsRightUniformizer (η : ℝ → ℂ) (φ : ℂ → ℂ) : Prop :=
  IsNormalizedUniformizer (rightComponent η) φ ∧
    Tendsto φ (𝓝[rightComponent η] 1) (𝓝 1)

/-- **KT2, right component** (D7). -/
def ChordKernelTheoremRight : Prop :=
  ∀ (η : ℕ → ℝ → ℂ) (ηi : ℝ → ℂ) (φ : ℕ → ℂ → ℂ) (φi : ℂ → ℂ),
    (∀ n, IsSimpleChord (η n)) → IsSimpleChord ηi → SphereUniformConv η ηi →
    (∀ n, IsRightUniformizer (η n) (φ n)) → IsRightUniformizer ηi φi →
    TendstoLocallyUniformlyOn (fun n => invFunOn (φ n) (rightComponent (η n)))
        (invFunOn φi (rightComponent ηi)) atTop H ∧
      ∀ K : Set ℂ, IsCompact K → K ⊆ rightComponent ηi →
        (∀ᶠ n in atTop, K ⊆ rightComponent (η n)) ∧ TendstoUniformlyOn φ φi atTop K

theorem bijOn_refl_left (η : ℝ → ℂ) :
    BijOn refl (leftComponent (refl ∘ η)) (rightComponent η) :=
  ⟨fun _ hz => refl_mem_right_of_mem_left hz, refl_injective.injOn,
    fun z hz => ⟨refl z, mem_rightComponent_iff.1 hz, refl_refl z⟩⟩

theorem isOpen_rightComponent_qz {η : ℝ → ℂ} (hη : IsSimpleChord η) :
    IsOpen (rightComponent η) := by
  have : rightComponent η = refl ⁻¹' leftComponent (refl ∘ η) := by
    ext z; exact mem_rightComponent_iff
  rw [this]
  exact (isOpen_leftComponent (isSimpleChord_refl_comp hη)).preimage continuous_refl

theorem tendsto_refl_nhdsWithin_left (η : ℝ → ℂ) (a : ℂ) :
    Tendsto refl (𝓝[leftComponent (refl ∘ η)] a) (𝓝[rightComponent η] (refl a)) :=
  tendsto_nhdsWithin_iff.2 ⟨(continuous_refl.tendsto a).mono_left nhdsWithin_le_nhds,
    eventually_mem_nhdsWithin.mono fun _ hz => refl_mem_right_of_mem_left hz⟩

theorem isLeftUniformizer_refl {η : ℝ → ℂ} (hη : IsSimpleChord η) {φ : ℂ → ℂ}
    (hφ : IsRightUniformizer η φ) :
    IsLeftUniformizer (refl ∘ η) (fun z => refl (φ (refl z))) := by
  obtain ⟨⟨hφb, hφd, hφ0, hφinf⟩, hφ1⟩ := hφ
  have hRo := isOpen_rightComponent_qz hη
  refine ⟨⟨bijOn_refl_H.comp (hφb.comp (bijOn_refl_left η)), fun z hz => ?_, ?_, ?_⟩, ?_⟩
  · have hz' := refl_mem_right_of_mem_left hz
    exact (differentiableAt_refl_comp_refl
      (hφd.differentiableAt (hRo.mem_nhds hz'))).differentiableWithinAt
  · have h0' : Tendsto refl (𝓝[leftComponent (refl ∘ η)] 0) (𝓝[rightComponent η] 0) := by
      simpa [Uniformizer.refl] using tendsto_refl_nhdsWithin_left η 0
    have h := (continuous_refl.tendsto 0).comp (hφ0.comp h0')
    simpa [Uniformizer.refl, Function.comp_def] using h
  · have h1 : Tendsto refl (cobounded ℂ ⊓ 𝓟 (leftComponent (refl ∘ η)))
        (cobounded ℂ ⊓ 𝓟 (rightComponent η)) := by
      refine tendsto_inf.2 ⟨?_, tendsto_principal.2 (eventually_inf_principal.2
        (Eventually.of_forall fun z hz => refl_mem_right_of_mem_left hz))⟩
      rw [← tendsto_norm_atTop_iff_cobounded]
      simpa using tendsto_norm_cobounded_atTop.mono_left
        (inf_le_left : cobounded ℂ ⊓ 𝓟 (leftComponent (refl ∘ η)) ≤ cobounded ℂ)
    simpa [Function.comp_def] using hφinf.comp h1
  · have h1' : Tendsto refl (𝓝[leftComponent (refl ∘ η)] (-1)) (𝓝[rightComponent η] 1) := by
      simpa [Uniformizer.refl] using tendsto_refl_nhdsWithin_left η (-1)
    have h := (continuous_refl.tendsto 1).comp (hφ1.comp h1')
    simpa [Uniformizer.refl, Function.comp_def] using h

theorem chordalDist_refl (z w : ℂ) : chordalDist (refl z) (refl w) = chordalDist z w := by
  have : refl z - refl w = refl (z - w) := by simp [Uniformizer.refl]; ring
  simp only [chordalDist, this, norm_refl]

theorem sphereUniformConv_refl {η : ℕ → ℝ → ℂ} {ηi : ℝ → ℂ} (h : SphereUniformConv η ηi) :
    SphereUniformConv (fun n => refl ∘ η n) (refl ∘ ηi) := fun ε hε => by
  filter_upwards [h ε hε] with n hn t ht
  simpa [chordalDist_refl] using hn t ht

/-- The inverse of `φ` is the reflected inverse of `refl ∘ φ ∘ refl`. -/
theorem invFunOn_eq_refl {η : ℝ → ℂ} {φ : ℂ → ℂ}
    (hφb : BijOn φ (rightComponent η) H) {v : ℂ} (hv : v ∈ H) :
    invFunOn φ (rightComponent η) v =
      refl (invFunOn (fun z => refl (φ (refl z))) (leftComponent (refl ∘ η)) (refl v)) := by
  have hb' : BijOn (fun z => refl (φ (refl z))) (leftComponent (refl ∘ η)) H :=
    bijOn_refl_H.comp (hφb.comp (bijOn_refl_left η))
  have h1 : ∃ z ∈ rightComponent η, φ z = v := hφb.surjOn hv
  have h2 : ∃ z ∈ leftComponent (refl ∘ η), refl (φ (refl z)) = refl v :=
    hb'.surjOn (refl_mem_H_iff.2 hv)
  have hm := invFunOn_mem h2
  have he := invFunOn_eq h2
  apply hφb.injOn (invFunOn_mem h1) (refl_mem_right_of_mem_left hm)
  rw [invFunOn_eq h1]
  exact refl_injective he.symm

/-- **KT2 for the right component**, from KT2 for the left component. -/
theorem chordKernelTheoremRight_of_left (hL : ChordKernelTheoremLeft) :
    ChordKernelTheoremRight := by
  intro η ηi φ φi hη hηi hconv hφ hφi
  have hL' := hL (fun n => refl ∘ η n) (refl ∘ ηi) (fun n z => refl (φ n (refl z)))
    (fun z => refl (φi (refl z))) (fun n => isSimpleChord_refl_comp (hη n))
    (isSimpleChord_refl_comp hηi) (sphereUniformConv_refl hconv)
    (fun n => isLeftUniformizer_refl (hη n) (hφ n)) (isLeftUniformizer_refl hηi hφi)
  obtain ⟨h1, h2⟩ := hL'
  have hucr : UniformContinuous refl := by
    refine Isometry.uniformContinuous fun z w => ?_
    rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
    have : refl z - refl w = refl (z - w) := by simp [Uniformizer.refl]; ring
    rw [this, norm_refl]
  refine ⟨?_, fun K hKc hKR => ?_⟩
  · have h := hucr.comp_tendstoLocallyUniformlyOn
      (h1.comp refl (fun v hv => refl_mem_H_iff.2 hv) continuous_refl.continuousOn)
    refine (h.congr fun n v hv => ?_).congr_right fun v hv => ?_
    · simp only [comp_apply]
      exact (invFunOn_eq_refl (hφ n).1.1 hv).symm
    · simp only [comp_apply]
      exact (invFunOn_eq_refl hφi.1.1 hv).symm
  · have hK' : refl '' K ⊆ leftComponent (refl ∘ ηi) := by
      rintro _ ⟨z, hz, rfl⟩; exact mem_rightComponent_iff.1 (hKR hz)
    obtain ⟨hev, hU⟩ := h2 (refl '' K) (hKc.image continuous_refl) hK'
    refine ⟨?_, ?_⟩
    · filter_upwards [hev] with n hn z hz
      exact mem_rightComponent_iff.2 (hn ⟨z, hz, rfl⟩)
    · have h := hucr.comp_tendstoUniformlyOn ((hU.comp refl).mono fun z hz =>
        (⟨z, hz, rfl⟩ : refl z ∈ refl '' K))
      simpa [Function.comp_def] using h

end QuantumZipper.CA.Kernel
