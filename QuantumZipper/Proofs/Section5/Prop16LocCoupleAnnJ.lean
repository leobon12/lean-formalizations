import QuantumZipper.Proofs.Section5.Prop16LocCoupleAnnNodes
import QuantumZipper.Proofs.GFF.K3.MixedM7Gram

/-!
# DOM-a by annulus features (decision D34), AN5 part 1: the isometry `J`, the vectors `e μ`

* `exists_annJ`: the linear isometry `J : annulusSpan D S →ₗᵢ HkE` with `J a_i = â_i`, valued in
  `freeAnnSpan D S` (from AN1 and `K3.exists_linearIsometry_closure_of_gram`);
* `annE J μ = (J (P_M v_μ), remVec D S μ) ∈ WithLp 2 (HkE × GradSpace D)` and its Gram matrix
  `inner_annE = dualCov` (`K3.dualCov_mixed_eq_Qann_add`);
* `annulusPot_eq_zero_of_not_mem_closure`: the annulus potentials of local annuli vanish on
  `Hbar \ closure D`;
* `integral_annulusPot_eq_kernelCov`, `inner_freeVec_sub_annFree`: the free pairing of a
  balanced pair with a free annulus feature;
* `sub_annJ_mem_orthogonal`: `v̂_μ − v̂_{ρ₀} − J (P_M v_μ) ⊥ freeAnnSpan D S` when `ρ₀` lives on
  `Hbar \ closure D` (so `P_{M̂} (v̂_μ − v̂_{ρ₀}) = J (P_M v_μ)`).

Own elementary arguments from the proved identities of `MixedProj.lean`, `MixedM6Pre.lean` and
AN1 (`Prop16LocCoupleAnn.lean`).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace ComplexConjugate

namespace QuantumZipper

namespace Prop16Asm

open GFFExist K3 KernelId CircleMV

variable {D S : Set ℂ}

/-- The mixed annulus features, indexed by the local annuli. -/
def annMixed (D S : Set ℂ) (i : AnnIdx D S) : GradSpace D :=
  annulusFeat D i.1.1 i.1.2.1 i.1.2.2.1

/-- The free annulus features, indexed by the local annuli. -/
def annFree (D S : Set ℂ) (i : AnnIdx D S) : HkE :=
  freeAnnFeat i.1.1 i.1.2.1 i.1.2.2.1

theorem annulusSet_eq_range_an : annulusSet D S = Set.range (annMixed D S) := by
  ext v
  constructor
  · rintro ⟨z, s, s', R0, hloc, hs, hss', hs'R, rfl⟩
    exact ⟨⟨(z, s, s', R0), hloc, hs, hss', hs'R⟩, rfl⟩
  · rintro ⟨⟨⟨z, s, s', R0⟩, hloc, hs, hss', hs'R⟩, rfl⟩
    exact ⟨z, s, s', R0, hloc, hs, hss', hs'R, rfl⟩

theorem annulusSpan_eq_an :
    annulusSpan D S = (Submodule.span ℝ (Set.range (annMixed D S))).topologicalClosure := by
  rw [annulusSpan, annulusSet_eq_range_an]

theorem annMixed_mem (i : AnnIdx D S) : annMixed D S i ∈ annulusSpan D S :=
  annulusFeat_mem_annulusSpan i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2

theorem annFree_mem (i : AnnIdx D S) : annFree D S i ∈ freeAnnSpan D S :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The standing hypotheses of the annulus construction. -/
structure AnnGeom (D S : Set ℂ) : Prop where
  isOpen : IsOpen D
  subset_H : D ⊆ H
  bounded : Bornology.IsBounded D
  free_real : S ⊆ {z : ℂ | z.im = 0}
  pos : ∃ g ∈ mixedSpace D S, 0 < dirichletEnergyOn D g

/-- **The isometry `J` of the annulus spans** (AN1 + Gram extension). -/
theorem exists_annJ (h : AnnGeom D S) :
    ∃ J : annulusSpan D S →ₗᵢ[ℝ] HkE,
      (∀ i, J ⟨annMixed D S i, annMixed_mem i⟩ = annFree D S i) ∧
        ∀ x, J x ∈ freeAnnSpan D S := by
  have hG : ∀ i j, ⟪annMixed D S i, annMixed D S j⟫ = ⟪annFree D S i, annFree D S j⟫ :=
    fun i j => (inner_freeAnnFeat h.isOpen h.subset_H h.bounded h.free_real h.pos i.2.1 i.2.2.1
      i.2.2.2.1 i.2.2.2.2 j.2.1 j.2.2.1 j.2.2.2.1 j.2.2.2.2).symm
  obtain ⟨J₀, hJ₀, hJr⟩ := exists_linearIsometry_closure_of_gram (annMixed D S) (annFree D S) hG
  refine ⟨J₀.comp (LinearIsometryEquiv.ofEq _ _ annulusSpan_eq_an).toLinearIsometry,
    fun i => ?_, fun x => hJr _⟩
  have e : (LinearIsometryEquiv.ofEq _ _ annulusSpan_eq_an) ⟨annMixed D S i, annMixed_mem i⟩ =
      ⟨annMixed D S i, Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)⟩ :=
    Subtype.ext rfl
  show J₀ ((LinearIsometryEquiv.ofEq _ _ annulusSpan_eq_an) ⟨annMixed D S i, annMixed_mem i⟩) = _
  rw [e]
  exact hJ₀ i

/-- The projection onto the mixed annulus span, as an element of the span. -/
def annP (D S : Set ℂ) (v : GradSpace D) : annulusSpan D S :=
  ⟨(annulusSpan D S).starProjection v, (annulusSpan D S).starProjection_apply_mem v⟩

/-- **The mixed vectors of the construction:** `e μ = (J (P_M v_μ), remVec D S μ)`. -/
def annE (J : annulusSpan D S →ₗᵢ[ℝ] HkE) (μ : Measure ℂ) : WithLp 2 (HkE × GradSpace D) :=
  WithLp.toLp 2 (J (annP D S (rieszVec D (mixedSpace D S) μ)), remVec D S μ)

/-- **Gram matrix of `e`:** the mixed covariance. -/
theorem inner_annE (J : annulusSpan D S →ₗᵢ[ℝ] HkE) {μ ν : Measure ℂ}
    (hμ : IsAdmissibleDual D (mixedSpace D S) μ) (hν : IsAdmissibleDual D (mixedSpace D S) ν) :
    ⟪annE J μ, annE J ν⟫ = dualCov D (mixedSpace D S) μ ν := by
  rw [dualCov_mixed_eq_Qann_add hμ hν, annE, annE, WithLp.prod_inner_apply]
  simp only [LinearIsometry.inner_map_map]
  rfl

/-- `annProfile s s' u = 0` for `u ≥ s'²`. -/
theorem annProfile_eq_zero_of_le {s s' u : ℝ} (hu : s' ^ 2 ≤ u) : annProfile s s' u = 0 := by
  unfold annProfile
  refine integral_annIntegrand_zero fun t ht htI => ?_
  rw [uIcc_of_le hu] at ht
  exact absurd htI.2 (not_lt.2 ht.1)

/-- For `x, z ∈ Hbar`, `‖x − z‖ ≤ ‖x − conj z‖`. -/
theorem norm_sub_le_norm_sub_conj_an {x z : ℂ} (hx : x ∈ Hbar) (hz : z ∈ Hbar) :
    ‖x - z‖ ≤ ‖x - conj z‖ := by
  have hx' : 0 ≤ x.im := hx
  have hz' : 0 ≤ z.im := hz
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  nlinarith [mul_nonneg hx' hz']

/-- **The annulus potentials of local annuli vanish on `Hbar \ closure D`.** -/
theorem annulusPot_eq_zero_of_not_mem_closure (i : AnnIdx D S) {x : ℂ} (hx : x ∈ Hbar)
    (hxD : x ∉ closure D) : annulusPot i.1.1 i.1.2.1 i.1.2.2.1 x = 0 := by
  obtain ⟨⟨z, s, s', R0⟩, hloc, hs, hss', hs'R⟩ := i
  have hz : z ∈ Hbar := hloc.1
  have hfar : s' < ‖x - z‖ := by
    by_contra hle'
    have hle := not_lt.1 hle'
    exact hxD (hloc.2.2.2.1 ⟨by rw [mem_closedBall, dist_eq_norm]; linarith, hx⟩)
  have h1 : s' ^ 2 ≤ ‖x - z‖ ^ 2 := by nlinarith [hs.trans hss']
  have h2 : s' ^ 2 ≤ ‖x - conj z‖ ^ 2 := h1.trans (by
    have := norm_sub_le_norm_sub_conj_an hx hz
    nlinarith [norm_nonneg (x - z)])
  simp only [annulusPot, annProfile_eq_zero_of_le h1, annProfile_eq_zero_of_le h2, add_zero]

/-- The integral of an annulus potential against a finite measure carried by a compact set, as
free covariances with the two folded circles. -/
theorem integral_annulusPot_eq_kernelCov {μ : Measure ℂ} [IsFiniteMeasure μ] {K : Set ℂ}
    (hK : IsCompact K) (hμK : μ Kᶜ = 0) {z : ℂ} {s s' : ℝ} (hs : 0 < s) (hss' : s < s') :
    ∫ x, annulusPot z s s' x ∂μ =
      kernelCov neumannH μ (foldedCircle z s) - kernelCov neumannH μ (foldedCircle z s') := by
  simp_rw [annulusPot_eq_fcPot_sub hs hss']
  rw [integral_sub
    (integrable_of_continuousOn_carrier hK (continuous_fcPot hs z).continuousOn hμK)
    (integrable_of_continuousOn_carrier hK (continuous_fcPot (hs.trans hss') z).continuousOn hμK)]
  unfold kernelCov
  simp_rw [integral_neumannH_foldedCircle_right' z _ hs,
    integral_neumannH_foldedCircle_right' z _ (hs.trans hss')]

/-- **Free pairing of a balanced pair with a free annulus feature.** -/
theorem inner_freeVec_sub_annFree (i : AnnIdx D S) (μ ρ : AdmT) (hm : μ.1 univ = ρ.1 univ)
    {K L : Set ℂ} (hK : IsCompact K) (hμK : μ.1 Kᶜ = 0) (hL : IsCompact L) (hρL : ρ.1 Lᶜ = 0) :
    ⟪freeVec μ - freeVec ρ, annFree D S i⟫ =
      (∫ x, annulusPot i.1.1 i.1.2.1 i.1.2.2.1 x ∂μ.1) -
        ∫ x, annulusPot i.1.1 i.1.2.1 i.1.2.2.1 x ∂ρ.1 := by
  obtain ⟨⟨z, s, s', R0⟩, hloc, hs, hss', hs'R⟩ := i
  have hz : z ∈ Hbar := hloc.1
  have := μ.2.1
  have := ρ.2.1
  simp only [annFree]
  rw [freeAnnFeat_eq hz hs (hs.trans hss'), freeVec_inner _ _ _ _ hm
      (by simp only [measure_univ]),
    integral_annulusPot_eq_kernelCov hK hμK hs hss', integral_annulusPot_eq_kernelCov hL hρL hs hss']
  simp only [kernelCov2]
  ring

/-- **`v̂_μ − v̂_{ρ₀} − J (P_M v_μ)` is orthogonal to the free annulus span**, for `μ` admissible for
both fields and `ρ₀` of the same mass carried by a compact subset of `Hbar \ closure D`. -/
theorem sub_annJ_mem_orthogonal (h : AnnGeom D S) {J : annulusSpan D S →ₗᵢ[ℝ] HkE}
    (hJ : ∀ i, J ⟨annMixed D S i, annMixed_mem i⟩ = annFree D S i) (μ ρ₀ : AdmT)
    (hμD : IsAdmissibleDual D (mixedSpace D S) μ.1) (hm : μ.1 univ = ρ₀.1 univ)
    {K L : Set ℂ} (hK : IsCompact K) (hμK : μ.1 Kᶜ = 0) (hL : IsCompact L) (hρL : ρ₀.1 Lᶜ = 0)
    (hLD : L ⊆ Hbar \ closure D) :
    freeVec μ - freeVec ρ₀ - J (annP D S (rieszVec D (mixedSpace D S) μ.1)) ∈
      (freeAnnSpan D S)ᗮ := by
  set y := freeVec μ - freeVec ρ₀ - J (annP D S (rieszVec D (mixedSpace D S) μ.1)) with hy
  have hgen : ∀ i : AnnIdx D S, ⟪annFree D S i, y⟫ = 0 := by
    intro i
    have := ρ₀.2.1
    have hρ0 : ∫ x, annulusPot i.1.1 i.1.2.1 i.1.2.2.1 x ∂ρ₀.1 = 0 := by
      refine integral_eq_zero_of_ae ?_
      have hae : ∀ᵐ x ∂ρ₀.1, x ∈ L := mem_ae_iff.2 hρL
      filter_upwards [hae] with x hx
      exact annulusPot_eq_zero_of_not_mem_closure i (hLD hx).1 (hLD hx).2
    have hmix : ⟪J (annP D S (rieszVec D (mixedSpace D S) μ.1)), annFree D S i⟫ =
        ∫ x, annulusPot i.1.1 i.1.2.1 i.1.2.2.1 x ∂μ.1 := by
      rw [← hJ i, LinearIsometry.inner_map_map]
      obtain ⟨⟨z, s, s', R0⟩, hloc, hs, hss', hs'R⟩ := i
      have hz' : LocalBall D S z s' := hloc.mono hloc.1 (hs.trans hss') (by rw [dist_self]; linarith)
      show ⟪(annulusSpan D S).starProjection (rieszVec D (mixedSpace D S) μ.1),
        annulusFeat D z s s'⟫ = _
      rw [(annulusSpan D S).inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.2 (annulusFeat_mem_annulusSpan hloc hs hss' hs'R),
        inner_rieszVec_annulusFeat h.bounded h.pos hμD hz' hs hss']
    rw [real_inner_comm, hy, inner_sub_left, inner_freeVec_sub_annFree i μ ρ₀ hm hK hμK hL hρL,
      hρ0, hmix]
    ring
  rw [Submodule.mem_orthogonal]
  intro u hu
  have hle : Submodule.span ℝ (Set.range (annFree D S)) ≤ (ℝ ∙ y)ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.2 (hgen i)
  have hu' := Submodule.topologicalClosure_minimal _ hle (Submodule.isClosed_orthogonal _) hu
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 hu'

end Prop16Asm

end QuantumZipper
