import QuantumZipper.Proofs.Thm18.G1Z2ReflLeftB
import QuantumZipper.Proofs.Thm18.G1PkgLeft

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z2-REFL (3): `SideReflChordStmt` holds

From the left-normalized case (`sideReflGood_left_of_leftUniformizer`):

* every normalized uniformizer `φ₀` of the left component is `a⁻¹ φ` for a left-normalized `φ`
  and `a > 0` (`a = −1/b(−1)`, as in `G1Chord.leftUnifExistStmt`), so `φ₀⁻¹ = φ⁻¹ ∘ (a ·)` and the
  reflection data rescale (`sideReflGood_scale`);
* the right component is the reflection `z ↦ −z̄` of the left component of the reflected chord
  (`CA.Kernel.invFunOn_eq_refl`), and the reflection data reflect (`sideReflGood_refl`).

Own elementary bookkeeping.

Main result: **`sideReflChordStmt_holds : SideReflChordStmt`**.
-/

noncomputable section

open Set Metric Filter Topology Complex Function
open QuantumZipper.CA QuantumZipper.CA.Uniformizer QuantumZipper.CA.Kernel
open scoped ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm
namespace G1Z2

/-- A normalized uniformizer of the left component is a positive multiple of a left-normalized
one. -/
theorem exists_scale_leftUniformizer {η : ℝ → ℂ} (hη : IsSimpleChord η) {φ₀ : ℂ → ℂ}
    (hφ₀ : IsNormalizedUniformizer (leftComponent η) φ₀) :
    ∃ a : ℝ, 0 < a ∧ IsLeftUniformizer η (fun z => (a : ℂ) * φ₀ z) := by
  obtain ⟨b, hb, -, hb0⟩ := G1Chord.exists_boundary_values_normalized hη hφ₀
  have hc : b (-1) < 0 := G1Chord.boundary_neg_of_normalized hη hφ₀ hb hb0 (-1) (by norm_num)
  set a : ℝ := -1 / b (-1) with hadef
  have ha : 0 < a := div_pos_of_neg_of_neg (by norm_num) hc
  obtain ⟨hbij, hd, h0, hinf⟩ := hφ₀
  have hmul : BijOn (fun w : ℂ => (a : ℂ) * w) H H := by
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    refine ⟨fun w hw => G1.mul_mem_H ha hw, fun w _ w' _ h => mul_left_cancel₀ ha' h,
      fun w hw => ⟨((a⁻¹ : ℝ) : ℂ) * w, G1.mul_mem_H (inv_pos.2 ha) hw, ?_⟩⟩
    simp only
    rw [← mul_assoc, ← ofReal_mul, mul_inv_cancel₀ ha.ne', ofReal_one, one_mul]
  refine ⟨a, ha, ⟨hmul.comp hbij, (differentiableOn_const _).mul hd, ?_, ?_⟩, ?_⟩
  · simpa using h0.const_mul (a : ℂ)
  · have := Tendsto.const_mul_atTop ha hinf
    refine this.congr fun z => ?_
    simp only [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos ha]
  · have h1 := (hb (-1) (by norm_num)).const_mul (a : ℂ)
    have e : (a : ℂ) * (b (-1) : ℂ) = -1 := by
      rw [← ofReal_mul, hadef, div_mul_cancel₀ _ hc.ne]; simp
    rw [e] at h1
    simpa using h1

/-- `φ₀⁻¹ = (a φ₀)⁻¹ ∘ (a ·)` on `ℍ`. -/
theorem invFunOn_scale {D : Set ℂ} {φ₀ : ℂ → ℂ} {a : ℝ} (ha : 0 < a)
    (hb : BijOn (fun z => (a : ℂ) * φ₀ z) D H) (hb0 : BijOn φ₀ D H) :
    EqOn (invFunOn φ₀ D) (fun w => invFunOn (fun z => (a : ℂ) * φ₀ z) D ((a : ℂ) * w)) H := by
  intro w hw
  have h0 : ∃ z ∈ D, φ₀ z = w := hb0.surjOn hw
  have haw : (a : ℂ) * w ∈ H := G1.mul_mem_H ha hw
  have h1 : ∃ z ∈ D, (a : ℂ) * φ₀ z = (a : ℂ) * w := hb.surjOn haw
  refine hb.injOn (invFunOn_mem h0) (invFunOn_mem h1) ?_
  simp only
  rw [invFunOn_eq h0]
  exact (invFunOn_eq h1).symm

theorem mul_mem_g1SideHalf {a t : ℝ} (ha : 0 < a) {left : Bool} (ht : t ∈ g1SideHalf left) :
    a * t ∈ g1SideHalf left := by
  cases left
  · have : 0 < t := by simpa [g1SideHalf] using ht
    simpa [g1SideHalf] using mul_pos ha this
  · have : t < 0 := by simpa [g1SideHalf] using ht
    simpa [g1SideHalf] using mul_neg_of_pos_of_neg ha this

/-- Rescaling the reflection data. -/
theorem sideReflGood_scale {left : Bool} {ψ₀ ψ₁ : ℂ → ℂ} {Φ : ℝ ≃o ℝ} {a : ℝ} (ha : 0 < a)
    (h : SideReflGood left ψ₁ Φ) (heq : EqOn ψ₀ (fun w => ψ₁ ((a : ℂ) * w)) H) :
    SideReflGood left ψ₀ ((OrderIso.mulLeft₀ a ha).trans Φ) := by
  obtain ⟨h0, hwin⟩ := h
  refine ⟨by simp [h0], fun p q hpq hIcc => ?_⟩
  have hIcc' : Icc (a * p) (a * q) ⊆ g1SideHalf left := by
    intro s hs
    have hs' : s / a ∈ Icc p q := ⟨(le_div_iff₀ ha).2 (by linarith [hs.1]),
      (div_le_iff₀ ha).2 (by linarith [hs.2])⟩
    have := mul_mem_g1SideHalf ha (hIcc hs')
    rwa [mul_div_cancel₀ _ ha.ne'] at this
  obtain ⟨U, Ψ, hU, hJU, hΨ, hΨΦ, hder, hEq⟩ :=
    hwin (a * p) (a * q) (mul_lt_mul_of_pos_left hpq ha) hIcc'
  have hmem : ∀ t ∈ Icc p q, a * t ∈ Icc (a * p) (a * q) := fun t ht =>
    ⟨mul_le_mul_of_nonneg_left ht.1 ha.le, mul_le_mul_of_nonneg_left ht.2 ha.le⟩
  have hcast : ∀ t : ℝ, (a : ℂ) * (t : ℂ) = ((a * t : ℝ) : ℂ) := fun t => by push_cast; ring
  refine ⟨(fun z => (a : ℂ) * z) ⁻¹' U, fun z => Ψ ((a : ℂ) * z),
    hU.preimage (continuous_const.mul continuous_id), fun t ht => ?_, ?_, fun t ht => ?_,
    fun t ht => ?_, fun w hw => ?_⟩
  · show (a : ℂ) * (t : ℂ) ∈ U
    rw [hcast]; exact hJU _ (hmem t ht)
  · intro z hz
    exact ((hΨ.differentiableAt (hU.mem_nhds hz)).comp z
      ((differentiableAt_id).const_mul (a : ℂ))).differentiableWithinAt
  · show Ψ ((a : ℂ) * (t : ℂ)) = (((OrderIso.mulLeft₀ a ha).trans Φ) t : ℂ)
    rw [hcast, hΨΦ _ (hmem t ht)]
    rfl
  · have e : deriv (fun z => Ψ ((a : ℂ) * z)) (t : ℂ) = (a : ℂ) • deriv Ψ ((a : ℂ) * t) :=
      deriv_comp_mul_left (a : ℂ) Ψ (t : ℂ)
    rw [e, smul_eq_mul, hcast]
    exact mul_ne_zero (by exact_mod_cast ha.ne') (hder _ (hmem t ht))
  · rw [heq hw]
    exact hEq (G1.mul_mem_H ha hw)

/-- **Left side**, for every normalized uniformizer. -/
theorem sideReflGood_left {η : ℝ → ℂ} (hη : IsSimpleChord η) {φ₀ : ℂ → ℂ}
    (hφ₀ : IsNormalizedUniformizer (leftComponent η) φ₀) :
    ∃ Φ : ℝ ≃o ℝ, SideReflGood true (invFunOn φ₀ (leftComponent η)) Φ := by
  obtain ⟨a, ha, hφ⟩ := exists_scale_leftUniformizer hη hφ₀
  obtain ⟨Φ, hΦ⟩ := sideReflGood_left_of_leftUniformizer hη hφ
  exact ⟨_, sideReflGood_scale ha hΦ (invFunOn_scale ha hφ.1.1 hφ₀.1)⟩

/-- A normalized uniformizer of the right component, reflected, is a normalized uniformizer of the
left component of the reflected chord (the first part of `CA.Kernel.isLeftUniformizer_refl`). -/
theorem normalized_refl {η : ℝ → ℂ} (hη : IsSimpleChord η) {φ : ℂ → ℂ}
    (hφ : IsNormalizedUniformizer (rightComponent η) φ) :
    IsNormalizedUniformizer (leftComponent (refl ∘ η)) (fun z => refl (φ (refl z))) := by
  obtain ⟨hφb, hφd, hφ0, hφinf⟩ := hφ
  have hRo := isOpen_rightComponent_qz hη
  refine ⟨bijOn_refl_H.comp (hφb.comp (bijOn_refl_left η)), fun z hz => ?_, ?_, ?_⟩
  · have hz' := refl_mem_right_of_mem_left hz
    exact (differentiableAt_refl_comp_refl
      (hφd.differentiableAt (hRo.mem_nhds hz'))).differentiableWithinAt
  · have h0' : Tendsto refl (𝓝[leftComponent (refl ∘ η)] 0) (𝓝[rightComponent η] 0) := by
      simpa [Uniformizer.refl] using tendsto_refl_nhdsWithin_left η 0
    have h := (continuous_refl.tendsto 0).comp (hφ0.comp h0')
    simpa [Uniformizer.refl, Function.comp_def] using h
  · have h1 : Tendsto refl (Bornology.cobounded ℂ ⊓ 𝓟 (leftComponent (refl ∘ η)))
        (Bornology.cobounded ℂ ⊓ 𝓟 (rightComponent η)) := by
      refine tendsto_inf.2 ⟨?_, tendsto_principal.2 (eventually_inf_principal.2
        (Eventually.of_forall fun z hz => refl_mem_right_of_mem_left hz))⟩
      rw [← tendsto_norm_atTop_iff_cobounded]
      simpa using tendsto_norm_cobounded_atTop.mono_left
        (inf_le_left : Bornology.cobounded ℂ ⊓ 𝓟 (leftComponent (refl ∘ η)) ≤
          Bornology.cobounded ℂ)
    simpa [Function.comp_def] using hφinf.comp h1

/-- The reflected boundary map `t ↦ −Φ(−t)`. -/
def reflIso (Φ : ℝ ≃o ℝ) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (fun t => -Φ (-t))
    (fun x y hxy => neg_lt_neg (Φ.strictMono (neg_lt_neg hxy)))
    (fun y => ⟨-Φ.symm (-y), by simp⟩)

theorem reflIso_apply (Φ : ℝ ≃o ℝ) (t : ℝ) : reflIso Φ t = -Φ (-t) := rfl

/-- Reflecting the reflection data from the left to the right side. -/
theorem sideReflGood_refl {ψ ψ' : ℂ → ℂ} {Φ : ℝ ≃o ℝ} (h : SideReflGood true ψ' Φ)
    (heq : EqOn ψ (fun v => refl (ψ' (refl v))) H) : SideReflGood false ψ (reflIso Φ) := by
  obtain ⟨h0, hwin⟩ := h
  refine ⟨by simp [reflIso_apply, h0], fun p q hpq hIcc => ?_⟩
  have hpos : ∀ t ∈ Icc p q, 0 < t := fun t ht => by simpa [g1SideHalf] using hIcc ht
  have hmem : ∀ t ∈ Icc p q, -t ∈ Icc (-q) (-p) := fun t ht =>
    ⟨neg_le_neg ht.2, neg_le_neg ht.1⟩
  have hIcc' : Icc (-q) (-p) ⊆ g1SideHalf true := fun s hs => by
    have : 0 < -s := hpos (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
    simp [g1SideHalf]; linarith
  obtain ⟨U, Ψ, hU, hJU, hΨ, hΨΦ, hder, hEq⟩ := hwin (-q) (-p) (neg_lt_neg hpq) hIcc'
  have hrefl : ∀ t : ℝ, refl (t : ℂ) = ((-t : ℝ) : ℂ) := refl_ofReal
  refine ⟨refl ⁻¹' U, fun z => refl (Ψ (refl z)), hU.preimage continuous_refl,
    fun t ht => ?_, fun z hz => ?_, fun t ht => ?_, fun t ht => ?_, fun w hw => ?_⟩
  · show refl (t : ℂ) ∈ U
    rw [hrefl]; exact hJU _ (hmem t ht)
  · exact (differentiableAt_refl_comp_refl
      (hΨ.differentiableAt (hU.mem_nhds hz))).differentiableWithinAt
  · show refl (Ψ (refl (t : ℂ))) = ((reflIso Φ t : ℝ) : ℂ)
    rw [hrefl, hΨΦ _ (hmem t ht), hrefl, reflIso_apply]
  · have hU' : refl (t : ℂ) ∈ U := by rw [hrefl]; exact hJU _ (hmem t ht)
    have hd : HasDerivAt Ψ (deriv Ψ (refl (t : ℂ))) (-(conj (t : ℂ))) :=
      (hΨ.differentiableAt (hU.mem_nhds hU')).hasDerivAt
    have hg : HasDerivAt (fun u => -Ψ (-u)) (-(deriv Ψ (refl (t : ℂ)) * -1)) (conj (t : ℂ)) :=
      (hd.comp (conj (t : ℂ)) (hasDerivAt_neg (conj (t : ℂ)))).neg
    have hc := hg.conj_conj
    rw [Complex.conj_conj] at hc
    have hfun : (conj ∘ (fun u => -Ψ (-u)) ∘ conj) = fun z => refl (Ψ (refl z)) := by
      funext z; simp [Uniformizer.refl]
    rw [hfun] at hc
    rw [hc.deriv]
    have hne := hder _ (hmem t ht)
    rw [← hrefl] at hne
    simpa using hne
  · rw [heq hw]
    exact congrArg refl (hEq (refl_mem_H_iff.2 hw))

/-- **`SideReflChordStmt` holds.** -/
theorem sideReflChordStmt_holds : SideReflChordStmt := by
  intro η hη left φ hφ
  cases left
  · change IsNormalizedUniformizer (rightComponent η) φ at hφ
    change ∃ Φ : ℝ ≃o ℝ, SideReflGood false (invFunOn φ (rightComponent η)) Φ
    obtain ⟨Φ, hΦ⟩ := sideReflGood_left (isSimpleChord_refl_comp hη) (normalized_refl hη hφ)
    exact ⟨_, sideReflGood_refl hΦ fun v hv => invFunOn_eq_refl hφ.1 hv⟩
  · change IsNormalizedUniformizer (leftComponent η) φ at hφ
    exact sideReflGood_left hη hφ

end G1Z2
end Thm18Asm
end QuantumZipper
