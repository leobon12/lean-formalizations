import QuantumZipper.Proofs.GFF.CoordRegCompMeas

/-!
# RC3 composition law for the zipped fields `Y_t` (RC-COMP; targets (R1), (R2) of E1-PLAN)

For `0 ≤ t ≤ T`, a Brownian motion `B` independent of the free field `X`, the zipped field
`Y_t = coordChange (𝔥₀ + X) (fwdMapInv W (T−t)) Q` (`B2.Yf`) and `V = B2.Vr κ T B`:

* **(R1)** `ae_evalReg_Yf_fc`: for every dyadic index `i` (every folded circle, including those
  touching or crossing `ℝ`), a.s. `evalReg Y_t (fc_i.map (revMap V t)) = Y_t (fc_i.map (revMap V t))`;
* **(R2)** `ae_evalReg_Yf_compact`: the same at `ϖ.map (revMap V t)` for a probability measure
  `ϖ` carried by a compact subset of `ℍ` with a Frostman bound of positive exponent.

Proof: `CoordRegComp.ae_evalReg_comp_fc` / `ae_evalReg_comp_compact` (RC3-general applied to the
pushed measure) for every continuous path of `B` on `[0,T]`, Fubini over the independent pair
(path, field) (`ae_lhsC_eq_rhsC_random`), and the pathwise identification of the drivers
(`fwdMapInv W (T−t) = revMap V₁ (T−t)` on `ℍ`, `V = W(T−·) − W T` on `[0,t]`).

Sources: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1 (through RC3-general);
Sheffield arXiv:1012.4797 §5.2, pp. 57–59. The reduction is an own argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Real Topology

namespace QuantumZipper
namespace CoordRegComp

open CoordReg CharFun B2

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T t : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

omit [IsProbabilityMeasure P] in
/-- The fixed-driver law, read on the paths `revPath` of one path on `[0,T]`. -/
theorem hfix_of_law (hT : 0 ≤ T) (ht : 0 ≤ t) (hs : 0 ≤ T - t) (htT : t ≤ T) {μ : Measure ℂ}
    (hlaw : ∀ Vf V A : ℝ → ℝ, Continuous Vf → Continuous V → Continuous A →
      EqOn Vf V (Icc 0 t) → (∀ r ∈ Icc (0 : ℝ) (T - t), Vf (t + r) - Vf t = A r) →
      ∀ᵐ ω ∂P, evalReg (coordChange (ofFun (h0rev κ) + X ω) (revMap A (T - t))
          (Qc (Real.sqrt κ))) (μ.map (revMap V t)) =
        coordChange (ofFun (h0rev κ) + X ω) (revMap A (T - t)) (Qc (Real.sqrt κ))
          (μ.map (revMap V t)))
    (f : C(Icc (0 : ℝ) T, ℝ)) :
    ∀ᵐ ω ∂P, lhsC κ hT ht hs (h0rev κ) (Qc (Real.sqrt κ)) μ (f, X ω) =
      rhsC κ hT ht hs (h0rev κ) (Qc (Real.sqrt κ)) μ (f, X ω) := by
  unfold lhsC rhsC
  refine hlaw (Wof κ T hT (revPath hT T T f)) (Wof κ t ht (revPath hT T t f))
    (Wof κ (T - t) hs (revPath hT (T - t) (T - t) f)) (continuous_Wof κ T hT (revPath hT T T f))
    (continuous_Wof κ t ht (revPath hT T t f))
    (continuous_Wof κ (T - t) hs (revPath hT (T - t) (T - t) f)) (fun r hr => ?_) (fun r hr => ?_)
  · rw [Wof_revPath κ hT hT T f ⟨hr.1, hr.2.trans htT⟩, Wof_revPath κ hT ht T f hr]
  · rw [Wof_revPath κ hT hT T f ⟨by linarith [hr.1], by linarith [hr.2]⟩,
      Wof_revPath κ hT hT T f ⟨ht, htT⟩, Wof_revPath κ hT hs (T - t) f hr,
      show T - (t + r) = T - t - r by ring]
    ring

/-- **Composition law for `Y_t`, general pushed measure.** -/
theorem ae_evalReg_Yf_push (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (ht : 0 ≤ t) (htT : t ≤ T) {μ : Measure ℂ}
    [IsProbabilityMeasure μ] (hμH : ∀ᵐ z ∂μ, z ∈ H)
    (hlaw : ∀ Vf V A : ℝ → ℝ, Continuous Vf → Continuous V → Continuous A →
      EqOn Vf V (Icc 0 t) → (∀ r ∈ Icc (0 : ℝ) (T - t), Vf (t + r) - Vf t = A r) →
      ∀ᵐ ω ∂P, evalReg (coordChange (ofFun (h0rev κ) + X ω) (revMap A (T - t))
          (Qc (Real.sqrt κ))) (μ.map (revMap V t)) =
        coordChange (ofFun (h0rev κ) + X ω) (revMap A (T - t)) (Qc (Real.sqrt κ))
          (μ.map (revMap V t))) :
    ∀ᵐ ω ∂P, evalReg (Yf κ T t B X ω) (μ.map (revMap (Vr κ T B ω) t)) =
      Yf κ T t B X ω (μ.map (revMap (Vr κ T B ω) t)) := by
  have hT : 0 ≤ T := ht.trans htT
  have hs : 0 ≤ T - t := sub_nonneg.2 htT
  obtain ⟨B₁, hB₁m, hB₁c, hB₁eq⟩ := exists_good_version hB
  have hind₁ : IndepFun (pathOf B₁) X P :=
    hind.congr (hB₁eq.mono fun ω h => (funext fun s => (h s).symm : pathOf B ω = pathOf B₁ ω))
      (ae_eq_refl _)
  have hr := ae_lhsC_eq_rhsC_random κ hT ht hs (h0rev κ) (Qc (Real.sqrt κ)) μ hX hμH
    (measurable_pathC T hB₁m hB₁c) (indepFun_pathC T hind₁ hB₁c)
    (hfix_of_law hT ht hs htT hlaw)
  filter_upwards [hr, hB₁eq, hB.eval_zero_ae_eq_zero] with ω h h1 h0
  set f := pathC T B₁ hB₁c ω with hf
  have hPj : ∀ x (hx : x ∈ Icc (0 : ℝ) T), f (projIcc 0 T hT x) = B x.toNNReal ω := by
    intro x hx
    rw [projIcc_of_mem hT hx]
    exact h1 _
  have hcB : Continuous fun s => B s ω := by
    have : (fun s => B s ω) = fun s => B₁ s ω := funext fun s => (h1 s).symm
    rw [this]; exact hB₁c ω
  have hW : Continuous (drive κ B ω) := continuous_const.mul (hcB.comp continuous_real_toNNReal)
  have hW0 : drive κ B ω 0 = 0 := by
    have : B 0 ω = 0 := h0
    simp [drive, this]
  have hFeq : revMap (Vr κ T B ω) t = revMap (Wof κ t ht (revPath hT T t f)) t :=
    funext fun z => ReverseFlow.revMap_congr_drive z fun r hr => by
      rw [Wof_revPath κ hT ht T f hr, Vr, vrev_of_mem ⟨hr.1, hr.2.trans htT⟩,
        hPj _ ⟨by linarith [hr.2], by linarith [hr.1]⟩, hPj _ ⟨hT, le_rfl⟩]
      simp only [drive]; ring
  have hEq : EqOn (fwdMapInv (drive κ B ω) (T - t))
      (revMap (Wof κ (T - t) hs (revPath hT (T - t) (T - t) f)) (T - t)) H := fun z hz => by
    rw [eqOn_fwdMapInv hW hW0 hs hz]
    exact ReverseFlow.revMap_congr_drive z fun r hr => by
      show drive κ B ω (T - t - r) - drive κ B ω (T - t) = _
      rw [Wof_revPath κ hT hs (T - t) f hr, hPj _ ⟨by linarith [hr.2], by linarith [hr.1]⟩,
        hPj _ ⟨hs, by linarith⟩]
      simp only [drive]; ring
  have hνH : ∀ᵐ z ∂(μ.map (revMap (Wof κ t ht (revPath hT T t f)) t)), z ∈ H :=
    (ae_map_iff (TwoPoint.measurable_revMap (continuous_Wof κ t ht _) ht).aemeasurable
      isOpen_H.measurableSet).2
      (hμH.mono fun z hz => TwoPoint.im_revMap_pos (continuous_Wof κ t ht _) hz ht)
  rw [hFeq, show Yf κ T t B X ω = coordChange (ofFun (h0rev κ) + X ω)
      (fwdMapInv (drive κ B ω) (T - t)) (Qc (Real.sqrt κ)) by rw [Yf_eq_unzippedField]; rfl,
    evalReg_coordChange_congr _ hEq, coordChange_congr_of_eqOn_H _ hEq _ hνH]
  exact h

/-- **(R1)** RC3 composition law at every dyadic folded circle (arbitrary centre, positive
radius; circles touching or crossing `ℝ` included). -/
theorem ae_evalReg_Yf_fc (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (ht : 0 ≤ t) (htT : t ≤ T) :
    ∀ i : ℕ, ∀ᵐ ω ∂P, evalReg (Yf κ T t B X ω)
        ((foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2).map
          (revMap (Vr κ T B ω) t)) =
      Yf κ T t B X ω ((foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2).map
        (revMap (Vr κ T B ω) t)) := by
  intro i
  have hr := UnzipFull.fullIndex_radius_pos i
  refine ae_evalReg_Yf_push hB hX hind ht htT (TwoPoint.foldedCircle_ae_mem_H _ hr)
    fun Vf V A hVf hV hA hVV hAV => ?_
  rw [h0rev_eq_logAdd κ]
  exact ae_evalReg_comp_fc hX (2 / Real.sqrt κ) continuous_const _ hVf hV hA ht
    (sub_nonneg.2 htT) hVV hAV _ hr

/-- **(R2)** RC3 composition law at the image of a compactly supported Frostman probability
measure. -/
theorem ae_evalReg_Yf_compact (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (ht : 0 ≤ t) (htT : t ≤ T) {ϖ : Measure ℂ}
    [IsProbabilityMeasure ϖ] {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) (hϖ : ϖ Kᶜ = 0)
    {α C : ℝ} (hFϖ : IsFrostman ϖ α C) (hα : 0 < α) :
    ∀ᵐ ω ∂P, evalReg (Yf κ T t B X ω) (ϖ.map (revMap (Vr κ T B ω) t)) =
      Yf κ T t B X ω (ϖ.map (revMap (Vr κ T B ω) t)) := by
  refine ae_evalReg_Yf_push hB hX hind ht htT ((ae_iff.2 hϖ).mono fun z hz => hKH hz)
    fun Vf V A hVf hV hA hVV hAV => ?_
  rw [h0rev_eq_logAdd κ]
  exact ae_evalReg_comp_compact hX (2 / Real.sqrt κ) continuous_const _ hVf hV hA ht
    (sub_nonneg.2 htT) hVV hAV hK hKH hϖ hFϖ hα

end CoordRegComp
end QuantumZipper
