import QuantumZipper.Proofs.Zipper.UnifUOPlusRefl
import QuantumZipper.Proofs.Zipper.UnifUOMain

/-!
# UNIF-UO (plus side): `UnifOffTipPlusStmt` by reflection

Task UO-PLUS (decision D26). `RegUnif.UnifOffTipPlusStmt` (windows `0 < u` of the time-`s`
picture) is obtained from the minus side `RegUnif.ae_offTip_minus` by reflecting the coupling
`(B, X) ↦ (−B, X ∘ refl)` in the real axis:

* **reflection invariance of the free field** (`isFreeGFFModConstH_reflRaw`): the reflected field
  `X'(ω)(μ) = X ω (μ.map (z ↦ −z̄))` is again a free GFF modulo constants, because `neumannH` is
  invariant under `z ↦ −z̄` (`neumannH_neg_conj`) and admissibility, mass and the covariance
  kernel are preserved (`isAdmissibleH_map_negConj`, `map_negConj_univ`,
  `kernelCov_neumannH_map_negConj`); the proof is that of
  `S5.FieldLaw.Raw.isFreeGFFModConstH_translate` with `z ↦ z + t` replaced by `z ↦ −z̄`.
* `−B` is Brownian (mathlib `IsBrownianReal.neg`) and independent of `X'`
  (`indepFun_neg_reflRaw`: independence is preserved by composing the two sides with the
  measurable maps `W ↦ −W` and `reflRaw`).
* **the pathwise identity** (`avgReg_unzippedField_reflRaw_neg_real`, file `UnifUOPlusRefl`):
  the regularized averages of the time-`s` picture of the reflected pair at a real point `t` are
  those of the original pair at `−t`; hence `bdryApprox` of the reflected pair is the pushforward
  of `bdryApprox` of the original by `t ↦ −t` at the level of test integrals
  (`integral_bdryApprox_neg`), and a vague limit on a window maps to a vague limit on the
  mirrored window (`isVagueLimitOnR_map_neg`).

The reflected pair needs its own `AnchorUnifFamExtStmt` (AC-fam-ext), taken as a hypothesis in
the same form as in `UnifUOMain.lean`. All reductions are own bookkeeping; the analytic input is
the stated hypothesis.

Sheffield, arXiv:1012.4797, §5.4 p. 72 ("by symmetry").
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace RegUnif

open B2 B5 E1 E1.M4

/-- The reflected driver `−B`. -/
def negB {Ω : Type} (B : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := fun t ω => -(B t ω)

/-- The reflected field `X ∘ refl`. -/
def reflX {Ω : Type} (X : Ω → FieldSample) : Ω → FieldSample := fun ω => reflRaw (X ω)

theorem drive_negB (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    drive κ (negB B) ω = -drive κ B ω := by
  funext t
  simp [drive, negB]

variable {Ω : Type} [MeasurableSpace Ω]

/-! ## 1. Reflection invariance of the free field -/

theorem neumannH_neg_conj (u v : ℂ) : neumannH (-conj u) (-conj v) = neumannH u v := by
  have h1 : (-conj u) - (-conj v) = -conj (u - v) := by
    simp only [map_sub]
    ring
  have h2 : (-conj u) - conj (-conj v) = -conj (u - conj v) := by
    simp only [map_sub, map_neg]
    ring
  have e1 : ‖-conj (u - v)‖ = ‖u - v‖ := by rw [norm_neg, Complex.norm_conj]
  have e2 : ‖-conj (u - conj v)‖ = ‖u - conj v‖ := by rw [norm_neg, Complex.norm_conj]
  rw [neumannH, neumannH, h1, h2, e1, e2]

theorem isAdmissibleH_map_negConj {μ : Measure ℂ} (hμ : IsAdmissibleH μ) :
    IsAdmissibleH (μ.map fun z => -conj z) := by
  obtain ⟨K, hK, hKH, hμK⟩ := hμ.2.1
  refine isAdmissibleH_map hμ hK hμK measurable_negConj
    (Complex.continuous_conj.neg.continuousOn) ?_ one_pos fun a ha b hb => ?_
  · rintro _ ⟨z, hz, rfl⟩
    show 0 ≤ (-conj z).im
    simpa using (show 0 ≤ z.im from hKH hz)
  · rw [one_mul, show (-conj a) - (-conj b) = -conj (a - b) by
      simp only [map_sub]
      ring, norm_neg, Complex.norm_conj]

theorem map_negConj_univ (μ : Measure ℂ) :
    (μ.map fun z => -conj z) univ = μ univ := by
  rw [Measure.map_apply measurable_negConj MeasurableSet.univ, preimage_univ]

theorem kernelCov_neumannH_map_negConj (μ ν : Measure ℂ) :
    kernelCov neumannH (μ.map fun z => -conj z) (ν.map fun z => -conj z) =
      kernelCov neumannH μ ν := by
  unfold kernelCov
  have e : (fun z : ℂ => -conj z) = ⇑F1.negConjEquiv := rfl
  rw [e, integral_map_equiv]
  congr 1
  funext a
  rw [integral_map_equiv]
  congr 1
  funext b
  exact neumannH_neg_conj a b

/-- **Reflection invariance** of the free boundary GFF modulo constants under `z ↦ −z̄`
(proof of `S5.FieldLaw.Raw.isFreeGFFModConstH_translate`, with the translation replaced by the
reflection). -/
theorem isFreeGFFModConstH_reflRaw {X : Ω → FieldSample} {P : Measure Ω}
    (hX : IsFreeGFFModConstH X P) :
    IsFreeGFFModConstH (fun ω (μ : Measure ℂ) => X ω (μ.map fun z => -conj z)) P where
  measurable_coord := fun μ => hX.measurable_coord _
  gaussian := by
    let f : {p : Measure ℂ × Measure ℂ //
          IsAdmissibleH p.1 ∧ IsAdmissibleH p.2 ∧ p.1 Set.univ = p.2 Set.univ} →
        {p : Measure ℂ × Measure ℂ //
          IsAdmissibleH p.1 ∧ IsAdmissibleH p.2 ∧ p.1 Set.univ = p.2 Set.univ} :=
      fun p => ⟨(p.1.1.map (fun z => -conj z), p.1.2.map (fun z => -conj z)),
        isAdmissibleH_map_negConj p.2.1, isAdmissibleH_map_negConj p.2.2.1, by
          rw [map_negConj_univ, map_negConj_univ]; exact p.2.2.2⟩
    exact hX.gaussian.comp_right f
  centered := fun μ ν hμ hν h => hX.centered _ _ (isAdmissibleH_map_negConj hμ)
    (isAdmissibleH_map_negConj hν) (by rw [map_negConj_univ, map_negConj_univ, h])
  covariance_eq := fun p q hp1 hp2 hp hq1 hq2 hq => by
    have h := hX.covariance_eq (p.1.map fun z => -conj z, p.2.map fun z => -conj z)
      (q.1.map fun z => -conj z, q.2.map fun z => -conj z) (isAdmissibleH_map_negConj hp1)
      (isAdmissibleH_map_negConj hp2) (by rw [map_negConj_univ, map_negConj_univ, hp])
      (isAdmissibleH_map_negConj hq1) (isAdmissibleH_map_negConj hq2)
      (by rw [map_negConj_univ, map_negConj_univ, hq])
    refine h.trans ?_
    simp only [kernelCov2, kernelCov_neumannH_map_negConj]
  linear := fun μ ν hμ hν a b => by
    have h := hX.linear _ _ (isAdmissibleH_map_negConj hμ) (isAdmissibleH_map_negConj hν) a b
    refine Filter.EventuallyEq.trans (Eventually.of_forall fun ω => ?_) h
    show X ω ((a • μ + b • ν).map fun z => -conj z) =
      X ω (a • μ.map (fun z => -conj z) + b • ν.map (fun z => -conj z))
    rw [Measure.map_add _ _ measurable_negConj, Measure.map_smul, Measure.map_smul]
    all_goals exact measurable_negConj.aemeasurable

/-- Independence of the reflected pair. -/
theorem indepFun_neg_reflRaw {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {P : Measure Ω}
    (hind : IndepFun (pathOf B) X P) :
    IndepFun (pathOf (negB B)) (reflX X) P := by
  have h := hind.comp (φ := fun W : ℝ≥0 → ℝ => -W) (ψ := reflRaw) measurable_neg measurable_reflRaw
  rwa [show (fun W : ℝ≥0 → ℝ => -W) ∘ pathOf B = pathOf (negB B) from rfl,
    show reflRaw ∘ X = reflX X from rfl] at h

/-! ## 2. Boundary measures under reflection -/

theorem measurable_bdryDens (γ : ℝ) (x : FieldSample) (k : ℕ) :
    Measurable fun t : ℝ => radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg x k (t : ℂ)) := by
  have hm : Measurable fun t : ℝ => avgReg x k ((t : ℝ) : ℂ) :=
    (RegClosure.measurable_avgReg_slice x k).comp Complex.continuous_ofReal.measurable
  exact ((hm.const_mul (γ / 2)).exp).const_mul _

/-- Change of variables `t ↦ −t` for integrals against Lebesgue measure on `ℝ`. -/
theorem integral_neg_eq_self_volume {F : ℝ → ℝ} (hF : AEStronglyMeasurable F (volume : Measure ℝ)) :
    ∫ t, F (-t) ∂(volume : Measure ℝ) = ∫ t, F t ∂volume := by
  have hm : AEStronglyMeasurable F ((volume : Measure ℝ).map fun t => -t) := by
    rwa [Measure.map_neg_eq_self (volume : Measure ℝ)]
  rw [← integral_map (φ := fun t : ℝ => -t) measurable_neg.aemeasurable hm,
    Measure.map_neg_eq_self (volume : Measure ℝ)]

/-- **Test integrals of `bdryApprox` under reflection.** -/
theorem integral_bdryApprox_neg {γ : ℝ} {x x' : FieldSample} (k : ℕ)
    (havg : ∀ t : ℝ, avgReg x' k (t : ℂ) = avgReg x k ((-t : ℝ) : ℂ)) (g : ℝ → ℝ)
    (hg : Continuous g) :
    ∫ t, g t ∂bdryApprox γ x k = ∫ t, g (-t) ∂bdryApprox γ x' k := by
  have hd : Measurable fun t : ℝ => radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg x k (t : ℂ)) :=
    measurable_bdryDens γ x k
  have hd' : Measurable fun t : ℝ =>
      radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg x' k (t : ℂ)) :=
    measurable_bdryDens γ x' k
  have h0 : ∀ t : ℝ, 0 ≤ radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg x k (t : ℂ)) :=
    fun t => mul_nonneg (Real.rpow_nonneg (radius_pos k).le _) (Real.exp_pos _).le
  have h0' : ∀ t : ℝ, 0 ≤ radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg x' k (t : ℂ)) :=
    fun t => mul_nonneg (Real.rpow_nonneg (radius_pos k).le _) (Real.exp_pos _).le
  rw [bdryApprox, bdryApprox,
    GoodSample.integral_withDensity_ofReal hd h0 g,
    GoodSample.integral_withDensity_ofReal hd' h0' fun t => g (-t)]
  have hpt : ∀ t : ℝ,
      radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg x k (t : ℂ)) * g t =
      (fun u : ℝ => radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg x' k (u : ℂ)) * g (-u)) (-t) :=
    fun t => by
      rw [show γ / 2 * avgReg x k (t : ℂ) = γ / 2 * avgReg x' k (((-t : ℝ)) : ℂ) from by
        rw [havg (-t)]; ring_nf]
      ring
  refine (integral_congr_ae (ae_of_all _ hpt)).trans ?_
  have hFm : Measurable fun u : ℝ => radius k ^ (γ ^ 2 / 4) *
      Real.exp (γ / 2 * avgReg x' k (u : ℂ)) * g (-u) :=
    hd'.mul (hg.comp continuous_neg).measurable
  exact integral_neg_eq_self_volume (F := fun u : ℝ => radius k ^ (γ ^ 2 / 4) *
      Real.exp (γ / 2 * avgReg x' k (u : ℂ)) * g (-u)) hFm.aestronglyMeasurable

/-- The topological support of `t ↦ g (−t)` is squeezed by the one of `g`. -/
theorem tsupport_comp_neg_subset {g : ℝ → ℝ} :
    tsupport (fun t : ℝ => g (-t)) ⊆ (fun t : ℝ => -t) ⁻¹' tsupport g :=
  closure_minimal (fun x hx => subset_tsupport g (by simpa using hx))
    ((isClosed_tsupport g).preimage continuous_neg)

/-- **Vague limits push forward under `t ↦ −t`.** If `ν` is the local vague limit of the
approximations of `x'` on the window `(−b, −a)`, and the regularized averages of `x'` and `x`
are related by reflection, then `ν.map (t ↦ −t)` is the local vague limit of the approximations
of `x` on `(a, b)`. -/
theorem isVagueLimitOnR_map_neg {γ : ℝ} {x x' : FieldSample} {a b : ℝ} {ν : Measure ℝ}
    (havg : ∀ k : ℕ, ∀ t : ℝ, avgReg x' k (t : ℂ) = avgReg x k ((-t : ℝ) : ℂ))
    (h : IsVagueLimitOnR (Ioo (-b) (-a)) (bdryApprox γ x') ν) :
    IsVagueLimitOnR (Ioo a b) (bdryApprox γ x) (ν.map fun t : ℝ => -t) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · have hpre : (fun t : ℝ => -t) ⁻¹' Ioo a b = Ioo (-b) (-a) := by
      ext t
      simp only [mem_preimage, mem_Ioo]
      constructor <;> intro h <;> exact ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [Measure.map_apply measurable_neg measurableSet_Ioo.compl, Set.preimage_compl, hpre]
    exact h1
  · intro K hK hKV
    have hpre : (fun t : ℝ => -t) ⁻¹' K = (fun t : ℝ => -t) '' K := by
      ext t
      constructor
      · intro ht
        exact ⟨-t, by simpa using ht, by simp⟩
      · rintro ⟨u, hu, rfl⟩
        simpa using hu
    rw [Measure.map_apply measurable_neg hK.measurableSet, hpre]
    refine h2 _ (hK.image continuous_neg) ?_
    rintro _ ⟨t, ht, rfl⟩
    have hmem := hKV ht
    simp only [mem_Ioo] at hmem ⊢
    constructor <;> linarith [hmem.1, hmem.2]
  · intro g hg hgc hgs
    have hgs' : tsupport (fun t : ℝ => g (-t)) ⊆ Ioo (-b) (-a) := by
      intro t ht
      have h1 : t ∈ (fun t : ℝ => -t) ⁻¹' tsupport g := tsupport_comp_neg_subset ht
      have h2 := hgs h1
      simp only [mem_Ioo] at h2 ⊢
      constructor <;> linarith [h2.1, h2.2]
    have hlim := h3 (fun t => g (-t)) (hg.comp continuous_neg)
      (hgc.comp_homeomorph (Homeomorph.neg ℝ)) hgs'
    have hν : ∫ t : ℝ, g t ∂(ν.map fun t : ℝ => -t) = ∫ t : ℝ, g (-t) ∂ν :=
      integral_map measurable_neg.aemeasurable hg.aestronglyMeasurable
    rw [hν]
    refine hlim.congr' (Eventually.of_forall fun k => ?_)
    exact (integral_bdryApprox_neg k (havg k) g hg).symm

/-! ## 3. A.e. regularity of the deterministic-plus-free field -/

/-- Almost every sample of `𝔥₀(κ) + X` is a regular sample (from the a.e. regularity of the free
field and the decomposition `AtomlessUncond.gamma0_decomp`). -/
theorem ae_isRegularSample_ofFun_h0rev [IsProbabilityMeasure P] {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) (κ : ℝ) :
    ∀ᵐ ω ∂P, IsRegularSample (ofFun (h0rev κ) + X ω) := by
  filter_upwards [RegSample.ae_isRegularSample hX] with ω hreg
  rw [AtomlessUncond.gamma0_decomp κ (X ω)]
  exact ((hreg.addConst' _).add_ofFun_log' (-2 / Real.sqrt κ) 0).add_ofFun' continuousOn_const

/-! ## 4. The plus side -/

variable {P : Measure Ω} [IsProbabilityMeasure P] {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ}
  {X : Ω → FieldSample}

/-- **UO, plus side**, from AC-fam-ext for the reflected pair. -/
theorem unifOffTipPlusStmt_of_refl (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hF : AnchorUnifFamExtStmt κ T P (negB B) (reflX X)) :
    UnifOffTipPlusStmt κ T P B X := by
  have hB' : IsBrownianReal (negB B) P := hB.neg
  have hX' : IsFreeGFFModConstH (reflX X) P := isFreeGFFModConstH_reflRaw hX
  have hind' : IndepFun (pathOf (negB B)) (reflX X) P := indepFun_neg_reflRaw hind
  have hoff := ae_offTip_minus hκ hκ4 hT hB' hX' hind' hF
  filter_upwards [hoff, hB.cont, hB.eval_zero_ae_eq_zero,
    ae_forall_isRegularWith_joint (κ := κ) (γ := Real.sqrt κ) hB hX hind hT,
    ae_isRegularSample_ofFun_h0rev hX κ] with ω hoff hcont hB0 hG hbase
  obtain ⟨G, -, hGr⟩ := hG
  obtain ⟨Fb, hFb⟩ := hbase
  set W := drive κ B ω with hW
  have hWc : Continuous W := drive_continuous hcont
  have hW0 : W 0 = 0 := drive_zero hB0
  intro s hs u v hu
  have hYs : IsRegularWith (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, W) s)
      (fun p => G (s, p)) := hGr s hs
  obtain ⟨ν, hν, hνatom⟩ := hoff s hs (-v) (-u) (by push_cast; linarith)
  have hν' : IsVagueLimitOnR (Ioo (-(v : ℝ)) (-(u : ℝ)))
      (bdryApprox (Real.sqrt κ) (h0f κ s (negB B) (reflX X) ω)) ν := by
    simpa using hν
  have hcfg : cfg κ (negB B) (reflX X) ω = (reflRaw (ofFun (h0rev κ) + X ω), -W) := by
    simp only [B2.cfg]
    refine Prod.ext ?_ ?_
    · exact (reflRaw_add_ofFun_h0rev κ (X ω)).symm
    · rw [hW, drive_negB κ B ω]
  have hcfgB : cfg κ B X ω = (ofFun (h0rev κ) + X ω, W) := by
    simp only [B2.cfg, hW]
  have hkey : ∀ k : ℕ, ∀ t : ℝ,
      avgReg (h0f κ s (negB B) (reflX X) ω) k (t : ℂ) =
        avgReg (h0f κ s B X ω) k ((-t : ℝ) : ℂ) := by
    intro k t
    rw [B2.h0f_eq_unzippedField, B2.h0f_eq_unzippedField, hcfg, hcfgB]
    exact avgReg_unzippedField_reflRaw_neg_real hWc hW0 hs.1 hFb hYs k t
  refine ⟨ν.map fun t : ℝ => -t,
    isVagueLimitOnR_map_neg (a := (u : ℝ)) (b := (v : ℝ)) (x := h0f κ s B X ω)
      (x' := h0f κ s (negB B) (reflX X) ω) hkey hν', ?_⟩
  · intro x
    rw [Measure.map_apply measurable_neg (measurableSet_singleton x)]
    have hpre : (fun t : ℝ => -t) ⁻¹' {(x : ℝ)} = {-(x : ℝ)} := by
      ext t
      simp
    rw [hpre]
    exact hνatom (-(x : ℝ))

/-- **UO from AC-fam-ext for the pair and for its reflection.** With the analytic input for both
`(B, X)` and `(−B, X ∘ refl)`, the off-tip statement `UnifOffTipStmt` holds (the plus side is
`unifOffTipPlusStmt_of_refl`). -/
theorem unifOffTipStmt_of_ext_refl (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hF : AnchorUnifFamExtStmt κ T P B X)
    (hFr : AnchorUnifFamExtStmt κ T P (negB B) (reflX X)) :
    UnifOffTipStmt κ T P B X :=
  unifOffTipStmt_of_ext hκ hκ4 hT hB hX hind hF
    (unifOffTipPlusStmt_of_refl hκ hκ4 hT hB hX hind hFr)

end RegUnif
end QuantumZipper
