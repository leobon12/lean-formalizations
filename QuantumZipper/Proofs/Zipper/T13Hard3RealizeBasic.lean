import QuantumZipper.Proofs.GFF.Existence
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Representation
import Mathlib.Probability.Independence.Integration

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# T13-HARD3, part 1: generic tools for the realization of `P_*` samples

* `exists_freeGFF_stdP`: the free field of `GFFExist.exists_freeGFF`, exposed on its carrier
  `(ℕ → ℝ, stdP)` (a standard Borel space). The proof is verbatim the one of
  `exists_freeGFF` (`Proofs/GFF/Existence.lean`), only the conclusion is exposed.
* `T13Hard3.exists_transfer`: the **transfer theorem** (Kallenberg, *Foundations of Modern
  Probability*, 2nd ed., Thm. 6.10, with Thm. 6.3 (disintegration) and Lemma 3.22
  (randomization)): if `s` under `P'` has the law of `ξ₀` under `P₀`, with `P₀` on a standard
  Borel space, there is a measurable `f` such that `G ω = f (s ω.1) ω.2` is measure preserving
  `P' ⊗ Leb → P₀` and `ξ₀ ∘ G = s ∘ fst` a.s. It follows Kallenberg's proof: disintegrate
  `ρ = law(ξ₀, id)` along its first coordinate (`Measure.condKernel`, `Measure.disintegrate`),
  realize the kernel from the uniform law (`Kernel.exists_measurable_map_eq_unitInterval`), and
  identify the joint law of `(s, G)` with `law(s) ⊗ₘ κ = ρ`.
* `T13Hard3.indepFun_pair_fst`: an independent pair `(a, b)` on `P'` stays independent after
  adjoining a fresh coordinate to `a` on `P' ⊗ Q` (own elementary proof, Fubini + product
  formula for independent functions).
* `T13Hard3.indepFun_comp_mp`: independence of a.e.-measurable functions is transported by
  measure-preserving maps (own elementary proof).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped ENNReal

namespace QuantumZipper

section FreeStdP
open GFFExist LQGDimension.ExistAsm
open scoped RealInnerProductSpace

/-- The free field modulo constants on the i.i.d. Gaussian sequence space (proof copied from
`exists_freeGFF`). -/
theorem exists_freeGFF_stdP : ∃ X : (ℕ → ℝ) → FieldSample, IsFreeGFFModConstH X stdP := by
  classical
  obtain ⟨X, hXm, hX⟩ := gs_process_hilbert AdmT freeVec
  set F : (ℕ → ℝ) → FieldSample := fun ω μ => if h : IsAdmissibleH μ then X ⟨μ, h⟩ ω else 0
    with hF
  have hFX : ∀ (μ : Measure ℂ) (h : IsAdmissibleH μ) ω, F ω μ = X ⟨μ, h⟩ ω := by
    intro μ h ω; simp only [hF, h, ↓reduceDIte]
  have hdiff : ∀ (μ ν : Measure ℂ) (hμ : IsAdmissibleH μ) (hν : IsAdmissibleH ν),
      (fun ω => F ω μ - F ω ν) = fun ω => X ⟨μ, hμ⟩ ω - X ⟨ν, hν⟩ ω := by
    intro μ ν hμ hν; funext ω; rw [hFX μ hμ, hFX ν hν]
  have hlaw2 : ∀ μ ν : AdmT, HasLaw (fun ω => X μ ω - X ν ω)
      (gaussianReal 0 (‖freeVec μ - freeVec ν‖ ^ 2).toNNReal) stdP :=
    fun μ ν => gs_comb4 hX ![μ, ν, μ, μ] ![1, -1, 0, 0] _
      (fun ω => by simp [Fin.sum_univ_four]; ring) _
      (by simp [Fin.sum_univ_four, sub_eq_add_neg])
  refine ⟨F, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro μ
    by_cases h : IsAdmissibleH μ
    · have : (fun ω => F ω μ) = X ⟨μ, h⟩ := funext (hFX μ h)
      rw [this]; exact hXm _
    · have : (fun ω => F ω μ) = fun _ => 0 := by funext ω; simp only [hF, h, ↓reduceDIte]
      rw [this]; exact measurable_const
  · refine gs_isGaussianProcess (fun p => ?_) fun I c => ?_
    · rw [hdiff _ _ p.2.1 p.2.2.1]
      exact ((hXm _).sub (hXm _)).aemeasurable
    · set τ : I ⊕ I → AdmT := Sum.elim (fun i => ⟨i.1.1.1, i.1.2.1⟩)
        (fun i => ⟨i.1.1.2, i.1.2.2.1⟩) with hτ
      set c' : I ⊕ I → ℝ := Sum.elim c (fun i => -c i) with hc'
      have e : (fun ω => ∑ i : I, c i * (F ω i.1.1.1 - F ω i.1.1.2)) =
          fun ω => ∑ j, c' j * X (τ j) ω := by
        funext ω
        rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hτ, hc', Sum.elim_inl, Sum.elim_inr]
        rw [hFX _ i.1.2.1 ω, hFX _ i.1.2.2.1 ω]
        ring
      exact ⟨_, e ▸ hX τ c'⟩
  · intro μ ν hμ hν _
    rw [hdiff μ ν hμ hν]
    exact gs_integral_eq_zero (hlaw2 ⟨μ, hμ⟩ ⟨ν, hν⟩)
  · intro p q hp1 hp2 hp hq1 hq2 hq
    rw [hdiff _ _ hp1 hp2, hdiff _ _ hq1 hq2]
    have hinner := freeVec_inner ⟨p.1, hp1⟩ ⟨p.2, hp2⟩ ⟨q.1, hq1⟩ ⟨q.2, hq2⟩ hp hq
    simp only [Prod.mk.eta] at hinner
    rw [← hinner]
    refine gs_cov_eq (hlaw2 _ _) (hlaw2 _ _) ?_
    exact gs_comb4 hX ![⟨p.1, hp1⟩, ⟨p.2, hp2⟩, ⟨q.1, hq1⟩, ⟨q.2, hq2⟩] ![1, -1, 1, -1] _
      (fun ω => by simp [Fin.sum_univ_four]; ring) _
      (by simp [Fin.sum_univ_four]; abel)
  · intro μ ν hμ hν a b
    have hw := gffEx_admissible_comb hμ hν a b
    have hlaw := gs_comb4 hX ![⟨_, hw⟩, ⟨μ, hμ⟩, ⟨ν, hν⟩, ⟨μ, hμ⟩] ![1, -(a : ℝ), -(b : ℝ), 0]
      (fun ω => X ⟨_, hw⟩ ω - ((a : ℝ) * X ⟨μ, hμ⟩ ω + (b : ℝ) * X ⟨ν, hν⟩ ω))
      (fun ω => by simp [Fin.sum_univ_four]; ring) (0 : HkE)
      (by
        simp [Fin.sum_univ_four, freeVec_comb ⟨μ, hμ⟩ ⟨ν, hν⟩ a b ⟨_, hw⟩ rfl]
        try module)
    have h0 : (‖(0 : HkE)‖ ^ 2).toNNReal = 0 := by simp
    have hae : ∀ᵐ ω ∂stdP,
        X ⟨_, hw⟩ ω - ((a : ℝ) * X ⟨μ, hμ⟩ ω + (b : ℝ) * X ⟨ν, hν⟩ ω) = 0 := by
      refine ae_of_ae_map (p := fun y : ℝ => y = 0) hlaw.aemeasurable ?_
      rw [hlaw.map_eq, h0, gaussianReal_zero_var, ae_dirac_eq]
      exact Filter.eventually_pure.2 rfl
    filter_upwards [hae] with ω hω
    rw [hFX _ hw ω, hFX μ hμ ω, hFX ν hν ω]
    linarith

end FreeStdP

namespace T13Hard3

section Transfer

variable {Ω' S Ω₀ : Type*} [MeasurableSpace Ω'] [MeasurableSpace S] [MeasurableSpace Ω₀]

/-- Randomizing a kernel along `s`: the joint law of `(s, f (s ·) u)` under `P' ⊗ Leb` is
`law(s) ⊗ₘ κ`. -/
theorem map_pair_eq_compProd {P' : Measure Ω'} [IsProbabilityMeasure P'] {s : Ω' → S}
    (hs : Measurable s) (κ : Kernel S Ω₀) [IsMarkovKernel κ] {f : S → unitInterval → Ω₀}
    (hf : Measurable (uncurry f))
    (hfκ : ∀ a, (volume : Measure unitInterval).map (f a) = κ a) :
    (P'.prod (volume : Measure unitInterval)).map (fun ω => (s ω.1, f (s ω.1) ω.2)) =
      (P'.map s) ⊗ₘ κ := by
  have hfa : ∀ a, Measurable (f a) := fun a => hf.comp measurable_prodMk_left
  have hm : Measurable (fun ω : Ω' × unitInterval => (s ω.1, f (s ω.1) ω.2)) :=
    (hs.comp measurable_fst).prodMk (hf.comp ((hs.comp measurable_fst).prodMk measurable_snd))
  ext E hE
  rw [Measure.map_apply hm hE, Measure.compProd_apply hE, Measure.prod_apply (hm hE),
    lintegral_map (Kernel.measurable_kernel_prodMk_left hE) hs]
  refine lintegral_congr fun x => ?_
  rw [← hfκ (s x), Measure.map_apply (hfa (s x)) (measurable_prodMk_left hE)]
  rfl

variable [StandardBorelSpace Ω₀] [Nonempty Ω₀]

/-- **Transfer theorem** (Kallenberg, FMP 2nd ed., Thm. 6.10). -/
theorem exists_transfer [MeasurableEq S] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
    {ξ₀ : Ω₀ → S} (hξ₀ : Measurable ξ₀) {P' : Measure Ω'} [IsProbabilityMeasure P']
    {s : Ω' → S} (hs : Measurable s) (hlaw : P'.map s = P₀.map ξ₀) :
    ∃ f : S → unitInterval → Ω₀, Measurable (uncurry f) ∧
      MeasurePreserving (fun ω : Ω' × unitInterval => f (s ω.1) ω.2)
        (P'.prod (volume : Measure unitInterval)) P₀ ∧
      ∀ᵐ ω ∂(P'.prod (volume : Measure unitInterval)), ξ₀ (f (s ω.1) ω.2) = s ω.1 := by
  set ρ : Measure (S × Ω₀) := P₀.map (fun ω₀ => (ξ₀ ω₀, ω₀)) with hρ
  have hρm : Measurable (fun ω₀ => (ξ₀ ω₀, ω₀)) := hξ₀.prodMk measurable_id
  have : IsProbabilityMeasure ρ := by rw [hρ]; infer_instance
  obtain ⟨f, hf, hfκ⟩ := Kernel.exists_measurable_map_eq_unitInterval ρ.condKernel
  have hfst : ρ.fst = P'.map s := by
    rw [Measure.fst, hρ, Measure.map_map measurable_fst hρm, hlaw]
    rfl
  have hm : Measurable (fun ω : Ω' × unitInterval => (s ω.1, f (s ω.1) ω.2)) :=
    (hs.comp measurable_fst).prodMk (hf.comp ((hs.comp measurable_fst).prodMk measurable_snd))
  have hkey : (P'.prod volume).map (fun ω => (s ω.1, f (s ω.1) ω.2)) = ρ := by
    rw [map_pair_eq_compProd hs _ hf hfκ, ← hfst, Measure.disintegrate]
  refine ⟨f, hf, ⟨hf.comp ((hs.comp measurable_fst).prodMk measurable_snd), ?_⟩, ?_⟩
  · have e : (fun ω : Ω' × unitInterval => f (s ω.1) ω.2) =
        Prod.snd ∘ (fun ω => (s ω.1, f (s ω.1) ω.2)) := rfl
    rw [e, ← Measure.map_map measurable_snd hm, hkey, hρ, Measure.map_map measurable_snd hρm]
    exact Measure.map_id
  · have hD : MeasurableSet {p : S × Ω₀ | ξ₀ p.2 = p.1} :=
      measurableSet_eq_fun (hξ₀.comp measurable_snd) measurable_fst
    have h1 : ∀ᵐ p ∂ρ, ξ₀ p.2 = p.1 := by
      rw [hρ, ae_map_iff hρm.aemeasurable hD]
      exact ae_of_all _ fun _ => rfl
    rw [← hkey] at h1
    exact ae_of_ae_map hm.aemeasurable h1

end Transfer

section Indep

variable {Ω' Ω₂ Ω₀ Ω S T : Type*} [MeasurableSpace Ω'] [MeasurableSpace Ω₂]
  [MeasurableSpace Ω₀] [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]

/-- Adjoining a fresh independent coordinate to `a` keeps it independent of `b`. -/
theorem indepFun_pair_fst {P' : Measure Ω'} [IsProbabilityMeasure P'] {Q : Measure Ω₂}
    [IsProbabilityMeasure Q] {a : Ω' → S} {b : Ω' → T} (ha : Measurable a) (hb : Measurable b)
    (h : IndepFun a b P') :
    IndepFun (fun ω : Ω' × Ω₂ => (a ω.1, ω.2)) (fun ω => b ω.1) (P'.prod Q) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro E F hE hF
  have hV : Measurable (fun ω : Ω' × Ω₂ => (a ω.1, ω.2)) :=
    (ha.comp measurable_fst).prodMk measurable_snd
  have hW : Measurable (fun ω : Ω' × Ω₂ => b ω.1) := hb.comp measurable_fst
  set g : S → ℝ≥0∞ := fun x => Q (Prod.mk x ⁻¹' E) with hg_def
  have hg : Measurable g := measurable_measure_prodMk_left hE
  set φ : T → ℝ≥0∞ := F.indicator 1 with hφ_def
  have hφ : Measurable φ := measurable_one.indicator hF
  have e1 : ∀ x, Q (Prod.mk x ⁻¹' ((fun ω : Ω' × Ω₂ => (a ω.1, ω.2)) ⁻¹' E ∩
      (fun ω => b ω.1) ⁻¹' F)) = (φ ∘ b) x * (g ∘ a) x := by
    intro x
    by_cases hx : b x ∈ F
    · simp only [hφ_def, hg_def, Function.comp, Set.indicator_of_mem hx, Pi.one_apply, one_mul]
      congr 1
      ext u
      simp [hx]
    · simp only [hφ_def, Function.comp, Set.indicator_of_notMem hx, zero_mul]
      convert measure_empty (μ := Q)
      ext u
      simp [hx]
  have e2 : ∀ x, Q (Prod.mk x ⁻¹' ((fun ω : Ω' × Ω₂ => (a ω.1, ω.2)) ⁻¹' E)) = (g ∘ a) x :=
    fun x => rfl
  have e3 : ∀ x, Q (Prod.mk x ⁻¹' ((fun ω : Ω' × Ω₂ => b ω.1) ⁻¹' F)) = (φ ∘ b) x := by
    intro x
    by_cases hx : b x ∈ F
    · simp only [hφ_def, Function.comp, Set.indicator_of_mem hx, Pi.one_apply]
      convert measure_univ (μ := Q)
      ext u
      simp [hx]
    · simp only [hφ_def, Function.comp, Set.indicator_of_notMem hx]
      convert measure_empty (μ := Q)
      ext u
      simp [hx]
  rw [Measure.prod_apply ((hV hE).inter (hW hF)), Measure.prod_apply (hV hE),
    Measure.prod_apply (hW hF)]
  simp_rw [e1, e2, e3]
  have := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (hφ.comp hb) (hg.comp ha)
    (h.symm.comp hφ hg)
  simp only [Pi.mul_apply] at this
  rw [this, mul_comm]

/-- Independence of a.e.-measurable functions is transported by measure-preserving maps. -/
theorem indepFun_comp_mp {μ : Measure Ω} {P₀ : Measure Ω₀} {G : Ω → Ω₀}
    (hG : MeasurePreserving G μ P₀) {F : Ω₀ → S} {H : Ω₀ → T} (hF : AEMeasurable F P₀)
    (hH : AEMeasurable H P₀) (h : IndepFun F H P₀) : IndepFun (F ∘ G) (H ∘ G) μ := by
  have h' : IndepFun (hF.mk F) (hH.mk H) P₀ := h.congr hF.ae_eq_mk hH.ae_eq_mk
  have h'' : IndepFun (hF.mk F ∘ G) (hH.mk H ∘ G) μ := by
    rw [indepFun_iff_measure_inter_preimage_eq_mul] at h' ⊢
    intro s t hs ht
    rw [preimage_comp, preimage_comp, ← preimage_inter,
      hG.measure_preimage ((hF.measurable_mk hs).inter (hH.measurable_mk ht)).nullMeasurableSet,
      hG.measure_preimage (hF.measurable_mk hs).nullMeasurableSet,
      hG.measure_preimage (hH.measurable_mk ht).nullMeasurableSet]
    exact h' s t hs ht
  exact h''.congr (hG.quasiMeasurePreserving.ae_eq_comp hF.ae_eq_mk).symm
    (hG.quasiMeasurePreserving.ae_eq_comp hH.ae_eq_mk).symm

end Indep

end T13Hard3
end QuantumZipper
