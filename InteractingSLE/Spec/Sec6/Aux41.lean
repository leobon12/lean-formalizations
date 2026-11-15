import InteractingSLE.Foundations.Loewner.YuanSimpleApprox
import InteractingSLE.Foundations.Loewner.YuanCharacterisationMarkov

/-!
# Aux. lemma 41: the Loewner criterion for the strict-angle pocket erasure

Specification §6, **Aux.** lemma 41 (`source/spec/p193-240.md` L214–L265): the pause-free erased
path `ζ = ψ ∘ γ̂_C` of **Aux.** lemma 40 "has a continuous Loewner driving function up to its
terminal capacity time. In particular it has the order-sensitive uniform simple approximations
required in Proposition 6.12."

The proof of Aux. 41 has two parts.

1. (RG1)–(RG5): for every nonterminal erased time the own-mapped future of `ζ` is continuous,
   i.e. condition (ii) of [Yua22, Theorem 1.1] holds on every compact nonterminal interval. This
   part uses the objects of Aux. 36–40 (the Jordan pocket `C`, the erasure, the Jordan faces
   `F_s`), which have no Lean statement yet; it is not formalized here.
2. The **Loewner-criterion step**: "Apply the implication (ii) ⇒ (i) of [Yua22, Theorem 1.1], on
   compact intervals before the terminal time. It gives local growth and hence a continuous Loewner
   driver after the continuous strictly increasing capacity change. The same theorem then gives
   the asserted uniform simple approximations." This file proves this step, in the form consumed
   by Proposition 6.12 (`HasSimpleApproxOn`), for every path satisfying condition (ii)
   (`YuanCharacterisation.HasContinuousOwnFuture`) and strict growth of its fillings.

## Main results

* `hasSimpleApproxOn_of_fwdHull_comp`: a path whose fillings are the hulls of a continuous driver
  after a continuous strictly increasing time change `σ` has the uniform simple approximations on
  every `[0, S]` strictly inside the interval of definition of `σ` (transfer of [Yua22, Theorem
  1.1, (i) ⇒ (iii)], `IsLoewnerTraceLT.hasSimpleApproxOn`, through `σ⁻¹`);
* `exists_loewner_and_hasSimpleApproxOn_of_hasContinuousOwnFuture`: **the Loewner-criterion step
  of Aux. lemma 41**: condition (ii) and strict growth on `[0, S']` give a continuous driver after
  a capacity change on `[0, S']` (PROVE-YUAN-M23, (ii) ⇒ (i)) and the uniform simple
  approximations of Proposition 6.12 on every `[0, S]`, `S < S'`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Function

open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Sec6

/-- **Transfer of the simple approximations through a capacity change.** If the fillings of
`ζ([0, t])` are the hulls `K_{σ(t)}` of a continuous driver `W` for a continuous strictly increasing
`σ` with `σ 0 = 0` on `[0, S']`, then `ζ` has the uniform simple approximations on `[0, S]` for
every `S < S'`. -/
theorem hasSimpleApproxOn_of_fwdHull_comp {ζ : ℝ → ℂ} {W : ℝ → ℝ} {σ : ℝ → ℝ} {S S' : ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) (hσ0 : σ 0 = 0) (hσm : StrictMonoOn σ (Icc 0 S'))
    (hσc : ContinuousOn σ (Icc 0 S')) (hζ : ContinuousOn ζ (Icc 0 S')) (hζ0 : ζ 0 = 0)
    (hhull : ∀ t ∈ Icc 0 S', fwdHull W (σ t) = fillH (ζ '' Icc 0 t)) (hSS' : S < S') :
    HasSimpleApproxOn ζ S := by
  rcases lt_or_ge S 0 with hS | hS
  · refine ⟨fun _ _ => 0, fun _ => ⟨continuousOn_const, ?_, rfl, ?_⟩, ?_⟩
    · intro u hu; exact absurd (hu.1.trans hu.2) (not_le.2 hS)
    · intro u hu; exact absurd (hu.1.trans_le hu.2) (not_lt.2 hS.le)
    · refine Metric.tendstoUniformlyOn_iff.2 fun e he => Eventually.of_forall fun n u hu => ?_
      exact absurd (hu.1.trans hu.2) (not_le.2 hS)
  have hS'0 : 0 ≤ S' := hS.trans hSS'.le
  have hmem0 : (0 : ℝ) ∈ Icc 0 S' := ⟨le_rfl, hS'0⟩
  have hmemS' : S' ∈ Icc 0 S' := ⟨hS'0, le_rfl⟩
  have hσS'0 : 0 ≤ σ S' := by
    have := hσm.monotoneOn hmem0 hmemS' hS'0; rwa [hσ0] at this
  -- the inverse of `σ` as an order isomorphism `[0, σ S'] ≃o [0, S']`
  set f : Icc (0 : ℝ) S' → Icc (0 : ℝ) (σ S') := fun x =>
    ⟨σ x, by have := hσm.monotoneOn hmem0 x.2 x.2.1; rwa [hσ0] at this,
      hσm.monotoneOn x.2 hmemS' x.2.2⟩ with hf
  have hfm : StrictMono f := fun x y hxy => hσm x.2 y.2 hxy
  have hfs : Surjective f := by
    intro y
    obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc hS'0 hσc (by rw [hσ0]; exact y.2)
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  set e := StrictMono.orderIsoOfSurjective f hfm hfs with he
  set σinv : ℝ → ℝ := fun u => (e.symm (projIcc 0 (σ S') hσS'0 u) : ℝ) with hσinv
  have hσinvc : Continuous σinv :=
    continuous_subtype_val.comp (e.symm.continuous.comp continuous_projIcc)
  have hσinv_mem : ∀ u, σinv u ∈ Icc 0 S' := fun u => (e.symm _).2
  have hσσinv : ∀ u ∈ Icc 0 (σ S'), σ (σinv u) = u := by
    intro u hu
    have := StrictMono.orderIsoOfSurjective_self_symm_apply f hfm hfs (projIcc 0 (σ S') hσS'0 u)
    show σ (e.symm (projIcc 0 (σ S') hσS'0 u) : ℝ) = u
    have h2 := congrArg Subtype.val this
    rw [projIcc_of_mem hσS'0 hu] at h2 ⊢
    exact h2
  have hσinvσ : ∀ x ∈ Icc 0 S', σinv (σ x) = x := by
    intro x hx
    have hx' : σ x ∈ Icc 0 (σ S') := (f ⟨x, hx⟩).2
    have := StrictMono.orderIsoOfSurjective_symm_apply_self f hfm hfs ⟨x, hx⟩
    show (e.symm (projIcc 0 (σ S') hσS'0 (σ x)) : ℝ) = x
    rw [projIcc_of_mem hσS'0 hx']
    exact congrArg Subtype.val this
  have hσinv0 : σinv 0 = 0 := by rw [← hσ0, hσinvσ 0 hmem0, hσ0]
  have hσinv_mono : Monotone σinv := fun u v huv =>
    e.symm.monotone (monotone_projIcc hσS'0 huv)
  -- the capacity-parametrized trace
  set η' : ℝ → ℂ := fun u => ζ (σinv u) with hη'
  have hη'trace : IsLoewnerTraceLT W (σ S') η' := by
    refine ⟨by simp only [hη', hσinv0, hζ0], (hζ.comp hσinvc.continuousOn
      fun u _ => hσinv_mem u).mono Ico_subset_Icc_self |>.mono subset_rfl, fun u hu huS => ?_⟩
    · have hu' : u ∈ Icc 0 (σ S') := ⟨hu, huS.le⟩
      have himg : σinv '' Icc 0 u = Icc 0 (σinv u) := by
        ext x
        constructor
        · rintro ⟨v, hv, rfl⟩
          exact ⟨hσinv0 ▸ hσinv_mono hv.1, hσinv_mono hv.2⟩
        · intro hx
          have hxS' : x ∈ Icc 0 S' := ⟨hx.1, hx.2.trans (hσinv_mem u).2⟩
          refine ⟨σ x, ⟨?_, ?_⟩, hσinvσ x hxS'⟩
          · have := hσm.monotoneOn hmem0 hxS' hx.1; rwa [hσ0] at this
          · rw [← hσσinv u hu']; exact hσm.monotoneOn hxS' (hσinv_mem u) hx.2
      rw [show η' '' Icc 0 u = ζ '' (σinv '' Icc 0 u) from (image_image ζ σinv _).symm, himg,
        ← hhull (σinv u) (hσinv_mem u), hσσinv u hu']
  have hσSS' : σ S < σ S' := hσm ⟨hS, hSS'.le⟩ hmemS' hSS'
  obtain ⟨γ, hγ, hlim⟩ := hη'trace.hasSimpleApproxOn hW hW0 hσSS'
  have hσmaps : MapsTo σ (Icc 0 S) (Icc 0 (σ S)) := fun x hx =>
    ⟨by have := hσm.monotoneOn hmem0 ⟨hx.1, hx.2.trans hSS'.le⟩ hx.1; rwa [hσ0] at this,
      hσm.monotoneOn ⟨hx.1, hx.2.trans hSS'.le⟩ ⟨hS, hSS'.le⟩ hx.2⟩
  refine ⟨fun n => γ n ∘ σ, fun n => ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (hγ n).1.comp (hσc.mono (Icc_subset_Icc_right hSS'.le)) hσmaps
  · exact (hγ n).2.1.comp (hσm.injOn.mono (Icc_subset_Icc_right hSS'.le)) hσmaps
  · simp only [comp_apply, hσ0]; exact (hγ n).2.2.1
  · intro x hx
    refine (hγ n).2.2.2 ⟨?_, (hσmaps ⟨hx.1.le, hx.2⟩).2⟩
    rw [← hσ0]
    exact hσm hmem0 ⟨hx.1.le, hx.2.trans hSS'.le⟩ hx.1
  · have := (hlim.comp σ).mono (fun x hx => hσmaps hx)
    refine this.congr_right fun x hx => ?_
    simp only [comp_apply, hη', hσinvσ x ⟨hx.1, hx.2.trans hSS'.le⟩]

/-- **Aux. lemma 41, the Loewner-criterion step** ([Yua22, Theorem 1.1, (ii) ⇒ (i) ⇒ (iii)]). Let
`ζ : [0, S'] → ℍ̄` be continuous with `ζ 0 = 0`, with strictly increasing fillings, and satisfy
condition (ii) of [Yua22, Theorem 1.1] (`HasContinuousOwnFuture`: after mapping out every own
prefix, the future is continuous). Then `ζ` has a continuous Loewner driving function after a
continuous strictly increasing capacity change on `[0, S']`, and the uniform simple approximations
of Proposition 6.12's non-crossing convention on every `[0, S]` with `S < S'`. -/
theorem exists_loewner_and_hasSimpleApproxOn_of_hasContinuousOwnFuture {ζ : ℝ → ℂ} {S S' : ℝ}
    (hS' : 0 < S') (hζ : ContinuousOn ζ (Icc 0 S')) (hζ0 : ζ 0 = 0)
    (hHbar : MapsTo ζ (Icc 0 S') Hbar)
    (hmono : StrictMonoOn (fun t => fillH (ζ '' Icc 0 t)) (Icc 0 S'))
    (hii : YuanCharacterisation.HasContinuousOwnFuture ζ S') (hSS' : S < S') :
    (∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ ∃ σ : ℝ → ℝ, σ 0 = 0 ∧ StrictMonoOn σ (Icc 0 S') ∧
      ContinuousOn σ (Icc 0 S') ∧ ∀ t ∈ Icc 0 S', fwdHull W (σ t) = fillH (ζ '' Icc 0 t)) ∧
      HasSimpleApproxOn ζ S := by
  obtain ⟨W, hW, hW0, σ, hσ0, hσm, hσc, hhull⟩ :=
    YuanCharacterisation.exists_loewner_of_hasContinuousOwnFuture hS' hζ hζ0 hHbar hmono hii
  exact ⟨⟨W, hW, hW0, σ, hσ0, hσm, hσc, hhull⟩,
    hasSimpleApproxOn_of_fwdHull_comp hW hW0 hσ0 hσm hσc hζ hζ0 hhull hSS'⟩

end InteractingSLE.Sec6
