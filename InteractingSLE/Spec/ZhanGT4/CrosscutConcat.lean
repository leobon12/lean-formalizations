/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.RestartMarkov

/-!
# Concatenating a stopped Brownian path with an independent one

Packet PROVE-ZHAN-GT4-A2, probabilistic step of §A.4.2 (`source/external/AstraIG1/ig1_followup_proofs.txt` L768–L776:
"If the claimed assertion failed with positive probability on a localized past event, its intersection with the
positive-conditional-probability continuation event would have positive probability, contradicting the
first-swallow theorem").

To apply the first-swallow theorem (a statement about every Brownian motion) to a *past* event that need not be
measurable, the argument is run on the product space `Ω × Ω` with `P ⊗ P`: the first coordinate carries the path
stopped at the stopping time `T`, the second an independent Brownian path glued on at `T`,

  `concatBM B T t (ω, ω') = B_{t ∧ T(ω)}(ω) + (B_{(t − T(ω))⁺}(ω') − B_0(ω'))`.

`isBrownianReal_concatBM`: **this is a Brownian motion under `P ⊗ P`.** Its finite-dimensional laws are those of
`B`: by the strong Markov property (QuantumZipper's `StrongMarkov.indepFun_smPath`), the past `(B_{i ∧ T})_i` together
with a dyadic approximation `T_m ↓ T` is independent of the restarted path `B_{T+·} − B_T`, whose law is that of `B`;
so at the dyadic level both integrals equal the same integral against a product measure, and dominated convergence
(continuity of paths) passes to the limit.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal BoundedContinuousFunction

namespace InteractingSLE.ZhanGT4

open QuantumZipper QuantumZipper.StrongMarkov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The concatenation at `T(ω)`** of the path of `ω` stopped at `T(ω)` with the recentred path of `ω'`. -/
def concatBM (B : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) (t : ℝ≥0) (q : Ω × Ω) : ℝ :=
  B (min t (T q.1)) q.1 + (B (t - T q.1) q.2 - B 0 q.2)

theorem concatBM_of_le (B : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) {t : ℝ≥0} {q : Ω × Ω} (ht : t ≤ T q.1) :
    concatBM B T t q = B t q.1 := by
  simp [concatBM, min_eq_left ht, tsub_eq_zero_of_le ht]

theorem concatBM_add (B : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) (s : ℝ≥0) (q : Ω × Ω) :
    concatBM B T (T q.1 + s) q - concatBM B T (T q.1) q = B s q.2 - B 0 q.2 := by
  simp [concatBM, add_tsub_cancel_left]

theorem continuous_concatBM {B : ℝ≥0 → Ω → ℝ} (hBc : ∀ ω, Continuous (B · ω)) (T : Ω → ℝ≥0)
    (q : Ω × Ω) : Continuous fun t => concatBM B T t q := by
  unfold concatBM
  exact ((hBc q.1).comp (continuous_id.min continuous_const)).add
    (((hBc q.2).comp (continuous_id.sub continuous_const)).sub continuous_const)

theorem measurable_concatBM {B : ℝ≥0 → Ω → ℝ} (hBc : ∀ ω, Continuous (B · ω)) (hBm : ∀ t, Measurable (B t))
    {T : Ω → ℝ≥0} (hTm : Measurable T) (t : ℝ≥0) : Measurable (concatBM B T t) := by
  have hU : Measurable fun p : ℝ≥0 × Ω => B p.1 p.2 := measurable_uncurry_of_continuous_of_measurable hBc hBm
  unfold concatBM
  refine (hU.comp ((measurable_const.min (hTm.comp measurable_fst)).prodMk measurable_fst)).add
    ((hU.comp (((measurable_const.sub (hTm.comp measurable_fst))).prodMk measurable_snd)).sub
      ((hBm 0).comp measurable_snd))

/-- The value at time `t` of a path decomposes at `T`: `B_t = B_{t ∧ T} + (B_{T + (t − T)⁺} − B_T)`. -/
theorem eq_min_add_smShift (B : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    B t ω = B (min t (T ω)) ω + smShift B T (t - T ω) ω := by
  simp only [smShift]
  rcases le_total t (T ω) with h | h
  · rw [min_eq_left h, tsub_eq_zero_of_le h, add_zero]; ring
  · rw [min_eq_right h, add_tsub_cancel_of_le h]; ring

/-! ### The finite-dimensional laws -/

section Markov

variable {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ≥0}

/-- A finite stopping time is measurable for its own σ-algebra. -/
theorem measurable_stoppingTime_self (hT : IsStoppingTime 𝓖 (fun ω => (T ω : WithTop ℝ≥0))) :
    Measurable[hT.measurableSpace] T := by
  refine measurable_of_Iic (mδ := hT.measurableSpace) fun u => ?_
  have h := hT.measurableSet_le' u
  convert h using 1
  ext ω
  simp only [mem_preimage, mem_Iic, mem_ofPred_eq, WithTop.coe_le_coe]

/-- The stopped values `(B_{i ∧ T})_{i ∈ I}` are `𝓖_T`-measurable. -/
theorem measurable_stoppedValues (hprog : IsStronglyProgressive 𝓖 B)
    (hT : IsStoppingTime 𝓖 (fun ω => (T ω : WithTop ℝ≥0))) (I : Finset ℝ≥0) :
    Measurable[hT.measurableSpace] (fun ω (i : I) => B (min (i : ℝ≥0) (T ω)) ω) := by
  refine @Measurable.of_eval _ _ _ hT.measurableSpace _ _ fun i => ?_
  have hτ : IsStoppingTime 𝓖 (fun ω => ((min (i : ℝ≥0) (T ω) : ℝ≥0) : WithTop ℝ≥0)) := by
    have := hT.min_const (i : ℝ≥0)
    convert this using 2 with ω
    rw [WithTop.coe_min, min_comm]
  have h := measurable_stoppedValue hprog hτ
  have hle : hτ.measurableSpace ≤ hT.measurableSpace :=
    IsStoppingTime.measurableSpace_mono hτ hT fun ω => WithTop.coe_le_coe.2 (min_le_right _ _)
  exact h.mono hle le_rfl

variable [IsProbabilityMeasure P]

/-- **The dyadic step.** With `T_m` the dyadic ceiling of `T`, the past values together with the restarted path
evaluated at `i − T_m` have the same joint law as the past values together with an independent copy of `B`. -/
theorem integral_dyadic_eq (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (hBm : ∀ t, Measurable (B t))
    (hind : ∀ t, Indep (𝓖 t) (MeasurableSpace.comap (smPath B (fun _ => t)) MeasurableSpace.pi) P)
    (hprog : IsStronglyProgressive 𝓖 B) (hT : IsStoppingTime 𝓖 (fun ω => (T ω : WithTop ℝ≥0)))
    (I : Finset ℝ≥0) (m : ℕ) {F : (I → ℝ) → ℝ} (hF : Measurable F) {C : ℝ} (hFC : ∀ x, |F x| ≤ C) :
    ∫ ω, F (fun i : I => B (min (i : ℝ≥0) (T ω)) ω + smShift B T ((i : ℝ≥0) - dyadicTime T m ω) ω) ∂P =
      ∫ q, F (fun i : I => B (min (i : ℝ≥0) (T q.1)) q.1 + (B ((i : ℝ≥0) - dyadicTime T m q.1) q.2 - B 0 q.2))
        ∂(P.prod P) := by
  set a : Ω → (I → ℝ) := fun ω i => B (min (i : ℝ≥0) (T ω)) ω with ha
  set k : Ω → ℕ := fun ω => ⌈T ω * 2 ^ m⌉₊ with hk
  set Z : Ω → (I → ℝ) × ℕ := fun ω => (a ω, k ω) with hZ
  have hTT := measurable_stoppingTime_self hT
  have hZT : Measurable[hT.measurableSpace] Z :=
    (measurable_stoppedValues hprog hT I).prodMk (Nat.measurable_ceil.comp (hTT.mul_const _))
  have hZm : Measurable Z := hZT.mono hT.measurableSpace_le le_rfl
  have hYm : Measurable (smPath B T) := measurable_smPath hBc hBm (measurable_of_isStoppingTime hT)
  have hpath : Measurable fun ω (t : ℝ≥0) => B t ω := measurable_path hBm
  set φ : ((I → ℝ) × ℕ) × (ℝ≥0 → ℝ) → ℝ :=
    fun p => F (fun i : I => p.1.1 i + (p.2 ((i : ℝ≥0) - (p.1.2 : ℝ≥0) / 2 ^ m) - p.2 0)) with hφ
  have hφm : Measurable φ := by
    refine hF.comp (measurable_pi_iff.2 fun i => ?_)
    have hev : Measurable fun p : (ℝ≥0 → ℝ) × ℕ => p.1 ((i : ℝ≥0) - (p.2 : ℝ≥0) / 2 ^ m) :=
      measurable_from_prod_countable_left fun n =>
        (measurable_pi_apply ((i : ℝ≥0) - (n : ℝ≥0) / 2 ^ m) : Measurable fun f : ℝ≥0 → ℝ => f _)
    exact ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)).add
      ((hev.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).sub
        ((measurable_pi_apply 0).comp measurable_snd))
  have hφi : Integrable φ ((P.map Z).prod (P.map fun ω (t : ℝ≥0) => B t ω)) :=
    Integrable.of_bound hφm.aestronglyMeasurable C (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs]; exact hFC _)
  have hdy : ∀ ω, dyadicTime T m ω = (k ω : ℝ≥0) / 2 ^ m := fun ω => rfl
  -- the `P` side
  have hindZ : IndepFun Z (smPath B T) P := indepFun_smPath hB hBc hBm hind hT hZT
  have hlaw : P.map (fun ω => (Z ω, smPath B T ω)) = (P.map Z).prod (P.map (smPath B T)) :=
    (indepFun_iff_map_prod_eq_prod_map_map hZm.aemeasurable hYm.aemeasurable).1 hindZ
  have hY : P.map (smPath B T) = P.map fun ω (t : ℝ≥0) => B t ω := by
    have := map_restrict_smPath_eq hB hBc hBm hind hT (@MeasurableSet.univ Ω hT.measurableSpace)
    simpa only [Measure.restrict_univ, measure_univ, one_smul] using this
  have hL : ∫ ω, F (fun i : I => B (min (i : ℝ≥0) (T ω)) ω + smShift B T ((i : ℝ≥0) - dyadicTime T m ω) ω) ∂P =
      ∫ p, φ p ∂((P.map Z).prod (P.map fun ω (t : ℝ≥0) => B t ω)) := by
    rw [← hY, ← hlaw, integral_map (hZm.prodMk hYm).aemeasurable hφm.aestronglyMeasurable]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [hφ, hZ, ha, hdy, smPath, smShift, add_zero, sub_self, sub_zero]
  -- the product side
  have hR : ∫ q, F (fun i : I => B (min (i : ℝ≥0) (T q.1)) q.1 +
        (B ((i : ℝ≥0) - dyadicTime T m q.1) q.2 - B 0 q.2)) ∂(P.prod P) =
      ∫ p, φ p ∂((P.map Z).prod (P.map fun ω (t : ℝ≥0) => B t ω)) := by
    rw [Measure.map_prod_map P P hZm hpath, integral_map (hZm.prodMap hpath).aemeasurable
      hφm.aestronglyMeasurable]
    refine integral_congr_ae (ae_of_all _ fun q => ?_)
    simp only [hφ, hZ, ha, hdy, Prod.map]
  rw [hL, hR]

/-- **The limit step**: the finite-dimensional integrals of `concatBM` are those of `B`. -/
theorem integral_concatBM_eq (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (hBm : ∀ t, Measurable (B t))
    (hind : ∀ t, Indep (𝓖 t) (MeasurableSpace.comap (smPath B (fun _ => t)) MeasurableSpace.pi) P)
    (hprog : IsStronglyProgressive 𝓖 B) (hT : IsStoppingTime 𝓖 (fun ω => (T ω : WithTop ℝ≥0)))
    (I : Finset ℝ≥0) (F : (I → ℝ) →ᵇ ℝ) :
    ∫ q, F (fun i : I => concatBM B T i q) ∂(P.prod P) = ∫ ω, F (fun i : I => B i ω) ∂P := by
  have hFC : ∀ x, |F x| ≤ ‖F‖ := fun x => by rw [← Real.norm_eq_abs]; exact F.norm_coe_le_norm x
  have hTm : Measurable T := measurable_of_isStoppingTime hT
  have hU : Measurable fun p : ℝ≥0 × Ω => B p.1 p.2 := measurable_uncurry_of_continuous_of_measurable hBc hBm
  have hdT : ∀ m, Measurable (dyadicTime T m) := fun m =>
    measurable_of_isStoppingTime (isStoppingTime_dyadicTime hT m)
  have hTd : ∀ ω, Tendsto (fun m => dyadicTime T m ω) atTop (𝓝 (T ω)) := fun ω =>
    ItoLite.tendsto_dyadicCeil (T ω)
  -- the `P` side
  have hL : Tendsto (fun m => ∫ ω, F (fun i : I => B (min (i : ℝ≥0) (T ω)) ω +
      smShift B T ((i : ℝ≥0) - dyadicTime T m ω) ω) ∂P) atTop (𝓝 (∫ ω, F (fun i : I => B i ω) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ‖F‖) (fun m => ?_) (integrable_const _)
      (fun m => ae_of_all _ fun ω => F.norm_coe_le_norm _) (ae_of_all _ fun ω => ?_)
    · refine (F.continuous.measurable.comp (measurable_pi_iff.2 fun i => ?_)).aestronglyMeasurable
      exact (hU.comp ((measurable_const.min hTm).prodMk measurable_id)).add
        ((hU.comp ((hTm.add (measurable_const.sub (hdT m))).prodMk measurable_id)).sub
          (hU.comp (hTm.prodMk measurable_id)))
    · have heq : (fun i : I => B i ω) = fun i : I => B (min (i : ℝ≥0) (T ω)) ω +
          smShift B T ((i : ℝ≥0) - T ω) ω := funext fun i => eq_min_add_smShift B T i ω
      rw [heq]
      refine (F.continuous.tendsto _).comp (tendsto_pi_nhds.2 fun i => ?_)
      refine tendsto_const_nhds.add ?_
      simp only [smShift]
      exact (((hBc ω).tendsto _).comp (tendsto_const_nhds.add
        (tendsto_const_nhds.sub (hTd ω)))).sub tendsto_const_nhds
  -- the product side
  have hR : Tendsto (fun m => ∫ q, F (fun i : I => B (min (i : ℝ≥0) (T q.1)) q.1 +
      (B ((i : ℝ≥0) - dyadicTime T m q.1) q.2 - B 0 q.2)) ∂(P.prod P)) atTop
      (𝓝 (∫ q, F (fun i : I => concatBM B T i q) ∂(P.prod P))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ‖F‖) (fun m => ?_) (integrable_const _)
      (fun m => ae_of_all _ fun q => F.norm_coe_le_norm _) (ae_of_all _ fun q => ?_)
    · refine (F.continuous.measurable.comp (measurable_pi_iff.2 fun i => ?_)).aestronglyMeasurable
      exact (hU.comp ((measurable_const.min (hTm.comp measurable_fst)).prodMk measurable_fst)).add
        ((hU.comp ((measurable_const.sub ((hdT m).comp measurable_fst)).prodMk measurable_snd)).sub
          ((hBm 0).comp measurable_snd))
    · refine (F.continuous.tendsto _).comp (tendsto_pi_nhds.2 fun i => ?_)
      refine tendsto_const_nhds.add (Tendsto.sub ?_ tendsto_const_nhds)
      exact ((hBc q.2).tendsto _).comp (tendsto_const_nhds.sub (hTd q.1))
  have heq : ∀ m, ∫ ω, F (fun i : I => B (min (i : ℝ≥0) (T ω)) ω +
      smShift B T ((i : ℝ≥0) - dyadicTime T m ω) ω) ∂P = ∫ q, F (fun i : I => B (min (i : ℝ≥0) (T q.1)) q.1 +
      (B ((i : ℝ≥0) - dyadicTime T m q.1) q.2 - B 0 q.2)) ∂(P.prod P) := fun m =>
    integral_dyadic_eq hB hBc hBm hind hprog hT I m F.continuous.measurable hFC
  simp_rw [heq] at hL
  exact tendsto_nhds_unique hR hL

/-- **The concatenation is a Brownian motion under `P ⊗ P`.** -/
theorem isBrownianReal_concatBM (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (hBm : ∀ t, Measurable (B t))
    (hind : ∀ t, Indep (𝓖 t) (MeasurableSpace.comap (smPath B (fun _ => t)) MeasurableSpace.pi) P)
    (hprog : IsStronglyProgressive 𝓖 B) (hT : IsStoppingTime 𝓖 (fun ω => (T ω : WithTop ℝ≥0))) :
    IsBrownianReal (concatBM B T) (P.prod P) where
  toIsPreBrownianReal := IsPreBrownianReal.mk' fun I => by
    have hTm : Measurable T := measurable_of_isStoppingTime hT
    have hm : Measurable fun q : Ω × Ω => I.restrict fun t => concatBM B T t q :=
      measurable_pi_iff.2 fun i => measurable_concatBM hBc hBm hTm i
    have hmB : Measurable fun ω => I.restrict fun t => B t ω :=
      measurable_pi_iff.2 fun i => hBm i
    refine ⟨hm.aemeasurable, ?_⟩
    rw [← (hB.hasLaw I).map_eq]
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun F => ?_
    rw [integral_map hm.aemeasurable F.continuous.aestronglyMeasurable,
      integral_map hmB.aemeasurable F.continuous.aestronglyMeasurable]
    exact integral_concatBM_eq hB hBc hBm hind hprog hT I F
  cont := ae_of_all _ (continuous_concatBM hBc T)

end Markov

end InteractingSLE.ZhanGT4
