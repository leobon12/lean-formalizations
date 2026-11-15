/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtLPiece
import InteractingSLE.Foundations.Loewner.HullRightCont

/-!
# Aux. lemma 54, (K-pre): the protected kernel before the local stop survives the extension

Packet PROVE-LOCEXT-L. Let `E` be a record extension of a stopped seed coupling `(Q, h)` by a two-seed reference
`(P̂, ĥ)` whose usual augmentation `𝓖` is **time-adapted** to the recorded history (`hTAG`: an event of `𝓖_q` agrees,
almost surely on `{t < Ŝ}`, with an event of the history truncated at any rational `t > q`; Theorem 1.1's construction
on the coordinate filtration has this property). For a stop `s` of `𝓖` that is safe for an open `U` (`s < ζ̂`,
`U ∩ K_s = ∅`), `supp ψ ⊆ U` and `A₀ ∈ 𝓖_s`:

`∫_{snd⁻¹(A₀ ∩ {s < Ŝ})} e^{i h(p.1)(ψ)} dE = ∫_{snd⁻¹(A₀ ∩ {s < Ŝ})} e^{i ĥ(p.2)(ψ)} dE`.

Proof (`planning/handoffs/PROVE-LOCEXT-J.md`, (K-pre)). Cut `A₀` along the dyadic grid of level `n`: the pieces
`A₀ ∩ {⌈2ⁿ s⌉ = k}` are events of `𝓖_{k/2ⁿ}`; at `t = (k+1)/2ⁿ` each piece, restricted to `{t < Ŝ}` and to
`{supp ψ ∩ K_t = ∅}` (read from the truncated history), is almost surely a truncated-history event (`hTAG`), on which
the identity holds (`setIntegral_trunc_eq`). Summing over `k` gives the identity on `B_n ⊆ A₀ ∩ {s < Ŝ}`; `B_n` increases
to `A₀ ∩ {s < Ŝ}` almost surely along the subsequence because `t_n ↓ s` and the hulls are right-continuous on the compact
support of `ψ` (`HullRightCont`); dominated convergence concludes.

## Main results

* `measurableSet_inter_ceil_eq`: the dyadic pieces of an event of a stopped σ-algebra;
* **`setIntegral_preStop_eq_of_tag`**: (K-pre) for a time-adapted reference.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace LocalExt

open Sec7 Sec4 LQGMetric Coupling

/-! ### Dyadic pieces -/

section Dyadic

theorem ceil_le_iff_le_dyadicTime (x : ℝ≥0) (n j : ℕ) :
    ⌈(2 : ℝ≥0) ^ n * x⌉₊ ≤ j ↔ x ≤ LawUnique.dyadicTime (n, j) := by
  rw [Nat.ceil_le, LawUnique.dyadicTime, le_div_iff₀ (pow_pos two_pos n), mul_comm]

theorem le_dyadicTime_ceil (x : ℝ≥0) (n : ℕ) : x ≤ LawUnique.dyadicTime (n, ⌈(2 : ℝ≥0) ^ n * x⌉₊) :=
  (ceil_le_iff_le_dyadicTime x n _).1 le_rfl

theorem lt_dyadicTime_ceil_succ (x : ℝ≥0) (n : ℕ) :
    x < LawUnique.dyadicTime (n, ⌈(2 : ℝ≥0) ^ n * x⌉₊ + 1) := by
  refine (le_dyadicTime_ceil x n).trans_lt ?_
  simp only [LawUnique.dyadicTime]
  gcongr
  exact_mod_cast Nat.lt_succ_self _

theorem dyadicTime_ceil_succ_le (x : ℝ≥0) (n : ℕ) :
    LawUnique.dyadicTime (n, ⌈(2 : ℝ≥0) ^ n * x⌉₊ + 1) ≤ x + 2 * (1 / 2 ^ n) := by
  have hpos : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
  have hk : (⌈(2 : ℝ≥0) ^ n * x⌉₊ : ℝ≥0) < 2 ^ n * x + 1 := Nat.ceil_lt_add_one zero_le
  simp only [LawUnique.dyadicTime]
  rw [div_le_iff₀ hpos]
  have : (x + 2 * (1 / 2 ^ n)) * 2 ^ n = 2 ^ n * x + 2 := by
    field_simp
  rw [this]
  push_cast
  calc (⌈(2 : ℝ≥0) ^ n * x⌉₊ : ℝ≥0) + 1 ≤ (2 ^ n * x + 1) + 1 := by gcongr
    _ = 2 ^ n * x + 2 := by ring

theorem tendsto_dyadicTime_ceil_succ (x : ℝ≥0) :
    Tendsto (fun n : ℕ => LawUnique.dyadicTime (n, ⌈(2 : ℝ≥0) ^ n * x⌉₊ + 1)) atTop (𝓝 x) := by
  have hup : Tendsto (fun n : ℕ => x + 2 * (1 / (2 : ℝ≥0) ^ n)) atTop (𝓝 x) := by
    have := (LawUnique.tendsto_one_div_two_pow.const_mul (2 : ℝ≥0)).const_add x
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun n => (lt_dyadicTime_ceil_succ x n).le) (fun n => dyadicTime_ceil_succ_le x n)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ}

/-- **The dyadic pieces of an event of a stopped σ-algebra**: `A₀ ∩ {⌈2ⁿ s⌉ = k}` is an event of `𝓖_{k/2ⁿ}`. -/
theorem measurableSet_inter_ceil_eq {s : Ω → ℝ≥0} (hs : IsStoppingTime 𝓖 fun ω => (s ω : WithTop ℝ≥0))
    {A₀ : Set Ω} (hA₀ : MeasurableSet[hs.measurableSpace] A₀) (n k : ℕ) :
    MeasurableSet[𝓖 (LawUnique.dyadicTime (n, k))] (A₀ ∩ {ω | ⌈(2 : ℝ≥0) ^ n * s ω⌉₊ = k}) := by
  have hle : ∀ j, {ω | ⌈(2 : ℝ≥0) ^ n * s ω⌉₊ ≤ j} =
      {ω | (s ω : WithTop ℝ≥0) ≤ ((LawUnique.dyadicTime (n, j) : ℝ≥0) : WithTop ℝ≥0)} := fun j => by
    ext ω
    simp only [mem_ofPred_eq, WithTop.coe_le_coe, ceil_le_iff_le_dyadicTime]
  have h1 : MeasurableSet[𝓖 (LawUnique.dyadicTime (n, k))] (A₀ ∩ {ω | ⌈(2 : ℝ≥0) ^ n * s ω⌉₊ ≤ k}) := by
    rw [hle]
    exact hA₀.2 _
  cases k with
  | zero =>
    have e : A₀ ∩ {ω | ⌈(2 : ℝ≥0) ^ n * s ω⌉₊ = 0} = A₀ ∩ {ω | ⌈(2 : ℝ≥0) ^ n * s ω⌉₊ ≤ 0} := by
      ext ω; simp only [mem_inter_iff, mem_ofPred_eq, nonpos_iff_eq_zero]
    rw [e]
    exact h1
  | succ j =>
    have e : A₀ ∩ {ω | ⌈(2 : ℝ≥0) ^ n * s ω⌉₊ = j + 1} =
        (A₀ ∩ {ω | ⌈(2 : ℝ≥0) ^ n * s ω⌉₊ ≤ j + 1}) \ {ω | ⌈(2 : ℝ≥0) ^ n * s ω⌉₊ ≤ j} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, Set.mem_sdiff, not_le]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.le⟩, by omega⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, by omega⟩
    rw [e]
    refine h1.diff ?_
    rw [hle]
    have hj : LawUnique.dyadicTime (n, j) ≤ LawUnique.dyadicTime (n, j + 1) := by
      simp only [LawUnique.dyadicTime]
      gcongr
      exact_mod_cast Nat.le_succ j
    exact 𝓖.mono hj _ (hs _)

end Dyadic

/-! ### (K-pre) -/

section Main

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {S : Ω → WithTop ℝ≥0}
  {h : Ω → DistOn upperHalfPlaneOpens}
  {Ωr : Type u} {mΩr : MeasurableSpace Ωr} {Pr : Measure Ωr} {𝓕r : Filtration ℝ≥0 mΩr}
  {Wr : ℝ≥0 → Ωr → ℝ} {VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ} {Br : ℝ≥0 → Ωr → ℝ} {ζr : Ωr → ℝ≥0∞}
  {hr' : Ωr → DistOn upperHalfPlaneOpens} {Gr : Set Ωr}

variable (xL xR) in
/-- **Time-adapted generation of a reference by its recorded history**: every event of the usual augmentation at a
rational time `q` agrees, almost surely on `{t < Ŝ}`, with an event of the reference history at the capped local stop
truncated at any rational `t > q`. -/
def IsTimeAdaptedRef (r : ℝ) (Gr : Set Ωr) (Pr : Measure Ωr) (𝓕r : Filtration ℝ≥0 mΩr) (Wr : ℝ≥0 → Ωr → ℝ)
    (VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ) (ζr : Ωr → ℝ≥0∞) : Prop :=
  ∀ (q t : ℚ≥0), q < t → ∀ A : Set Ωr, MeasurableSet[usualAugmentation 𝓕r Pr (q : ℝ≥0)] A →
    ∃ Γ : Set TwoSeedHist, MeasurableSet Γ ∧ ∀ᵐ ω ∂Pr, ((t : ℝ≥0) : WithTop ℝ≥0) < capStop r Gr ζr Wr ω →
      (ω ∈ A ↔ truncH t (refRecHist xL xR r Gr Wr VLr VRr ζr ω) ∈ Γ)

theorem isProbabilityMeasure_of_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {E : Measure (α × β)}
    {Q : Measure α} [IsProbabilityMeasure Q] (h : E.map Prod.fst = Q) : IsProbabilityMeasure E := by
  constructor
  rw [← Set.preimage_univ (f := (Prod.fst : α × β → α)), ← Measure.map_apply measurable_fst MeasurableSet.univ, h]
  exact measure_univ

/-- **(K-pre): the protected kernel before the local stop survives the extension**, for a time-adapted reference. -/
theorem setIntegral_preStop_eq_of_tag [IsProbabilityMeasure Q] [IsProbabilityMeasure Pr]
    (hr : 0 < r) (hL : -2 < seedSumL xL ρL) (hR : -2 < seedSumR xR ρR)
    (hc : IsStoppedSeedCoupling κ xL xR ρL ρR r Q W VL VR S h)
    (hC : IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => seedSumL xL ρL)
      (fun _ => seedSumR xR ρR) Pr 𝓕r Wr VLr VRr Br ζr hr')
    (hGm : MeasurableSet Gr) (hG0 : Pr Grᶜ = 0)
    (hG : ∀ ω ∈ Gr, IsGoodPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => seedSumL xL ρL) (fun _ => seedSumR xR ρR)
      Wr VLr VRr Br ζr ω)
    (hTAG : IsTimeAdaptedRef xL xR r Gr Pr 𝓕r Wr VLr VRr ζr)
    {E : Measure (Ω × Ωr)}
    (hE : IsRecordExtension Q Pr h (stRecHist xL xR W VL VR S) hr' (refRecHist xL xR r Gr Wr VLr VRr ζr) E)
    (U : Set ℂ) (s : Ωr → ℝ≥0) (hs : IsStoppingTime (usualAugmentation 𝓕r Pr) fun ω => (s ω : WithTop ℝ≥0))
    (hsafe : ∀ᵐ ω ∂Pr, (s ω : ℝ≥0∞) < ζr ω ∧ Disjoint U (fwdHull (fun r : ℝ => Wr r.toNNReal ω) (s ω)))
    (ψ : TestOn upperHalfPlaneOpens) (hψ : tsupport ψ ⊆ U) (A₀ : Set Ωr)
    (hA₀ : MeasurableSet[hs.measurableSpace] A₀) :
    ∫ p in Prod.snd ⁻¹' (A₀ ∩ {ω | (s ω : WithTop ℝ≥0) < capStop r Gr ζr Wr ω}),
        Complex.exp (Complex.I * (h p.1 ψ : ℂ)) ∂E =
      ∫ p in Prod.snd ⁻¹' (A₀ ∩ {ω | (s ω : WithTop ℝ≥0) < capStop r Gr ζr Wr ω}),
        Complex.exp (Complex.I * (hr' p.2 ψ : ℂ)) ∂E := by
  classical
  have hEp : IsProbabilityMeasure E := isProbabilityMeasure_of_map_fst hE.1
  have hsnd : E.map Prod.snd = Pr := hE.2.1
  obtain ⟨-, -, -, -, -, -, -, hhm, -⟩ := id hc
  obtain ⟨hXr, -⟩ := hC.2.2.2
  have hŜm : Measurable (capStop r Gr ζr Wr) := (isStoppingTime_capStop hXr hGm hG0 hG r).measurable'
  have hsm : Measurable fun ω => (s ω : WithTop ℝ≥0) := hs.measurable'
  set Dψ : Set TwoSeedHist := {y | Disjoint (tsupport ψ) (tsHull y)} with hDψdef
  have hDψ : MeasurableSet Dψ := measurableSet_disjoint_tsHull ψ.hasCompactSupport.isCompact
  set tt : ℕ → ℕ → ℚ≥0 := fun n k => dyadicQ (n, k + 1) with htt
  set Iev : ℕ → ℕ → Set Ωr := fun n k => A₀ ∩ {ω | ⌈(2 : ℝ≥0) ^ n * s ω⌉₊ = k} with hIevdef
  have hIev : ∀ n k, MeasurableSet[usualAugmentation 𝓕r Pr ((dyadicQ (n, k) : ℚ≥0) : ℝ≥0)] (Iev n k) := by
    intro n k
    rw [coe_dyadicQ]
    exact measurableSet_inter_ceil_eq hs hA₀ n k
  have hqt : ∀ n k, dyadicQ (n, k) < tt n k := by
    intro n k
    simp only [htt, dyadicQ]
    gcongr
    exact_mod_cast Nat.lt_succ_self k
  choose Γ hΓm hΓ using fun n k => hTAG (dyadicQ (n, k)) (tt n k) (hqt n k) (Iev n k) (hIev n k)
  set Ev : ℕ → ℕ → Set Ωr := fun n k => {ω | ((tt n k : ℝ≥0) : WithTop ℝ≥0) < capStop r Gr ζr Wr ω ∧
    truncH (tt n k) (refRecHist xL xR r Gr Wr VLr VRr ζr ω) ∈ Dψ} with hEvdef
  set Hv : ℕ → ℕ → Set Ωr := fun n k => {ω | ((tt n k : ℝ≥0) : WithTop ℝ≥0) < capStop r Gr ζr Wr ω ∧
    truncH (tt n k) (refRecHist xL xR r Gr Wr VLr VRr ζr ω) ∈ Γ n k ∩ Dψ} with hHvdef
  set P : ℕ → ℕ → Set Ωr := fun n k => Iev n k ∩ Ev n k with hPdef
  have hEvm : ∀ n k, MeasurableSet (Ev n k) := fun n k =>
    (setIntegral_cexp_trunc_ref (r := r) xL xR hL hR hr hC hGm hG0 hG (fun h' => seedSumL_eq_zero h')
      (fun h' => seedSumR_eq_zero h') (tt n k) hDψ ψ fun y hy => hy).1
  have hPm : ∀ n k, MeasurableSet (P n k) := fun n k =>
    ((usualAugmentation 𝓕r Pr).le _ _ (hIev n k)).inter (hEvm n k)
  have hPH : ∀ n k, ∀ᵐ ω ∂Pr, (ω ∈ P n k ↔ ω ∈ Hv n k) := by
    intro n k
    filter_upwards [hΓ n k] with ω hω
    simp only [hPdef, hHvdef, hEvdef, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hI, ht, hD⟩
      exact ⟨ht, (hω ht).1 hI, hD⟩
    · rintro ⟨ht, hΓω, hD⟩
      exact ⟨(hω ht).2 hΓω, ht, hD⟩
  have hcexp1 : Measurable fun p : Ω × Ωr => Complex.exp (Complex.I * (h p.1 ψ : ℂ)) :=
    Complex.continuous_exp.measurable.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp ((measurable_distOn_apply ψ).comp (hhm.comp measurable_fst))))
  have hcexp2 : Measurable fun p : Ω × Ωr => Complex.exp (Complex.I * (hr' p.2 ψ : ℂ)) :=
    Complex.continuous_exp.measurable.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp ((measurable_distOn_apply ψ).comp (hC.2.1.comp measurable_snd))))
  have hint1 : Integrable (fun p : Ω × Ωr => Complex.exp (Complex.I * (h p.1 ψ : ℂ))) E :=
    Integrable.of_bound hcexp1.aestronglyMeasurable 1
      (Eventually.of_forall fun p => (Complex.norm_exp_I_mul_ofReal _).le)
  have hint2 : Integrable (fun p : Ω × Ωr => Complex.exp (Complex.I * (hr' p.2 ψ : ℂ))) E :=
    Integrable.of_bound hcexp2.aestronglyMeasurable 1
      (Eventually.of_forall fun p => (Complex.norm_exp_I_mul_ofReal _).le)
  -- the identity on each piece
  have hpiece : ∀ n k, ∫ p in Prod.snd ⁻¹' P n k, Complex.exp (Complex.I * (h p.1 ψ : ℂ)) ∂E =
      ∫ p in Prod.snd ⁻¹' P n k, Complex.exp (Complex.I * (hr' p.2 ψ : ℂ)) ∂E := by
    intro n k
    have hset : (Prod.snd ⁻¹' P n k : Set (Ω × Ωr)) =ᵐ[E] (Prod.snd ⁻¹' Hv n k : Set (Ω × Ωr)) := by
      have h1 := hPH n k
      rw [← hsnd] at h1
      filter_upwards [ae_of_ae_map measurable_snd.aemeasurable h1] with p hp
      exact propext hp
    rw [setIntegral_congr_set hset, setIntegral_congr_set hset]
    exact setIntegral_trunc_eq hr hL hR hc hC hGm hG0 hG hE (tt n k) ((hΓm n k).inter hDψ) ψ
      fun y hy => hy.2
  -- the unions over `k`
  set B : ℕ → Set Ωr := fun n => ⋃ k, P n k with hBdef
  have hPdisj : ∀ n, Pairwise (Function.onFun Disjoint fun k => (Prod.snd ⁻¹' P n k : Set (Ω × Ωr))) := by
    intro n k k' hkk'
    refine Set.disjoint_left.2 fun p hp hp' => hkk' ?_
    exact hp.1.2.symm.trans hp'.1.2
  have hBint : ∀ n, ∫ p in Prod.snd ⁻¹' B n, Complex.exp (Complex.I * (h p.1 ψ : ℂ)) ∂E =
      ∫ p in Prod.snd ⁻¹' B n, Complex.exp (Complex.I * (hr' p.2 ψ : ℂ)) ∂E := by
    intro n
    simp only [hBdef, preimage_iUnion]
    rw [integral_iUnion (fun k => measurable_snd (hPm n k)) (hPdisj n) hint1.integrableOn,
      integral_iUnion (fun k => measurable_snd (hPm n k)) (hPdisj n) hint2.integrableOn]
    exact tsum_congr fun k => hpiece n k
  -- the target event
  set T : Set Ωr := A₀ ∩ {ω | (s ω : WithTop ℝ≥0) < capStop r Gr ζr Wr ω} with hTdef
  have hTm : MeasurableSet T := (hs.measurableSpace_le A₀ hA₀).inter (measurableSet_lt hsm hŜm)
  have hBT : ∀ n, B n ⊆ T := by
    intro n ω hω
    obtain ⟨k, hk⟩ := mem_iUnion.1 hω
    obtain ⟨⟨hA, hceil⟩, ht, -⟩ := hk
    refine ⟨hA, lt_of_le_of_lt ?_ ht⟩
    have h1 : s ω ≤ LawUnique.dyadicTime (n, k) := (ceil_le_iff_le_dyadicTime (s ω) n k).1 hceil.le
    have h2 : LawUnique.dyadicTime (n, k) ≤ ((tt n k : ℚ≥0) : ℝ≥0) := by
      rw [htt, coe_dyadicQ]
      simp only [LawUnique.dyadicTime]
      gcongr
      exact_mod_cast Nat.le_succ k
    exact WithTop.coe_le_coe.2 (h1.trans h2)
  have hGP : ∀ᵐ ω ∂Pr, ω ∈ Gr := ae_iff.2 (by exact hG0)
  have hconv : ∀ᵐ ω ∂Pr, ω ∈ T → ∀ᶠ n in atTop, ω ∈ B n := by
    filter_upwards [hGP, hsafe] with ω hω hsf hωT
    obtain ⟨hS, hSζ⟩ := capStop_ref hL hR hr hG hω
    set S₀ : ℝ≥0 := (capStop r Gr ζr Wr ω).untopD 0 with hS₀
    have hxS : s ω < S₀ := by
      have : (s ω : WithTop ℝ≥0) < capStop r Gr ζr Wr ω := hωT.2
      rw [hS] at this
      exact WithTop.coe_lt_coe.1 this
    set tn : ℕ → ℝ≥0 := fun n => LawUnique.dyadicTime (n, ⌈(2 : ℝ≥0) ^ n * s ω⌉₊ + 1) with htn
    have htnT : Tendsto tn atTop (𝓝 (s ω)) := tendsto_dyadicTime_ceil_succ (s ω)
    have hev1 : ∀ᶠ n in atTop, tn n < S₀ := htnT.eventually (gt_mem_nhds hxS)
    have hwc : ContinuousOn (fun t => Wr t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < ζr ω} := (hG ω hω).1.2.2.2.1
    have hev2 : ∀ᶠ n in atTop, Disjoint (tsupport ψ) (fwdHull (Ito.rpath fun t => Wr t ω) (tn n : ℝ)) :=
      HullRightCont.eventually_disjoint_fwdHull_rpath_of_tendsto hwc hsf.1
        ψ.hasCompactSupport.isCompact (tsupport_subset_H ψ) (hsf.2.mono_left hψ)
        (fun n => (lt_dyadicTime_ceil_succ (s ω) n).le) htnT
    filter_upwards [hev1, hev2] with n h1 h2
    refine mem_iUnion.2 ⟨⌈(2 : ℝ≥0) ^ n * s ω⌉₊, ⟨hωT.1, rfl⟩, ?_, ?_⟩
    · show ((tt n ⌈(2 : ℝ≥0) ^ n * s ω⌉₊ : ℝ≥0) : WithTop ℝ≥0) < capStop r Gr ζr Wr ω
      rw [htt, coe_dyadicQ, hS]
      exact WithTop.coe_lt_coe.2 h1
    · have htζ : ((tn n : ℝ≥0) : ℝ≥0∞) < ζr ω := lt_trans (by exact_mod_cast h1) hSζ
      have htS : ((tt n ⌈(2 : ℝ≥0) ^ n * s ω⌉₊ : ℝ≥0) : WithTop ℝ≥0) < capStop r Gr ζr Wr ω := by
        rw [htt, coe_dyadicQ, hS]
        exact WithTop.coe_lt_coe.2 h1
      show Disjoint (tsupport ψ) (tsHull (truncH (tt n ⌈(2 : ℝ≥0) ^ n * s ω⌉₊)
        (refRecHist xL xR r Gr Wr VLr VRr ζr ω)))
      rw [truncH_refRecHist xL xR htS]
      have hcoe : ((tt n ⌈(2 : ℝ≥0) ^ n * s ω⌉₊ : ℚ≥0) : ℝ≥0) = tn n := by rw [htt, coe_dyadicQ]
      rw [hcoe]
      exact disjoint_tsHull_tsOf (continuousOn_refState xL xR (hG ω hω) htζ) htζ hwc (fun _ _ => rfl)
        (tsupport_subset_H ψ) h2
  -- dominated convergence on `E`
  have hconvE : ∀ᵐ p ∂E, p.2 ∈ T → ∀ᶠ n in atTop, p.2 ∈ B n := by
    rw [← hsnd] at hconv
    exact ae_of_ae_map measurable_snd.aemeasurable hconv
  have hBm : ∀ n, MeasurableSet (Prod.snd ⁻¹' B n : Set (Ω × Ωr)) := fun n =>
    measurable_snd (MeasurableSet.iUnion fun k => hPm n k)
  have hlim : ∀ f : Ω × Ωr → ℂ, Measurable f → (∀ p, ‖f p‖ ≤ 1) →
      Tendsto (fun n => ∫ p in Prod.snd ⁻¹' B n, f p ∂E) atTop
        (𝓝 (∫ p in Prod.snd ⁻¹' T, f p ∂E)) := by
    intro f hf hf1
    simp_rw [← integral_indicator (hBm _), ← integral_indicator (measurable_snd hTm)]
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun n => (hf.indicator (hBm n)).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun p => ?_) ?_
    · by_cases hp : p ∈ Prod.snd ⁻¹' B n
      · rw [indicator_of_mem hp]; exact hf1 p
      · rw [indicator_of_notMem hp, norm_zero]; exact zero_le_one
    · filter_upwards [hconvE] with p hp
      by_cases hpT : p.2 ∈ T
      · rw [indicator_of_mem (show p ∈ Prod.snd ⁻¹' T from hpT)]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hp hpT] with n hn
        rw [indicator_of_mem (show p ∈ Prod.snd ⁻¹' B n from hn)]
      · rw [indicator_of_notMem (show p ∉ Prod.snd ⁻¹' T from hpT)]
        refine tendsto_const_nhds.congr fun n => ?_
        rw [indicator_of_notMem (show p ∉ Prod.snd ⁻¹' B n from fun hn => hpT (hBT n hn))]
  have h1 := hlim _ hcexp1 fun p => (Complex.norm_exp_I_mul_ofReal _).le
  have h2 := hlim _ hcexp2 fun p => (Complex.norm_exp_I_mul_ofReal _).le
  exact tendsto_nhds_unique h1 (h2.congr fun n => (hBint n).symm)

end Main

end LocalExt

end InteractingSLE
