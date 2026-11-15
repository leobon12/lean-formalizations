/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Prop418RangeGlue
import InteractingSLE.WangWu.Theorem425
import InteractingSLE.Spec.Sec2.Assembly2Entr
import InteractingSLE.Spec.Coupling.ResampleProjBridge

/-!
# Wang–Wu Proposition 4.18: the range identity and determination from the reverse-tip contact

Packet PROVE-WW-B10. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), proof of
Proposition 4.18 (text dump L1604–1653). The proof samples a forward line `α` and a reverse line `β` conditionally
independently given `h` and shows, for each finite positive stopping time `s` of `β`, that `α` passes through `β(s)`
(two-slit Corollary 4.8, the conformal transfer of `α` into `ℍ \ β[0, s]`, Lemma 2.11, transience). Then:

> "Apply this conclusion at a countable dense set of reverse times. The compactified forward range is closed and contains
> the corresponding dense subset of the reverse range. It therefore contains the entire reverse range. Interchange the
> curves to obtain the reverse inclusion. The two compactified ranges are equal. […] Lemma 4.1 makes the oriented forward
> range a function of `h`. Half-plane capacity determines the parameter of a simple Loewner trace, so the complete hull
> history is determined."

This file proves everything after the contact step, for the two-seed words with nonnegative weights (the words of
Proposition 4.18 that `LP.TwoSeedGraphInput 4` needs), on the frozen carriers:

* **`ReverseTipContactStatement`** — the contact step, a *named input* (not proved here): for every optional hull
  coupling of `SLE₄(r_L; r_R)`, `r_L, r_R ≥ 0`, every optional hull coupling of the reflected word `SLE₄(r_R; r_L)`
  whose reflected field `−h₂ ∘ R` has the law of `h`, and every regular conditional law `k` of the reverse killed history
  given the reflected field, on the glued space `P ⊗ k(h)` the forward seed line passes almost surely through the
  reverse point `R(β(s))` for each rational `s > 0`.
* **`ae_hitCode_seedLine_eq_revLine`** (the range identity, from the contact step applied twice, the interchange being
  `glue_swap_law`): almost surely on the glued space, the forward line and the reflected reverse line have the same
  hitting code, i.e. the same range.
* **`isFieldDeterminedHistory_twoSeed_of_contact`**: the killed history of every such forward coupling is
  field-determined (`IsMarkedChain.isFieldDeterminedHistory_of_glue_hitCode`: Lemma 4.1 and Lusin–Souslin).
* **`hasFieldDeterminedHistories_twoSeed_of_contact`**, **`twoSeed_of_nonneg_of_contact`**: the nonnegative two-seed
  part of `LP.TwoSeedGraphInput 4` (determination of every coupling, and the trace), from the contact step alone.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

universe u v

namespace InteractingSLE.WangWu

open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open LawUnique

/-! ### The contact step (named input) -/

/-- **The reverse-tip contact step of Proposition 4.18** (proof, text dump L1607–1641; PROVE-WW-B9's steps S2–S5), the
remaining input of Proposition 4.18's determination. Let `(h, W, …)` be an optional hull coupling of `SLE₄(r_L; r_R)`
(`r_L, r_R ≥ 0`) and `(h₂, W₂, …)` one of the reflected word `SLE₄(r_R; r_L)` whose reflected field `−h₂ ∘ R`,
`R(z) = −1/z`, has the law of `h` (the reverse line is the level line of `−h` from `∞` to `0`). Let `k` be a regular
conditional law of the reverse killed history given the reflected field. On the glued space `P ⊗ k(h)` (the forward
coupling and a reverse line sampled conditionally independently given `h`), for each rational `s > 0` the forward seed
line almost surely passes through the reverse point `R(β(s))` (`revLine`, read from the glued reverse history). -/
def ReverseTipContactStatement : Prop :=
  ∀ (rL rR : ℝ), 0 ≤ rL → 0 ≤ rR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
      (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (h : Ω → DistOn upperHalfPlaneOpens)
      (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
      {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
      (𝓕₂ : Filtration ℝ≥0 mΩ₂) (W₂ : ℝ≥0 → Ω₂ → ℝ) (VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ)
      (ζ₂ : Ω₂ → ℝ≥0∞) (h₂ : Ω₂ → DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR) (fun _ => rL) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ →
      P.map h = P₂.map (fun ω => reflectField (h₂ ω)) →
      ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k],
        P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
          P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k →
        ∀ s : ℚ, 0 < s → ∀ᵐ p ∂(glueMeasure P k h hC.2.1), revLine p.2 s ∈ arcRange (seedLine ζ W p.1)

/-! ### Transfer of almost sure properties to glued spaces -/

section Transfer

variable {Ω α β : Type*} {mΩ : MeasurableSpace Ω} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → α}

theorem ae_glue_fst (κ : Kernel α β) [IsMarkovKernel κ] (hX : Measurable X) {Q : Ω → Prop}
    (hQ : ∀ᵐ ω ∂μ, Q ω) : ∀ᵐ p ∂(glueMeasure μ κ X hX), Q p.1 := by
  have e := glueMeasure_fst (μ := μ) κ hX
  rw [← e] at hQ
  exact ae_of_ae_map measurable_fst.aemeasurable hQ

/-- **The glued sample has the law of the reverse variable**: if `k` is a conditional law of `D₂` given `X₂` and `X`,
`X₂` have the same law, the glued sample of `k(X)` has the law of `D₂`. -/
theorem glueMeasure_map_snd_eq {Ω₂ : Type*} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {X₂ : Ω₂ → α} {D₂ : Ω₂ → β} (hX : Measurable X) (hX₂ : Measurable X₂) (hD₂ : Measurable D₂)
    (hlaw : μ.map X = P₂.map X₂) (k : Kernel α β) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (X₂ ω, D₂ ω)) = P₂.map X₂ ⊗ₘ k) :
    (glueMeasure μ k X hX).map Prod.snd = P₂.map D₂ := by
  ext s hs
  rw [Measure.map_apply measurable_snd hs, Measure.map_apply hD₂ hs]
  have e1 : (Prod.snd ⁻¹' s : Set (Ω × β)) = univ ×ˢ s := by ext; simp
  rw [e1, glueMeasure_apply_prod k hX MeasurableSet.univ hs, Measure.restrict_univ,
    ← lintegral_map (k.measurable_coe hs) hX, hlaw, ← setLIntegral_univ,
    ← Measure.compProd_apply_prod MeasurableSet.univ hs, ← hk, Measure.map_apply (hX₂.prodMk hD₂)
    (MeasurableSet.univ.prod hs)]
  congr 1
  ext; simp

theorem ae_glue_snd {Ω₂ : Type*} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {X₂ : Ω₂ → α} {D₂ : Ω₂ → β} (hX : Measurable X) (hX₂ : Measurable X₂) (hD₂ : Measurable D₂)
    (hlaw : μ.map X = P₂.map X₂) (k : Kernel α β) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (X₂ ω, D₂ ω)) = P₂.map X₂ ⊗ₘ k) {S : Set β} (hS : MeasurableSet S)
    (hQ : ∀ᵐ ω ∂P₂, D₂ ω ∈ S) : ∀ᵐ p ∂(glueMeasure μ k X hX), p.2 ∈ S := by
  have h1 : ∀ᵐ y ∂(P₂.map D₂), y ∈ S := (ae_map_iff hD₂.aemeasurable hS).2 hQ
  rw [← glueMeasure_map_snd_eq hX hX₂ hD₂ hlaw k hk] at h1
  exact ae_of_ae_map measurable_snd.aemeasurable h1

end Transfer

/-! ### Approximation by rational times -/

section Near

/-- `z` is a limit of values of `γ` at nonnegative rational times. -/
def NearRat (z : ℂ) (γ : ℝ → ℂ) : Prop := ∀ m : ℕ, ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ ‖z - γ q‖ < 1 / ((m : ℝ) + 1)

/-- A point of the range of a curve continuous on `[0, ∞)` is a limit of its values at nonnegative rational times. -/
theorem nearRat_of_mem_arcRange {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Ici 0)) {z : ℂ} (hz : z ∈ arcRange γ) :
    NearRat z γ := by
  obtain ⟨s, hs, rfl⟩ := hz
  intro m
  have hr : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  obtain ⟨q, hq0, -, hq⟩ := exists_rat_mem_of_continuousOn (t := s + 1) hγ
    (isOpen_ball (x := γ s) (ε := 1 / ((m : ℝ) + 1)))
    ⟨mem_Ici.1 hs, by linarith⟩ (by linarith) (mem_ball_self hr)
  refine ⟨q, hq0, ?_⟩
  rw [mem_ball, dist_eq_norm, norm_sub_rev] at hq
  exact hq

/-- The pairs (forward history, reverse history) for which every reflected forward point at a positive rational time
is a limit of reverse points at rational times. -/
def NearSet : Set (HistorySpace 1 1 × HistorySpace 1 1) :=
  {xy | ∀ t : ℚ, 0 < t → NearRat (revLine xy.1 t) (histLine xy.2)}

theorem measurableSet_nearSet : MeasurableSet NearSet := by
  refine measurableSet_setOfPred.2 (Measurable.forall fun t => Measurable.imp measurable_const
    (Measurable.forall fun m => Measurable.exists fun q => Measurable.and measurable_const ?_))
  exact measurableSet_setOfPred.1 (measurableSet_lt
    (((measurable_revLine (t : ℝ)).comp measurable_fst).sub ((measurable_histLine (q : ℝ)).comp measurable_snd)).norm
    measurable_const)

/-- Two curves whose rational-time hitting events agree on every rational disc have equal hitting codes. -/
theorem hitCode_eq_of_iff {γ ρ : ℝ → ℂ}
    (h : ∀ i, (∃ q : ℚ, 0 ≤ (q : ℝ) ∧ γ q ∈ ratBall i) ↔ (∃ q : ℚ, 0 ≤ (q : ℝ) ∧ ρ q ∈ ratBall i)) :
    hitCode γ = hitCode ρ := by
  funext i
  unfold hitCode
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ((h i).1 h1) h2
  · exact absurd ((h i).2 h2) h1
  · rfl

/-- **The deterministic range identity.** Let `γ` be a proper arc and `y` a history whose reflected line `ρ = R ∘ β`
(`revLine y`) starts at `0`. If every reflected reverse point at a positive rational time lies on `γ`, and every
reflected forward point `R(γ(t))` at a positive rational time is a limit of reverse points at rational times, then `γ`
and `ρ` have the same hitting code. -/
theorem hitCode_eq_of_contact {γ : ℝ → ℂ} (hγ : IsProperArc γ) {y : HistorySpace 1 1} (hy0 : revLine y 0 = 0)
    (h₁ : ∀ s : ℚ, 0 < s → revLine y s ∈ arcRange γ)
    (h₂ : ∀ t : ℚ, 0 < t → NearRat (negInv (γ t)) (histLine y)) : hitCode γ = hitCode (revLine y) := by
  refine hitCode_eq_of_iff fun i => ⟨?_, ?_⟩
  · rintro ⟨q, hq0, hq⟩
    rcases hq0.lt_or_eq with hqpos | hq0'
    · -- a forward point at a positive rational time: approximate it by reflected reverse points
      have hγq : γ q ∈ H := hγ.mem_H q hqpos
      have hz : negInv (γ q) ≠ 0 := by
        unfold negInv
        exact neg_ne_zero.2 (inv_ne_zero (Sec7.StripSysField.mem_H_ne_zero hγq))
      obtain ⟨ε, hε, hεb⟩ := Metric.isOpen_iff.1 isOpen_ball (γ q) hq
      have hc := continuousAt_negInv hz
      rw [Metric.continuousAt_iff] at hc
      obtain ⟨δ, hδ, hδc⟩ := hc ε hε
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
      obtain ⟨q', hq'0, hq'⟩ := h₂ q (by exact_mod_cast hqpos) m
      refine ⟨q', hq'0, hεb ?_⟩
      have hd : dist (histLine y q') (negInv (γ q)) < δ := by
        rw [dist_eq_norm, norm_sub_rev]; exact hq'.trans hm
      have := hδc hd
      rwa [negInv_negInv'] at this
    · -- the time `0`: both curves start at `0`
      have e : (q : ℝ) = 0 := hq0'.symm
      rw [e, hγ.zero] at hq
      exact ⟨0, by simp, by simpa [hy0] using hq⟩
  · rintro ⟨q, hq0, hq⟩
    rcases hq0.lt_or_eq with hqpos | hq0'
    · have hmem := h₁ q (by exact_mod_cast hqpos)
      obtain ⟨j, hji, hj⟩ := (arcRange_inter_nonempty_iff_hitCode hγ.cont isOpen_ball).1 ⟨_, hmem, hq⟩
      unfold hitCode at hj
      split_ifs at hj with hex
      · obtain ⟨q'', hq''0, hq''⟩ := hex
        exact ⟨q'', hq''0, hji hq''⟩
      · norm_num at hj
    · have e : (q : ℝ) = 0 := hq0'.symm
      rw [e, hy0] at hq
      exact ⟨0, by simp, by simpa [hγ.zero] using hq⟩

end Near

/-! ### The range identity and determination -/

section Main

variable {rL rR : ℝ}

/-- On a nonnegative two-seed marked chain, almost surely the seed line is a proper arc and is the line read from the
killed history. -/
theorem ae_good_twoSeed {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    (hE : IsMarkedChain LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, IsProperArc (seedLine ζ W ω) ∧ histLine (killedHistory W VL VR ζ ω) = seedLine ζ W ω := by
  filter_upwards [IsMarkedChain.ae_seedLine isOrderedForceWord_twoSeed (hasNonnegCumWeights_twoSeed hL hR) hE,
    IsIntegratedSLEEvolution.ae_continuousOn_driving hE] with ω h1 h2
  have hc : Continuous fun t => W t ω :=
    continuousOn_univ.1 (h2.1.mono fun t _ => show (t : ℝ≥0∞) < ζ ω by rw [h1.1]; exact ENNReal.coe_lt_top)
  exact ⟨h1.2.2.2.1, histLine_killedHistory h1.1 hc⟩

/-- **Proposition 4.18, the range identity** ("the two compactified ranges are equal"), from the contact step applied
to both curves: almost surely on the glued space, the forward seed line and the reflected reverse line have the same
hitting code. The interchange of the curves is `glue_swap_law`. -/
theorem ae_hitCode_seedLine_eq_revLine (hcon : ReverseTipContactStatement.{u}) (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 mΩ₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
    {ζ₂ : Ω₂ → ℝ≥0∞} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR) (fun _ => rL) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂
      h₂)
    (hlaw : P.map h = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k) :
    ∀ᵐ p ∂(glueMeasure P k h hC.2.1), hitCode (seedLine ζ W p.1) = hitCode (revLine p.2) := by
  obtain ⟨hX, -⟩ := hC.2.2.2
  obtain ⟨hX₂, -⟩ := hC₂.2.2.2
  have hD := measurable_killedHistory hX
  have hD₂ := measurable_killedHistory hX₂
  have hh : Measurable h := hC.2.1
  have hh₂ : Measurable h₂ := hC₂.2.1
  have hRh : Measurable fun ω => reflectField (h ω) := measurable_reflectField.comp hh
  have hRh₂ : Measurable fun ω => reflectField (h₂ ω) := measurable_reflectField.comp hh₂
  set k₁ := condDistrib (killedHistory W VL VR ζ) h P with hk₁def
  have hk₁ : P.map (fun ω => (h ω, killedHistory W VL VR ζ ω)) = P.map h ⊗ₘ k₁ :=
    (compProd_map_condDistrib hh.aemeasurable hD.aemeasurable).symm
  set k' := k₁.comap reflectField measurable_reflectField with hk'def
  have hk' : P.map (fun ω => (reflectField (h ω), killedHistory W VL VR ζ ω)) =
      P.map (fun ω => reflectField (h ω)) ⊗ₘ k' := by
    have hm : Measurable (Prod.map reflectField (id : HistorySpace 1 1 → HistorySpace 1 1)) :=
      measurable_reflectField.prodMap measurable_id
    rw [show (fun ω => (reflectField (h ω), killedHistory W VL VR ζ ω)) =
        Prod.map reflectField id ∘ (fun ω => (h ω, killedHistory W VL VR ζ ω)) from rfl,
      ← Measure.map_map hm (hh.prodMk hD), hk₁,
      map_prodMap_compProd_of_involutive k₁ measurable_reflectField reflectField_reflectField,
      Measure.map_map measurable_reflectField hh]
    rfl
  have hlaw' : P₂.map h₂ = P.map (fun ω => reflectField (h ω)) := by
    have e := congrArg (fun μ : Measure (DistOn upperHalfPlaneOpens) => μ.map reflectField) hlaw
    rw [Measure.map_map measurable_reflectField hh, Measure.map_map measurable_reflectField hRh₂] at e
    rw [show (reflectField ∘ fun ω => reflectField (h₂ ω)) = h₂ from
      funext fun ω => reflectField_reflectField _] at e
    exact e.symm
  -- (a) the forward line is a proper arc, read from the forward history
  have hgood := ae_glue_fst (μ := P) k hh (ae_good_twoSeed hL hR hC.1)
  -- (b) the reflected reverse sample starts at `0`
  have hS0 : MeasurableSet {y : HistorySpace 1 1 | revLine y 0 = 0} :=
    measurableSet_eq_fun (measurable_revLine 0) measurable_const
  have h0 : ∀ᵐ p ∂(glueMeasure P k h hh), revLine p.2 0 = 0 := by
    refine ae_glue_snd hh hRh₂ hD₂ hlaw k hk hS0 ?_
    filter_upwards [ae_good_twoSeed hR hL hC₂.1] with ω hω
    show revLine _ 0 = 0
    rw [revLine, hω.2, hω.1.zero]
    simp [negInv]
  -- (c) the contact step for the forward line
  have hc₁ : ∀ᵐ p ∂(glueMeasure P k h hh), ∀ s : ℚ, 0 < s → revLine p.2 s ∈ arcRange (seedLine ζ W p.1) := by
    rw [ae_all_iff]
    intro s
    by_cases hs : 0 < s
    · filter_upwards [hcon rL rR hL hR P 𝓕 W VL VR B ζ h hC P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hC₂ hlaw k hk s hs]
        with p hp _ using hp
    · exact Eventually.of_forall fun p h' => absurd h' hs
  -- (d) the contact step for the reverse line, carried over by the interchange
  have hc₂ : ∀ᵐ p ∂(glueMeasure P k h hh), (killedHistory W VL VR ζ p.1, p.2) ∈ NearSet := by
    have hglue2 : ∀ᵐ p ∂(glueMeasure P₂ k' h₂ hh₂), (p.2, killedHistory W₂ VL₂ VR₂ ζ₂ p.1) ∈ NearSet := by
      have hg2 := ae_glue_fst (μ := P₂) k' hh₂ (ae_good_twoSeed hR hL hC₂.1)
      have hct : ∀ᵐ p ∂(glueMeasure P₂ k' h₂ hh₂), ∀ t : ℚ, 0 < t →
          revLine p.2 t ∈ arcRange (seedLine ζ₂ W₂ p.1) := by
        rw [ae_all_iff]
        intro t
        by_cases ht : 0 < t
        · filter_upwards [hcon rR rL hR hL P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hC₂ P 𝓕 W VL VR B ζ h hC hlaw' k' hk' t ht]
            with p hp _ using hp
        · exact Eventually.of_forall fun p h' => absurd h' ht
      filter_upwards [hg2, hct] with p hp hpt
      show ∀ t : ℚ, 0 < t → NearRat (revLine p.2 t) (histLine (killedHistory W₂ VL₂ VR₂ ζ₂ p.1))
      intro t ht
      rw [hp.2]
      exact nearRat_of_mem_arcRange hp.1.cont (hpt t ht)
    have hsw := glue_swap_law hh hh₂ hD hD₂ hlaw k hk k₁ hk₁
    have h1 : ∀ᵐ z ∂((glueMeasure P₂ k' h₂ hh₂).map (fun p => (p.2, killedHistory W₂ VL₂ VR₂ ζ₂ p.1))),
        z ∈ NearSet :=
      (ae_map_iff (measurable_snd.prodMk (hD₂.comp measurable_fst)).aemeasurable measurableSet_nearSet).2 hglue2
    rw [← hsw] at h1
    exact ae_of_ae_map ((hD.comp measurable_fst).prodMk measurable_snd).aemeasurable h1
  filter_upwards [hgood, h0, hc₁, hc₂] with p hp hp0 hp1 hp2
  refine hitCode_eq_of_contact hp.1 hp0 hp1 fun t ht => ?_
  have e := hp2 t ht
  rwa [revLine, hp.2] at e

/-- **Proposition 4.18, determination, for the nonnegative two-seed words, from the contact step**: the killed driving
history of every optional hull coupling of `SLE₄(r_L; r_R)`, `r_L, r_R ≥ 0`, is field-determined, given one coupling of
the reflected word with the reflected field law and a regular conditional law of its history. -/
theorem isFieldDeterminedHistory_twoSeed_of_contact (hcon : ReverseTipContactStatement.{u}) (hL : 0 ≤ rL)
    (hR : 0 ≤ rR) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 mΩ₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
    {ζ₂ : Ω₂ → ℝ≥0∞} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR) (fun _ => rL) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂
      h₂)
    (hlaw : P.map h = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k) :
    LP.IsFieldDeterminedHistory P h W VL VR ζ :=
  IsMarkedChain.isFieldDeterminedHistory_of_glue_hitCode isOrderedForceWord_twoSeed
    (hasNonnegCumWeights_twoSeed hL hR) hC.1 hC.2.1 k (L := fun y => hitCode (revLine y))
    (measurable_hitCode.comp (measurable_pi_iff.2 measurable_revLine))
    (ae_hitCode_seedLine_eq_revLine hcon hL hR hC hC₂ hlaw k hk)

/-- **A reference coupling with a field-determined history** for each nonnegative two-seed word, from the contact
step: Theorem 1.1's coupling of `SLE₄(r_L; r_R)`, glued with Theorem 1.1's coupling of `SLE₄(r_R; r_L)` through the
regular conditional law of its history given the reflected field. -/
theorem exists_reference_twoSeed_of_contact (hcon : ReverseTipContactStatement.{v}) (hL : 0 ≤ rL)
    (hR : 0 ≤ rR) :
    ∃ (Ω : Type v) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ)
      (VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (h : Ω → DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h ∧
        LP.IsFieldDeterminedHistory P h W VL VR ζ := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, h, hC⟩ :=
    Coupling.exists_isOptionalHullCoupling_of_thm22.{v} (κ := 4) (ρL := fun _ : Fin 1 => rL)
      (ρR := fun _ : Fin 1 => rR) (by norm_num) isOrderedForceWord_twoSeed
      (exists_isIntegratedSLEEvolution_assembled (by norm_num) isOrderedForceWord_twoSeed)
  obtain ⟨Ω₂, mΩ₂, P₂, hP₂, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, h₂, hC₂⟩ :=
    Coupling.exists_isOptionalHullCoupling_of_thm22.{v} (κ := 4) (ρL := fun _ : Fin 1 => rR)
      (ρR := fun _ : Fin 1 => rL) (by norm_num) isOrderedForceWord_twoSeed
      (exists_isIntegratedSLEEvolution_assembled (by norm_num) isOrderedForceWord_twoSeed)
  have hlaw : P.map h = P₂.map (fun ω => reflectField (h₂ ω)) :=
    map_reflectField_eq_twoSeed ⟨hC.2.1, hC.2.2.1⟩ ⟨hC₂.2.1, hC₂.2.2.1⟩
  obtain ⟨hX₂, -⟩ := hC₂.2.2.2
  have hRh₂ : Measurable fun ω => reflectField (h₂ ω) := measurable_reflectField.comp hC₂.2.1
  have hk := (compProd_map_condDistrib (μ := P₂) hRh₂.aemeasurable (measurable_killedHistory hX₂).aemeasurable).symm
  exact ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, h, hC,
    isFieldDeterminedHistory_twoSeed_of_contact hcon hL hR hC hC₂ hlaw _ hk⟩

/-- **The nonnegative two-seed part of `LP.TwoSeedGraphInput 4`, from the contact step** (Proposition 4.18's words):
every optional hull coupling of `SLE₄(r_L; r_R)`, `r_L, r_R ≥ 0`, has a field-determined killed history, and every
such evolution has a continuous generating trace. -/
theorem twoSeed_of_nonneg_of_contact (hcon : ReverseTipContactStatement.{v}) (hL : 0 ≤ rL) (hR : 0 ≤ rR) :
    LP.HasFieldDeterminedHistories.{u} 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) ∧
      ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
        (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ)
        (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
        IsIntegratedSLEEvolution 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ →
          ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η :=
  twoSeed_of_nonneg.{u, v} hL hR (exists_reference_twoSeed_of_contact.{v} hcon hL hR)

/-- `LP.HasFieldDeterminedHistories 4` for the nonnegative two-seed words, from the contact step. -/
theorem hasFieldDeterminedHistories_twoSeed_of_contact (hcon : ReverseTipContactStatement.{v}) (hL : 0 ≤ rL)
    (hR : 0 ≤ rR) :
    LP.HasFieldDeterminedHistories.{u} 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) :=
  (twoSeed_of_nonneg_of_contact.{u, v} hcon hL hR).1

/-- **`LP.TwoSeedGraphInput 4` (Wang–Wu Proposition 4.24) split by the sign of the weights**: the nonnegative words
from the contact step of Proposition 4.18; the words with a negative weight in `(−2, 0)` (determination) and the
boundary-hitting trace (`Theorem18.TwoSeedHittingStatement 4`) as the remaining inputs. -/
theorem twoSeedGraphInput_four_of_contact (hcon : ReverseTipContactStatement.{v})
    (hneg : ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < 0 ∨ rR < 0) →
      LP.HasFieldDeterminedHistories.{u} 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR))
    (hhit : Theorem18.TwoSeedHittingStatement.{u} 4) : LP.TwoSeedGraphInput.{u} 4 := by
  refine twoSeedGraphInput_four (fun rL rR hL hR => ?_) hhit
  by_cases hs : rL < 0 ∨ rR < 0
  · exact hneg rL rR hL hR hs
  · simp only [not_or, not_lt] at hs
    exact hasFieldDeterminedHistories_twoSeed_of_contact.{u, v} hcon hs.1 hs.2

end Main

end InteractingSLE.WangWu
