/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71BLife
import InteractingSLE.Spec.Sec7.Lemma71Reduce
import InteractingSLE.Spec.Coupling.MartMeans2Lemma71

/-!
# Lemma 7.1: the terminal capacity of the mapped segment is infinite

Packet PROVE-LEMMA71B. Specification, proof of Lemma 7.1 (`source/spec/p193-240.md` L604, p. 225): "Its terminal
capacity cannot be finite. Otherwise the globally defined admissible two-seed driving process would have a bounded
driver on that finite interval, and the elementary Loewner hull bounds would put the entire mapped prefix in a
bounded rectangle, contrary to its limit at `∞`."

## Main results

* **`ae_eq_top_of_hasMartingaleMeansBefore`**: a two-seed driver with weights `> −2`, continuous and adapted on
  `[0, T)`, whose coupling means are local martingales before `min (swallowTime z) T`, and which is unbounded near
  `T` when `T < ∞`, has `T = ∞` almost surely. (Theorem 2.4's localization gives Doob's bound on the martingale part
  up to the localizing times, uniformly in the level; a bounded martingale part bounds the two-seed driver,
  `abs_le_twoSeedBound`; so the driver could not be unbounded at a finite `T`.)
* `forall_abs_le_of_fwdHull_eq`, `unbounded_of_fwdHull_eq`: the elementary hull bound — a driver bounded on `[0, T)`,
  `T < ∞`, would keep every filled prefix of a path tending to `∞` in a bounded set.
* `Lemma71KilledSegmentStatement` (**named input**, the killed form of `Lemma71MappedSegmentStatement`): the mapped
  segment's driver is only given up to its terminal capacity time `T` ("a continuous Loewner driver up to the
  terminal capacity time of `ψ(η_C)`", Remark 6.14, p. 218), with the coupling means local martingales before
  `min (swallowTime z) T`, in a filtration satisfying the usual conditions.
* **`lemma71MappedSegmentStatement_of_killed`**: `Lemma71MappedSegmentStatement` from the killed form, and
  `lemma71TraceReferenceStatement_of_killed`: `Sec7.Lemma71TraceReferenceStatement` from it. Conditional helpers; they
  replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

universe v

namespace InteractingSLE.Sec7.Lemma71B

open MartChar MartChar.RealFlow Coupling

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### The killing time is infinite -/

section Top

variable {P : Measure Ω} [IsProbabilityMeasure P] {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous]
  {κ rL rR : ℝ} {T : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}

/-- **The killing time of the two-seed driver is infinite almost surely** (proof of Lemma 7.1, p. 225, "Its
terminal capacity cannot be finite"). Let `ρᴸ, ρᴿ > −2`, let `W` be continuous on `[0, T)` with `W₀ = 0`, adapted
before `T` in a right-continuous filtration whose time-zero σ-algebra contains the null sets, with the coupling means
of the two-seed word local martingales before `min (swallowTime z) T`, and almost surely unbounded near `T` when
`T < ∞`. Then `T = ∞` almost surely. -/
theorem ae_eq_top_of_hasMartingaleMeansBefore (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR)
    (hm : HasMartingaleMeansBefore κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓖 W T)
    (hW0 : ∀ ω, W 0 ω = 0) (hc : ∀ ω, ContinuousOn (fun s => W s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < T ω})
    (hWa : AdaptedBefore 𝓖 T W) (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s)
    (hunb : ∀ᵐ ω ∂P, T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω|) :
    ∀ᵐ ω ∂P, T ω = ⊤ := by
  classical
  set Bad := {ω | ¬ (T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω|)} with hBad
  have hBad0 : P Bad = 0 := ae_iff.1 hunb
  set G := (toMeasurable P Bad)ᶜ with hGdef
  have hGc : P Gᶜ = 0 := by rw [hGdef, compl_compl, measure_toMeasurable]; exact hBad0
  have hG : MeasurableSet[𝓖 0] G :=
    (hnull _ (measurableSet_toMeasurable P Bad) (by rw [measure_toMeasurable]; exact hBad0)).compl
  have hunbG : ∀ ω, ω ∈ G → T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω| := by
    intro ω hω
    by_contra h
    exact hω (subset_toMeasurable P Bad h)
  -- for each `K`, the event `{ω ∈ G, T ω < K}` is null
  have hK : ∀ K : ℕ, P {ω | ω ∈ G ∧ T ω < K} = 0 := by
    intro K
    have hK1 : 0 < 1 + κ * K := by positivity
    have hle : ∀ c : ℝ, 0 < c →
        P {ω | ω ∈ G ∧ T ω < K} ≤ ENNReal.ofReal ((1 + κ * K) / (2 * c)) := by
      intro c hcpos
      set A : ℕ → Set Ω := fun n => {ω | c ≤ ⨆ i : Set.Iic (K : ℝ≥0),
        ‖stoppedProcess (sMart rL rR W T G n) (sTau W T G K n) i ω‖} with hAdef
      have hA : ∀ n, P (A n) ≤ ENNReal.ofReal ((1 + κ * K) / (2 * c)) := fun n => by
        rw [← ofReal_measureReal (measure_ne_top P (A n))]
        exact ENNReal.ofReal_le_ofReal (measureReal_le_sMart hκ hm hW0 hc hWa hG hGc hunbG K n hcpos)
      set D : ℕ → Set Ω := fun N => ⋂ n, ⋂ (_ : N ≤ n), A n with hDdef
      have hDmono : Monotone D := fun N N' hNN' ω hω => by
        simp only [hDdef, mem_iInter] at hω ⊢
        exact fun n hn => hω n (hNN'.trans hn)
      have hsub : {ω | ω ∈ G ∧ T ω < K} ⊆ ⋃ N, D N := by
        rintro ω ⟨hω, hTK⟩
        by_contra hnot
        simp only [hDdef, mem_iUnion, mem_iInter, not_exists, not_forall] at hnot
        have hTne : T ω ≠ ⊤ := ne_top_of_lt hTK
        obtain ⟨s, hs, hlt⟩ := hunbG ω hω hTne (twoSeedBound rL rR K c)
        have hsK : s ≤ (K : ℝ≥0) := by
          have : s < (K : ℝ≥0) := by exact_mod_cast hs.trans hTK
          exact this.le
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (eventually_le_sTau hW0 hc hunbG hω hs hsK)
        obtain ⟨n, hNn, hn⟩ := hnot N
        exact absurd (abs_le_of_not_le_iSup hL hR hW0 hc hunbG K n hω hn (hN n hNn)) (not_le.2 hlt)
      calc P {ω | ω ∈ G ∧ T ω < K} ≤ P (⋃ N, D N) := measure_mono hsub
        _ = ⨆ N, P (D N) := hDmono.measure_iUnion
        _ ≤ _ := iSup_le fun N => (measure_mono (iInter₂_subset N le_rfl)).trans (hA N)
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
    have hε' : (0 : ℝ) < ε := hε
    have h := hle ((1 + κ * K) / (2 * ε)) (by positivity)
    have heq : (1 + κ * K) / (2 * ((1 + κ * K) / (2 * (ε : ℝ)))) = ε := by
      field_simp
    rw [heq, ENNReal.ofReal_coe_nnreal] at h
    rw [zero_add]
    exact h
  rw [ae_iff]
  refine measure_mono_null (t := Gᶜ ∪ ⋃ K : ℕ, {ω | ω ∈ G ∧ T ω < K}) ?_
    (measure_union_null hGc (measure_iUnion_null hK))
  intro ω hω
  by_cases hωG : ω ∈ G
  · right
    obtain ⟨K, hK⟩ := ENNReal.exists_nat_gt hω
    exact mem_iUnion.2 ⟨K, hωG, hK⟩
  · left
    exact hωG

end Top

/-! ### The elementary hull bound -/

section Hull

/-- **A driver bounded on `[0, T)` keeps the hulls before `T` in a ball** (the elementary Loewner hull bound): if
`|W| ≤ C` on `[0, T)` and `s < T`, then every point of `K_s` has norm at most `C + 3√T`. -/
theorem norm_le_of_mem_fwdHull_killed {w : ℝ≥0 → ℝ} {T : ℝ≥0}
    (hc : ContinuousOn w {s : ℝ≥0 | (s : ℝ≥0∞) < T}) {C : ℝ}
    (hC : ∀ s : ℝ≥0, (s : ℝ≥0∞) < T → |w s| ≤ C) {s : ℝ≥0} (hs : s < T) {z : ℂ}
    (hz : z ∈ QuantumZipper.fwdHull (fun r : ℝ => w r.toNNReal) s) : ‖z‖ ≤ C + 3 * Real.sqrt T := by
  obtain ⟨s', hss', hs'T⟩ := exists_between hs
  -- the driver frozen after `s'`
  set wf : ℝ → ℝ := fun r => w (min r.toNNReal s') with hwf
  have hmem : ∀ r : ℝ, min r.toNNReal s' ∈ {s : ℝ≥0 | (s : ℝ≥0∞) < T} := fun r =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right _ _)) (ENNReal.coe_lt_coe.2 hs'T)
  have hwfc : Continuous wf :=
    hc.comp_continuous (continuous_real_toNNReal.min continuous_const) hmem
  have hK : QuantumZipper.fwdHull (fun r : ℝ => w r.toNNReal) s = QuantumZipper.fwdHull wf s := by
    refine fwdHull_eq_of_eqOn (t₂ := s') s.coe_nonneg (by exact_mod_cast hss') fun r hr => ?_
    simp only [hwf, min_eq_left (Real.toNNReal_le_iff_le_coe.2 hr.2)]
  rw [hK] at hz
  have hb : ∀ r ∈ Icc (0 : ℝ) s, |wf r| ≤ C := fun r _ => hC _ (hmem r)
  by_contra hlt
  rw [not_le] at hlt
  have hsq : Real.sqrt s ≤ Real.sqrt T := Real.sqrt_le_sqrt (by exact_mod_cast hs.le)
  have := mem_diff_fwdHull_of_norm hwfc s.coe_nonneg hb hz.1 (by linarith)
  exact this.2 hz

/-- **A driver of the filled prefixes of a path tending to `∞` is unbounded at a finite killing time** (proof of
Lemma 7.1, p. 225: "the elementary Loewner hull bounds would put the entire mapped prefix in a bounded rectangle,
contrary to its limit at `∞`"). -/
theorem unbounded_of_fwdHull_eq {γ : ℝ → ℂ} {w : ℝ≥0 → ℝ} {T : ℝ≥0∞}
    (hc : ContinuousOn w {s : ℝ≥0 | (s : ℝ≥0∞) < T}) (hγc : ContinuousOn γ (Ici 0))
    (hH : MapsTo γ (Ici 0) Hbar) (h0 : γ 0 = 0) (hinf : Tendsto (fun t => ‖γ t‖) atTop atTop)
    (hR : interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (γ u).im = 0} = ∅)
    (hK : ∀ t, 0 ≤ t → ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ∧
      QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) s = fillH (γ '' Icc 0 t)) :
    T ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ∧ C < |w s| := by
  intro hT C
  by_contra hcon
  push Not at hcon
  lift T to ℝ≥0 using hT with T'
  set R := C + 3 * Real.sqrt T' with hRdef
  have hupper : ∀ u, 0 < u → 0 < (γ u).im → ‖γ u‖ ≤ R := by
    intro u hu him
    obtain ⟨s, hs, hKs⟩ := hK u hu.le
    have hmem : γ u ∈ fillH (γ '' Icc 0 u) :=
      ⟨him, Or.inl (subset_closure ⟨u, ⟨hu.le, le_rfl⟩, rfl⟩)⟩
    rw [← hKs] at hmem
    exact norm_le_of_mem_fwdHull_killed (T := T') (by exact_mod_cast hc) (fun s hs' => hcon s hs')
      (by exact_mod_cast hs) hmem
  have hall : ∀ u, 0 ≤ u → ‖γ u‖ ≤ max R 0 := by
    intro u hu
    rcases hu.eq_or_lt with rfl | hu
    · rw [h0, norm_zero]
      exact le_max_right _ _
    · exact (Lemma71.norm_le_of_forall_im_pos hγc hH hR hupper hu).trans (le_max_left _ _)
  obtain ⟨t, ht1, ht2⟩ := ((hinf.eventually_gt_atTop (max R 0)).and (eventually_ge_atTop 0)).exists
  linarith [hall t ht2]

end Hull

/-! ### The killed form of the named input, and the reduction -/

section Reduction

/-- A process that is adapted and, at each time, almost surely equal to a martingale is a martingale. -/
theorem martingale_of_ae_eq {𝓖 : Filtration ℝ≥0 mΩ} {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ}
    (hX : Martingale X 𝓖 P) (hY : StronglyAdapted 𝓖 Y) (h : ∀ t, Y t =ᵐ[P] X t) :
    Martingale Y 𝓖 P :=
  ⟨hY, fun i j hij => (condExp_congr_ae (h j)).trans ((hX.2 i j hij).trans (h i).symm)⟩

/-- **Named input: the killed form of `Lemma71MappedSegmentStatement`** (Specification §7.1, the setup, p. 221; proof
of Lemma 7.1, pp. 223–225; Remark 6.14, p. 218: "That proposition gives a continuous Loewner driver up to the
terminal capacity time of `ψ(η_C)`"). Fix `0 < κ < 4` and angles `θ₁ < 0 < θ₂`. On the probability space of the
three-curve construction there are a filtration `𝓖` with the usual conditions (right-continuous, time-zero σ-algebra
containing the null sets; the augmentation of the filtration retaining the complete outer curves, rulings R15 Q2,
R34), the mapped segment `γ` (the same geometric clause as `Lemma71MappedSegmentStatement`), and its driver `W` **up
to its terminal capacity time `T`**: `W₀ = 0`, `W` continuous on `[0, T)` and adapted before `T`, almost surely every
filled prefix of `γ` is the hull of `W` at a capacity time `< T`, and the coupling means of the two-seed word with the
seed weights (CPF2) are local martingales before `min (swallowTime z) T` (Lemma 6.2's history locality, Remark 6.7's
three-curve means, Proposition 6.5's time continuity, p. 225). The finiteness of `T` is not excluded here: that is the
content of `lemma71MappedSegmentStatement_of_killed`. -/
def Lemma71KilledSegmentStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ₁ θ₂ : ℝ, θ₁ < 0 → 0 < θ₂ →
    ∃ (Ω : Type v) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓖 : Filtration ℝ≥0 mΩ) (_ : 𝓖.IsRightContinuous) (γ : Ω → ℝ → ℂ) (W : ℝ≥0 → Ω → ℝ)
      (T : Ω → ℝ≥0∞),
      (∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s) ∧
      (∀ᵐ ω ∂P, ContinuousOn (γ ω) (Ici 0) ∧ InjOn (γ ω) (Ici 0) ∧ MapsTo (γ ω) (Ici 0) Hbar ∧
        γ ω 0 = 0 ∧ Tendsto (fun t => ‖γ ω t‖) atTop atTop ∧
        interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (γ ω u).im = 0} = ∅) ∧
      (∀ ω, W 0 ω = 0) ∧ (∀ ω, ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < T ω}) ∧
      AdaptedBefore 𝓖 T W ∧
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧
        QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) s = fillH (γ ω '' Icc 0 t)) ∧
      HasMartingaleMeansBefore κ LP.twoSeedXL LP.twoSeedXR (fun _ => cpf2RhoL κ θ₂)
        (fun _ => cpf2RhoR κ θ₁) P 𝓖 W T

/-- **`Lemma71MappedSegmentStatement` from its killed form** (proof of Lemma 7.1, p. 225: "Its terminal capacity cannot
be finite"). The driver of the mapped segment is unbounded at a finite terminal capacity time (the elementary hull
bound, `unbounded_of_fwdHull_eq`), so its terminal capacity time is almost surely infinite
(`ae_eq_top_of_hasMartingaleMeansBefore`); on the null event where it is finite the driver is replaced by `0`, which
keeps adaptedness because the time-zero σ-algebra contains the null sets. Conditional helper: it replaces no source
theorem. -/
theorem lemma71MappedSegmentStatement_of_killed (h : Lemma71KilledSegmentStatement.{v}) :
    Lemma71.Lemma71MappedSegmentStatement.{v} := by
  classical
  intro κ hκ hκ4 θ₁ θ₂ hθ₁ hθ₂
  obtain ⟨Ω, mΩ, P, hP, 𝓖, h𝓖, γ, W, T, hnull, hγ, hW0, hc, hWa, hK, hm⟩ :=
    h κ hκ hκ4 θ₁ θ₂ hθ₁ hθ₂
  have hL : -2 < cpf2RhoL κ θ₂ := neg_two_lt_cpf2RhoL hκ hκ4 hθ₂
  have hR : -2 < cpf2RhoR κ θ₁ := neg_two_lt_cpf2RhoR hκ hκ4 hθ₁
  have hunb : ∀ᵐ ω ∂P, T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω| := by
    filter_upwards [hγ, hK] with ω hγω hKω
    obtain ⟨hγc, -, hH, h0, hinf, hRi⟩ := hγω
    exact unbounded_of_fwdHull_eq (w := fun s => W s ω) (hc ω) hγc hH h0 hinf hRi hKω
  have hT := ae_eq_top_of_hasMartingaleMeansBefore hκ hL hR hm hW0 hc hWa hnull hunb
  -- the good event `G`, in `𝓖₀`, on which `T = ⊤`
  set Bad := {ω | ¬ T ω = ⊤} with hBad
  have hBad0 : P Bad = 0 := ae_iff.1 hT
  set G := (toMeasurable P Bad)ᶜ with hGdef
  have hGc : P Gᶜ = 0 := by rw [hGdef, compl_compl, measure_toMeasurable]; exact hBad0
  have hG : MeasurableSet[𝓖 0] G :=
    (hnull _ (measurableSet_toMeasurable P Bad) (by rw [measure_toMeasurable]; exact hBad0)).compl
  have hGt : ∀ t, MeasurableSet[𝓖 t] G := fun t => 𝓖.mono zero_le _ hG
  have hTG : ∀ ω ∈ G, T ω = ⊤ := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable P Bad h)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    simpa only [compl_def] using hGc
  -- the global driver
  set W' : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ G then W t ω else 0 with hW'def
  have hW'G : ∀ ω ∈ G, ∀ t, W' t ω = W t ω := fun ω hω t => by simp only [hW'def, hω, ↓reduceIte]
  have hW'n : ∀ ω ∉ G, ∀ t, W' t ω = 0 := fun ω hω t => by simp only [hW'def, hω, ↓reduceIte]
  have hW'0 : ∀ ω, W' 0 ω = 0 := fun ω => by
    by_cases hω : ω ∈ G
    · rw [hW'G ω hω, hW0]
    · exact hW'n ω hω 0
  have hW'c : ∀ ω, Continuous fun t => W' t ω := fun ω => by
    by_cases hω : ω ∈ G
    · have heq : (fun t => W' t ω) = fun t => W t ω := funext (hW'G ω hω)
      rw [heq]
      have hcu := hc ω
      have huniv : {t : ℝ≥0 | (t : ℝ≥0∞) < T ω} = univ := by
        ext t
        simp [hTG ω hω]
      rw [huniv] at hcu
      exact continuousOn_univ.1 hcu
    · have heq : (fun t => W' t ω) = fun _ => (0 : ℝ) := funext (hW'n ω hω)
      rw [heq]
      exact continuous_const
  have hW'a : StronglyAdapted 𝓖 W' := fun t => by
    have heq : (fun ω => W' t ω) = G.indicator (Girsanov.killed T W t) := funext fun ω => by
      by_cases hω : ω ∈ G
      · rw [hW'G ω hω, indicator_of_mem hω,
          Girsanov.killed_of_lt (by rw [hTG ω hω]; exact ENNReal.coe_lt_top)]
      · rw [hW'n ω hω, indicator_of_notMem hω]
    show StronglyMeasurable[𝓖 t] fun ω => W' t ω
    rw [heq]
    exact ((Girsanov.measurable_killed hWa t).indicator (hGt t)).stronglyMeasurable
  have hpath : ∀ ω ∈ G, (fun s : ℝ => W' s.toNNReal ω) = fun s : ℝ => W s.toNNReal ω :=
    fun ω hω => funext fun s => hW'G ω hω _
  have hgeomL : ∀ ω ∈ G, ∀ i t, geomL W' LP.twoSeedXL i t ω = geomL W LP.twoSeedXL i t ω :=
    fun ω hω i t => by
      have : Bessel.realPath (fun t ω => -W' t ω) ω = Bessel.realPath (fun t ω => -W t ω) ω :=
        funext fun s => by simp only [Bessel.realPath, hW'G ω hω]
      simp only [geomL, this]
  have hgeomR : ∀ ω ∈ G, ∀ i t, geomR W' LP.twoSeedXR i t ω = geomR W LP.twoSeedXR i t ω :=
    fun ω hω i t => by
      have : Bessel.realPath W' ω = Bessel.realPath W ω :=
        funext fun s => by simp only [Bessel.realPath, hW'G ω hω]
      simp only [geomR, this]
  refine ⟨Ω, mΩ, P, hP, 𝓖, γ, W', hγ, hW'0, hW'c, hW'a, ?_, ?_⟩
  · filter_upwards [hK, hGae] with ω hKω hω t ht
    obtain ⟨s, -, hs⟩ := hKω t ht
    refine ⟨s, s.coe_nonneg, ?_⟩
    rw [hpath ω hω]
    exact hs
  -- the martingale clause
  intro u hu z hz
  set ρL : Fin 1 → ℝ := fun _ => cpf2RhoL κ θ₂ with hρL
  set ρR : Fin 1 → ℝ := fun _ => cpf2RhoR κ θ₁ with hρR
  set u' : Ω → ℝ≥0 → ℂ → ℝ := fun ω t => if ω ∈ G then u ω t else
    meanExt κ ρL ρR (W t ω) (fun i => geomL W LP.twoSeedXL i t ω) (fun i => geomR W LP.twoSeedXR i t ω)
    with hu'def
  have hu' : ∀ ω t, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => geomL W LP.twoSeedXL i t ω - W t ω)
        (fun i => geomR W LP.twoSeedXR i t ω - W t ω))
      (forceJumpSet (fun i => geomL W LP.twoSeedXL i t ω - W t ω)
        (fun i => geomR W LP.twoSeedXR i t ω - W t ω)) (u' ω t) := by
    intro ω t
    by_cases hω : ω ∈ G
    · have h1 := hu ω t
      simp only [hgeomL ω hω, hgeomR ω hω, hW'G ω hω] at h1
      simp only [hu'def, hω, ↓reduceIte]
      exact h1
    · simp only [hu'def, hω, ↓reduceIte]
      exact isBoundedHarmonicExtension_meanExt κ ρL ρR (W t ω) _ _
  obtain ⟨σ, hσ, hσζ, hσlim, hσmart⟩ := hm u' hu' z hz
  set X' : ℝ≥0 → Ω → ℝ := fun t ω => couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u' ω t) z
    with hX'
  set X : ℝ≥0 → Ω → ℝ := fun t ω => couplingMean κ (fun s : ℝ => W' s.toNNReal ω) t (u ω t) z
    with hXdef
  have hXG : ∀ ω ∈ G, ∀ t, X t ω = X' t ω := fun ω hω t => by
    simp only [hXdef, hX', hpath ω hω, hu'def, hω, ↓reduceIte]
  -- the value at time `0` off `G` is the canonical one
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hz)
  set c₀ : ℝ := meanExt κ ρL ρR 0 (fun _ => 0) (fun _ => 0) z with hc₀
  have hX0 : ∀ ω ∉ G, X 0 ω = c₀ := fun ω hω => by
    have hw0 : (fun s : ℝ => W' s.toNNReal ω) 0 = 0 := by
      simp only [Real.toNNReal_zero, hW'0]
    have h1 : X 0 ω = u ω 0 z := Coupling.MartMeans2.couplingMean_zero κ hw0 (u ω 0) hz0
    rw [h1]
    have hu0 := hu ω 0
    have hgL : ∀ i, geomL W' LP.twoSeedXL i 0 ω = 0 := geomL_twoSeed_zero' (hW'c ω) (hW'0 ω)
    have hgR : ∀ i, geomR W' LP.twoSeedXR i 0 ω = 0 := geomR_twoSeed_zero' (hW'c ω) (hW'0 ω)
    simp only [hgL, hgR, hW'0] at hu0
    have hmean := isBoundedHarmonicExtension_meanExt κ ρL ρR 0 (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
    have huniq := Impl.eqOn_of_isBoundedHarmonicExtension
      (Impl.forceJumpSet_finite (Ito.weightWord ρL ρR) (fun _ => (0 : ℝ) - 0) (fun _ => (0 : ℝ) - 0))
      hmean hu0
    exact huniq hz
  refine ⟨fun k ω => if ω ∈ G then σ k ω else 0, fun k => ?_, fun k ω => ?_, ?_, fun k => ?_⟩
  · -- a stopping time
    intro t
    have heq : {ω | (if ω ∈ G then σ k ω else 0) ≤ (t : WithTop ℝ≥0)} =
        (G ∩ {ω | σ k ω ≤ t}) ∪ Gᶜ := by
      ext ω
      by_cases hω : ω ∈ G
      · simp [hω]
      · simp only [hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_inter_iff, false_and, mem_compl_iff,
          not_false_eq_true, or_true, iff_true]
        exact WithTop.coe_le_coe.2 (zero_le : (0 : ℝ≥0) ≤ t)
    rw [heq]
    exact ((hGt t).inter (hσ k t)).union (hGt t).compl
  · -- below the swallowing time
    by_cases hω : ω ∈ G
    · simp only [hω, ↓reduceIte]
      rw [hpath ω hω]
      exact (hσζ k ω).trans (min_le_left _ _)
    · simp only [hω, ↓reduceIte]
      rw [← WithTop.coe_zero]
      exact WithTop.coe_le_iff.2 fun _ _ => zero_le
  · -- exhausting
    filter_upwards [hσlim, hGae] with ω hω hωG r hr
    simp only [hωG, ↓reduceIte]
    rw [hpath ω hωG] at hr
    have hmin : min (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z : WithTop ℝ≥0) (T ω) =
        (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z : WithTop ℝ≥0) := by
      have := hTG ω hωG
      exact min_eq_left (by rw [this]; exact le_top)
    exact hω r (lt_of_lt_of_eq hr hmin.symm)
  · -- a martingale
    refine martingale_of_ae_eq (hσmart k) (fun t => ?_) fun t => ?_
    · have heq : stoppedProcess X (fun ω => if ω ∈ G then σ k ω else 0) t =
          G.piecewise (stoppedProcess X' (σ k) t) (fun _ => c₀) := by
        funext ω
        by_cases hω : ω ∈ G
        · simp only [piecewise, hω, ↓reduceIte, stoppedProcess]
          exact hXG ω hω _
        · simp only [piecewise, hω, ↓reduceIte, stoppedProcess, untopA_min_zero]
          exact hX0 ω hω
      rw [heq]
      exact ((hσmart k).1 t).piecewise (hGt t) stronglyMeasurable_const
    · filter_upwards [hGae] with ω hω
      simp only [stoppedProcess, hω, ↓reduceIte]
      exact hXG ω hω _

/-- **Lemma 7.1's reference evolution from the killed named input**: `lemma71MappedSegmentStatement_of_killed`
followed by PROVE-LEMMA71's `lemma71TraceReferenceStatement_of_mappedSegment`. Conditional helper. -/
theorem lemma71TraceReferenceStatement_of_killed (h : Lemma71KilledSegmentStatement.{v}) :
    Lemma71TraceReferenceStatement.{v} :=
  Lemma71.lemma71TraceReferenceStatement_of_mappedSegment (lemma71MappedSegmentStatement_of_killed h)

end Reduction

end InteractingSLE.Sec7.Lemma71B
