/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartChart
import InteractingSLE.Spec.Jordan.Coupling
import InteractingSLE.Foundations.Loewner.YuanCorollary13Tip

/-!
# Proposition GB6: the counterflow hulls in the chart of the flow's own component (fixed-hull restriction)

Packet PROVE-GB6B. Supplement §8.6, proof of Proposition GB6 (`source/spec/p481-528.md` L935–L975, p. 519):

> "Fixed-hull restriction gives continuous relative Loewner growth before `T`. This assertion is local in the
> histories: the removed flow prefix is separated from each compact counterflow prefix […] Strict relative growth
> follows from strict original hull growth and conformality in these neighborhoods."

Setting (deterministic). The counterflow is read in its own chart (the inversion `R(w) = −1/w`, frozen
`IsCenteredCounterflowDriver`): its hulls are the Loewner hulls `K'_t` of a continuous driver `W` (`W 0 = 0`), and its
physical hulls are `R(K'_t)`. The flow prefix is the Loewner hull `A₀ = K_σ` of a continuous driver `U` (`U 0 = 0`)
with tip `p` (the limit of `f_σ⁻¹` at `0`). The chart of the flow's own component `ℍ \ K_σ` is
`ownComponentChart U σ = I ∘ f_σ`, so the counterflow hulls read in it are `Ψ(K'_t)` with
`Ψ(w) = −1/f_σ(−1/w)` (`relMap`).

## Main result

* **`exists_loewner_relMap`**: if the closed physical counterflow hull `R(K'_T)` and the closed flow hull `K_σ` are
  disjoint (before the first contact, on a compact time interval), then `t ↦ Ψ(K'_t)`, `t ∈ [0, T]`, is a chordal
  Loewner chain after a capacity time change: a continuous driver `W'` with `W'(0) = 0` and a continuous strictly
  increasing clock `τ` with `τ(0) = 0` and `K^{W'}_{τ(t)} = Ψ(K'_t)`.

## Proof

`Ψ` factors as `M₂ ∘ g_A ∘ M₁`: choose a real point `x < 0` outside both closed hulls (`exists_real_sep`, left of the
real trace of the flow hull, within the separation distance); `M₁(w) = w/(xw + 1)` moves the counterflow target `∞`
to a finite point (pole `−1/x` away from `K'_T`); `A = m(K_σ)` with `m(z) = −1/(z − x)` is a compact hull, mapped out
by `g_A`; and `Ψ ∘ M₁⁻¹ ∘ g_A⁻¹` is a real Möbius map `M₂` (`Sec5.CrossRestart.exists_realMobius_conj`). The three
factors are handled by the Möbius image theorem (`Sec5.CrossRestart.exists_loewner_mobius_image`, twice) and
Specification Aux. lemma 8 (`ConformalImageFull.exists_loewner_image`), as in
`Sec5.CrossRestart.exists_loewner_restartMap`.
The analytic facts specific to GB6: `M₂` moves `∞` (`c ≠ 0`), because the chart of `U` is unbounded at the tip prime
end while `g_A ∘ m` stays bounded there; the start `g_A(0)` of the middle chain is the zero of `M₂`, because `Ψ → 0`
at the counterflow seed; and the middle chain keeps a positive distance from the pole of `M₂`, because the counterflow
hull stays away from the tip (`|f_σ| ≥ ε` on `R(K'_T)`, by the tip limit).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H)
open QuantumZipper.CA (realMobius)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE

namespace Supp8

namespace GB6

open ConformalImage ConformalImageFull Sec5.CrossRestart

/-- **A real separating point**: left of a compact set `A ∋ 0`, within the separation distance, hence outside both `A`
and a disjoint closed set `B`. -/
theorem exists_real_sep {A B : Set ℂ} (hA : IsCompact A) (hB : IsClosed B) (hAB : Disjoint A B)
    (h0 : (0 : ℂ) ∈ A) : ∃ x : ℝ, x < 0 ∧ (x : ℂ) ∉ A ∧ (x : ℂ) ∉ B := by
  obtain ⟨δ, hδ, hdis⟩ := hAB.exists_thickenings hA hB
  set S : Set ℝ := {y : ℝ | (y : ℂ) ∈ A} with hS
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded (hA.isClosed.preimage continuous_ofReal) ?_
    obtain ⟨M, hM⟩ := hA.isBounded.exists_norm_le
    refine isBounded_iff_forall_norm_le.2 ⟨M, fun y hy => ?_⟩
    have := hM _ hy
    rwa [Complex.norm_real] at this
  have hS0 : (0 : ℝ) ∈ S := by simpa [hS] using h0
  have hne : S.Nonempty := ⟨0, hS0⟩
  set a := sInf S with ha
  have haS : a ∈ S := hSc.sInf_mem hne
  have ha0 : a ≤ 0 := csInf_le hSc.bddBelow hS0
  refine ⟨a - δ / 2, by linarith, fun hx => ?_, fun hx => ?_⟩
  · have : a ≤ a - δ / 2 := csInf_le hSc.bddBelow hx
    linarith
  · have h1 : ((a - δ / 2 : ℝ) : ℂ) ∈ thickening δ A := by
      rw [mem_thickening_iff]
      refine ⟨(a : ℂ), haS, ?_⟩
      rw [dist_eq_norm, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rw [show a - δ / 2 - a = -(δ / 2) by ring, abs_neg, abs_of_pos (by linarith)]
      linarith
    exact Set.disjoint_left.1 hdis h1 (self_subset_thickening hδ B hx)

/-- A point outside a closed set has a ball outside it. -/
theorem exists_ball_disjoint_of_notMem_closure {S : Set ℂ} {z : ℂ} (hz : z ∉ closure S) :
    ∃ r : ℝ, 0 < r ∧ Disjoint (ball z r) S := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (isOpen_compl_iff.2 isClosed_closure |>.mem_nhds hz)
  exact ⟨r, hr, Set.disjoint_left.2 fun w hw hwS => hball hw (subset_closure hwS)⟩

/-- The counterflow chart (`−1/w` back to the original flow chart) followed by the chart of the flow's own component:
`w ↦ c_U(−1/w) = −1/f_σ(−1/w)`. -/
def relMap (U : ℝ → ℝ) (σ : ℝ) (w : ℂ) : ℂ := -(QuantumZipper.fwdMap U σ (-w⁻¹))⁻¹

theorem relMap_eq_ownComponentChart (U : ℝ → ℝ) (σ : ℝ) (w : ℂ) :
    relMap U σ w = (ownComponentChart U σ).1 (-w⁻¹) := rfl

/-- `m⁻¹ ∘ M₁ = R` on `ℍ`, with `M₁(w) = w/(xw + 1)` and `m⁻¹(v) = x − 1/v`. -/
theorem mobInv_M₁ {x : ℝ} {w : ℂ} (hw : w ∈ H) :
    realMobius (-x) 1 (-1) 0 (realMobius 1 0 x 1 w) = -w⁻¹ := by
  have hw0 : w ≠ 0 := fun h => by simp [h, QuantumZipper.H] at hw
  have hden : (x : ℂ) * w + 1 ≠ 0 := by
    have := QuantumZipper.CA.realMobius_denom_ne_zero (a := 1) (b := 0) (c := x) (d := 1)
      (by norm_num) hw
    simpa using this
  simp only [realMobius, ofReal_neg, ofReal_one, ofReal_zero, add_zero, one_mul]
  have h2 : -1 * (w / (↑x * w + 1)) ≠ 0 := by
    simp only [neg_mul, one_mul, ne_eq, neg_eq_zero, div_eq_zero_iff, not_or]
    exact ⟨hw0, hden⟩
  rw [div_eq_iff h2]
  field_simp
  ring

/-- `m⁻¹ ∘ m = id` on `ℍ`, with `m(z) = −1/(z − x)`. -/
theorem mobInv_m {x : ℝ} {z : ℂ} (hz : z ∈ H) :
    realMobius (-x) 1 (-1) 0 (realMobius 0 (-1) 1 (-x) z) = z := by
  have := QuantumZipper.CA.realMobius_inv_apply (a := 0) (b := -1) (c := 1) (d := -x) (by norm_num) hz
  simpa using this

/-- `m ∘ m⁻¹ = id` on `ℍ`. -/
theorem m_mobInv {x : ℝ} {v : ℂ} (hv : v ∈ H) :
    realMobius 0 (-1) 1 (-x) (realMobius (-x) 1 (-1) 0 v) = v := by
  have := realMobius_mobInv (a := 0) (b := -1) (c := 1) (d := -x) (by norm_num) hv
  simpa using this

/-- **The factorization of the chart of `U` read in the counterflow chart** (the data of `exists_loewner_relMap`):
`relMap U σ = M₂ ∘ g_A ∘ M₁` near the counterflow hull, with `M₁(w) = w/(xw + 1)` (`x ≠ 0`, pole `−1/x` at distance
`≥ r₁` from `K'_T`), `g_A` the mapping-out function of a compact hull `A` whose closure misses `0` and the closed
`M₁`-image of `K'_T`, and `M₂ = realMobius a' b' c' d'` with `c' ≠ 0`, whose zero is the boundary value `x₁` of `g_A`
at `0` and whose pole keeps a distance `≥ r₃` from `g_A(M₁(K'_T))`. -/
theorem exists_relMap_factor {W U : ℝ → ℝ} (hW : Continuous W) (hU : Continuous U)
    (hU0 : U 0 = 0) {σ T : ℝ} (hσ : 0 < σ) (hT : 0 ≤ T) {p : ℂ}
    (htip : Tendsto (QuantumZipper.fwdMapInv U σ) (𝓝[H] 0) (𝓝 p))
    (hd : Disjoint (closure (QuantumZipper.fwdHull U σ))
      (closure ((fun w : ℂ => -w⁻¹) '' QuantumZipper.fwdHull W T))) :
    ∃ (x r₁ : ℝ) (A : Set ℂ) (gA : ℂ → ℂ) (a' b' c' d' x₁ r₃ : ℝ),
      x ≠ 0 ∧ 0 < r₁ ∧ Disjoint (ball (mobPole x 1 : ℂ) r₁) (QuantumZipper.fwdHull W T) ∧
      IsHPHull A ∧ IsMapOut A gA ∧
      Disjoint (closure A) (insert 0 (closure (realMobius 1 0 x 1 '' QuantumZipper.fwdHull W T))) ∧
      Tendsto gA (𝓝[H] 0) (𝓝 (x₁ : ℂ)) ∧
      0 < a' * d' - b' * c' ∧ c' ≠ 0 ∧ c' * x₁ + d' ≠ 0 ∧ a' * x₁ + b' = 0 ∧ 0 < r₃ ∧
      (∀ w ∈ QuantumZipper.fwdHull W T, r₃ ≤ ‖gA (realMobius 1 0 x 1 w) - mobPole c' d'‖) ∧
      ∀ w ∈ H, -w⁻¹ ∉ QuantumZipper.fwdHull U σ →
        realMobius 1 0 x 1 w ∈ H \ A ∧ relMap U σ w = realMobius a' b' c' d' (gA (realMobius 1 0 x 1 w)) := by
  set A₀ := QuantumZipper.fwdHull U σ with hA₀def
  set K := QuantumZipper.fwdHull W T with hKdef
  set R : ℂ → ℂ := fun w => -w⁻¹ with hRdef
  have hA₀ : IsHPHull A₀ := isHPHull_fwdHull hU hσ.le
  have hK : IsHPHull K := isHPHull_fwdHull hW hT
  have hA₀c : IsCompact (closure A₀) := hA₀.2.1.isCompact_closure
  have h0A : (0 : ℂ) ∈ closure A₀ := zero_mem_closure_fwdHull hU hU0 hσ
  have hpA : p ∈ closure A₀ := YuanCorollary13.mem_closure_fwdHull_of_tendsto hU hU0 hσ htip
  obtain ⟨x, hx0, hxA, hxB⟩ := exists_real_sep hA₀c isClosed_closure hd h0A
  have hxne : x ≠ 0 := hx0.ne
  have hKH : ∀ w ∈ K, w ∈ H := fun w hw => hK.1 hw
  have hRK : ∀ w ∈ K, R w ∉ A₀ := fun w hw hA =>
    Set.disjoint_left.1 hd (subset_closure hA) (subset_closure ⟨w, hw, rfl⟩)
  -- step 1: the Möbius map `M₁(w) = w/(xw + 1)`, pole `−1/x`
  set M₁ := realMobius 1 0 x 1 with hM₁def
  have hpole₁ : ((mobPole x 1 : ℝ) : ℂ) ∉ closure K := by
    intro hm
    apply hxB
    have hne : ((mobPole x 1 : ℝ) : ℂ) ≠ 0 := by
      simp [mobPole, hxne]
    have hcont : ContinuousAt R ((mobPole x 1 : ℝ) : ℂ) := (continuousAt_inv₀ hne).neg
    have hmem := hcont.continuousWithinAt.mem_closure_image hm
    have hval : R ((mobPole x 1 : ℝ) : ℂ) = (x : ℂ) := by
      simp only [hRdef, mobPole]
      push_cast
      field_simp
    rwa [hval] at hmem
  obtain ⟨r₁, hr₁, hd₁⟩ := exists_ball_disjoint_of_notMem_closure hpole₁
  have hdet₁ : (0 : ℝ) < 1 * 1 - 0 * x := by norm_num
  have hp₁ : mobPole x 1 ≠ 0 := by simp [mobPole, hxne]
  -- step 2: the flow hull in the chart `m(z) = −1/(z − x)`, and its mapping-out function
  set m := realMobius 0 (-1) 1 (-x) with hmdef
  set φ := realMobius (-x) 1 (-1) 0 with hφdef
  set A := m '' A₀ with hAdef
  have hxA' : ((mobPole 1 (-x) : ℝ) : ℂ) ∉ closure A₀ := by simpa [mobPole] using hxA
  obtain ⟨r₀, hr₀, hd₀⟩ := exists_ball_disjoint_of_notMem_closure hxA'
  have hdetm : (0 : ℝ) < 0 * (-x) - (-1) * 1 := by norm_num
  have hA : IsHPHull A := isHPHull_image hdetm one_ne_zero hA₀ hr₀ hd₀
  obtain ⟨gA, hgA⟩ := hA.exists_isMapOut
  have hφm : ∀ z ∈ H, φ (m z) = z := fun z hz => mobInv_m hz
  have hmφ : ∀ v ∈ H, m (φ v) = v := fun v hv => m_mobInv hv
  have hφM₁ : ∀ w ∈ H, φ (M₁ w) = R w := fun w hw => mobInv_M₁ hw
  have h0A' : (0 : ℂ) ∉ closure A := by
    obtain ⟨M, hM⟩ := hA₀.2.1.exists_norm_le
    set ε : ℝ := 1 / (|M| + |x| + 1) with hε
    have hεpos : 0 < ε := by positivity
    have hsub : A ⊆ {v : ℂ | ε ≤ ‖v‖} := by
      rintro _ ⟨z, hz, rfl⟩
      have hzH : z ∈ H := hA₀.1 hz
      have hzx : z - (x : ℂ) ≠ 0 := fun h => by
        have : z = (x : ℂ) := sub_eq_zero.1 h
        rw [this] at hzH
        simp [QuantumZipper.H] at hzH
      have hmz : m z = -(z - x)⁻¹ := by
        simp only [hmdef, realMobius]
        push_cast
        ring
      show ε ≤ ‖m z‖
      rw [hmz, norm_neg, norm_inv]
      have hn : ‖z - x‖ ≤ |M| + |x| := by
        refine (norm_sub_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs]
        linarith [hM z hz, le_abs_self M]
      rw [hε, one_div]
      exact inv_anti₀ (norm_pos_iff.2 hzx) (by linarith)
    intro h0
    have := closure_minimal hsub (isClosed_le continuous_const continuous_norm) h0
    simp only [mem_ofPred_eq, norm_zero] at this
    linarith
  have hdisjAK : Disjoint (closure A) (closure (M₁ '' K)) := by
    rw [Set.disjoint_left]
    intro v hvA hvK
    have hv0 : v ≠ 0 := fun h => h0A' (h ▸ hvA)
    have hcont : ContinuousAt φ v := continuousAt_realMobius (by push_cast; simpa using hv0)
    have h1 : φ v ∈ closure (φ '' A) := hcont.continuousWithinAt.mem_closure_image hvA
    have h2 : φ v ∈ closure (φ '' (M₁ '' K)) := hcont.continuousWithinAt.mem_closure_image hvK
    have hφA : φ '' A ⊆ A₀ := by
      rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      rw [hφm z (hA₀.1 hz)]
      exact hz
    have hφK : φ '' (M₁ '' K) ⊆ R '' K := by
      rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨w, hw, (hφM₁ w (hKH w hw)).symm⟩
    exact Set.disjoint_left.1 hd (closure_mono hφA h1) (closure_mono hφK h2)
  -- the boundary value `x₁` of `g_A` at `0`
  obtain ⟨r₀', hr₀', hball0⟩ := exists_ball_disjoint_of_notMem_closure h0A'
  obtain ⟨hLre, hgA0'⟩ := hgA.tendsto_limUnder_of_disjoint hA (y := 0) hr₀' (by simpa using hball0)
  set x₁ := (limUnder (𝓝[H] ((0 : ℝ) : ℂ)) gA).re with hx₁def
  have hx₁C : (x₁ : ℂ) = limUnder (𝓝[H] ((0 : ℝ) : ℂ)) gA := Complex.ext (by simp [hx₁def])
    (by rw [ofReal_im]; exact hLre.symm)
  have hgA0 : Tendsto gA (𝓝[H] (0 : ℂ)) (𝓝 (x₁ : ℂ)) := by
    rw [hx₁C]
    simpa using hgA0'
  have hdA' : Disjoint (closure A) (insert 0 (closure (M₁ '' K))) :=
    Set.disjoint_insert_right.2 ⟨h0A', hdisjAK⟩
  -- step 4: the chart of `U`, read through `m⁻¹`, is a real Möbius map `M₂` of `g_A`
  have hG : IsConformalBijection (ownComponentChart U σ).1 (H \ A₀) H :=
    (isDomainChart_ownComponentChart hU hU0 hσ.le).isConformalBijection
  have hdetφ : (0 : ℝ) < (-x) * 0 - 1 * (-1) := by norm_num
  have hφd : DifferentiableOn ℂ φ (H \ A) := (differentiableOn_realMobius hdetφ).mono sdiff_subset
  have hmA : ∀ z ∈ H, ∀ z' ∈ A₀, m z' = m z → z' = z := fun z hz z' hz' h => by
    have := congrArg φ h
    rwa [hφm z' (hA₀.1 hz'), hφm z hz] at this
  have hφb : BijOn φ (H \ A) (H \ A₀) := by
    refine ⟨fun v hv => ⟨QuantumZipper.CA.realMobius_mem_H hdetφ hv.1,
      fun hA' => hv.2 ⟨φ v, hA', hmφ v hv.1⟩⟩,
      (QuantumZipper.CA.bijOn_realMobius_H hdetφ).injOn.mono sdiff_subset, fun z hz => ?_⟩
    have hmz : m z ∈ H \ A := ⟨QuantumZipper.CA.realMobius_mem_H hdetm hz.1, fun ⟨z', hz', hzz'⟩ =>
      hz.2 (hmA z hz.1 z' hz' hzz' ▸ hz')⟩
    exact ⟨m z, hmz, hφm z hz.1⟩
  obtain ⟨a', b', c', d', hdet', hconj⟩ := exists_realMobius_conj hA hgA hφd hφb hG
  set M₂ := realMobius a' b' c' d' with hM₂def
  have hM₁A : ∀ w ∈ H, R w ∉ A₀ → M₁ w ∈ H \ A := by
    intro w hw hwA
    refine ⟨QuantumZipper.CA.realMobius_mem_H hdet₁ hw, fun ⟨z, hz, hzw⟩ => hwA ?_⟩
    have := congrArg φ hzw
    rw [hφm z (hA₀.1 hz), hφM₁ w hw] at this
    exact this ▸ hz
  have hrel : ∀ w ∈ H, R w ∉ A₀ → relMap U σ w = M₂ (gA (M₁ w)) := by
    intro w hw hwA
    have := hconj (M₁ w) (hM₁A w hw hwA)
    rw [hφM₁ w hw] at this
    exact this
  -- step 5a: the counterflow hull stays away from the tip prime end: `|f_σ| ≥ ε` on `R(K)`
  have hRKH : ∀ w ∈ K, R w ∈ H \ A₀ := fun w hw =>
    ⟨Chart.isConformal_infinitySourceChart.2.1 (hKH w hw), hRK w hw⟩
  obtain ⟨ε, hεpos, hεK⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ w ∈ K, ε ≤ ‖QuantumZipper.fwdMap U σ (R w)‖ := by
    by_contra hcon
    push Not at hcon
    have hseq : ∀ n : ℕ, ∃ w ∈ K, ‖QuantumZipper.fwdMap U σ (R w)‖ < 1 / ((n : ℝ) + 1) :=
      fun n => hcon _ (by positivity)
    choose w hwK hw using hseq
    have hv : Tendsto (fun n => QuantumZipper.fwdMap U σ (R (w n))) atTop (𝓝[H] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n =>
        QuantumZipper.FwdHolo.mapsTo_fwdMap hU hσ.le (hRKH (w n) (hwK n))⟩
      rw [tendsto_zero_iff_norm_tendsto_zero]
      exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hw n).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hz : Tendsto (fun n => R (w n)) atTop (𝓝 p) := by
      refine (htip.comp hv).congr fun n => ?_
      exact QuantumZipper.RS.fwdMapInv_fwdMap hU hU0 hσ.le (hRKH (w n) (hwK n))
    have hpK : p ∈ closure (R '' K) :=
      mem_closure_of_tendsto hz (Eventually.of_forall fun n => ⟨w n, hwK n, rfl⟩)
    exact Set.disjoint_left.1 hd hpA hpK
  have hbdd : ∀ w ∈ K, ‖relMap U σ w‖ ≤ 1 / ε := fun w hw => by
    rw [relMap, norm_neg, norm_inv, one_div]
    exact inv_anti₀ hεpos (hεK w hw)
  -- step 5b: `M₂` moves `∞` (`c' ≠ 0`): near the tip prime end the chart of `U` is unbounded, `g_A ∘ m` is bounded
  have hpx : p - (x : ℂ) ≠ 0 := fun h => hxA (sub_eq_zero.1 h ▸ hpA)
  have hmc : ContinuousAt m p := continuousAt_realMobius (by push_cast; simpa [sub_eq_add_neg] using hpx)
  have hpath : Tendsto (fun y : ℝ => QuantumZipper.fwdMapInv U σ ((y : ℂ) * I)) (𝓝[>] 0) (𝓝 p) := by
    refine htip.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
    · have h0 : Tendsto (fun y : ℝ => (y : ℂ) * I) (𝓝 0) (𝓝 0) := by
        have hc : Continuous (fun y : ℝ => (y : ℂ) * I) := by fun_prop
        simpa using hc.tendsto (0 : ℝ)
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      show 0 < ((y : ℂ) * I).im
      simpa using hy
  have hc' : c' ≠ 0 := by
    intro hc0
    have hd0 : d' ≠ 0 := by
      rintro rfl
      simp [hc0] at hdet'
    obtain ⟨CA, hCA⟩ := hgA.exists_norm_le hA
    set D : ℝ := (|a'| * (‖m p‖ + 1 + |CA|) + |b'|) / |d'| with hD
    have hD0 : 0 ≤ D := by positivity
    have hev1 : ∀ᶠ (y : ℝ) in 𝓝[>] 0, ‖m (QuantumZipper.fwdMapInv U σ ((y : ℂ) * I))‖ ≤ ‖m p‖ + 1 :=
      (hmc.tendsto.comp hpath).norm.eventually (Iic_mem_nhds (lt_add_one _))
    have hev2 : ∀ᶠ (y : ℝ) in 𝓝[>] 0, y ∈ Ioo (0 : ℝ) (1 / (D + 1)) := Ioo_mem_nhdsGT (by positivity)
    obtain ⟨y, hy1, hy2⟩ := (hev1.and hev2).exists
    have hyH : (y : ℂ) * I ∈ H := by
      show 0 < ((y : ℂ) * I).im
      simpa using hy2.1
    set z := QuantumZipper.fwdMapInv U σ ((y : ℂ) * I) with hzdef
    have hzA : z ∈ H \ A₀ := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hU hU0 hσ.le hyH
    have hfz : QuantumZipper.fwdMap U σ z = (y : ℂ) * I :=
      QuantumZipper.RS.fwdMap_fwdMapInv hU hU0 hσ.le hyH
    have hmz : m z ∈ H \ A := ⟨QuantumZipper.CA.realMobius_mem_H hdetm hzA.1, fun ⟨z', hz', h⟩ =>
      hzA.2 (hmA z hzA.1 z' hz' h ▸ hz')⟩
    have hc := hconj (m z) hmz
    rw [hφm z hzA.1] at hc
    have hL : ‖(ownComponentChart U σ).1 z‖ = 1 / y := by
      change ‖-(QuantumZipper.fwdMap U σ z)⁻¹‖ = 1 / y
      rw [hfz, norm_neg, norm_inv, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, abs_of_pos hy2.1, one_div]
    have hgz : ‖gA (m z)‖ ≤ ‖m p‖ + 1 + |CA| := by
      have := hCA (m z) hmz
      linarith [le_abs_self CA]
    have hR : ‖M₂ (gA (m z))‖ ≤ D := by
      have hM : M₂ (gA (m z)) = ((a' : ℂ) * gA (m z) + b') / d' := by
        simp only [hM₂def, realMobius, hc0, ofReal_zero, zero_mul, zero_add]
      rw [hM, norm_div, Complex.norm_real, Real.norm_eq_abs, hD]
      have hnum : ‖(a' : ℂ) * gA (m z) + b'‖ ≤ |a'| * (‖m p‖ + 1 + |CA|) + |b'| := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
        gcongr
      exact div_le_div_of_nonneg_right hnum (abs_nonneg _)
    rw [← hc, hL] at hR
    have : 1 / (1 / (D + 1)) < 1 / y := one_div_lt_one_div_of_lt hy2.1 hy2.2
    rw [one_div_one_div] at this
    linarith
  -- step 5c: the start `x₁ = W₂(0)` of the `g_A`-chain is the zero of `M₂`, not its pole
  have hNe : (𝓝[H] (0 : ℂ)).NeBot := by simpa using MobHyp.nhdsWithin_neBot 0
  have hRcob : Tendsto R (𝓝[H] (0 : ℂ)) (Bornology.cobounded ℂ ⊓ 𝓟 (H \ A₀)) := by
    have h1 : Tendsto R (𝓝[H] (0 : ℂ)) (Bornology.cobounded ℂ) := by
      have hsub : 𝓝[H] (0 : ℂ) ≤ 𝓝[≠] 0 := nhdsWithin_mono _ fun w hw => by
        intro h0
        rw [Set.mem_singleton_iff] at h0
        subst h0
        simp [QuantumZipper.H] at hw
      have h2 := tendsto_inv₀_nhdsNE_zero (α := ℂ)
      rw [← tendsto_norm_atTop_iff_cobounded] at h2 ⊢
      simpa [hRdef] using h2.mono_left hsub
    refine tendsto_inf.2 ⟨h1, tendsto_principal.2 ?_⟩
    have hcomp : A₀ᶜ ∈ Bornology.cobounded ℂ :=
      Bornology.isBounded_def.1 (show Bornology.IsBounded A₀ from hA₀.2.1)
    filter_upwards [h1.eventually hcomp, self_mem_nhdsWithin] with w hw hwH
    exact ⟨Chart.isConformal_infinitySourceChart.2.1 hwH, hw⟩
  have hΨ0 : Tendsto (relMap U σ) (𝓝[H] (0 : ℂ)) (𝓝 0) := by
    have hf : Tendsto (QuantumZipper.fwdMap U σ) (Bornology.cobounded ℂ ⊓ 𝓟 (H \ A₀))
        (Bornology.cobounded ℂ) := by
      rw [← tendsto_norm_atTop_iff_cobounded]
      have hsub := (tendsto_fwdMap_add_sub hU hU0 hσ.le).norm.eventually
        (gt_mem_nhds (show ‖(0 : ℂ)‖ < 1 by simp))
      have hid : Tendsto (fun z : ℂ => ‖z‖ + -(1 + |U σ|)) (Bornology.cobounded ℂ ⊓ 𝓟 (H \ A₀)) atTop :=
        tendsto_atTop_add_const_right _ _ (tendsto_norm_cobounded_atTop.mono_left inf_le_left)
      refine tendsto_atTop_mono' _ ?_ hid
      filter_upwards [hsub] with z hz
      have h1 : ‖z‖ ≤ ‖QuantumZipper.fwdMap U σ z‖ + ‖QuantumZipper.fwdMap U σ z + U σ - z‖ + |U σ| := by
        have hz' : z = QuantumZipper.fwdMap U σ z - (QuantumZipper.fwdMap U σ z + U σ - z) + (U σ : ℂ) := by
          ring
        calc ‖z‖ = ‖QuantumZipper.fwdMap U σ z - (QuantumZipper.fwdMap U σ z + U σ - z) + (U σ : ℂ)‖ := by
              rw [← hz']
          _ ≤ ‖QuantumZipper.fwdMap U σ z - (QuantumZipper.fwdMap U σ z + U σ - z)‖ + ‖(U σ : ℂ)‖ :=
              norm_add_le _ _
          _ ≤ ‖QuantumZipper.fwdMap U σ z‖ + ‖QuantumZipper.fwdMap U σ z + U σ - z‖ + ‖(U σ : ℂ)‖ := by
              gcongr
              exact norm_sub_le _ _
          _ = _ := by rw [Complex.norm_real, Real.norm_eq_abs]
      linarith
    have := ((tendsto_inv₀_cobounded (α := ℂ)).comp (hf.comp hRcob)).neg
    rw [neg_zero] at this
    exact this.congr fun w => rfl
  have hM₁0 : Tendsto M₁ (𝓝[H] (0 : ℂ)) (𝓝[H] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc : ContinuousAt M₁ 0 := continuousAt_realMobius (by simp)
      have h0 : M₁ 0 = 0 := by simp [hM₁def, realMobius]
      have := hc.tendsto
      rw [h0] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      exact QuantumZipper.CA.realMobius_mem_H hdet₁ hw
  have hgM : Tendsto (fun w => gA (M₁ w)) (𝓝[H] (0 : ℂ)) (𝓝 (x₁ : ℂ)) := hgA0.comp hM₁0
  have hevA : ∀ᶠ w in 𝓝[H] (0 : ℂ), w ∈ H ∧ R w ∉ A₀ := by
    filter_upwards [hRcob.eventually (mem_inf_of_right (mem_principal_self _)), self_mem_nhdsWithin]
      with w hw hwH
    exact ⟨hwH, hw.2⟩
  have hevrel : ∀ᶠ w in 𝓝[H] (0 : ℂ), relMap U σ w = M₂ (gA (M₁ w)) := by
    filter_upwards [hevA] with w hw
    exact hrel w hw.1 hw.2
  have hM₂lim : Tendsto (fun w => M₂ (gA (M₁ w))) (𝓝[H] (0 : ℂ)) (𝓝 0) := hΨ0.congr' hevrel
  have hgMH : ∀ᶠ w in 𝓝[H] (0 : ℂ), gA (M₁ w) ∈ H := by
    filter_upwards [hevA] with w hw
    exact hgA.1.2.mapsTo (hM₁A w hw.1 hw.2)
  set κ₂ := (a' * d' - b' * c') / c' ^ 2 with hκ₂
  have hκ₂pos : 0 < κ₂ := div_pos hdet' (by positivity)
  have hx₁ : (c' : ℂ) * x₁ + d' ≠ 0 := by
    intro hpole
    have hP : c' * x₁ + d' = 0 := by exact_mod_cast hpole
    have hev1 : ∀ᶠ w in 𝓝[H] (0 : ℂ), ‖M₂ (gA (M₁ w))‖ < 1 :=
      hM₂lim.norm.eventually (gt_mem_nhds (by simp))
    have hev2 : ∀ᶠ w in 𝓝[H] (0 : ℂ), ‖gA (M₁ w) - x₁‖ < κ₂ / (|a' / c'| + 2) := by
      have := (hgM.sub_const (x₁ : ℂ)).norm
      rw [sub_self, norm_zero] at this
      exact this.eventually (gt_mem_nhds (by positivity))
    obtain ⟨w, h1, h2, h3⟩ := (hev1.and (hev2.and hgMH)).exists
    have hv0 : gA (M₁ w) - x₁ ≠ 0 := sub_ne_zero.2 fun h => by
      rw [h] at h3
      simp [QuantumZipper.H] at h3
    have hnf : M₂ (gA (M₁ w)) = nf (a' / c') κ₂ x₁ (gA (M₁ w)) := realMobius_eq_nf_of_pole hc' hP hv0
    have hn : κ₂ / ‖gA (M₁ w) - x₁‖ - |a' / c'| ≤ ‖M₂ (gA (M₁ w))‖ := by
      rw [hnf, nf]
      have := norm_sub_norm_le ((κ₂ : ℂ) / (gA (M₁ w) - x₁)) ((a' / c' : ℝ) : ℂ)
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ₂pos, Complex.norm_real,
        Real.norm_eq_abs] at this
      exact this.trans (norm_sub_rev _ _).le
    have hlt : |a' / c'| + 2 < κ₂ / ‖gA (M₁ w) - x₁‖ := by
      rw [lt_div_iff₀ (norm_pos_iff.2 hv0)]
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < |a' / c'| + 2)).1 h2
      linarith
    linarith
  have hM₂x₁ : M₂ (x₁ : ℂ) = 0 :=
    tendsto_nhds_unique ((continuousAt_realMobius (a' := a') (b' := b') hx₁).tendsto.comp hgM) hM₂lim
  have hnum : a' * x₁ + b' = 0 := by
    have h : ((a' : ℂ) * x₁ + b') / ((c' : ℂ) * x₁ + d') = 0 := hM₂x₁
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · exact_mod_cast h
    · exact absurd h hx₁
  -- step 5d: the `g_A`-images of the counterflow hulls keep a distance `r₃` from the pole `P₂` of `M₂`
  set P₂ := mobPole c' d' with hP₂
  set r₃ := κ₂ / (|a' / c'| + 1 / ε) with hr₃
  have hr₃pos : 0 < r₃ := by positivity
  have hclear : ∀ w ∈ K, r₃ ≤ ‖gA (M₁ w) - P₂‖ := by
    intro w hw
    have hvH : gA (M₁ w) ∈ H := hgA.1.2.mapsTo (hM₁A w (hKH w hw) (hRK w hw))
    have hv0 : gA (M₁ w) - P₂ ≠ 0 := sub_ne_zero.2 fun h => by
      rw [h] at hvH
      simp [QuantumZipper.H] at hvH
    have hnf : M₂ (gA (M₁ w)) = nf (a' / c') κ₂ P₂ (gA (M₁ w)) := realMobius_eq_nf hc' hv0
    have hΨ := hrel w (hKH w hw) (hRK w hw)
    have hb := hbdd w hw
    have hn : κ₂ / ‖gA (M₁ w) - P₂‖ ≤ |a' / c'| + 1 / ε := by
      have h1 : ‖((κ₂ : ℝ) : ℂ) / (gA (M₁ w) - P₂)‖ ≤ ‖((a' / c' : ℝ) : ℂ)‖ + ‖M₂ (gA (M₁ w))‖ := by
        rw [hnf, nf]
        calc ‖((κ₂ : ℝ) : ℂ) / (gA (M₁ w) - P₂)‖
            = ‖((a' / c' : ℝ) : ℂ) - (((a' / c' : ℝ) : ℂ) - ((κ₂ : ℝ) : ℂ) / (gA (M₁ w) - P₂))‖ := by
              ring_nf
          _ ≤ _ := norm_sub_le _ _
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ₂pos, Complex.norm_real,
        Real.norm_eq_abs, ← hΨ] at h1
      linarith
    rw [hr₃, div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (norm_pos_iff.2 hv0)] at hn
    linarith [mul_comm (|a' / c'| + 1 / ε) ‖gA (M₁ w) - P₂‖]
  have hx₁' : c' * x₁ + d' ≠ 0 := by exact_mod_cast hx₁
  exact ⟨x, r₁, A, gA, a', b', c', d', x₁, r₃, hxne, hr₁, hd₁, hA, hgA, hdA', hgA0, hdet', hc', hx₁', hnum,
    hr₃pos, hclear, fun w hw hwA => ⟨hM₁A w hw hwA, hrel w hw hwA⟩⟩

/-- **Fixed-hull restriction** (GB6, proof, p. 519): before the first contact, the counterflow hulls read in the chart
of the flow's own component form a chordal Loewner chain after a capacity time change. Hypotheses: the counterflow
driver `W` and the flow driver `U` are continuous with `W 0 = U 0 = 0`, `σ > 0`, `T ≥ 0`, the flow trace has tip `p`
(`f_σ⁻¹ → p` at `0`), and the closed flow hull `K_σ` is disjoint from the closed physical counterflow hull
`R(K'_T)`. -/
theorem exists_loewner_relMap {W U : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) (hU : Continuous U)
    (hU0 : U 0 = 0) {σ T : ℝ} (hσ : 0 < σ) (hT : 0 ≤ T) {p : ℂ}
    (htip : Tendsto (QuantumZipper.fwdMapInv U σ) (𝓝[H] 0) (𝓝 p))
    (hd : Disjoint (closure (QuantumZipper.fwdHull U σ))
      (closure ((fun w : ℂ => -w⁻¹) '' QuantumZipper.fwdHull W T))) :
    ∃ τ W' : ℝ → ℝ, Continuous W' ∧ W' 0 = 0 ∧ τ 0 = 0 ∧ StrictMonoOn τ (Icc 0 T) ∧
      ContinuousOn τ (Icc 0 T) ∧ ∀ t ∈ Icc (0 : ℝ) T,
        QuantumZipper.fwdHull W' (τ t) = relMap U σ '' QuantumZipper.fwdHull W t := by
  obtain ⟨x, r₁, A, gA, a', b', c', d', x₁, r₃, hxne, hr₁, hd₁, hA, hgA, hdA', hgA0, hdet', hc', hx₁', hnum,
    hr₃pos, hclear, hfac⟩ := exists_relMap_factor hW hU hU0 hσ hT htip hd
  set K := QuantumZipper.fwdHull W T with hKdef
  set M₁ := realMobius 1 0 x 1 with hM₁def
  set M₂ := realMobius a' b' c' d' with hM₂def
  set P₂ := mobPole c' d' with hP₂
  have hK : IsHPHull K := isHPHull_fwdHull hW hT
  have hdet₁ : (0 : ℝ) < 1 * 1 - 0 * x := by norm_num
  have hp₁ : mobPole x 1 ≠ 0 := by simp [mobPole, hxne]
  have hKH : ∀ w ∈ K, w ∈ H := fun w hw => hK.1 hw
  have hRK : ∀ w ∈ K, -w⁻¹ ∉ QuantumZipper.fwdHull U σ := fun w hw hA =>
    Set.disjoint_left.1 hd (subset_closure hA) (subset_closure ⟨w, hw, rfl⟩)
  have hrel : ∀ w ∈ K, relMap U σ w = M₂ (gA (M₁ w)) := fun w hw => (hfac w (hKH w hw) (hRK w hw)).2
  -- step 1: the Möbius map `M₁`
  obtain ⟨σ₁, W₁, _, _, _, hW₁c, hW₁0, hσ₁0, hσ₁m, hσ₁c, h₁⟩ :=
    exists_loewner_mobius_image hW hW0 hT hdet₁ hxne hp₁ hr₁ hd₁
  have hK₁ : ∀ t ∈ Icc (0 : ℝ) T, QuantumZipper.fwdHull W₁ (σ₁ t) = M₁ '' QuantumZipper.fwdHull W t :=
    fun t ht => (h₁ t ht).2.1
  have hW₁0' : W₁ 0 = 0 := by rw [hW₁0]; simp
  have hT₁ : 0 ≤ σ₁ T := by
    rw [← hσ₁0]; exact hσ₁m.monotoneOn ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT
  have hdA : Disjoint (closure A) (insert (W₁ 0 : ℂ) (closure (QuantumZipper.fwdHull W₁ (σ₁ T)))) := by
    rw [hK₁ T ⟨hT, le_rfl⟩, hW₁0']
    simpa using hdA'
  -- Specification Aux. lemma 8 for `g_A`
  obtain ⟨a₂, W₂, hW₂c, ha₂0, ha₂m, ha₂c, h₂⟩ := exists_loewner_image hW₁c hT₁ hA hgA hdA
  have hK₂ : ∀ s ∈ Icc (0 : ℝ) (σ₁ T), QuantumZipper.fwdHull W₂ (a₂ s) =
      gA '' QuantumZipper.fwdHull W₁ s := fun s hs => (h₂ s hs).2.1
  have hW₂0 : W₂ 0 = x₁ := by
    obtain ⟨-, -, hR⟩ := h₂ 0 ⟨le_rfl, hT₁⟩
    have himg : (fun z => QuantumZipper.fwdMap W₁ 0 z + W₁ 0) '' A = A := by
      have : ∀ z ∈ A, QuantumZipper.fwdMap W₁ 0 z + W₁ 0 = z := fun z hz =>
        gmap_zero_apply hW₁c (hA.1 hz)
      rw [image_congr this, image_id']
    obtain ⟨-, hlim⟩ := hR gA (by rw [himg]; exact hgA)
    rw [ha₂0, hW₁0'] at hlim
    have hNe : (𝓝[H] (0 : ℂ)).NeBot := by simpa using MobHyp.nhdsWithin_neBot 0
    have := tendsto_nhds_unique (by simpa using hlim) hgA0
    exact_mod_cast this
  have hT₂ : 0 ≤ a₂ (σ₁ T) := by
    rw [← ha₂0]; exact ha₂m.monotoneOn ⟨le_rfl, hT₁⟩ ⟨hT₁, le_rfl⟩ hT₁
  -- step 6: translate the `g_A`-chain to start at `0`, then apply `M₂` (pole `P₂ − x₁ ≠ 0`)
  set W₃ : ℝ → ℝ := fun s => W₂ s + -x₁ with hW₃
  have hW₃c : Continuous W₃ := by fun_prop
  have hW₃0 : W₃ 0 = 0 := by simp [hW₃, hW₂0]
  have hK₃ : ∀ s, QuantumZipper.fwdHull W₃ s =
      (fun z : ℂ => z + ((-x₁ : ℝ) : ℂ)) '' QuantumZipper.fwdHull W₂ s :=
    fun s => fwdHull_add_const W₂ (-x₁) s
  have hdet₂ : 0 < a' * (c' * x₁ + d') - (a' * x₁ + b') * c' := by
    have : a' * (c' * x₁ + d') - (a' * x₁ + b') * c' = a' * d' - b' * c' := by ring
    rw [this]
    exact hdet'
  have hpole₂ : mobPole c' (c' * x₁ + d') ≠ 0 := by
    simp only [mobPole]
    exact div_ne_zero (neg_ne_zero.2 hx₁') hc'
  have hpole₂' : ((mobPole c' (c' * x₁ + d') : ℝ) : ℂ) = (P₂ : ℂ) - x₁ := by
    have hc'C : (c' : ℂ) ≠ 0 := ofReal_ne_zero.2 hc'
    simp only [hP₂, mobPole]
    push_cast
    field_simp
    ring
  have hd4 : Disjoint (ball (mobPole c' (c' * x₁ + d') : ℂ) r₃)
      (QuantumZipper.fwdHull W₃ (a₂ (σ₁ T))) := by
    rw [hpole₂', hK₃, hK₂ (σ₁ T) ⟨hT₁, le_rfl⟩, hK₁ T ⟨hT, le_rfl⟩, Set.disjoint_left]
    rintro _ hb ⟨_, ⟨_, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
    rw [mem_ball, dist_eq_norm] at hb
    have := hclear w hw
    have heq : gA (M₁ w) + ((-x₁ : ℝ) : ℂ) - ((P₂ : ℂ) - x₁) = gA (M₁ w) - P₂ := by
      push_cast
      ring
    rw [heq] at hb
    linarith
  obtain ⟨τ₄, W₄, _, _, _, hW₄c, hW₄0, hτ₄0, hτ₄m, hτ₄c, h₄⟩ :=
    exists_loewner_mobius_image hW₃c hW₃0 hT₂ hdet₂ hc' hpole₂ hr₃pos hd4
  have hmaps₁ : MapsTo σ₁ (Icc 0 T) (Icc 0 (σ₁ T)) := fun t ht =>
    ⟨by rw [← hσ₁0]; exact hσ₁m.monotoneOn ⟨le_rfl, hT⟩ ht ht.1,
      hσ₁m.monotoneOn ht ⟨hT, le_rfl⟩ ht.2⟩
  have hmaps₂ : MapsTo a₂ (Icc 0 (σ₁ T)) (Icc 0 (a₂ (σ₁ T))) := fun s hs =>
    ⟨by rw [← ha₂0]; exact ha₂m.monotoneOn ⟨le_rfl, hT₁⟩ hs hs.1,
      ha₂m.monotoneOn hs ⟨hT₁, le_rfl⟩ hs.2⟩
  refine ⟨fun t => τ₄ (a₂ (σ₁ t)), W₄, hW₄c, ?_, by simp [hσ₁0, ha₂0, hτ₄0], ?_, ?_, fun t ht => ?_⟩
  · rw [hW₄0, hnum, zero_div]
  · intro t ht t' ht' htt'
    exact hτ₄m (hmaps₂ (hmaps₁ ht)) (hmaps₂ (hmaps₁ ht'))
      (ha₂m (hmaps₁ ht) (hmaps₁ ht') (hσ₁m ht ht' htt'))
  · exact hτ₄c.comp (ha₂c.comp hσ₁c hmaps₁) (hmaps₂.comp hmaps₁)
  · rw [(h₄ _ (hmaps₂ (hmaps₁ ht))).2.1, hK₃, hK₂ _ (hmaps₁ ht), hK₁ t ht, image_image, image_image,
      image_image]
    refine image_congr fun w hw => ?_
    have hwK : w ∈ K := (QuantumZipper.fwdHull_mono (W := W)).1 ht.2 hw
    rw [hrel w hwK]
    simp only [hM₂def, realMobius]
    push_cast
    congr 1 <;> ring

end GB6

end Supp8

end InteractingSLE
