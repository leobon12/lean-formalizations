/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartMobius
import InteractingSLE.Spec.Sec4.Counterflow

/-!
# The restart chart of the counterflow after a segment of another curve: the hull-level coordinate change

Packet PROVE-SEC5-F (obstruction (ii) of `planning/handoffs/PROVE-SEC5-E.md`, deterministic part). Lemma 5.7's proof
(specification p. 138): "We apply a conformal transformation `ψ : 𝒮 \ η([0, σ]) → 𝒮` which fixes `±∞` and sends
`η(σ)` to `0`; the boundary data for the GFF which describes the evolution of `ψ(η′)` is as in the right panel of
Figure 5.5." The evolution of `ψ(η′)` is a chordal Loewner evolution in the chart in which the counterflow starts at
`0` and targets the tip `η(σ)` at `∞` (PROVE-SEC5-E's normalization of the restart chart: the strip end `+∞` goes to
`−1`).

In the exponential chart `E` the flow-line segment is the hull `A = K^U_σ` of its own driver `U` (`U 0 = 0`), the
counterflow lives in the chart `M_q` (`Sec4.stripCounterflowChart`, start `0`, target `∞ = E(0)`), and
`M_q⁻¹(w) = −(1 + q)/(w + 1)` is a real Möbius map with pole `−1` (the image of the strip end `+∞`). The restart chart
read in the counterflow chart is

  `Φ = m₂ ∘ (· − x₁) ∘ g_A ∘ M_q⁻¹`,  `x₁ = g_A(−1 − q)`,  `m₂(w) = −w/(w − (U_σ − x₁))`,

which sends the counterflow's start `0` to `0`, the tip prime end (`g_A`-image `U_σ`) to `∞`, and the strip end
`+∞` to `−1`.

**Main result** (`exists_loewner_restartMap`). If the counterflow hulls `K′_t`, `t ≤ T`, keep a positive distance from
`−1`, their `E`-images `M_q⁻¹(K′_T)` are at positive distance from the flow-line hull `A` and from `E(z₀) = −1 − q`,
and their `g_A`-images keep a positive distance from `U_σ`, then `t ↦ Φ(K′_t)` is a chordal Loewner chain after a
capacity time change: a continuous driver `W̃` with `W̃(0) = 0` and a continuous strictly increasing clock `τ` with
`τ(0) = 0` and `K̃_{τ(t)} = Φ(K′_t)`. This is the change of coordinates SEC5-E listed as missing ("the image of the
counterflow hulls under the map of `ℍ \ η([0, σ])` is a Loewner chain with a continuous driver after a capacity time
change"); it holds for the non-simple counterflow, since it is proved at the level of hulls.

Proof: the Möbius image theorem (`exists_loewner_mobius_image`) for `M_q⁻¹`, Specification Aux. lemma 8
(`ConformalImageFull.exists_loewner_image`, arbitrary start) for `g_A`, a translation, and the Möbius image theorem for
`m₂`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open QuantumZipper (H)
open QuantumZipper.CA (realMobius)

namespace InteractingSLE

namespace Sec5

namespace CrossRestart

open ConformalImage ConformalImageFull

/-! ### Small facts -/

/-- `M_q⁻¹(w) = −(1 + q)/(w + 1)` is the real Möbius map `(0 · w − (1 + q))/(w + 1)`. -/
theorem stripCounterflowChart_inv_eq_realMobius (q : ℝ) (z : ℂ) :
    (Sec4.stripCounterflowChart q).2.1 z = realMobius 0 (-(1 + q)) 1 1 z := by
  rw [Sec4.stripCounterflowChart_inv, realMobius]
  push_cast
  ring

/-- `g_0 = id` on `ℍ` for a continuous driver with any starting value. -/
theorem gmap_zero_apply {W : ℝ → ℝ} (hW : Continuous W) {z : ℂ} (hz : z ∈ H) : gmap W 0 z = z := by
  set V : ℝ → ℝ := fun s => W s - W 0 with hV
  have hVc : Continuous V := by fun_prop
  have hV0 : V 0 = 0 := by simp [hV]
  have hfun : (fun s => V s + W 0) = W := funext fun s => by simp [hV]
  have hK0 : QuantumZipper.fwdHull V 0 = ∅ := (imageHyp_empty hVc hV0 le_rfl).K_zero
  have hzH : z - W 0 ∈ H \ QuantumZipper.fwdHull V 0 := by
    refine ⟨?_, by rw [hK0]; exact Set.notMem_empty _⟩
    have hz' : 0 < z.im := hz
    show 0 < (z - W 0).im
    simpa using hz'
  have h1 := fwdMap_add_const V (W 0) 0 z
  rw [hfun] at h1
  rw [gmap, h1, fwdMap_zero_eq hVc hV0 le_rfl hzH]
  ring

/-- A real point left of the seed stays left of the driver: `g_t(y) < W_t` for `y < 0` away from `K_T`. -/
theorem bdryVal_re_lt {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {y r T : ℝ} (hT : 0 ≤ T)
    (hr : 0 < r) (hd : Disjoint (ball (y : ℂ) r) (QuantumZipper.fwdHull W T)) (hy : y < 0) :
    (bdryVal W y T).re < W T := by
  set ψ : ℝ → ℝ := fun t => (bdryVal W y t).re - W t with hψ
  have hψc : ContinuousOn ψ (Icc 0 T) :=
    ((Complex.continuous_re.comp_continuousOn (continuousOn_bdryVal hW hW0 hT hr hd)).sub
      hW.continuousOn)
  have hψ0 : ψ 0 < 0 := by simp [hψ, bdryVal_zero hW hW0, hW0, hy]
  have hne : ∀ t ∈ Icc (0 : ℝ) T, ψ t ≠ 0 := fun t ht h0 => by
    have hb := bdryVal_ne hW hW0 hr hd hy.ne ht
    have him := (bdryVal_spec hW hW0 ht.1 hr (disjoint_ball_of_le hd ht.2)).1
    apply hb
    apply Complex.ext
    · simp only [ofReal_re]; linarith [show (bdryVal W y t).re - W t = 0 from h0]
    · simp [him]
  by_contra hcon
  push Not at hcon
  have hψT : 0 ≤ ψ T := by simp only [hψ]; linarith
  obtain ⟨t, ht, ht0⟩ := isPreconnected_Icc.intermediate_value₂ (left_mem_Icc.2 hT)
    (right_mem_Icc.2 hT) hψc continuousOn_const (show ψ 0 ≤ 0 from hψ0.le) hψT
  exact hne t ht ht0

/-! ### The restart chart -/

/-- The restart chart read in the counterflow chart: `Φ(z) = m₂(g_A(M_q⁻¹ z) − x₁)` with `A = K^U_σ`,
`m₂(w) = −w/(w − (U_σ − x₁))`. -/
def restartMap (q : ℝ) (U : ℝ → ℝ) (σ x₁ : ℝ) (z : ℂ) : ℂ :=
  realMobius (-1) 0 1 (-(U σ - x₁)) (gmap U σ (realMobius 0 (-(1 + q)) 1 1 z) - x₁)

/-- **The counterflow hulls in the restart chart form a Loewner chain** (the hull-level coordinate change of
Lemma 5.7's proof). Let `W` (`W 0 = 0`) drive the counterflow in the chart `M_q` up to time `T`, with its hulls at
distance `≥ r` from `−1` (the strip end `+∞`); let `U` (`U 0 = 0`) drive the flow line in the chart `E` and
`A = K^U_σ`; let the `E`-images `M_q⁻¹(K′_T)` and `E(z₀) = −1 − q` have closures disjoint from that of `A`, and let
the `g_A`-images of `M_q⁻¹(K′_T)` stay at distance `≥ r₃` from `U_σ`. With `x₁ = g_A(−1 − q)` (the boundary value):
there are a continuous driver `W̃`, `W̃(0) = 0`, and a continuous strictly increasing clock `τ`, `τ(0) = 0`, with
`K̃_{τ(t)} = Φ(K′_t)` for `t ∈ [0, T]`. -/
theorem exists_loewner_restartMap {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ}
    (hT : 0 ≤ T) {q r : ℝ} (hq : 0 < q) (hr : 0 < r)
    (hd1 : Disjoint (ball (-1 : ℂ) r) (QuantumZipper.fwdHull W T)) {U : ℝ → ℝ} (hU : Continuous U)
    (hU0 : U 0 = 0) {σ : ℝ} (hσ : 0 ≤ σ)
    (hd2 : Disjoint (closure (QuantumZipper.fwdHull U σ))
      (insert ((-1 - q : ℝ) : ℂ) (closure (realMobius 0 (-(1 + q)) 1 1 '' QuantumZipper.fwdHull W T))))
    {x₁ : ℝ} (hx₁ : (x₁ : ℂ) = bdryVal U (-1 - q) σ) {r₃ : ℝ} (hr₃ : 0 < r₃)
    (hd3 : Disjoint (ball (U σ : ℂ) r₃)
      (gmap U σ '' (realMobius 0 (-(1 + q)) 1 1 '' QuantumZipper.fwdHull W T))) :
    ∃ (τ W' : ℝ → ℝ), Continuous W' ∧ W' 0 = 0 ∧ τ 0 = 0 ∧ StrictMonoOn τ (Icc 0 T) ∧
      ContinuousOn τ (Icc 0 T) ∧ ∀ t ∈ Icc (0 : ℝ) T,
        QuantumZipper.fwdHull W' (τ t) = restartMap q U σ x₁ '' QuantumZipper.fwdHull W t := by
  set m₁ := realMobius 0 (-(1 + q)) 1 1 with hm₁
  set A := QuantumZipper.fwdHull U σ with hAdef
  set φ := gmap U σ with hφdef
  have hA : IsHPHull A := isHPHull_fwdHull hU hσ
  have hφ : IsMapOut A φ := isMapOut_fwdMap hU hU0 hσ
  -- step 1: `M_q⁻¹`
  have hdet₁ : 0 < (0 : ℝ) * 1 - (-(1 + q)) * 1 := by linarith
  have hpole₁ : mobPole 1 1 = -1 := by simp [mobPole]
  obtain ⟨σ₁, W₁, _, _, _, hW₁c, hW₁0, hσ₁0, hσ₁m, hσ₁c, h₁⟩ :=
    exists_loewner_mobius_image hW hW0 hT hdet₁ one_ne_zero (by rw [hpole₁]; norm_num) hr
      (by rw [hpole₁]; push_cast; exact hd1)
  have hT₁ : 0 ≤ σ₁ T := by
    rw [← hσ₁0]; exact hσ₁m.monotoneOn ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT
  have hK₁ : ∀ t ∈ Icc (0 : ℝ) T, QuantumZipper.fwdHull W₁ (σ₁ t) = m₁ '' QuantumZipper.fwdHull W t :=
    fun t ht => (h₁ t ht).2.1
  have hW₁0' : W₁ 0 = -1 - q := by rw [hW₁0]; ring
  -- step 2: `g_A` (Aux. lemma 8, arbitrary start)
  have hd : Disjoint (closure A) (insert (W₁ 0 : ℂ) (closure (QuantumZipper.fwdHull W₁ (σ₁ T)))) := by
    rw [hK₁ T ⟨hT, le_rfl⟩, hW₁0']; exact hd2
  obtain ⟨a₂, W₂, hW₂c, ha₂0, ha₂m, ha₂c, h₂⟩ := exists_loewner_image hW₁c hT₁ hA hφ hd
  -- the start of the second chain is `x₁`
  have hW₂0 : W₂ 0 = x₁ := by
    obtain ⟨-, -, hR⟩ := h₂ 0 ⟨le_rfl, hT₁⟩
    have hgA : (fun z => QuantumZipper.fwdMap W₁ 0 z + W₁ 0) '' A = A := by
      have : ∀ z ∈ A, QuantumZipper.fwdMap W₁ 0 z + W₁ 0 = z := fun z hz =>
        gmap_zero_apply hW₁c (hA.1 hz)
      rw [image_congr this, image_id']
    obtain ⟨-, hlim⟩ := hR φ (by rw [hgA]; exact hφ)
    rw [ha₂0, hW₁0'] at hlim
    have hcl : ((-1 - q : ℝ) : ℂ) ∉ closure A := fun h =>
      Set.disjoint_left.1 hd2 h (mem_insert _ _)
    obtain ⟨r', hr', hr'd⟩ := Metric.mem_nhds_iff.1 (isOpen_compl_iff.2 isClosed_closure
      |>.mem_nhds hcl)
    have hball : Disjoint (ball ((-1 - q : ℝ) : ℂ) r') A :=
      Set.disjoint_left.2 fun z hz hzA => hr'd hz (subset_closure hzA)
    have hspec := (bdryVal_spec hU hU0 hσ hr' hball).2
    have := MobHyp.nhdsWithin_neBot (-1 - q)
    have heq := tendsto_nhds_unique hlim hspec
    rw [← hx₁] at heq
    exact_mod_cast heq
  have hT₂ : 0 ≤ a₂ (σ₁ T) := by
    rw [← ha₂0]; exact ha₂m.monotoneOn ⟨le_rfl, hT₁⟩ ⟨hT₁, le_rfl⟩ hT₁
  have hK₂ : ∀ s ∈ Icc (0 : ℝ) (σ₁ T), QuantumZipper.fwdHull W₂ (a₂ s) =
      φ '' QuantumZipper.fwdHull W₁ s := fun s hs => (h₂ s hs).2.1
  -- step 3: translate by `−x₁`
  set W₃ : ℝ → ℝ := fun s => W₂ s + -x₁ with hW₃
  have hW₃c : Continuous W₃ := by fun_prop
  have hW₃0 : W₃ 0 = 0 := by simp [hW₃, hW₂0]
  have hK₃ : ∀ s, QuantumZipper.fwdHull W₃ s = (fun z : ℂ => z + (-x₁ : ℝ)) '' QuantumZipper.fwdHull W₂ s :=
    fun s => fwdHull_add_const W₂ (-x₁) s
  -- step 4: `m₂`
  set P₂ : ℝ := U σ - x₁ with hP₂
  have hx₁lt : x₁ < U σ := by
    have hcl : ((-1 - q : ℝ) : ℂ) ∉ closure A := fun h =>
      Set.disjoint_left.1 hd2 h (mem_insert _ _)
    obtain ⟨r', hr', hr'd⟩ := Metric.mem_nhds_iff.1 (isOpen_compl_iff.2 isClosed_closure
      |>.mem_nhds hcl)
    have hball : Disjoint (ball ((-1 - q : ℝ) : ℂ) r') A :=
      Set.disjoint_left.2 fun z hz hzA => hr'd hz (subset_closure hzA)
    have := bdryVal_re_lt hU hU0 hσ hr' hball (by linarith)
    have hre : (bdryVal U (-1 - q) σ).re = x₁ := by rw [← hx₁]; simp
    linarith
  have hdet₂ : 0 < (-1 : ℝ) * (-P₂) - 0 * 1 := by simp only [hP₂]; linarith
  have hpole₂ : mobPole 1 (-P₂) = P₂ := by simp [mobPole]
  have hd4 : Disjoint (ball (mobPole 1 (-P₂) : ℂ) r₃) (QuantumZipper.fwdHull W₃ (a₂ (σ₁ T))) := by
    rw [hpole₂, hK₃, hK₂ (σ₁ T) ⟨hT₁, le_rfl⟩, hK₁ T ⟨hT, le_rfl⟩]
    rw [Set.disjoint_left]
    rintro w hw ⟨v, hv, rfl⟩
    have hv' : v ∈ ball (U σ : ℂ) r₃ := by
      rw [mem_ball, dist_eq_norm] at hw ⊢
      have : v + ((-x₁ : ℝ) : ℂ) - (P₂ : ℂ) = v - U σ := by simp only [hP₂]; push_cast; ring
      rwa [this] at hw
    exact Set.disjoint_left.1 hd3 hv' hv
  obtain ⟨τ₄, W₄, _, _, _, hW₄c, hW₄0, hτ₄0, hτ₄m, hτ₄c, h₄⟩ :=
    exists_loewner_mobius_image hW₃c hW₃0 hT₂ hdet₂ one_ne_zero
      (by rw [hpole₂]; simp only [hP₂]; linarith) hr₃ hd4
  refine ⟨fun t => τ₄ (a₂ (σ₁ t)), W₄, hW₄c, by rw [hW₄0]; simp, by simp [hσ₁0, ha₂0, hτ₄0],
    ?_, ?_, fun t ht => ?_⟩
  · -- strict monotonicity of the composed clock
    have hmaps₁ : MapsTo σ₁ (Icc 0 T) (Icc 0 (σ₁ T)) := fun t ht =>
      ⟨by rw [← hσ₁0]; exact hσ₁m.monotoneOn ⟨le_rfl, hT⟩ ht ht.1,
        hσ₁m.monotoneOn ht ⟨hT, le_rfl⟩ ht.2⟩
    have hmaps₂ : MapsTo a₂ (Icc 0 (σ₁ T)) (Icc 0 (a₂ (σ₁ T))) := fun s hs =>
      ⟨by rw [← ha₂0]; exact ha₂m.monotoneOn ⟨le_rfl, hT₁⟩ hs hs.1,
        ha₂m.monotoneOn hs ⟨hT₁, le_rfl⟩ hs.2⟩
    intro t ht t' ht' htt'
    exact hτ₄m (hmaps₂ (hmaps₁ ht)) (hmaps₂ (hmaps₁ ht'))
      (ha₂m (hmaps₁ ht) (hmaps₁ ht') (hσ₁m ht ht' htt'))
  · have hmaps₁ : MapsTo σ₁ (Icc 0 T) (Icc 0 (σ₁ T)) := fun t ht =>
      ⟨by rw [← hσ₁0]; exact hσ₁m.monotoneOn ⟨le_rfl, hT⟩ ht ht.1,
        hσ₁m.monotoneOn ht ⟨hT, le_rfl⟩ ht.2⟩
    have hmaps₂ : MapsTo a₂ (Icc 0 (σ₁ T)) (Icc 0 (a₂ (σ₁ T))) := fun s hs =>
      ⟨by rw [← ha₂0]; exact ha₂m.monotoneOn ⟨le_rfl, hT₁⟩ hs hs.1,
        ha₂m.monotoneOn hs ⟨hT₁, le_rfl⟩ hs.2⟩
    exact hτ₄c.comp (ha₂c.comp hσ₁c hmaps₁) (hmaps₂.comp hmaps₁)
  · have hs₁ : σ₁ t ∈ Icc 0 (σ₁ T) :=
      ⟨by rw [← hσ₁0]; exact hσ₁m.monotoneOn ⟨le_rfl, hT⟩ ht ht.1,
        hσ₁m.monotoneOn ht ⟨hT, le_rfl⟩ ht.2⟩
    have hs₂ : a₂ (σ₁ t) ∈ Icc 0 (a₂ (σ₁ T)) :=
      ⟨by rw [← ha₂0]; exact ha₂m.monotoneOn ⟨le_rfl, hT₁⟩ hs₁ hs₁.1,
        ha₂m.monotoneOn hs₁ ⟨hT₁, le_rfl⟩ hs₁.2⟩
    rw [(h₄ _ hs₂).2.1, hK₃, hK₂ _ hs₁, hK₁ t ht, image_image, image_image, image_image]
    refine image_congr fun z _ => ?_
    simp only [restartMap, hm₁, hφdef, hP₂]
    congr 1
    push_cast
    ring

end CrossRestart

end Sec5

end InteractingSLE
