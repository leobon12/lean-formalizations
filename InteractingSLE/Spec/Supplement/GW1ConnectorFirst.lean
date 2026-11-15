/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1ConnectorFlow
import InteractingSLE.Spec.Supplement.GW3Word
import InteractingSLE.Foundations.Loewner.FiniteEndpointLaunch
import InteractingSLE.Spec.Sec4.RepulsionNoncollision

/-!
# Lemma GW1: the first piece of an extreme walk ends on its own side; `WalkConnectorSideStatement` reduced

Packet PROVE-T14-GW6. Lemma GW1, proof (`source/spec/p577-624.md` L949, p. 618): for the lower-extreme flow (angle
`−π/2`) the left cumulatives of an admissible word exceed `−2` ((GW1.1)), "Thus a lower-extreme continuation threshold
can occur only on its right side … Every finite threshold of a nonempty ordinary stage consequently has physical value
`q_j > w_j`, and is a new original right record".

* **Word sums at an angle** (`neg_two_lt_sum_flowLineRhoL_theta`, `…R_theta`): the partial sums of the angle-`θ`
  flow-line word of data `b` are `−(b(y) + θχ)/λ − 1` (left) and `(b(y) + θχ)/λ − 1` (right) at points `y` off the
  jumps; so they exceed `−2` as soon as `b + θχ < λ` on the left (resp. `> −λ` on the right).
* **The hit is on the admissible side's opposite** (`exists_hit_right_of_tendsto`, `ae_exists_hit_right`, and the
  mirrors): if every left group-end sum of an integrated `SLE_a(ρ)` evolution exceeds a constant `c > −2`, then at a
  finite positive lifetime the colliding group is a right one (the left colliding group is an initial segment with
  sum `> −2`, `Sec4.neg_two_lt_sum_collision`), so a right force point `x > 0` is alive before the lifetime and not at
  it.
* **The ambient bounds** (`ambient_bounds`, GW0 on the counterflow word, as in
  `GW3Word.gw3WordBoundStatement_of_inputs`): `b(t) − (π/2)χ < λ` for `t < 0` and `−λ < b(t) + (π/2)χ` for `t > 0`
  off the jumps.
* **The first piece** (`ae_status_run_one_ne_right`, `ae_status_run_one_ne_left`): almost surely the first piece of
  the right walk does not end at a new left record, and the first piece of the left walk not at a new right record.
  The frozen `ExplState.launch` tests the right side first, so for the left walk one needs that **no** point right of
  the seed is swallowed at a left threshold: the seeds have separated (`GW1Conn.lt_of_tendsto_marks`) and the right
  seed gap stays open (`GW1Conn.exists_isForwardSol_of_tendsto_gap`, file `GW1ConnectorFlow`).
* **`walkConnectorSideStatement_of_later`**: `WalkConnectorSideStatement` from GW0's forward implication and the named
  input `WalkLaterRecordStatement` (the same assertion for the later pieces, launched from a boundary mark in a
  random conditional domain).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol chiC)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW1Conn

open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

/-! ### Word sums of the flow-line word at an angle -/

/-- Only the seed weight of the left flow-line word depends on the angle. -/
theorem flowLineRhoL_theta (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (θ : ℝ) (l : Fin (flowLineNL b J 0)) :
    flowLineRhoL κ b J 0 θ l =
      flowLineRhoL κ b J 0 0 l + if (l : ℕ) = 0 then -(θ * chiC κ / sleLambda κ) else 0 := by
  obtain ⟨m, hm⟩ := l
  cases m with
  | zero =>
    simp only [↓reduceIte]
    show -(leftLim b 0 + θ * chiC κ) / sleLambda κ - 1 =
      -(leftLim b 0 + 0 * chiC κ) / sleLambda κ - 1 + -(θ * chiC κ / sleLambda κ)
    ring
  | succ m =>
    simp only [Nat.add_one_ne_zero, ↓reduceIte, add_zero]
    rfl

/-- Only the seed weight of the right flow-line word depends on the angle. -/
theorem flowLineRhoR_theta (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (θ : ℝ) (l : Fin (flowLineNR b J 0)) :
    flowLineRhoR κ b J 0 θ l =
      flowLineRhoR κ b J 0 0 l + if (l : ℕ) = 0 then θ * chiC κ / sleLambda κ else 0 := by
  obtain ⟨m, hm⟩ := l
  cases m with
  | zero =>
    simp only [↓reduceIte]
    show (rightLim b 0 + θ * chiC κ) / sleLambda κ - 1 =
      (rightLim b 0 + 0 * chiC κ) / sleLambda κ - 1 + θ * chiC κ / sleLambda κ
    ring
  | succ m =>
    simp only [Nat.add_one_ne_zero, ↓reduceIte, add_zero]
    rfl

/-- A sum over an initial segment of the seed-only correction. -/
theorem sum_filter_le_ite_val_eq_zero {n : ℕ} (c : ℝ) (j z : Fin n) (hz : (z : ℕ) = 0) :
    ∑ l ∈ univ.filter (fun l : Fin n => l ≤ j), (if (l : ℕ) = 0 then c else 0) = c := by
  have hzj : z ≤ j := by rw [Fin.le_def, hz]; exact Nat.zero_le _
  refine (Finset.sum_eq_single_of_mem z (Finset.mem_filter.2 ⟨mem_univ _, hzj⟩)
    (fun l _ hl => ite_eq_right_iff.2 fun h => absurd (Fin.ext (h.trans hz.symm)) hl)).trans ?_
  simp [hz]

/-- **Left partial sums at an angle from a pointwise bound**: if `b + θχ < λ` left of the seed (off the jumps),
every left partial sum of the angle-`θ` flow-line word from `0` exceeds `−2`. -/
theorem neg_two_lt_sum_flowLineRhoL_theta {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {θ : ℝ}
    (hL : ∀ y, y < 0 → y ∉ J → b y + θ * chiC κ < sleLambda κ) (j : Fin (flowLineNL b J 0)) :
    -2 < ∑ l ∈ univ.filter (fun l => l ≤ j), flowLineRhoL κ b J 0 θ l := by
  have hsum : ∑ l ∈ univ.filter (fun l => l ≤ j), flowLineRhoL κ b J 0 θ l =
      ∑ l ∈ univ.filter (fun l => l ≤ j), flowLineRhoL κ b J 0 0 l - θ * chiC κ / sleLambda κ := by
    rw [Finset.sum_congr rfl (fun l _ => flowLineRhoL_theta κ b J θ l), Finset.sum_add_distrib,
      sum_filter_le_ite_val_eq_zero _ j ⟨0, by unfold flowLineNL; omega⟩ rfl]
    ring
  rw [hsum, GW3Word.filter_le_eq_filter_le_flowLineXL]
  obtain ⟨y, -, hy, hyJ, hS⟩ := Sec5.Aux22ChartE.exists_sum_flowLineRhoL_eq hκ hb
    (lo := flowLineXL b J 0 j - 1) (by linarith) (GW3Word.flowLineXL_nonpos b J j)
  rw [hS, Sec4.cumWeightLeft]
  have hl := Sec4.sleLambda_pos hκ
  have h1 := hL y (lt_of_lt_of_le hy (GW3Word.flowLineXL_nonpos b J j)) hyJ
  have h2 : (b y + θ * chiC κ) / sleLambda κ < 1 := by rw [div_lt_one hl]; exact h1
  have e : -b y / sleLambda κ - 1 - θ * chiC κ / sleLambda κ = -((b y + θ * chiC κ) / sleLambda κ) - 1 := by ring
  rw [e]
  linarith

/-- **Right partial sums at an angle from a pointwise bound**: if `−λ < b + θχ` right of the seed (off the jumps),
every right partial sum of the angle-`θ` flow-line word from `0` exceeds `−2`. -/
theorem neg_two_lt_sum_flowLineRhoR_theta {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {θ : ℝ}
    (hR : ∀ y, 0 < y → y ∉ J → -sleLambda κ < b y + θ * chiC κ) (j : Fin (flowLineNR b J 0)) :
    -2 < ∑ l ∈ univ.filter (fun l => l ≤ j), flowLineRhoR κ b J 0 θ l := by
  have hsum : ∑ l ∈ univ.filter (fun l => l ≤ j), flowLineRhoR κ b J 0 θ l =
      ∑ l ∈ univ.filter (fun l => l ≤ j), flowLineRhoR κ b J 0 0 l + θ * chiC κ / sleLambda κ := by
    rw [Finset.sum_congr rfl (fun l _ => flowLineRhoR_theta κ b J θ l), Finset.sum_add_distrib,
      sum_filter_le_ite_val_eq_zero _ j ⟨0, by unfold flowLineNR; omega⟩ rfl]
  rw [hsum, GW3Word.filter_le_eq_filter_flowLineXR_le]
  obtain ⟨y, hy, hyJ, hS⟩ := Sec5.Aux22ChartE.exists_sum_flowLineRhoR_eq hκ hb (GW3Word.flowLineXR_nonneg b J j)
  rw [hS, Sec4.cumWeightRight]
  have hl := Sec4.sleLambda_pos hκ
  have h1 := hR y (lt_of_le_of_lt (GW3Word.flowLineXR_nonneg b J j) hy) hyJ
  have h2 : -1 < (b y + θ * chiC κ) / sleLambda κ := by rw [lt_div_iff₀ hl]; linarith
  have e : b y / sleLambda κ - 1 + θ * chiC κ / sleLambda κ = (b y + θ * chiC κ) / sleLambda κ - 1 := by ring
  rw [e]
  linarith

/-- The left side of the angle-`θ` flow-line word has group-end sums at least some `c > −2` (positions `−xL`). -/
theorem exists_hasGroupEndSums_flowLineL {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {θ : ℝ}
    (hL : ∀ y, y < 0 → y ∉ J → b y + θ * chiC κ < sleLambda κ) :
    ∃ c : ℝ, -2 < c ∧ Sec4.HasGroupEndSums c (flowLineRhoL κ b J 0 θ) (-flowLineXL b J 0) := by
  obtain ⟨c, hc, hc'⟩ := GW0.exists_neg_two_lt_le
    (fun j => ∑ l ∈ univ.filter (fun l => l ≤ j), flowLineRhoL κ b J 0 θ l) (fun _ => True)
    (fun j _ => neg_two_lt_sum_flowLineRhoL_theta hκ hb hL j)
  exact ⟨c, hc, fun j _ => hc' j trivial⟩

/-- The right side of the angle-`θ` flow-line word has group-end sums at least some `c > −2`. -/
theorem exists_hasGroupEndSums_flowLineR {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {θ : ℝ}
    (hR : ∀ y, 0 < y → y ∉ J → -sleLambda κ < b y + θ * chiC κ) :
    ∃ c : ℝ, -2 < c ∧ Sec4.HasGroupEndSums c (flowLineRhoR κ b J 0 θ) (flowLineXR b J 0) := by
  obtain ⟨c, hc, hc'⟩ := GW0.exists_neg_two_lt_le
    (fun j => ∑ l ∈ univ.filter (fun l => l ≤ j), flowLineRhoR κ b J 0 θ l) (fun _ => True)
    (fun j _ => neg_two_lt_sum_flowLineRhoR_theta hκ hb hR j)
  exact ⟨c, hc, fun j _ => hc' j trivial⟩

/-! ### The hit at a finite lifetime is on the side opposite an admissible one -/

section Hit

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **A right force point is hit when the left side is admissible** (deterministic): for a path with all
conditions of Definition 2.1 except the driving equation, at a finite positive lifetime `T` at which the state
converges to a threshold state, if the left side has injective antitone positions and group-end sums at least some
`c > −2`, then some right force point `x > 0` is alive on every `[0, r]`, `r < T`, and not on `[0, T]`, for every
driver agreeing with `W` before `T`. -/
theorem exists_hit_right_of_tendsto (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {c : ℝ} (hc : -2 < c)
    (hxL : Antitone xL) (hxLi : Function.Injective xL) (hL : Sec4.HasGroupEndSums c ρL (-xL))
    {T : ℝ≥0} (hT : 0 < T) (hζ : (T : ℝ≥0∞) = ζ) {w₀ : ℝ} {vL₀ : Fin nL → ℝ} {vR₀ : Fin nR → ℝ}
    (hlim : Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)))
    (hthr : ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) {U : ℝ → ℝ}
    (hU : ∀ r : ℝ, 0 ≤ r → r < T → U r = w r.toNNReal) :
    ∃ x : ℝ, 0 < x ∧ (∀ r : ℝ, r < T → ∃ u, IsForwardSol U (x : ℂ) r u) ∧
      ¬ ∃ u, IsForwardSol U (x : ℂ) T u := by
  have := Sec2.IsForcePath.neBot_nhdsLT hT
  have hev : ∀ᶠ t : ℝ≥0 in 𝓝[<] T, (t : ℝ≥0∞) < ζ := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [← hζ]; exact_mod_cast ht
  have hw : Tendsto w (𝓝[<] T) (𝓝 w₀) := (continuous_fst.tendsto _).comp hlim
  have hvL : ∀ i, Tendsto (fun t => vL i t) (𝓝[<] T) (𝓝 (vL₀ i)) := fun i =>
    tendsto_pi_nhds.1 hlim.snd_nhds.fst_nhds i
  have hLs : -2 < ∑ i ∈ univ.filter (fun i => vL₀ i = w₀), ρL i := by
    have h' := Sec4.neg_two_lt_sum_collision (v₀ := -vL₀) (w₀ := -w₀) hc
      (fun i j hij => neg_le_neg (hxL hij)) hL
      (fun i j hij => neg_le_neg (le_of_tendsto_of_tendsto (hvL j) (hvL i)
        (hev.mono fun t ht => h.antitone_vL ht hij)))
      (fun i => neg_le_neg (le_of_tendsto_of_tendsto (hvL i) hw (hev.mono fun t ht => h.vL_le_w ht i)))
      (fun i j hij => by
        have e : i = j := hxLi (neg_injective hij)
        rw [e])
    simpa only [Pi.neg_apply, neg_inj] using h'
  have hR : ∑ i ∈ univ.filter (fun i => vR₀ i = w₀), ρR i ≤ -2 :=
    hthr.resolve_left (not_le.2 hLs)
  obtain ⟨k, hk, hk0⟩ := h.exists_gapR_of_tendsto hT hζ hlim hR
  have hv : Tendsto (vR k) (𝓝[<] T) (𝓝 (vR₀ k)) := tendsto_pi_nhds.1 hlim.snd_nhds.snd_nhds k
  refine ⟨xR k, ?_, fun r hr => ⟨_, h.isForwardSol_gapR hζ hk hU hr⟩,
    Sec2.IsForcePath.not_exists_isForwardSol_of_tendsto hT (fun r hr => h.isForwardSol_gapR hζ hk hU hr) ?_⟩
  · have h0 := hk 0 hT
    rwa [h.w_zero, h.vR_zero] at h0
  · have hg : Tendsto (fun t => vR k t - w t) (𝓝[<] T) (𝓝 0) := by
      simpa [hk0] using hv.sub hw
    have h2 := (Complex.continuous_ofReal.tendsto 0).comp (hg.comp (Sec2.IsForcePath.tendsto_toNNReal_nhdsLT T))
    rw [Complex.ofReal_zero] at h2
    exact h2

/-- **A left force point is hit when the right side is admissible** (deterministic; mirror of
`exists_hit_right_of_tendsto`). -/
theorem exists_hit_left_of_tendsto (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {c : ℝ} (hc : -2 < c)
    (hxR : Monotone xR) (hxRi : Function.Injective xR) (hR : Sec4.HasGroupEndSums c ρR xR)
    {T : ℝ≥0} (hT : 0 < T) (hζ : (T : ℝ≥0∞) = ζ) {w₀ : ℝ} {vL₀ : Fin nL → ℝ} {vR₀ : Fin nR → ℝ}
    (hlim : Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)))
    (hthr : ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) {U : ℝ → ℝ}
    (hU : ∀ r : ℝ, 0 ≤ r → r < T → U r = w r.toNNReal) :
    ∃ x : ℝ, x < 0 ∧ (∀ r : ℝ, r < T → ∃ u, IsForwardSol U (x : ℂ) r u) ∧
      ¬ ∃ u, IsForwardSol U (x : ℂ) T u := by
  have := Sec2.IsForcePath.neBot_nhdsLT hT
  have hev : ∀ᶠ t : ℝ≥0 in 𝓝[<] T, (t : ℝ≥0∞) < ζ := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [← hζ]; exact_mod_cast ht
  have hw : Tendsto w (𝓝[<] T) (𝓝 w₀) := (continuous_fst.tendsto _).comp hlim
  have hvR : ∀ i, Tendsto (fun t => vR i t) (𝓝[<] T) (𝓝 (vR₀ i)) := fun i =>
    tendsto_pi_nhds.1 hlim.snd_nhds.snd_nhds i
  have hRs : -2 < ∑ i ∈ univ.filter (fun i => vR₀ i = w₀), ρR i :=
    Sec4.neg_two_lt_sum_collision hc hxR hR
      (fun i j hij => le_of_tendsto_of_tendsto (hvR i) (hvR j) (hev.mono fun t ht => h.monotone_vR ht hij))
      (fun i => le_of_tendsto_of_tendsto hw (hvR i) (hev.mono fun t ht => h.w_le_vR ht i))
      (fun i j hij => by
        have e : i = j := hxRi hij
        rw [e])
  have hLs : ∑ i ∈ univ.filter (fun i => vL₀ i = w₀), ρL i ≤ -2 :=
    hthr.resolve_right (not_le.2 hRs)
  -- the left group, through the reflection
  have hlim' : Tendsto (fun t => ((-w) t, fun i => -vR i t, fun i => -vL i t)) (𝓝[<] T)
      (𝓝 (-w₀, fun i => -vR₀ i, fun i => -vL₀ i)) := by
    have hcont : Continuous fun p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) =>
        (-p.1, fun i => -p.2.2 i, fun i => -p.2.1 i) := by fun_prop
    exact (hcont.tendsto _).comp hlim
  have hS : (∑ i ∈ univ.filter (fun i => -vL₀ i = -w₀), ρL i) ≤ -2 := by
    simpa only [neg_inj] using hLs
  obtain ⟨k, hk, hk0⟩ := h.reflect.exists_gapR_of_tendsto hT hζ hlim' hS
  have hk' : ∀ t : ℝ≥0, t < T → vL k t < w t := fun t ht => by simpa using hk t ht
  have hk0' : vL₀ k = w₀ := neg_inj.1 hk0
  have hv : Tendsto (vL k) (𝓝[<] T) (𝓝 (vL₀ k)) := tendsto_pi_nhds.1 hlim.snd_nhds.fst_nhds k
  refine ⟨xL k, ?_, fun r hr => ⟨_, h.isForwardSol_gapL hζ hk' hU hr⟩,
    Sec2.IsForcePath.not_exists_isForwardSol_of_tendsto hT (fun r hr => h.isForwardSol_gapL hζ hk' hU hr) ?_⟩
  · have h0 := hk' 0 hT
    rwa [h.w_zero, h.vL_zero] at h0
  · have hg : Tendsto (fun t => vL k t - w t) (𝓝[<] T) (𝓝 0) := by
      simpa [hk0'] using hv.sub hw
    have h2 := (Complex.continuous_ofReal.tendsto 0).comp (hg.comp (Sec2.IsForcePath.tendsto_toNNReal_nhdsLT T))
    rw [Complex.ofReal_zero] at h2
    exact h2

end Hit

section AeHit

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **Almost surely a right real point is swallowed at a finite positive lifetime when the left side is
admissible.** -/
theorem ae_exists_hit_right (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) (ha : 0 < a)
    {c : ℝ} (hc : -2 < c) (hxL : Antitone xL) (hxLi : Function.Injective xL)
    (hL : Sec4.HasGroupEndSums c ρL (-xL)) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω → ∀ U : ℝ → ℝ,
      (∀ r : ℝ, 0 ≤ r → r < T → U r = W r.toNNReal ω) →
      ∃ x : ℝ, 0 < x ∧ (∀ r : ℝ, r < T → ∃ u, IsForwardSol U (x : ℂ) r u) ∧
        ¬ ∃ u, IsForwardSol U (x : ℂ) T u := by
  filter_upwards [h.ae_isIntegratedSLEPath, h.ae_tendsto_threshold ha] with ω hp hth T hT hζ U hU
  obtain ⟨w₀, vL₀, vR₀, hlim, hthr⟩ := hth T hT hζ
  exact exists_hit_right_of_tendsto hp.isForcePath hc hxL hxLi hL hT hζ hlim hthr hU

/-- **Almost surely a left real point is swallowed at a finite positive lifetime when the right side is
admissible.** -/
theorem ae_exists_hit_left (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) (ha : 0 < a)
    {c : ℝ} (hc : -2 < c) (hxR : Monotone xR) (hxRi : Function.Injective xR)
    (hR : Sec4.HasGroupEndSums c ρR xR) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω → ∀ U : ℝ → ℝ,
      (∀ r : ℝ, 0 ≤ r → r < T → U r = W r.toNNReal ω) →
      ∃ x : ℝ, x < 0 ∧ (∀ r : ℝ, r < T → ∃ u, IsForwardSol U (x : ℂ) r u) ∧
        ¬ ∃ u, IsForwardSol U (x : ℂ) T u := by
  filter_upwards [h.ae_isIntegratedSLEPath, h.ae_tendsto_threshold ha] with ω hp hth T hT hζ U hU
  obtain ⟨w₀, vL₀, vR₀, hlim, hthr⟩ := hth T hT hζ
  exact exists_hit_left_of_tendsto hp.isForcePath hc hxR hxRi hR hT hζ hlim hthr hU

end AeHit

/-! ### The first piece of a walk -/

/-- The first instruction of a walk program launches its first piece from the root state. -/
theorem run_one_boundaryWalkSpec (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D 1 =
      ExplState.launch (ExplState.init 0) 0 (D 0) θ ⊤ := by
  have h := Exist.Staged.run_succ (κ := κ) (b := b) (jumps := jumps) (boundaryWalkSpec b jumps θ right) D 0
  rw [getElem?_boundaryWalkSpec, ite_eq_left (by simp [boundaryWalkSpec, List.replicate_succ])] at h
  rw [h]
  rfl

/-- The root state launched with a right hit at a finite positive lifetime does not end at a new left record. -/
theorem status_launch_init_ne_left (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ)
    (hhit : D.2 ≠ ⊤ → D.2 ≠ 0 → ∃ x : ℝ, 0 < x ∧
      (∀ r : ℝ, r < (D.2.toNNReal : ℝ) → ∃ u, IsForwardSol
        (fun r : ℝ => D.1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) D.2).toNNReal) (x : ℂ) r u) ∧
      ¬ ∃ u, IsForwardSol (fun r : ℝ => D.1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) D.2).toNNReal)
        (x : ℂ) (D.2.toNNReal : ℝ) u) :
    (ExplState.launch (ExplState.init 0) 0 D θ ⊤).2.2.2.2.2.1 ≠ stThr (some false) := by
  have hstop : min (⊤ : ℝ≥0∞) D.2 = D.2 := min_eq_right le_top
  have hc : ∀ y : ℝ, (Chart.id.recenter 0).1 (y : ℂ) = (y : ℂ) := fun y => by
    simp [Chart.recenter, Chart.id]
  unfold ExplState.launch ExplState.init
  dsimp only
  rw [hstop]
  split_ifs with h1 h2 h3 h4 h5 <;> try simp
  obtain ⟨x, hx, ha, hd⟩ := hhit h1 h3
  exact h4 ⟨x, hx, by rw [hc]; exact ⟨ha, hd⟩⟩

/-- The root state launched with no right hit at a finite positive lifetime does not end at a new right record. -/
theorem status_launch_init_ne_right (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ)
    (hnoR : D.2 ≠ ⊤ → D.2 ≠ 0 → ¬ ∃ x : ℝ, 0 < x ∧
      (∀ r : ℝ, r < (D.2.toNNReal : ℝ) → ∃ u, IsForwardSol
        (fun r : ℝ => D.1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) D.2).toNNReal) (x : ℂ) r u) ∧
      ¬ ∃ u, IsForwardSol (fun r : ℝ => D.1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) D.2).toNNReal)
        (x : ℂ) (D.2.toNNReal : ℝ) u) :
    (ExplState.launch (ExplState.init 0) 0 D θ ⊤).2.2.2.2.2.1 ≠ stThr (some true) := by
  have hstop : min (⊤ : ℝ≥0∞) D.2 = D.2 := min_eq_right le_top
  have hc : ∀ y : ℝ, (Chart.id.recenter 0).1 (y : ℂ) = (y : ℂ) := fun y => by
    simp [Chart.recenter, Chart.id]
  unfold ExplState.launch ExplState.init
  dsimp only
  rw [hstop]
  split_ifs with h1 h2 h3 h4 h5 <;> try simp
  obtain ⟨x, hx, ha, hd⟩ := h4
  exact hnoR h1 h3 ⟨x, hx, by rw [hc] at ha hd; exact ⟨ha, hd⟩⟩

/-! ### The ambient bounds -/

/-- **The ambient bounds** (GW0's forward implication on the ambient counterflow word, as in
`GW3Word.gw3WordBoundStatement_of_inputs`): in the setting of Theorem 1.4, `b(t) − (π/2)χ < λ` for `t < 0` and
`−λ < b(t) + (π/2)χ` for `t > 0`, off the jumps. -/
theorem ambient_bounds (hGW0 : GW0.GW0ForwardStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ}
    {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) :
    (∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ) ∧
      (∀ t, 0 < t → t ∉ jumps → -sleLambda κ < b t + Real.pi / 2 * chiC κ) := by
  have hκ' : 0 < 16 / κ := div_pos (by norm_num) hκ
  have hΛ := Sec4.sleLambda_sixteen_div_eq_sub hκ
  obtain ⟨_, -, hfla⟩ := GW2Cone.isFlowLineDriver_counterflowData hκ hb hh hcf
  obtain ⟨hAL, hAR⟩ := GW0.counterflow_admissible hGW0 hκ hκ4 hfla hζ'
  have hcfb := Sec7.StripSysField.isPiecewiseConstant_counterflowData κ hb
  refine ⟨fun t ht htJ => ?_, fun t ht htJ => ?_⟩
  · have hy : 0 < -t⁻¹ := neg_pos.2 (inv_lt_zero.2 ht)
    have h1 := GW3Word.neg_lambda_lt_of_sum_flowLineRhoR hκ' hcfb hAR hy
      (GW3Word.negInv_notMem_returnExcept ht.ne htJ)
    rw [GW3Word.counterflowData_of_pos hκ b hy, GW3Word.negInv_negInv, hΛ] at h1
    linarith
  · have hy : -t⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 ht)
    have h1 := GW3Word.lt_lambda_of_sum_flowLineRhoL hκ' hcfb hAL hy
      (GW3Word.negInv_notMem_returnExcept ht.ne' htJ)
    rw [GW3Word.counterflowData_of_neg hκ b hy, GW3Word.negInv_negInv, hΛ] at h1
    linarith

/-- The root seed bounds of the two walks, from the ambient bounds. -/
theorem root_bounds {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hL : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ)
    (hR : ∀ t, 0 < t → t ∉ jumps → -sleLambda κ < b t + Real.pi / 2 * chiC κ) :
    leftLim b 0 + -(Real.pi / 2) * chiC κ < sleLambda κ ∧
      -sleLambda κ < rightLim b 0 + Real.pi / 2 * chiC κ := by
  obtain ⟨t, -, ht0, htJ, hlt⟩ := Sec5.Aux22ChartE.exists_leftLim_eq hb (z := 0) (lo := -1) (by norm_num)
  obtain ⟨t', ht'0, -, ht'J, hrt⟩ := Sec5.Aux22ChartE.exists_rightLim_eq hb (z := 0) (hi := 1) (by norm_num)
  exact ⟨by rw [hlt]; exact hL t ht0 htJ, by rw [hrt]; exact hR t' ht'0 ht'J⟩

/-! ### The first pieces of the two walks -/

section FirstPiece

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The first piece of the right walk does not end at a new left record** (almost surely; Lemma GW1, (GW1.1)):
its left word is admissible by the ambient bound, so at a finite positive lifetime a right point is swallowed. -/
theorem ae_status_run_one_ne_right (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hamb : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) E) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun k => E k ω) 1).2.2.2.2.2.1 ≠ stThr (some false) := by
  obtain ⟨_, 𝓕, VL, VR, B, -, hC⟩ :=
    hE.isFlowLineDriver_first hκ hb hh rfl (θ := -(Real.pi / 2)) (t := ⊤) rfl
  obtain ⟨c, hc, hgc⟩ := exists_hasGroupEndSums_flowLineL hκ hb hamb
  have hanti : StrictAnti (flowLineXL b jumps 0) := fun i j hij => GW0.flowLineXL_lt b jumps 0 hij
  filter_upwards [ae_exists_hit_right hC.1 hκ hc hanti.antitone hanti.injective hgc] with ω hω
  rw [run_one_boundaryWalkSpec]
  refine status_launch_init_ne_left _ _ fun hD hpos => ?_
  set T : ℝ≥0 := (E 0 ω).2.toNNReal with hTdef
  have hTζ : (T : ℝ≥0∞) = (E 0 ω).2 := ENNReal.coe_toNNReal hD
  have hT : 0 < T := by
    rw [pos_iff_ne_zero]
    intro h0
    rw [h0, ENNReal.coe_zero] at hTζ
    exact hpos hTζ.symm
  refine hω T hT hTζ _ fun r hr hrT => ?_
  have hlt : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < (E 0 ω).2 := by
    rw [← hTζ, ENNReal.coe_lt_coe, Real.toNNReal_lt_iff_lt_coe hr]
    exact hrT
  simp only [min_eq_left hlt.le, ENNReal.toNNReal_coe]

/-- **The first piece of the left walk does not end at a new right record** (almost surely; Lemma GW1 reflected):
its right word is admissible by the ambient bound, so at a finite positive lifetime the colliding group is on the
left, the left seed collides, the two seeds have separated, the right seed gap stays open, and no point right of the
seed is swallowed (`exists_isForwardSol_of_tendsto_gap`). -/
theorem ae_status_run_one_ne_left (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hamb : ∀ t, 0 < t → t ∉ jumps → -sleLambda κ < b t + Real.pi / 2 * chiC κ)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps (Real.pi / 2) false) E) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
      (fun k => E k ω) 1).2.2.2.2.2.1 ≠ stThr (some true) := by
  obtain ⟨_, 𝓕, VL, VR, B, -, hC⟩ :=
    hE.isFlowLineDriver_first hκ hb hh rfl (θ := Real.pi / 2) (t := ⊤) rfl
  obtain ⟨c, hc, hgc⟩ := exists_hasGroupEndSums_flowLineR hκ hb hamb
  have hmono : StrictMono (flowLineXR b jumps 0) := fun i j hij => GW0.flowLineXR_lt b jumps 0 hij
  have hanti : StrictAnti (flowLineXL b jumps 0) := fun i j hij => GW0.flowLineXL_lt b jumps 0 hij
  filter_upwards [hC.1.ae_isIntegratedSLEPath, hC.1.ae_tendsto_threshold hκ, hE.2.2.1 0] with ω hp hth hcl
  rw [run_one_boundaryWalkSpec]
  refine status_launch_init_ne_right _ _ fun hD hpos => ?_
  set T : ℝ≥0 := (E 0 ω).2.toNNReal with hTdef
  have hTζ : (T : ℝ≥0∞) = (E 0 ω).2 := ENNReal.coe_toNNReal hD
  have hT : 0 < T := by
    rw [pos_iff_ne_zero]
    intro h0
    rw [h0, ENNReal.coe_zero] at hTζ
    exact hpos hTζ.symm
  obtain ⟨w₀, vL₀, vR₀, hlim, hthr⟩ := hth T hT hTζ
  have hfp := hp.isForcePath
  have := Sec2.IsForcePath.neBot_nhdsLT hT
  have hev : ∀ᶠ t : ℝ≥0 in 𝓝[<] T, (t : ℝ≥0∞) < (E 0 ω).2 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [← hTζ]; exact_mod_cast ht
  have hw : Tendsto (fun t => (E 0 ω).1 t) (𝓝[<] T) (𝓝 w₀) := (continuous_fst.tendsto _).comp hlim
  have hvL : ∀ i, Tendsto (fun t => VL i t ω) (𝓝[<] T) (𝓝 (vL₀ i)) := fun i =>
    tendsto_pi_nhds.1 hlim.snd_nhds.fst_nhds i
  have hvR : ∀ i, Tendsto (fun t => VR i t ω) (𝓝[<] T) (𝓝 (vR₀ i)) := fun i =>
    tendsto_pi_nhds.1 hlim.snd_nhds.snd_nhds i
  -- the right colliding group is admissible, so the left one is bad and nonempty
  have hRs : -2 < ∑ i ∈ univ.filter (fun i => vR₀ i = w₀), flowLineRhoR κ b jumps 0 (Real.pi / 2) i :=
    Sec4.neg_two_lt_sum_collision hc hmono.monotone hgc
      (fun i j hij => le_of_tendsto_of_tendsto (hvR i) (hvR j) (hev.mono fun t ht => hfp.monotone_vR ht hij))
      (fun i => le_of_tendsto_of_tendsto hw (hvR i) (hev.mono fun t ht => hfp.w_le_vR ht i))
      (fun i j hij => by rw [hmono.injective hij])
  have hLs := hthr.resolve_right (not_le.2 hRs)
  obtain ⟨i, hi⟩ : ∃ i, vL₀ i = w₀ := by
    by_contra hn
    push Not at hn
    have he : univ.filter (fun i => vL₀ i = w₀) = ∅ := Finset.filter_eq_empty_iff.2 fun i _ => hn i
    rw [he, Finset.sum_empty] at hLs
    linarith
  set i0 : Fin (flowLineNL b jumps 0) := ⟨0, by unfold flowLineNL; omega⟩ with hi0
  set j0 : Fin (flowLineNR b jumps 0) := ⟨0, by unfold flowLineNR; omega⟩ with hj0
  have hvL0 : vL₀ i0 = w₀ := by
    refine le_antisymm (le_of_tendsto_of_tendsto (hvL i0) hw (hev.mono fun t ht => hfp.vL_le_w ht i0)) ?_
    rw [← hi]
    exact le_of_tendsto_of_tendsto (hvL i) (hvL i0)
      (hev.mono fun t ht => hfp.antitone_vL ht (show i0 ≤ i from Fin.le_def.2 (Nat.zero_le _)))
  have hx00 : flowLineXL b jumps 0 i0 ≤ flowLineXR b jumps 0 j0 := le_of_eq rfl
  have hsep := GW1Conn.lt_of_tendsto_marks hfp hx00 hT hTζ (hvL i0) (hvR j0)
  -- the launch driver is continuous
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) < (E 0 ω).2} = Iio T := by
    ext t
    show (t : ℝ≥0∞) < (E 0 ω).2 ↔ t < T
    rw [← hTζ, ENNReal.coe_lt_coe]
  have hcont : ContinuousOn (E 0 ω).1 (Iio T) := by
    have := hfp.continuousOn_w
    rwa [hset] at this
  have hval : (E 0 ω).1 T = w₀ := hcl hD (pos_iff_ne_zero.2 hpos) w₀ hw
  have hUc := continuous_launchDriver hTζ hcont (by rw [hval]; exact hw)
  rintro ⟨x, hx, halive, hdead⟩
  refine hdead (exists_isForwardSol_of_tendsto_gap hfp (iR := j0) rfl hT hTζ (g := vR₀ j0 - w₀)
    (by linarith) ((hvR j0).sub hw) hUc (fun r hr hrT => launchDriver_eq hTζ hr hrT) hx halive)

end FirstPiece

/-! ### `WalkConnectorSideStatement` -/

/-- **Named input: the later pieces of an extreme walk end on its own side** (Lemma GW1, p. 619: "Thus a
lower-extreme continuation threshold can occur only on its right side. … Every finite threshold of a nonempty ordinary
stage consequently has physical value `q_j > w_j`, and is a new original right record"; "Reflection gives the left
boundary walk `L` at angle `+π/2`"). Setting of `GW3Word.WalkConnectorSideStatement` (verbatim binders): almost surely
no instruction after the first ends the right walk at a new left record (status *thr* `some false`), and none ends
the left walk at a new right record. (The first instruction is `ae_status_run_one_ne_right`/`…_left`; a continuation
instruction never produces a threshold status.) -/
def WalkLaterRecordStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      ∀ᵐ ω₀ ∂P, ∀ k : ℕ, 0 < k →
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω₀) (k + 1)).2.2.2.2.2.1 ≠
          stThr (some false) ∧
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun j => E (boundaryWalkSpec b jumps (Real.pi / 2) false) j ω₀) (k + 1)).2.2.2.2.2.1 ≠
          stThr (some true)

/-- **`WalkConnectorSideStatement` from GW0's forward implication and the later pieces** (Lemma GW1, "Every
nontrivial real connector is rightward"; conditional helper with a distinct name). The first piece of each walk is
proved (`ae_status_run_one_ne_right`, `ae_status_run_one_ne_left`), the zero-lifetime cases are deterministic
(admissible seeds, the root seed bound from the ambient bounds), and the walk bookkeeping is
`arcs_subset_Ici_of_forall_ne` / `arcs_subset_Iic_of_forall_ne`. -/
theorem walkConnectorSideStatement_of_later (hGW0 : GW0.GW0ForwardStatement.{u})
    (hlater : WalkLaterRecordStatement.{u}) : GW3Word.WalkConnectorSideStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE
  obtain ⟨hambL, hambR⟩ := ambient_bounds hGW0 hκ hκ4 hb hh hcf hζ'
  obtain ⟨hrootL, hrootR⟩ := root_bounds hb hambL hambR
  have hpi := Real.pi_pos
  have hSR := hE _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps
    (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith⟩ true)
  have hSL := hE _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps
    (θ := Real.pi / 2) ⟨by linarith, le_rfl⟩ false)
  filter_upwards [hlater κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE,
    ae_status_run_one_ne_right hκ hb hh hambL hSR, ae_status_run_one_ne_left hκ hb hh hambR hSL]
    with ω hlat h1R h1L
  refine ⟨arcs_subset_Ici_of_forall_ne hrootL _ fun k => ?_, arcs_subset_Iic_of_forall_ne hrootR _ fun k => ?_⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact h1R
    · exact (hlat k hk).1
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact h1L
    · exact (hlat k hk).2

end GW1Conn

end Theorem14

end InteractingSLE
