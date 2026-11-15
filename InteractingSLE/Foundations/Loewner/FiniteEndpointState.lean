/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.CriticalLifetime
import QuantumZipper.Proofs.Thm18.ASepCentre
import QuantumZipper.Proofs.RS.RealAlive

/-!
# The force points at a finite lifetime: the swallowed real point

Packet PROVE-ENDPOINT. Deterministic facts about one path satisfying `Sec2.IsForcePath` (every
condition of Definition 2.1 except the driving equation) at a finite positive lifetime `ζ = T` at
which the state `(W, V^L, V^R)` converges to a limit satisfying the continuation-threshold condition
(Aux. lemma 3, `IsIntegratedSLEEvolution.ae_tendsto_threshold`, gives this almost surely).

* `IsForcePath.vR_sub_vR_le_of_le`, `IsForcePath.vR_eq_of_eq`: on one side, the spread of two force
  coordinates is nonincreasing, so two right force points that met stay together.
* `IsForcePath.exists_gapR_of_tendsto`: if the right colliding group has weight `≤ −2`, its last
  member `k` (the group is an initial segment `0..k`) is strictly to the right of the driver at every
  `t < T` and collides with it at `T`. Proof: at a first meeting `W_t = V^{k,R}_t` before `T`, the
  whole group `0..k` meets the driver; since the threshold condition fails at `t`, a further force
  point `j > k` meets the driver at `t`, then stays merged with `k`, and so belongs to the
  colliding group at `T`, contradicting maximality of `k`.
* `IsForcePath.exists_gap_of_tendsto`: either side (the left side by the reflection
  `IsForcePath.reflect`).
* `IsForcePath.isForwardSol_gapR`, `IsForcePath.isForwardSol_gapL`: `V^{j,q}_t − W_t` is
  QuantumZipper's centered forward flow from the real point `x^{j,q}` on `[0, r]`, `r < T`, for every
  driver `U : ℝ → ℝ` that agrees with `W` before `T` (Specification (1.11)).
* `IsForcePath.exists_hit_of_tendsto`: **the real point swallowed at the threshold** (input to
  `Theorem14.GW1FirstThresholdStatement`, `planning/handoffs/PROVE-T14-IN.md` §5 (ii)): at a finite
  positive lifetime there is a real force point `x ≠ 0` that is alive on every `[0, r]`, `r < T`,
  and not on `[0, T]`, for every driver agreeing with `W` before `T`. This is the `hit` predicate of
  the frozen `ExplState.launch`, with `x > 0` a new right record or `x < 0` a new left record.
* `IsIntegratedSLEEvolution.ae_exists_hit`: the same, almost surely, at every finite positive
  lifetime (with Aux. lemma 3, `IsIntegratedSLEEvolution.ae_tendsto_threshold`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (IsForwardSol)

namespace InteractingSLE

namespace Sec2

namespace IsForcePath

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

section Helpers

theorem neBot_nhdsLT {T : ℝ≥0} (hT : 0 < T) : (𝓝[<] T).NeBot :=
  nhdsLT_neBot_of_exists_lt ⟨0, hT⟩

/-- The forward solution from a colliding force point does not extend to `[0, T]`: any solution on
`[0, T]` agrees with the gap before `T` (uniqueness), so by continuity it would vanish at `T`. -/
theorem not_exists_isForwardSol_of_tendsto {T : ℝ≥0} (hT : 0 < T) {U : ℝ → ℝ} {p : ℂ}
    {u : ℝ → ℂ} (hu : ∀ r : ℝ, r < T → IsForwardSol U p r u)
    (hlim : Tendsto u (𝓝[Ico (0 : ℝ) T] (T : ℝ)) (𝓝 0)) : ¬ ∃ v, IsForwardSol U p T v := by
  rintro ⟨v, hv⟩
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have heq : EqOn v u (Ico (0 : ℝ) T) := fun t ht =>
    QuantumZipper.ASep.isForwardSol_unique_any
      (QuantumZipper.isForwardSol_restrict hv ht.1 ht.2.le) (hu t ht.2) ⟨ht.1, le_rfl⟩
  have hcl : (T : ℝ) ∈ closure (Ico (0 : ℝ) T) := by
    rw [closure_Ico hT'.ne]; exact ⟨hT'.le, le_rfl⟩
  have : (𝓝[Ico (0 : ℝ) T] (T : ℝ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have hvT : Tendsto v (𝓝[Ico (0 : ℝ) T] (T : ℝ)) (𝓝 (v T)) :=
    (hv.1.continuousWithinAt ⟨hT'.le, le_rfl⟩).mono Ico_subset_Icc_self
  have hv0 : v T = 0 :=
    tendsto_nhds_unique hvT (hlim.congr' (eventually_nhdsWithin_of_forall fun t ht => (heq ht).symm))
  exact (hv.2 T ⟨hT'.le, le_rfl⟩).1 hv0

/-- Along `t ↑ T` in `ℝ` (from `[0, T)`), `t.toNNReal ↑ T`. -/
theorem tendsto_toNNReal_nhdsLT (T : ℝ≥0) :
    Tendsto Real.toNNReal (𝓝[Ico (0 : ℝ) T] (T : ℝ)) (𝓝[<] T) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun t ht => ?_⟩
  · have := (continuous_real_toNNReal.tendsto (T : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Ico (0 : ℝ) T))
    simpa using this
  · show t.toNNReal < T
    rw [Real.toNNReal_lt_iff_lt_coe ht.1]; exact ht.2

/-- The centered gap `s ↦ V^{j,R}_s − W_s`, read on `ℝ` and cast to `ℂ`. -/
def gapR (vR : Fin nR → ℝ≥0 → ℝ) (w : ℝ≥0 → ℝ) (j : Fin nR) (s : ℝ) : ℂ :=
  ((vR j s.toNNReal - w s.toNNReal : ℝ) : ℂ)

/-- The centered gap `s ↦ V^{j,L}_s − W_s`, read on `ℝ` and cast to `ℂ`. -/
def gapL (vL : Fin nL → ℝ≥0 → ℝ) (w : ℝ≥0 → ℝ) (j : Fin nL) (s : ℝ) : ℂ :=
  ((vL j s.toNNReal - w s.toNNReal : ℝ) : ℂ)

end Helpers

section Merge

variable (h : IsForcePath xL xR ρL ρR w vL vR ζ)
include h

/-- **Right spreads are nonincreasing**: for `i ≤ j` and `s ≤ t < ζ`,
`V^{j,R}_t − V^{i,R}_t ≤ V^{j,R}_s − V^{i,R}_s` (the integrand `2/(V^j − W) − 2/(V^i − W)` is
`≤ 0` off the null collision set of `i`). -/
theorem vR_sub_vR_le_of_le {s t : ℝ≥0} (hst : s ≤ t) (ht : (t : ℝ≥0∞) < ζ) {i j : Fin nR}
    (hij : i ≤ j) : vR j t - vR i t ≤ vR j s - vR i s := by
  have hsub : uIcc (s : ℝ) t ⊆ uIcc 0 t := by
    rw [uIcc_of_le (by exact_mod_cast hst), uIcc_of_le (NNReal.coe_nonneg t)]
    exact Icc_subset_Icc (NNReal.coe_nonneg s) le_rfl
  have hj := (h.intervalIntegrable_forceR ht j).mono_set hsub
  have hi := (h.intervalIntegrable_forceR ht i).mono_set hsub
  have key : (vR j t - vR i t) - (vR j s - vR i s) = ∫ r in (s : ℝ)..t,
      (2 / (vR j r.toNNReal - w r.toNNReal) - 2 / (vR i r.toNNReal - w r.toNNReal)) := by
    rw [intervalIntegral.integral_sub hj hi, ← h.vR_sub hst ht j, ← h.vR_sub hst ht i]
    ring
  have hae : (fun r : ℝ => 2 / (vR j r.toNNReal - w r.toNNReal) -
      2 / (vR i r.toNNReal - w r.toNNReal)) ≤ᵐ[volume.restrict (Icc (s : ℝ) t)] fun _ => 0 := by
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (h.volume_collisionR i)] with r hr hrI
    have hrI' : r ∈ Icc (0 : ℝ) t := ⟨(NNReal.coe_nonneg s).trans hrI.1, hrI.2⟩
    have hlt := toNNReal_lt_of_mem_Icc ht hrI'
    have hne : w r.toNNReal ≠ vR i r.toNNReal := fun he => hr ⟨hrI'.1, hlt, he⟩
    have hp : 0 < vR i r.toNNReal - w r.toNNReal :=
      sub_pos.2 (lt_of_le_of_ne (h.w_le_vR hlt i) hne)
    have hpq : vR i r.toNNReal - w r.toNNReal ≤ vR j r.toNNReal - w r.toNNReal :=
      sub_le_sub_right (h.monotone_vR hlt hij) _
    have h1 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hp hpq
    linarith
  have hle := intervalIntegral.integral_mono_ae_restrict (by exact_mod_cast hst) (hj.sub hi)
    intervalIntegrable_const hae
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_zero] at hle
  linarith

/-- **Merged right force points stay merged**: if `V^{i,R}_s = V^{j,R}_s` (`i ≤ j`), then
`V^{i,R}_t = V^{j,R}_t` for every `s ≤ t < ζ`. -/
theorem vR_eq_of_eq {s t : ℝ≥0} (hst : s ≤ t) (ht : (t : ℝ≥0∞) < ζ) {i j : Fin nR}
    (hij : i ≤ j) (heq : vR j s = vR i s) : vR j t = vR i t := by
  have h1 := h.vR_sub_vR_le_of_le hst ht hij
  have h2 := h.monotone_vR ht hij
  linarith

end Merge

section Collision

variable (h : IsForcePath xL xR ρL ρR w vL vR ζ)
include h

/-- **The last member of a colliding right group of weight `≤ −2`** is strictly to the right of the
driver before `T` and collides with it at `T`. -/
theorem exists_gapR_of_tendsto {T : ℝ≥0} (hT : 0 < T) (hζ : (T : ℝ≥0∞) = ζ) {w₀ : ℝ}
    {vL₀ : Fin nL → ℝ} {vR₀ : Fin nR → ℝ}
    (hlim : Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T)
      (𝓝 (w₀, vL₀, vR₀)))
    (hS : (∑ i ∈ Finset.univ.filter (fun i => vR₀ i = w₀), ρR i) ≤ -2) :
    ∃ k : Fin nR, (∀ t : ℝ≥0, t < T → w t < vR k t) ∧ vR₀ k = w₀ := by
  have := neBot_nhdsLT hT
  have hlt : ∀ t : ℝ≥0, t < T → (t : ℝ≥0∞) < ζ := fun t ht => hζ ▸ (by exact_mod_cast ht)
  have hw : Tendsto w (𝓝[<] T) (𝓝 w₀) := (continuous_fst.tendsto _).comp hlim
  have hv : ∀ j, Tendsto (vR j) (𝓝[<] T) (𝓝 (vR₀ j)) := fun j =>
    ((continuous_apply j).tendsto _).comp ((continuous_snd.comp continuous_snd).tendsto _ |>.comp
      hlim)
  have hev : ∀ᶠ t in 𝓝[<] T, t < T := self_mem_nhdsWithin
  have hle : ∀ j, w₀ ≤ vR₀ j := fun j =>
    le_of_tendsto_of_tendsto hw (hv j) (hev.mono fun t ht => h.w_le_vR (hlt t ht) j)
  have hmono : ∀ i j : Fin nR, i ≤ j → vR₀ i ≤ vR₀ j := fun i j hij =>
    le_of_tendsto_of_tendsto (hv i) (hv j) (hev.mono fun t ht => h.monotone_vR (hlt t ht) hij)
  set S := Finset.univ.filter (fun i => vR₀ i = w₀) with hSdef
  have hne : S.Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    rw [hcon, Finset.sum_empty] at hS
    linarith
  set k := S.max' hne with hkdef
  have hkS : k ∈ S := S.max'_mem hne
  have hk : vR₀ k = w₀ := (Finset.mem_filter.1 hkS).2
  have hdown : ∀ i, i ≤ k → i ∈ S := fun i hik =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, le_antisymm ((hmono i k hik).trans hk.le) (hle i)⟩
  refine ⟨k, fun t ht => ?_, hk⟩
  by_contra hcon
  have hwk : vR k t = w t := le_antisymm (not_lt.1 hcon) (h.w_le_vR (hlt t ht) k)
  have hgrp : ∀ i, i ≤ k → vR i t = w t := fun i hik =>
    le_antisymm ((h.monotone_vR (hlt t ht) hik).trans hwk.le) (h.w_le_vR (hlt t ht) i)
  set St := Finset.univ.filter (fun i => vR i t = w t) with hStdef
  have hSSt : S ⊆ St := fun i hi => Finset.mem_filter.2 ⟨Finset.mem_univ _,
    hgrp i (S.le_max' i hi)⟩
  have hnot := h.not_threshold (hlt t ht)
  have hR : ¬ (∑ i ∈ St, ρR i) ≤ -2 := fun h' => hnot (Or.inr h')
  have hex : ∃ j ∈ St, j ∉ S := by
    by_contra hcon'
    push Not at hcon'
    have : St = S := Finset.Subset.antisymm (fun j hj => hcon' j hj) hSSt
    exact hR (this ▸ hS)
  obtain ⟨j, hjSt, hjS⟩ := hex
  have hkj : k < j := by
    by_contra hkj
    exact hjS (hdown j (not_lt.1 hkj))
  have hjt : vR j t = vR k t := by rw [(Finset.mem_filter.1 hjSt).2, hwk]
  have hmerge : ∀ᶠ t' in 𝓝[<] T, vR j t' = vR k t' := by
    have hmem : Ioo t T ∈ 𝓝[<] T := Ioo_mem_nhdsLT ht
    filter_upwards [hmem] with t' ht'
    exact h.vR_eq_of_eq ht'.1.le (hlt t' ht'.2) hkj.le hjt
  have hj0 : vR₀ j = vR₀ k := tendsto_nhds_unique ((hv j).congr' hmerge) (hv k)
  exact hjS (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj0.trans hk⟩)

/-- **The colliding force point at a finite threshold**, either side: at a finite positive lifetime
at which the state converges to a threshold state, some right force point stays strictly right of
the driver before `T` and collides with it at `T`, or some left force point stays strictly left of
it and collides with it at `T`. -/
theorem exists_gap_of_tendsto {T : ℝ≥0} (hT : 0 < T) (hζ : (T : ℝ≥0∞) = ζ) {w₀ : ℝ}
    {vL₀ : Fin nL → ℝ} {vR₀ : Fin nR → ℝ}
    (hlim : Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T)
      (𝓝 (w₀, vL₀, vR₀)))
    (hthr : ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) :
    (∃ k : Fin nR, (∀ t : ℝ≥0, t < T → w t < vR k t) ∧ vR₀ k = w₀) ∨
      (∃ k : Fin nL, (∀ t : ℝ≥0, t < T → vL k t < w t) ∧ vL₀ k = w₀) := by
  rcases hthr with hL | hR
  · right
    have hlim' : Tendsto (fun t => ((-w) t, fun i => -vR i t, fun i => -vL i t)) (𝓝[<] T)
        (𝓝 (-w₀, fun i => -vR₀ i, fun i => -vL₀ i)) := by
      have hc : Continuous fun p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) =>
          (-p.1, fun i => -p.2.2 i, fun i => -p.2.1 i) := by fun_prop
      exact (hc.tendsto _).comp hlim
    have hS : (∑ i ∈ Finset.univ.filter (fun i => -vL₀ i = -w₀), ρL i) ≤ -2 := by
      simpa only [neg_inj] using hL
    obtain ⟨k, hk, hk0⟩ := h.reflect.exists_gapR_of_tendsto hT hζ hlim' hS
    exact ⟨k, fun t ht => by simpa using hk t ht, neg_inj.1 hk0⟩
  · exact Or.inl (h.exists_gapR_of_tendsto hT hζ hlim hR)

end Collision

section ForwardFlow

variable (h : IsForcePath xL xR ρL ρR w vL vR ζ)
include h

/-- **A separated right force point solves the centered forward flow** (Specification (1.11)): if
`W < V^{j,R}` before `T = ζ`, then `V^{j,R} − W` is QuantumZipper's centered forward solution from
the real point `x^{j,R}` on `[0, r]`, `r < T`, for every driver `U` that agrees with `W` before
`T`. -/
theorem isForwardSol_gapR {T : ℝ≥0} (hζ : (T : ℝ≥0∞) = ζ) {j : Fin nR}
    (hgap : ∀ t : ℝ≥0, t < T → w t < vR j t) {U : ℝ → ℝ}
    (hU : ∀ r : ℝ, 0 ≤ r → r < T → U r = w r.toNNReal) {r : ℝ} (hr : r < T) :
    IsForwardSol U (xR j : ℂ) r (gapR vR w j) := by
  have hlt : ∀ s ∈ Icc (0 : ℝ) r, (s.toNNReal : ℝ≥0∞) < ζ := fun s hs => by
    rw [← hζ, ENNReal.coe_lt_coe, Real.toNNReal_lt_iff_lt_coe hs.1]
    exact hs.2.trans_lt hr
  have hmaps : MapsTo Real.toNNReal (Icc (0 : ℝ) r) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} := fun s hs =>
    hlt s hs
  refine ⟨?_, fun s hs => ⟨?_, ?_⟩⟩
  · exact Complex.continuous_ofReal.comp_continuousOn
      (((h.continuousOn_vR j).comp continuous_real_toNNReal.continuousOn hmaps).sub
        (h.continuousOn_w.comp continuous_real_toNNReal.continuousOn hmaps))
  · have hsT : s.toNNReal < T := by
      rw [Real.toNNReal_lt_iff_lt_coe hs.1]; exact hs.2.trans_lt hr
    simp only [gapR, ne_eq, Complex.ofReal_eq_zero, sub_eq_zero]
    exact (hgap _ hsT).ne'
  · have hs0 : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal _ hs.1
    have hveq := h.vR_eq (hlt s hs) j
    rw [hs0] at hveq
    have hint : (∫ q in (0 : ℝ)..s, (2 : ℂ) / gapR vR w j q) =
        ((∫ q in (0 : ℝ)..s, 2 / (vR j q.toNNReal - w q.toNNReal) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun q _ => ?_
      simp only [gapR]
      push_cast
      rfl
    rw [hint, hU s hs.1 (hs.2.trans_lt hr)]
    simp only [gapR]
    rw [hveq]
    push_cast
    ring

/-- **A separated left force point solves the centered forward flow** (mirror of
`isForwardSol_gapR`). -/
theorem isForwardSol_gapL {T : ℝ≥0} (hζ : (T : ℝ≥0∞) = ζ) {j : Fin nL}
    (hgap : ∀ t : ℝ≥0, t < T → vL j t < w t) {U : ℝ → ℝ}
    (hU : ∀ r : ℝ, 0 ≤ r → r < T → U r = w r.toNNReal) {r : ℝ} (hr : r < T) :
    IsForwardSol U (xL j : ℂ) r (gapL vL w j) := by
  have hU' : ∀ r : ℝ, 0 ≤ r → r < T → (fun s => -U s) r = (-w) r.toNNReal := fun r hr0 hrT => by
    simp [hU r hr0 hrT]
  have hsol := h.reflect.isForwardSol_gapR hζ (j := j) (fun t ht => by simpa using hgap t ht) hU' hr
  have hsol' := QuantumZipper.RS.isForwardSol_neg hsol
  simp only [neg_neg, Pi.neg_apply, Complex.ofReal_neg] at hsol'
  convert hsol' using 1
  funext t
  simp only [gapR, gapL, Pi.neg_apply]
  push_cast
  ring

/-- **The real point swallowed at a finite threshold** (input to
`Theorem14.GW1FirstThresholdStatement`): at a finite positive lifetime `T = ζ` at which the state
converges to a threshold state, there is a real force point `x ≠ 0` (a right one, `x > 0`, or a left
one, `x < 0`) that is alive on every `[0, r]`, `r < T`, and not alive on `[0, T]`, for every driver
`U` agreeing with `W` before `T`. -/
theorem exists_hit_of_tendsto {T : ℝ≥0} (hT : 0 < T) (hζ : (T : ℝ≥0∞) = ζ) {w₀ : ℝ}
    {vL₀ : Fin nL → ℝ} {vR₀ : Fin nR → ℝ}
    (hlim : Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T)
      (𝓝 (w₀, vL₀, vR₀)))
    (hthr : ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) {U : ℝ → ℝ}
    (hU : ∀ r : ℝ, 0 ≤ r → r < T → U r = w r.toNNReal) :
    ∃ x : ℝ, (0 < x ∨ x < 0) ∧ (∀ r : ℝ, r < T → ∃ u, IsForwardSol U (x : ℂ) r u) ∧
      ¬ ∃ u, IsForwardSol U (x : ℂ) T u := by
  have hw : Tendsto w (𝓝[<] T) (𝓝 w₀) := (continuous_fst.tendsto _).comp hlim
  have hm := tendsto_toNNReal_nhdsLT T
  rcases h.exists_gap_of_tendsto hT hζ hlim hthr with ⟨k, hk, hk0⟩ | ⟨k, hk, hk0⟩
  · have hv : Tendsto (vR k) (𝓝[<] T) (𝓝 (vR₀ k)) :=
      ((continuous_apply k).tendsto _).comp ((continuous_snd.comp continuous_snd).tendsto _ |>.comp
        hlim)
    refine ⟨xR k, Or.inl ?_, fun r hr => ⟨_, h.isForwardSol_gapR hζ hk hU hr⟩,
      not_exists_isForwardSol_of_tendsto hT (fun r hr => h.isForwardSol_gapR hζ hk hU hr) ?_⟩
    · have := hk 0 hT
      rwa [h.w_zero, h.vR_zero] at this
    · have hg : Tendsto (fun t => vR k t - w t) (𝓝[<] T) (𝓝 0) := by
        simpa [hk0] using hv.sub hw
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp (hg.comp hm)
      rw [Complex.ofReal_zero] at h2
      exact h2
  · have hv : Tendsto (vL k) (𝓝[<] T) (𝓝 (vL₀ k)) :=
      ((continuous_apply k).tendsto _).comp ((continuous_fst.comp continuous_snd).tendsto _ |>.comp
        hlim)
    refine ⟨xL k, Or.inr ?_, fun r hr => ⟨_, h.isForwardSol_gapL hζ hk hU hr⟩,
      not_exists_isForwardSol_of_tendsto hT (fun r hr => h.isForwardSol_gapL hζ hk hU hr) ?_⟩
    · have := hk 0 hT
      rwa [h.w_zero, h.vL_zero] at this
    · have hg : Tendsto (fun t => vL k t - w t) (𝓝[<] T) (𝓝 0) := by
        simpa [hk0] using hv.sub hw
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp (hg.comp hm)
      rw [Complex.ofReal_zero] at h2
      exact h2

end ForwardFlow

end IsForcePath

end Sec2

namespace IsIntegratedSLEEvolution

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The real point swallowed at a finite lifetime** (almost surely; the `hit` predicate of the
frozen `ExplState.launch`, input to `Theorem14.GW1FirstThresholdStatement`): for `a > 0`, almost
surely, at every finite positive lifetime `T = ζ` some real force point `x ≠ 0` is alive on every
`[0, r]`, `r < T`, and not on `[0, T]`, for every driver `U` that agrees with `W` before `T`. -/
theorem ae_exists_hit (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (ha : 0 < a) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω → ∀ U : ℝ → ℝ,
      (∀ r : ℝ, 0 ≤ r → r < T → U r = W r.toNNReal ω) →
      ∃ x : ℝ, (0 < x ∨ x < 0) ∧ (∀ r : ℝ, r < T → ∃ u, IsForwardSol U (x : ℂ) r u) ∧
        ¬ ∃ u, IsForwardSol U (x : ℂ) T u := by
  filter_upwards [h.ae_isIntegratedSLEPath, h.ae_tendsto_threshold ha] with ω hp hth T hT hζ U hU
  obtain ⟨w₀, vL₀, vR₀, hlim, hthr⟩ := hth T hT hζ
  exact hp.isForcePath.exists_hit_of_tendsto hT hζ hlim hthr hU

end IsIntegratedSLEEvolution

end InteractingSLE
