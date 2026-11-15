/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.TwoTime2Flow
import InteractingSLE.Spec.ZhanGT4.TwoTime

/-!
# The other-time identities of (D3) and the Schwarzian identity (D5)

Packet PROVE-ZHAN-GT4-A4. Source: Astra, *Follow-up proofs and dependency audit*, Part A.1.1, (D3) right column and
rows 3–4, and (D5) (`source/external/AstraIG1/ig1_followup_proofs.txt` L245–L275, ruling R38); the additional note
§2.1 (`ig1_additional_proofs.txt` L725–L742, R39):

  `d_j A_{k,0} = 2A²_{j,1}/(A_{k,0} − A_{j,0}) dt_j`,  `d_j A_{k,1}/A_{k,1} = −2A²_{j,1}/E²_{j,0} dt_j`,
  `d_j B_{m,0} = 2A²_{j,1}/(B_{m,0} − A_{j,0}) dt_j`,  `d_j B_{m,1}/B_{m,1} = −2A²_{j,1}/E²_{j,m} dt_j`,
  `∂_{t_j} 𝒮h_k(W_k) = −12 A²_{1,1}A²_{2,1}/E⁴`.

When curve `j` grows and the hull `A = K_k` of curve `k` is frozen, the map `h_k = G ∘ g_k⁻¹` removing `g_k(K_j)` is the
Loewner map `g̃_{a(t)}` of the **image chain** (Specification Aux. lemma 8, landed as
`ConformalImageFull.exists_loewner_image_rate_of_pos`), run at the capacity clock `a` with `ȧ = A²_{j,1}` and driver
`W̃(a(t)) = A_{j,0}`. The quantities `A_{k,r}` (and `B_{m,r}`, up to the constant factor `φ'(p_m)`) are the derivatives
of that Loewner map at a point `ζ` alive for the image chain (`ζ = W_k`, resp. `ζ = φ(p_m)`). So these identities are
the one-chain calculus of `TwoTime2Flow.lean` composed with the clock:

* `hasDerivWithinAt_gmap_clock`, `hasDerivWithinAt_logDerivFwd_clock`, `hasDerivWithinAt_deriv_fwdMap_clock`,
  `hasDerivWithinAt_schwarzFwd_clock`: the clocked one-chain derivatives for any differentiable clock;
* `exists_otherTime_identities`: the identities above in the two-hull setting, for every point alive for the image
  chain.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull logDerivFwd)

/-- The alive disc of a solution on `[0, S]`. -/
theorem exists_aliveDisc_self {W : ℝ → ℝ} {x : ℂ} {S : ℝ} {v : ℝ → ℂ} (hv : IsForwardSol W x S v)
    (hS : 0 ≤ S) : ∃ δ > 0, (∀ r ∈ Icc (0 : ℝ) S, 2 * δ ≤ ‖v r‖) ∧ x ∈ ball x (aliveRad S δ) := by
  obtain ⟨δ, hδ, hlow⟩ := InteractingSLE.exists_two_mul_le_norm_of_isForwardSol hS hv
  exact ⟨δ, hδ, hlow, mem_ball_self (aliveRad_pos hδ)⟩

section Clocked

variable {W : ℝ → ℝ} (hW : Continuous W) {x : ℂ} {S : ℝ} {v : ℝ → ℂ} (hv : IsForwardSol W x S v)
  {T : ℝ} {a : ℝ → ℝ} (ha : MapsTo a (Icc 0 T) (Icc 0 S)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {c : ℝ}
  (hat : HasDerivWithinAt a c (Icc 0 T) t)
include hW hv ha ht hat

/-- **The clocked Loewner equation**: `d/dt g̃_{a(t)}(x) = ȧ(t) · 2/(g̃_{a(t)}(x) − W̃(a(t)))`. -/
theorem hasDerivWithinAt_gmap_clock :
    HasDerivWithinAt (fun s => fwdMap W (a s) x + W (a s)) (c * (2 / fwdMap W (a t) x)) (Icc 0 T) t := by
  have h := (hasDerivWithinAt_gmap hW hv (ha ht)).scomp t hat ha
  rw [real_smul] at h
  exact h

/-- **The clocked variational equation**: `d/dt log g̃'_{a(t)}(x) = ȧ(t) · (−2/(g̃_{a(t)}(x) − W̃(a(t)))²)`. -/
theorem hasDerivWithinAt_logDerivFwd_clock :
    HasDerivWithinAt (fun s => logDerivFwd W (a s) x) (c * -(2 / fwdMap W (a t) x ^ 2)) (Icc 0 T) t := by
  have hS : 0 ≤ S := (ha ht).1.trans (ha ht).2
  obtain ⟨δ, hδ, hlow, hx⟩ := exists_aliveDisc_self hv hS
  have h := (hasDerivWithinAt_logDerivFwd_time hW hv hδ hlow hx (ha ht)).scomp t hat ha
  rw [real_smul] at h
  exact h

/-- **The clocked derivative**: `d/dt g̃'_{a(t)}(x) = ȧ(t) · (−2 g̃'_{a(t)}(x)/(g̃_{a(t)}(x) − W̃(a(t)))²)`. -/
theorem hasDerivWithinAt_deriv_fwdMap_clock :
    HasDerivWithinAt (fun s => deriv (fwdMap W (a s)) x)
      (c * -(2 * Complex.exp (logDerivFwd W (a t) x) / fwdMap W (a t) x ^ 2)) (Icc 0 T) t := by
  have hS : 0 ≤ S := (ha ht).1.trans (ha ht).2
  obtain ⟨δ, hδ, hlow, hx⟩ := exists_aliveDisc_self hv hS
  have h := (hasDerivWithinAt_logDerivFwd_clock hW hv ha ht hat).cexp
  refine (h.congr (fun s hs => deriv_fwdMap_aliveDisc hW hv hδ hlow hx (ha hs))
    (deriv_fwdMap_aliveDisc hW hv hδ hlow hx (ha ht))).congr_deriv ?_
  ring

/-- **The clocked Schwarzian identity**: `d/dt 𝒮g̃_{a(t)}(x) = ȧ(t) · (−12 g̃'_{a(t)}(x)²/(g̃_{a(t)}(x) − W̃(a(t)))⁴)`. -/
theorem hasDerivWithinAt_schwarzFwd_clock :
    HasDerivWithinAt (fun s => schwarzFwd W (a s) x)
      (c * -(12 * Complex.exp (logDerivFwd W (a t) x) ^ 2 / fwdMap W (a t) x ^ 4)) (Icc 0 T) t := by
  have hS : 0 ≤ S := (ha ht).1.trans (ha ht).2
  obtain ⟨δ, hδ, hlow, hx⟩ := exists_aliveDisc_self hv hS
  have h := (hasDerivWithinAt_schwarzFwd_time hW hv hδ hlow hx (ha ht)).scomp t hat ha
  rw [real_smul] at h
  exact h

end Clocked

/-! ### The two-hull setting -/

/-- **The other-time identities (D3) and the Schwarzian identity (D5).** Let curve `j` have continuous driver `W` on
`[0, T]` (`T > 0`), and freeze the hull `A = K_k` of curve `k` (a compact `ℍ`-hull with mapping-out function `φ = g_k`,
`closure A ∩ closure K_T = ∅`). There are a capacity clock `a` and an image driver `W̃` (Aux. lemma 8) with
`K̃_{a(t)} = φ(K_t)` such that, for every `t ∈ [0, T]`, every mapping-out function `R = h_j` of `g_t(A)` (boundary value
`A_{j,0} = W̃(a(t))` at `W_t`) and every holomorphic extension `R̂` of `R` across the real line near `W_t`
(`A_{j,1} = R̂'(W_t)`), and every point `ζ` alive for the image chain on `[0, a(T)]` (e.g. `ζ = W_k`, or `ζ = φ(p_m)`):
with `h_k = g̃_{a(t)}`, `A_{k,0} − A_{j,0} = g̃_{a(t)}(ζ) − W̃(a(t))` and `A_{k,1} = g̃'_{a(t)}(ζ)`,

* `d/dt A_{k,0} = 2A²_{j,1}/(A_{k,0} − A_{j,0})`;
* `d/dt A_{k,1} = −2A²_{j,1} A_{k,1}/(A_{k,0} − A_{j,0})²`;
* `d/dt 𝒮h_k(ζ) = −12 A²_{j,1} A²_{k,1}/(A_{k,0} − A_{j,0})⁴`.

All derivatives are within `[0, T]`. -/
theorem exists_otherTime_identities {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 < T)
    {A : Set ℂ} (hA : IsHPHull A) {φ : ℂ → ℂ} (hφ : IsMapOut A φ)
    (hd : Disjoint (closure A) (closure (fwdHull W T))) :
    ∃ (a : ℝ → ℝ) (W' : ℝ → ℝ), Continuous W' ∧ a 0 = 0 ∧ StrictMonoOn a (Icc 0 T) ∧
      (∀ t ∈ Icc (0 : ℝ) T, fwdHull W' (a t) = φ '' fwdHull W t) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ R : ℂ → ℂ, IsMapOut ((fun z => fwdMap W t z + W t) '' A) R →
        Tendsto R (𝓝[H] (W t : ℂ)) (𝓝 (W' (a t) : ℂ)) ∧
        ∀ δ > (0 : ℝ), ∀ Rext : ℂ → ℂ, DifferentiableOn ℂ Rext (ball (W t : ℂ) δ) →
          EqOn Rext R (ball (W t : ℂ) δ ∩ H) → ∀ (ζ : ℂ) (v : ℝ → ℂ), IsForwardSol W' ζ (a T) v →
            HasDerivWithinAt (fun s => fwdMap W' (a s) ζ + W' (a s))
              (2 * ((deriv Rext (W t)).re : ℂ) ^ 2 / fwdMap W' (a t) ζ) (Icc 0 T) t ∧
            HasDerivWithinAt (fun s => deriv (fwdMap W' (a s)) ζ)
              (-(2 * ((deriv Rext (W t)).re : ℂ) ^ 2 * deriv (fwdMap W' (a t)) ζ / fwdMap W' (a t) ζ ^ 2))
              (Icc 0 T) t ∧
            HasDerivWithinAt (fun s => schwarzFwd W' (a s) ζ)
              (-(12 * ((deriv Rext (W t)).re : ℂ) ^ 2 * deriv (fwdMap W' (a t)) ζ ^ 2 / fwdMap W' (a t) ζ ^ 4))
              (Icc 0 T) t := by
  obtain ⟨a, W', hW'c, ha0, hamono, -, hmain⟩ := ConformalImageFull.exists_loewner_image_rate_of_pos hW hT hA hφ hd
  have hTmem : T ∈ Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  have hmaps : MapsTo a (Icc 0 T) (Icc 0 (a T)) := fun s hs => by
    refine ⟨?_, hamono.monotoneOn hs hTmem hs.2⟩
    rw [← ha0]; exact hamono.monotoneOn ⟨le_rfl, hT.le⟩ hs hs.1
  refine ⟨a, W', hW'c, ha0, hamono, fun t ht => (hmain t ht).2.1, fun t ht R hRm => ?_⟩
  obtain ⟨-, -, hR⟩ := hmain t ht
  obtain ⟨-, h2, -, hrate⟩ := hR R hRm
  refine ⟨h2, fun δ hδ Rext hRd hRe ζ v hv => ?_⟩
  obtain ⟨-, -, hder⟩ := hrate δ hδ Rext hRd hRe
  have haT : 0 ≤ a T := (hmaps hTmem).1
  obtain ⟨ε, hε, hlow, hζ⟩ := exists_aliveDisc_self hv haT
  have hdf : deriv (fwdMap W' (a t)) ζ = Complex.exp (logDerivFwd W' (a t) ζ) :=
    deriv_fwdMap_aliveDisc hW'c hv hε hlow hζ (hmaps ht)
  refine ⟨?_, ?_, ?_⟩
  · refine (hasDerivWithinAt_gmap_clock hW'c hv hmaps ht hder).congr_deriv ?_
    push_cast; ring
  · refine (hasDerivWithinAt_deriv_fwdMap_clock hW'c hv hmaps ht hder).congr_deriv ?_
    rw [hdf]; push_cast; ring
  · refine (hasDerivWithinAt_schwarzFwd_clock hW'c hv hmaps ht hder).congr_deriv ?_
    rw [hdf]; push_cast; ring

end InteractingSLE.ZhanGT4
