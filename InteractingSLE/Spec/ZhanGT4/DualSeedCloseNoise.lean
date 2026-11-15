/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedCloseD10
import InteractingSLE.Spec.ZhanGT4.DualSeedFinalCapacity

/-!
# Identifying the compensated capacity driver

Packet PROVE-ZHAN-GT4-A22. Partition the full image force word into its
left and right marks without assuming that seeds are initially distinct.
The capacity-noise identity follows from the actual D10 integral, rather
than from a hypothesis identifying two compensated stochastic processes.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

/-- A partition of the image forces gives exactly the compensated
capacity driver. The driver is centered at its own initial image. -/
theorem SeedData.capacity_noise_eq_d10 {n nL nR : ℕ} (s : SeedData n)
    {A : Set ℂ} {T t : ℝ} (h : OwnData s.W A s.φ T s.a s.W')
    (ht : t ∈ Icc (0 : ℝ) T) (e : Fin nL ⊕ Fin nR ≃ Fin (n + 1))
    {w : ℝ≥0 → ℝ} {v : Fin (n + 1) → ℝ≥0 → ℝ}
    (hw : ∀ u ∈ Icc (0 : ℝ) T, w (s.a u).toNNReal = s.A 0 u - s.A 0 0)
    (hv : ∀ i u, u ∈ Icc (0 : ℝ) T →
      v i (s.a u).toNNReal = s.imageForce u i - s.A 0 0)
    (hi : ∀ i, IntervalIntegrable
      (fun u => s.A 1 u ^ 2 / (s.A 0 u - s.imageForce u i)) volume 0 t) :
    seedCapacityNoise s.κ (fun i => s.imageCharge (e (.inl i)))
      (fun j => s.imageCharge (e (.inr j))) w
      (fun i => v (e (.inl i))) (fun j => v (e (.inr j))) (s.a t).toNNReal =
      (s.A 0 t - s.A 0 0 - (∫ u in (0 : ℝ)..t, s.d10Rate u)) / Real.sqrt s.κ := by
  have ha : 0 ≤ s.a t := by
    rw [← h.a0]
    exact h.mono.monotoneOn ⟨le_rfl, h.pos.le⟩ ht ht.1
  have hd := (s.integral_d10_capacity h ht (w := fun u => w u.toNNReal)
    (v := fun i u => v i u.toNNReal) hw hv hi).2
  have hsplit :
      (∑ i, ∫ u in (0 : ℝ)..s.a t,
        s.imageCharge (e (.inl i)) / (w u.toNNReal - v (e (.inl i)) u.toNNReal)) +
      (∑ j, ∫ u in (0 : ℝ)..s.a t,
        s.imageCharge (e (.inr j)) / (w u.toNNReal - v (e (.inr j)) u.toNNReal)) =
      ∑ i, ∫ u in (0 : ℝ)..s.a t, s.imageCharge i / (w u.toNNReal - v i u.toNNReal) := by
    simpa only [Fintype.sum_sum_type] using
      (e.sum_comp (fun i => ∫ u in (0 : ℝ)..s.a t,
        s.imageCharge i / (w u.toNNReal - v i u.toNNReal)))
  unfold seedCapacityNoise
  rw [Real.coe_toNNReal _ ha, hw t ht, sub_sub, hsplit, ← hd]

/-- The same calculation identifies the stopped, spliced own-time noise
used in the Brownian time-change theorem. -/
theorem seed_capacityNoise_eq_ownMappedNoise {Ω : Type*} {n nL nR : ℕ}
    {d : Ω → SeedData n} {S : Ω → ℝ≥0} {A : Ω → Set ℂ} {κ : ℝ}
    {B W : ℝ≥0 → Ω → ℝ} {V : Fin (n + 1) → ℝ≥0 → Ω → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (e : Fin nL ⊕ Fin nR ≃ Fin (n + 1))
    (hown : ∀ ω, OwnData (d ω).W (A ω) (d ω).φ (S ω) (d ω).a (d ω).W')
    (hκ : ∀ ω, (d ω).κ = κ)
    (hρL : ∀ ω i, (d ω).imageCharge (e (.inl i)) = ρL i)
    (hρR : ∀ ω j, (d ω).imageCharge (e (.inr j)) = ρR j)
    (hW : ∀ ω u, u ∈ Icc (0 : ℝ) (S ω) →
      W ((d ω).a u).toNNReal ω = (d ω).A 0 u - (d ω).A 0 0)
    (hV : ∀ ω i u, u ∈ Icc (0 : ℝ) (S ω) →
      V i ((d ω).a u).toNNReal ω = (d ω).imageForce u i - (d ω).A 0 0)
    (hi : ∀ ω i t, t ∈ Icc (0 : ℝ) (S ω) → IntervalIntegrable
      (fun u => (d ω).A 1 u ^ 2 / ((d ω).A 0 u - (d ω).imageForce u i)) volume 0 t)
    (ω : Ω) (r : ℝ≥0) (hr : r ≤ S ω) :
    seedCapacityNoise κ ρL ρR (W · ω) (fun i u => V (e (.inl i)) u ω)
      (fun j u => V (e (.inr j)) u ω) ((d ω).a r).toNNReal =
        seedOwnMappedNoise κ d S B r ω := by
  have ht : (r : ℝ) ∈ Icc (0 : ℝ) (S ω) := ⟨r.coe_nonneg, hr⟩
  have hh := (d ω).capacity_noise_eq_d10 (hown ω) ht e (w := (W · ω))
    (v := fun i u => V i u ω) (hW ω) (hV ω) (fun i => hi ω i r ht)
  simp_rw [hκ ω, hρL ω, hρR ω] at hh
  rw [hh]
  simp only [seedOwnMappedNoise, min_eq_left hr, min_eq_left (show (r : ℝ) ≤ S ω from hr), sub_self, add_zero]

end InteractingSLE.ZhanGT4
