import HigherDimLQGMetric.Shell.EpsilonChain

/-!
# Uniform finite chains in a compact connected set

The chain relation from W0 is converted into a bound on any directed triangle cost.
This is the deterministic counting input for the shell-diameter tightness proof.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace HigherDimLQGMetric

open Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

def sharpShortStep (K : Set (Rd d)) (b : ℝ) (u v : Rd d) : Prop :=
  u ∈ K ∧ v ∈ K ∧ dist u v < b

/-- A finite short-step chain has a uniform step count for every directed triangle cost. -/
theorem cost_of_shortChain {K : Set (Rd d)} {b : ℝ} {u v : Rd d}
    (hu : u ∈ K) (hc : Relation.ReflTransGen (sharpShortStep K b) u v) :
    ∃ N : ℕ, ∀ (δ : Rd d → Rd d → ℝ≥0∞),
      (∀ x ∈ K, δ x x = 0) → (∀ x y z, δ x z ≤ δ x y + δ y z) →
      ∀ M : ℝ≥0∞, (∀ x y, sharpShortStep K b x y → δ x y ≤ M) →
      δ u v ≤ (N : ℝ≥0∞) * M := by
  induction hc with
  | refl =>
      refine ⟨0, fun δ h0 _ M _ => ?_⟩
      simp only [h0 _ hu, Nat.cast_zero, zero_mul, le_refl]
  | @tail w z _ hw ih =>
      obtain ⟨N, hN⟩ := ih
      refine ⟨N + 1, fun δ h0 ht M hs => ?_⟩
      calc
        δ u z ≤ δ u w + δ w z := ht u w z
        _ ≤ (N : ℝ≥0∞) * M + M := add_le_add (hN δ h0 ht M hs) (hs w z hw)
        _ = ((N + 1 : ℕ) : ℝ≥0∞) * M := by
          push_cast
          ring

/-- Compact connected sets admit one step count which works for every directed triangle cost
whose short steps are bounded. -/
theorem compact_connected_chain_bound {K : Set (Rd d)} (hK : IsCompact K)
    (hKc : IsConnected K) {b : ℝ} (hb : 0 < b) :
    ∃ N : ℕ, ∀ u ∈ K, ∀ v ∈ K, ∀ (δ : Rd d → Rd d → ℝ≥0∞),
      (∀ x ∈ K, δ x x = 0) → (∀ x y z, δ x z ≤ δ x y + δ y z) →
      ∀ M : ℝ≥0∞, (∀ x y, sharpShortStep K b x y → δ x y ≤ M) →
      δ u v ≤ (N : ℝ≥0∞) * M := by
  classical
  obtain ⟨T, hTK, hTf, hcover⟩ := finite_cover_balls_of_compact hK (by positivity : 0 < b / 3)
  haveI : Fintype T := hTf.fintype
  let f : T × T → ℕ := fun p => Classical.choose
    (cost_of_shortChain (hTK p.1.2) (connected_epsilon_chain hKc (by positivity : 0 < b / 3)
      (hTK p.1.2) (hTK p.2.2)))
  have hf : ∀ p : T × T, ∀ (δ : Rd d → Rd d → ℝ≥0∞),
      (∀ x ∈ K, δ x x = 0) → (∀ x y z, δ x z ≤ δ x y + δ y z) →
      ∀ M : ℝ≥0∞, (∀ x y, sharpShortStep K b x y → δ x y ≤ M) →
      δ p.1 p.2 ≤ (f p : ℝ≥0∞) * M := by
    intro p δ h0 ht M hs
    have hshort : ∀ x y, sharpShortStep K (b / 3) x y → δ x y ≤ M := by
      intro x y hxy
      exact hs x y ⟨hxy.1, hxy.2.1, by linarith [hxy.2.2]⟩
    exact Classical.choose_spec (cost_of_shortChain (hTK p.1.2)
      (connected_epsilon_chain hKc (by positivity : 0 < b / 3)
        (hTK p.1.2) (hTK p.2.2))) δ h0 ht M hshort
  let N : ℕ := 2 + ∑ p : T × T, f p
  refine ⟨N, ?_⟩
  intro u hu v hv δ h0 ht M hs
  obtain ⟨x, hxT, hux⟩ := mem_iUnion₂.1 (hcover hu)
  obtain ⟨y, hyT, hvy⟩ := mem_iUnion₂.1 (hcover hv)
  let p : T × T := (⟨x, hxT⟩, ⟨y, hyT⟩)
  have hfx : f p ≤ ∑ q : T × T, f q :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)
  have hux' : δ u x ≤ M := hs u x ⟨hu, hTK hxT, by linarith [Metric.mem_ball.mp hux]⟩
  have hyv' : δ y v ≤ M := hs y v ⟨hTK hyT, hv, by
    rw [dist_comm]
    linarith [Metric.mem_ball.mp hvy]⟩
  have hxy : δ x y ≤ (f p : ℝ≥0∞) * M := hf p δ h0 ht M hs
  have hNM : ((f p + 2 : ℕ) : ℝ≥0∞) * M ≤ (N : ℝ≥0∞) * M := by
    gcongr
    dsimp [N]
    omega
  calc
    δ u v ≤ δ u x + δ x v := ht u x v
    _ ≤ δ u x + (δ x y + δ y v) := add_le_add le_rfl (ht x y v)
    _ ≤ M + ((f p : ℝ≥0∞) * M + M) := add_le_add hux' (add_le_add hxy hyv')
    _ = ((f p + 2 : ℕ) : ℝ≥0∞) * M := by push_cast; ring
    _ ≤ (N : ℝ≥0∞) * M := hNM

end HigherDimLQGMetric
