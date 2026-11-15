/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1Connector

/-!
# Induction over the flow stages of the walk program

Packet PROVE-SB2-CANON, round 8 (D80: the final (P1) assembly). The walk program `boundaryWalkSpec b jumps θ right` has
its flow instructions `(θ, ⊤)` exactly at the even indices below its length (`GW1Conn.getElem?_boundaryWalkSpec`).
**`flow_iff`** records this; **`flow_of_flow_add_two`** steps down; **`flow_induction`**: a property of stages that
holds at `0` and passes from a flow stage `ℓ` to the flow stage `ℓ + 2` holds at every flow stage — the shape of
SB2(2)'s retained-law induction `ℓ → ℓ + 2`.

R48: no source theorem is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace InteractingSLE.Theorem14.SB.Cz

/-- **The flow stages of a walk program** are the even indices below its length. -/
theorem flow_iff (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool) (ℓ : ℕ) :
    (boundaryWalkSpec b jumps θ right).2.2[ℓ]? = some (Sum.inl (θ, ⊤)) ↔
      ℓ % 2 = 0 ∧ ℓ < (boundaryWalkSpec b jumps θ right).2.2.length := by
  rw [GW1Conn.getElem?_boundaryWalkSpec]
  by_cases hlt : ℓ < (boundaryWalkSpec b jumps θ right).2.2.length
  · by_cases hev : ℓ % 2 = 0
    · simp [hlt, hev]
    · simp [hlt, hev]
  · simp [hlt]

/-- **A flow stage two steps on has a flow stage before it.** -/
theorem flow_of_flow_add_two {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ} {right : Bool} {ℓ : ℕ}
    (h : (boundaryWalkSpec b jumps θ right).2.2[ℓ + 2]? = some (Sum.inl (θ, ⊤))) :
    (boundaryWalkSpec b jumps θ right).2.2[ℓ]? = some (Sum.inl (θ, ⊤)) := by
  rw [flow_iff] at h ⊢
  exact ⟨by omega, by omega⟩

/-- **Induction over the flow stages**: from stage `0` and the step `ℓ → ℓ + 2` between flow stages. -/
theorem flow_induction (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool) {Q : ℕ → Prop} (h0 : Q 0)
    (hstep : ∀ ℓ, (boundaryWalkSpec b jumps θ right).2.2[ℓ]? = some (Sum.inl (θ, ⊤)) →
      (boundaryWalkSpec b jumps θ right).2.2[ℓ + 2]? = some (Sum.inl (θ, ⊤)) → Q ℓ → Q (ℓ + 2)) :
    ∀ ℓ, (boundaryWalkSpec b jumps θ right).2.2[ℓ]? = some (Sum.inl (θ, ⊤)) → Q ℓ := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases n with _ | _ | m
    · exact h0
    · exact absurd ((flow_iff b jumps θ right 1).1 hn).1 (by norm_num)
    · have hm := flow_of_flow_add_two hn
      exact hstep m hm hn (ih m (by omega) hm)

end InteractingSLE.Theorem14.SB.Cz
