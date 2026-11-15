/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.R1RefFreshTip
import InteractingSLE.Spec.Supplement.R4Gaps

/-!
# A fresh boundary visit is a current attachment (Lemma 1.4 of the elimination note)

Packet PROVE-R16. Ruling R41 (`source/external/AstraIG1/ig1_ztip_elimination.txt` §1.2, L211–L231):
Corollary R.2 (supplement p. 472, `source/spec/p433-480.md` L945–L948: "If the current interior tip
belongs to `α`, then it is `α(u_s)` and `q_s = W_s`") is replaced by its fresh-contact form

> **Lemma 1.4.** In a contained, mixed or outer pocket, suppose `τ ≤ a < σ`, `p = η(a) ∈ ∂C` is an
> interior physical point, and `p` has not been visited before `a`. Then `p` is a current first-visit
> attachment on each selected arm containing it. Its lifted incoming endpoint equals `W_a`.
>
> *Proof.* For a contained arm `α`, write `p = α(v)` and let `u = u(a)`. One has `u ≤ v` because
> `p ∈ R_a`. If `u < v`, the distinct point `α(u)` was visited strictly before `a`, and reverse
> first-visit order gives `T(p) ≤ T(α(u)) < a`, a contradiction. Thus `u = v`. Its incoming endpoint
> maps to the fresh interior tip, so the deterministic fresh-tip lemma makes it `W_a`.

This file proves the contained-arm case, for a continuous Loewner trace `η` (`R_t = η([0, t])`) and an
injective incoming arc `α : [0, 1] → ℂ` in **reverse first-visit order** (§5.1's "reverse first-visit
containment of every strict-angle incoming flow line": when a point of `α` has been visited, so has
every later point of `α`; `IsReverseVisitOrder`). The lifted incoming endpoint is any real `q` (centred
coordinate of the `g_a` chart) with `F̄_a(q) = α(u(a))`; Lemma 1.1 (`R1RefFreshTip.lean`) makes it
`0 = W_a − W_a`.

The outer-arm case uses the exterior Jordan embedding of Aux. 31, which has no Lean statement yet
(see the handoff).

## Main results

* `IsReverseVisitOrder`: reverse first-visit order of an incoming arc;
* `firstVisitParam_eq_of_fresh`: `u(a) = v` (the first part of Lemma 1.4);
* `lemma14_contained`: **Lemma 1.4, contained arm**: `u(a) = v` and every lifted incoming endpoint is
  the driver.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H Hbar fwdHull fwdMapInv)

namespace InteractingSLE

namespace R16

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {α : ℝ → ℂ}

/-- **Reverse first-visit order** of an incoming arc `α : [0, 1] → ℂ` along the range process `R`:
whenever `α(v₁)` has been visited by time `t` and `v₁ ≤ v₂`, so has `α(v₂)`. Equivalently the visited
parameters at each time form a final segment of `[0, 1]`, and `T(α(v₂)) ≤ T(α(v₁))` for `v₁ ≤ v₂`
(specification §6.2, Aux. 37, first paragraph; supplement §5.1: "reverse first-visit containment of
every strict-angle incoming flow line and of both extremal lines"). -/
def IsReverseVisitOrder (α : ℝ → ℂ) (R : ℝ → Set ℂ) : Prop :=
  ∀ t : ℝ, ∀ v₁ ∈ Icc (0 : ℝ) 1, ∀ v₂ ∈ Icc (0 : ℝ) 1, v₁ ≤ v₂ → α v₁ ∈ R t → α v₂ ∈ R t

/-- **Lemma 1.4, first part.** If the point `p = η(a) = α(v)` of an injective incoming arc in reverse
first-visit order is visited for the first time at `a`, then it is the current first attachment:
`u(a) = min {w : α(w) ∈ η([0, a])} = v`. -/
theorem firstVisitParam_eq_of_fresh (hαi : InjOn α (Icc 0 1))
    (hrev : IsReverseVisitOrder α fun t => η '' Icc 0 t) {a v : ℝ} (ha : 0 ≤ a)
    (hv : v ∈ Icc (0 : ℝ) 1) (hp : η a = α v) (hfresh : η a ∉ η '' Ico 0 a) :
    R7.firstVisitParam α (fun t => η '' Icc 0 t) a = v := by
  have hvmem : v ∈ {w ∈ Icc (0 : ℝ) 1 | α w ∈ η '' Icc 0 a} :=
    ⟨hv, ⟨a, ⟨ha, le_rfl⟩, hp⟩⟩
  have hle : R7.firstVisitParam α (fun t => η '' Icc 0 t) a ≤ v :=
    csInf_le (R7.bddBelow_firstVisitSet α (fun t => η '' Icc 0 t) a) hvmem
  refine le_antisymm hle (not_lt.1 fun hlt => ?_)
  -- a parameter `w < v` already visited by time `a`
  obtain ⟨w, ⟨hw, hwR⟩, hwv⟩ := (csInf_lt_iff (R7.bddBelow_firstVisitSet α (fun t => η '' Icc 0 t) a) ⟨v, hvmem⟩).1 hlt
  obtain ⟨s, hs, hse⟩ := hwR
  -- `α(w) ≠ p`, so it was visited strictly before `a`
  have hsa : s < a := by
    refine lt_of_le_of_ne hs.2 fun hsa => ?_
    rw [hsa, hp] at hse
    exact (ne_of_lt hwv) (hαi hw hv hse.symm)
  -- reverse order: `α(v)` was visited by time `s < a`
  obtain ⟨r, hr, hre⟩ := hrev s w hw v hv hwv.le ⟨s, ⟨hs.1, le_rfl⟩, hse⟩
  exact hfresh ⟨r, ⟨hr.1, lt_of_le_of_lt hr.2 hsa⟩, hre.trans hp.symm⟩

/-- **Lemma 1.4 of the elimination note, contained arm** (`ig1_ztip_elimination.txt` L211–L224). Let
`η` be a continuous Loewner trace of `W`, and `α : [0, 1] → ℂ` an injective incoming arc in reverse
first-visit order. If `p = η(a) = α(v)` is an interior point visited for the first time at `a ≥ 0`,
then `p` is the current first attachment, `u(a) = v`, and every real `q` (centred coordinate of the
`g_a` chart) whose boundary image is the attachment `α(u(a))` is the driver: `q = 0`, i.e. the lifted
incoming endpoint is `W_a`. -/
theorem lemma14_contained (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hαi : InjOn α (Icc 0 1)) (hrev : IsReverseVisitOrder α fun t => η '' Icc 0 t) {a v : ℝ}
    (ha : 0 ≤ a) (hv : v ∈ Icc (0 : ℝ) 1) (hp : η a = α v) (hpH : η a ∈ H)
    (hfresh : η a ∉ η '' Ico 0 a) :
    R7.firstVisitParam α (fun t => η '' Icc 0 t) a = v ∧
      ∀ q : ℝ, extendFrom H (fwdMapInv W a) (q : ℂ) =
        α (R7.firstVisitParam α (fun t => η '' Icc 0 t) a) → q = 0 := by
  have hu := firstVisitParam_eq_of_fresh hαi hrev ha hv hp hfresh
  refine ⟨hu, fun q hq => ?_⟩
  have ha0 : 0 < a := by
    refine lt_of_le_of_ne ha fun h0 => ?_
    have h1 : (0 : ℝ) < (η a).im := hpH
    rw [← h0, hη.1] at h1
    simp at h1
  rw [hu, ← hp] at hq
  exact hη.eq_zero_of_extendFrom_eq_of_isCutTime hW hW0 ha0 ⟨hpH, hfresh⟩ hq

end R16

end InteractingSLE
