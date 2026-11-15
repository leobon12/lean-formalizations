/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfFinishSupport

/-!
# Enumerating the genuine force jumps

Packet PROVE-CFCHART2. Strict ordering identifies the canonical finite-set enumeration
with the given nonseed force coordinates, including the required finite-index casts.
-/

set_option autoImplicit false

noncomputable section

open Filter Set Topology

namespace InteractingSLE.Sec5.CfFinish

open PiecewiseConstantBoundaryData Cond44Ref

/-- Changing only the proof of the enumeration's length casts its argument. -/
theorem orderEmbOfFin_cast {S : Finset ℝ} {n : ℕ} (hn : S.card = n) (i : Fin S.card) :
    S.orderEmbOfFin rfl i = S.orderEmbOfFin hn (Fin.cast hn i) := by
  subst n
  rfl

open scoped Classical in
/-- The decreasing enumeration of a strictly decreasing tail is that tail. -/
theorem orderEmb_left_tail {n : ℕ} {v : Fin (n + 1) → ℝ} (hv : StrictAnti v)
    {S : Finset ℝ} (hS : S = Finset.univ.image (fun i : Fin n => v i.succ))
    (hn : S.card = n) (i : Fin S.card) :
    S.orderEmbOfFin rfl i.rev = v (Fin.cast hn i).succ := by
  classical
  have hm : StrictMono (fun j : Fin n => v j.rev.succ) := by
    intro j k hjk
    apply hv
    change k.rev.val + 1 < j.rev.val + 1
    exact Nat.succ_lt_succ (Fin.rev_lt_rev.2 hjk)
  have he : (fun j : Fin n => v j.rev.succ) = S.orderEmbOfFin hn :=
    Finset.orderEmbOfFin_unique hn (fun j => by
      rw [hS]
      exact Finset.mem_image.2 ⟨j.rev, Finset.mem_univ _, rfl⟩) hm
  rw [orderEmbOfFin_cast hn, ← he]
  have hi : i.val < n := hn ▸ i.is_lt
  dsimp only
  congr 1
  apply Fin.ext
  simp only [Fin.val_succ, Fin.val_rev, Fin.val_cast, hn]
  omega

open scoped Classical in
/-- The increasing enumeration of a strictly increasing tail is that tail. -/
theorem orderEmb_right_tail {n : ℕ} {v : Fin (n + 1) → ℝ} (hv : StrictMono v)
    {S : Finset ℝ} (hS : S = Finset.univ.image (fun i : Fin n => v i.succ))
    (hn : S.card = n) (i : Fin S.card) :
    S.orderEmbOfFin rfl i = v (Fin.cast hn i).succ := by
  classical
  have hm : StrictMono (fun j : Fin n => v j.succ) := by
    intro j k hjk
    exact hv (show j.succ < k.succ from Nat.succ_lt_succ hjk)
  have he : (fun j : Fin n => v j.succ) = S.orderEmbOfFin hn :=
    Finset.orderEmbOfFin_unique hn (fun j => by
      rw [hS]
      exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩) hm
  rw [orderEmbOfFin_cast hn, ← he]

variable {nL nR : ℕ} {κ : ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
  {vL : Fin (nL + 1) → ℝ} {vR : Fin (nR + 1) → ℝ}

/-- Counting negative genuine jumps recovers the original number of left marks. -/
theorem card_left_jumps_force (hκ : 0 < κ) (hL : StrictAnti vL) (hL0 : vL 0 = 0)
    (hρL : ∀ i : Fin nL, ρL i.succ ≠ 0) :
    ((jumpSet (forceBoundaryData κ ρL ρR vL vR)
      (forceJumpFinset vL vR)).filter (· < 0)).card = nL := by
  classical
  have hinj : Function.Injective (fun i : Fin nL => vL i.succ) :=
    hL.injective.comp (Fin.succ_injective nL)
  rw [left_jumps_force hκ hL hL0 hρL,
    Finset.card_image_of_injective _ hinj,
    Finset.card_univ, Fintype.card_fin]

/-- Counting positive genuine jumps recovers the original number of right marks. -/
theorem card_right_jumps_force (hκ : 0 < κ) (hR : StrictMono vR) (hR0 : vR 0 = 0)
    (hρR : ∀ i : Fin nR, ρR i.succ ≠ 0) :
    ((jumpSet (forceBoundaryData κ ρL ρR vL vR)
      (forceJumpFinset vL vR)).filter (0 < ·)).card = nR := by
  classical
  have hinj : Function.Injective (fun j : Fin nR => vR j.succ) :=
    hR.injective.comp (Fin.succ_injective nR)
  rw [right_jumps_force hκ hR hR0 hρR,
    Finset.card_image_of_injective _ hinj,
    Finset.card_univ, Fintype.card_fin]

end InteractingSLE.Sec5.CfFinish
