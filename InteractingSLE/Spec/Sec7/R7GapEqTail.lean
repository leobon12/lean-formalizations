/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEq

/-!
# The old local boundary cover at a strict contained-side point

Packet PROVE-R7-GAPEQ. The local old-boundary cover used in `pocketGapEq_of_collars` is proved
here whenever the contact is off the other pocket side. Compactness separates it from that
side and from a shorter incoming prefix. Reverse visit order puts the remaining boundary
in the range strictly before the contact. The shared entrance corner is deliberately not
covered by this assertion: it lies on the other side too.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology

namespace InteractingSLE.Sec7.R7GapEq

open Sec6 R7StopIn

/-- At a strict old contact of a reverse-visited simple barrier, away from the other closed
boundary piece `A`, the local pocket boundary is already visited strictly earlier.
This proves the strict-side part of the old-boundary input without any Jordan collar theorem. -/
theorem hasOldBoundaryCover_of_strict_tail
    {η B : ℝ → ℂ} {C A : Set ℂ} {t v : ℝ}
    (hc : ContinuousOn η (Ici 0)) (hBc : ContinuousOn B (Icc 0 1))
    (hBi : InjOn B (Icc 0 1))
    (hrev : R16.IsReverseVisitOrder B fun s => η '' Icc 0 s)
    (hA : IsClosed A) (hfr : frontier C ⊆ B '' Icc 0 1 ∪ A)
    (ht : 0 ≤ t) (hv : v ∈ Icc (0 : ℝ) 1) (hp : η t = B v)
    (hpA : B v ∉ A) (hold : firstVisit (fun s => η '' Icc 0 s) B t < v) :
    HasOldBoundaryCover η C (η t) t := by
  let u := firstVisit (fun s => η '' Icc 0 s) B t
  have hcompact : IsCompact (η '' Icc 0 t) :=
    isCompact_Icc.image_of_continuousOn (hc.mono fun _ hs => hs.1)
  have hu := firstVisit_mem (R := fun s => η '' Icc 0 s) hBc hcompact.isClosed
    ⟨v, hv, t, ⟨ht, le_rfl⟩, hp⟩
  obtain ⟨r, hr, hru⟩ := hu.2
  have hrt : r < t := lt_of_le_of_ne hr.2 fun h => by
    have he : B u = B v := hru.symm.trans (h ▸ hp)
    exact hold.ne (hBi hu.1 hv he)
  let w := (u + v) / 2
  have huw : u < w := by dsimp [w]; linarith only [hold]
  have hwv : w < v := by dsimp [w]; linarith only [hold]
  have hw0 : 0 ≤ w := hu.1.1.trans huw.le
  have hw1 : w ≤ 1 := hwv.le.trans hv.2
  let P := B '' Icc 0 w
  have hPc : IsClosed P := (isCompact_Icc.image_of_continuousOn
    (hBc.mono (Icc_subset_Icc_right hw1))).isClosed
  have hpP : B v ∉ P := by
    rintro ⟨q, hq, hqv⟩
    have hq' : q ∈ Icc (0 : ℝ) 1 := ⟨hq.1, hq.2.trans hw1⟩
    have he := hBi hq' hv hqv
    exact hwv.not_ge (he ▸ hq.2)
  refine ⟨r, hr.1, hrt, (A ∪ P)ᶜ, B '' Icc w 1, (hA.union hPc).isOpen_compl,
    ?_, ?_, ?_⟩
  · rw [hp]
    exact fun h => h.elim hpA hpP
  · rintro _ ⟨q, hq, rfl⟩
    exact hrev r u hu.1 q ⟨hw0.trans hq.1, hq.2⟩ (huw.le.trans hq.1)
      ⟨r, ⟨hr.1, le_rfl⟩, hru⟩
  · intro p hpf
    rcases hfr hpf.1 with ⟨q, hq, hqp⟩ | hpA'
    · have hwq : w < q := by
        by_contra hn
        exact hpf.2 (Or.inr ⟨q, ⟨hq.1, le_of_not_gt hn⟩, hqp⟩)
      exact ⟨q, ⟨hwq.le, hq.2⟩, hqp⟩
    · exact False.elim (hpf.2 (Or.inl hpA'))

/-- **Mixed bounded pocket, with the strict old-tail geometry discharged.** The other side
`A` is closed and disjoint from the open barrier. Only the old shared entrance corner still
needs the explicitly displayed old-boundary cover, in addition to exterior collars and the
one-barrier attachment constancy. -/
theorem pocketGapEq_of_cornerCover
    {W : ℝ → ℝ} {η B : ℝ → ℂ} {C F K A : Set ℂ} {τ σ : ℝ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hCo : IsOpen C)
    (h42 : ∀ c d : ℝ, 0 ≤ c → c < d → ¬ η '' Icc c d ⊆ K)
    (hfrK : frontier C ⊆ K) (havoid : ∀ t, 0 ≤ t → η t ∉ F)
    (hA : IsClosed A) (hfr : frontier C ⊆ B '' Icc 0 1 ∪ A)
    (hdisj : ∀ v ∈ Ioo (0 : ℝ) 1, B v ∉ A)
    (houter : ∀ p ∈ A, p ∉ B '' Icc 0 1 → HasExteriorCollar C F K p)
    (hBc : ContinuousOn B (Icc 0 1)) (hBi : InjOn B (Icc 0 1))
    (hrev : R16.IsReverseVisitOrder B fun t => η '' Icc 0 t)
    (hτ0 : 0 ≤ τ) (hτ : η τ = B 1) (hτf : η τ ∉ η '' Ico 0 τ)
    (hAC : BarrierAttachConst η C B τ σ)
    (hcorner : ∀ t ∈ Ioo τ σ, firstVisit (fun s => η '' Icc 0 s) B t < 1 →
      η t = B 1 → HasOldAllowedCover η C F K (η t) t) :
    PocketGapEq η C τ σ := by
  have hfr' : frontier C ⊆ B '' Icc 0 1 ∪ (A \ B '' Icc 0 1) := by
    intro p hp
    by_cases hB : p ∈ B '' Icc 0 1
    · exact Or.inl hB
    · exact Or.inr ⟨(hfr hp).resolve_left hB, hB⟩
  apply pocketGapEq_of_collars hη hW hW0 hCo h42 havoid hfr'
    (fun p hp => houter p hp.1 hp.2) hBi hrev hτ0 hτ hτf hAC
  intro t ht v hv hlt hp
  rcases hv.2.eq_or_lt with hv1 | hv1
  · subst v
    exact hcorner t ht hlt hp
  have hu0 : 0 ≤ firstVisit (fun s => η '' Icc 0 s) B t :=
    le_csInf ⟨v, hv, t, ⟨hτ0.trans ht.1.le, le_rfl⟩, hp⟩ fun _ hq => hq.1.1
  exact (hasOldBoundaryCover_of_strict_tail hη.2.1 hBc hBi hrev hA hfr
    (hτ0.trans ht.1.le) hv hp (hdisj v ⟨hu0.trans_lt hlt, hv1⟩) hlt).toAllowed hCo hfrK

end InteractingSLE.Sec7.R7GapEq
