import SupercriticalLQGUniqueness.B2.DG20Lim.EndpointChain

 


set_option autoImplicit false
noncomputable section

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem right_endpoint_disconnects_chain
    (k : ℕ) (hk : 0 < k) (O : Fin (k + 1) → RatCircle)
    (w : ℂ)
    (hdisj : ∀ i j : Fin (k + 1), i ≠ j →
      Disjoint (O i).toSet (O j).toSet)
    (hsep : ∀ j : ℕ, (hj : 0 < j) → (hjk : j < k) →
      Disconnects (O ⟨j, by omega⟩).toSet
        (O ⟨j - 1, by omega⟩).toSet
        (O ⟨j + 1, by omega⟩).toSet)
    (hw : (O ⟨k, by omega⟩).DisconnectsPoint w
      (O ⟨k - 1, by omega⟩)) :
    (O ⟨k, by omega⟩).DisconnectsPoint w
      (O ⟨0, by omega⟩) := by
  let V : Fin (k + 1) → RatCircle := fun i => O ⟨k - i.val, by omega⟩
  have hVdisj : ∀ i j : Fin (k + 1), i ≠ j →
      Disjoint (V i).toSet (V j).toSet := by
    intro i j hij
    apply hdisj
    intro heq
    apply hij
    apply Fin.ext
    have hval := congrArg Fin.val heq
    change k - i.val = k - j.val at hval
    omega
  have hVsep : ∀ j : ℕ, (hj : 0 < j) → (hjk : j < k) →
      Disconnects (V ⟨j, by omega⟩).toSet
        (V ⟨j - 1, by omega⟩).toSet
        (V ⟨j + 1, by omega⟩).toSet := by
    intro j hj hjk
    have hj' : 0 < k - j := by omega
    have hjk' : k - j < k := by omega
    have h := disconnects_symm (hsep (k - j) hj' hjk')
    have hVm : V ⟨j - 1, by omega⟩ = O ⟨k - j + 1, by omega⟩ := by
      change O ⟨k - (j - 1), by omega⟩ = O ⟨k - j + 1, by omega⟩
      congr 1
      apply Fin.ext
      dsimp
      omega
    have hVp : V ⟨j + 1, by omega⟩ = O ⟨k - j - 1, by omega⟩ := by
      change O ⟨k - (j + 1), by omega⟩ = O ⟨k - j - 1, by omega⟩
      congr 1
    simpa only [V, hVm, hVp] using h
  have hV0 : V ⟨0, by omega⟩ = O ⟨k, by omega⟩ := by simp [V]
  have hV1 : V ⟨1, by omega⟩ = O ⟨k - 1, by omega⟩ := by simp [V]
  have hVk : V ⟨k, by omega⟩ = O ⟨0, by omega⟩ := by simp [V]
  have hVw : (V ⟨0, by omega⟩).DisconnectsPoint w
      (V ⟨1, by omega⟩) := by simpa only [hV0, hV1] using hw
  have hresult := left_endpoint_disconnects_chain k hk V w hVdisj hVsep hVw
  simpa only [hV0, hVk] using hresult

end SupercriticalLQGUniqueness.B2.DG20Lim
