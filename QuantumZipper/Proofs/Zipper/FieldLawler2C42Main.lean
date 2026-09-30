import QuantumZipper.Proofs.Zipper.FieldLawler2C42
import QuantumZipper.Proofs.Zipper.FieldLawler2P41

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Field–Lawler Corollary 4.2 for finitely many real crosscuts, unconditional (task FL2-C42)

Source: L. S. Field, G. F. Lawler, *Escape probability and transience for SLE*, EJP 20 (2015),
§4, Corollary 4.2, p. 11 (normalized to the real line; FL use the unit circle and a Möbius map).
`fl2C42` combines `fl2C42_main` (the maximum-principle rendering of FL's geometric-domination
proof, `FieldLawler2C42.lean`) with FL Prop 4.1 (p. 10), `fl2_prop41_half_intervals`
(`FieldLawler2P41.lean`). Crosscut hypothesis: the endpoints of each `I k = (a k, b k)` lie in
one connected set `K_k` disjoint from `D`, and `I k ⊆ D`.
-/

open Filter Set Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open QuantumZipper.Thm18Asm.LWFar

/-- **Field–Lawler, Corollary 4.2** (EJP 20 (2015), p. 11), analytic form for finitely many real
crosscuts `I k = (a k, b k)` of an open `D`: with `h k` the harmonic measure of `I k` in
`D \ I k`, `w` that of `⋃ I k` in `D \ ⋃ I k`, and `u k` that of the other crosscuts,
`∑_k h_k ≤ 2 w` on `D \ ⋃ I k` (i.e. `E_z[#crosscuts visited] ≤ 2 P_z{hit ℝ}`). -/
theorem fl2C42 {n : ℕ} {D : Set ℂ} {a b : Fin n → ℝ} (hD : IsOpen D)
    (hsub : ∀ k, ∀ t ∈ Ioo (a k) (b k), (t : ℂ) ∈ D)
    (hK : ∀ k, ∃ K : Set ℂ, IsConnected K ∧ Disjoint K D ∧ (a k : ℂ) ∈ K ∧ (b k : ℂ) ∈ K)
    (hdisj : Pairwise fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)))
    {h : Fin n → ℂ → ℝ}
    (hh : ∀ k, IsHarmMeas (D \ fl2C42Cut (a k) (b k)) (fl2C42Cut (a k) (b k)) (h k))
    {w : ℂ → ℝ}
    (hw : IsHarmMeas (D \ ⋃ k, fl2C42Cut (a k) (b k)) (⋃ k, fl2C42Cut (a k) (b k)) w)
    {u : Fin n → ℂ → ℝ}
    (hu : ∀ k, IsHarmMeas (D \ ⋃ (i) (_ : i ≠ k), fl2C42Cut (a i) (b i))
      (⋃ (i) (_ : i ≠ k), fl2C42Cut (a i) (b i)) (u k)) :
    ∀ z ∈ D \ ⋃ k, fl2C42Cut (a k) (b k), ∑ k, h k z ≤ 2 * w z := by
  have ha : ∀ k, (a k : ℂ) ∉ D := fun k hD' => by
    obtain ⟨K, -, hKD, haK, -⟩ := hK k
    exact Set.disjoint_left.1 hKD haK hD'
  have hb : ∀ k, (b k : ℂ) ∉ D := fun k hD' => by
    obtain ⟨K, -, hKD, -, hbK⟩ := hK k
    exact Set.disjoint_left.1 hKD hbK hD'
  refine fl2C42_main hD hsub ha hb hdisj hh hw hu fun k t ht => ?_
  obtain ⟨K, hKc, hKD, haK, hbK⟩ := hK k
  set I : Finset (ℝ × ℝ) := (Finset.univ.erase k).image fun i => (a i, b i) with hI
  have eU : (⋃ p ∈ I, ((↑) : ℝ → ℂ) '' Ioo p.1 p.2) =
      ⋃ (i) (_ : i ≠ k), fl2C42Cut (a i) (b i) := by
    ext z
    simp [hI, fl2C42Cut]
  refine fl2_prop41_half_intervals I hD (hsub k t ht) ht.1 ht.2 hKc hKD hbK haK ?_ ?_
    (by rw [eU]; exact hu k)
  · intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    rintro _ ⟨s, hs, rfl⟩
    exact hsub i s hs
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
    have hik : i ≠ k := Finset.ne_of_mem_erase hi
    refine Set.disjoint_left.2 fun s hs hs' => ?_
    rcases eq_or_lt_of_le hs'.1 with h1 | h1
    · exact ha k (by rw [h1]; exact hsub i s hs)
    rcases eq_or_lt_of_le hs'.2 with h2 | h2
    · exact hb k (by rw [← h2]; exact hsub i s hs)
    exact Set.disjoint_left.1 (hdisj hik) hs ⟨h1, h2⟩

end FieldLawler
end QuantumZipper
