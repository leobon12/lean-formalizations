import HigherDimLQGMetric.Weak.DetInternalTight

/-!
# Uniform internal diameter bounds on compact endpoint sets
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace HigherDimLFPPAS.Det

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Locally uniform convergence of continuous length metrics gives a uniform bound on the
internal distances in a fixed open connected set, when both endpoints range over a compact
subset. The bound in fact holds for every index after enlarging it to account for the finite
initial segment. -/
theorem eventually_uniform_internal_bound
    (Dn : ℕ → ContMetric d) (D : ContMetric d)
    (hDn : ∀ n, (Dn n).IsLength)
    (hconv : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(Dn n).1) ⇑D.1 atTop
      (Metric.closedBall (0 : Rd d) R ×ˢ Metric.closedBall (0 : Rd d) R))
    {U F : Set (Rd d)} (hU : IsOpen U) (hUc : IsConnected U)
    (hF : IsCompact F) (hFU : F ⊆ U) :
    ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n ≥ N, ∀ x ∈ F, ∀ y ∈ F,
      (Dn n).internal U x y ≤ ENNReal.ofReal C := by
  classical
  let φ : {p : Rd d × Rd d // p ∈ F ×ˢ F} → U × U := fun p =>
    (⟨p.1.1, hFU p.2.1⟩, ⟨p.1.2, hFU p.2.2⟩)
  have hφ₁ : Continuous (fun p : {q : Rd d × Rd d // q ∈ F ×ˢ F} =>
      (⟨p.1.1, hFU p.2.1⟩ : U)) :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk (fun p => hFU p.2.1)
  have hφ₂ : Continuous (fun p : {q : Rd d × Rd d // q ∈ F ×ˢ F} =>
      (⟨p.1.2, hFU p.2.2⟩ : U)) :=
    (continuous_snd.comp continuous_subtype_val).subtype_mk (fun p => hFU p.2.2)
  have hφc : Continuous φ := hφ₁.prodMk hφ₂
  let K : Set (U × U) := Set.range φ
  have hFF : IsCompact (F ×ˢ F) := hF.prod hF
  have hFF' : IsCompact (Set.univ : Set {p : Rd d × Rd d // p ∈ F ×ˢ F}) :=
    (isCompact_iff_isCompact_univ (s := F ×ˢ F)).mp hFF
  have hK : IsCompact K := by
    simpa [K, Set.image_univ] using hFF'.image hφc
  have hlocal (p : U × U) : ∃ W : Set (U × U), IsOpen W ∧ p ∈ W ∧
      ∃ N : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ n ≥ N, ∀ q ∈ W,
        internalC (Dn n) (hDn n) hU hUc.isPreconnected q ≤ B := by
    obtain ⟨B, hB, hBp⟩ := bounded_internalC_pointwise Dn D hDn hconv hU
      hUc.isPreconnected p
    obtain ⟨V₁, hV₁, hsmall₁⟩ := eventually_internalC_small_near Dn D hDn hconv hU
      hUc.isPreconnected p.1 (by norm_num : (0 : ℝ) < 1 / 2)
    obtain ⟨V₂, hV₂, hsmall₂⟩ := eventually_internalC_small_near Dn D hDn hconv hU
      hUc.isPreconnected p.2 (by norm_num : (0 : ℝ) < 1 / 2)
    have hV : V₁ ×ˢ V₂ ∈ 𝓝 p := prod_mem_nhds hV₁ hV₂
    let W : Set (U × U) := interior (V₁ ×ˢ V₂)
    have hpW : p ∈ W := mem_interior_iff_mem_nhds.2 hV
    have hWopen : IsOpen W := isOpen_interior
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 hsmall₁
    obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 hsmall₂
    refine ⟨W, hWopen, hpW, max N₁ N₂, B + 1, by linarith, ?_⟩
    intro n hn q hq
    have hq' : q ∈ V₁ ×ˢ V₂ := interior_subset hq
    have h₁ := hN₁ n (le_trans (le_max_left _ _) hn) q.1 hq'.1
    have h₂ := hN₂ n (le_trans (le_max_right _ _) hn) q.2 hq'.2
    have hdist := internalC_dist_le (Dn n) (hDn n) hU hUc.isPreconnected p q
    have hclose : dist
        (internalC (Dn n) (hDn n) hU hUc.isPreconnected p)
        (internalC (Dn n) (hDn n) hU hUc.isPreconnected q) < 1 := by
      have hsmall₁' : internalC (Dn n) (hDn n) hU hUc.isPreconnected (p.1, q.1) < 1 / 2 := h₁
      have hsmall₂' : internalC (Dn n) (hDn n) hU hUc.isPreconnected (p.2, q.2) < 1 / 2 := h₂
      calc
        _ ≤ internalC (Dn n) (hDn n) hU hUc.isPreconnected (p.1, q.1) +
              internalC (Dn n) (hDn n) hU hUc.isPreconnected (p.2, q.2) := hdist
        _ < 1 := by linarith
    have hqle : internalC (Dn n) (hDn n) hU hUc.isPreconnected q ≤
        internalC (Dn n) (hDn n) hU hUc.isPreconnected p + 1 := by
      rw [Real.dist_eq] at hclose
      have := (abs_lt.mp hclose).1
      linarith
    exact hqle.trans (by linarith [hBp n])
  choose W hWopen hWp Np Bp hBp using hlocal
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover W hWopen (by
    rintro q ⟨p, rfl⟩
    exact Set.mem_iUnion.2 ⟨φ p, hWp (φ p)⟩)
  let N : ℕ := t.sup Np
  let C : ℝ := t.sum (fun p => Bp p + 1)
  refine ⟨N, C, ?_, ?_⟩
  · dsimp [C]
    exact Finset.sum_nonneg fun p hp => by linarith [hBp p]
  · intro n hn x hx y hy
    let p : U × U := (⟨x, hFU hx⟩, ⟨y, hFU hy⟩)
    have hpK : p ∈ K := ⟨(⟨(x,y), hx, hy⟩), rfl⟩
    obtain ⟨q, hqt, hpq⟩ := Set.mem_iUnion₂.1 (ht hpK)
    have hNq : Np q ≤ N := by
      dsimp [N]
      exact Finset.le_sup hqt
    have hqbound := (hBp q).2 n (hNq.trans hn) p hpq
    have hqC : Bp q + 1 ≤ C := by
      dsimp [C]
      exact Finset.single_le_sum (f := fun r => Bp r + 1)
        (fun r hr => add_nonneg (hBp r).1 (by norm_num)) hqt
    have hfinite := (Dn n).internal_ne_top_of_isPreconnected (hDn n) hU
      hUc.isPreconnected (hFU hx) (hFU hy)
    have hreal : ((Dn n).internal U x y).toReal ≤ C := by
      change internalC (Dn n) (hDn n) hU hUc.isPreconnected p ≤ C
      exact hqbound.trans (by linarith)
    rw [← ENNReal.ofReal_toReal hfinite]
    exact ENNReal.ofReal_le_ofReal hreal

end HigherDimLFPPAS.Det

