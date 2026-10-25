import SupercriticalLQGUniqueness.B2.PfeWeyl.LocalComparison
import SupercriticalLQGUniqueness.B2.PfeWeyl.GammaCompact

 




set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

private theorem ennreal_le_liminf_add (u v : ℕ → ENNReal) :
    liminf u atTop + liminf v atTop ≤ liminf (fun n => u n + v n) atTop := by
  have hc (w : ℕ → ENNReal) : ((liminf w atTop : ENNReal) : EReal) =
      liminf (fun n => (w n : EReal)) atTop :=
    EReal.coe_ennreal_strictMono.monotone.map_liminf_of_continuousAt w
      continuous_coe_ennreal_ereal.continuousAt
  apply EReal.coe_ennreal_le_coe_ennreal_iff.mp
  rw [EReal.coe_ennreal_add, hc u, hc v, hc (fun n => u n + v n)]
  simp only [EReal.coe_ennreal_add]
  exact EReal.le_liminf_add

 

theorem finite_sum_le_liminf {ι : Type*} (s : Finset ι)
    (a : ι → ENNReal) (u : ℕ → ι → ENNReal)
    (h : ∀ i ∈ s, a i ≤ liminf (fun n => u n i) atTop) :
    (∑ i ∈ s, a i) ≤ liminf (fun n => ∑ i ∈ s, u n i) atTop := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hi' : a i ≤ liminf (fun n => u n i) atTop :=
      h i (Finset.mem_insert_self _ _)
    have hs : ∀ j ∈ s, a j ≤ liminf (fun n => u n j) atTop :=
      fun j hj => h j (Finset.mem_insert_of_mem hj)
    simpa only [Finset.sum_insert hi] using
      (add_le_add hi' (ih hs)).trans (ennreal_le_liminf_add _ _ :
        liminf (fun n => u n i) atTop +
          liminf (fun n => ∑ j ∈ s, u n j) atTop ≤
            liminf (fun n => u n i + ∑ j ∈ s, u n j) atTop)

 


theorem finiteChain_subseq_liminf
    {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D))
    {K : Set ℂ} (hK : IsCompact K) (N : ℕ)
    (v : ℕ → Fin (N + 1) → ℂ)
    (hv : ∀ n i, v n i ∈ K) :
    ∃ (φ : ℕ → ℕ) (w : Fin (N + 1) → ℂ),
      StrictMono φ ∧
      (∀ i, w i ∈ K) ∧
      (∀ i, Tendsto (fun n => v (φ n) i) atTop (𝓝 (w i))) ∧
      (∀ (i : Fin (N + 1)) (hi : (i : ℕ) < N),
        D (w i, w ⟨(i : ℕ) + 1, Nat.succ_lt_succ hi⟩) ≤
          liminf (fun n => G (φ n)
            (v (φ n) i, v (φ n) ⟨(i : ℕ) + 1, Nat.succ_lt_succ hi⟩)) atTop) := by
  have hpi : IsCompact (Set.pi Set.univ (fun _ : Fin (N + 1) => K)) :=
    isCompact_univ_pi fun _ => hK
  have hvpi : ∀ n, v n ∈ Set.pi Set.univ (fun _ : Fin (N + 1) => K) := by
    intro n
    exact Set.mem_pi.mpr fun i _ => hv n i
  obtain ⟨w, hw, φ, hφ, hconv⟩ := hpi.tendsto_subseq (x := v) hvpi
  have hwK : ∀ i, w i ∈ K := fun i => (Set.mem_pi.mp hw) i (Set.mem_univ i)
  have hcoord : ∀ i, Tendsto (fun n => v (φ n) i) atTop (𝓝 (w i)) :=
    (tendsto_pi_nhds.mp hconv)
  refine ⟨φ, w, hφ, hwK, hcoord, ?_⟩
  intro i hi
  let j : Fin (N + 1) := ⟨(i : ℕ) + 1, Nat.succ_lt_succ hi⟩
  have hp : Tendsto (fun n => (v (φ n) i, v (φ n) j)) atTop (𝓝 (w i, w j)) :=
    (hcoord i).prodMk_nhds (hcoord j)
  have hGφ : Tendsto (fun n => G (φ n)) atTop (𝓝 D) :=
    hG.comp hφ.tendsto_atTop
  exact (LSCMetric.tendsto_iff.mp hGφ).1 _ _ hp

 

theorem field_at_moving_vertex_tendsto
    {K : Set ℂ} (f : C(ℂ, ℝ)) (fn : ℕ → C(ℂ, ℝ))
    (hfn : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ x ∈ K, |fn n x - f x| < ε)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {v : ℕ → ℂ} (hvK : ∀ n, v n ∈ K)
    {w : ℂ} (hv : Tendsto (fun n => v (φ n)) atTop (𝓝 w)) :
    Tendsto (fun n => fn (φ n) (v (φ n))) atTop (𝓝 (f w)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hclose := hφ.tendsto_atTop.eventually (hfn (ε / 2) (half_pos hε))
  have hcont := Metric.tendsto_nhds.mp ((f.continuous.tendsto w).comp hv)
    (ε / 2) (half_pos hε)
  filter_upwards [hclose, hcont] with n hn hc
  have h1 := hn (v (φ n)) (hvK (φ n))
  have hc' : |f (v (φ n)) - f w| < ε / 2 := by
    simpa only [Function.comp_def, Real.dist_eq] using hc
  rw [Real.dist_eq]
  calc
    |fn (φ n) (v (φ n)) - f w| ≤
        |fn (φ n) (v (φ n)) - f (v (φ n))| +
          |f (v (φ n)) - f w| := by
      calc
        _ = |(fn (φ n) (v (φ n)) - f (v (φ n))) +
            (f (v (φ n)) - f w)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
    _ < ε := by linarith

 


def chainLeft (N : ℕ) (j : Fin N) : Fin (N + 1) :=
  ⟨j, Nat.lt_succ_of_lt j.isLt⟩

def chainRight (N : ℕ) (j : Fin N) : Fin (N + 1) :=
  ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩

def chainWeight (ξ : ℝ) (g : C(ℂ, ℝ)) (z : ℂ) : ENNReal :=
  ENNReal.ofReal (Real.exp (ξ * g z))

theorem finiteChain_weighted_liminf
    {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D))
    {K : Set ℂ} (hK : IsCompact K)
    (ξ : ℝ) (f : C(ℂ, ℝ)) (fn : ℕ → C(ℂ, ℝ))
    (hfn : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ x ∈ K, |fn n x - f x| < ε)
    (N : ℕ) (v : ℕ → Fin (N + 1) → ℂ)
    (hv : ∀ n i, v n i ∈ K) :
    ∃ (φ : ℕ → ℕ) (w : Fin (N + 1) → ℂ),
      StrictMono φ ∧ (∀ i, w i ∈ K) ∧
      (∀ i, Tendsto (fun n => v (φ n) i) atTop (𝓝 (w i))) ∧
      (∑ j : Fin N,
          chainWeight ξ f (w (chainLeft N j)) *
            D (w (chainLeft N j), w (chainRight N j))) ≤
        liminf (fun n => ∑ j : Fin N,
          chainWeight ξ (fn (φ n)) (v (φ n) (chainLeft N j)) *
            G (φ n) (v (φ n) (chainLeft N j), v (φ n) (chainRight N j))) atTop := by
  obtain ⟨φ, w, hφ, hwK, hcoord, hdist⟩ := finiteChain_subseq_liminf hG hK N v hv
  refine ⟨φ, w, hφ, hwK, hcoord, ?_⟩
  apply finite_sum_le_liminf Finset.univ
  intro j hj
  let i : Fin (N + 1) := chainLeft N j
  let k : Fin (N + 1) := chainRight N j
  have hfield := field_at_moving_vertex_tendsto f fn hfn hφ
    (hvK := fun n => hv n i) (hv := hcoord i)
  have hreal : Tendsto
      (fun n => Real.exp (ξ * fn (φ n) (v (φ n) i))) atTop
      (𝓝 (Real.exp (ξ * f (w i)))) := by
    exact (Real.continuous_exp.tendsto _).comp
      (tendsto_const_nhds.mul hfield)
  have hweight : Tendsto
      (fun n => chainWeight ξ (fn (φ n)) (v (φ n) i)) atTop
      (𝓝 (chainWeight ξ f (w i))) := by
    simpa only [chainWeight] using ENNReal.tendsto_ofReal hreal
  have hmul := ENNReal.le_liminf_mul
    (u := fun n => chainWeight ξ (fn (φ n)) (v (φ n) i))
    (v := fun n => G (φ n) (v (φ n) i, v (φ n) k)) (f := atTop)
  have hbase : chainWeight ξ f (w i) * D (w i, w k) ≤
      liminf (fun n =>
        chainWeight ξ (fn (φ n)) (v (φ n) i) *
          G (φ n) (v (φ n) i, v (φ n) k)) atTop := by
    calc
      _ ≤ chainWeight ξ f (w i) *
          liminf (fun n => G (φ n) (v (φ n) i, v (φ n) k)) atTop :=
        mul_le_mul' le_rfl (by
          have hseg := hdist i (by simpa only [i, chainLeft] using j.isLt)
          simpa only [i, k, chainLeft, chainRight] using hseg)
      _ = liminf (fun n =>
          chainWeight ξ (fn (φ n)) (v (φ n) i)) atTop *
            liminf (fun n => G (φ n) (v (φ n) i, v (φ n) k)) atTop := by
        rw [hweight.liminf_eq]
      _ ≤ _ := hmul
  exact hbase

end SupercriticalLQGUniqueness.B2.PfeWeyl
