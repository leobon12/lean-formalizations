import QuantumZipper.Proofs.Zipper.SWCoreB8FBox

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B8F (2): fixed-path offset convergence on the whole `(s, c)` rectangle

`flow_fixed_conv3`: for a **fixed** continuous driver `W` (anchor `0 < q ≤ T`, window live at `q`)
and every free field `Y`, almost surely, for every continuous `f` supported in `[u₂, v₂]`, the
dilated transported test integrals `offInt … s c k` (`flowFam` maps composed with `z ↦ c z`, test
function `awTest (F_s) u v f (c ·)`) are uniformly Cauchy in `k`, uniformly in
`(s, c) ∈ [q,T] × [1,2]`. Finite cover of the compact rectangle by the boxes of `flow_box_conv3`,
exactly as `flow_fixed_conv` (SWCoreB7cBox.lean).

`uniformCauchySeqOn_of_dense`: a uniformly Cauchy sequence on a dense subset `D` of a closed set
`S`, of functions continuous on `S`, is uniformly Cauchy on `S` (the continuity step (c) of the
B8 plan, at fixed `k`).

Sheffield–Wang arXiv:1605.06171 Thm 1.4 / Thm 4.3 through the D64 family cores; own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace SWCore

open B2 RegUnif

/-- The dilated transported test integral of the offset flow box: test function
`awTest (F_s) u v f (c ·)`, field `coordChange (𝔥₀ + y) (ψ_s ∘ (c ·)) Q`, scale `k`. -/
def offInt (κ γ : ℝ) (W : ℝ → ℝ) (T q u v : ℝ) (f : ℝ → ℝ) (y : FieldSample) (s c : ℝ)
    (k : ℕ) : ℝ :=
  ∫ x, awTest (realRevMap (vrev W T) (T - s)) u v f (c * x) ∂bdryApprox γ
    (coordChange (ofFun (h0rev κ) + y) (fun z => flowFam W q ![s, W s] ((c : ℂ) * z)) (Qc γ)) k

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

set_option maxHeartbeats 1000000 in
/-- **Fixed-path offset convergence on `[q,T] × [1,2]`, Cauchy across offsets**: the limit does
not depend on the offset (`dil_limit_eq` in each box, local constancy in `c` on the connected
`[1,2]`), so the integrals at `(k, c)` and `(k', c')` are close for all large `k, k'`. -/
theorem flow_fixed_conv3 {W : ℝ → ℝ} (hW : Continuous W) {T q : ℝ} (hq0 : 0 < q) (hqT : q ≤ T)
    {u v u' v' u₂ v₂ : ℝ} (huu' : u < u') (hu'v' : u' < v') (hv'v : v' < v)
    (hu₂ : u' < u₂) (hu₂v₂ : u₂ ≤ v₂) (hv₂ : v₂ < v')
    (hLive : ∀ x ∈ Icc u v, ENNReal.ofReal (T - q) < realHitTime (vrev W T) x)
    (κ : ℝ) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (Y : Ω → FieldSample)
    (hY : IsFreeGFFModConstH Y P) :
    ∀ᵐ ω ∂P, ∀ f : ℝ → ℝ, Continuous f → tsupport f ⊆ Icc u₂ v₂ →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k : ℕ, N ≤ k → ∀ k' : ℕ, N ≤ k' → ∀ s ∈ Icc q T,
        ∀ c ∈ Icc (1 : ℝ) 2, ∀ c' ∈ Icc (1 : ℝ) 2,
          |offInt κ γ W T q u v f (Y ω) s c k - offInt κ γ W T q u v f (Y ω) s c' k'| < ε := by
  classical
  have hbox : ∀ p₀ ∈ Icc q T ×ˢ Icc (1 : ℝ) 2, ∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂P, ∀ f : ℝ → ℝ,
      Continuous f → tsupport f ⊆ Icc u₂ v₂ → ∃ Λ : ℝ → ℝ, ∀ η : ℝ, 0 < η →
        ∀ᶠ k in atTop, ∀ s ∈ Icc q T, |s - p₀.1| ≤ ε → ∀ c ∈ Icc (1 : ℝ) 2, |c - p₀.2| ≤ ε →
          |offInt κ γ W T q u v f (Y ω) s c k - Λ s| ≤ η := fun p₀ hp₀ => by
    obtain ⟨ε, hε, h⟩ := flow_box_conv3 (P := P) hW hq0 hqT huu' hu'v' hv'v hu₂ hu₂v₂ hv₂ hLive
      hp₀.1 hp₀.2 κ hγ hγ2
    exact ⟨ε, hε, h Y hY⟩
  choose! εf hεf hae using hbox
  obtain ⟨t, htS, hcov⟩ := (isCompact_Icc.prod isCompact_Icc :
      IsCompact (Icc q T ×ˢ Icc (1 : ℝ) 2)).elim_nhds_subcover
    (fun p₀ => ball p₀ (εf p₀)) (fun p₀ hp₀ => ball_mem_nhds _ (hεf p₀ hp₀))
  have hall : ∀ᵐ ω ∂P, ∀ p₀ ∈ t, ∀ f : ℝ → ℝ, Continuous f →
      tsupport f ⊆ Icc u₂ v₂ → ∃ Λ : ℝ → ℝ, ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
        ∀ s ∈ Icc q T, |s - p₀.1| ≤ εf p₀ → ∀ c ∈ Icc (1 : ℝ) 2, |c - p₀.2| ≤ εf p₀ →
          |offInt κ γ W T q u v f (Y ω) s c k - Λ s| ≤ η :=
    (ae_ball_iff t.countable_toSet).2 fun p₀ hp₀ => hae p₀ (htS p₀ hp₀)
  filter_upwards [hall] with ω hω f hf hfs
  choose Λ hΛ using fun (p₀ : t) => hω p₀.1 p₀.2 f hf hfs
  have hpick : ∀ p ∈ Icc q T ×ˢ Icc (1 : ℝ) 2, ∃ p₀ : t,
      |p.1 - p₀.1.1| < εf p₀.1 ∧ |p.2 - p₀.1.2| < εf p₀.1 := by
    intro p hp
    obtain ⟨p₀, hp₀t, hpp⟩ := mem_iUnion₂.1 (hcov hp)
    rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hpp
    exact ⟨⟨p₀, hp₀t⟩, hpp⟩
  choose j hj using hpick
  have htend : ∀ p₀ : t, ∀ s ∈ Icc q T, |s - p₀.1.1| ≤ εf p₀.1 → ∀ c ∈ Icc (1 : ℝ) 2,
      |c - p₀.1.2| ≤ εf p₀.1 →
      Tendsto (fun k => offInt κ γ W T q u v f (Y ω) s c k) atTop (𝓝 (Λ p₀ s)) := by
    intro p₀ s hs hss c hc hcc
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hΛ p₀ (η / 2) (by positivity))
    exact ⟨N, fun k hk => by
      rw [Real.dist_eq]; exact lt_of_le_of_lt (hN k hk s hs hss c hc hcc) (by linarith)⟩
  have h1I : (1 : ℝ) ∈ Icc (1 : ℝ) 2 := ⟨le_rfl, by norm_num⟩
  have hconst : ∀ s (hs : s ∈ Icc q T), ∀ c (hc : c ∈ Icc (1 : ℝ) 2),
      Λ (j (s, c) ⟨hs, hc⟩) s = Λ (j (s, 1) ⟨hs, h1I⟩) s := by
    intro s hs
    let φ : Icc (1 : ℝ) 2 → ℝ := fun c => Λ (j (s, c.1) ⟨hs, c.2⟩) s
    have hloc : IsLocallyConstant φ := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro c
      obtain ⟨g1, g2⟩ := hj (s, c.1) ⟨hs, c.2⟩
      have hr : 0 < εf (j (s, c.1) ⟨hs, c.2⟩).1 - |c.1 - (j (s, c.1) ⟨hs, c.2⟩).1.2| := by
        simp only at g2; linarith
      filter_upwards [Metric.ball_mem_nhds c hr] with c'' hc''
      rw [mem_ball, Subtype.dist_eq, Real.dist_eq] at hc''
      have hin : |c''.1 - (j (s, c.1) ⟨hs, c.2⟩).1.2| ≤ εf (j (s, c.1) ⟨hs, c.2⟩).1 := by
        have := abs_sub_le c''.1 c.1 (j (s, c.1) ⟨hs, c.2⟩).1.2
        linarith
      have t1 := htend (j (s, c.1) ⟨hs, c.2⟩) s hs g1.le c''.1 c''.2 hin
      obtain ⟨g1', g2'⟩ := hj (s, c''.1) ⟨hs, c''.2⟩
      have t2 := htend (j (s, c''.1) ⟨hs, c''.2⟩) s hs g1'.le c''.1 c''.2 g2'.le
      exact tendsto_nhds_unique t2 t1
    intro c hc
    haveI : PreconnectedSpace (Icc (1 : ℝ) 2) :=
      isPreconnected_iff_preconnectedSpace.1 isPreconnected_Icc
    exact hloc.apply_eq_of_preconnectedSpace ⟨c, hc⟩ ⟨1, h1I⟩
  intro ε hε
  have hfin : ∀ᶠ k in atTop, ∀ p₀ : t, ∀ s ∈ Icc q T, |s - p₀.1.1| ≤ εf p₀.1 →
      ∀ c ∈ Icc (1 : ℝ) 2, |c - p₀.1.2| ≤ εf p₀.1 →
      |offInt κ γ W T q u v f (Y ω) s c k - Λ p₀ s| ≤ ε / 3 :=
    eventually_all.2 fun p₀ => hΛ p₀ (ε / 3) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hfin
  refine ⟨N, fun k hk k' hk' s hs c hc c' hc' => ?_⟩
  have b1 := hN k hk (j (s, c) ⟨hs, hc⟩) s hs (hj (s, c) ⟨hs, hc⟩).1.le c hc
    (hj (s, c) ⟨hs, hc⟩).2.le
  have b2 := hN k' hk' (j (s, c') ⟨hs, hc'⟩) s hs (hj (s, c') ⟨hs, hc'⟩).1.le c' hc'
    (hj (s, c') ⟨hs, hc'⟩).2.le
  rw [hconst s hs c hc] at b1
  rw [hconst s hs c' hc'] at b2
  rw [abs_le] at b1 b2
  rw [abs_sub_lt_iff]
  constructor <;> linarith [b1.1, b1.2, b2.1, b2.2]

end SWCore
end QuantumZipper
