import LQGMetric.Papers.DDDF.T20EGlue

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.DDDF.T20E LQGMetric.LFPP

 

theorem laneC_one_detour_le {ξ : ℝ} {f g : ℂ → ℝ} {Fr : Set ℂ}
    (hfg : ∀ x ∈ Fr, g x = f x)
    {γ ρ : ℝ → ℂ}
    (hγ : AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁
      (rectAB 1 1).side₂ γ)
    (hγfin : lfppLen ξ f γ ≠ ⊤)
    (hρ : IsPiecewiseC1Path ρ (ρ 0) (ρ 1))
    (hρfin : lfppLen ξ f ρ ≠ ⊤)
    (hρsq : ∀ t ∈ Icc (0 : ℝ) 1,
      ρ t ∈ (rectAB 1 1).toSet ∩ Fr)
    {t₀ t₁ s₀ s₁ : ℝ}
    (ht₀ : t₀ ∈ Icc (0 : ℝ) 1)
    (ht₁ : t₁ ∈ Icc (0 : ℝ) 1)
    (htord : t₀ ≤ t₁)
    (hs₀ : s₀ ∈ Icc (0 : ℝ) 1)
    (hs₁ : s₁ ∈ Icc (0 : ℝ) 1)
    (hmeet₀ : γ t₀ = ρ s₀)
    (hmeet₁ : γ t₁ = ρ s₁)
    (hbefore : ∀ t ∈ Icc (0 : ℝ) t₀,
      γ t ∈ (rectAB 1 1).toSet ∩ Fr)
    (hafter : ∀ t ∈ Icc t₁ (1 : ℝ),
      γ t ∈ (rectAB 1 1).toSet ∩ Fr) :
    (rectLen ξ g (rectAB 1 1)).toReal ≤
      (lfppLen ξ f γ).toReal + (lfppLen ξ f ρ).toReal := by
  classical
  let e : Circle × ℂ := (1, 0)
  let pc : Circle × ℂ → ℝ → ℂ := fun _ => ρ
  obtain ⟨z, hz, w, hw, hpath, hU⟩ := hγ
  have hz₀ : γ 0 ∈ (rectAB 1 1).side₁ := by rw [hpath.source]; exact hz
  have hz₁ : γ 1 ∈ (rectAB 1 1).side₂ := by rw [hpath.target]; exact hw
  have hS : lfppDOn ξ g (rectAB 1 1).toSet (γ 0) (pc e s₀) ≤
      ∫⁻ t in Icc 0 t₀, lenDens ξ f γ t := by
    rw [show pc e s₀ = γ t₀ by exact hmeet₀.symm]
    exact dOn_piece_le hfg hpath le_rfl ht₀.1 ht₀.2 hbefore
  have hE : lfppDOn ξ g (rectAB 1 1).toSet (pc e s₁) (γ 1) ≤
      ∫⁻ t in Icc t₁ 1, lenDens ξ f γ t := by
    rw [show pc e s₁ = γ t₁ by exact hmeet₁.symm]
    exact dOn_piece_le hfg hpath ht₁.1 ht₁.2 le_rfl hafter
  have hpc : ∀ j ∈ ({e} : Finset (Circle × ℂ)),
      IsPiecewiseC1Path (pc j) (pc j 0) (pc j 1) := by
    intro j hj
    exact hρ
  have hpcsq : ∀ j ∈ ({e} : Finset (Circle × ℂ)),
      ∀ t ∈ Icc (0 : ℝ) 1, pc j t ∈ (rectAB 1 1).toSet ∩ Fr := by
    intro j hj t ht
    exact hρsq t ht
  have hpcfin : ∀ j ∈ ({e} : Finset (Circle × ℂ)), lfppLen ξ f (pc j) ≠ ⊤ := by
    intro j hj
    exact hρfin
  have hconn : ∀ i ∈ ({e} : Finset (Circle × ℂ)),
      ∀ j ∈ ({e} : Finset (Circle × ℂ)),
      (meetGraph pc (({e} : Finset (Circle × ℂ)) : Set (Circle × ℂ))).Reachable i j := by
    intro i hi j hj
    simp only [Finset.mem_singleton] at hi hj
    subst i
    subst j
    exact SimpleGraph.Reachable.refl _
  have hbase := glue_le (ξ := ξ) hfg hγfin
    (R := {e}) (pc := pc) hpc hpcsq hpcfin hconn
    ht₀.1 htord ht₁.2 (Finset.mem_singleton_self e)
    (Finset.mem_singleton_self e) hs₀ hs₁
    hz₀ hz₁ hS hE
  simpa only [Finset.sum_singleton] using hbase

end SupercriticalLQGUniqueness.B2.DG20Conc
