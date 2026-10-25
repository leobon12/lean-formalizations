import SupercriticalLQGUniqueness.B2.PfeAxioms.InputsGeometry0
import SupercriticalLQGUniqueness.B2.LscTop.Limits
import SupercriticalLQGUniqueness.B2.LscTop.LFPP

 

set_option autoImplicit false
noncomputable section

open Filter Topology MeasureTheory
open LQGMetric (DistC)

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

open SupercriticalLQGUniqueness.B2.Iface

theorem subseqLimit_comp_strictMono
    (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (D : DistC → LSCMetric)
    (hD : SubseqLimit ξ m ε D)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    SubseqLimit ξ m (ε ∘ φ) D := by
  intro Ω _ P _ h hh X hX
  obtain ⟨hLsc, hCirc⟩ := hD P h hh X hX
  constructor
  · filter_upwards [hLsc] with ω hω
    let G : ℕ → LSCFun := fun n => B2.LscTop.rescaledLFPPFun
      (ξ : ℝ) (m (ε n)) (X (ε n) ω)
    have hG : LSCTendsto (fun n => (G n).1) (D (h ω)).toLSCFun.1 := by
      simpa only [G, B2.LscTop.rescaledLFPPFun_val] using hω
    have hT : Tendsto G atTop (𝓝 (D (h ω)).toLSCFun) :=
      LSCFun.tendsto_of_lscTendsto hG
    have hComp : Tendsto (G ∘ φ) atTop (𝓝 (D (h ω)).toLSCFun) :=
      hT.comp hφ.tendsto_atTop
    have hGcomp := LSCFun.lscTendsto_of_tendsto hComp
    simpa only [G, Function.comp_apply, B2.LscTop.rescaledLFPPFun_val] using hGcomp
  · intro O O' hO hO'
    filter_upwards [hCirc O O' hO hO'] with ω hω
    simpa only [Function.comp_apply, Function.comp_def] using hω.comp hφ.tendsto_atTop

end SupercriticalLQGUniqueness.B2.PfeAxioms
