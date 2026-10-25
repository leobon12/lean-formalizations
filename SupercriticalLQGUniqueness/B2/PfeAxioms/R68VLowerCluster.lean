import SupercriticalLQGUniqueness.B2.PfeAxioms.R68VScaledConvergence
import SupercriticalLQGUniqueness.B2.PfeAxioms.UniformLimsupLower

 






set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set LQGMetric LQGMetric.DFGPS
open scoped ENNReal
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

theorem r68v_scaled_across_lower_tail_cluster_of_coupling
    (hPerc : DG20PercEstimate')
    {ξ : Ioi (0 : ℝ)} {Q : ℝ} {m : Ioi (0 : ℝ) → Ioi (0 : ℝ)}
    {e : ℕ → Ioi (0 : ℝ)} {c : Ioi (0 : ℝ) → Ioi (0 : ℝ)}
    {V : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {h' : Ω' → DistC} {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}
    (hB : Final.DG20CouplingData ξ Q m e c V P' h' hN L)
    (hSA : Final.CoupledSmallAnnuli ξ m e V P' hN L)
    (A : EuclideanAnnulus) (η : ℝ) (hη : 0 < η) :
    ∃ M : ℝ, 0 < M ∧
      ∀ (r c' : Ioi (0 : ℝ)) (ψ : ℕ → ℕ), StrictMono ψ →
        Tendsto (fun n => (r : ℝ) *
          (m ⟨(e (ψ n) : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (e (ψ n)).property r.property)⟩ : ℝ) /
          (m (e (ψ n)) : ℝ)) atTop (𝓝 (c' : ℝ)) →
        P' {ω | acrossDist (B2.LscTop.smulMetric
          ⟨(c' : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h' ω) r 0),
            Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr c'.property) (Real.exp_pos _))⟩
          (B2.LscTop.dilate r (L ω))) A < ENNReal.ofReal M⁻¹} ≤
          ENNReal.ofReal η := by
  obtain ⟨T, ε₀, hT, hε₀, hTail⟩ :=
    r68v_finite_scaled_crossing_lower_tail hPerc hB A η hη
  refine ⟨2 * T, by positivity, ?_⟩
  intro r c' ψ hψ hc
  obtain ⟨χ, hχ, hCircle⟩ := exists_subseq_ae_coupled_circleAvg
    (hB.comp hψ) 0 r
  have hχψ : StrictMono (ψ ∘ χ) := hψ.comp hχ
  have hcχ : Tendsto (fun n => (r : ℝ) *
      (m ⟨(e ((ψ ∘ χ) n) : ℝ) / (r : ℝ),
        Set.mem_Ioi.mpr (div_pos (e ((ψ ∘ χ) n)).property r.property)⟩ : ℝ) /
      (m (e ((ψ ∘ χ) n)) : ℝ)) atTop (𝓝 (c' : ℝ)) :=
    hc.comp hχ.tendsto_atTop
  have hConv := r68v_ae_scaled_crossing_tendsto hB hSA A r c'
    (ψ ∘ χ) hχψ hcχ hCircle
  have hδ0 : Tendsto (fun n => (e ((ψ ∘ χ) n) : ℝ) / (r : ℝ))
      atTop (𝓝 0) := by
    simpa using (hB.scale_tendsto.comp hχψ.tendsto_atTop).div_const (r : ℝ)
  obtain ⟨N, hNevent⟩ := Filter.eventually_atTop.1
    (hδ0.eventually (Iio_mem_nhds
      (show (0 : ℝ) < min ε₀ 1 from lt_min hε₀ (by norm_num))))
  let F (n : ℕ) (ω : Ω') : ℝ≥0∞ :=
    acrossDist (r68vScaledFiniteMetric ξ m (e ((ψ ∘ χ) (n + N))) r V
      (hN ((ψ ∘ χ) (n + N)) ω)) A
  let Z (ω : Ω') : ℝ≥0∞ := acrossDist (B2.LscTop.smulMetric
      ⟨(c' : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h' ω) r 0),
        Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr c'.property) (Real.exp_pos _))⟩
      (B2.LscTop.dilate r (L ω))) A
  have hFin : ∀ n, P' {ω | F n ω < ENNReal.ofReal T⁻¹} ≤
      ENNReal.ofReal η := by
    intro n
    have he : (e ((ψ ∘ χ) (n + N)) : ℝ) / (r : ℝ) < min ε₀ 1 :=
      hNevent (n + N) (by omega)
    simpa only [F, Function.comp_apply] using
      hTail ((ψ ∘ χ) (n + N)) r he
  have hLim : ∀ᵐ ω ∂P', limsup (fun n => F n ω) atTop ≤ Z ω := by
    filter_upwards [hConv] with ω hω
    have hmono : StrictMono (fun n : ℕ => n + N) :=
      strictMono_nat_of_lt_succ (fun n => by omega)
    have hs := (hω.comp hmono.tendsto_atTop).limsup_eq
    simpa only [F, Z, Function.comp_apply, Function.comp_def] using hs.le
  have hRes := uniform_lower_tail_of_ae_limsup_le P'
    (fun (_ : Unit) n ω => F n ω) (fun (_ : Unit) ω => Z ω)
    T⁻¹ η (inv_pos.mpr hT) (fun _ n => hFin n) (fun _ => hLim) ()
  have heq : T⁻¹ / 2 = (2 * T)⁻¹ := by field_simp
  simpa only [heq, Z] using hRes

end SupercriticalLQGUniqueness.B2.PfeAxioms
