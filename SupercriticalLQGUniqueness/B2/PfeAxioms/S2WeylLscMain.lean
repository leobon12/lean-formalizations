import SupercriticalLQGUniqueness.B2.PfeAxioms.S2WeylLsc

 





set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 


theorem lowerSemicontinuous_weylScale
    (D : LSCMetric) (hlen : D.IsLengthSpace)
    (hforget : Continuous (PfeWeyl.euclidForget D))
    (hacross : PfeWeyl.AcrossUnbounded D) (hSSA : SelfSmallAnnuli D univ)
    (ξ : ℝ) (hξ : 0 ≤ ξ) (f : C(ℂ, ℝ)) :
    LowerSemicontinuous (fun p : ℂ × ℂ => weylScale ξ f D p) := by
  have hmet := Uniqueness.Toolkit.WeylLength.weylScale_isExtMetric D ξ f hforget
  have hsymm : ∀ a b : ℂ, weylScale ξ f D (a, b) = weylScale ξ f D (b, a) :=
    fun a b => hmet.2.2.1 a b
  rw [lowerSemicontinuous_iff_seq]
  rintro u ⟨x, y⟩ hu
  by_cases hxy : x = y
  · subst hxy
    have h0 : weylScale ξ f D (x, x) = 0 := hmet.1 x
    rw [h0]; exact zero_le
  have hd : 0 < dist x y := dist_pos.2 hxy
  set r : ℝ := dist x y / 4 with hrdef
  have hr : 0 < r := by positivity
  set Lm : ℝ≥0∞ := liminf (fun n => weylScale ξ f D (u n)) atTop
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hLm
  have hε4 : (0 : ℝ) < ε / 4 := by positivity
  set T : ℝ≥0∞ := Lm + ENNReal.ofReal (ε / 2)
  have hTtop : T ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hLm.ne, ENNReal.ofReal_ne_top⟩
  have hLT : Lm < T := ENNReal.lt_add_right hLm.ne (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hfreq : ∃ᶠ n in atTop, weylScale ξ f D (u n) < T := frequently_lt_of_liminf_lt (by isBoundedDefault) hLT
  have hu1 : Tendsto (fun n => (u n).1) atTop (𝓝 x) := (continuous_fst.tendsto _).comp hu
  have hu2 : Tendsto (fun n => (u n).2) atTop (𝓝 y) := (continuous_snd.tendsto _).comp hu
  have hev1 : ∀ᶠ n in atTop, (u n).1 ∈ Metric.ball x (r / 2) :=
    hu1 (Metric.ball_mem_nhds x (by positivity))
  have hev2 : ∀ᶠ n in atTop, 2 * r ≤ dist (u n).2 x := by
    filter_upwards [hu2 (Metric.ball_mem_nhds y (by positivity : (0 : ℝ) < r))] with n hn
    have h1 := dist_triangle x (u n).2 y
    have hn' : dist (u n).2 y < r := hn
    rw [dist_comm (u n).2 x]
    linarith
  obtain ⟨φ, hφ, hP⟩ := extraction_of_frequently_atTop
    (hfreq.and_eventually (hev1.and hev2))
  have hstep1 := weylScale_one_end_join D hlen hforget hacross hSSA ξ hξ f
    (xs := fun k => (u (φ k)).1) (ys := fun k => (u (φ k)).2)
    (hu1.comp hφ.tendsto_atTop) hr (fun k => (hP k).2.1) (fun k => (hP k).2.2)
    hTtop (fun k => (hP k).1) hε4
  
  have hys : Tendsto (fun k => (u (φ k)).2) atTop (𝓝 y) := hu2.comp hφ.tendsto_atTop
  have hev3 : ∀ᶠ k in atTop, (u (φ k)).2 ∈ Metric.ball y (r / 2) :=
    hys (Metric.ball_mem_nhds y (by positivity))
  obtain ⟨ψ, hψ, hQ⟩ := extraction_of_frequently_atTop (hstep1.and_eventually hev3)
  have hT2 : T + ENNReal.ofReal (ε / 4) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hTtop, ENNReal.ofReal_ne_top⟩
  have hxfar : 2 * r ≤ dist x y := by rw [hrdef]; linarith
  have hstep2 := weylScale_one_end_join D hlen hforget hacross hSSA ξ hξ f
    (x := y) (xs := fun j => (u (φ (ψ j))).2) (ys := fun _ => x)
    (hys.comp hψ.tendsto_atTop) hr (fun j => (hQ j).2) (fun _ => hxfar) hT2
    (fun j => by rw [hsymm]; exact (hQ j).1) hε4
  obtain ⟨j, hj⟩ := hstep2.exists
  rw [hsymm] at hj
  have hsum : T + ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) = Lm + ENNReal.ofReal ε := by
    rw [add_assoc, add_assoc, ← ENNReal.ofReal_add hε4.le hε4.le,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 2
    ring
  simpa only [ENNReal.ofReal_coe_nnreal] using (hj.trans_eq hsum).le

end SupercriticalLQGUniqueness.B2.PfeAxioms
