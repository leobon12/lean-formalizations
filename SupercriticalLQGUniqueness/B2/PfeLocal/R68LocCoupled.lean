import SupercriticalLQGUniqueness.B2.PfeLocal.R68LocUpper
import SupercriticalLQGUniqueness.B2.PfeLocal.L6Iface
import SupercriticalLQGUniqueness.B2.PfeWeyl.W3WeylMetric
import SupercriticalLQGUniqueness.B2.PfeWeyl.W3Stochastic
import SupercriticalLQGUniqueness.B2.PfeAxioms.AnnulusWeylTransfer

 

















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal
open LQGMetric (DistC normGFFLaw heatMollify)

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open Uniqueness.Toolkit.CompactPathInfimum

 
def r68Wt (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)) (ε : Set.Ioi (0 : ℝ)) (F : C(ℂ, ℝ)) (M : ℝ)
    (hM : ∀ z, |F z| ≤ M) (g : DistC) : C(ℂ, ℝ) :=
  V ε g + LQGMetric.LFPP.mollCont (ε : ℝ) ε.property.ne' F M hM

 
theorem r68_mollCont_tendsto {e : ℕ → Set.Ioi (0 : ℝ)}
    (he : Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0)) (F : C(ℂ, ℝ)) {M : ℝ}
    (hM : ∀ z, |F z| ≤ M) :
    ∀ K : Set ℂ, IsCompact K → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ K,
      |LQGMetric.LFPP.mollCont (e n : ℝ) (e n).property.ne' F M hM x - F x| < ε := by
  intro K hK ε hε
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hR1 : 0 < |R| + 1 := by positivity
  have hconv := LQGMetric.DFGPS.tendstoUniformlyOn_heatMollify_seq (εn := fun n => (e n : ℝ))
    (fun n => (e n).property.ne') he (fn := fun _ => F) (f := F) (fun _ => hM) hM
    (fun R' _ => Metric.tendstoUniformlyOn_iff.2 fun η hη =>
      Eventually.of_forall fun n x _ => by simpa using hη) hR1
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hconv ε hε] with n hn x hx
  have hx' : x ∈ closedBall (0 : ℂ) (|R| + 1) := by
    have := hR hx
    rw [mem_closedBall, dist_zero_right] at this ⊢
    linarith [le_abs_self R]
  have := hn x hx'
  rw [Real.dist_eq, abs_sub_comm] at this
  exact this

 
theorem r68_coupled_weyl_limsup {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)} {e : ℕ → Set.Ioi (0 : ℝ)}
    {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)} {V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} {h' : Ω' → DistC}
    {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}
    (hB : Final.DG20CouplingData ξ Q m e c V P' h' hN L)
    (hSA : Final.CoupledSmallAnnuli ξ m e V P' hN L) (hAT : Final.CoupledAcrossTails P' L)
    (F : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ z, |F z| ≤ M) :
    ∀ᵐ ω ∂P', ∃ E : LSCMetric, (∀ p, E p = weylScale (ξ : ℝ) F (L ω) p) ∧
      ∀ (K : Set ℂ), IsCompact K → ∀ (b₁ b₂ : ℚ × ℚ × ℚ) (η : ℝ), 0 < η →
        limsup (fun n => r68Y (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e n))
          (r68Wt V (e n) F M hM (hN n ω))) K b₁ b₂ η) atTop ≤ r68Z E K b₁ b₂ := by
  have hξ0 : (0 : ℝ) ≤ ξ := ξ.property.le
  have hacr := PfeWeyl.ae_acrossUnbounded_of_acrossTail P' L hAT
  have hsm : ∀ᵐ ω ∂P', ∀ k : ℕ, PfeWeyl.SmallAnnulusCosts
      (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e n)) (V (e n) (hN n ω)))
      (L ω) (closedBall 0 k) (ball 0 ((k : ℝ) + 1)) := ae_all_iff.2 hSA
  filter_upwards [hB.metric_tendsto, hB.geometry, hacr, hsm] with ω hG hgeo hacrω hsmω
  have hLforget : Continuous (PfeWeyl.euclidForget (L ω)) :=
    continuous_euclidForget_of_small_metric _ hgeo.2.1
  obtain ⟨E, hE, hWE⟩ := PfeWeyl.weyl_tendsto_lscMetric hG
    (fun _ => PfeWeyl.isLengthSpace_normalizedLFPPMetric _ _ _)
    (fun _ => PfeAxioms.continuous_euclidForget_normalizedLFPPMetric _ _ _) (ξ : ℝ) hξ0 F
    (fun n => LQGMetric.LFPP.mollCont (e n : ℝ) (e n).property.ne' F M hM)
    (r68_mollCont_tendsto hB.scale_tendsto F hM) M hM
    (fun n z => PfeWeyl.abs_mollCont_le _ F M hM z) hgeo.1 hLforget hacrω
    (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e n)) (r68Wt V (e n) F M hM (hN n ω)))
    (fun n x y => PfeWeyl.normalizedLFPPMetric_add_eq_weylScale _ _ _ _ (x, y))
    (fun _ => PfeAxioms.continuous_euclidForget_normalizedLFPPMetric _ _ _) hsmω
  have hsmallW : ∀ k : ℕ, PfeWeyl.SmallAnnulusCosts
      (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e n)) (r68Wt V (e n) F M hM (hN n ω)))
      E (closedBall 0 k) (ball 0 ((k : ℝ) + 1)) := fun k =>
    PfeAxioms.smallAnnulusCosts_of_bounded_weyl (ξ : ℝ) hξ0 _ _ (L ω) E F
      (fun n => LQGMetric.LFPP.mollCont (e n : ℝ) (e n).property.ne' F M hM) hLforget hE
      (fun n p => PfeWeyl.normalizedLFPPMetric_add_eq_weylScale _ _ _ _ p) M
      (fun z => (abs_le.1 (hM z)).1)
      (fun n z _ => (abs_le.1 (PfeWeyl.abs_mollCont_le _ F M hM z)).2) (hsmω k)
  refine ⟨E, hE, fun K hK b₁ b₂ η hη => ?_⟩
  exact l6_limsup_le hWE (fun _ => PfeWeyl.isLengthSpace_normalizedLFPPMetric _ _ _)
    (fun _ => PfeAxioms.finitePathsEuclideanContinuous_normalizedLFPPMetric _ _ _)
    (fun _ => PfeAxioms.continuous_euclidForget_normalizedLFPPMetric _ _ _) hsmallW hK hη
    (thickening_subset_cthickening _ _) (thickening_subset_cthickening _ _)
    (thickening_subset_cthickening _ _)

end SupercriticalLQGUniqueness.B2.PfeLocal
