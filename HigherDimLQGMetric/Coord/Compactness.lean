import HigherDimLQGMetric.Coord.CurveLimit
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Arzelà–Ascoli for curves controlled by varying coordinates

The common lower modulus of MA1 A3 converts a uniform Lipschitz bound in the varying
coordinates into Euclidean equicontinuity on a compact set.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology BoundedContinuousFunction

namespace HigherDimLQGMetric

variable {X : Type*} [MetricSpace X] {a b : ℝ}

/-- The compactness assertion in MA1 Lemma CC.  Curves are bounded continuous functions on
the compact parameter interval; this avoids choosing extensions outside the interval. -/
theorem exists_curve_subseq_of_uniform_lower_modulus
    {L : Set X} (hL : IsCompact L) (ρ : ℕ → X → X → ℝ) (A : ℝ)
    (u : ℕ → Icc a b →ᵇ X)
    (huL : ∀ n t, u n t ∈ L)
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ n, ∀ x ∈ L, ∀ y ∈ L, ρ n x y < δ → dist x y < ε)
    (hspeed : ∀ n : ℕ, ∀ s t : Icc a b, ρ n (u n s) (u n t) ≤ A * dist s t) :
    ∃ f : Icc a b →ᵇ X, (∀ t, f t ∈ L) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoUniformly (fun n t => u (φ n) t) f atTop := by
  have hequi : Equicontinuous ((↑) : Set.range u → Icc a b → X) := by
    intro p
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    obtain ⟨δ, hδ, hδmod⟩ := hmod ε hε
    let τ : ℝ := δ / (|A| + 1)
    have hτ : 0 < τ := div_pos hδ (by positivity)
    filter_upwards [Metric.ball_mem_nhds p hτ] with q hq
    intro g
    obtain ⟨n, hn⟩ := g.property
    rw [← hn]
    have hqdist : dist q p < τ := by simpa [Metric.mem_ball] using hq
    have hρ : ρ n (u n p) (u n q) < δ := by
      calc
        ρ n (u n p) (u n q) ≤ A * dist p q := hspeed n p q
        _ ≤ |A| * dist p q := mul_le_mul_of_nonneg_right (le_abs_self A) dist_nonneg
        _ ≤ (|A| + 1) * dist p q := by
          gcongr
          linarith
        _ < (|A| + 1) * τ := by
          apply mul_lt_mul_of_pos_left
          · simpa [dist_comm] using hqdist
          · positivity
        _ = δ := by dsimp [τ]; field_simp
    exact hδmod n (u n p) (huL n p) (u n q) (huL n q) hρ
  have hin : ∀ (f : Icc a b →ᵇ X) (t : Icc a b), f ∈ range u → f t ∈ L := by
    rintro _ t ⟨n, rfl⟩
    exact huL n t
  have hcpt := arzela_ascoli L hL (range u) hin hequi
  obtain ⟨f, hf, φ, hφ, hlim⟩ := hcpt.tendsto_subseq (x := u)
    (fun n => subset_closure ⟨n, rfl⟩)
  refine ⟨f, ?_, φ, hφ, ?_⟩
  · intro t
    have hft : Tendsto (fun n => u (φ n) t) atTop (𝓝 (f t)) :=
      (tendsto_iff_tendstoUniformly.1 hlim).tendsto_at t
    exact hL.isClosed.mem_of_tendsto hft (Eventually.of_forall fun n => huL (φ n) t)
  · exact tendsto_iff_tendstoUniformly.1 hlim

/-- The coordinate Lipschitz bound passes to the limit selected by Arzelà–Ascoli. -/
theorem coordinate_speed_limit
    {L : Set X} (ρ : X × X → ℝ) (ρi : ℕ → X × X → ℝ)
    (hρ : ContinuousOn ρ (L ×ˢ L))
    (hρi : TendstoUniformlyOn ρi ρ atTop (L ×ˢ L))
    (A : ℝ) (u : ℕ → Icc a b →ᵇ X) (f : Icc a b →ᵇ X)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (huL : ∀ n t, u n t ∈ L) (hfL : ∀ t, f t ∈ L)
    (hlim : TendstoUniformly (fun n t => u (φ n) t) f atTop)
    (hspeed : ∀ n : ℕ, ∀ s t : Icc a b,
      ρi n (u n s, u n t) ≤ A * dist s t) :
    ∀ s t : Icc a b, ρ (f s, f t) ≤ A * dist s t := by
  intro s t
  have hs : Tendsto (fun n => u (φ n) s) atTop (𝓝 (f s)) := hlim.tendsto_at s
  have ht : Tendsto (fun n => u (φ n) t) atTop (𝓝 (f t)) := hlim.tendsto_at t
  have hpair : Tendsto (fun n => (u (φ n) s, u (φ n) t)) atTop (𝓝 (f s, f t)) :=
    hs.prodMk_nhds ht
  have hpairL : Tendsto (fun n => (u (φ n) s, u (φ n) t)) atTop
      (𝓝[L ×ˢ L] (f s, f t)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hpair, Eventually.of_forall fun n =>
      ⟨huL (φ n) s, huL (φ n) t⟩⟩
  have hcoord := hρi.seq_tendstoUniformlyOn φ hφ.tendsto_atTop
  have hdist : Tendsto (fun n => ρi (φ n) (u (φ n) s, u (φ n) t)) atTop
      (𝓝 (ρ (f s, f t))) :=
    hcoord.tendsto_comp (hρ (f s, f t) (⟨hfL s, hfL t⟩)) hpairL
  exact le_of_tendsto' hdist (fun n => hspeed (φ n) s t)

/-- The length assertion of MA1 Lemma CC on every subinterval.  `Set.IccExtend` is the
canonical extension of an interval curve, constant outside the interval. -/
theorem coordinate_curveLength_le_liminf
    {L : Set X} {ρ : X × X → ℝ} {ρi : ℕ → X × X → ℝ}
    (hab : a ≤ b) (hρ : ContinuousOn ρ (L ×ˢ L))
    (hρi : TendstoUniformlyOn ρi ρ atTop (L ×ˢ L))
    (u : ℕ → Icc a b →ᵇ X) (f : Icc a b →ᵇ X)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (huL : ∀ n t, u n t ∈ L) (hfL : ∀ t, f t ∈ L)
    (hlim : TendstoUniformly (fun n t => u (φ n) t) f atTop)
    {c d : ℝ} (hac : a ≤ c) (_hcd : c ≤ d) (hdb : d ≤ b) :
    curveLengthWith (fun x y => ENNReal.ofReal (ρ (x, y))) (Set.IccExtend hab f) c d ≤
      liminf (fun n => curveLengthWith
        (fun x y => ENNReal.ofReal (ρi (φ n) (x, y)))
        (Set.IccExtend hab (u (φ n))) c d) atTop := by
  have hρseq := hρi.seq_tendstoUniformlyOn φ hφ.tendsto_atTop
  apply curveLengthWith_le_liminf_of_uniform_coordinates hρ hρseq
  · intro t ht
    have ht' : t ∈ Icc a b := ⟨hac.trans ht.1, ht.2.trans hdb⟩
    simpa only [Set.IccExtend_of_mem (h := hab) _ ht'] using
      (hlim.tendsto_at (⟨t, ht'⟩ : Icc a b))
  · intro t ht
    have ht' : t ∈ Icc a b := ⟨hac.trans ht.1, ht.2.trans hdb⟩
    rw [Set.IccExtend_of_mem (h := hab) _ ht']
    exact hfL ⟨t, ht'⟩
  · intro n t ht
    have ht' : t ∈ Icc a b := ⟨hac.trans ht.1, ht.2.trans hdb⟩
    rw [Set.IccExtend_of_mem (h := hab) _ ht']
    exact huL (φ n) ⟨t, ht'⟩

/-- A continuous weight on the compact common image is uniformly continuous there, so
uniform convergence of curves gives uniform convergence of weights. -/
theorem coordinate_weight_tendstoUniformly
    {L : Set X} (hL : IsCompact L) (w : X → ℝ) (hw : ContinuousOn w L)
    (u : ℕ → Icc a b →ᵇ X) (f : Icc a b →ᵇ X)
    (φ : ℕ → ℕ) (huL : ∀ n t, u n t ∈ L) (hfL : ∀ t, f t ∈ L)
    (hlim : TendstoUniformly (fun n t => u (φ n) t) f atTop) :
    TendstoUniformly (fun n t => w (u (φ n) t)) (fun t => w (f t)) atTop := by
  have huc := hL.uniformContinuousOn_of_continuous hw
  rw [Metric.tendstoUniformly_iff] at hlim ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδw⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  filter_upwards [hlim δ hδ] with n hn
  intro t
  exact hδw (f t) (hfL t) (u (φ n) t) (huL (φ n) t) (hn t)

end HigherDimLQGMetric
