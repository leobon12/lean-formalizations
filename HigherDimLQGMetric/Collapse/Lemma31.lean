import HigherDimLQGMetric.Collapse.Upper

/-! # Collapse of weighted distances to the internal graph distance -/

set_option autoImplicit false

open Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

variable {X : Type*} [MetricSpace X]

/-- [S] Lemma 3.1′, claim (a), with the exact statement of MA1's probe. -/
theorem lemma31_collapse (Y K : Set X) (hY : IsCompact Y) (hK : IsCompact K) (hKY : K ⊆ Y)
    (hKfin : ∀ x ∈ K, ∀ y ∈ K, internalEDist K x y ≠ ⊤)
    (hKcont : ContinuousOn (fun p : X × X => internalEDist K p.1 p.2) (K ×ˢ K))
    (δ : ℝ) (hδ : 0 < δ)
    (hreal : ∀ x ∈ Y, ∀ y ∈ K, dist x y < δ → ∃ P : ℝ → X, ContinuousOn P (Icc 0 1) ∧
      P 0 = x ∧ P 1 = y ∧ MapsTo P (Icc 0 1) Y ∧ curveLength P 0 1 = edist x y)
    (lam eta : ℕ → ℝ) (hlam0 : ∀ n, 0 < lam n) (hlam : Tendsto lam atTop (𝓝 0))
    (heta0 : ∀ n, 0 < eta n) (heta : Tendsto (fun n => eta n / lam n) atTop (𝓝 0))
    (a₀ : ℝ) (ha₀ : 0 < a₀) (w : ℕ → X → ℝ) (hw : ∀ n, Continuous (w n))
    (hw1 : ∀ n x, lam n ≤ w n x ∧ w n x ≤ 1) (hwK : ∀ n, ∀ x ∈ K, w n x = lam n)
    (hwoff : ∀ n x, eta n ≤ Metric.infDist x K → a₀ ≤ w n x)
    (x y u v : ℕ → X) (uLim vLim : X)
    (hx : ∀ n, x n ∈ Y) (hy : ∀ n, y n ∈ Y) (hu : ∀ n, u n ∈ K) (hv : ∀ n, v n ∈ K)
    (hxu : ∀ n, dist (x n) (u n) ≤ eta n) (hyv : ∀ n, dist (y n) (v n) ≤ eta n)
    (huLim : Tendsto u atTop (𝓝 uLim)) (hvLim : Tendsto v atTop (𝓝 vLim)) :
    Tendsto (fun n => (ENNReal.ofReal (lam n))⁻¹ * weylDistOn (w n) Y (x n) (y n)) atTop
      (𝓝 (internalEDist K uLim vLim)) := by
  have _ := hw
  have hKclosed : IsClosed K := hK.isClosed
  have hKne : K.Nonempty := ⟨u 0, hu 0⟩
  have huK : uLim ∈ K :=
    hKclosed.mem_of_tendsto huLim (Eventually.of_forall hu)
  have hvK : vLim ∈ K :=
    hKclosed.mem_of_tendsto hvLim (Eventually.of_forall hv)
  have hdfin : internalEDist K uLim vLim ≠ ⊤ := hKfin uLim huK vLim hvK
  have hdk : Tendsto (fun n => internalEDist K (u n) (v n)) atTop
      (𝓝 (internalEDist K uLim vLim)) := by
    have hp : Tendsto (fun n => (u n, v n)) atTop
        (nhdsWithin (uLim, vLim) (K ×ˢ K)) :=
      tendsto_nhdsWithin_iff.mpr ⟨huLim.prodMk_nhds hvLim,
        Eventually.of_forall fun n => ⟨hu n, hv n⟩⟩
    exact (hKcont.continuousWithinAt ⟨huK, hvK⟩).tendsto.comp hp
  have hetaLim : Tendsto eta atTop (𝓝 0) := by
    have hp : Tendsto (fun n => eta n / lam n * lam n) atTop (𝓝 0) := by
      simpa using heta.mul hlam
    have heq : (fun n => eta n / lam n * lam n) = eta := by
      funext n
      exact div_mul_cancel₀ _ (ne_of_gt (hlam0 n))
    simpa only [heq] using hp
  have hxLim : Tendsto x atTop (𝓝 uLim) := by
    have hd : Tendsto (fun n => dist (u n) (x n)) atTop (𝓝 0) := by
      apply squeeze_zero (fun n => dist_nonneg) (fun n => by simpa [dist_comm] using hxu n)
      exact hetaLim
    exact huLim.congr_dist hd
  have hyLim : Tendsto y atTop (𝓝 vLim) := by
    have hd : Tendsto (fun n => dist (v n) (y n)) atTop (𝓝 0) := by
      apply squeeze_zero (fun n => dist_nonneg) (fun n => by simpa [dist_comm] using hyv n)
      exact hetaLim
    exact hvLim.congr_dist hd
  let R : ℕ → ℝ≥0∞ := fun n =>
    (ENNReal.ofReal (lam n))⁻¹ * weylDistOn (w n) Y (x n) (y n)
  let U : ℕ → ℝ := fun n =>
    eta n / lam n + (internalEDist K (u n) (v n)).toReal + eta n / lam n
  have hηδ : ∀ᶠ n in atTop, eta n < δ :=
    hetaLim.eventually (eventually_lt_nhds hδ)
  have hrec : ∀ᶠ n in atTop,
      weylDistOn (w n) Y (x n) (y n) ≤
        ENNReal.ofReal (eta n) +
          ENNReal.ofReal (lam n) * internalEDist K (u n) (v n) +
          ENNReal.ofReal (eta n) := by
    filter_upwards [hηδ] with n hn
    exact collapse_recovery_bound hKY hreal (fun z => (hw1 n z).2) (hlam0 n)
      (hwK n) (hx n) (hy n) (hu n) (hv n) (hxu n) (hyv n) hn
  have hfinR : ∀ᶠ n in atTop, R n ≠ ⊤ := by
    filter_upwards [hrec] with n hn
    have hd : internalEDist K (u n) (v n) ≠ ⊤ := hKfin _ (hu n) _ (hv n)
    have hterm : ENNReal.ofReal (lam n) * internalEDist K (u n) (v n) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hd
    have hsum : ENNReal.ofReal (eta n) +
        ENNReal.ofReal (lam n) * internalEDist K (u n) (v n) +
        ENNReal.ofReal (eta n) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
        ⟨ENNReal.ofReal_ne_top, hterm⟩, ENNReal.ofReal_ne_top⟩
    have hWfin := ne_top_of_le_ne_top hsum hn
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr
      (ne_of_gt (ENNReal.ofReal_pos.mpr (hlam0 n)))) hWfin
  have hU : Tendsto U atTop (𝓝 (internalEDist K uLim vLim).toReal) := by
    have hd : Tendsto (fun n => (internalEDist K (u n) (v n)).toReal) atTop
        (𝓝 (internalEDist K uLim vLim).toReal) :=
      (ENNReal.tendsto_toReal hdfin).comp hdk
    simpa [U] using (heta.add hd).add heta
  have hupper : ∀ᶠ n in atTop, (R n).toReal ≤ U n := by
    filter_upwards [hrec] with n hn
    exact normalized_recovery_real_le (hlam0 n) (heta0 n).le
      (hKfin _ (hu n) _ (hv n)) hn
  have hlower : ∀ C : ℝ, 0 ≤ C → C < (internalEDist K uLim vLim).toReal →
      ∀ᶠ n in atTop, ENNReal.ofReal C ≤ R n := by
    intro C hC hCd
    let B := (C + (internalEDist K uLim vLim).toReal) / 2
    have hB0 : 0 ≤ B := by dsimp [B]; linarith [ENNReal.toReal_nonneg (a := internalEDist K uLim vLim)]
    have hCB : C < B := by dsimp [B]; linarith
    have hBd : B < (internalEDist K uLim vLim).toReal := by dsimp [B]; linarith
    have hBd' : ENNReal.ofReal B < internalEDist K uLim vLim :=
      (ENNReal.ofReal_lt_iff_lt_toReal hB0 hdfin).2 hBd
    exact collapse_eventually_lower hY hKclosed hKne hlam0 hlam hetaLim ha₀
      (fun n z => (hw1 n z).1) hwoff
      (fun n => (Metric.infDist_le_dist_of_mem (hu n)).trans (hxu n))
      hxLim hyLim hC hCB hBd'
  exact tendsto_ennreal_of_real_bounds hdfin hfinR hU hupper hlower

end HigherDimLQGMetric
