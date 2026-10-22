import HigherDimLQGMetric.Sec8.EventMeas
import HigherDimLQGMetric.Select.Internal

/-!
# A Borel version of Section 8 configurations

The internal distance has a Borel rational-chain formula on continuous length
metrics. `sec8ConfigBorel` uses that formula on every metric; it agrees with
`config` whenever the two metrics are length metrics. This keeps configuration
events Borel without imposing any behavior on an assignment outside its
almost-sure length-metric domain.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- The four annular coordinates with `chainInf` in place of the possibly
non-Borel internal path infimum off length metrics. -/
def sec8ConfigBorel (D Dt : ContMetric d) (s r : ℝ) (z : Rd d) : Config d :=
  (fun u v => ENNReal.ofReal s⁻¹ *
    D.chainInf (ann z (r / 2) (5 * r)) (r • u + z) (r • v + z),
   fun u v => ENNReal.ofReal s⁻¹ *
    Dt.chainInf (ann z (r / 2) (5 * r)) (r • u + z) (r • v + z),
   fun u v => ENNReal.ofReal s⁻¹ *
    D.chainInf (ann z (3 * r / 4) (7 * r / 2)) (r • u + z) (r • v + z),
   fun u v => ENNReal.ofReal s⁻¹ *
    Dt.chainInf (ann z (3 * r / 4) (7 * r / 2)) (r • u + z) (r • v + z))

theorem sec8ConfigBorel_eq_config {D Dt : ContMetric d}
    (hD : D.IsLength) (hDt : Dt.IsLength) (s r : ℝ) (z : Rd d) :
    sec8ConfigBorel D Dt s r z = config D Dt s r z := by
  unfold sec8ConfigBorel config
  apply Prod.ext
  · funext u v
    dsimp only
    rw [D.internal_eq_chainInf hD (isOpen_ann z _ _)]
  apply Prod.ext
  · funext u v
    dsimp only
    rw [Dt.internal_eq_chainInf hDt (isOpen_ann z _ _)]
  apply Prod.ext
  · funext u v
    dsimp only
    rw [D.internal_eq_chainInf hD (isOpen_ann z _ _)]
  · funext u v
    dsimp only
    rw [Dt.internal_eq_chainInf hDt (isOpen_ann z _ _)]

theorem measurable_sec8ConfigBorel
    {Ω : Type} [MeasurableSpace Ω] {D Dt : Ω → ContMetric d}
    (hD : Measurable D) (hDt : Measurable Dt)
    {s : Ω → ℝ} (hs : Measurable s) (r : ℝ) (z : Rd d) :
    Measurable fun ω => sec8ConfigBorel (D ω) (Dt ω) (s ω) r z := by
  have hchain (A : Ω → ContMetric d) (hA : Measurable A)
      (V : Set (Rd d)) (u v : Rd d) :
      Measurable fun ω => ENNReal.ofReal (s ω)⁻¹ *
        (A ω).chainInf V (r • u + z) (r • v + z) := by
    exact (ENNReal.measurable_ofReal.comp hs.inv).mul
      ((ContMetric.measurable_chainInf V).comp
        (hA.prodMk (measurable_const.prodMk measurable_const)))
  unfold sec8ConfigBorel
  exact (measurable_pi_iff.2 fun u => measurable_pi_iff.2 fun v =>
    hchain D hD (ann z (r / 2) (5 * r)) u v).prodMk
    ((measurable_pi_iff.2 fun u => measurable_pi_iff.2 fun v =>
      hchain Dt hDt (ann z (r / 2) (5 * r)) u v).prodMk
    ((measurable_pi_iff.2 fun u => measurable_pi_iff.2 fun v =>
      hchain D hD (ann z (3 * r / 4) (7 * r / 2)) u v).prodMk
    (measurable_pi_iff.2 fun u => measurable_pi_iff.2 fun v =>
      hchain Dt hDt (ann z (3 * r / 4) (7 * r / 2)) u v)))

/-- The Borel version of (C2). It has exactly the same meaning on length
metrics, the almost-sure domain of the sharp weak assignments. -/
def sec8C2Borel (D Dt : DistRd d → ContMetric d) (ξ Q q R r : ℝ)
    (J : ℕ) (N : ℕ → Set (Config d)) (Z : Finset (Rd d × ℕ))
    (g : DistRd d) : Prop :=
  ∀ site ∈ Z, site.2 < J ∧
    sec8ConfigBorel (D g) (Dt g) (sNorm ξ Q g r site.1) r site.1 ∈ N site.2 ∧
    q * macroS ξ Q g R ≤ sNorm ξ Q g r site.1 ∧
    sNorm ξ Q g r site.1 ≤ 2 * q * macroS ξ Q g R

theorem sec8C2Borel_iff {D Dt : DistRd d → ContMetric d}
    (g : DistRd d) (hD : (D g).IsLength) (hDt : (Dt g).IsLength)
    (ξ Q q R r : ℝ) (J : ℕ) (N : ℕ → Set (Config d))
    (Z : Finset (Rd d × ℕ)) :
    sec8C2Borel D Dt ξ Q q R r J N Z g ↔
      sec8C2 D Dt ξ Q q R r J N Z g := by
  unfold sec8C2Borel sec8C2
  simp only [sec8ConfigBorel_eq_config hD hDt]

theorem measurableSet_sec8C2Borel {D Dt : DistRd d → ContMetric d}
    (hD : Measurable D) (hDt : Measurable Dt)
    (ξ Q q R r : ℝ) (J : ℕ) (N : ℕ → Set (Config d))
    (hN : ∀ j < J, MeasurableSet (N j)) (Z : Finset (Rd d × ℕ)) :
    MeasurableSet {g : DistRd d | sec8C2Borel D Dt ξ Q q R r J N Z g} := by
  have hmacro : Measurable fun g : DistRd d => macroS ξ Q g R := by
    exact measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul (measurable_sphereAvg_left (8 * R) 0)))
  have hsite (site : Rd d × ℕ) :
      MeasurableSet {g : DistRd d | site.2 < J ∧
        sec8ConfigBorel (D g) (Dt g) (sNorm ξ Q g r site.1) r site.1 ∈ N site.2 ∧
        q * macroS ξ Q g R ≤ sNorm ξ Q g r site.1 ∧
        sNorm ξ Q g r site.1 ≤ 2 * q * macroS ξ Q g R} := by
    by_cases hj : site.2 < J
    · have hs : Measurable fun g : DistRd d => sNorm ξ Q g r site.1 :=
        measurable_const.mul (Real.measurable_exp.comp
          (measurable_const.mul (measurable_sphereAvg_left r site.1)))
      have hcfg := measurable_sec8ConfigBorel hD hDt hs r site.1
      have hcfgSet : MeasurableSet {g : DistRd d |
          sec8ConfigBorel (D g) (Dt g) (sNorm ξ Q g r site.1) r site.1 ∈ N site.2} := by
        change MeasurableSet ((fun g => sec8ConfigBorel (D g) (Dt g)
          (sNorm ξ Q g r site.1) r site.1) ⁻¹' N site.2)
        exact hcfg (hN site.2 hj)
      simpa only [hj, true_and, Set.ofPred_and, Pi.mul_apply] using
        (hcfgSet.inter
          ((measurableSet_le (measurable_const.mul hmacro) hs).inter
            (measurableSet_le hs (measurable_const.mul hmacro))))
    · simp only [hj, false_and, Set.ofPred_false, MeasurableSet.empty]
  have heq : {g : DistRd d | sec8C2Borel D Dt ξ Q q R r J N Z g} =
      ⋂ site : {site : Rd d × ℕ // site ∈ Z},
        {g | site.1.2 < J ∧
          sec8ConfigBorel (D g) (Dt g) (sNorm ξ Q g r site.1.1) r site.1.1 ∈ N site.1.2 ∧
          q * macroS ξ Q g R ≤ sNorm ξ Q g r site.1.1 ∧
          sNorm ξ Q g r site.1.1 ≤ 2 * q * macroS ξ Q g R} := by
    ext g
    simp only [sec8C2Borel, mem_ofPred_eq, mem_iInter]
    constructor
    · intro hg site
      exact hg site.1 site.2
    · intro hg site hmem
      exact hg ⟨site, hmem⟩
  rw [heq]
  exact MeasurableSet.iInter fun site => hsite site.1

end HigherDimLQGMetric
