import GaussianLQG.Assembly.MainCoord
import GaussianLQG.Assembly.Instance
import GaussianLQG.Core.MainDefs
import GaussianLQG.LQG.Bridge.Defs

/-!
# The main theorem from the interface propositions (blueprint Theorem `thm:main`)

`main_theorem_of_interfaces` is the statement of the draft main theorem
(`planning/main-theorem-draft.lean.txt`; source Theorem 1.1, blueprint Theorem `thm:main`), with
the same binders and conclusions and the definitions of `Core/MainDefs.lean` and
`LQG/Bridge/Defs.lean`, plus one extra hypothesis `hI`: every `Setup` satisfies the four interface
propositions of `Core/Interfaces.lean` (Proposition `prop:crossing`, Corollary `cor:fixed-pair`,
Lemma `lem:law-M`, and `H(0,0) ~ N(0, 3/2)`), which other packets prove.

Proof (blueprint §1.3, the paragraph after Proposition `prop:realization`, and §7):

* `exists_setup` builds a `Setup` `S` on `(ℝ^ℕ, stdP)` from the canonical metrics and the input
  (S6), driven by a normalized whole-plane GFF `h₀`, with `D^γ = D^γ_{h₀}` for `γ ∈ (0,2)`, and
  with `H(0,0)`, `M`, `q` equal (a.s., resp. exactly) to `segPairing h₀ 0 0`, `diagMin h₀`,
  `qConst`;
* `Setup.main_coord` gives the conclusions for `S` (Steps 1–6), and `S.LawM` gives Step 5;
* every quantity is a measurable functional of the field and the law of the normalized field is
  unique, so laws, medians and convergence in probability transfer from `h₀` to the given field `h`
  (`map_comp_eq_of_isNormalizedWPGFF`, `isMedian_map_comp_iff`, `tendstoInMeasure_comp_iff`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

/-- **Main theorem** (source Theorem 1.1, blueprint Theorem `thm:main`), relative to the input
(S6) (source Lemma 2.1) and to the interface propositions `hI` (proved by other packets for every
`Setup`). -/
theorem main_theorem_of_interfaces (D : ℝ → LQGMetric.DistC → LQGMetric.ContMetric)
    (hD : ∀ γ, 0 < γ → γ < 2 → IsCanonicalLQGMetric γ (D γ))
    (hS6 : UniformMomentInput D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → LQGMetric.DistC) (hh : LQGMetric.IsNormalizedWPGFF h P)
    (hI : ∀ S : Setup, S.CrossingConv ∧ S.FixedPairConv ∧ S.LawM ∧ S.H00Law) :
    -- `q` is the unique median of `M`, and `q < 0`
    (LQGMetric.IsMedian (P.map fun ω => diagMin (h ω)) qConst ∧
      ∀ m, LQGMetric.IsMedian (P.map fun ω => diagMin (h ω)) m → m = qConst) ∧
    qConst < 0 ∧
    -- (1.7): convergence in probability
    TendstoInMeasure P (fun γ ω => ((D γ (h ω)).1 (0, 1) - 1) / γ) (𝓝[>] 0)
      (fun ω => (segPairing (h ω) 0 0 - qConst) / 2) ∧
    -- the limit has law `N(-q/2, 3/8)`
    P.map (fun ω => (segPairing (h ω) 0 0 - qConst) / 2) =
      gaussianReal (-qConst / 2) (3 / 8 : NNReal) ∧
    -- (1.8): convergence in law to `N(-q/2, 3/8)` (indexed by `γ ∈ (0,2)`)
    TendstoInDistribution (fun (γ : Ioo (0 : ℝ) 2) ω => ((D γ (h ω)).1 (0, 1) - 1) / (γ : ℝ))
      ((𝓝[>] (0 : ℝ)).comap Subtype.val) (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal (-qConst / 2) (3 / 8 : NNReal)) ∧
    -- (1.9) for every choice of medians `m_γ` of `D^γ(0,1)`
    ∀ m : ℝ → ℝ, (∀ γ, 0 < γ → γ < 2 →
        LQGMetric.IsMedian (P.map fun ω => (D γ (h ω)).1 (0, 1)) (m γ)) →
      Tendsto (fun γ => (m γ - (1 - qConst / 2 * γ)) / γ) (𝓝[>] 0) (𝓝 0) := by
  -- the coordinate setup and its conclusions
  obtain ⟨S, h₀, -, hh₀, hSD, hSH, hSM, hSq⟩ := exists_setup D hD hS6
  obtain ⟨hcross, hfix, hlawM, hH⟩ := hI S
  obtain ⟨c1, c2, -, c4⟩ := S.main_coord hcross hfix hlawM hH
  have hev : ∀ᶠ γ in 𝓝[>] (0 : ℝ), γ ∈ Ioo (0 : ℝ) 2 :=
    Ioo_mem_nhdsGT (show (0 : ℝ) < 2 by norm_num)
  have hDm : ∀ γ ∈ Ioo (0 : ℝ) 2, Measurable fun g => (D γ g).1 (0, 1) := fun γ hγ =>
    measurable_canonical_dist_zero_one hD hγ.1 hγ.2
  have hGm : Measurable fun g : LQGMetric.DistC => (segPairing g 0 0 - qConst) / 2 :=
    ((measurable_segPairing 0 0).sub_const _).div_const _
  have hH00 : S.H 0 0 =ᵐ[stdP] fun ω => segPairing (h₀ ω) 0 0 :=
    hSH 0 ⟨le_rfl, zero_le_one⟩ 0 ⟨le_rfl, zero_le_one⟩
  -- Step 5: the law of `M` is the same for `h₀` and `h`
  have hlawMP : stdP.map S.M = P.map fun ω => diagMin (h ω) := by
    rw [Measure.map_congr hSM]
    exact map_comp_eq_of_isNormalizedWPGFF measurable_diagMin hh₀ hh
  -- (1.7) for the field `h₀`, then for `h`
  have c1' : TendstoInMeasure stdP (fun γ ω => ((D γ (h₀ ω)).1 (0, 1) - 1) / γ) (𝓝[>] 0)
      (fun ω => (segPairing (h₀ ω) 0 0 - qConst) / 2) := by
    refine TendstoInMeasure.congr' ?_ ?_ c1
    · filter_upwards [hev] with γ hγ
      exact ae_of_all _ fun ω =>
        congrArg (fun d : LQGMetric.ContMetric => (d.1 (0, 1) - 1) / γ) ((hSD γ hγ).2 ω)
    · filter_upwards [hH00] with ω hω
      rw [hω, hSq]
  have hP1 : TendstoInMeasure P (fun γ ω => ((D γ (h ω)).1 (0, 1) - 1) / γ) (𝓝[>] 0)
      (fun ω => (segPairing (h ω) 0 0 - qConst) / 2) :=
    (tendstoInMeasure_comp_iff (F := fun γ g => ((D γ g).1 (0, 1) - 1) / γ)
      (G := fun g => (segPairing g 0 0 - qConst) / 2)
      (hev.mono fun γ hγ => ((hDm γ hγ).sub_const 1).div_const γ) hGm hh₀ hh).1 c1'
  -- the limit law, for `h₀` and then for `h`
  have hP2 : P.map (fun ω => (segPairing (h ω) 0 0 - qConst) / 2) =
      gaussianReal (-qConst / 2) (3 / 8 : NNReal) := by
    rw [← map_comp_eq_of_isNormalizedWPGFF hGm hh₀ hh, ← hSq, ← c2]
    refine Measure.map_congr ?_
    filter_upwards [hH00] with ω hω
    rw [hω]
  refine ⟨⟨?_, ?_⟩, ?_, hP1, hP2, ?_, ?_⟩
  · -- `q` is a median of `M`
    rw [← hlawMP, ← hSq]
    exact hlawM.1.1
  · -- and its only median
    intro m hm
    rw [← hlawMP] at hm
    rw [← hSq]
    exact hlawM.1.2 m hm
  · -- `q < 0`
    rw [← hSq]
    exact hlawM.2
  · -- (1.8)
    exact tendstoInDistribution_Ioo_of_tendstoInMeasure
      (X := fun γ ω => ((D γ (h ω)).1 (0, 1) - 1) / γ) hP1
      (fun γ => ((((hDm γ.1 γ.2).comp hh.1.measurable).sub_const 1).div_const _).aemeasurable)
      (hGm.comp hh.1.measurable).aemeasurable hP2
  · -- (1.9): transfer the medians to `h₀` and apply Step 6
    intro m hm
    have hm' : ∀ γ, 0 < γ → γ < 2 →
        LQGMetric.IsMedian (stdP.map fun ω => (S.D γ ω).1 (0, 1)) (m γ) := by
      intro γ hγ0 hγ2
      have e : (fun ω => (S.D γ ω).1 (0, 1)) = fun ω => (D γ (h₀ ω)).1 (0, 1) :=
        funext fun ω => by rw [(hSD γ ⟨hγ0, hγ2⟩).2 ω]
      rw [e, isMedian_map_comp_iff (hDm γ ⟨hγ0, hγ2⟩) hh₀ hh]
      exact hm γ hγ0 hγ2
    have hlim := c4 m hm'
    rw [hSq] at hlim
    exact hlim

end GaussianLQG
