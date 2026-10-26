import SupercriticalLFPPAS.Main.Recovery

/-!
# §7: Theorem 1.1 for the strong metric of the setup (packet T7)

Paper §7, l. 625–662; SB2 §2.8 and D11. On the one probability-one event `Ω₀` of `ae_mainGood` (countable: the mesh
comparisons for integers `j, R ≥ 1`, (2.1), (2.2) for the countably many mesh exponents, Lemma 6.2, Pfeffer geodesics and
the Euclidean continuity of finite-length `D`-curves), both defining conditions of `LSCTendsto` hold for every sequence
of positive cutoffs `ε_n → 0`: (1.2) by `lowerLimit`, recovery by `recovery`. Every choice after `Ω₀` is fixed is a
deterministic argument on `Ω₀`; no intersection over uncountably many endpoint-dependent events is taken.

The rescaled LFPP `rescaledLFPP ξ (m ε) (X ε ω)` is pointwise the coercion of `Core.lfppM S ε (X ε ω)`
(`B2.Median.lfppMetric_toLSCFun`, definitional).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace SupercriticalLFPPAS.Main

/-- **§7: Theorem 1.1 for the strong metric `D` of the setup** (every `ξ > 0`, every jointly continuous heat version),
from Proposition 5.1 (internal form), the corrected Lemma 6.1, Lemma 6.2, (2.1), (2.2) and deterministic LFPP
geodesics. -/
theorem mainAe_of (S : Core.Setup) (h51 : Core.Prop51Stmt S) (hW : Core.NormalizerWindowStmt S)
    (h62 : Core.Lemma62Stmt S) (hM : Core.MeshOscStmt) (hA : Core.LocApproxStmt) (hG : Core.LFPPGeodesicStmt) :
    Core.MainAeStmt S := by
  intro Ω _ P _ h hh X hX
  obtain ⟨a, s, hae⟩ := ae_mainGood S h51 h62 hM hA P h hh X hX
  filter_upwards [hae] with ω hω
  intro ε hε
  exact ⟨fun p q hp => lowerLimit S hG hW hω hε p q hp, fun q => recovery S hG hW hω hε q⟩

end SupercriticalLFPPAS.Main
