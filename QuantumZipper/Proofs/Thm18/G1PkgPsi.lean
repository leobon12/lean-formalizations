import QuantumZipper.Proofs.Thm18.G1PkgChordFin
import QuantumZipper.Proofs.Thm18.G1PkgSep

/-!
# G1 package: `G1PsiSelStmt` from the existence of side-normalized uniformizers

With the trace part (`G1Pkg.g1TraceSelStmt`, G1PkgTrace.lean) and the separability of simple
chords (`G1Chord.chordSepStmt`, G1PkgSep.lean) proved, the measurable selection `G1PsiSelStmt`
(G1RegRepRed.lean) needs only `G1Chord.SideUnifExistStmt`: every simple chord has a
left-normalized (`φ(−1) = −1`) and a right-normalized (`φ(1) = 1`) uniformizer, the
normalizations of KT2 (`CA.Kernel.chordKernelTheoremLeft/Right`).

Own argument (bookkeeping).
-/

namespace QuantumZipper
namespace Thm18Asm

/-- **`G1PsiSelStmt` from the existence of side-normalized uniformizers.** -/
theorem g1PsiSelStmt_of_sideUnifExist (hex : G1Chord.SideUnifExistStmt) : G1PsiSelStmt :=
  G1Chord.g1PsiSelStmt_of_sep G1Chord.chordSepStmt hex

end Thm18Asm
end QuantumZipper
