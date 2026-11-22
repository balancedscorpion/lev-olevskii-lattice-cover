module

public import AppendixA

public section

namespace MeyerGeneralProblem.LevOlevskii

noncomputable section

/-- Martin’s Theorem A.1, including the support and spectrum covers proved in Appendix A. -/
theorem theoremA1 : theoremA1Statement :=
  theoremA1_of_unitEquations unitaryUnitEquationFiniteness

/-- The physical cover in Theorem A.1 answers the original question in dimensions ≥ 2. -/
theorem theoremA1Statement_implies_latticeCoverQuestion
    (h : theoremA1Statement) : latticeCoverQuestion := by
  intro n hn μ Λ S a b ha hb _ hΛ hS
  exact (h n (by omega) μ Λ S a b ⟨ha.1, fun φ _ => ha.2 φ⟩
    ⟨hb.1, fun φ _ => hb.2 φ⟩ hΛ hS).2.1

/-- The support in the Lev–Olevskii question admits a finite lattice cover. -/
theorem latticeCoverQuestion_holds : latticeCoverQuestion :=
  theoremA1Statement_implies_latticeCoverQuestion theoremA1

end

end MeyerGeneralProblem.LevOlevskii
