module

public import AppendixA

public section

namespace MeyerGeneralProblem.LevOlevskii

noncomputable section

/-- The physical cover in Theorem A.1 answers the original question in dimensions ≥ 2. -/
theorem theoremA1Statement_implies_latticeCoverQuestion
    (h : theoremA1Statement) : latticeCoverQuestion := by
  intro n hn μ Λ S a b ha hb _ hΛ hS
  exact (h n (by omega) μ Λ S a b ⟨ha.1, fun φ _ => ha.2 φ⟩
    ⟨hb.1, fun φ _ => hb.2 φ⟩ hΛ hS).2.1

end

end MeyerGeneralProblem.LevOlevskii
