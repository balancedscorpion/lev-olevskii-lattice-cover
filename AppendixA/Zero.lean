module

public import AppendixA.AtomicGrowth

/-!
# The zero distribution in Appendix A
-/

public section

namespace MeyerGeneralProblem.LevOlevskii

open FourierTransform
open scoped FourierTransform

/-- Nonzero recorded coefficients force the carrier of a zero distribution
to be empty. -/
theorem carrier_empty_of_zero {d : ℕ} {A : Set (Space d)} {a : A → ℂ}
    (hμ : HasLocallyAtomicExpansion 0 A a) (hA : UniformlyDiscrete A) : A = ∅ := by
  obtain ⟨φ, hc, hzero, hisol⟩ := exists_isolating_test hA
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hμ.1 ⟨x, hx⟩ (translated_isolating_test_eq hμ φ hc hzero hisol ⟨x, hx⟩).symm

/-- The empty comb sum and empty physical and spectral records satisfy all
three conclusions of Theorem A.1. -/
theorem theoremA1_zero {d : ℕ} {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion 0 A a) (hA : UniformlyDiscrete A)
    (hμhat : HasLocallyAtomicExpansion (𝓕 (0 : TemperedDistribution (Space d) ℂ)) B b)
    (hB : UniformlyDiscrete B) :
    IsFiniteModulatedLatticeCombSum (0 : TemperedDistribution (Space d) ℂ) ∧
      HasFiniteLatticeCover A ∧ HasFiniteLatticeCover B := by
  have hzero : (𝓕 (0 : TemperedDistribution (Space d) ℂ)) = 0 := by ext; simp
  rw [hzero] at hμhat
  have hempty : HasFiniteLatticeCover (∅ : Set (Space d)) :=
    ⟨1, le_rfl, fun _ => 0, fun _ => 1, fun _ => by simp, fun _ hx => False.elim hx⟩
  refine ⟨?_, carrier_empty_of_zero hμ hA ▸ hempty, carrier_empty_of_zero hμhat hB ▸ hempty⟩
  refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, (fun j => j.elim0), fun φ => ?_⟩
  simp

end MeyerGeneralProblem.LevOlevskii
