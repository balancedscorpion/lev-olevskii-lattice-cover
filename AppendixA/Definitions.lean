module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.Fourier.Notation
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

/-!
# Lev and Olevskii's lattice-cover question

Lev and Olevskii ask this question for complex measures in dimension at least two
in [§11.2(1) of their paper](https://arxiv.org/pdf/1512.08735#page=20).
We specify a measure and its Fourier transform by their actions on Schwartz tests,
using the project's tempered-distribution Fourier convention.

The stronger statement in [Martin, Appendix A](https://hexagonmath.org/pdf/2611.00744v2#page=12)
recovers the complex weights as well as the locations of the atoms.
-/

namespace MeyerGeneralProblem.LevOlevskii

noncomputable section

open scoped ENNReal

/-- Euclidean space with its standard inner product and Fourier transform. -/
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {n : ℕ}

/-- The distribution acts as the sum of point masses at exactly the sites of `E`.
`HasSum` requires convergence of the unordered sum on each Schwartz test. -/
def HasAtomicExpansion (μ : TemperedDistribution (Space n) ℂ)
    (E : Set (Space n)) (a : E → ℂ) : Prop :=
  (∀ x, a x ≠ 0) ∧
    ∀ φ : SchwartzMap (Space n) ℂ, HasSum (fun x : E => a x * φ x) (μ φ)

/-- Total variation of the atomic record in the open ball of radius `R` about zero. -/
def massInBall {E : Set (Space n)} (a : E → ℂ) (R : ℝ) : ℝ≥0∞ :=
  ∑' x : {x : E // ‖(x : Space n)‖ < R}, ‖a x.val‖ₑ

/-- A common polynomial bounds the sum of the two variation masses at every radius ≥ 1. -/
def JointPolynomialGrowth {Λ S : Set (Space n)} (a : Λ → ℂ) (b : S → ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N : ℝ, 0 ≤ N ∧ ∀ R : ℝ, 1 ≤ R →
    massInBall a R + massInBall b R ≤ ENNReal.ofReal (C * (1 + R) ^ N)

/-- Distinct sites in the set have a common positive lower bound on their distance. -/
def UniformlyDiscrete (E : Set (Space n)) : Prop :=
  ∃ η : ℝ, 0 < η ∧ E.Pairwise (fun x y => η ≤ dist x y)

/-- The point of the translated lattice with integer coordinates `z`. -/
def latticeSite (t : Space n) (T : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℤ) : Space n :=
  t + WithLp.toLp 2 (T.mulVec (fun i => (z i : ℝ)))

/-- Every site belongs to one of `m ≥ 1` translates of full-rank lattices.
The shift and matrix depend on the lattice index. The integer coordinates may vary by site. -/
def HasFiniteLatticeCover (Λ : Set (Space n)) : Prop :=
  ∃ (m : ℕ) (_ : 1 ≤ m) (t : Fin m → Space n) (T : Fin m → Matrix (Fin n) (Fin n) ℝ),
    (∀ j, (T j).det ≠ 0) ∧
    ∀ x ∈ Λ, ∃ (j : Fin m) (z : Fin n → ℤ),
      x = latticeSite (t j) (T j) z

/-- The assertion asked about by Lev and Olevskii (§11.2, question 1). -/
def latticeCoverQuestion : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (μ : TemperedDistribution (Space n) ℂ)
    (Λ S : Set (Space n)) (a : Λ → ℂ) (b : S → ℂ),
    HasAtomicExpansion μ Λ a →
    HasAtomicExpansion (FourierTransform.fourier μ) S b →
    JointPolynomialGrowth a b →
    UniformlyDiscrete Λ → UniformlyDiscrete S →
    HasFiniteLatticeCover Λ

/-- Local point-mass expansion as in Appendix A. Under uniform discreteness each
compact set meets only finitely many sites, so the sum on a compact test is finite. -/
def HasLocallyAtomicExpansion (μ : TemperedDistribution (Space n) ℂ)
    (E : Set (Space n)) (a : E → ℂ) : Prop :=
  (∀ x, a x ≠ 0) ∧ ∀ φ : SchwartzMap (Space n) ℂ, HasCompactSupport φ →
    HasSum (fun x : E => a x * φ x) (μ φ)

/-- A finite sum of translated, modulated lattice combs as a distribution.
At the site `x = t j + T j z`, term `j` contributes the weight
`c j * exp(2πi ⟪s j, x⟫)`. Summing over pairs adds all contributions at overlapping sites. -/
def IsFiniteModulatedLatticeCombSum (μ : TemperedDistribution (Space n) ℂ) : Prop :=
  ∃ (m : ℕ) (t s : Fin m → Space n) (c : Fin m → ℂ) (T : Fin m → Matrix (Fin n) (Fin n) ℝ),
    (∀ j, (T j).det ≠ 0) ∧ ∀ φ : SchwartzMap (Space n) ℂ,
      HasSum (fun p : Fin m × (Fin n → ℤ) =>
        let x := latticeSite (t p.1) (T p.1) p.2
        c p.1 * (Real.fourierChar (inner ℝ (s p.1) x) : ℂ) * φ x) (μ φ)

/-- Martin, Theorem A.1, with the two lattice covers established in its proof.
The local expansions are tested on compact supports. The comb identity holds on
every Schwartz test. The empty sum includes the zero distribution. -/
def theoremA1Statement : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (μ : TemperedDistribution (Space d) ℂ)
    (A B : Set (Space d)) (a : A → ℂ) (b : B → ℂ),
    HasLocallyAtomicExpansion μ A a →
    HasLocallyAtomicExpansion (FourierTransform.fourier μ) B b →
    UniformlyDiscrete A → UniformlyDiscrete B →
    IsFiniteModulatedLatticeCombSum μ ∧ HasFiniteLatticeCover A ∧ HasFiniteLatticeCover B

end

end MeyerGeneralProblem.LevOlevskii
