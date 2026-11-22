module

public import AppendixA.AtomicSeries
public import AppendixA.CharacterSeparation
public import Mathlib.Algebra.Field.GeomSum

/-!
# Restricting the atomic distribution to lattice cosets

Products of one-dimensional character means give the average over a box
in dual-lattice coordinates. The multiplier converges to the indicator of
the coset and its absolute value is bounded by one at every point.
-/

@[expose] public section

namespace MeyerGeneralProblem.LevOlevskii

noncomputable section

open Filter Set Matrix
open scoped Topology Matrix Classical

/-- The normalized mean of powers indexed by the integers from zero to `N`. -/
def phaseMean (N : ℕ) (z : Circle) : ℂ :=
  (∑ j ∈ Finset.range (N + 1), (z : ℂ) ^ j) / (N + 1 : ℕ)

theorem norm_phaseMean_le_one (N : ℕ) (z : Circle) : ‖phaseMean N z‖ ≤ 1 := by
  unfold phaseMean
  rw [norm_div, Complex.norm_natCast, div_le_one (by positivity)]
  simpa using norm_sum_le (Finset.range (N + 1)) (fun j => (z : ℂ) ^ j)

/-- The average retains exactly the trivial phase. -/
theorem tendsto_phaseMean (z : Circle) :
    Tendsto (fun N => phaseMean N z) atTop (𝓝 (if z = 1 then 1 else 0)) := by
  by_cases hz : z = 1
  · subst z
    have h (N : ℕ) : phaseMean N 1 = 1 := by
      simp [phaseMean, Nat.cast_add_one_ne_zero N]
    simp [h]
  simp only [hz, ↓reduceIte]
  have hne : (z : ℂ) ≠ 1 := fun h => hz (Subtype.ext h)
  apply squeeze_zero_norm (a := fun N : ℕ => (2 / ‖(z : ℂ) - 1‖) / (N + 1 : ℕ))
  · intro N
    rw [phaseMean, geom_sum_eq hne, norm_div, norm_div, Complex.norm_natCast]
    gcongr
    simpa [one_add_one_eq_two] using norm_sub_le ((z : ℂ) ^ (N + 1)) 1
  · exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1) |>.const_div_atTop _

/-- Average over a dual-lattice box based at the origin. Each inverse-matrix
row is a generator of the dual lattice in physical coordinates. -/
def latticeBoxAverage {d : ℕ} (t : Space d) (T : Matrix (Fin d) (Fin d) ℝ)
    (N : ℕ) (x : Space d) : ℂ :=
  ∏ i, phaseMean N (Real.fourierChar ((T⁻¹ *ᵥ (WithLp.ofLp x - WithLp.ofLp t)) i))

theorem norm_latticeBoxAverage_le_one {d : ℕ} (t : Space d) (T : Matrix (Fin d) (Fin d) ℝ)
    (N : ℕ) (x : Space d) : ‖latticeBoxAverage t T N x‖ ≤ 1 := by
  rw [latticeBoxAverage, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => norm_phaseMean_le_one _ _

theorem tendsto_latticeBoxAverage {d : ℕ} (t : Space d) (T : Matrix (Fin d) (Fin d) ℝ)
    (hT : T.det ≠ 0) (x : Space d) :
    Tendsto (fun N => latticeBoxAverage t T N x) atTop
      (𝓝 ((Set.range (latticeSite t T)).indicator (fun _ => (1 : ℂ)) x)) := by
  classical
  let z (i : Fin d) := Real.fourierChar ((T⁻¹ *ᵥ (WithLp.ofLp x - WithLp.ofLp t)) i)
  have h := tendsto_finsetProd Finset.univ (fun i _ => tendsto_phaseMean (z i))
  have hmem : x ∈ range (latticeSite t T) ↔ ∀ i, z i = 1 := by
    rw [← translated_lattice_iff_characters T hT]
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, congrArg (WithLp.toLp 2) hj.symm⟩
  by_cases hall : ∀ i, z i = 1 <;>
    simpa [latticeBoxAverage, Fintype.prod_boole, Set.indicator_apply, hmem, hall, z] using h

/-- Products of the dual averages restrict to intersections, including when
the intersection has lower rank or is empty. Convergence is tested on each
Schwartz function with the original complex weights. -/
theorem tendsto_latticeIntersection_on_test {d : ℕ} {ι : Type*} (J : Finset ι)
    (t : ι → Space d) (T : ι → Matrix (Fin d) (Fin d) ℝ) (hT : ∀ j ∈ J, (T j).det ≠ 0)
    {A : Set (Space d)} {a : A → ℂ} {μ : TemperedDistribution (Space d) ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (φ : SchwartzMap (Space d) ℂ) :
    Tendsto (fun N => ∑' x : A, (a x * φ x) * ∏ j ∈ J, latticeBoxAverage (t j) (T j) N x)
      atTop (𝓝 (∑' x : A, (⋂ j ∈ J, range (latticeSite (t j) (T j))).indicator
        (fun y => a x * φ y) x.val)) := by
  classical
  apply tendsto_tsum_of_dominated_convergence (summable_atomic_schwartz hμ hA φ)
  · intro x
    have h := (tendsto_finsetProd J (fun j hj => tendsto_latticeBoxAverage (t j) (T j)
      (hT j hj) x.val)).const_mul (a x * φ x)
    by_cases hmem : ∀ j ∈ J, x.val ∈ range (latticeSite (t j) (T j))
    · simpa [Set.indicator_apply, Finset.prod_boole, hmem] using h
    · simpa [Set.indicator_apply, Finset.prod_boole, hmem] using h
  · apply Eventually.of_forall
    intro N x
    rw [norm_mul, norm_prod]
    apply mul_le_of_le_one_right (norm_nonneg _)
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => norm_latticeBoxAverage_le_one ..

end
end MeyerGeneralProblem.LevOlevskii
