module

public import AppendixA.Definitions
public import Mathlib.Order.Interval.Set.Infinite

/-!
# Atom exclusion for restrictions with continuous translation symmetry

An infinite set of distinct translates inside a compact region cannot carry
the same positive mass at every site. In particular invariance of singleton
masses along any real line excludes all atoms.
-/

public section

namespace MeyerGeneralProblem.LevOlevskii

open MeasureTheory Set Metric
open scoped ENNReal

/-- Equal singleton masses on an infinite family in a finite-measure set
must all be zero. -/
theorem equal_atom_mass_zero {X ι : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    [Infinite ι] (ν : Measure X) {K : Set X} (hK : ν K < ∞) (s : ι ↪ X)
    (hs : ∀ i, s i ∈ K) (m : ℝ≥0∞) (hm : ∀ i, ν {s i} = m) : m = 0 := by
  by_contra hn
  have h := tsum_meas_le_meas_iUnion_of_disjoint ν (fun i => measurableSet_singleton (s i))
    (fun i j hij => Set.disjoint_singleton.mpr (s.injective.ne hij))
  rw [show (∑' i, ν {s i}) = ∞ by simp only [hm, ENNReal.tsum_const_eq_top_of_ne_zero hn]] at h
  exact (not_le_of_gt hK) (h.trans (measure_mono (iUnion_subset fun i => singleton_subset_iff.mpr (hs i))))

/-- Continuous translation symmetry along a nonzero direction excludes a
point mass. Applied to variation this also excludes complex atoms. -/
theorem atom_zero_of_line_invariance {d : ℕ} (ν : Measure (Space d)) [IsFiniteMeasureOnCompacts ν]
    (v : Space d) (hv : v ≠ 0) (x : Space d) (hinv : ∀ t : ℝ, ν {x + t • v} = ν {x}) :
    ν {x} = 0 := by
  let := Icc.infinite (show (0 : ℝ) < 1 by norm_num)
  let s : Icc (0 : ℝ) 1 ↪ Space d :=
    ⟨fun t => x + t.val • v, fun t u h => Subtype.ext (smul_left_injective ℝ hv (add_left_cancel h))⟩
  apply equal_atom_mass_zero ν (K := closedBall x ‖v‖) measure_closedBall_lt_top s _ _ (fun i => hinv i.val)
  intro i
  change dist (x + i.val • v) x ≤ ‖v‖
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg i.property.1]
  exact mul_le_of_le_one_left (norm_nonneg _) i.property.2

end MeyerGeneralProblem.LevOlevskii
