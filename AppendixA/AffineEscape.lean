module

public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Empty balls outside finite families of proper affine subspaces
-/

public section

namespace MeyerGeneralProblem.LevOlevskii

open Filter Metric
open scoped Pointwise

/-- Along a direction outside every underlying subspace, the distance from
each translated subspace eventually exceeds any prescribed radius. -/
theorem exists_ball_avoiding_affine_subspaces {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Finite ι]
    (W : ι → Submodule ℝ E) (hW : ∀ i, W i ≠ ⊤) (a : ι → E) (R : ℝ) :
    ∃ c : E, ∀ i x, x - a i ∈ W i → R < dist c x := by
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top W hW
  let δ (i : ι) := infDist v (W i : Set E)
  have hδ (i : ι) : 0 < δ i :=
    ((W i).closed_of_finiteDimensional.notMem_iff_infDist_pos ⟨0, (W i).zero_mem⟩).mp (hv i)
  have hlarge : ∀ᶠ t : ℝ in atTop, ∀ i, (R + ‖a i‖) / δ i < t :=
    eventually_all.mpr fun _ => eventually_gt_atTop _
  obtain ⟨t, ht, hlarge⟩ := ((eventually_gt_atTop (0 : ℝ)).and hlarge).exists
  refine ⟨t • v, fun i x hx => ?_⟩
  have hscaled : x - a i ∈ t • (W i : Set E) :=
    ⟨t⁻¹ • (x - a i), (W i).smul_mem _ hx, smul_inv_smul₀ ht.ne' _⟩
  have hbound := infDist_le_dist_of_mem (x := t • v) hscaled
  rw [infDist_smul₀ ht.ne', Real.norm_eq_abs, abs_of_pos ht] at hbound
  have htriangle := dist_triangle (t • v) x (x - a i)
  have hshift : dist x (x - a i) = ‖a i‖ := by simp
  rw [hshift] at htriangle
  have hlt := (div_lt_iff₀ (hδ i)).mp (hlarge i)
  change t * δ i ≤ _ at hbound
  linarith

end MeyerGeneralProblem.LevOlevskii
