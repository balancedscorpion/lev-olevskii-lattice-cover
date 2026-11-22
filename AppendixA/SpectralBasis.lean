module

public import AppendixA.PhaseGeneration
public import AppendixA.AffineEscape
public import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Coordinates for the spectral torus
-/

public section
namespace MeyerGeneralProblem.LevOlevskii
noncomputable section
open Set Metric FourierTransform Submodule
open scoped FourierTransform

/-- A nonempty spectrum has an integer basis for its additive group, with
a real-linearly independent subfamily of full ambient dimension. -/
theorem spectral_integer_basis {d : ℕ} {μ : TemperedDistribution (Space d) ℂ}
    {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B) (hne : B.Nonempty) :
    ∃ (n : ℕ) (u : Fin n → Space d), LinearIndependent ℤ u ∧
      span ℤ (range u) = span ℤ B ∧ ∃ e : Fin d ↪ Fin n, LinearIndependent ℝ (u ∘ e) := by
  classical
  obtain ⟨href,hsep⟩ := reflected_atomic_expansion hμ hA
  obtain ⟨R,hdense⟩ := relatively_dense_atomic_support hν hB href hsep hne
  have hfull : span ℝ B = ⊤ := by
    by_contra hp
    obtain ⟨c,hc⟩ := exists_ball_avoiding_affine_subspaces (fun _ : Unit => span ℝ B)
      (fun _ => hp) (fun _ => 0) R
    obtain ⟨x,hx,hd⟩ := hdense c
    exact hd.not_gt (hc () x (by simpa using (subset_span hx : x ∈ span ℝ B)))
  let G := span ℤ B
  have hg : G.FG := (fg_iff_addSubgroup_fg G).mpr (by
    simpa [G, span_int_eq_addSubgroupClosure] using (support_and_spectrum_groups_fg hμ hA hν hB).2)
  let := Module.Finite.iff_fg.mpr hg
  let : Module.IsTorsionFree ℤ (Space d) := .of_smul_eq_zero fun r x h => by
    rw [← Int.cast_smul_eq_zsmul ℝ, smul_eq_zero] at h
    simpa using h
  let β := Module.finBasis ℤ G
  let u := G.subtype ∘ β
  have hu : LinearIndependent ℤ u := β.linearIndependent.map' G.subtype G.ker_subtype
  have hus : span ℤ (range u) = G := by
    unfold u
    rw [range_comp, ← map_span, β.span_eq, Submodule.map_top, range_subtype]
  have hur : span ℝ (range u) = ⊤ := by
    rw [← span_span_of_tower ℤ ℝ, hus, span_span_of_tower, hfull]
  have hchoose := exists_fun_fin_finrank_span_eq ℝ (range u)
  rw [hur, finrank_top] at hchoose
  rw [finrank_euclideanSpace_fin] at hchoose
  obtain ⟨v,hv,_,hind⟩ := hchoose
  choose e he using hv
  have hinj : Function.Injective e := fun i j h => hind.injective ((he i).symm.trans ((congrArg u h).trans (he j)))
  refine ⟨_,u,hu,hus,⟨e,hinj⟩,?_⟩
  simpa only [Function.comp_def, Function.Embedding.coeFn_mk, he] using hind

end
end MeyerGeneralProblem.LevOlevskii
