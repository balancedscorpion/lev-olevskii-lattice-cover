module

public import AppendixA.AffineEscape
public import AppendixA.CharacterSeparation
public import AppendixA.Definitions

/-!
# Removing proper affine subspaces from the covering argument

A trigonometric polynomial which kills a finite family of lattice cosets and
survives at an uncovered atom leaves a relatively dense set of atoms, by
almost periodicity. Such a set cannot fit in finitely many proper flats.
-/

public section

namespace MeyerGeneralProblem.LevOlevskii

open Matrix
open scoped Matrix
noncomputable section

/-- Complex trigonometric polynomials on real coordinate space. -/
@[expose] def trigPolynomials (d : ℕ) : Subalgebra ℂ ((Fin d → ℝ) → ℂ) :=
  Algebra.adjoin ℂ (Set.range fun (u : Fin d → ℝ) (x : Fin d → ℝ) =>
    (Real.fourierChar (u ⬝ᵥ x) : ℂ))

private theorem character_difference_mem {d : ℕ} (u a : Fin d → ℝ) :
    (fun x => (Real.fourierChar (u ⬝ᵥ (x - a)) : ℂ) - 1) ∈ trigPolynomials d := by
  have hchar : (fun x => (Real.fourierChar (u ⬝ᵥ x) : ℂ)) ∈ trigPolynomials d :=
    Algebra.subset_adjoin ⟨u, rfl⟩
  have hconst := (trigPolynomials d).algebraMap_mem (Real.fourierChar (u ⬝ᵥ a) : ℂ)⁻¹
  convert (trigPolynomials d).sub_mem ((trigPolynomials d).mul_mem hchar hconst)
    (trigPolynomials d).one_mem using 1
  ext x
  simp [dotProduct_sub, AddChar.map_sub_eq_div, div_eq_mul_inv]

/-- Relative density of the atoms surviving each polynomial multiplier
eliminates the affine subspaces from a finite lattice-and-flat cover. -/
theorem remove_affine_subspaces_from_cover {m d : ℕ} {ι : Type*} [Finite ι]
    (A : Set (Fin d → ℝ)) (a : Fin m → Fin d → ℝ)
    (T : Fin m → Matrix (Fin d) (Fin d) ℝ) (hT : ∀ j, (T j).det ≠ 0)
    (W : ι → Submodule ℝ (Fin d → ℝ)) (hW : ∀ i, W i ≠ ⊤) (b : ι → Fin d → ℝ)
    (hcover : ∀ x ∈ A, (∃ (j : Fin m) (z : Fin d → ℤ), x = a j + T j *ᵥ (fun i => (z i : ℝ))) ∨
      ∃ i, x - b i ∈ W i)
    (hdense : ∀ f ∈ trigPolynomials d, (∃ p ∈ A, f p ≠ 0) →
      ∃ R : ℝ, ∀ c, ∃ x ∈ A, f x ≠ 0 ∧ dist c x ≤ R) :
    ∀ x ∈ A, ∃ (j : Fin m) (z : Fin d → ℤ), x = a j + T j *ᵥ (fun i => (z i : ℝ)) := by
  classical
  intro p hp
  by_contra hout
  obtain ⟨i, hnonzero, hvanish⟩ :=
    exists_separating_character_product a T hT p (fun j hj => hout ⟨j, hj⟩)
  let g (j : Fin m) (x : Fin d → ℝ) : ℂ :=
    (Real.fourierChar (((T j)⁻¹ *ᵥ (x - a j)) (i j)) : ℂ) - 1
  have hprod : (∏ j, g j) ∈ trigPolynomials d :=
    (trigPolynomials d).prod_mem fun j _ => character_difference_mem ((T j)⁻¹ (i j)) (a j)
  obtain ⟨R, hR⟩ := hdense _ hprod ⟨p, hp, by simpa [Finset.prod_apply, g] using hnonzero⟩
  obtain ⟨c, hc⟩ := exists_ball_avoiding_affine_subspaces W hW b R
  obtain ⟨x, hx, hfx, hdist⟩ := hR c
  obtain ⟨j, z, rfl⟩ | ⟨j, hj⟩ := hcover x hx
  · exact hfx (by simpa [Finset.prod_apply, g] using hvanish j z)
  · exact (hc j x hj).not_ge hdist

/-- A finite cover by character fibers of codimension at least the ambient
dimension gives a lattice cover once polynomially filtered atoms recur. An
extra identity lattice makes the final family nonempty even for empty support. -/
theorem finiteLatticeCover_of_character_fibers {d n : ℕ} {ι : Type*} [Finite ι]
    (A : Set (Space d)) (L : Matrix (Fin n) (Fin d) ℝ) (hL : LinearIndependent ℤ L.row)
    (k : ι → ℕ) (hk : ∀ j, d ≤ k j) (a : ι → Fin d → ℝ)
    (C : (j : ι) → Matrix (Fin (k j)) (Fin n) ℤ) (hC : ∀ j, LinearIndependent ℤ (C j).row)
    (hfibers : ∀ x ∈ A, ∃ j, ∀ i, Real.fourierChar
      ((((C j).map (Int.castRingHom ℝ) * L) *ᵥ (WithLp.ofLp x - a j)) i) = 1)
    (hdense : ∀ f ∈ trigPolynomials d, (∃ p ∈ A, f (WithLp.ofLp p) ≠ 0) →
      ∃ R : ℝ, ∀ c, ∃ x ∈ A, f (WithLp.ofLp x) ≠ 0 ∧ dist c (WithLp.ofLp x) ≤ R) :
    HasFiniteLatticeCover A := by
  classical
  let F (j : ι) := {x : Fin d → ℝ | ∀ i, Real.fourierChar
    ((((C j).map (Int.castRingHom ℝ) * L) *ᵥ (x - a j)) i) = 1}
  let good (j : ι) := ∃ T : Matrix (Fin d) (Fin d) ℝ, T.det ≠ 0 ∧
    ∀ x ∈ F j, ∃ z : Fin d → ℤ, x = a j + T *ᵥ (fun i => (z i : ℝ))
  have split (j : ι) : good j ∨ ∃ W : Submodule ℝ (Fin d → ℝ), W ≠ ⊤ ∧
      ∀ x ∈ F j, x - a j ∈ W :=
    characterFiber_lattice_or_subspace (hk j) (C j) L (hC j) hL (a j)
  let g := {j : ι // good j}
  let bad := {j : ι // ¬ good j}
  let := Fintype.ofFinite g
  let e := Fintype.equivFin g
  choose T hT hcoset using fun j : g => j.property
  choose W hW hflat using fun j : bad => (split j.val).resolve_left j.property
  let S := WithLp.ofLp '' A
  have hcover (x) (hx : x ∈ S) :
      (∃ (j : Fin (Fintype.card g)) (z : Fin d → ℤ),
        x = a (e.symm j).val + T (e.symm j) *ᵥ (fun i => (z i : ℝ))) ∨
        ∃ j : bad, x - a j.val ∈ W j := by
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨j, hj⟩ := hfibers p hp
    by_cases hg : good j
    · let l : g := ⟨j, hg⟩
      exact Or.inl ⟨e l, by simpa [l] using hcoset l _ hj⟩
    · exact Or.inr ⟨⟨j, hg⟩, hflat ⟨j, hg⟩ _ hj⟩
  have hS (f) (hf : f ∈ trigPolynomials d) (hp : ∃ p ∈ S, f p ≠ 0) :
      ∃ R : ℝ, ∀ c, ∃ x ∈ S, f x ≠ 0 ∧ dist c x ≤ R := by
    obtain ⟨_, ⟨p, hp, rfl⟩, hfp⟩ := hp
    obtain ⟨R, hR⟩ := hdense f hf ⟨p, hp, hfp⟩
    refine ⟨R, fun c => ?_⟩
    obtain ⟨x, hx, hfx, hdist⟩ := hR c
    exact ⟨_, ⟨x, hx, rfl⟩, hfx, hdist⟩
  have hfinal := remove_affine_subspaces_from_cover S _ _ (fun j => hT (e.symm j))
    W hW (fun j => a j.val) hcover hS
  refine ⟨Fintype.card g + 1, by omega,
    Fin.cases 0 (fun j => WithLp.toLp 2 (a (e.symm j).val)),
    Fin.cases 1 (fun j => T (e.symm j)), Fin.cases (by simp) (fun j => hT _), ?_⟩
  intro x hx
  obtain ⟨j, z, hz⟩ := hfinal _ ⟨x, hx, rfl⟩
  exact ⟨j.succ, z, congrArg (WithLp.toLp 2) hz⟩

end
end MeyerGeneralProblem.LevOlevskii
