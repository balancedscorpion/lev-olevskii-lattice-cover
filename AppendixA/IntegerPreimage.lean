module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Preimages of torus cosets

In the covering argument of Appendix A, integer characters impose conditions
of the form `M x ∈ ℤᵈ`. If the rows have no integer relation, a singular
real matrix confines all such points to a proper real subspace.
-/

public section

namespace MeyerGeneralProblem.LevOlevskii

open Matrix
open scoped Matrix

/-- Real vectors sent to integer coordinates by every row of a matrix. -/
@[expose] def integerPreimage {k d : ℕ} (M : Matrix (Fin k) (Fin d) ℝ) : Set (Fin d → ℝ) :=
  {x | ∃ z : Fin k → ℤ, M *ᵥ x = fun i => (z i : ℝ)}

private theorem independent_rows_iff {k d : ℕ} (M : Matrix (Fin k) (Fin d) ℝ) :
    LinearIndependent ℤ M.row ↔
      ∀ z : Fin k → ℤ, (fun i => (z i : ℝ)) ᵥ* M = 0 → z = 0 := by
  rw [Fintype.linearIndependent_iff]
  simp only [funext_iff, Pi.zero_apply, Matrix.vecMul_eq_sum, Int.cast_smul_eq_zsmul, Matrix.row]

/-- Independent integer characters stay independent after composition with
the matrix whose rows are a ℤ-basis of the spectral group. -/
theorem independent_rows_character_matrix {k n d : ℕ}
    (C : Matrix (Fin k) (Fin n) ℤ) (L : Matrix (Fin n) (Fin d) ℝ)
    (hC : LinearIndependent ℤ C.row) (hL : LinearIndependent ℤ L.row) :
    LinearIndependent ℤ (C.map (Int.castRingHom ℝ) * L).row := by
  rw [independent_rows_iff] at hL ⊢
  intro z hz
  have hzC : z ᵥ* C = 0 := by
    apply hL
    have hcast : (fun i => ((z ᵥ* C) i : ℝ)) =
        (fun i => (z i : ℝ)) ᵥ* C.map (Int.castRingHom ℝ) := by
      funext i
      simpa only [Function.comp_def, Int.coe_castRingHom] using
        (Int.castRingHom ℝ).map_vecMul C z i
    rwa [hcast, Matrix.vecMul_vecMul]
  exact Matrix.vecMul_injective_iff.mpr hC (hzC.trans (Matrix.zero_vecMul C).symm)

/-- If the integer preimage spans, evaluating the rows on a basis from that
preimage gives an integer matrix. A singular determinant would give an
integer row relation, which transports back along the basis change. -/
theorem det_ne_zero_of_integerPreimage_spans {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (hrows : LinearIndependent ℤ M.row)
    (hspan : Submodule.span ℝ (integerPreimage M) = ⊤) : M.det ≠ 0 := by
  classical
  let b := Module.Basis.ofSpan hspan.ge
  let e := b.indexEquiv (Pi.basisFun ℝ (Fin d))
  let basis := b.reindex e
  let P : Matrix (Fin d) (Fin d) ℝ := fun i j => basis j i
  have hP : IsUnit P := Matrix.linearIndependent_cols_iff_isUnit.mp basis.linearIndependent
  have hmem (j : Fin d) : basis j ∈ integerPreimage M :=
    Module.Basis.ofSpan_subset hspan.ge ⟨e.symm j, by simp [basis, b]⟩
  choose coord hcoord using hmem
  let Z : Matrix (Fin d) (Fin d) ℤ := fun i j => coord j i
  have hZ : Z.map (Int.castRingHom ℝ) = M * P := by
    ext i j
    exact (congrFun (hcoord j) i).symm
  intro hdet
  have hzero : Z.det = 0 := by
    have hz : (Z.det : ℝ) = 0 := by
      rw [Int.cast_det]
      change (Z.map (Int.castRingHom ℝ)).det = 0
      rw [hZ, Matrix.det_mul, hdet, zero_mul]
    exact_mod_cast hz
  obtain ⟨v, hv, hvZ⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hzero
  apply hv
  apply (independent_rows_iff M).mp hrows
  apply Matrix.vecMul_injective_of_isUnit hP
  dsimp only
  rw [Matrix.zero_vecMul, Matrix.vecMul_vecMul, ← hZ]
  funext j
  simpa only [hvZ, Pi.zero_apply, map_zero, Function.comp_def, Int.coe_castRingHom] using
    ((Int.castRingHom ℝ).map_vecMul Z v j).symm

/-- A nonsingular system of integer character constraints yields one
full-rank lattice; a singular system with integer-independent rows is
contained in a proper real subspace. -/
theorem integerPreimage_lattice_or_subspace {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (hrows : LinearIndependent ℤ M.row) :
    (∃ T : Matrix (Fin d) (Fin d) ℝ, T.det ≠ 0 ∧
      ∀ x ∈ integerPreimage M, ∃ z : Fin d → ℤ, x = T *ᵥ (fun i => (z i : ℝ))) ∨
    (∃ W : Submodule ℝ (Fin d → ℝ), W ≠ ⊤ ∧ integerPreimage M ⊆ W) := by
  by_cases h : Submodule.span ℝ (integerPreimage M) = ⊤
  · have hu := isUnit_iff_ne_zero.mpr (det_ne_zero_of_integerPreimage_spans M hrows h)
    refine Or.inl ⟨M⁻¹, (M.isUnit_nonsing_inv_det hu).ne_zero, ?_⟩
    rintro x ⟨z, hz⟩
    exact ⟨z, by rw [← hz, Matrix.mulVec_mulVec, M.nonsing_inv_mul hu, Matrix.one_mulVec]⟩
  · exact Or.inr ⟨_, h, Submodule.subset_span⟩

/-- Pulling integral character equations back to real coordinates gives either
a translated full-rank lattice cover or a translate of a proper subspace.
There may be more equations than ambient coordinates. -/
theorem translated_integerPreimage_lattice_or_subspace {d k : ℕ} (hdk : d ≤ k)
    (M : Matrix (Fin k) (Fin d) ℝ) (hrows : LinearIndependent ℤ M.row)
    (a : Fin d → ℝ) :
    (∃ T : Matrix (Fin d) (Fin d) ℝ, T.det ≠ 0 ∧
      ∀ x, x - a ∈ integerPreimage M →
        ∃ z : Fin d → ℤ, x = a + T *ᵥ (fun i => (z i : ℝ))) ∨
    (∃ W : Submodule ℝ (Fin d → ℝ), W ≠ ⊤ ∧
      ∀ x, x - a ∈ integerPreimage M → x - a ∈ W) := by
  let e : Fin d ↪ Fin k := Fin.castLEEmb hdk
  let N := M.submatrix e id
  have hN : LinearIndependent ℤ N.row := hrows.comp e e.injective
  have hincl : integerPreimage M ⊆ integerPreimage N := by
    rintro x ⟨z, hz⟩
    exact ⟨z ∘ e, funext fun i => congrFun hz (e i)⟩
  obtain ⟨T, hT, hcover⟩ | ⟨W, hW, hcover⟩ := integerPreimage_lattice_or_subspace N hN
  · refine Or.inl ⟨T, hT, fun x hx => ?_⟩
    obtain ⟨z, hz⟩ := hcover (x - a) (hincl hx)
    exact ⟨z, by rw [← hz]; abel⟩
  · exact Or.inr ⟨W, hW, fun _ hx => hcover (hincl hx)⟩

end MeyerGeneralProblem.LevOlevskii
