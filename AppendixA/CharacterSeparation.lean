module

public import AppendixA.IntegerPreimage
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Character equations and separation of a finite union of lattice cosets
-/

public section

namespace MeyerGeneralProblem.LevOlevskii

open Matrix
open scoped Matrix
noncomputable section

/-- The analyst's Fourier character is trivial exactly on the integers. -/
theorem fourierChar_eq_one_iff_int {r : ℝ} :
    Real.fourierChar r = 1 ↔ ∃ z : ℤ, r = (z : ℝ) := by
  rw [Real.fourierChar_apply', Circle.exp_eq_one]
  have hp : 2 * Real.pi ≠ 0 := by positivity
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, mul_left_cancel₀ hp (hz.trans (mul_comm ..))⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, mul_comm ..⟩

theorem mem_integerPreimage_iff_fourierChar {k d : ℕ}
    (M : Matrix (Fin k) (Fin d) ℝ) (x : Fin d → ℝ) :
    x ∈ integerPreimage M ↔ ∀ i, Real.fourierChar ((M *ᵥ x) i) = 1 := by
  simp only [fourierChar_eq_one_iff_int]
  constructor
  · rintro ⟨z, hz⟩ i
    exact ⟨z i, congrFun hz i⟩
  · intro h
    choose z hz using h
    exact ⟨z, funext hz⟩

/-- The preimage of a translated subtorus specified by integer character rows.
Both the character rows and the chosen spectral-group basis have no ℤ-relations. -/
theorem characterFiber_lattice_or_subspace {d n k : ℕ} (hdk : d ≤ k)
    (C : Matrix (Fin k) (Fin n) ℤ) (L : Matrix (Fin n) (Fin d) ℝ)
    (hC : LinearIndependent ℤ C.row) (hL : LinearIndependent ℤ L.row)
    (a : Fin d → ℝ) :
    let M := C.map (Int.castRingHom ℝ) * L
    let F := {x : Fin d → ℝ | ∀ i, Real.fourierChar ((M *ᵥ (x - a)) i) = 1}
    (∃ T : Matrix (Fin d) (Fin d) ℝ, T.det ≠ 0 ∧
      ∀ x ∈ F, ∃ z : Fin d → ℤ, x = a + T *ᵥ (fun i => (z i : ℝ))) ∨
    (∃ W : Submodule ℝ (Fin d → ℝ), W ≠ ⊤ ∧ ∀ x ∈ F, x - a ∈ W) := by
  simpa only [Set.mem_ofPred_eq, ← mem_integerPreimage_iff_fourierChar] using
    translated_integerPreimage_lattice_or_subspace hdk _ (independent_rows_character_matrix C L hC hL) a

/-- The rows of the inverse lattice matrix test membership of its coset. -/
theorem translated_lattice_iff_characters {d : ℕ} (T : Matrix (Fin d) (Fin d) ℝ)
    (hT : T.det ≠ 0) (a x : Fin d → ℝ) :
    (∃ z : Fin d → ℤ, x = a + T *ᵥ (fun i => (z i : ℝ))) ↔
      ∀ i, Real.fourierChar ((T⁻¹ *ᵥ (x - a)) i) = 1 := by
  rw [← mem_integerPreimage_iff_fourierChar]
  have hu := isUnit_iff_ne_zero.mpr hT
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    rw [add_sub_cancel_left, Matrix.mulVec_mulVec, T.nonsing_inv_mul hu, Matrix.one_mulVec]
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [← hz, Matrix.mulVec_mulVec, T.mul_nonsing_inv hu, Matrix.one_mulVec]
    abel

/-- For every lattice choose one inverse-coordinate character detecting the point
outside it. Their product of differences vanishes on the entire finite union
and is nonzero at the chosen point. This includes an empty family of cosets. -/
theorem exists_separating_character_product {m d : ℕ} (a : Fin m → Fin d → ℝ)
    (T : Fin m → Matrix (Fin d) (Fin d) ℝ) (hT : ∀ j, (T j).det ≠ 0)
    (p : Fin d → ℝ)
    (hp : ∀ j, ¬ ∃ z : Fin d → ℤ, p = a j + T j *ᵥ (fun i => (z i : ℝ))) :
    ∃ i : Fin m → Fin d,
      let f := fun (x : Fin d → ℝ) => ∏ j, ((Real.fourierChar
        (((T j)⁻¹ *ᵥ (x - a j)) (i j)) : ℂ) - 1)
      f p ≠ 0 ∧ ∀ j (z : Fin d → ℤ), f (a j + T j *ᵥ (fun l => (z l : ℝ))) = 0 := by
  classical
  have hout (j : Fin m) := (translated_lattice_iff_characters (T j) (hT j) (a j) p).not.mp (hp j)
  simp only [not_forall] at hout
  choose i hi using hout
  refine ⟨i, Finset.prod_ne_zero_iff.mpr (fun j _ => sub_ne_zero.mpr ?_), ?_⟩
  · exact fun heq => hi j (Subtype.ext heq)
  · intro j z
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    apply sub_eq_zero.mpr
    exact congrArg (fun t : Circle => (t : ℂ))
      ((translated_lattice_iff_characters (T j) (hT j) (a j) _).mp ⟨z, rfl⟩ (i j))

end
end MeyerGeneralProblem.LevOlevskii
