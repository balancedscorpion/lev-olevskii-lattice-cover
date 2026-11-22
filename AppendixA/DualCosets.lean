module

public import AppendixA.FullRankRestrictions

/-!
# Phase of a single physical restriction on its dual lattice
-/

@[expose] public section

namespace MeyerGeneralProblem.LevOlevskii

noncomputable section

open Set Matrix FourierTransform
open scoped Matrix FourierTransform RealInnerProductSpace Classical

/-- The inverse transpose generates the dual lattice in the standard
Euclidean inner product. -/
def dualMatrix {d : ℕ} (T : Matrix (Fin d) (Fin d) ℝ) := T⁻¹ᵀ

theorem dualMatrix_det_ne_zero {d : ℕ} (T : Matrix (Fin d) (Fin d) ℝ) (hT : T.det ≠ 0) :
    (dualMatrix T).det ≠ 0 := by simp [dualMatrix, hT]

theorem dual_phase_on_lattice {d : ℕ} (t : Space d) (T : Matrix (Fin d) (Fin d) ℝ)
    (hT : T.det ≠ 0) (u : Space d) (hu : u ∈ matrixLattice (dualMatrix T)) :
    ∀ y ∈ range (latticeSite t T), frequencyPhase u y = frequencyPhase u t := by
  have hmem : u ∈ range (latticeSite 0 (dualMatrix T)) :=
    (mem_latticeCoset_iff ..).mpr (by simpa using hu)
  obtain ⟨z, rfl⟩ := hmem
  rintro _ ⟨w, rfl⟩
  let r (z : Fin d → ℤ) := fun i => (z i : ℝ)
  have hdot : (T *ᵥ r w) ⬝ᵥ ((dualMatrix T) *ᵥ r z) = ↑(z ⬝ᵥ w) := by
    rw [dualMatrix, Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec,
      T.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hT), Matrix.one_mulVec]
    simp [dotProduct, r]
  have hphase : frequencyPhase (latticeSite 0 (dualMatrix T) z) (WithLp.toLp 2 (T *ᵥ r w)) = 1 := by
    apply fourierChar_eq_one_iff_int.mpr
    refine ⟨z ⬝ᵥ w, ?_⟩
    simpa [frequencyPhase, EuclideanSpace.inner_eq_star_dotProduct, latticeSite, r] using hdot
  change frequencyPhase _ (t + WithLp.toLp 2 (T *ᵥ r w)) = _
  rw [AddChar.map_add_eq_mul, hphase, mul_one]

/-- On every dual-lattice translate the atom function is one fixed
modulation, with an amplitude determined by any one representative. -/
theorem restrictedAtom_on_dual_coset {d : ℕ} {A : Set (Space d)} {a : A → ℂ}
    {μ : TemperedDistribution (Space d) ℂ} (hμ : HasLocallyAtomicExpansion μ A a)
    (hA : UniformlyDiscrete A) (t : Space d) (T : Matrix (Fin d) (Fin d) ℝ) (hT : T.det ≠ 0)
    (hL : HasLocalTestBounds (restrictedFourierLinear hμ hA (range (latticeSite t T))))
    (p y : Space d) (hy : y ∈ range (latticeSite p (dualMatrix T))) :
    let F := testAtom (restrictedFourierLinear hμ hA (range (latticeSite t T)))
    F y = (F p * (frequencyPhase t p : ℂ)) * (frequencyPhase (-t) y : ℂ) := by
  have hu := (matrixLattice (dualMatrix T)).neg_mem ((mem_latticeCoset_iff ..).mp hy)
  rw [neg_sub] at hu
  have h := restrictedAtom_translate hμ hA _ hL (p-y) _
    (dual_phase_on_lattice t T hT _ hu) p
  rw [sub_sub_cancel] at h
  have hph : frequencyPhase (p-y) t = frequencyPhase t p * frequencyPhase (-t) y := by
    simp [frequencyPhase, real_inner_comm p t,
      real_inner_comm y t, AddChar.map_sub_eq_div, AddChar.map_neg_eq_inv, div_eq_mul_inv]
  simpa only [hph, Circle.coe_mul, mul_assoc, mul_comm, mul_left_comm] using h

/-- Finitely many nonzero classes modulo the dual lattice give an explicit
finite sum of modulated coset indicators for this restriction. -/
theorem restrictedAtom_comb_of_finite_classes {d : ℕ} {A : Set (Space d)} {a : A → ℂ}
    {μ : TemperedDistribution (Space d) ℂ} (hμ : HasLocallyAtomicExpansion μ A a)
    (hA : UniformlyDiscrete A) (t : Space d) (T : Matrix (Fin d) (Fin d) ℝ) (hT : T.det ≠ 0)
    (hL : HasLocalTestBounds (restrictedFourierLinear hμ hA (range (latticeSite t T)))) :
    let F := testAtom (restrictedFourierLinear hμ hA (range (latticeSite t T)))
    let H := matrixLattice (dualMatrix T)
    (H.mkQ '' Function.support F).Finite →
      ∃ (m : ℕ) (p : Fin m → Space d) (c : Fin m → ℂ), ∀ y, F y =
        ∑ j, (range (latticeSite (p j) (dualMatrix T))).indicator
          (fun z => c j * (frequencyPhase (-t) z : ℂ)) y := by
  intro F H hfin
  let S := H.mkQ '' Function.support F
  let := hfin.fintype
  choose pick _ hpick using fun q : S => q.property
  let e := Fintype.equivFin S
  let c (q : S) := F (pick q) * (frequencyPhase t (pick q) : ℂ)
  let D (q : S) := range (latticeSite (pick q) (dualMatrix T))
  have hclass (q : S) (y : Space d) : y ∈ D q ↔ H.mkQ y = q.val := by
    rw [← hpick q, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, mem_latticeCoset_iff]
  refine ⟨Fintype.card S, pick ∘ e.symm, c ∘ e.symm, fun y => ?_⟩
  change F y = ∑ j, (D (e.symm j)).indicator (fun z => c (e.symm j) * _) y
  rw [e.symm.sum_comp (fun q => (D q).indicator (fun z => c q * (frequencyPhase (-t) z : ℂ)) y)]
  by_cases h : H.mkQ y ∈ S
  · let q : S := ⟨H.mkQ y, h⟩
    have hy : y ∈ D q := (hclass q y).mpr rfl
    rw [Finset.sum_eq_single q, Set.indicator_of_mem hy]
    · exact restrictedAtom_on_dual_coset hμ hA t T hT hL (pick q) y hy
    · intro j _ hj
      exact Set.indicator_of_notMem (fun hmem => hj (Subtype.ext ((hclass j y).mp hmem).symm)) _
    · simp
  · have hzero : F y = 0 := by
      by_contra hy
      exact h ⟨y, hy, rfl⟩
    rw [hzero]
    symm
    exact Finset.sum_eq_zero fun j _ => Set.indicator_of_notMem
      (fun hy => h (((hclass j y).mp hy).symm ▸ j.property)) _

end
end MeyerGeneralProblem.LevOlevskii
