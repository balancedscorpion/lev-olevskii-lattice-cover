module

public import AppendixA.RestrictedAtoms
public import AppendixA.LatticeIntersections

/-!
# Reducing weight recovery to single full-rank physical cosets
-/

public section

namespace MeyerGeneralProblem.LevOlevskii

noncomputable section

open Set Filter FourierTransform
open scoped Topology FourierTransform

/-- Given a finite physical lattice cover, the entire spectral coefficient
function is a finite integer combination of coefficient functions of
full-rank single-coset restrictions. This includes points off the spectrum. -/
theorem spectral_weights_from_fullRank_restrictions {d : ℕ}
    {μ : TemperedDistribution (Space d) ℂ} {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B)
    (hcover : HasFiniteLatticeCover A) :
    ∃ (m : ℕ) (c : Fin m → ℤ) (t : Fin m → Space d) (T : Fin m → Matrix (Fin d) (Fin d) ℝ),
      (∀ j, (T j).det ≠ 0) ∧ ∀ x, recordWeight b x =
      ∑ j, c j • testAtom (restrictedFourierLinear hμ hA (range (latticeSite (t j) (T j)))) x := by
  classical
  obtain ⟨m, _, t, T, hT, hcover⟩ := hcover
  let D (j : Fin m) := range (latticeSite (t j) (T j))
  let J := (Finset.univ : Finset (Fin m)).powerset.filter Finset.Nonempty
  let I (S : J) := ⋂ j ∈ S.val, D j
  have hI (S : J) : I S = ⋂ j : S.val, range (latticeSite (t j.val) (T j.val)) := by
    simp [I, D, iInter_subtype]
  have hlocal (S : J) : HasLocalTestBounds (restrictedFourierLinear hμ hA (I S)) := by
    rw [hI]
    exact restrictedFourierLinear_hasLocalTestBounds hμ hA hν hB _ _ (fun j => hT j.val)
  have split (S : J) : ∃ (k : ℤ) (p : Space d) (U : Matrix (Fin d) (Fin d) ℝ),
      U.det ≠ 0 ∧ ∀ x, ((-1 : ℤ) ^ (S.val.card + 1)) • testAtom (restrictedFourierLinear hμ hA (I S)) x =
        k • testAtom (restrictedFourierLinear hμ hA (range (latticeSite p U))) x := by
    by_cases hne : (I S).Nonempty
    · obtain ⟨j, hj⟩ := (Finset.mem_filter.mp S.property).2
      let : Nonempty S.val := ⟨⟨j, hj⟩⟩
      obtain ⟨p, hp⟩ := hne
      rw [hI, mem_iInter] at hp
      obtain ⟨U, hU, heq⟩ | ⟨v, hv, hflat⟩ :=
        latticeIntersection_lattice_or_hyperplane _ _ (fun j : S.val => hT j.val) p hp
      · exact ⟨_, p, U, hU, fun x => by rw [hI, heq]⟩
      · refine ⟨0, 0, 1, by simp, fun x => ?_⟩
        rw [restrictedAtom_zero_of_hyperplane hμ hA (I S) (hlocal S) v hv _ (hI S ▸ hflat), smul_zero, zero_smul]
    · have hemp := Set.not_nonempty_iff_eq_empty.mp hne
      have hz (x : Space d) : testAtom (restrictedFourierLinear hμ hA (I S)) x = 0 := by
        apply tendsto_nhds_unique (tendsto_testAtom (hlocal S) x)
        simp only [hemp]
        simp [restrictedFourierLinear, restrictedFourierValue]
      exact ⟨0, 0, 1, by simp, fun x => by rw [hz, smul_zero, zero_smul]⟩
  choose k p U hU hcoeff using split
  let e := Fintype.equivFin J
  refine ⟨Fintype.card J, k ∘ e.symm, p ∘ e.symm, U ∘ e.symm, fun j => hU _, fun x => ?_⟩
  have hcov : A ⊆ ⋃ j ∈ (Finset.univ : Finset (Fin m)), D j := by
    intro y hy
    obtain ⟨j, z, hz⟩ := hcover y hy
    exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨Finset.mem_univ _, z, hz.symm⟩⟩
  rw [recordWeight_inclusion_exclusion hμ hA hν hB Finset.univ t T (fun j _ => hT j) hcov x]
  change (∑ S ∈ J, _) = _
  rw [← Finset.sum_attach J]
  change (∑ S : J, ((-1 : ℤ) ^ (S.val.card + 1)) • testAtom (restrictedFourierLinear hμ hA (I S)) x) = _
  simp_rw [hcoeff]
  exact (e.symm.sum_comp _).symm

end
end MeyerGeneralProblem.LevOlevskii
