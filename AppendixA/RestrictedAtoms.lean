module

public import AppendixA.ShrinkingTests
public import Mathlib.Order.Interval.Set.Infinite

/-!
# Atomic coefficients of transformed lattice restrictions

Inclusion–exclusion holds for the actual coefficients of the spectrum.
The coefficients of a transformed restriction inherit its translation
phase. Any continuous direction of this symmetry forces them all to vanish.
-/

public section

namespace MeyerGeneralProblem.LevOlevskii

noncomputable section

open Set Filter FourierTransform
open scoped Topology FourierTransform RealInnerProductSpace

/-- A uniformly locally bounded functional cannot have equal nonzero atom
magnitudes at infinitely many distinct sites in a bounded ball. -/
theorem testAtom_zero_of_equal_orbit {d : ℕ} {L : SchwartzMap (Space d) ℂ →ₗ[ℂ] ℂ}
    (hL : HasLocalTestBounds L) {ι : Type*} [Infinite ι] (s : ι ↪ Space d)
    (c : Space d) (r : ℝ) (hs : ∀ i, dist (s i) c ≤ r)
    (w : ℂ) (heq : ∀ i, ‖testAtom L (s i)‖ = ‖w‖) : w = 0 := by
  obtain ⟨M, hM⟩ := testAtom_variation_on_ball hL r
  by_contra hw
  have hpos := norm_pos_iff.mpr hw
  obtain ⟨n, hn⟩ := exists_nat_gt ((M : ℝ) / ‖w‖)
  let e : Fin n ↪ ι := Fin.valEmbedding.trans (Infinite.natEmbedding ι)
  have h := hM (e.trans s) c (fun i => hs (e i))
  simp only [Function.Embedding.trans_apply, heq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at h
  exact ((div_lt_iff₀ hpos).mp hn).not_ge h

/-- The coefficient at a translated frequency acquires the same phase as
the translated test when the physical character is constant on `D`. -/
theorem restrictedAtom_translate {d : ℕ} {A : Set (Space d)} {a : A → ℂ}
    {μ : TemperedDistribution (Space d) ℂ} (hμ : HasLocallyAtomicExpansion μ A a)
    (hA : UniformlyDiscrete A) (D : Set (Space d)) (hL : HasLocalTestBounds (restrictedFourierLinear hμ hA D))
    (u : Space d) (z : Circle) (hz : ∀ y ∈ D, frequencyPhase u y = z) (x : Space d) :
    testAtom (restrictedFourierLinear hμ hA D) (x - u) =
      (z : ℂ) * testAtom (restrictedFourierLinear hμ hA D) x := by
  apply tendsto_nhds_unique (tendsto_testAtom hL (x - u))
  apply ((tendsto_testAtom hL x).const_mul (z : ℂ)).congr
  intro n
  have ht : (SchwartzMap.compSubConstCLM ℂ (-u)) (atomTest n x) = atomTest n (x - u) := by
    ext y
    simp only [SchwartzMap.compSubConstCLM_apply, atomTest_apply, atomProfile]
    congr 1
    congr 1
    abel
  exact ht ▸ (restrictedFourierValue_translate hμ hA D u z hz (atomTest n x)).symm

/-- When the physical restriction lies in a proper affine hyperplane, its
Fourier transform has zero extracted coefficient at every spectral point. -/
theorem restrictedAtom_zero_of_hyperplane {d : ℕ} {A : Set (Space d)} {a : A → ℂ}
    {μ : TemperedDistribution (Space d) ℂ} (hμ : HasLocallyAtomicExpansion μ A a)
    (hA : UniformlyDiscrete A) (D : Set (Space d)) (hL : HasLocalTestBounds (restrictedFourierLinear hμ hA D))
    (v : Space d) (hv : v ≠ 0) (k : ℝ) (hk : ∀ y ∈ D, inner ℝ v y = k) (x : Space d) :
    testAtom (restrictedFourierLinear hμ hA D) x = 0 := by
  let := Icc.infinite (show (0 : ℝ) < 1 by norm_num)
  let s : Icc (0 : ℝ) 1 ↪ Space d :=
    ⟨fun t => x - t.val • v, fun _ _ h => Subtype.ext (smul_left_injective ℝ hv (sub_right_inj.mp h))⟩
  apply testAtom_zero_of_equal_orbit hL s x ‖v‖
  · intro t
    change dist (x - t.val • v) x ≤ ‖v‖
    rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
    exact mul_le_of_le_one_left (norm_nonneg _) t.property.2
  · intro t
    have hz (y) (hy : y ∈ D) : frequencyPhase (t.val • v) y = Real.fourierChar (t.val * k) := by
      simp [frequencyPhase, hk y hy]
    change ‖testAtom _ (x - t.val • v)‖ = _
    simpa only [norm_mul, Circle.norm_coe, one_mul] using congrArg norm (restrictedAtom_translate hμ hA D hL (t.val • v) _ hz x)

/-- Every actual spectral coefficient, extended by zero off the spectrum,
is the signed sum of the coefficients of the nonempty physical restrictions. -/
theorem recordWeight_inclusion_exclusion {d : ℕ} {ι : Type} [DecidableEq ι]
    {μ : TemperedDistribution (Space d) ℂ} {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B)
    (J : Finset ι) (t : ι → Space d) (T : ι → Matrix (Fin d) (Fin d) ℝ)
    (hT : ∀ j ∈ J, (T j).det ≠ 0) (hcover : A ⊆ ⋃ j ∈ J, range (latticeSite (t j) (T j)))
    (x : Space d) :
    recordWeight b x = ∑ S ∈ J.powerset with S.Nonempty, ((-1 : ℤ) ^ (S.card + 1)) •
      testAtom (restrictedFourierLinear hμ hA (⋂ j ∈ S, range (latticeSite (t j) (T j)))) x := by
  classical
  let D (j : ι) := range (latticeSite (t j) (T j))
  have hbounded (S : Finset ι) (hS : S ⊆ J) :
      HasLocalTestBounds (restrictedFourierLinear hμ hA (⋂ j ∈ S, D j)) := by
    simpa only [D, iInter_subtype] using restrictedFourierLinear_hasLocalTestBounds hμ hA hν hB
      (fun j : S => t j.val) (fun j : S => T j.val) (fun j => hT j.val (hS j.property))
  have h := tendsto_finsetSum (J.powerset.filter Finset.Nonempty) (fun S hS =>
    (tendsto_testAtom (hbounded S (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)) x).const_smul
      ((-1 : ℤ) ^ (S.card + 1)))
  apply tendsto_nhds_unique _ h
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_atomTest_eq_weight hν hB x] with n hn
  exact hn.symm.trans (fourierValue_inclusion_exclusion hμ hA J D hcover (atomTest n x))

end
end MeyerGeneralProblem.LevOlevskii
