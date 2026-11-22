module

public import AppendixA.BoxPacking

/-!
# Finite dual-lattice classes for a full-rank restriction

The shrinking-test coefficient can survive only on the spectral cosets
whose orbits under the dual lattice are finite. Compare its Fourier box
average with the number of indices whose translated spectrum hits the
shrinking ball, then take the box limit before the shrinking-test limit.
-/

public section

namespace MeyerGeneralProblem.LevOlevskii

noncomputable section

open Set Filter Metric FourierTransform
open scoped Topology FourierTransform NNReal ENNReal Classical

private def spectralBoxTest {d : ℕ} {B : Set (Space d)} (b : B → ℂ) (t : Space d)
    (U : Matrix (Fin d) (Fin d) ℝ) (φ : SchwartzMap (Space d) ℂ) (N : ℕ) : ℂ :=
  ∑ q : Fin d → Fin (N+1), boxCoefficient t U q * ∑' y : B, b y * φ (y.val + boxFrequency U q)

private theorem spectralBoxTest_bound {d k : ℕ} {B : Set (Space d)} (b : B → ℂ)
    (t : Space d) (U : Matrix (Fin d) (Fin d) ℝ) (p : Fin k → Space d)
    (T : Fin k → Matrix (Fin d) (Fin d) ℝ) (hcover : ∀ y ∈ B, ∃ j, y - p j ∈ matrixLattice (T j))
    (M : ℝ≥0) (hM : ∀ c : Space d, (∑' y : {y : B // dist y.val c ≤ 1}, ‖b y.val‖ₑ) ≤ M)
    (x : Space d) (n N : ℕ) :
    let Q := Finset.univ.biUnion fun j => boxHits (dualMatrix U) (matrixLattice (T j)) (p j) x (atomRadius n) N
    ‖spectralBoxTest b t U (atomTest n x) N‖ ≤ Q.card * (M : ℝ) / ((N : ℝ) + 1)^d := by
  intro Q
  let w (q : Fin d → Fin (N+1)) := ∑' y : B, b y * atomTest n x (y.val + boxFrequency U q)
  have hzero (q) (hq : q ∉ Q) : w q = 0 := by
    have hz' (y : B) : b y * atomTest n x (y.val + boxFrequency U q) = 0 := by
      by_cases hz : atomTest n x (y.val + boxFrequency U q) = 0
      · simp [hz]
      obtain ⟨j, hj⟩ := hcover _ y.property
      apply False.elim (hq (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, y.val, hj, dist_lt_atomRadius_of_ne hz⟩⟩))
    simp [w, hz']
  have hw (q) : ‖w q‖ ≤ M := translated_sum_ball_bound b 1 M hM (atomTest n x) x (norm_atomTest_le n x)
    (fun _ hy => (dist_lt_atomRadius_of_ne hy).le.trans (pow_le_one₀ (by norm_num) (by norm_num))) _
  have hnorm (q : Fin d → Fin (N+1)) : ‖boxCoefficient t U q‖ = (((N : ℝ) + 1)^d)⁻¹ := by
    have hN : ‖(N : ℂ) + 1‖ = (N : ℝ) + 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (N+1)
    simp [boxCoefficient, boxWeight, hN]
  change ‖∑ q, boxCoefficient t U q * w q‖ ≤ _
  rw [← Finset.sum_subset (Finset.subset_univ Q) (fun q _ hq => by rw [hzero q hq, mul_zero])]
  calc
    _ ≤ ∑ _q ∈ Q, (((N : ℝ) + 1)^d)⁻¹ * M :=
      norm_sum_le_of_le _ (fun q _ => by rw [norm_mul, hnorm]; gcongr; exact hw q)
    _ = _ := by simp; ring

private theorem box_ratio_tendsto (d C : ℕ) :
    Tendsto (fun N : ℕ => (((N : ℝ) + C + 1) / (N + 1))^d) atTop (𝓝 1) := by
  have h := (tendsto_add_mul_div_add_mul_atTop_nhds ((C : ℝ)+1) 1 1 (one_ne_zero : (1 : ℝ) ≠ 0)).pow d
  simpa [add_comm, add_left_comm, add_assoc] using h

private theorem atom_zero_outside_finite_orbits {d k : ℕ}
    {μ : TemperedDistribution (Space d) ℂ} {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B)
    (t : Space d) (U : Matrix (Fin d) (Fin d) ℝ) (hU : U.det ≠ 0)
    (p : Fin k → Space d) (T : Fin k → Matrix (Fin d) (Fin d) ℝ) (hT : ∀ j, (T j).det ≠ 0)
    (hcover : ∀ y ∈ B, ∃ j, y - p j ∈ matrixLattice (T j)) (x : Space d)
    (hx : ∀ j, ((matrixLattice (T j)).mkQ '' (matrixLattice (dualMatrix U) : Set (Space d))).Finite →
      x ∉ enlargedCoset (matrixLattice (dualMatrix U)) (matrixLattice (T j)) (p j)) :
    testAtom (restrictedFourierLinear hμ hA (range (latticeSite t U))) x = 0 := by
  let L := restrictedFourierLinear hμ hA (range (latticeSite t U))
  have hL : HasLocalTestBounds L := by
    simpa [L, Set.iInter_const] using restrictedFourierLinear_hasLocalTestBounds hμ hA hν hB
      (fun _ : Unit => t) (fun _ => U) (fun _ => hU)
  obtain ⟨M, hM⟩ := joint_atomic_variation_translation_bounded hμ hA hν hB 1
  have hbound (m : ℕ) : (m : ℝ) * ‖testAtom L x‖ ≤ k * (M : ℝ) := by
    obtain ⟨C, hC⟩ := cover_box_packing (dualMatrix U) (dualMatrix_det_ne_zero U hU) T hT p x hx m
    apply le_of_tendsto ((tendsto_testAtom hL x).norm.const_mul (m : ℝ))
    filter_upwards [hC] with n hn
    let φ := atomTest n x
    have hbox : Tendsto (spectralBoxTest b t U φ) atTop (𝓝 (L φ)) :=
      spectral_box_limit_on_test hμ hA hν hB t U hU φ
    have hlim := (box_ratio_tendsto d C).const_mul ((k : ℝ) * M)
    rw [mul_one] at hlim
    apply le_of_tendsto_of_tendsto' (hbox.norm.const_mul (m : ℝ)) hlim
    intro N
    let Q := Finset.univ.biUnion fun j =>
      boxHits (dualMatrix U) (matrixLattice (T j)) (p j) x (atomRadius n) N
    have hcount : (m : ℝ) * Q.card ≤ k * (((N : ℝ) + C + 1)^d) := by exact_mod_cast hn N
    have htest := spectralBoxTest_bound b t U p T hcover M (fun c => (hM c).2) x n N
    change (m : ℝ) * ‖spectralBoxTest b t U φ N‖ ≤ _
    calc
      _ ≤ m * (Q.card * (M : ℝ) / ((N : ℝ)+1)^d) := mul_le_mul_of_nonneg_left htest (by positivity)
      _ = (m * Q.card : ℝ) * M / ((N : ℝ)+1)^d := by ring
      _ ≤ (k * (((N : ℝ)+C+1)^d)) * M / ((N : ℝ)+1)^d := by gcongr
      _ = _ := by rw [div_pow]; ring
  by_contra hne
  have hpos : 0 < ‖testAtom L x‖ := norm_pos_iff.mpr hne
  obtain ⟨m, hm⟩ := exists_nat_gt ((k * (M : ℝ)) / ‖testAtom L x‖)
  exact ((div_lt_iff₀ hpos).mp hm).not_ge (hbound m)

/-- A spectral lattice cover forces the nonzero Fourier coefficients of each
full-rank restricted physical record onto finitely many dual-lattice cosets. -/
theorem finite_dual_classes_of_spectral_cover {d : ℕ}
    {μ : TemperedDistribution (Space d) ℂ} {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B)
    (hcover : HasFiniteLatticeCover B) (t : Space d) (U : Matrix (Fin d) (Fin d) ℝ) (hU : U.det ≠ 0) :
    ((matrixLattice (dualMatrix U)).mkQ '' Function.support
      (testAtom (restrictedFourierLinear hμ hA (range (latticeSite t U))))).Finite := by
  obtain ⟨k, _, p, T, hT, hcov⟩ := hcover
  let H := matrixLattice (dualMatrix U)
  let good := {j : Fin k // ((matrixLattice (T j)).mkQ '' (H : Set (Space d))).Finite}
  let D (j : good) := enlargedCoset H (matrixLattice (T j.val)) (p j.val)
  have hfin (j : good) : (H.mkQ '' D j).Finite :=
    (finite_lattice_orbit _ _ (dualMatrix_det_ne_zero U hU) (hT j.val) (p j.val) j.property).2
  have hcov' (y) (hy : y ∈ B) : ∃ j, y - p j ∈ matrixLattice (T j) := by
    obtain ⟨j, z, hz⟩ := hcov y hy
    exact ⟨j, (mem_latticeCoset_iff ..).mp ⟨z, hz.symm⟩⟩
  apply (Set.finite_iUnion hfin).subset
  rintro _ ⟨x, hx, rfl⟩
  by_contra hout
  apply hx
  apply atom_zero_outside_finite_orbits hμ hA hν hB t U hU p T hT hcov' x
  intro j hj hg
  exact hout (mem_iUnion.mpr ⟨⟨j,hj⟩, x, hg, rfl⟩)

/-- Given a finite lattice cover on each side, the weights in the spectral
record determine a finite sum of translated, modulated full-rank combs. -/
theorem spectral_comb_of_lattice_covers {d : ℕ}
    {μ : TemperedDistribution (Space d) ℂ} {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B)
    (hcovA : HasFiniteLatticeCover A) (hcovB : HasFiniteLatticeCover B) :
    IsFiniteModulatedLatticeCombSum (𝓕 μ) :=
  spectral_comb_of_finite_dual_classes hμ hA hν hB hcovA
    (finite_dual_classes_of_spectral_cover hμ hA hν hB hcovB)

/-- Once the algebraic covering step is proved, the analytic weight argument
supplies all remaining conclusions of Theorem A.1. -/
theorem theoremA1_of_physical_cover
    (hcovers : ∀ {d : ℕ} (_ : 0 < d) {μ : TemperedDistribution (Space d) ℂ}
      {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ},
      HasLocallyAtomicExpansion μ A a → UniformlyDiscrete A →
      HasLocallyAtomicExpansion (𝓕 μ) B b → UniformlyDiscrete B → HasFiniteLatticeCover A) :
    theoremA1Statement :=
  theoremA1_of_cover_and_finite_dual_classes hcovers
    (fun {_} _ {_ _ _ _ _} hμ hA hν hB hcov => finite_dual_classes_of_spectral_cover hμ hA hν hB hcov)

end
end MeyerGeneralProblem.LevOlevskii
