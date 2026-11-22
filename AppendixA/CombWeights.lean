module

public import AppendixA.DualCosets

/-!
# Converting coefficient identities into distributional comb identities
-/

@[expose] public section

namespace MeyerGeneralProblem.LevOlevskii

noncomputable section

open Set Filter Metric FourierTransform
open scoped Matrix FourierTransform RealInnerProductSpace Classical

theorem latticeSite_injective {d : ℕ} (t : Space d) (T : Matrix (Fin d) (Fin d) ℝ) (hT : T.det ≠ 0) :
    Function.Injective (latticeSite t T) := by
  intro z w h
  have heq := congrArg WithLp.ofLp (add_left_cancel (show t + _ = t + _ from h))
  change T *ᵥ (fun i => (z i : ℝ)) = T *ᵥ (fun i => (w i : ℝ)) at heq
  have hzw := Matrix.mulVec_injective_of_isUnit (T.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hT)) heq
  exact funext fun i => by exact_mod_cast congrFun hzw i

theorem latticeCoset_uniformlyDiscrete {d : ℕ} (t : Space d) (T : Matrix (Fin d) (Fin d) ℝ)
    (hT : T.det ≠ 0) : UniformlyDiscrete (range (latticeSite t T)) := by
  let H := matrixLattice T
  let : DiscreteTopology H := matrixLattice_discrete T hT
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (isOpen_discrete ({0} : Set H)) 0 (mem_singleton _)
  refine ⟨r, hr, ?_⟩
  intro x hx y hy hne
  by_contra! hlt
  have hsub : x - y ∈ H := by
    have h := H.sub_mem ((mem_latticeCoset_iff ..).mp hx) ((mem_latticeCoset_iff ..).mp hy)
    simpa only [sub_sub_sub_cancel_right] using h
  let z : H := ⟨x - y, hsub⟩
  have hz : z ∈ ball 0 r := by simpa [z, dist_eq_norm] using hlt
  have hzero : z = 0 := hball hz
  exact hne (sub_eq_zero.mp (congrArg Subtype.val hzero))

private theorem summable_schwartz_on_sites {d : ℕ} {D : Set (Space d)} (hD : UniformlyDiscrete D)
    (φ : SchwartzMap (Space d) ℂ) : Summable (fun z : D => ‖φ z‖) := by
  let k := d+1
  let C := 2^k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) φ
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ ((summable_inverse_weight hD k (by omega)).mul_left C)
  intro x
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
  simpa only [norm_iteratedFDeriv_zero] using
    SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, 0)) le_rfl le_rfl φ x.val

/-- An identity of coefficient functions on the whole ambient space, with
the atomic record extended by zero, gives the unordered distributional sum
even for intersecting or incommensurate lattices. -/
theorem latticeCombSum_of_recordWeight {d m : ℕ} {ν : TemperedDistribution (Space d) ℂ}
    {B : Set (Space d)} {b : B → ℂ} (hν : HasLocallyAtomicExpansion ν B b) (hB : UniformlyDiscrete B)
    (t s : Fin m → Space d) (c : Fin m → ℂ) (T : Fin m → Matrix (Fin d) (Fin d) ℝ)
    (hT : ∀ j, (T j).det ≠ 0)
    (hw : ∀ y, recordWeight b y = ∑ j, (range (latticeSite (t j) (T j))).indicator
      (fun z => c j * (frequencyPhase (s j) z : ℂ)) y) :
    IsFiniteModulatedLatticeCombSum ν := by
  refine ⟨m, t, s, c, T, hT, fun φ => ?_⟩
  let D j := range (latticeSite (t j) (T j))
  let f j (z : Space d) := (c j * (frequencyPhase (s j) z : ℂ)) * φ z
  let g j := (D j).indicator (f j)
  have hs (j) : Summable (fun z : D j => ‖f j z‖) := by
    simpa [f, norm_mul] using (summable_schwartz_on_sites (latticeCoset_uniformlyDiscrete _ _ (hT j)) φ).mul_left ‖c j‖
  let M j := ∑' z : D j, f j z
  have hD (j) : HasSum (g j) (M j) := hasSum_subtype_iff_indicator.mp (hs j).of_norm.hasSum
  have hatom : HasSum (fun z : Space d => recordWeight b z * φ z) (ν φ) := by
    have h := (atomicExpansion_of_locallyAtomic_of_uniformlyDiscrete hν hB).2 φ
    apply (hasSum_subtype_iff_of_support_subset (s := B) (by
      intro x hx; by_contra hnot; exact hx (by simp [recordWeight, hnot]))).mp
    simpa [Function.comp_def, recordWeight] using h
  have hval : ν φ = ∑ j, M j := by
    apply hatom.unique
    apply (hasSum_sum (fun j (_ : j ∈ Finset.univ) => hD j)).congr_fun
    intro z
    rw [hw, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    change (D j).indicator _ z * φ z = (D j).indicator (f j) z
    by_cases hz : z ∈ D j <;> simp [hz, f]
  let term (p : Fin m × (Fin d → ℤ)) := f p.1 (latticeSite (t p.1) (T p.1) p.2)
  have hn (j) : Summable (fun z => ‖term (j,z)‖) := by
    let e := Equiv.ofInjective _ (latticeSite_injective (t j) (T j) (hT j))
    exact (e.summable_iff (f := fun z : D j => ‖f j z‖)).mpr (hs j)
  have hsum : Summable term :=
    ((summable_prod_of_nonneg (f := fun p => ‖term p‖) (fun _ => norm_nonneg _)).mpr
      ⟨hn, (hasSum_fintype _).summable⟩).of_norm
  have hrows (j) : HasSum (fun z => term (j,z)) (M j) :=
    ((latticeSite_injective (t j) (T j) (hT j)).hasSum_range_iff (f := f j)).mp (hs j).of_norm.hasSum
  have hall := hsum.hasSum.prod_fiberwise hrows
  have heq := hall.unique (hasSum_fintype M)
  rw [hval, ← heq]
  apply hsum.hasSum.congr_fun
  intro p
  simp [term, f, frequencyPhase]

/-- Once a physical cover and the finiteness of the dual classes for each
single-coset restriction are established, the original spectral distribution
is a finite sum of full-rank translated modulated combs. -/
theorem spectral_comb_of_finite_dual_classes {d : ℕ}
    {μ : TemperedDistribution (Space d) ℂ} {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B) (hcover : HasFiniteLatticeCover A)
    (hclasses : ∀ (t : Space d) (T : Matrix (Fin d) (Fin d) ℝ), T.det ≠ 0 →
      ((matrixLattice (dualMatrix T)).mkQ '' Function.support (testAtom
        (restrictedFourierLinear hμ hA (range (latticeSite t T))))).Finite) :
    IsFiniteModulatedLatticeCombSum (𝓕 μ) := by
  obtain ⟨m, k, t, T, hT, hweights⟩ := spectral_weights_from_fullRank_restrictions hμ hA hν hB hcover
  let F j := testAtom (restrictedFourierLinear hμ hA (range (latticeSite (t j) (T j))))
  have hlocal (j) : HasLocalTestBounds (restrictedFourierLinear hμ hA (range (latticeSite (t j) (T j)))) := by
    simpa [Set.iInter_const] using restrictedFourierLinear_hasLocalTestBounds hμ hA hν hB
      (fun _ : Unit => t j) (fun _ => T j) (fun _ => hT j)
  choose l p c hrow using fun j => restrictedAtom_comb_of_finite_classes hμ hA (t j) (T j) (hT j)
    (hlocal j) (hclasses (t j) (T j) (hT j))
  let I := (j : Fin m) × Fin (l j)
  let e := Fintype.equivFin I
  let center (i : I) := p i.1 i.2
  let scalar (i : I) := (k i.1 : ℂ) * c i.1 i.2
  let matrix (i : I) := dualMatrix (T i.1)
  let modulate (i : I) := -t i.1
  apply latticeCombSum_of_recordWeight hν hB (center ∘ e.symm) (modulate ∘ e.symm)
    (scalar ∘ e.symm) (matrix ∘ e.symm) (fun i => dualMatrix_det_ne_zero _ (hT (e.symm i).1))
  intro y
  let term (i : I) := (range (latticeSite (center i) (matrix i))).indicator
    (fun z => scalar i * (frequencyPhase (modulate i) z : ℂ)) y
  change recordWeight b y = ∑ j, term (e.symm j)
  rw [e.symm.sum_comp term, Fintype.sum_sigma, hweights]
  apply Finset.sum_congr rfl
  intro j _
  rw [hrow, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hy : y ∈ range (latticeSite (p j i) (dualMatrix (T j))) <;>
    simp [term, center, scalar, matrix, modulate, hy, zsmul_eq_mul, mul_assoc]

/-- The two outstanding geometric inputs suffice for the complete statement
of A.1. Applying weight recovery to the inverse Fourier pair gives the comb
formula on the physical side directly. -/
theorem theoremA1_of_cover_and_finite_dual_classes
    (hcovers : ∀ {d : ℕ} (_ : 0 < d) {μ : TemperedDistribution (Space d) ℂ}
      {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ},
      HasLocallyAtomicExpansion μ A a → UniformlyDiscrete A →
      HasLocallyAtomicExpansion (𝓕 μ) B b → UniformlyDiscrete B → HasFiniteLatticeCover A)
    (hclasses : ∀ {d : ℕ} (_ : 0 < d) {μ : TemperedDistribution (Space d) ℂ}
      {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ} (hμ : HasLocallyAtomicExpansion μ A a)
      (hA : UniformlyDiscrete A), HasLocallyAtomicExpansion (𝓕 μ) B b → UniformlyDiscrete B →
      HasFiniteLatticeCover B → ∀ (t : Space d) (T : Matrix (Fin d) (Fin d) ℝ), T.det ≠ 0 →
      ((matrixLattice (dualMatrix T)).mkQ '' Function.support
        (testAtom (restrictedFourierLinear hμ hA (range (latticeSite t T))))).Finite) :
    theoremA1Statement := by
  intro d hd μ A B a b hμ hν hA hB
  have hcovA := hcovers hd hμ hA hν hB
  obtain ⟨hdual, hsep⟩ := reflected_atomic_expansion hμ hA
  have hcovB := hcovers hd hν hB hdual hsep
  obtain ⟨hinv, hsep'⟩ := inverse_atomic_expansion hν hB
  have hrec : HasLocallyAtomicExpansion (𝓕 (𝓕⁻ μ)) A a := by simpa using hμ
  have hcomb := spectral_comb_of_finite_dual_classes hinv hsep' hrec hA
    (reflected_lattice_cover hcovB) (hclasses hd hinv hsep' hrec hA hcovA)
  exact ⟨by simpa using hcomb, hcovA, hcovB⟩

end
end MeyerGeneralProblem.LevOlevskii
