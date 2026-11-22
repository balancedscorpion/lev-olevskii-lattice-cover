module

public import AppendixA.TransformedAverages
public import AppendixA.FourierReflection
public import Mathlib.Combinatorics.Enumerative.InclusionExclusion

/-!
# Fourier tests of the restricted physical record

All intersections in a finite lattice cover admit the same local bound on
the Fourier side. The bound is uniform in the center and independent of
the number of lattices or the ranks of their intersections.
-/

@[expose] public section

namespace MeyerGeneralProblem.LevOlevskii

noncomputable section

open Set MeasureTheory Filter FourierTransform
open scoped Topology FourierTransform ENNReal NNReal Classical

/-- Fourier test value of the physical atomic record restricted to `D`. -/
def restrictedFourierValue {d : ℕ} {A : Set (Space d)} (a : A → ℂ) (D : Set (Space d))
    (φ : SchwartzMap (Space d) ℂ) : ℂ :=
  ∑' x : A, D.indicator (fun z => a x * (𝓕 φ) z) x.val

private theorem restricted_hasSum {d : ℕ} {A : Set (Space d)} {a : A → ℂ}
    {μ : TemperedDistribution (Space d) ℂ} (hμ : HasLocallyAtomicExpansion μ A a)
    (hA : UniformlyDiscrete A) (D : Set (Space d)) (φ : SchwartzMap (Space d) ℂ) :
    HasSum (fun x : A => D.indicator (fun z => a x * (𝓕 φ) z) x.val)
      (restrictedFourierValue a D φ) := by
  apply Summable.hasSum
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (summable_atomic_schwartz hμ hA (𝓕 φ))
  intro x
  by_cases hx : x.val ∈ D
  · simp [hx]
  · simpa only [Set.indicator_of_notMem hx, norm_zero] using norm_nonneg (a x * (𝓕 φ) x)

/-- Restricting in physical space and testing the transform is complex-linear
in the spectral test. -/
def restrictedFourierLinear {d : ℕ} {A : Set (Space d)} {a : A → ℂ}
    {μ : TemperedDistribution (Space d) ℂ} (hμ : HasLocallyAtomicExpansion μ A a)
    (hA : UniformlyDiscrete A) (D : Set (Space d)) : SchwartzMap (Space d) ℂ →ₗ[ℂ] ℂ where
  toFun := restrictedFourierValue a D
  map_add' φ ψ := by
    apply (restricted_hasSum hμ hA D _).unique
    apply ((restricted_hasSum hμ hA D φ).add (restricted_hasSum hμ hA D ψ)).congr_fun
    intro x
    by_cases hx : x.val ∈ D <;> simp [hx, mul_add]
  map_smul' c φ := by
    apply (restricted_hasSum hμ hA D _).unique
    apply ((restricted_hasSum hμ hA D φ).mul_left c).congr_fun
    intro x
    by_cases hx : x.val ∈ D <;> simp [hx, mul_left_comm]

/-- Translating a spectral test along a frequency which is constant on the
physical restriction multiplies its value by that phase. -/
theorem restrictedFourierValue_translate {d : ℕ} {A : Set (Space d)} {a : A → ℂ}
    {μ : TemperedDistribution (Space d) ℂ} (hμ : HasLocallyAtomicExpansion μ A a)
    (hA : UniformlyDiscrete A) (D : Set (Space d)) (u : Space d) (z : Circle)
    (hz : ∀ x ∈ D, frequencyPhase u x = z) (φ : SchwartzMap (Space d) ℂ) :
    restrictedFourierValue a D ((SchwartzMap.compSubConstCLM ℂ (-u)) φ) =
      (z : ℂ) * restrictedFourierValue a D φ := by
  apply (restricted_hasSum hμ hA D _).unique
  apply ((restricted_hasSum hμ hA D φ).mul_left (z : ℂ)).congr_fun
  intro x
  by_cases hx : x.val ∈ D
  · simp [hx, fourier_test_add, hz x.val hx, mul_left_comm]
  · simp [hx]

/-- Inclusion–exclusion on any finite physical cover recovers the original
spectral test value, including all cancellations at overlapping sites. -/
theorem fourierValue_inclusion_exclusion {d : ℕ} {ι : Type*}
    {μ : TemperedDistribution (Space d) ℂ} {A : Set (Space d)} {a : A → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (J : Finset ι) (D : ι → Set (Space d)) (hcover : A ⊆ ⋃ j ∈ J, D j)
    (φ : SchwartzMap (Space d) ℂ) :
    (𝓕 μ) φ = ∑ S ∈ J.powerset with S.Nonempty,
      ((-1 : ℤ) ^ (S.card + 1)) • restrictedFourierValue a (⋂ j ∈ S, D j) φ := by
  apply ((atomicExpansion_of_locallyAtomic_of_uniformlyDiscrete hμ hA).2 (𝓕 φ)).unique
  apply (hasSum_sum (s := J.powerset.filter Finset.Nonempty)
    (fun S _ => (restricted_hasSum hμ hA (⋂ j ∈ S, D j) φ).const_smul ((-1 : ℤ) ^ (S.card + 1)))).congr_fun
  intro x
  simpa only [Set.indicator_of_mem (hcover x.property)] using
    J.indicator_biUnion_eq_sum_powerset D (fun z => a x * (𝓕 φ) z) x.val

private theorem translated_sum_ball_bound {d : ℕ} {B : Set (Space d)} (b : B → ℂ) (r : ℝ)
    (M : ℝ≥0) (hM : ∀ c : Space d, (∑' x : {x : B // dist x.val c ≤ r}, ‖b x.val‖ₑ) ≤ M)
    (φ : SchwartzMap (Space d) ℂ) (c : Space d) (hφ : ∀ z, ‖φ z‖ ≤ 1)
    (hsupp : ∀ z, φ z ≠ 0 → dist z c ≤ r) (u : Space d) :
    ‖∑' y : B, b y * φ (y.val + u)‖ ≤ M := by
  let S := {y : B | dist y.val (c - u) ≤ r}
  let f (y : B) := b y * φ (y.val + u)
  have hs : Function.support f ⊆ S := by
    intro y hy
    have hz : φ (y.val + u) ≠ 0 := fun h => hy (by simp [f, h])
    have hd := hsupp _ hz
    change dist y.val (c - u) ≤ r
    simpa [dist_eq_norm, show y.val + u - c = y.val - (c - u) by abel] using hd
  change ‖∑' y, f y‖ ≤ M
  rw [← tsum_subtype_eq_of_support_subset hs]
  apply (ENNReal.ofReal_le_ofReal_iff M.coe_nonneg).mp
  rw [ofReal_norm, ENNReal.ofReal_coe_nnreal]
  refine enorm_tsum_le_tsum_enorm.trans ((ENNReal.tsum_le_tsum fun y : S => ?_).trans (hM _))
  rw [show f y.val = b y.val * φ (y.val.val + u) by rfl, enorm_mul]
  apply mul_le_of_le_one_right (by positivity)
  simpa only [← ofReal_norm, ← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hφ (y.val.val + u))

/-- Uniform bound on the transformed restrictions as functionals on compact
tests bounded by one in balls of radius `r`. -/
theorem restrictedTransform_local_bound {d : ℕ}
    {μ : TemperedDistribution (Space d) ℂ} {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B) (r : ℝ) :
    ∃ M : ℝ≥0, ∀ {ι : Type} [Fintype ι] (t : ι → Space d) (T : ι → Matrix (Fin d) (Fin d) ℝ),
      (∀ j, (T j).det ≠ 0) → ∀ c : Space d, ∀ φ : SchwartzMap (Space d) ℂ,
      (∀ z, ‖φ z‖ ≤ 1) → (∀ z, φ z ≠ 0 → dist z c ≤ r) →
      ‖restrictedFourierValue a (⋂ j, range (latticeSite (t j) (T j))) φ‖ ≤ M := by
  obtain ⟨M, hM⟩ := joint_atomic_variation_translation_bounded hμ hA hν hB r
  refine ⟨M, fun {ι} _ t T hT c φ hφ hsupp => ?_⟩
  apply le_of_tendsto' (spectral_intersection_limit_on_test hμ hA hν hB t T hT φ).norm
  intro N
  calc
    _ ≤ ∑ q : IntersectionBox ι d N, ‖intersectionCoefficient t T q‖ * M := by
      apply norm_sum_le_of_le
      intro q _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (translated_sum_ball_bound b r M (fun p => (hM p).2) φ c hφ hsupp _) (norm_nonneg _)
    _ = M := by rw [← Finset.sum_mul, intersectionCoefficient_norm_sum, one_mul]

end
end MeyerGeneralProblem.LevOlevskii
