module

public import AppendixA.AtomicSeries
public import AppendixA.AlmostPeriods

/-!
# Relative density from the two atomic Fourier records

Translation of a test contributes one phase per spectral atom. Absolute
convergence on the inverse Fourier test gives a uniform bound for the
translated values and gives relatively dense almost periods.
-/

@[expose] public section

namespace MeyerGeneralProblem.LevOlevskii

noncomputable section

open FourierTransform MeasureTheory
open scoped FourierTransform RealInnerProductSpace

/-- The positive Fourier phase at frequency `y`. -/
def frequencyPhase {d : ℕ} (y : Space d) : AddChar (Space d) Circle :=
  Real.fourierChar.compAddMonoidHom (((innerₗ (Space d)).flip y).toAddMonoidHom)

private theorem inverse_translate {d : ℕ} (φ : SchwartzMap (Space d) ℂ) (p y : Space d) :
    (𝓕⁻ ((SchwartzMap.compSubConstCLM ℂ p) φ)) y =
      (frequencyPhase y p : ℂ) * (𝓕⁻ φ) y := by
  simp only [SchwartzMap.fourierInv_coe]
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume
    (-(innerₗ (Space d))) (φ : Space d → ℂ) (-p)) y
  have hfun : ⇑((SchwartzMap.compSubConstCLM ℂ p) φ) = (φ : Space d → ℂ) ∘ (· + -p) := by
    ext x
    simp [SchwartzMap.compSubConstCLM_apply, sub_eq_add_neg]
  rw [hfun]
  simpa [real_inner_comm p y, SchwartzMap.compSubConstCLM_apply, sub_eq_add_neg, frequencyPhase,
    Circle.smul_def, FourierTransformInv.fourierInv] using h

/-- Translated test values are the absolutely convergent Fourier series with
coefficients obtained by testing the spectrum against the inverse transform. -/
theorem translated_test_fourier_series {d : ℕ} {μ : TemperedDistribution (Space d) ℂ}
    {B : Set (Space d)} {b : B → ℂ}
    (hμhat : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B)
    (φ : SchwartzMap (Space d) ℂ) :
    Summable (fun y : B => ‖b y * (𝓕⁻ φ) y‖) ∧
    ∀ p, HasSum (fun y : B => (b y * (𝓕⁻ φ) y) * (frequencyPhase y.val p : ℂ))
      (μ ((SchwartzMap.compSubConstCLM ℂ p) φ)) := by
  refine ⟨summable_atomic_schwartz hμhat hB _, fun p => ?_⟩
  have h := (atomicExpansion_of_locallyAtomic_of_uniformlyDiscrete hμhat hB).2
    (𝓕⁻ ((SchwartzMap.compSubConstCLM ℂ p) φ))
  simpa only [inverse_translate, TemperedDistribution.fourier_apply, fourier_fourierInv_eq,
    mul_left_comm, mul_comm, mul_assoc] using h


/-- The translated values of each fixed Schwartz test are uniformly bounded. -/
theorem uniform_translated_test_bound {d : ℕ} {μ : TemperedDistribution (Space d) ℂ}
    {B : Set (Space d)} {b : B → ℂ}
    (hμhat : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B)
    (φ : SchwartzMap (Space d) ℂ) :
    ∃ C : ℝ, ∀ p, ‖μ ((SchwartzMap.compSubConstCLM ℂ p) φ)‖ ≤ C := by
  obtain ⟨hs, h⟩ := translated_test_fourier_series hμhat hB φ
  refine ⟨∑' y : B, ‖b y * (𝓕⁻ φ) y‖, fun p => ?_⟩
  rw [← (h p).tsum_eq]
  have hnorm : Summable (fun y : B => ‖(b y * (𝓕⁻ φ) y) * (frequencyPhase y.val p : ℂ)‖) := by
    simpa [norm_mul] using hs
  simpa [norm_mul] using norm_tsum_le_tsum_norm hnorm

/-- The coefficients of a uniformly discrete Fourier pair are uniformly
bounded, even when the local atomic identities are the only input. -/
theorem atomic_coefficients_uniformly_bounded {d : ℕ} {μ : TemperedDistribution (Space d) ℂ}
    {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (hμhat : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B) :
    ∃ C : ℝ, ∀ x : A, ‖a x‖ ≤ C := by
  obtain ⟨φ, hc, hzero, hisol⟩ := exists_isolating_test hA
  obtain ⟨C, hC⟩ := uniform_translated_test_bound hμhat hB φ
  exact ⟨C, fun x => (translated_isolating_test_eq hμ φ hc hzero hisol x) ▸ hC x.val⟩

/-- Every nonempty physical support of a uniformly discrete Fourier pair is
relatively dense. The radius is uniform over the ambient Euclidean space. -/
theorem relatively_dense_atomic_support {d : ℕ} {μ : TemperedDistribution (Space d) ℂ}
    {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (hμhat : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B)
    (hne : A.Nonempty) :
    ∃ R : ℝ, ∀ c : Space d, ∃ x ∈ A, dist c x ≤ R := by
  obtain ⟨φ, hc, hzero, hisol⟩ := exists_isolating_test hA
  obtain ⟨hs, h⟩ := translated_test_fourier_series hμhat hB φ
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Space d)).mp hc.isBounded
  let F (p : Space d) := μ ((SchwartzMap.compSubConstCLM ℂ p) φ)
  apply relatively_dense_of_localized_series A _ _ hs F (fun p => (h p).tsum_eq.symm) _ r
  · intro p hp
    obtain ⟨x, hx⟩ : ∃ x : A, φ (x.val - p) ≠ 0 := by
      by_contra! hvanish
      apply hp
      have hsum := (atomicExpansion_of_locallyAtomic_of_uniformlyDiscrete hμ hA).2
        ((SchwartzMap.compSubConstCLM ℂ p) φ)
      simpa [SchwartzMap.compSubConstCLM_apply, hvanish, F] using hsum.tsum_eq.symm
    refine ⟨x, x.property, ?_⟩
    rw [dist_comm, dist_eq_norm]
    simpa only [Metric.mem_closedBall, dist_zero_right] using hr (subset_closure hx)
  · obtain ⟨x, hx⟩ := hne
    refine ⟨x, ?_⟩
    change μ ((SchwartzMap.compSubConstCLM ℂ x) φ) ≠ 0
    rw [translated_isolating_test_eq hμ φ hc hzero hisol ⟨x, hx⟩]
    exact hμ.1 ⟨x, hx⟩

end
end MeyerGeneralProblem.LevOlevskii
