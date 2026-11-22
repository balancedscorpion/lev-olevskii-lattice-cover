module

public import AppendixA.LatticeAverages
public import AppendixA.SpectralRecurrence

/-!
# Dual-lattice averages on the Fourier side

Expanding a box into its individual frequencies gives a finite average of
translates of the original spectrum. The normalization has total absolute
weight one for every box size.
-/

@[expose] public section

namespace MeyerGeneralProblem.LevOlevskii

noncomputable section

open Matrix Filter FourierTransform MeasureTheory
open scoped Topology FourierTransform RealInnerProductSpace Matrix Classical

/-- Frequency in a box of the dual lattice, in inverse-matrix row coordinates. -/
def boxFrequency {d N : ℕ} (T : Matrix (Fin d) (Fin d) ℝ) (q : Fin d → Fin (N + 1)) : Space d :=
  ∑ i, (q i).val • WithLp.toLp 2 (T⁻¹ i)

/-- The common normalization of a box containing `(N+1)^d` frequencies. -/
def boxWeight (d N : ℕ) : ℂ := ((N + 1 : ℕ) : ℂ)⁻¹ ^ d

private theorem phase_inner {d : ℕ} (u x : Space d) :
    (frequencyPhase u x : Circle) = Real.fourierChar (inner ℝ u x) := by simp [frequencyPhase]

private theorem boxPhase {d N : ℕ} (T : Matrix (Fin d) (Fin d) ℝ)
    (q : Fin d → Fin (N + 1)) (x : Space d) :
    (frequencyPhase (boxFrequency T q) x : ℂ) =
    ∏ i, (Real.fourierChar ((T⁻¹ *ᵥ WithLp.ofLp x) i) : ℂ) ^ (q i).val := by
  have hsum (s : Finset (Fin d)) :
      (frequencyPhase x (∑ i ∈ s, (q i).val • WithLp.toLp 2 (T⁻¹ i)) : ℂ) =
      ∏ i ∈ s, (Real.fourierChar ((T⁻¹ *ᵥ WithLp.ofLp x) i) : ℂ) ^ (q i).val := by
    induction s using Finset.induction_on with
    | empty => simp [AddChar.map_zero_eq_one]
    | @insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.prod_insert hj, AddChar.map_add_eq_mul, Circle.coe_mul, ih,
        AddChar.map_nsmul_eq_pow, Circle.coe_pow]
      simp [phase_inner, EuclideanSpace.inner_eq_star_dotProduct, Matrix.mulVec]
  rw [phase_inner, real_inner_comm, ← phase_inner]
  exact hsum Finset.univ

/-- Expansion of the actual restriction multiplier into the finite dual box. -/
theorem latticeBoxAverage_expansion {d : ℕ} (t : Space d) (T : Matrix (Fin d) (Fin d) ℝ)
    (N : ℕ) (x : Space d) :
    latticeBoxAverage t T N x = ∑ q : Fin d → Fin (N + 1),
      boxWeight d N * (frequencyPhase (boxFrequency T q) (x - t) : ℂ) := by
  rw [latticeBoxAverage]
  simp_rw [phaseMean, div_eq_inv_mul, ← Fin.sum_univ_eq_sum_range, Finset.prod_mul_distrib,
    Fintype.prod_sum, Finset.mul_sum]
  simp [boxWeight, boxPhase]

/-- Fourier transforming a translated spectral test multiplies its transform
by a positive physical character when the test is `φ(· + u)`. -/
theorem fourier_test_add {d : ℕ} (φ : SchwartzMap (Space d) ℂ) (u x : Space d) :
    (𝓕 ((SchwartzMap.compSubConstCLM ℂ (-u)) φ)) x =
      (frequencyPhase u x : ℂ) * (𝓕 φ) x := by
  simp only [SchwartzMap.fourier_coe]
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume
    (innerₗ (Space d)) (φ : Space d → ℂ) u) x
  have hfun : ⇑((SchwartzMap.compSubConstCLM ℂ (-u)) φ) = (φ : Space d → ℂ) ∘ (· + u) := by
    ext y
    simp [SchwartzMap.compSubConstCLM_apply]
  rw [hfun]
  simpa [phase_inner, real_inner_comm u x, Circle.smul_def, FourierTransform.fourier] using h

/-- Any finite complex combination of physical characters gives exactly the
same combination of translated spectral tests. -/
theorem finite_modulation_on_fourier_test {d : ℕ} {ι : Type*} [Fintype ι]
    {μ : TemperedDistribution (Space d) ℂ} {A : Set (Space d)} {a : A → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (c : ι → ℂ) (u : ι → Space d) (φ : SchwartzMap (Space d) ℂ) :
    HasSum (fun x : A => (a x * (𝓕 φ) x) * ∑ i, c i * (frequencyPhase (u i) x : ℂ))
      (∑ i, c i * (𝓕 μ) ((SchwartzMap.compSubConstCLM ℂ (-(u i))) φ)) := by
  have h (i : ι) := ((atomicExpansion_of_locallyAtomic_of_uniformlyDiscrete hμ hA).2
    (𝓕 ((SchwartzMap.compSubConstCLM ℂ (-(u i))) φ))).mul_left (c i)
  simp_rw [Finset.mul_sum]
  simpa only [fourier_test_add, TemperedDistribution.fourier_apply,
    mul_comm, mul_assoc, mul_left_comm] using hasSum_sum (s := Finset.univ) (fun i _ => h i)

/-- The coefficient at a dual-box frequency, including the phase of the
physical translate. -/
def boxCoefficient {d N : ℕ} (t : Space d) (T : Matrix (Fin d) (Fin d) ℝ)
    (q : Fin d → Fin (N + 1)) : ℂ :=
  boxWeight d N * (frequencyPhase (boxFrequency T q) (-t) : ℂ)

theorem boxCoefficient_norm_sum {d N : ℕ} (t : Space d) (T : Matrix (Fin d) (Fin d) ℝ) :
    ∑ q : Fin d → Fin (N + 1), ‖boxCoefficient t T q‖ = 1 := by
  have hn : ‖(N : ℂ) + 1‖ = (N : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (N + 1)
  simp [boxCoefficient, boxWeight, hn, Nat.cast_add_one_ne_zero]

/-- Fourier-side formula for the averaged physical record at finite box size. -/
theorem latticeBox_on_fourier_test {d : ℕ}
    {μ : TemperedDistribution (Space d) ℂ} {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B)
    (t : Space d) (T : Matrix (Fin d) (Fin d) ℝ) (N : ℕ) (φ : SchwartzMap (Space d) ℂ) :
    (∑' x : A, (a x * (𝓕 φ) x) * latticeBoxAverage t T N x) =
    ∑ q : Fin d → Fin (N + 1), boxCoefficient t T q * ∑' y : B, b y * φ (y.val + boxFrequency T q) := by
  have h := (finite_modulation_on_fourier_test hμ hA (boxCoefficient (N := N) t T)
    (boxFrequency T) φ).tsum_eq
  have hshift (u : Space d) : (𝓕 μ) ((SchwartzMap.compSubConstCLM ℂ (-u)) φ) =
      ∑' y : B, b y * φ (y.val + u) := by
    simpa [SchwartzMap.compSubConstCLM_apply] using
      ((atomicExpansion_of_locallyAtomic_of_uniformlyDiscrete hν hB).2
        ((SchwartzMap.compSubConstCLM ℂ (-u)) φ)).tsum_eq.symm
  simpa only [hshift, latticeBoxAverage_expansion, sub_eq_add_neg, AddChar.map_add_eq_mul,
    Circle.coe_mul, boxCoefficient, mul_left_comm, mul_comm, mul_assoc] using h

/-- The Fourier transform of the restriction to a coset is the weak limit on
Schwartz tests of the explicit weighted translates of the original spectrum. -/
theorem spectral_box_limit_on_test {d : ℕ}
    {μ : TemperedDistribution (Space d) ℂ} {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B)
    (t : Space d) (T : Matrix (Fin d) (Fin d) ℝ) (hT : T.det ≠ 0) (φ : SchwartzMap (Space d) ℂ) :
    Tendsto (fun N => ∑ q : Fin d → Fin (N + 1), boxCoefficient t T q *
      ∑' y : B, b y * φ (y.val + boxFrequency T q)) atTop
      (𝓝 (∑' x : A, (Set.range (latticeSite t T)).indicator (fun z => a x * (𝓕 φ) z) x.val)) := by
  simp_rw [← latticeBox_on_fourier_test hμ hA hν hB]
  simpa [Set.iInter_const] using tendsto_latticeIntersection_on_test ({()} : Finset Unit) (fun _ => t)
    (fun _ => T) (fun _ _ => hT) hμ hA (𝓕 φ)

private theorem phase_sum_frequency {d : ℕ} {ι : Type*} [Fintype ι] (u : ι → Space d) (x : Space d) :
    (frequencyPhase (∑ i, u i) x : ℂ) = ∏ i, (frequencyPhase (u i) x : ℂ) := by
  have h (S : Finset ι) : (frequencyPhase x (∑ i ∈ S, u i) : ℂ) =
      ∏ i ∈ S, (frequencyPhase x (u i) : ℂ) := by
    classical
    induction S using Finset.induction_on with
    | empty => simp [AddChar.map_zero_eq_one]
    | insert i S hi ih => simp only [Finset.sum_insert hi, Finset.prod_insert hi,
        AddChar.map_add_eq_mul, Circle.coe_mul, ih]
  simpa only [phase_inner, real_inner_comm x] using h Finset.univ

/-- The box indices for the product used to restrict to a finite intersection. -/
abbrev IntersectionBox (ι : Type*) (d N : ℕ) := ι → Fin d → Fin (N + 1)

def intersectionFrequency {d N : ℕ} {ι : Type*} [Fintype ι]
    (T : ι → Matrix (Fin d) (Fin d) ℝ) (q : IntersectionBox ι d N) : Space d :=
  ∑ j, boxFrequency (T j) (q j)

def intersectionCoefficient {d N : ℕ} {ι : Type*} [Fintype ι]
    (t : ι → Space d) (T : ι → Matrix (Fin d) (Fin d) ℝ) (q : IntersectionBox ι d N) : ℂ :=
  ∏ j, boxCoefficient (t j) (T j) (q j)

theorem intersectionCoefficient_norm_sum {d N : ℕ} {ι : Type*} [Fintype ι]
    (t : ι → Space d) (T : ι → Matrix (Fin d) (Fin d) ℝ) :
    ∑ q : IntersectionBox ι d N, ‖intersectionCoefficient t T q‖ = 1 := by
  classical
  calc
    _ = ∑ q : IntersectionBox ι d N, ∏ j, ‖boxCoefficient (t j) (T j) (q j)‖ := by
      simp only [intersectionCoefficient, norm_prod]
    _ = ∏ j, ∑ q : Fin d → Fin (N + 1), ‖boxCoefficient (t j) (T j) q‖ :=
      (Fintype.prod_sum (fun j q => ‖boxCoefficient (t j) (T j) q‖)).symm
    _ = _ := by simp [boxCoefficient_norm_sum]

theorem latticeIntersection_expansion {d N : ℕ} {ι : Type*} [Fintype ι]
    (t : ι → Space d) (T : ι → Matrix (Fin d) (Fin d) ℝ) (x : Space d) :
    ∏ j, latticeBoxAverage (t j) (T j) N x =
    ∑ q : IntersectionBox ι d N, intersectionCoefficient t T q *
      (frequencyPhase (intersectionFrequency T q) x : ℂ) := by
  classical
  simp_rw [latticeBoxAverage_expansion, Fintype.prod_sum, sub_eq_add_neg, AddChar.map_add_eq_mul,
    Circle.coe_mul, intersectionFrequency, phase_sum_frequency, intersectionCoefficient,
    boxCoefficient, ← Finset.prod_mul_distrib]
  congr 1
  funext q
  apply Finset.prod_congr rfl
  intro j _
  ring

/-- Spectral translates for a finite intersection have total absolute
weight one, also when the intersection has lower rank. Their limit is
the restricted distribution evaluated on the Fourier transform of the test. -/
theorem spectral_intersection_limit_on_test {d : ℕ} {ι : Type*} [Fintype ι]
    {μ : TemperedDistribution (Space d) ℂ} {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B)
    (t : ι → Space d) (T : ι → Matrix (Fin d) (Fin d) ℝ) (hT : ∀ j, (T j).det ≠ 0)
    (φ : SchwartzMap (Space d) ℂ) :
    Tendsto (fun N => ∑ q : IntersectionBox ι d N, intersectionCoefficient t T q *
      ∑' y : B, b y * φ (y.val + intersectionFrequency T q)) atTop
      (𝓝 (∑' x : A, (⋂ j, Set.range (latticeSite (t j) (T j))).indicator
        (fun z => a x * (𝓕 φ) z) x.val)) := by
  classical
  have h := tendsto_latticeIntersection_on_test Finset.univ t T (fun j _ => hT j) hμ hA (𝓕 φ)
  have hshift (u : Space d) : (𝓕 μ) ((SchwartzMap.compSubConstCLM ℂ (-u)) φ) =
      ∑' y : B, b y * φ (y.val + u) := by
    simpa [SchwartzMap.compSubConstCLM_apply] using
      ((atomicExpansion_of_locallyAtomic_of_uniformlyDiscrete hν hB).2
        ((SchwartzMap.compSubConstCLM ℂ (-u)) φ)).tsum_eq.symm
  have heq (N : ℕ) := (finite_modulation_on_fourier_test hμ hA
    (intersectionCoefficient (N := N) t T) (intersectionFrequency T) φ).tsum_eq
  simp_rw [hshift, ← latticeIntersection_expansion] at heq
  simpa [heq, Set.iInter_const] using h

end
end MeyerGeneralProblem.LevOlevskii
