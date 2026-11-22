module

public import AppendixA.Definitions
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Polynomial bounds on the actual atomic coefficients

Adapted to arbitrary Euclidean dimension from the one-dimensional translated
test estimates in MeyerGeneralProblem PR 1888's base development.
-/

public section

namespace MeyerGeneralProblem.LevOlevskii

noncomputable section
open scoped SchwartzMap ContDiff NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem temperedDistribution_norm_le_finsetSchwartzSeminorm
    (T : TemperedDistribution E ℂ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ≥0, C ≠ 0 ∧
      ∀ f : SchwartzMap E ℂ,
        ‖T f‖ ≤ C * s.sup (schwartzSeminormFamily ℂ E ℂ) f := by
  let q : Seminorm ℂ (SchwartzMap E ℂ) :=
    (normSeminorm ℂ ℂ).comp T.toLinearMap
  have hq : Continuous q := by
    exact continuous_norm.comp T.continuous
  obtain ⟨s, C, hC, hbound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E ℂ) q hq
  exact ⟨s, C, hC, fun f => hbound f⟩

/-- Explicit polynomial control of each Schwartz seminorm under translation. -/
theorem translation_seminorm_bound (f : SchwartzMap E ℂ) (a : E) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n ((SchwartzMap.compSubConstCLM ℂ a) f) ≤
      (1 + ‖a‖) ^ k * 2 ^ k *
        (Finset.Iic (k, n)).sup (schwartzSeminormFamily ℂ E ℂ) f := by
  have hP : 0 ≤ (Finset.Iic (k, n)).sup
      (schwartzSeminormFamily ℂ E ℂ) f := apply_nonneg _ _
  apply SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity)
  intro x
  have hderiv : iteratedFDeriv ℝ n (⇑((SchwartzMap.compSubConstCLM ℂ a) f)) x =
      iteratedFDeriv ℝ n (⇑f) (x - a) := iteratedFDeriv_comp_sub (f := ⇑f) n a x
  rw [hderiv]
  have hweight : ‖x‖ ≤ (1 + ‖a‖) * (1 + ‖x - a‖) := by
    have h := norm_add_le (x - a) a
    have hx : ‖x‖ ≤ ‖x - a‖ + ‖a‖ := by simpa using h
    nlinarith [mul_nonneg (norm_nonneg a) (norm_nonneg (x - a))]
  have hbase := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℂ) (m := (k, n)) (le_refl k) (le_refl n) f (x - a)
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑f) (x - a)‖ ≤
        ((1 + ‖a‖) * (1 + ‖x - a‖)) ^ k * ‖iteratedFDeriv ℝ n (⇑f) (x - a)‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg x) hweight k)
        (norm_nonneg _)
    _ = (1 + ‖a‖) ^ k *
        ((1 + ‖x - a‖) ^ k * ‖iteratedFDeriv ℝ n (⇑f) (x - a)‖) := by rw [mul_pow]; ring
    _ ≤ (1 + ‖a‖) ^ k *
        (2 ^ k * (Finset.Iic (k, n)).sup (schwartzSeminormFamily ℂ E ℂ) f) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = _ := by ring

/-- Every fixed Schwartz test has polynomially bounded translated action
under an actual continuous tempered distribution. -/
theorem tempered_translated_test_polynomial_growth
    (T : TemperedDistribution E ℂ) (f : SchwartzMap E ℂ) :
    ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a : E,
      ‖T ((SchwartzMap.compSubConstCLM ℂ a) f)‖ ≤ C * (1 + ‖a‖) ^ N := by
  classical
  obtain ⟨s, B, _, hB⟩ := temperedDistribution_norm_le_finsetSchwartzSeminorm T
  let N : ℕ := s.sup Prod.fst
  let c : ℕ × ℕ → ℝ := fun p =>
    2 ^ p.1 * (Finset.Iic p).sup (schwartzSeminormFamily ℂ E ℂ) f
  have hc (p : ℕ × ℕ) : 0 ≤ c p :=
    mul_nonneg (by positivity) (apply_nonneg _ _)
  have hsum : 0 ≤ ∑ p ∈ s, c p := Finset.sum_nonneg (fun p _ => hc p)
  refine ⟨N, (B : ℝ) * ∑ p ∈ s, c p, mul_nonneg B.coe_nonneg hsum, ?_⟩
  intro a
  have hs : s.sup (schwartzSeminormFamily ℂ E ℂ)
      ((SchwartzMap.compSubConstCLM ℂ a) f) ≤
      (∑ p ∈ s, c p) * (1 + ‖a‖) ^ N := by
    apply Seminorm.finset_sup_apply_le (mul_nonneg hsum (by positivity))
    intro p hp
    change SchwartzMap.seminorm ℂ p.1 p.2
      ((SchwartzMap.compSubConstCLM ℂ a) f) ≤ _
    calc
      _ ≤ (1 + ‖a‖) ^ p.1 * 2 ^ p.1 *
          (Finset.Iic p).sup (schwartzSeminormFamily ℂ E ℂ) f :=
        translation_seminorm_bound f a p.1 p.2
      _ = c p * (1 + ‖a‖) ^ p.1 := by dsimp [c]; ring
      _ ≤ c p * (1 + ‖a‖) ^ N := by
        apply mul_le_mul_of_nonneg_left _ (hc p)
        exact pow_le_pow_right₀ (by linarith [norm_nonneg a]) (Finset.le_sup hp)
      _ ≤ (∑ q ∈ s, c q) * (1 + ‖a‖) ^ N :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun q _ => hc q) hp)
          (by positivity)
  calc
    _ ≤ (B : ℝ) * s.sup (schwartzSeminormFamily ℂ E ℂ)
        ((SchwartzMap.compSubConstCLM ℂ a) f) := hB _
    _ ≤ (B : ℝ) * ((∑ p ∈ s, c p) * (1 + ‖a‖) ^ N) :=
      mul_le_mul_of_nonneg_left hs B.coe_nonneg
    _ = _ := by ring

/-- A single compact Schwartz bump isolates all atoms after translation.
Its radius depends only on the separation of the support. -/
theorem exists_isolating_test {d : ℕ} {A : Set (Space d)} (hA : UniformlyDiscrete A) :
    ∃ φ : SchwartzMap (Space d) ℂ, HasCompactSupport φ ∧ φ 0 = 1 ∧
      ∀ x ∈ A, ∀ y ∈ A, y ≠ x → φ (y - x) = 0 := by
  obtain ⟨η, hη, hsep⟩ := hA
  let b : ContDiffBump (0 : Space d) :=
    { rIn := η / 4, rOut := η / 2, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  let f : Space d → ℂ := Complex.ofRealCLM ∘ b
  have hc : HasCompactSupport f := b.hasCompactSupport.comp_left rfl
  have hs : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp b.contDiff
  refine ⟨hc.toSchwartzMap hs, hc, ?_, ?_⟩
  · change ((b 0 : ℝ) : ℂ) = 1
    rw [b.one_of_mem_closedBall (by simpa using b.rIn_pos.le)]
    norm_num
  · intro x hx y hy hne
    change ((b (y - x) : ℝ) : ℂ) = 0
    rw [b.zero_of_le_dist]
    · norm_num
    · have hxy := hsep hy hx hne
      change η / 2 ≤ dist (y - x) 0
      rw [dist_zero_right, ← dist_eq_norm]
      linarith

/-- Local atomicity controls each actual coefficient by a common polynomial
of the distance from the origin. This is used for both Fourier records. -/
theorem atomic_coefficients_polynomial_growth {d : ℕ}
    {μ : TemperedDistribution (Space d) ℂ} {A : Set (Space d)} {a : A → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A) :
    ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : A, ‖a x‖ ≤ C * (1 + ‖(x : Space d)‖) ^ N := by
  obtain ⟨φ, hc, hzero, hisol⟩ := exists_isolating_test hA
  obtain ⟨N, C, hC, hbound⟩ := tempered_translated_test_polynomial_growth μ φ
  refine ⟨N, C, hC, fun x => ?_⟩
  let ψ := (SchwartzMap.compSubConstCLM ℂ x.val) φ
  have hcψ : HasCompactSupport (⇑ψ) := by
    change HasCompactSupport (fun y => φ (y - x.val))
    simp only [sub_eq_add_neg]
    exact hc.comp_homeomorph (Homeomorph.addRight (-x.val))
  have hsum := hμ.2 ψ hcψ
  have hoff (y : A) (hy : y ≠ x) : a y * ψ y = 0 := by
    change a y * φ (y.val - x.val) = 0
    rw [hisol x x.property y y.property (fun he => hy (Subtype.ext he)), mul_zero]
  have heq := hsum.unique (hasSum_single x hoff)
  have hval : μ ψ = a x := by simpa [ψ, SchwartzMap.compSubConstCLM_apply, hzero] using heq
  rw [← hval]
  exact hbound x

end
end MeyerGeneralProblem.LevOlevskii
