module

public import AppendixA.SpectralRecurrence

/-!
# Uniform counts and variation on translates of balls

Cover the closed ball at zero by finitely many balls of diameter below the
separation. Translation gives the same bound at every center.
-/

public section

namespace MeyerGeneralProblem.LevOlevskii

noncomputable section

open Set Metric FourierTransform
open scoped FourierTransform ENNReal NNReal

/-- Every translate of a given ball has at most the same finite number of
sites. The embedding includes both the finiteness and the numerical bound. -/
theorem uniformlyDiscrete_ball_embeddings {d : ℕ} {A : Set (Space d)}
    (hA : UniformlyDiscrete A) (r : ℝ) :
    ∃ N : ℕ, ∀ c : Space d, Nonempty ({x : A // dist x.val c ≤ r} ↪ Fin N) := by
  classical
  obtain ⟨η, hη, hsep⟩ := hA
  have hcomp : IsCompact (closure (closedBall (0 : Space d) r)) := by
    rw [isClosed_closedBall.closure_eq]
    exact isCompact_closedBall _ _
  obtain ⟨S, _, hfin, hcover⟩ := exists_finite_cover_balls_of_isCompact_closure hcomp (half_pos hη)
  let := hfin.fintype
  refine ⟨Fintype.card S, fun c => ?_⟩
  let X := {x : A // dist x.val c ≤ r}
  have hclose (x : X) : ∃ s : S, dist (x.val.val - c) s.val < η / 2 := by
    have hmem : x.val.val - c ∈ closedBall 0 r := by simpa [dist_eq_norm] using x.property
    obtain ⟨s, hs⟩ := mem_iUnion.mp (hcover hmem)
    obtain ⟨hsS, hx⟩ := mem_iUnion.mp hs
    exact ⟨⟨s, hsS⟩, hx⟩
  choose label hlabel using hclose
  have hinj : Function.Injective label := by
    intro x y heq
    by_contra hne
    have hxy := hsep x.val.property y.val.property
      (fun h => hne (Subtype.ext (Subtype.ext h)))
    have h₁ := hlabel x
    have h₂ := hlabel y
    rw [← heq, dist_comm] at h₂
    have htri := dist_triangle (x.val.val - c) (label x).val (y.val.val - c)
    rw [dist_sub_right] at htri
    linarith
  exact ⟨(⟨label, hinj⟩ : X ↪ S).trans (Fintype.equivFin S).toEmbedding⟩

/-- Total variation of the actual atomic weights is uniformly bounded over
all closed balls of a fixed radius. -/
theorem atomic_variation_translation_bounded {d : ℕ} {μ : TemperedDistribution (Space d) ℂ}
    {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (hμhat : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B) (r : ℝ) :
    ∃ M : ℝ≥0, ∀ c : Space d, (∑' x : {x : A // dist x.val c ≤ r}, ‖a x.val‖ₑ) ≤ M := by
  classical
  obtain ⟨C, hC⟩ := atomic_coefficients_uniformly_bounded hμ hA hμhat hB
  obtain ⟨N, hN⟩ := uniformlyDiscrete_ball_embeddings hA r
  refine ⟨(N : ℝ≥0) * Real.toNNReal C, fun c => ?_⟩
  obtain ⟨e⟩ := hN c
  let := Fintype.ofInjective e e.injective
  rw [tsum_fintype]
  calc
    _ ≤ ∑ _ : {x : A // dist x.val c ≤ r}, (Real.toNNReal C : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro x _
      exact ENNReal.coe_le_coe.mpr (by exact_mod_cast (hC x.val).trans (Real.le_coe_toNNReal _))
    _ ≤ _ := by
      simpa using mul_le_mul_of_nonneg_right
        (show (Fintype.card {x : A // dist x.val c ≤ r} : ℝ≥0∞) ≤ N by
          exact_mod_cast (Fintype.card_le_of_embedding e).trans_eq (Fintype.card_fin N))
        (show 0 ≤ (Real.toNNReal C : ℝ≥0∞) by positivity)

end
end MeyerGeneralProblem.LevOlevskii
